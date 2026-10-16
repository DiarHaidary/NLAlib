# Design note: LowRank stage S7, the oblivious subspace injection and embedding routes

Status: drafted 2026-10-16 and reviewed 2026-10-16; §8 records the review's amendments and the
maintainer's scope decision (2026-10-16: about 2,050 lines, 48 declarations; Q1 (a), Q2 (a)) and
supersedes §0 to §7 where they differ. Drafted under `docs/PORT_LOWRANK.md`. Binding: the
maintainer decisions of 2026-10-15 (every error spelled as the matrix minus the algorithm's named output,
`A - rsvd A (X ω)`, `A - generalizedNystrom A (X ω) (Ψ ω)`, `A - earlyTruncatedRSVD A (X ω) k`,
`B - Y * sketchAndSolve Y S B`; late truncation `truncatedSVD (rsvd A (X ω)) k`; the Chen–Persson
manuscript never cited); D2, D3, D4, D10, D13 to D15; §4.3 "Oblivious subspace injections and
embeddings"; the S7 entry of §7; §9.3. Also binding: CONTRIBUTING §5.2 rule 2 (named constants
shown by value markers inside the formula, never "with $C$ = …") and rule 3 "Asymptotic forms"
(2026-10-16), §6 item 5 (outputs in `\mathsf`), §8 item 5 "Placement". Builds on S0 to S6, S6b and
S2c (§8 of each overrides its §3; all proved and registered). The S9 draft
(`docs/design/LowRank-S9.md`, read on 2026-10-16) waits for this note for its generalized Nyström
corollary; §0.3 and Q9 state what S7 gives it. The Sketching families' size forms and asymptotic
forms are being extended by another agent while this note is written: S7 depends only on the
explicit theorems listed in §1 "Used directly", all on disk; §3.5 says how each asymptotic form
is proved whichever family asymptotic forms exist when it is implemented.

Docstrings in §3 are shortened, and their line breaks are not final (the files keep 100 columns). The full ones carry §5's citations, LaTeX throughout, outputs as
$\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})$, $\mathsf{nystrom}(\mathbf{H}, \mathbf{\Omega})$,
$\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})$,
$\mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)$,
$\mathsf{earlyTruncatedGN}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi}, k)$,
$\mathsf{sketchAndSolve}(\mathbf{Y}, \mathbf{S}, \mathbf{B})$, never the formula they unfold to;
named sample sizes appear by their value with a value marker before the span.

Departures from the brief, each argued below:
- **The range side takes one fixed subspace, not an OSI** (Q1, hard). Every RSVD, generalized
  Nyström and early-truncation statement assumes that $\mathbf{\Omega}^{\mathsf{H}}$ injects the
  single subspace $\operatorname{range}\llbracket\mathbf{A}\rrbracket_k^{\mathsf{H}}$
  (`HasSubspaceInjection (fun ω => (X ω)ᴴ) (truncatedSVD A k)ᴴ a δ μ`), plus isotropy where
  Markov's inequality is used. This is the hypothesis the proofs use, it is what row sampling
  satisfies (sampling is not oblivious), and an OSI for dimension $k$ supplies it in one term. The
  co-range side, which must inject a random subspace, takes an OSI. Nyström takes an OSI (§3.0,
  "ties").
- **Size**: 55 public declarations, about 2,500 lines, in ten new files and seven additions to
  five registered files (§0.2, §4), against the brief's three files and 850 lines. The growth: the
  family statements and their asymptotic forms (rule 3 postdates the brief; about 1,220 lines),
  the approximate-multiplication route (Woodruff Lemma 45, Theorem 47's first part, the
  $(1+\varepsilon)$ early-truncation tails; about 450), HMT Theorem 11.2's bounded-sketch route
  (about 110), and the four sketch-and-solve tails generalized Nyström needs (about 170).
- **Family instances live in one file per Sketching family file**, `LowRank/Oblivious/<F>.lean`
  mirroring `Sketching/<Dir>/<F>.lean` (§4 "Placement", Q3).
- **Per-family statements for the randomized SVD and the early-truncated randomized SVD only.**
  Nyström, generalized Nyström and early-truncated generalized Nyström are stated once, for any
  sketch with the predicate; the family instance of each is two lines (Q6). No Gaussian RSVD
  instance: S3's Tropp–Webber tail is sharper. Haar enters through the Gaussian–Haar transfer of
  S3's tail, one statement placed in S3's file (Q7).
- **The approximate-multiplication route lives in the namespace `HasJLMoment`**, not under a
  suffix `_of_hasJLMoment`, which pushes three names past 100 characters (Q4).
- **Early truncation is stated for any random rank-$k$ projector that is optimal on the sketch**
  (S2b's projector form), so that the family statements, which analyse the normalised sketch,
  conclude about the output at the user's raw test matrix (Q2).
- **Woodruff Theorem 47's rank-$k$ clause is not ported** after the D15 check (Q8).
- **HMT Theorem 11.2 is ported in a sharper form**, $1 + 2n/\ell$ in place of $1 + 7n/\ell$, in
  every quadratic unitarily invariant norm (§3.2 A5, §3.5 T2).

**Literature checks** (PDFs: `~/Documents/prove2me/books/camano_epperly_meyer_tropp_25.pdf`,
`woodruff_14.pdf`, `halko_martinsson_tropp_10.pdf`, `tropp_webber_23.pdf`;
`/tmp/claude-1000/p0/papers/` for CEMMP and TYUC; printed page numbers):
- CEMT Definition 1.2 (p. 3, the sketch is $\mathbf{\Omega}^{*}$); Theorem 1.3 (p. 4, RSVD,
  Nyström and generalized Nyström with an $(r, \alpha)$-OSI, probability $4/5$, $C/\alpha$; the
  remark after it promotes to rank $r$ by HMT Theorem 9.3); Lemma 2.1 (p. 14); **Theorem 2.2**
  (p. 16): $\|\mathbf{A} - \hat{\mathbf{A}}\|_{\mathsf{F}}^2 \le (C/\alpha)\|\mathbf{A} -
  \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2$ with probability $9/10$, proved as Imported
  Theorem 2.3 plus Lemma 2.1 plus Eckart–Young, so the factor is $1 + C/\alpha$ before rounding;
  Imported Theorem 2.4 and **Corollary 2.5** (p. 17, nuclear norm, $9/10$); Theorem 2.7 (p. 18,
  sketch-and-solve); **Corollary 2.8** (p. 20): $\mathbf{\Omega}$ an $(r, \alpha)$-OSI with $k$
  columns, $\mathbf{\Psi}$ a $(k, \alpha)$-OSI, $(C/\alpha)^2$ with probability $4/5$, stated over
  $\mathbb{R}$ (the proof is field-free); Remark 2.9 (pp. 20 to 21): the oversampling $p = \gamma^2 r$
  and Woodruff's core-truncated estimator, which CEMT "cannot endorse".
- Woodruff 2014: Lemma 44 (p. 63); **Lemma 45** (pp. 63 to 65): an embedding of the head with
  constants $1 \pm 1/3$ and the $(\sqrt{\varepsilon/k}, 9/10, \ell)$ JL moment give a
  $(1+\varepsilon)$ rank-$k$ approximation in the row space of $\mathbf{S}\mathbf{A}$; its proof is
  the bound $\|(\mathbf{S}\mathbf{U}_k)^{+}\mathbf{S}\mathbf{E}\|_{\mathsf{F}} \le
  \frac94\|\mathbf{U}_k^{\mathsf{T}}\mathbf{S}^{\mathsf{T}}\mathbf{S}\mathbf{E}\|_{\mathsf{F}}$ and
  approximate multiplication; Remark 46 (p. 64: CountSketch with $O(k^2 + k/\varepsilon)$ rows,
  Gaussian with $O(k/\varepsilon)$); **Theorem 47** (pp. 66 to 67), first part
  $\|\mathbf{A}\mathbf{R}(\mathbf{S}\mathbf{A}\mathbf{R})^{+}\mathbf{S}\mathbf{A} -
  \mathbf{A}\|_{\mathsf{F}}^2 \le (1+\varepsilon)\|\mathbf{A} - \mathbf{A}_k\|_{\mathsf{F}}^2$ (the
  generalized Nyström bound, in Woodruff's orientation), second part the rank-$k$ clause (Q8);
  Lemma 48 (p. 69); **Theorem 23** (p. 33): sketch-and-solve to $(1 \pm \varepsilon)$ from a
  subspace embedding and approximate multiplication, through
  $\|\mathbf{y}' - \mathbf{y}\| \le 2\|\mathbf{U}^{\mathsf{T}}\mathbf{S}^{\mathsf{T}}\mathbf{S}
  \mathbf{U}(\mathbf{y}' - \mathbf{y})\|$; Theorem 61 (p. 95): early truncation under an embedding of
  the whole column space (S2b's T7, not the head-plus-tail route; S2b Q6).
- HMT Theorem 11.2 (pp. 62 to 63): SRFT with $4[\sqrt{k} + \sqrt{8\log(kn)}]^2\log k \le \ell \le n$
  gives $\|(\mathbf{I} - \mathbf{P}_{\mathbf{Y}})\mathbf{A}\| \le \sqrt{1 + 7n/\ell}\,\sigma_{k+1}$ and
  the same factor in Frobenius norm, failure $O(k^{-1})$; its proof uses $\|\mathbf{\Omega}\|_2 =
  \sqrt{n/\ell}$, which the library has as `ae_specNorm_eq_of_hasLaw_srht`.
- CEMMP 2015 §7.2 and the proof of Theorem 12 (the head–tail sketch conditions, through S2b and the
  S9 draft's checks); TYUC SIMAX §7.3.1 (early-truncated generalized Nyström as an algorithm and the
  remark that CEMMP's results give $(1+\varepsilon)$ at $\Theta(r/\varepsilon^2)$ for both sketch
  sizes, unspecified constants).

**Missing infrastructure, per result** (each a statement of this note):
- Generalized Nyström and early-truncated generalized Nyström under an OSI co-range sketch need the
  sketch-and-solve tail for a *random* design independent of the sketch (L2), the random-subspace
  twin of CEMT Theorem 2.7, which the library has for a fixed design only.
- Every $(1+\varepsilon)$ generalized Nyström statement needs the sketch-and-solve error through
  approximate multiplication, $\|\mathbf{\Pi}_{\mathbf{Y},\mathbf{S}}\mathbf{B}\|_{\Phi} \le
  \|\mathbf{P}_{\mathbf{Y}}\mathbf{S}^{\mathsf{H}}\mathbf{S}\mathbf{B}\|_{\Phi}/a$ (L1, basis-free), and
  its fixed and random-design tails (L3, L4).
- The family statements with a normalised sketch need $\mathsf{rsvd}(\mathbf{A}, c\mathbf{\Omega})
  = \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})$ (L5; S1 §0 noted it for S7).
- Late-truncated generalized Nyström needs $\|\llbracket\mathbf{M}\rrbracket_j\|_{\mathsf{F}} \le
  \|\mathbf{M}\|_{\mathsf{F}}$ in public (L6; private in S6's
  `TruncatedGeneralizedNystrom.lean`, real only).
- Everything else exists: S1's structural bound in all its forms and its approximate-multiplication
  form, S2a's truncation lemmas, S2b's early-truncation core, S0's splits, S2c's measurability,
  the Sketching round's predicates, transfer to a random subspace, fixed-design tails, family size
  forms, JL moments and approximate-multiplication tails (§1 "Used directly").

## 0. Scope, size and the recommended cut

### 0.1 Notation

$\mathbf{A}$ : `Matrix m n 𝕜`; the range test matrix is `X : Ω → Matrix n l 𝕜`, written
$\mathbf{\Omega}$ in docstrings (S6), $\ell = \lvert l \rvert$; its sketch is
$\mathbf{\Omega}^{\mathsf{H}}$, `fun ω => (X ω)ᴴ` (D2). The co-range test matrix is
`Ψ : Ω → Matrix m p 𝕜`, applied as $\mathbf{\Psi}^{\mathsf{H}}$, $p = \lvert p \rvert$. The target
rank is `k : ℕ`; $\mathbf{E} = \mathbf{A} - \llbracket\mathbf{A}\rrbracket_k$ and
$\mathrm{OPT} = \|\mathbf{E}\|_{\mathsf{F}}$, spelled `A - truncatedSVD A k` (no definition). The
head projector is $\mathbf{P}_{\llbracket\mathbf{A}\rrbracket_k^{\mathsf{H}}}$,
`rangeProjector (truncatedSVD A k)ᴴ`, the projector onto the dominant right singular subspace of
the library's truncation. In the Sketching files the sketch is `S : Ω → Matrix k n 𝕜` (their
convention; there `k` is the row type and `d` the subspace dimension). Singular values from $0$, so
$\sigma_k(\mathbf{A})$ = `singularValues A k` is the best rank-$k$ spectral error.

### 0.2 Items, sizes and the cut

| # | Item | Statements | Lines (est.) | Recommendation |
|---|---|---|---|---|
| 1 | Lower layers: the approximate-multiplication bound for the oblique projector (L1), random-design and JL sketch-and-solve tails (L2 to L4), `rsvd_smul_right` (L5), `frobNorm_truncatedSVD_le` (L6) | 6 | 210 | include |
| 2 | Randomized SVD under an injection: Gram, Frobenius, spectral, late-truncated (A1 to A4) | 4 | 160 | include |
| 3 | Bounded sketches, HMT Theorem 11.2 (A5) | 1 | 50 | include |
| 4 | Randomized SVD through approximate multiplication (A6 to A8), Woodruff Lemma 45 | 3 | 120 | include |
| 5 | Nyström: trace, gauge, spectral, truncated, approximate multiplication (A9 to A13) | 5 | 150 | include |
| 6 | Generalized Nyström: completion tails, CEMT Corollary 2.8, late truncation, Woodruff Theorem 47 first part (B1 to B5) | 5 | 250 | include |
| 7 | Early truncation: projector-form core tails, $(1+\varepsilon)$ form, early-truncated GN (C1 to C6) | 6 | 340 | include |
| 8 | Families with approximate multiplication: Gaussian (early truncation), Rademacher, sub-Gaussian, CountSketch (RSVD and early truncation), each with its asymptotic form | 14 | 720 | include |
| 9 | SRHT, both models: RSVD (OSI route) and the bounded-sketch spectral form, with asymptotic forms | 6 | 290 | include |
| 10 | Row sampling, with and without replacement: RSVD at the rank-$k$ leverage scores, with asymptotic forms | 4 | 210 | include |
| 11 | Haar: S3's Tropp–Webber tail through the Gaussian–Haar range transfer (HT1, in S3's file) | 1 | 35 | include (flagged, §4) |
| D1 | Per-family Nyström, generalized Nyström, late-truncated and early-truncated GN instances, with asymptotic forms | about 70 | about 2,500 | cut: each is the generic theorem composed with the family's predicate in two lines (Q6) |
| D2 | Gaussian RSVD through the OSI or approximate-multiplication route | 2 | 90 | cut: S3's `measureReal_not_frobNorm_sub_rsvd_sq_le_le_of_hasLaw_gaussianMatrix` is sharper ($\log(1/\delta)$ against $1/\delta$) |
| D3 | Haar early truncation and Haar instances of the OSI route | 4 | 150 | defer: the Haar OSI has tails in $(t, s)$ and no sample-size form (Sketching §6.1 item 5; the S9 draft's D4) |
| D4 | Woodruff Theorem 47's rank-$k$ clause | 3 and a definition | 250 | cut after the D15 check (Q8) |
| D5 | Late-truncated GN through approximate multiplication ($k/\varepsilon^3$) | 1 | 60 | cut: additive; S6's TG5 is the $\varepsilon^{-2}$ statement for Gaussian sketches |
| D6 | SRHT and sampling early truncation | 4 | 250 | defer: needs an SRHT approximate-multiplication tail (the S9 draft's D3) and, for sampling, probabilities depending on the tail $\mathbf{E}$ |
| D7 | Public per-family orientation lemmas (D2's "orientation lemmas") | 4 | 60 | cut: absorbed into the family statements (§3.0 step 5); additive |
| D8 | The approximate-multiplication route over `𝕜` from the JL moment | n/a | n/a | waits for complex JL-moment approximate multiplication (Sketching §6.1 item 5); CountSketch has it over `𝕜` now (A8, C2) |

**Recommended cut:** items 1 to 11, 55 public declarations (no definition), about 2,500 lines:
the generic half (items 1 to 7, 30 declarations, about 1,280 lines) and the family half (items 8
to 11, 25 declarations, about 1,255 lines). The family half depends on the generic half only, and
its seven files are independent of one another. If the maintainer wants the stage smaller, the
fallback is items 1, 2, 4, 5, 6, 7 and the RSVD statements of items 8 to 10 (about 1,700 lines);
it drops what the S9 draft's cut relies on (S7's per-family early truncation; Q6).

### 0.3 Consumers

| Item | Consumers |
|---|---|
| L1 | L3, L4; any sketch-and-solve analysis through approximate multiplication (Solvers: sketch-and-precondition residual estimates) |
| L2 (random-design OSI completion tail) | B1, B2, B3, C4; **the S9 draft's U2** (Q9); Solvers (sketch-and-solve with a random design, iterative sketching) |
| L3, L4 | B4, B5, C5, C6; Solvers (the $(1+\varepsilon)$ sketch-and-solve of Woodruff Theorem 23, matrix right-hand side, any injection) |
| L5, L6 | the family proofs, B3; users scaling a test matrix |
| A1 to A8 | users holding a structured sketch (CEMT Theorem 2.2, Woodruff Lemma 45, HMT 11.2); B2, B3, B5; the family statements; Estimation (trace estimators through a range finder) |
| A9 to A13 | Solvers (Nyström PCG wants the spectral form A11); users |
| B1, B4 | users combining any range-finder tail (S3's Gaussian tail, A2, a sampling bound) with a structured co-range sketch, since they take any law of $\mathbf{\Omega}$ |
| B2, B3, B5 | users of single-pass methods with structured sketches (CEMT Corollary 2.8; Woodruff Theorem 47) |
| C1, C2, C3 | the family early-truncation statements; users; the S9 draft's comparison of routes |
| C4 | **the S9 draft's U2**; any early-truncated RSVD tail (C3, the S9 draft's U1, S6b by Markov) composes with it |
| C5, C6 | users of early-truncated GN with structured sketches (the maintainer's $\varepsilon^{-2}$ / $\varepsilon^{-1}$ split) |
| family statements | users holding that family; the explorer's per-family pages |
| HT1 | users with Haar test matrices |

Not in S7: Gaussian and Haar expectations (S3 to S6b); probabilistic PCPs (S9); lower bounds
(S10); the rank-$k$ clause of Woodruff Theorem 47 (Q8); complex JL-moment routes (D8).

## 1. Objects

No definition, no interface, no §5.3 row, no deviation from Mathlib. Every hypothesis is an
existing spelling (§2). Nothing joins `docs/design/Mathlib-deviations.md`.

**Used directly** (names checked on disk, 2026-10-16). S0: `rsvd`, `sub_rsvd`, `generalizedNystrom`,
`sub_generalizedNystrom`, `frobNorm_sub_generalizedNystrom_sq`, `nystrom`, `sketchAndSolve`,
`mul_sketchAndSolve`, `obliqueProjector`, `frobNorm_one_sub_obliqueProjector_mul_sq`,
`earlyTruncatedRSVD`, `sub_earlyTruncatedRSVD`, `earlyTruncatedGeneralizedNystrom`,
`frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq`, `conjTranspose_mul_self_sub_nystrom`,
`nuclearNorm_conjTranspose_mul_self_sub_nystrom`. S1: `SymmetricGauge.matrixNorm_conjTranspose_mul_self_sub_rsvd_le`,
`HasOrthonormalCols.frobNorm_sub_rsvd_sq_le`, `HasOrthonormalCols.specNorm_sub_rsvd_sq_le`,
`HasOrthonormalCols.frobNorm_sub_truncatedSVD_rsvd_sq_le`, `IsSubspaceInjection.frobNorm_sub_rsvd_sq_le`,
`HasOrthonormalCols.sub_mul_mul_pinv_eq`, `IsSubspaceInjection.matrixNorm_sub_mul_mul_pinv_le`. S2a:
`frobNorm_sub_truncatedSVD_rsvd_sq` (T3), `frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_frobNorm_truncatedSVD`
(T10), `nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD_nystrom`. S2b:
`IsSubspaceInjection.frobNorm_sub_mul_sq_le` (T4), `IsSubspaceInjection.frobNorm_sub_earlyTruncatedRSVD_sq_le`
(T5). S2c: `measurable_truncatedSVD`, `measurable_rangeProjector`, `measurable_pinv`. Matrix:
`mul_rangeProjector_conjTranspose_truncatedSVD`, `rangeProjector_truncatedSVD_mul`,
`frobNorm_sub_truncatedSVD_le_of_rank_le`, `truncatedSVD_of_rank_le`, `specNorm_sub_truncatedSVD`,
`frobNorm_truncatedSVD_sq`, `rank_truncatedSVD_le`, `rsvd_eq_self_of_rank_eq`,
`exists_hasOrthonormalCols_range_eq`, `rangeProjector_smul`, `obliqueProjector_eq_of_range_eq`,
`sub_earlyTruncatedGeneralizedNystrom`, `HasOrthonormalCols.frobNorm_mul_conjTranspose_right`,
`matrixNorm_mul_left_of_hasOrthonormalCols`, `matrixNorm_mul_le_specNorm_mul`, `lpGauge_one_matrixNorm`,
`frobNorm_rangeProjector_sq`, `nuclearNorm_conjTranspose_mul_self`,
`SymmetricGauge.matrixNorm_conjTranspose_mul_self_sub_truncatedSVD`,
`nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD`, `Φ.matrixNorm_le_apply_single_mul_nuclearNorm`,
`matrixNorm_le_of_singularValues_le`, `singularValues_mul_le_mul_specNorm`,
`specNorm_pinv_sq_le_inv_of_smul_one_le`, `specNorm_conjTranspose`, `isClosed_setOf_rank_le`.
Sketching: `HasSubspaceInjection`, `IsObliviousSubspaceInjection` (`.hasSubspaceInjection`,
`.isotropic`), `IsIsotropicSketch.integral_frobNorm_mul_sq`, `.integrable_frobNorm_mul_sq`,
`IsSubspaceInjection.rank_mul_eq`, `.of_range_le`, `HasSubspaceInjection.of_range_le`,
`HasOrthonormalCols.isSubspaceInjection_iff`, `IsSubspaceInjection.frobNorm_obliqueProjector_mul_sq_le`,
`IsSubspaceInjection.frobNorm_sub_mul_pinv_mul_sq_le`, `IsSubspaceInjection.frobNorm_mul_pinv_sq_le`,
`hasSubspaceEmbedding_of_rank_eq_zero`, `IsSubgaussianVector.one_le_of_isIsotropic`,
`samplingInjectionSize_mono`, `ae_specNorm_eq_of_hasLaw_srht`,
`IsObliviousSubspaceInjection.measure_frobNorm_sub_mul_pinv_mul_sq_gt_le` (CEMT Theorem 2.7),
`HasJLMoment`, `HasJLMoment.measure_frobNorm_conjTranspose_mul_sub_ge_le`,
`measureReal_frobNorm_conjTranspose_mul_sub_ge_le_of_hasLaw_countSketch`, and the family theorems of
§3.5. Probability: `measureReal_ge_le_integral_div` (`Probability/Tail.lean`),
`ProbabilityTheory.IndepFun.measureReal_mem_le_add` (`ForMathlib/Probability/Independence/Basic.lean`).
RandomMatrix: `hasLaw_conjTranspose_of_hasLaw_gaussianMatrix`,
`hasLaw_rangeProjector_mul_of_hasLaw_haarFrame`. Mathlib: `measureReal_mono`,
`measureReal_union_le`, `Matrix.conjTranspose_smul`, `Matrix.rank_mul_le_left`,
`Matrix.rank_mul_le_right`, `Matrix.rank_conjTranspose`.

**Mathlib search** ("searched, none" unless named): randomized range finder, sketch-and-solve,
oblivious subspace embeddings, approximate matrix multiplication (none); the union bound and
Markov's inequality (Mathlib's `measureReal_union_le`, the library's `measureReal_ge_le_integral_div`);
Fubini for an event of two independent variables (the library's
`IndepFun.measureReal_mem_le_add`).

## 2. Interfaces

No new predicate. Hypotheses, each an existing spelling:
- **Range side** (Q1): `h : HasSubspaceInjection (fun ω => (X ω)ᴴ) (truncatedSVD A k)ᴴ a δ μ`, with
  `hiso : IsIsotropicSketch (fun ω => (X ω)ᴴ) μ` where a Markov step uses the mean of
  $\|\mathbf{E}\mathbf{\Omega}\|_{\mathsf{F}}^2$. An OSI for dimension $k$ gives both:
  `hOSI.hasSubspaceInjection (by rw [Matrix.rank_conjTranspose]; exact rank_truncatedSVD_le A k)` and
  `hOSI.isotropic`. Nyström takes `IsObliviousSubspaceInjection (fun ω => (X ω)ᴴ) k a δ μ` (§3.0).
- **Co-range side**: `IsObliviousSubspaceInjection (fun ω => (Ψ ω)ᴴ) d a δ μ` with
  `hd : min A.rank (Fintype.card l) ≤ d` for generalized Nyström and `d = k` for the early-truncated
  version; `hind : IndepFun X Ψ μ`, `hX : AEMeasurable X μ`, `hΨ : AEMeasurable Ψ μ`.
- **Approximate multiplication**: `HasJLMoment (fun ω => (X ω)ᴴ) ε δ' p μ` with `2 ≤ p`, over ℝ
  (the JL-moment multiplication bound is real; D8); over `𝕜`, raw tails at the two fixed pairs, in
  the form S2b's §5.3 row "early-truncation sketch quantities" fixed: tail–tail
  $\|\mathbf{E}\mathbf{\Omega}\mathbf{\Omega}^{\mathsf{H}}\mathbf{E}^{\mathsf{H}} -
  \mathbf{E}\mathbf{E}^{\mathsf{H}}\|_{\mathsf{F}}$ and tail–head
  $\|\mathbf{E}\mathbf{\Omega}\mathbf{\Omega}^{\mathsf{H}}\mathbf{P}_{\llbracket\mathbf{A}
  \rrbracket_k^{\mathsf{H}}}\|_{\mathsf{F}}$ (basis-free: equal to S2b's
  $\|\mathbf{E}\mathbf{\Omega}\mathbf{\Omega}^{\mathsf{H}}\mathbf{Z} - \mathbf{E}\mathbf{Z}\|_{\mathsf{F}}$ for
  every frame $\mathbf{Z}$ of the head, since $\mathbf{E}\mathbf{Z} = \mathbf{0}$). No predicate for
  these tails (as the Sketching round and the S9 draft).
- **Early truncation, projector form**: a random `P : Ω → Matrix m m 𝕜` with
  `hP : ∀ ω, IsStarProjection (P ω)`, `hPk : ∀ ω, (P ω).rank ≤ k` and
  `hopt : ∀ ω, frobNorm (A * X ω - P ω * (A * X ω)) ≤ frobNorm ((A - truncatedSVD A k) * X ω)`,
  S2b's T4 hypothesis with the frame removed. The early-truncated output's projector
  `rangeProjector (truncatedSVD (A * X ω) k)` satisfies it (Eckart–Young), and so does the projector
  of the output at the raw test matrix when the analysis runs on a rescaled one (Q2).
- **Family laws** (Q2, hard): Gaussian and Haar on the test matrix, `HasLaw X (gaussianMatrix n l) μ`,
  `HasLaw X (haarFrame n l) μ` (D2, as S3 to S6); every other family on the sketch,
  `HasLaw (fun ω => (X ω)ᴴ) (srht l F) μ`, `(countSketch l n)`, `(samplingSketch l p)`,
  `(samplingSketchWithoutReplacement l n)`, `(rademacherMatrix l n)`, and for sub-Gaussian sketches
  the row hypotheses on `fun i ω => (X ω)ᴴ i`; these laws exist only in the sketch orientation.
- **Tails**: generic statements in the namespace of their interface take Mathlib's `measure_` and
  the event $\{c < X\}$, as `Sketching/Properties/Injection.lean`; family statements are root-level,
  `measureReal_…_gt_le_of_<law>`; the Haar transfer keeps S3's `measureReal_not_…_le_le_of_…`
  (CONTRIBUTING §4).

## 3. Statement shapes

`namespace NLAlib`, `open MeasureTheory ProbabilityTheory`, `open scoped Matrix MatrixOrder`.
LowRank variables: `{Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
{m n l p : Type*} [Fintype m] [Fintype n] [Fintype l] [Fintype p] [DecidableEq m] [DecidableEq n]
{X : Ω → Matrix n l 𝕜} {Ψ : Ω → Matrix m p 𝕜}`, with `𝕜 := ℝ` in the real sections.

### 3.0 Common steps and degenerate cases

**Common steps.**
1. *Head frame.* Take `Z : Matrix n (Fin r) 𝕜` with orthonormal columns and range
   $\operatorname{range}\llbracket\mathbf{A}\rrbracket_k^{\mathsf{H}}$
   (`exists_hasOrthonormalCols_range_eq`, $r = \operatorname{rank}\llbracket\mathbf{A}\rrbracket_k \le
   k$). Then $\mathbf{Z}\mathbf{Z}^{\mathsf{H}} = \mathbf{P}_{\llbracket\mathbf{A}\rrbracket_k^{\mathsf{H}}}$,
   $\mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}} = \llbracket\mathbf{A}\rrbracket_k$
   (`mul_rangeProjector_conjTranspose_truncatedSVD`), so S1's and S2b's $\mathbf{A} -
   \mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}}$ is $\mathbf{E}$, and the injection transfers to
   $\mathbf{Z}$ (`HasSubspaceInjection.of_range_le`). This needs no case split on $k$ against
   $\lvert n \rvert$ or $\operatorname{rank}\mathbf{A}$, unlike S1's top-$k$ frame lemma, and it is
   choice-consistent: the hypothesis, $\mathbf{E}$ and $\mathrm{OPT}$ use the same `truncatedSVD A k`.
2. *Markov step.* $\|\mathbf{E}\mathbf{\Omega}\|_{\mathsf{F}} =
   \|\mathbf{\Omega}^{\mathsf{H}}\mathbf{E}^{\mathsf{H}}\|_{\mathsf{F}}$ has mean square
   $\|\mathbf{E}\|_{\mathsf{F}}^2$ (`IsIsotropicSketch.integral_frobNorm_mul_sq` at $\mathbf{E}^{\mathsf{H}}$);
   `measureReal_ge_le_integral_div` bounds $\{t\|\mathbf{E}\|_{\mathsf{F}}^2 <
   \|\mathbf{E}\mathbf{\Omega}\|_{\mathsf{F}}^2\}$ by $1/t$; at $\mathbf{E} = \mathbf{0}$ the event is
   empty.
3. *Union step.* Each bad event lies in the union of the failure events; `measureReal_mono` and
   `measureReal_union_le` (no measurability needed). On the good event the deterministic bound of
   S1, S2a or S2b applies, with the rank hypothesis $(\mathbf{\Omega}^{\mathsf{H}}\mathbf{Z})$ of full
   rank from `IsSubspaceInjection.rank_mul_eq` at $a > 0$.
4. *Independence step* (L2, L4, B1 to B5, C4 to C6). For an event $E$ of
   $(\mathbf{S}, (\mathbf{Y}, \mathbf{B}))$ with $\mathbf{S}$ independent of the pair,
   `IndepFun.measureReal_mem_le_add` bounds it by the supremum of the fixed-pair probabilities over
   the good set $\{\operatorname{rank}\mathbf{Y} \le d\}$ (closed, `isClosed_setOf_rank_le`); $E$ is
   measurable by S2c's `measurable_rangeProjector`, `measurable_pinv` and continuity of the norms.
   The fixed-pair bound is the Sketching round's fixed-design theorem (L2) or L3 (L4). The design
   is a measurable function of $\mathbf{\Omega}$ ($\mathbf{A}\mathbf{\Omega}$, or
   $\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k$ by `measurable_truncatedSVD`).
5. *Scaling step* (families whose sketch is normalised). The Gaussian, Rademacher and sub-Gaussian
   predicates are about `fun ω => (√ℓ)⁻¹ • (X ω)ᴴ`, which is `fun ω => ((√ℓ)⁻¹ • X ω)ᴴ` over ℝ
   (`Matrix.conjTranspose_smul`); the generic theorem runs at $\mathbf{\Omega}' = \ell^{-1/2}
   \mathbf{\Omega}$, and `rsvd_smul_right` (L5) returns to $\mathbf{\Omega}$. Early truncation goes
   through the projector form at $\mathbf{\Omega}'$ with $\mathbf{P}$ the projector of
   $\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k$: `hopt` at $\mathbf{\Omega}$ is Eckart–Young, and
   both of its sides scale by $\ell^{-1/2}$ (`frobNorm_smul`). The output at
   $\ell^{-1/2}\mathbf{\Omega}$ is never identified with the one at $\mathbf{\Omega}$ (S2b §3.0,
   "Scaling": not provable under ties). CountSketch, SRHT and sampling sketches are isotropic
   unscaled; the Haar sketch is $\sqrt{n/\ell}\,\mathbf{\Omega}^{\mathsf{H}}$ (HT1 does not use it).

**Degenerate cases** (checked for every statement; the routes say where a case bites).
- *$k = 0$.* $\llbracket\mathbf{A}\rrbracket_0 = \mathbf{0}$, $\mathbf{E} = \mathbf{A}$, the head
  projector is $\mathbf{0}$, the injection hypothesis is about the zero subspace and holds with
  $\delta = 0$ (`hasSubspaceEmbedding_of_rank_eq_zero` gives its injection half), the early-truncated
  outputs are $\mathbf{0}$. Every bound has factor at least $1$ against
  $\|\mathbf{A}\|_{\mathsf{F}}^2$ and every error is at most $\|\mathbf{A}\|_{\mathsf{F}}^2$ (a
  projection residual, or $\mathbf{0}$), so every event is empty; A6's factor
  $1 + k\varepsilon^2/a^2$ is $1$, still at least the error. The family statements' JL accuracy
  $\varepsilon/(8\sqrt{k})$ is Lean's $0$ there; their proofs branch on $k = 0$ first.
- *$k \ge \operatorname{rank}\mathbf{A}$, including $k \ge \lvert n \rvert$ or $\lvert m \rvert$.*
  $\llbracket\mathbf{A}\rrbracket_k = \mathbf{A}$, $\mathbf{E} = \mathbf{0}$, $\mathrm{OPT} = 0$; the
  injection of $\operatorname{range}\mathbf{A}^{\mathsf{H}}$ gives
  $\operatorname{rank}(\mathbf{A}\mathbf{\Omega}) = \operatorname{rank}\mathbf{A}$, so
  $\mathsf{rsvd} = \mathbf{A}$ on the good event (`rsvd_eq_self_of_rank_eq`) and every event lies in
  the injection failure. No hypothesis on $k$.
- *Fewer samples than the rank, $\ell < k$.* An injection of a nonzero subspace of dimension above
  $\ell$ fails surely; the hypothesis then forces $\delta \ge 1$ and every statement is vacuous.
  The family size hypotheses exclude it ($\ell \ge 16(\sqrt{k} + \cdots)^2 > k$ and the like).
- *More samples than the dimension, $\ell > n$.* Allowed for Gaussian, Rademacher, sub-Gaussian,
  CountSketch, SRHT with replacement and sampling with replacement; SRHT without replacement,
  sampling without replacement and Haar carry `Fintype.card l ≤ Fintype.card n`, as their laws need.
- *Empty sketch.* `l` empty makes every isotropy hypothesis false (no isotropic map to
  $\Bbbk^0$ on a nonzero space) and the family size hypotheses false; the statements that need it
  carry the family's `[Nonempty l]` or derive it from the size hypothesis.
- *Ties* $\sigma_{k-1} = \sigma_k$ of $\mathbf{A}$: the hypothesis is about the library's
  $\llbracket\mathbf{A}\rrbracket_k$, the same matrix as in $\mathbf{E}$, so no choice mismatch
  arises. **Nyström** is different: its proofs pass to a factor $\mathbf{F}$ with
  $\mathbf{H} = \mathbf{F}^{\mathsf{H}}\mathbf{F}$, and
  $\operatorname{range}\llbracket\mathbf{F}\rrbracket_k^{\mathsf{H}}$ is a choice of the top
  eigenspace of $\mathbf{H}$ that need not be the one of $\llbracket\mathbf{H}\rrbracket_k$ under a
  tie $\lambda_k = \lambda_{k+1}$. So Nyström takes an OSI (every subspace of dimension $k$), as CEMT
  Corollary 2.5 does. Early truncation: the projector form holds for every optimal projector;
  `truncatedSVD (A * X ω) k` is one.
- *Rank hypothesis of the split* (`(Ψᴴ * X).rank = X.rank`): never a hypothesis; it holds on the
  injection event.
- *Constants.* $a \le 0$: excluded by `0 < a` wherever $t/a$ or $1/a$ appears; the families give
  $a = 1 - \varepsilon$ or $1/2$. $t \le 0$: excluded. $\delta \ge 1$: every statement is true for a
  probability measure; the families do not exclude it. $a > 1$ is allowed except in early
  truncation, where S2b's core needs $a \le 1$ (`ha1`). $\varepsilon > 1$: the RSVD
  $(1+\varepsilon)$ statements allow it; early truncation needs $\varepsilon \le 1$ (the factor
  arithmetic of §3.6).
- *Hermitian, not positive semidefinite, Nyström input*: excluded by `H.PosSemidef` (the Gram
  correspondence).
- *Field.* The OSI route, the bounded-sketch route, the raw approximate-multiplication forms and
  every random-design tail are over `𝕜`; the JL-moment forms are over ℝ (D8). Families: Gaussian,
  Rademacher, sub-Gaussian real; CountSketch, SRHT, sampling over `𝕜`; Haar real.
- *Measure.* Single-sketch tails take `[IsFiniteMeasure μ]` (as Sketching's
  `measure_frobNorm_mul_pinv_sq_gt_le`); two-sketch tails `[IsProbabilityMeasure μ]` (the
  independence step); the families get it from `HasLaw`.

### 3.1 Lower layers (6)

Homes and reasons in §4 "Placement". Variables of the host files (`S : Ω → Matrix k n 𝕜`,
`A : Matrix n q 𝕜`, `Y : Matrix n r 𝕜` in the Sketching files).

```lean
/-- **Sketch-and-solve error through approximate multiplication**: if $\mathbf{S}$ injects
$\operatorname{range}\mathbf{A}$ with constant $a > 0$, then for every $\mathbf{Y}$ and every
unitarily invariant norm
$$\|\mathbf{\Pi}_{\mathbf{A},\mathbf{S}}\mathbf{Y}\|_{\Phi} \le
\frac{\|\mathbf{P}_{\mathbf{A}}\mathbf{S}^{\mathsf{H}}\mathbf{S}\mathbf{Y}\|_{\Phi}}{a}\,.$$
For $\mathbf{Y}$ with $\mathbf{P}_{\mathbf{A}}\mathbf{Y} = \mathbf{0}$ the right side is an
approximate-multiplication error. The bound in $\|\mathbf{S}\mathbf{Y}\|_{\mathsf{F}}$ is
`NLAlib.IsSubspaceInjection.frobNorm_obliqueProjector_mul_sq_le`; this one decays with the sketch
size. [Woodruff2014, proof of Theorem 23]; there for an orthonormal basis and a $(1 \pm 1/2)$
embedding; here basis-free, any injection constant, every gauge. -/
theorem IsSubspaceInjection.matrixNorm_obliqueProjector_mul_le (h : IsSubspaceInjection S A a)
    (ha : 0 < a) (Φ : SymmetricGauge) (Y : Matrix n r 𝕜) :
    Φ.matrixNorm (obliqueProjector A S * Y) ≤ Φ.matrixNorm (rangeProjector A * Sᴴ * S * Y) / a

/-- **Sketch-and-solve with an OSI and a random design**: if $\mathbf{S}$ is an OSI for dimension
$d$ with constant $a > 0$ and failure probability $\delta$, independent of a random design
$\mathbf{Y}$ of rank at most $d$ and right-hand side $\mathbf{B}$, then for $t > 0$
$$\|\mathbf{B} - \mathbf{Y}\,\mathsf{sketchAndSolve}(\mathbf{Y}, \mathbf{S}, \mathbf{B})\|_{\mathsf{F}}^2
\le \Bigl(1 + \frac{t}{a}\Bigr)\|(\mathbf{I} - \mathbf{P}_{\mathbf{Y}})\mathbf{B}\|_{\mathsf{F}}^2$$
except with probability $\delta + 1/t$. The fixed-design form is
`NLAlib.IsObliviousSubspaceInjection.measure_frobNorm_sub_mul_pinv_mul_sq_gt_le`. It is the
completion step of generalized Nyström and its early-truncated form under a structured co-range
sketch. [CamanoEpperlyMeyerTropp2025, Theorem 2.7 and proof of Corollary 2.8]; there a fixed
design and probability $9/10$. Result: sketch-and-solve-ls -/
theorem IsObliviousSubspaceInjection.measure_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_indepFun
    [IsProbabilityMeasure μ] (h : IsObliviousSubspaceInjection S d a δ μ) (ha : 0 < a) (ht : 0 < t)
    {Y : Ω → Matrix n q 𝕜} {B : Ω → Matrix n r 𝕜} (hind : IndepFun S (fun ω => (Y ω, B ω)) μ)
    (hS : AEMeasurable S μ) (hY : AEMeasurable Y μ) (hB : AEMeasurable B μ)
    (hrank : ∀ᵐ ω ∂μ, (Y ω).rank ≤ d) :
    μ.real {ω | (1 + t / a) * frobNorm ((1 - rangeProjector (Y ω)) * B ω) ^ 2 <
      frobNorm (B ω - Y ω * sketchAndSolve (Y ω) (S ω) (B ω)) ^ 2} ≤ δ + 1 / t

/-- **Sketch-and-solve to relative error through approximate multiplication**: if the real
sketch $\mathbf{S}$ injects $\operatorname{range}\mathbf{A}$ with constant $a > 0$ except with
probability $\delta$ and has the $(\varepsilon, \delta', p)$ JL moment property, $\varepsilon > 0$,
$p \ge 2$, then
$$\|\mathbf{B} - \mathbf{A}\,\mathsf{sketchAndSolve}(\mathbf{A}, \mathbf{S}, \mathbf{B})\|_{\mathsf{F}}^2
\le \Bigl(1 + \frac{\operatorname{rank}(\mathbf{A})\,\varepsilon^2}{a^2}\Bigr)
\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{B}\|_{\mathsf{F}}^2$$
except with probability $\delta + \delta'$. Its rule-4 neighbour, constant factor $1 + t/a$ without
the moment, is `NLAlib.HasSubspaceInjection.measure_frobNorm_sub_mul_pinv_mul_sq_gt_le`; this one
reaches $1 + \varepsilon$. [Woodruff2014, Theorem 23]; there sparse embeddings, a vector
right-hand side and the unsquared objective; here any injection, a matrix right-hand side.
Result: sketch-and-solve-ls -/
theorem HasJLMoment.measure_frobNorm_sub_mul_sketchAndSolve_sq_gt_le [IsFiniteMeasure μ]
    {S : Ω → Matrix k n ℝ} {A : Matrix n q ℝ} {a δ ε δ' p : ℝ} (hJL : HasJLMoment S ε δ' p μ)
    (h : HasSubspaceInjection S A a δ μ) (hS : AEMeasurable S μ) (ha : 0 < a) (hε : 0 < ε)
    (hp : 2 ≤ p) (B : Matrix n r ℝ) :
    μ.real {ω | (1 + A.rank * ε ^ 2 / a ^ 2) * frobNorm ((1 - rangeProjector A) * B) ^ 2 <
      frobNorm (B - A * sketchAndSolve A (S ω) B) ^ 2} ≤ δ + δ'

/-- The random-design form of
`NLAlib.HasJLMoment.measure_frobNorm_sub_mul_sketchAndSolve_sq_gt_le`: for an OSI for dimension
$d$ independent of a design of rank at most $d$, the factor is $1 + d\varepsilon^2/a^2$ and the
failure probability $\delta + \delta'$. Result: sketch-and-solve-ls -/
theorem HasJLMoment.measure_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_indepFun
    [IsProbabilityMeasure μ] {S : Ω → Matrix k n ℝ} {d : ℕ} {a δ ε δ' p : ℝ}
    (hJL : HasJLMoment S ε δ' p μ) (h : IsObliviousSubspaceInjection S d a δ μ) (ha : 0 < a)
    (hε : 0 < ε) (hp : 2 ≤ p) {Y : Ω → Matrix n q ℝ} {B : Ω → Matrix n r ℝ}
    (hind : IndepFun S (fun ω => (Y ω, B ω)) μ) (hS : AEMeasurable S μ) (hY : AEMeasurable Y μ)
    (hB : AEMeasurable B μ) (hrank : ∀ᵐ ω ∂μ, (Y ω).rank ≤ d) :
    μ.real {ω | (1 + d * ε ^ 2 / a ^ 2) * frobNorm ((1 - rangeProjector (Y ω)) * B ω) ^ 2 <
      frobNorm (B ω - Y ω * sketchAndSolve (Y ω) (S ω) (B ω)) ^ 2} ≤ δ + δ'

/-- The randomized SVD does not see a nonzero scaling of the test matrix:
$\mathsf{rsvd}(\mathbf{A}, c\mathbf{\Omega}) = \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})$. -/
theorem rsvd_smul_right (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) {c : 𝕜} (hc : c ≠ 0) :
    rsvd A (c • Ω) = rsvd A Ω

/-- Truncation does not increase the Frobenius norm:
$\|\llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}} \le \|\mathbf{A}\|_{\mathsf{F}}$. -/
theorem frobNorm_truncatedSVD_le (A : Matrix m n 𝕜) (k : ℕ) :
    frobNorm (truncatedSVD A k) ≤ frobNorm A
```

Proof routes. *L1:* a basis $\mathbf{Q}$ of $\operatorname{range}\mathbf{A}$
(`exists_hasOrthonormalCols_range_eq`), the injection transferred to it, `obliqueProjector_eq_of_range_eq`
(rank hypothesis from `rank_mul_eq`); $\mathbf{\Pi}\mathbf{Y} = \mathbf{Q}\mathbf{G}^{-1}
\mathbf{Q}^{\mathsf{H}}\mathbf{S}^{\mathsf{H}}\mathbf{S}\mathbf{Y}$ with $\mathbf{G} =
(\mathbf{S}\mathbf{Q})^{\mathsf{H}}\mathbf{S}\mathbf{Q} \succeq a\mathbf{I}$
(`HasOrthonormalCols.isSubspaceInjection_iff`), then `matrixNorm_mul_left_of_hasOrthonormalCols`,
`matrixNorm_mul_le_specNorm_mul` with $\|\mathbf{G}^{-1}\|_2 \le 1/a$, and
$\|\mathbf{Q}^{\mathsf{H}}\mathbf{W}\|_{\Phi} = \|\mathbf{Q}\mathbf{Q}^{\mathsf{H}}\mathbf{W}\|_{\Phi}$.
S1's `IsSubspaceInjection.matrixNorm_sub_mul_mul_pinv_le` is this bound in the frame orientation; L1
is not derived from it because S1's form needs a frame. About 40 lines. *L2:* common step 4 with
the fixed-design `IsObliviousSubspaceInjection.measure_frobNorm_sub_mul_pinv_mul_sq_gt_le`, whose
`Y - A * (pinv (S ω * A) * (S ω * Y))` is `B - Y * sketchAndSolve Y S B` by unfolding; about 35.
*L3:* on the injection event `frobNorm_one_sub_obliqueProjector_mul_sq` (with `mul_sketchAndSolve`)
splits the error into $\|\mathbf{C}\|^2 + \|\mathbf{\Pi}\mathbf{C}\|^2$, $\mathbf{C} = (\mathbf{I} -
\mathbf{P}_{\mathbf{A}})\mathbf{B}$; L1 at the Frobenius gauge and $\mathbf{P}_{\mathbf{A}}\mathbf{C} =
\mathbf{0}$ give $\|\mathbf{\Pi}\mathbf{C}\|_{\mathsf{F}} \le \|\mathbf{P}_{\mathbf{A}}^{\mathsf{H}}
\mathbf{S}^{\mathsf{H}}\mathbf{S}\mathbf{C} - \mathbf{P}_{\mathbf{A}}^{\mathsf{H}}\mathbf{C}\|_{\mathsf{F}}/a$;
the JL multiplication tail at $(\mathbf{P}_{\mathbf{A}}, \mathbf{C})$ with $\|\mathbf{P}_{\mathbf{A}}
\|_{\mathsf{F}}^2 = \operatorname{rank}\mathbf{A}$ (`frobNorm_rangeProjector_sq`) bounds it by
$\varepsilon\sqrt{\operatorname{rank}\mathbf{A}}\,\|\mathbf{C}\|_{\mathsf{F}}$ outside $\delta'$
($\mathbf{C} = \mathbf{0}$ or $\mathbf{A} = \mathbf{0}$: the event is empty); union step. About 45.
*L4:* common step 4 with L3 at fixed $(\mathbf{y}, \mathbf{b})$, `h.hasSubspaceInjection` and
$\operatorname{rank}\mathbf{y} \le d$ in the factor; about 30. *L5:* `sub_rsvd`, `Matrix.mul_smul`,
`rangeProjector_smul`; 5. *L6:* `frobNorm_truncatedSVD_sq` against the sum of all squared singular
values; S6's private real copy is replaced (§4 flags); 10.

### 3.2 `LowRank/Oblivious/RangeFinder.lean`: the randomized SVD and Nyström (13)

Labels A1 to A13. A1 to A5, A8 over `𝕜`; A6, A7, A13 real.

```lean
/-- **The tail of the randomized SVD under a subspace injection, Gram form**: if
$\mathbf{\Omega}^{\mathsf{H}}$ is isotropic and injects
$\operatorname{range}\llbracket\mathbf{A}\rrbracket_k^{\mathsf{H}}$ with constant $a > 0$ except
with probability $\delta$, then for every unitarily invariant norm and $t > 0$, with
$\mathbf{E} = \mathbf{A} - \llbracket\mathbf{A}\rrbracket_k$,
$$\bigl\|(\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega}))^{\mathsf{H}}
(\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega}))\bigr\|_{\Phi} \le
\|\mathbf{E}^{\mathsf{H}}\mathbf{E}\|_{\Phi} + \Phi(\mathbf{e}_0)\,\frac{t}{a}\,
\|\mathbf{E}\|_{\mathsf{F}}^2$$
except with probability $\delta + 1/t$, with $\mathbf{e}_0$ the first unit coordinate sequence.
An OSI for dimension $k$ supplies both hypotheses. [CamanoEpperlyMeyerTropp2025, Theorem 2.2];
there an OSI, Frobenius norm, $C/\alpha$ with probability $9/10$; here one fixed subspace, every
quadratic unitarily invariant norm, the factor and the failure probability explicit in $t$; the
shape of [TroppWebber2023, Theorem 8.1 (RSVD1)]. Result: randomized-svd-tail -/
theorem HasSubspaceInjection.measure_matrixNorm_conjTranspose_mul_self_sub_rsvd_gt_le
    [IsFiniteMeasure μ] {A : Matrix m n 𝕜} {k : ℕ} {a δ t : ℝ}
    (h : HasSubspaceInjection (fun ω => (X ω)ᴴ) (truncatedSVD A k)ᴴ a δ μ)
    (hiso : IsIsotropicSketch (fun ω => (X ω)ᴴ) μ) (ha : 0 < a) (ht : 0 < t)
    (Φ : SymmetricGauge) :
    μ.real {ω | Φ.matrixNorm ((A - truncatedSVD A k)ᴴ * (A - truncatedSVD A k)) +
        Φ (Finsupp.single 0 1) * (t / a) * frobNorm (A - truncatedSVD A k) ^ 2 <
      Φ.matrixNorm ((A - rsvd A (X ω))ᴴ * (A - rsvd A (X ω)))} ≤ δ + 1 / t

/-- **The randomized SVD with an oblivious subspace injection** (CEMT's theorem): with the
hypotheses of the Gram form above, for $t > 0$
$$\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_{\mathsf{F}}^2 \le
\Bigl(1 + \frac{t}{a}\Bigr)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta + 1/t$. [CamanoEpperlyMeyerTropp2025, Theorem 2.2]; there
$C/\alpha$ at $9/10$. Result: randomized-svd-tail -/
theorem HasSubspaceInjection.measure_frobNorm_sub_rsvd_sq_gt_le [IsFiniteMeasure μ]
    {A : Matrix m n 𝕜} {k : ℕ} {a δ t : ℝ}
    (h : HasSubspaceInjection (fun ω => (X ω)ᴴ) (truncatedSVD A k)ᴴ a δ μ)
    (hiso : IsIsotropicSketch (fun ω => (X ω)ᴴ) μ) (ha : 0 < a) (ht : 0 < t) :
    μ.real {ω | (1 + t / a) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - rsvd A (X ω)) ^ 2} ≤ δ + 1 / t

/-- The spectral form: $\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_2^2 \le
\sigma_k(\mathbf{A})^2 + \frac{t}{a}\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$
except with probability $\delta + 1/t$; the bounded-sketch neighbour, without the Frobenius
term, is `NLAlib.HasSubspaceInjection.measure_matrixNorm_conjTranspose_mul_self_sub_rsvd_gt_le_of_specNorm_le`.
Result: randomized-svd-tail -/
theorem HasSubspaceInjection.measure_specNorm_sub_rsvd_sq_gt_le [IsFiniteMeasure μ]
    {A : Matrix m n 𝕜} {k : ℕ} {a δ t : ℝ}
    (h : HasSubspaceInjection (fun ω => (X ω)ᴴ) (truncatedSVD A k)ᴴ a δ μ)
    (hiso : IsIsotropicSketch (fun ω => (X ω)ᴴ) μ) (ha : 0 < a) (ht : 0 < t) :
    μ.real {ω | singularValues A k ^ 2 + t / a * frobNorm (A - truncatedSVD A k) ^ 2 <
      specNorm (A - rsvd A (X ω)) ^ 2} ≤ δ + 1 / t

/-- **The rank-$k$ randomized SVD with an injection**: the bound of
`NLAlib.HasSubspaceInjection.measure_frobNorm_sub_rsvd_sq_gt_le` holds for
$\llbracket\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\rrbracket_k$ with the same constant.
[CamanoEpperlyMeyerTropp2025, remark after Theorem 1.3]; there by HMT Theorem 9.3, which is
spectral only; here in Frobenius norm by [Woodruff2014, Lemma 48]'s competitor.
Result: randomized-svd-tail -/
theorem HasSubspaceInjection.measure_frobNorm_sub_truncatedSVD_rsvd_sq_gt_le [IsFiniteMeasure μ]
    {A : Matrix m n 𝕜} {k : ℕ} {a δ t : ℝ}
    (h : HasSubspaceInjection (fun ω => (X ω)ᴴ) (truncatedSVD A k)ᴴ a δ μ)
    (hiso : IsIsotropicSketch (fun ω => (X ω)ᴴ) μ) (ha : 0 < a) (ht : 0 < t) :
    μ.real {ω | (1 + t / a) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2} ≤ δ + 1 / t

/-- **The randomized SVD with a bounded sketch**: if $\mathbf{\Omega}^{\mathsf{H}}$ injects
$\operatorname{range}\llbracket\mathbf{A}\rrbracket_k^{\mathsf{H}}$ with constant $a > 0$ except
with probability $\delta$ and $\|\mathbf{\Omega}\|_2 \le L$ almost surely, then for every unitarily
invariant norm
$$\bigl\|(\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega}))^{\mathsf{H}}
(\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega}))\bigr\|_{\Phi} \le
\Bigl(1 + \frac{L^2}{a}\Bigr)\|\mathbf{E}^{\mathsf{H}}\mathbf{E}\|_{\Phi}$$
except with probability $\delta$; in spectral norm the right side is
$(1 + L^2/a)\sigma_k(\mathbf{A})^2$. No isotropy and no Markov step. [HalkoMartinssonTropp2011,
Theorem 11.2]; there SRFT, $L^2 = n/\ell$, factor $1 + 7n/\ell$ in spectral and Frobenius norm,
failure $O(k^{-1})$; here any sketch, every quadratic norm. Result: randomized-svd-tail -/
theorem
    HasSubspaceInjection.measure_matrixNorm_conjTranspose_mul_self_sub_rsvd_gt_le_of_specNorm_le
    {A : Matrix m n 𝕜} {k : ℕ} {a δ L : ℝ}
    (h : HasSubspaceInjection (fun ω => (X ω)ᴴ) (truncatedSVD A k)ᴴ a δ μ) (ha : 0 < a)
    (hL : ∀ᵐ ω ∂μ, specNorm (X ω) ≤ L) (Φ : SymmetricGauge) :
    μ.real {ω | (1 + L ^ 2 / a) *
        Φ.matrixNorm ((A - truncatedSVD A k)ᴴ * (A - truncatedSVD A k)) <
      Φ.matrixNorm ((A - rsvd A (X ω))ᴴ * (A - rsvd A (X ω)))} ≤ δ

/-- **The randomized SVD to relative error through approximate multiplication**: if the real
sketch $\mathbf{\Omega}^{\mathsf{H}}$ injects $\operatorname{range}\llbracket\mathbf{A}\rrbracket_k^{\mathsf{H}}$
with constant $a > 0$ except with probability $\delta$ and has the $(\varepsilon, \delta', p)$ JL
moment property, $\varepsilon > 0$, $p \ge 2$, then
$$\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_{\mathsf{F}}^2 \le
\Bigl(1 + \frac{k\varepsilon^2}{a^2}\Bigr)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta + \delta'$. Its rule-4 neighbour without the moment is
`NLAlib.HasSubspaceInjection.measure_frobNorm_sub_rsvd_sq_gt_le`, constant factor; this one
reaches $1 + \varepsilon$ at $\ell = O(k/(\varepsilon\delta'))$. [Woodruff2014, Lemma 45]; there
constants $1 \pm 1/3$ and the $(\sqrt{\varepsilon/k}, 9/10, \ell)$ moment; here any injection
constant, explicit. Result: randomized-svd-tail -/
theorem HasJLMoment.measure_frobNorm_sub_rsvd_sq_gt_le {A : Matrix m n ℝ} {k : ℕ}
    {a δ ε δ' p : ℝ} (hJL : HasJLMoment (fun ω => (X ω)ᴴ) ε δ' p μ)
    (h : HasSubspaceInjection (fun ω => (X ω)ᴴ) (truncatedSVD A k)ᴴ a δ μ)
    (hX : AEMeasurable X μ) (ha : 0 < a) (hε : 0 < ε) (hp : 2 ≤ p) :
    μ.real {ω | (1 + k * ε ^ 2 / a ^ 2) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - rsvd A (X ω)) ^ 2} ≤ δ + δ'

/-- Its rank-$k$ form, for $\llbracket\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\rrbracket_k$, the
same constant. [Woodruff2014, Lemmas 44 and 45]. Result: randomized-svd-tail -/
theorem HasJLMoment.measure_frobNorm_sub_truncatedSVD_rsvd_sq_gt_le {A : Matrix m n ℝ} {k : ℕ}
    {a δ ε δ' p : ℝ} (hJL : HasJLMoment (fun ω => (X ω)ᴴ) ε δ' p μ)
    (h : HasSubspaceInjection (fun ω => (X ω)ᴴ) (truncatedSVD A k)ᴴ a δ μ)
    (hX : AEMeasurable X μ) (ha : 0 < a) (hε : 0 < ε) (hp : 2 ≤ p) :
    μ.real {ω | (1 + k * ε ^ 2 / a ^ 2) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2} ≤ δ + δ'

/-- **The rank-$k$ randomized SVD through an approximate-multiplication tail**, any field: if
$\mathbf{\Omega}^{\mathsf{H}}$ injects the head with constant $a > 0$ except with probability
$\delta$, and the tail–head error
$\|\mathbf{E}\mathbf{\Omega}\mathbf{\Omega}^{\mathsf{H}}\mathbf{P}_{\llbracket\mathbf{A}\rrbracket_k^{\mathsf{H}}}\|_{\mathsf{F}}$
exceeds $\eta$ with probability at most $\delta'$, then
$$\|\mathbf{A} - \llbracket\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\rrbracket_k\|_{\mathsf{F}}^2 \le
\|\mathbf{E}\|_{\mathsf{F}}^2 + \frac{\eta^2}{a^2}$$
except with probability $\delta + \delta'$, and so does the error of
$\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})$, which is smaller. The form a family with its own
multiplication tail uses (CountSketch over `𝕜`); the JL-moment forms above are its real
corollaries. [Woodruff2014, proof of Lemma 45]. Result: randomized-svd-tail -/
theorem HasSubspaceInjection.measure_frobNorm_sub_truncatedSVD_rsvd_sq_gt_add_le
    {A : Matrix m n 𝕜} {k : ℕ} {a δ η δ' : ℝ}
    (h : HasSubspaceInjection (fun ω => (X ω)ᴴ) (truncatedSVD A k)ᴴ a δ μ) (ha : 0 < a)
    (hχ : μ.real {ω | η < frobNorm ((A - truncatedSVD A k) * X ω * (X ω)ᴴ *
      rangeProjector (truncatedSVD A k)ᴴ)} ≤ δ') :
    μ.real {ω | frobNorm (A - truncatedSVD A k) ^ 2 + η ^ 2 / a ^ 2 <
      frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2} ≤ δ + δ'

/-- **Randomized Nyström with an oblivious subspace injection**, trace norm: for positive
semidefinite $\mathbf{H}$ and an OSI $\mathbf{\Omega}^{\mathsf{H}}$ for dimension $k$ with constant
$a > 0$ and failure probability $\delta$, for $t > 0$
$$\|\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{\Omega})\|_* \le
\Bigl(1 + \frac{t}{a}\Bigr)\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_*$$
except with probability $\delta + 1/t$. [CamanoEpperlyMeyerTropp2025, Corollary 2.5]; there
$C/\alpha$ at $9/10$. Result: randomized-nystrom-tail -/
theorem IsObliviousSubspaceInjection.measure_nuclearNorm_sub_nystrom_gt_le [IsFiniteMeasure μ]
    {H : Matrix n n 𝕜} (hH : H.PosSemidef) {k : ℕ} {a δ t : ℝ}
    (h : IsObliviousSubspaceInjection (fun ω => (X ω)ᴴ) k a δ μ) (ha : 0 < a) (ht : 0 < t) :
    μ.real {ω | (1 + t / a) * nuclearNorm (H - truncatedSVD H k) <
      nuclearNorm (H - nystrom H (X ω))} ≤ δ + 1 / t

/-- Every unitarily invariant norm:
$\|\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{\Omega})\|_{\Phi} \le
\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_{\Phi} + \Phi(\mathbf{e}_0)\frac{t}{a}
\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_*$ except with probability $\delta + 1/t$, the
Gram correspondence applied to the Gram form. Result: randomized-nystrom-tail -/
theorem IsObliviousSubspaceInjection.measure_matrixNorm_sub_nystrom_gt_le [IsFiniteMeasure μ]
    {H : Matrix n n 𝕜} (hH : H.PosSemidef) {k : ℕ} {a δ t : ℝ}
    (h : IsObliviousSubspaceInjection (fun ω => (X ω)ᴴ) k a δ μ) (ha : 0 < a) (ht : 0 < t)
    (Φ : SymmetricGauge) :
    μ.real {ω | Φ.matrixNorm (H - truncatedSVD H k) +
        Φ (Finsupp.single 0 1) * (t / a) * nuclearNorm (H - truncatedSVD H k) <
      Φ.matrixNorm (H - nystrom H (X ω))} ≤ δ + 1 / t

/-- Spectral norm: $\|\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{\Omega})\|_2 \le
\lambda_k(\mathbf{H}) + \frac{t}{a}\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_*$ except with
probability $\delta + 1/t$ (the eigenvalue written as `singularValues H k`). The form a Nyström
preconditioner consumes. Result: randomized-nystrom-tail -/
theorem IsObliviousSubspaceInjection.measure_specNorm_sub_nystrom_gt_le [IsFiniteMeasure μ]
    {H : Matrix n n 𝕜} (hH : H.PosSemidef) {k : ℕ} {a δ t : ℝ}
    (h : IsObliviousSubspaceInjection (fun ω => (X ω)ᴴ) k a δ μ) (ha : 0 < a) (ht : 0 < t) :
    μ.real {ω | singularValues H k + t / a * nuclearNorm (H - truncatedSVD H k) <
      specNorm (H - nystrom H (X ω))} ≤ δ + 1 / t

/-- Truncated Nyström, trace norm: the bound of
`NLAlib.IsObliviousSubspaceInjection.measure_nuclearNorm_sub_nystrom_gt_le` holds for
$\llbracket\mathsf{nystrom}(\mathbf{H}, \mathbf{\Omega})\rrbracket_k$.
[CamanoEpperlyMeyerTropp2025, remark after Theorem 1.3]. Result: randomized-nystrom-tail -/
theorem IsObliviousSubspaceInjection.measure_nuclearNorm_sub_truncatedSVD_nystrom_gt_le
    [IsFiniteMeasure μ] {H : Matrix n n 𝕜} (hH : H.PosSemidef) {k : ℕ} {a δ t : ℝ}
    (h : IsObliviousSubspaceInjection (fun ω => (X ω)ᴴ) k a δ μ) (ha : 0 < a) (ht : 0 < t) :
    μ.real {ω | (1 + t / a) * nuclearNorm (H - truncatedSVD H k) <
      nuclearNorm (H - truncatedSVD (nystrom H (X ω)) k)} ≤ δ + 1 / t

/-- Nyström to relative error through approximate multiplication, trace norm: factor
$1 + k\varepsilon^2/a^2$, failure probability $\delta + \delta'$.
[Woodruff2014, Lemma 45] through [CamanoEpperlyMeyerTropp2025, Imported Theorem 2.4].
Result: randomized-nystrom-tail -/
theorem HasJLMoment.measure_nuclearNorm_sub_nystrom_gt_le {H : Matrix n n ℝ} (hH : H.PosSemidef)
    {k : ℕ} {a δ ε δ' p : ℝ} (hJL : HasJLMoment (fun ω => (X ω)ᴴ) ε δ' p μ)
    (h : IsObliviousSubspaceInjection (fun ω => (X ω)ᴴ) k a δ μ) (hX : AEMeasurable X μ)
    (ha : 0 < a) (hε : 0 < ε) (hp : 2 ≤ p) :
    μ.real {ω | (1 + k * ε ^ 2 / a ^ 2) * nuclearNorm (H - truncatedSVD H k) <
      nuclearNorm (H - nystrom H (X ω))} ≤ δ + δ'
```

Proof routes. *A1:* common steps 1 to 3: on the injection event, S1's
`SymmetricGauge.matrixNorm_conjTranspose_mul_self_sub_rsvd_le`; its second term is at most
$\Phi(\mathbf{e}_0)\|\mathbf{M}\|_{\mathsf{F}}^2$ (`matrixNorm_le_apply_single_mul_nuclearNorm`,
`nuclearNorm_conjTranspose_mul_self`), and $\|\mathbf{M}\|_{\mathsf{F}}^2 \le
\|\mathbf{E}\mathbf{\Omega}\|_{\mathsf{F}}^2/a$ (`IsSubspaceInjection.frobNorm_mul_pinv_sq_le` at
$\mathbf{S} = \mathbf{\Omega}^{\mathsf{H}}$, $\mathbf{U} = \mathbf{Z}$); the Markov event carries the
$1/t$. About 45 lines. *A2:* A1 at `lpGauge 1` (`lpGauge_one_matrixNorm`, $\Phi(\mathbf{e}_0) = 1$),
or directly from `IsSubspaceInjection.frobNorm_sub_rsvd_sq_le`; 10. *A3:* A1 at the spectral gauge,
`specNorm_sub_truncatedSVD`; 10. *A4:* as A2 through `HasOrthonormalCols.frobNorm_sub_truncatedSVD_rsvd_sq_le`
(width $r \le k$); 20. *A5:* on the injection event and $\|\mathbf{\Omega}\|_2 \le L$:
$\sigma_i(\mathbf{M}) \le \sigma_i(\mathbf{E})\,L\,\|(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^{+}\|_2$
(`singularValues_mul_le_mul_specNorm` twice) with $\|(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^{+}\|_2^2
\le 1/a$ (`specNorm_pinv_sq_le_inv_of_smul_one_le`, `specNorm_conjTranspose`), so
$\Phi(\mathbf{M}^{\mathsf{H}}\mathbf{M}) \le (L^2/a)\Phi(\mathbf{E}^{\mathsf{H}}\mathbf{E})$
(`matrixNorm_le_of_singularValues_le`); the null event $\{L < \|\mathbf{\Omega}\|_2\}$ adds nothing.
About 45. *A8:* common step 1, S1's truncated competitor bound, S1's
`IsSubspaceInjection.matrixNorm_sub_mul_mul_pinv_le` at the Frobenius gauge (`lpGauge 2 one_le_two`,
as S1 anticipates), $\mathbf{E}\mathbf{Z} = \mathbf{0}$ and
$\|\mathbf{W}\mathbf{Z}\|_{\mathsf{F}} = \|\mathbf{W}\mathbf{Z}\mathbf{Z}^{\mathsf{H}}\|_{\mathsf{F}}$; union
step. About 35. *A6, A7:* A8 with $\eta = \varepsilon\sqrt{k}\,\mathrm{OPT}$: the JL multiplication
tail at $(\mathbf{E}^{\mathsf{H}}, \mathbf{P}_{\llbracket\mathbf{A}\rrbracket_k^{\mathsf{H}}})$, whose
squared Frobenius norm is the rank $\le k$; A6 also uses T3 (the rank-$k$ error dominates). About
15 each. *A9 to A12:* $\mathbf{H} = \mathbf{F}^{\mathsf{H}}\mathbf{F}$
(`CStarAlgebra.nonneg_iff_eq_star_mul_self`, as S5), `conjTranspose_mul_self_sub_nystrom` and
`nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD` (and their gauge forms), then A2, A1, A3, A4 at
$\mathbf{F}$ with `h.hasSubspaceInjection` at $\llbracket\mathbf{F}\rrbracket_k^{\mathsf{H}}$ and
`h.isotropic`; A12 through `nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD_nystrom`. About 10
each. *A13:* A6 at $\mathbf{F}$; 10.

### 3.3 `LowRank/Oblivious/GeneralizedNystrom.lean`: generalized Nyström (5)

Labels B1 to B5. B1 to B3 over `𝕜`; B4, B5 real.

```lean
/-- **Generalized Nyström = randomized SVD × completion, structured co-range sketch**: for any
law of $\mathbf{\Omega}$ and an independent co-range test matrix $\mathbf{\Psi}$ whose
$\mathbf{\Psi}^{\mathsf{H}}$ is an OSI for dimension $d \ge \min(\operatorname{rank}\mathbf{A}, \ell)$
with constant $a > 0$ and failure probability $\delta$, for $t > 0$
$$\|\mathbf{A} - \mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})\|_{\mathsf{F}}^2 \le
\Bigl(1 + \frac{t}{a}\Bigr)\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_{\mathsf{F}}^2$$
except with probability $\delta + 1/t$. Any range-finder tail (S3's Gaussian tail, the injection
forms, a sampling bound) composes with it. [CamanoEpperlyMeyerTropp2025, proof of
Corollary 2.8]. Result: generalized-nystrom-tail -/
theorem IsObliviousSubspaceInjection.measure_frobNorm_sub_generalizedNystrom_sq_gt_mul_le
    [IsProbabilityMeasure μ] {A : Matrix m n 𝕜} {d : ℕ} {a δ t : ℝ}
    (h : IsObliviousSubspaceInjection (fun ω => (Ψ ω)ᴴ) d a δ μ)
    (hd : min A.rank (Fintype.card l) ≤ d) (hind : IndepFun X Ψ μ) (hX : AEMeasurable X μ)
    (hΨ : AEMeasurable Ψ μ) (ha : 0 < a) (ht : 0 < t) :
    μ.real {ω | (1 + t / a) * frobNorm (A - rsvd A (X ω)) ^ 2 <
      frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2} ≤ δ + 1 / t

/-- **Generalized Nyström with oblivious subspace injections**: with the range side of
`NLAlib.HasSubspaceInjection.measure_frobNorm_sub_rsvd_sq_gt_le` (constant $a$, failure $\delta$,
parameter $t$) and the co-range side of
`NLAlib.IsObliviousSubspaceInjection.measure_frobNorm_sub_generalizedNystrom_sq_gt_mul_le`
(constant $a'$, failure $\delta'$, parameter $t'$),
$$\|\mathbf{A} - \mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})\|_{\mathsf{F}}^2 \le
\Bigl(1 + \frac{t'}{a'}\Bigr)\Bigl(1 + \frac{t}{a}\Bigr)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta + 1/t + \delta' + 1/t'$. One pass.
[CamanoEpperlyMeyerTropp2025, Corollary 2.8]; there $(C/\alpha)^2$ at $4/5$, over $\mathbb{R}$,
$\mathbf{\Psi}$ an OSI for dimension $\ell$; here over `𝕜`, dimension
$\min(\operatorname{rank}\mathbf{A}, \ell)$ suffices. Result: generalized-nystrom-tail -/
theorem HasSubspaceInjection.measure_frobNorm_sub_generalizedNystrom_sq_gt_le
    [IsProbabilityMeasure μ] {A : Matrix m n 𝕜} {k d : ℕ} {a δ t a' δ' t' : ℝ}
    (h : HasSubspaceInjection (fun ω => (X ω)ᴴ) (truncatedSVD A k)ᴴ a δ μ)
    (hiso : IsIsotropicSketch (fun ω => (X ω)ᴴ) μ)
    (hΨ : IsObliviousSubspaceInjection (fun ω => (Ψ ω)ᴴ) d a' δ' μ)
    (hd : min A.rank (Fintype.card l) ≤ d) (hind : IndepFun X Ψ μ) (hX : AEMeasurable X μ)
    (hΨm : AEMeasurable Ψ μ) (ha : 0 < a) (ht : 0 < t) (ha' : 0 < a') (ht' : 0 < t') :
    μ.real {ω | (1 + t' / a') * (1 + t / a) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2} ≤ δ + 1 / t + (δ' + 1 / t')

/-- **Late-truncated generalized Nyström with oblivious subspace injections**: with the
hypotheses of `NLAlib.HasSubspaceInjection.measure_frobNorm_sub_generalizedNystrom_sq_gt_le`,
$$\|\mathbf{A} - \llbracket\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})\rrbracket_k
\|_{\mathsf{F}}^2 \le \Bigl(1 + 2\sqrt{t'/a'}\Bigr)^2\Bigl(1 + \frac{t}{a}\Bigr)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta + 1/t + \delta' + 1/t'$; a rank-$k$ single-pass output with a
constant factor. Proved without a literature source; [CamanoEpperlyMeyerTropp2025, Remark 2.9]
discusses a different, core-truncated estimator. Result: generalized-nystrom-tail -/
theorem HasSubspaceInjection.measure_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_gt_le
    [IsProbabilityMeasure μ] {A : Matrix m n 𝕜} {k d : ℕ} {a δ t a' δ' t' : ℝ}
    (h : HasSubspaceInjection (fun ω => (X ω)ᴴ) (truncatedSVD A k)ᴴ a δ μ)
    (hiso : IsIsotropicSketch (fun ω => (X ω)ᴴ) μ)
    (hΨ : IsObliviousSubspaceInjection (fun ω => (Ψ ω)ᴴ) d a' δ' μ)
    (hd : min A.rank (Fintype.card l) ≤ d) (hind : IndepFun X Ψ μ) (hX : AEMeasurable X μ)
    (hΨm : AEMeasurable Ψ μ) (ha : 0 < a) (ht : 0 < t) (ha' : 0 < a') (ht' : 0 < t') :
    μ.real {ω | (1 + 2 * √(t' / a')) ^ 2 * (1 + t / a) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - truncatedSVD (generalizedNystrom A (X ω) (Ψ ω)) k) ^ 2} ≤
      δ + 1 / t + (δ' + 1 / t')

/-- The completion through approximate multiplication: for any law of $\mathbf{\Omega}$ and an
independent real $\mathbf{\Psi}$ whose $\mathbf{\Psi}^{\mathsf{H}}$ is an OSI for dimension
$d \ge \min(\operatorname{rank}\mathbf{A}, \ell)$ (constant $a$, failure $\delta$) with the
$(\varepsilon, \delta', p)$ JL moment property,
$\|\mathbf{A} - \mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})\|_{\mathsf{F}}^2 \le
(1 + d\varepsilon^2/a^2)\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_{\mathsf{F}}^2$
except with probability $\delta + \delta'$. [Woodruff2014, proof of Theorem 47].
Result: generalized-nystrom-tail -/
theorem HasJLMoment.measure_frobNorm_sub_generalizedNystrom_sq_gt_mul_le [IsProbabilityMeasure μ]
    {A : Matrix m n ℝ} {d : ℕ} {a δ ε δ' p : ℝ} (hJL : HasJLMoment (fun ω => (Ψ ω)ᴴ) ε δ' p μ)
    (h : IsObliviousSubspaceInjection (fun ω => (Ψ ω)ᴴ) d a δ μ)
    (hd : min A.rank (Fintype.card l) ≤ d) (hind : IndepFun X Ψ μ) (hX : AEMeasurable X μ)
    (hΨ : AEMeasurable Ψ μ) (ha : 0 < a) (hε : 0 < ε) (hp : 2 ≤ p) :
    μ.real {ω | (1 + d * ε ^ 2 / a ^ 2) * frobNorm (A - rsvd A (X ω)) ^ 2 <
      frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2} ≤ δ + δ'

/-- **Generalized Nyström to relative error**: both sides through approximate multiplication,
$$\|\mathbf{A} - \mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})\|_{\mathsf{F}}^2 \le
\Bigl(1 + \frac{d\varepsilon'^2}{a'^2}\Bigr)\Bigl(1 + \frac{k\varepsilon^2}{a^2}\Bigr)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta + \delta_1 + \delta' + \delta_2$; $1 + \varepsilon$ at
$\ell = O(k/\varepsilon)$ and $p = O(\ell/\varepsilon)$ at constant failure probability.
[Woodruff2014, Theorem 47, first part]; there $\mathbf{R}$ a $(1 + O(\varepsilon))$ embedding of the
row space of $\mathbf{S}\mathbf{A}$ and the multiplication step implicit; here explicit.
Result: generalized-nystrom-tail -/
theorem HasJLMoment.measure_frobNorm_sub_generalizedNystrom_sq_gt_le [IsProbabilityMeasure μ]
    {A : Matrix m n ℝ} {k d : ℕ} {a δ ε δ₁ p a' δ' ε' δ₂ p' : ℝ}
    (hJL : HasJLMoment (fun ω => (X ω)ᴴ) ε δ₁ p μ)
    (h : HasSubspaceInjection (fun ω => (X ω)ᴴ) (truncatedSVD A k)ᴴ a δ μ)
    (hJLΨ : HasJLMoment (fun ω => (Ψ ω)ᴴ) ε' δ₂ p' μ)
    (hΨ : IsObliviousSubspaceInjection (fun ω => (Ψ ω)ᴴ) d a' δ' μ)
    (hd : min A.rank (Fintype.card l) ≤ d) (hind : IndepFun X Ψ μ) (hX : AEMeasurable X μ)
    (hΨm : AEMeasurable Ψ μ) (ha : 0 < a) (hε : 0 < ε) (hp : 2 ≤ p) (ha' : 0 < a')
    (hε' : 0 < ε') (hp' : 2 ≤ p') :
    μ.real {ω | (1 + d * ε' ^ 2 / a' ^ 2) * (1 + k * ε ^ 2 / a ^ 2) *
        frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2} ≤ δ + δ₁ + (δ' + δ₂)
```

Proof routes. *B1:* L2 at $\mathbf{S} = \mathbf{\Psi}^{\mathsf{H}}$, $\mathbf{Y} =
\mathbf{A}\mathbf{\Omega}$, $\mathbf{B} = \mathbf{A}$ (a constant); independence of
$\mathbf{\Psi}^{\mathsf{H}}$ and the pair by composing `hind.symm` with measurable maps; rank of
$\mathbf{A}\mathbf{\Omega}$ at most $\min(\operatorname{rank}\mathbf{A}, \ell)$ surely
(`Matrix.rank_mul_le_left`, `rank_mul_le_right`, `Matrix.rank_le_card_width`); `sub_rsvd`,
`sub_generalizedNystrom`, `mul_sketchAndSolve` identify the two sides. About 25. *B2:* union of
A2's event and B1's; on both good events multiply. About 20. *B3:* T10 bounds the error by
$u^2 + (v + 2w)^2$ with $u = \|\mathbf{A} - \mathsf{rsvd}\|_{\mathsf{F}}$, $v =
\|\mathsf{rsvd} - \llbracket\mathsf{rsvd}\rrbracket_k\|_{\mathsf{F}}$ and $w \le
\|\mathbf{\Pi}(\mathbf{A} - \mathsf{rsvd})\|_{\mathsf{F}}$ (L6); on B1's good event
$\|\mathbf{\Pi}(\mathbf{A} - \mathsf{rsvd})\|_{\mathsf{F}}^2 \le (t'/a')u^2$
(`frobNorm_sub_generalizedNystrom_sq`); with $c = 2\sqrt{t'/a'}$,
$u^2 + (v + cu)^2 \le (\sqrt{u^2 + v^2} + cu)^2 \le (1 + c)^2(u^2 + v^2)$; T3 makes
$u^2 + v^2 = \|\mathbf{A} - \llbracket\mathsf{rsvd}\rrbracket_k\|_{\mathsf{F}}^2$, bounded on A4's good
event. About 40. *B4:* L4 as B1 uses L2; 20. *B5:* union of A6's and B4's events; 20.

### 3.4 `LowRank/Oblivious/EarlyTruncation.lean`: early truncation (6)

Labels C1 to C6. C1, C2, C4 over `𝕜`; C3, C5, C6 real. S9 appends its U1, U2 in a final section
(§4, Q9). (The S9 draft's own labels C1 to C7 are for its `ProjectionCost.lean` statements; this
note always writes "the S9 draft's C4" for those.)

```lean
/-- **Early truncation from a head injection and approximate-multiplication tails, any optimal
projector**: if $\mathbf{\Omega}^{\mathsf{H}}$ injects
$\operatorname{range}\llbracket\mathbf{A}\rrbracket_k^{\mathsf{H}}$ with constant $0 < a \le 1$
except with probability $\delta$, the tail–tail error
$\|\mathbf{E}\mathbf{\Omega}\mathbf{\Omega}^{\mathsf{H}}\mathbf{E}^{\mathsf{H}} -
\mathbf{E}\mathbf{E}^{\mathsf{H}}\|_{\mathsf{F}}$ exceeds $\eta_w$ with probability at most
$\delta_w$ and the tail–head error
$\|\mathbf{E}\mathbf{\Omega}\mathbf{\Omega}^{\mathsf{H}}\mathbf{P}_{\llbracket\mathbf{A}\rrbracket_k^{\mathsf{H}}}\|_{\mathsf{F}}$
exceeds $\eta_\chi$ with probability at most $\delta_\chi$, then for every random orthogonal
projector $\mathbf{P}$ of rank at most $k$ at least as good on the sketch as the head,
$\|\mathbf{A}\mathbf{\Omega} - \mathbf{P}\mathbf{A}\mathbf{\Omega}\|_{\mathsf{F}} \le
\|\mathbf{E}\mathbf{\Omega}\|_{\mathsf{F}}$, and $0 < \theta < 1$,
$$\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{\mathsf{F}}^2 \le
\frac{\|\mathbf{E}\|_{\mathsf{F}}^2 + \sqrt{k}\,\eta_w}{(1-\theta)a} +
\frac{\eta_\chi^2}{\theta(1-\theta)a^2}$$
except with probability $\delta + \delta_w + \delta_\chi$. The projector of
$\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k$ qualifies, and so does the projector of the output
at $c^{-1}\mathbf{\Omega}$ when the analysis runs at $\mathbf{\Omega}$. Proved without a literature
source (S2b's core); the sketch conditions are those of [CohenElderMuscoMuscoPersu2015, §7.2 and
proof of Theorem 12]. Result: etrsvd -/
theorem HasSubspaceInjection.measure_frobNorm_sub_mul_sq_gt_le {A : Matrix m n 𝕜} {k : ℕ}
    {a θ δ ηw δw ηχ δχ : ℝ}
    (h : HasSubspaceInjection (fun ω => (X ω)ᴴ) (truncatedSVD A k)ᴴ a δ μ) (ha : 0 < a)
    (ha1 : a ≤ 1) (hθ : 0 < θ) (hθ1 : θ < 1) {P : Ω → Matrix m m 𝕜}
    (hP : ∀ ω, IsStarProjection (P ω)) (hPk : ∀ ω, (P ω).rank ≤ k)
    (hopt : ∀ ω, frobNorm (A * X ω - P ω * (A * X ω)) ≤
      frobNorm ((A - truncatedSVD A k) * X ω))
    (hw : μ.real {ω | ηw < frobNorm ((A - truncatedSVD A k) * X ω * (X ω)ᴴ *
      (A - truncatedSVD A k)ᴴ - (A - truncatedSVD A k) * (A - truncatedSVD A k)ᴴ)} ≤ δw)
    (hχ : μ.real {ω | ηχ < frobNorm ((A - truncatedSVD A k) * X ω * (X ω)ᴴ *
      rangeProjector (truncatedSVD A k)ᴴ)} ≤ δχ) :
    μ.real {ω | (frobNorm (A - truncatedSVD A k) ^ 2 + √(k : ℝ) * ηw) / ((1 - θ) * a) +
        ηχ ^ 2 / (θ * (1 - θ) * a ^ 2) < frobNorm (A - P ω * A) ^ 2} ≤ δ + δw + δχ

/-- **Early truncation to relative error**: with injection constant $1 - \varepsilon/8$,
$0 < \varepsilon \le 1$, tail–tail level $\frac{\varepsilon}{8\sqrt{k}}\|\mathbf{E}\|_{\mathsf{F}}^2$
and tail–head level $\frac{\varepsilon}{8}\|\mathbf{E}\|_{\mathsf{F}}$ in the hypotheses of
`NLAlib.HasSubspaceInjection.measure_frobNorm_sub_mul_sq_gt_le`,
$\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{\mathsf{F}}^2 \le (1 + \varepsilon)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$ except with probability
$\delta + \delta_w + \delta_\chi$. The form every family statement instantiates.
Result: etrsvd -/
theorem HasSubspaceInjection.measure_frobNorm_sub_mul_sq_gt_one_add_mul_le
    {A : Matrix m n 𝕜} {k : ℕ} {ε δ δw δχ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (h : HasSubspaceInjection (fun ω => (X ω)ᴴ) (truncatedSVD A k)ᴴ (1 - ε / 8) δ μ)
    {P : Ω → Matrix m m 𝕜} (hP : ∀ ω, IsStarProjection (P ω)) (hPk : ∀ ω, (P ω).rank ≤ k)
    (hopt : ∀ ω, frobNorm (A * X ω - P ω * (A * X ω)) ≤
      frobNorm ((A - truncatedSVD A k) * X ω))
    (hw : μ.real {ω | ε / (8 * √(k : ℝ)) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm ((A - truncatedSVD A k) * X ω * (X ω)ᴴ * (A - truncatedSVD A k)ᴴ -
        (A - truncatedSVD A k) * (A - truncatedSVD A k)ᴴ)} ≤ δw)
    (hχ : μ.real {ω | ε / 8 * frobNorm (A - truncatedSVD A k) <
      frobNorm ((A - truncatedSVD A k) * X ω * (X ω)ᴴ *
        rangeProjector (truncatedSVD A k)ᴴ)} ≤ δχ) :
    μ.real {ω | (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - P ω * A) ^ 2} ≤ δ + δw + δχ

/-- **The early-truncated randomized SVD from an injection and the JL moment property**: for a
real sketch with the head injection of constant $0 < a \le 1$ (failure $\delta$) and the
$(\varepsilon, \delta', p)$ JL moment property, $\varepsilon > 0$, $p \ge 2$, and $0 < \theta < 1$,
$$\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)\|_{\mathsf{F}}^2 \le
\Bigl(\frac{1 + \sqrt{k}\,\varepsilon}{(1-\theta)a} + \frac{k\varepsilon^2}{\theta(1-\theta)a^2}\Bigr)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta + 2\delta'$; with $\varepsilon$ of order $\varepsilon_0/\sqrt{k}$ this
is $1 + O(\varepsilon_0)$ at $\ell = O(k/(\varepsilon_0^2\delta'))$. Its uniform-PCP neighbour is the
S9 route; its Gaussian expectation twin is
`NLAlib.integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_one_add_mul_of_hasLaw_gaussianMatrix`.
Proved without a literature source (S2b's core); [CohenElderMuscoMuscoPersu2015, §7.2]; [Woodruff2014,
Theorem 61] is the full-row-space form. Result: etrsvd -/
theorem HasJLMoment.measure_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le {A : Matrix m n ℝ} {k : ℕ}
    {a θ δ ε δ' p : ℝ} (hJL : HasJLMoment (fun ω => (X ω)ᴴ) ε δ' p μ)
    (h : HasSubspaceInjection (fun ω => (X ω)ᴴ) (truncatedSVD A k)ᴴ a δ μ)
    (hX : AEMeasurable X μ) (ha : 0 < a) (ha1 : a ≤ 1) (hθ : 0 < θ) (hθ1 : θ < 1) (hε : 0 < ε)
    (hp : 2 ≤ p) :
    μ.real {ω | ((1 + √(k : ℝ) * ε) / ((1 - θ) * a) + k * ε ^ 2 / (θ * (1 - θ) * a ^ 2)) *
        frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2} ≤ δ + 2 * δ'

/-- **Early-truncated generalized Nyström = early-truncated randomized SVD × completion,
structured co-range sketch**: for any law of $\mathbf{\Omega}$ and an independent $\mathbf{\Psi}$
whose $\mathbf{\Psi}^{\mathsf{H}}$ is an OSI for dimension $k$ (constant $a > 0$, failure
$\delta$), for $t > 0$
$$\|\mathbf{A} - \mathsf{earlyTruncatedGN}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi}, k)\|_{\mathsf{F}}^2
\le \Bigl(1 + \frac{t}{a}\Bigr)
\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)\|_{\mathsf{F}}^2$$
except with probability $\delta + 1/t$. Every early-truncated RSVD tail (the core route, the PCP
route) composes with it. Proved without a literature source, as a composition; the algorithm is
[TroppYurtseverUdellCevher2017, §7.3.1, (7.3)]. Result: etgn -/
theorem
    IsObliviousSubspaceInjection.measure_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_gt_mul_le
    [IsProbabilityMeasure μ] {A : Matrix m n 𝕜} {k : ℕ} {a δ t : ℝ}
    (h : IsObliviousSubspaceInjection (fun ω => (Ψ ω)ᴴ) k a δ μ) (ha : 0 < a) (ht : 0 < t)
    (hind : IndepFun X Ψ μ) (hX : AEMeasurable X μ) (hΨ : AEMeasurable Ψ μ) :
    μ.real {ω | (1 + t / a) * frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 <
      frobNorm (A - earlyTruncatedGeneralizedNystrom A (X ω) (Ψ ω) k) ^ 2} ≤ δ + 1 / t

/-- The completion through approximate multiplication, real: factor $1 + k\varepsilon^2/a^2$,
failure probability $\delta + \delta'$. Result: etgn -/
theorem HasJLMoment.measure_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_gt_mul_le
    [IsProbabilityMeasure μ] {A : Matrix m n ℝ} {k : ℕ} {a δ ε δ' p : ℝ}
    (hJL : HasJLMoment (fun ω => (Ψ ω)ᴴ) ε δ' p μ)
    (h : IsObliviousSubspaceInjection (fun ω => (Ψ ω)ᴴ) k a δ μ) (ha : 0 < a) (hε : 0 < ε)
    (hp : 2 ≤ p) (hind : IndepFun X Ψ μ) (hX : AEMeasurable X μ) (hΨ : AEMeasurable Ψ μ) :
    μ.real {ω | (1 + k * ε ^ 2 / a ^ 2) * frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 <
      frobNorm (A - earlyTruncatedGeneralizedNystrom A (X ω) (Ψ ω) k) ^ 2} ≤ δ + δ'

/-- **Early-truncated generalized Nyström with structured sketches**: the range side of
`NLAlib.HasJLMoment.measure_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le` and the co-range side of
`NLAlib.HasJLMoment.measure_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_gt_mul_le` give
$$\|\mathbf{A} - \mathsf{earlyTruncatedGN}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi}, k)\|_{\mathsf{F}}^2
\le \Bigl(1 + \frac{k\varepsilon'^2}{a'^2}\Bigr)
\Bigl(\frac{1 + \sqrt{k}\,\varepsilon}{(1-\theta)a} + \frac{k\varepsilon^2}{\theta(1-\theta)a^2}\Bigr)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta + 2\delta_1 + \delta' + \delta_2$: $1 + \varepsilon_0$ at
$\ell = O(k/\varepsilon_0^2)$ and $p = O(k/\varepsilon_0)$ at constant failure probability. Proved
without a literature source, as a composition; [TroppYurtseverUdellCevher2017, §7.3.1] states the
algorithm and the rate $\Theta(r/\varepsilon^2)$ for both sizes, with unspecified constants.
Result: etgn -/
theorem HasJLMoment.measure_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_gt_le
    [IsProbabilityMeasure μ] {A : Matrix m n ℝ} {k : ℕ} {a θ δ ε δ₁ p a' δ' ε' δ₂ p' : ℝ}
    (hJL : HasJLMoment (fun ω => (X ω)ᴴ) ε δ₁ p μ)
    (h : HasSubspaceInjection (fun ω => (X ω)ᴴ) (truncatedSVD A k)ᴴ a δ μ)
    (hJLΨ : HasJLMoment (fun ω => (Ψ ω)ᴴ) ε' δ₂ p' μ)
    (hΨ : IsObliviousSubspaceInjection (fun ω => (Ψ ω)ᴴ) k a' δ' μ) (hind : IndepFun X Ψ μ)
    (hX : AEMeasurable X μ) (hΨm : AEMeasurable Ψ μ) (ha : 0 < a) (ha1 : a ≤ 1) (hθ : 0 < θ)
    (hθ1 : θ < 1) (hε : 0 < ε) (hp : 2 ≤ p) (ha' : 0 < a') (hε' : 0 < ε') (hp' : 2 ≤ p') :
    μ.real {ω | (1 + k * ε' ^ 2 / a' ^ 2) *
        ((1 + √(k : ℝ) * ε) / ((1 - θ) * a) + k * ε ^ 2 / (θ * (1 - θ) * a ^ 2)) *
        frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - earlyTruncatedGeneralizedNystrom A (X ω) (Ψ ω) k) ^ 2} ≤
      δ + 2 * δ₁ + (δ' + δ₂)
```

Proof routes. *C1:* common steps 1 and 3; on the good events S2b's T4
(`IsSubspaceInjection.frobNorm_sub_mul_sq_le` at the frame $\mathbf{Z}$, `hopt` rewritten by
$\mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}} = \llbracket\mathbf{A}\rrbracket_k$), monotone in $w$ and
$\chi$, with $\|\mathbf{E}\mathbf{\Omega}\mathbf{\Omega}^{\mathsf{H}}\mathbf{Z} -
\mathbf{E}\mathbf{Z}\|_{\mathsf{F}} = \|\mathbf{E}\mathbf{\Omega}\mathbf{\Omega}^{\mathsf{H}}
\mathbf{P}_{\llbracket\mathbf{A}\rrbracket_k^{\mathsf{H}}}\|_{\mathsf{F}}$; on the good event
$\chi \le \eta_\chi$ forces $\eta_\chi \ge 0$, so no sign hypothesis. About 35. *C2:* C1 at
$a = 1 - \varepsilon/8$, $\theta = \varepsilon/8$; $k = 0$ first ($\mathbf{P} = \mathbf{0}$, the event
is empty); then the factor is at most $1 + \varepsilon$ (§3.6). About 30. *C3:* C1 at $\mathbf{P}$ the
projector of $\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k$ (`sub_earlyTruncatedRSVD`; `hopt` by
`rangeProjector_truncatedSVD_mul` and `frobNorm_sub_truncatedSVD_le_of_rank_le`, the competitor
$\llbracket\mathbf{A}\rrbracket_k\mathbf{\Omega}$ of rank at most $k$), with $\eta_w =
\varepsilon\|\mathbf{E}\|_{\mathsf{F}}^2$ and $\eta_\chi = \varepsilon\sqrt{k}\,\|\mathbf{E}\|_{\mathsf{F}}$ from
the JL multiplication tails at $(\mathbf{E}^{\mathsf{H}}, \mathbf{E}^{\mathsf{H}})$ and
$(\mathbf{E}^{\mathsf{H}}, \mathbf{P}_{\llbracket\mathbf{A}\rrbracket_k^{\mathsf{H}}})$. About 35.
*C4:* L2 at $\mathbf{Y} = \llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k$ (rank at most $k$,
`rank_truncatedSVD_le`; measurable, `measurable_truncatedSVD`), $\mathbf{B} = \mathbf{A}$;
`sub_earlyTruncatedRSVD`, `sub_earlyTruncatedGeneralizedNystrom`, `mul_sketchAndSolve`. About 25.
*C5:* L4 likewise; 20. *C6:* union of C3's and C5's events; 20.

### 3.5 Family files (25)

Each family file opens with a module docstring naming the Sketching file it mirrors and the
generic theorems that apply to the family with no per-family statement (Nyström, generalized
Nyström, the truncations), with the two lines that instantiate them. Every explicit sample-size
statement is followed by its asymptotic form in the same file; the explicit docstring says
"Asymptotic form: `…`.", and the asymptotic docstring says "$O(\ldots)$ columns suffice" in words,
names the explicit theorem in a sentence ("The asymptotic form of `…`.") and ends with the line
`Asymptotic: <explicit name>` before `Result:` (CONTRIBUTING §5.2 rule 3, §9), so the explorer lists
each pair as Related. The pairs described in prose below follow the written ones exactly. Constants of
the explicit forms are the arithmetic of §3.6.

**Asymptotic proofs.** Each asymptotic form instantiates its explicit theorem: the constant $C$
covers the explicit second hypothesis (an inline integer) and the family's named size, bounded by
its threshold through the family's size API (`gaussianInjectionDim`, `jlDim`,
`subgaussianEmbeddingDim`, `countSketchRows`, `samplingInjectionSize`, `srhtRowBound`: each has
monotonicity and an upper comparison in the Sketching round). Where the family's own asymptotic
OSI form exists when the file is written (`exists_forall_isObliviousSubspaceInjection_of_…`), the
proof may take its constant instead; the statement is the same either way. $\varepsilon_0 = 1$
throughout; $\delta \le 1/2$ makes $\log(c/\delta) \le C'\log(1/\delta)$.

#### `LowRank/Oblivious/Gaussian.lean` (2, real)

```lean
/-- **Early-truncated randomized SVD with a Gaussian test matrix, tail**: for a standard Gaussian
$n \times \ell$ test matrix $\mathbf{\Omega}$,
$0 < \varepsilon \le 1$, $\delta > 0$, <!-- value gaussianInjectionDim k (\varepsilon/8) (\delta/3) -->
$\ell \ge 4 (\sqrt{k} + \sqrt{2 \log(1/(\delta/3))})^2/(\varepsilon/8)^2$ and
$\ell \ge 384k/(\varepsilon^2\delta)$,
$$\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)\|_{\mathsf{F}}^2 \le
(1 + \varepsilon)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta$. Its expectation twin, at $\ell \ge 900k/\varepsilon^2$, is
`NLAlib.integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_one_add_mul_of_hasLaw_gaussianMatrix`; a
tail from that by Markov's inequality needs $\ell$ of order $k/(\varepsilon\delta)^2$.
Asymptotic form:
`NLAlib.exists_forall_measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_gaussianMatrix`.
[CohenElderMuscoMuscoPersu2015, §7.2]; there with unspecified constants. Result: etrsvd -/
theorem measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ} {ε δ : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hδ : 0 < δ) (hl : gaussianInjectionDim k (ε / 8) (δ / 3) ≤ Fintype.card l)
    (hl' : 384 * (k : ℝ) ≤ ε ^ 2 * δ * Fintype.card l) :
    μ.real {ω | (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2} ≤ δ

/-- **$O((k/\delta + \log(1/\delta))/\varepsilon^2)$ Gaussian columns suffice for early
truncation**: there are absolute constants $C, \varepsilon_0 > 0$ such that for a standard Gaussian
test matrix, $0 < \varepsilon \le \varepsilon_0$, $0 < \delta \le 1/2$ and
$\ell \ge C(k/\delta + \log(1/\delta))/\varepsilon^2$, the early-truncated randomized SVD has error at
most $(1 + \varepsilon)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$ except with
probability $\delta$. The asymptotic form of
`NLAlib.measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_gaussianMatrix`.
Asymptotic: NLAlib.measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_gaussianMatrix
Result: etrsvd -/
theorem
    exists_forall_measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l : Type} [MeasurableSpace Ω] [Fintype m] [Fintype n]
      [Fintype l] [DecidableEq m] [DecidableEq n] (μ : Measure Ω) (A : Matrix m n ℝ)
      (X : Ω → Matrix n l ℝ) (k : ℕ) (ε δ : ℝ),
      HasLaw X (gaussianMatrix n l) μ → 0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ 1 / 2 →
      C * (((k : ℝ) / δ + Real.log (1 / δ)) / ε ^ 2) ≤ Fintype.card l →
      μ.real {ω | (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 <
        frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2} ≤ δ
```

Route: $\mathbf{\Omega}^{\mathsf{H}}$ has law `gaussianMatrix l n`
(`hasLaw_conjTranspose_of_hasLaw_gaussianMatrix`); the OSI at $(\varepsilon/8, \delta/3)$
(`isObliviousSubspaceInjection_of_hasLaw_gaussianMatrix_of_gaussianInjectionDim_le`) and the JL
moment at $\varepsilon/(8\sqrt{k})$ (`hasJLMoment_of_hasLaw_gaussianMatrix`, failure
$128k/(\ell\varepsilon^2) \le \delta/3$) at the normalised test matrix; the two multiplication tails
from `HasJLMoment.measure_frobNorm_conjTranspose_mul_sub_ge_le`; C2 with $\mathbf{P}$ from
$\mathbf{\Omega}$ (common step 5). About 50 lines for the pair with the asymptotic form.

#### `LowRank/Oblivious/Rademacher.lean` (4, real)

Hypothesis `hX : HasLaw (fun ω => (X ω)ᴴ) (rademacherMatrix l n) μ`.

```lean
/-- **The randomized SVD with a Rademacher test matrix, relative error**: for $\varepsilon,
\delta > 0$, <!-- value jlDim (1/4) (\delta/(2 \cdot 9^k)) -->
$\ell \ge \log(2/(\delta/(2 \cdot 9^k)))/((1/4)^2/4 - (1/4)^3/6)$ and $\ell \ge 16k/(\varepsilon\delta)$,
$\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_{\mathsf{F}}^2 \le (1 + \varepsilon)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$ except with probability $\delta$.
Asymptotic form: `NLAlib.exists_forall_measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_rademacherMatrix`.
[Woodruff2014, Lemma 45 and Remark 46]. Result: randomized-svd-tail -/
theorem measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_rademacherMatrix (A : Matrix m n ℝ)
    (hX : HasLaw (fun ω => (X ω)ᴴ) (rademacherMatrix l n) μ) {k : ℕ} {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) (hl : jlDim (1 / 4) (δ / (2 * 9 ^ k)) ≤ Fintype.card l)
    (hl' : 16 * (k : ℝ) ≤ ε * δ * Fintype.card l) :
    μ.real {ω | (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - rsvd A (X ω)) ^ 2} ≤ δ

/-- **$O(k/(\varepsilon\delta) + \log(1/\delta))$ Rademacher columns suffice for the randomized
SVD** to relative error $1 + \varepsilon$ with probability $1 - \delta$. The asymptotic form of
`NLAlib.measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_rademacherMatrix`.
Asymptotic: NLAlib.measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_rademacherMatrix
Result: randomized-svd-tail -/
theorem exists_forall_measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_rademacherMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l : Type} [MeasurableSpace Ω] [Fintype m] [Fintype n]
      [Fintype l] [DecidableEq m] [DecidableEq n] (μ : Measure Ω) (A : Matrix m n ℝ)
      (X : Ω → Matrix n l ℝ) (k : ℕ) (ε δ : ℝ),
      HasLaw (fun ω => (X ω)ᴴ) (rademacherMatrix l n) μ → 0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ 1 / 2 →
      C * ((k : ℝ) / (ε * δ) + Real.log (1 / δ)) ≤ Fintype.card l →
      μ.real {ω | (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 <
        frobNorm (A - rsvd A (X ω)) ^ 2} ≤ δ

/-- Early truncation with a Rademacher test matrix: for
$0 < \varepsilon \le 1$, $\delta > 0$, <!-- value jlDim (\varepsilon/16) (\delta/(3 \cdot 9^k)) -->
$\ell \ge \log(2/(\delta/(3 \cdot 9^k)))/((\varepsilon/16)^2/4 - (\varepsilon/16)^3/6)$ and
$\ell \ge 384k/(\varepsilon^2\delta)$, the bound of the Gaussian statement
`NLAlib.measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_gaussianMatrix`. Asymptotic
form: `NLAlib.exists_forall_measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_rademacherMatrix`.
Result: etrsvd -/
theorem measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_rademacherMatrix
    (A : Matrix m n ℝ) (hX : HasLaw (fun ω => (X ω)ᴴ) (rademacherMatrix l n) μ) {k : ℕ}
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hl : jlDim (ε / 16) (δ / (3 * 9 ^ k)) ≤ Fintype.card l)
    (hl' : 384 * (k : ℝ) ≤ ε ^ 2 * δ * Fintype.card l) :
    μ.real {ω | (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2} ≤ δ

/-- $O((k/\delta + \log(1/\delta))/\varepsilon^2)$ Rademacher columns suffice for early truncation.
The asymptotic form of
`NLAlib.measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_rademacherMatrix`.
Asymptotic: NLAlib.measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_rademacherMatrix
Result: etrsvd -/
theorem
    exists_forall_measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_rademacherMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l : Type} [MeasurableSpace Ω] [Fintype m] [Fintype n]
      [Fintype l] [DecidableEq m] [DecidableEq n] (μ : Measure Ω) (A : Matrix m n ℝ)
      (X : Ω → Matrix n l ℝ) (k : ℕ) (ε δ : ℝ),
      HasLaw (fun ω => (X ω)ᴴ) (rademacherMatrix l n) μ → 0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ 1 / 2 →
      C * (((k : ℝ) / δ + Real.log (1 / δ)) / ε ^ 2) ≤ Fintype.card l →
      μ.real {ω | (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 <
        frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2} ≤ δ
```

A declaration whose name does not fit after `theorem` on a 100-column line breaks after it, as S6's.
Routes: `isObliviousSubspaceInjection_of_hasLaw_rademacherMatrix_of_jlDim_le` (accuracy $1/2$ or
$\varepsilon/8$, both below $3$) and `hasJLMoment_of_hasLaw_rademacherMatrix` (failure
$2/(\ell\varepsilon_J^2)$), then A6 with L5, and C2 as for the Gaussian.

#### `LowRank/Oblivious/SubGaussian.lean` (4, real)

Hypotheses on the rows of the sketch, as `Sketching/Gaussian/SubGaussian.lean`:
`(hind : iIndepFun (fun i ω => (X ω)ᴴ i) μ) (hsub : ∀ i, IsSubgaussianVector (fun ω => (X ω)ᴴ i) c μ)
(hiso : ∀ i, IsIsotropic (fun ω => (X ω)ᴴ i) μ)` with `c : ℝ≥0`, `[Nonempty l]`, and
`hX : AEMeasurable X μ` for the multiplication tail, dropped if `IsSubgaussianVector` gives it
(checked at implementation; CONTRIBUTING §5.2, minimal hypotheses). The family's side condition
$\varepsilon \le 2c$ holds at the accuracies used here ($1/2$ and $\varepsilon/8$) because
isotropy forces $c \ge 1$ (`IsSubgaussianVector.one_le_of_isIsotropic`), so no hypothesis on $c$.

```lean
/-- The randomized SVD with a sub-Gaussian test matrix, relative error: for $\varepsilon,
\delta > 0$, <!-- value subgaussianEmbeddingDim c k (1/2) (\delta/2) -->
$\ell \ge 256 c^2 (k \log 9 + \log(2/(\delta/2)))/(1/2)^2$ and
$\ell \ge 8(16c^2 - 1)k/(\varepsilon\delta)$, the bound of the Rademacher statement.
Asymptotic form: `NLAlib.exists_forall_measureReal_frobNorm_sub_rsvd_sq_gt_le_of_isSubgaussianVector`.
Result: randomized-svd-tail -/
theorem measureReal_frobNorm_sub_rsvd_sq_gt_le_of_isSubgaussianVector [Nonempty l]
    (A : Matrix m n ℝ) {c : ℝ≥0} (hind : iIndepFun (fun i ω => (X ω)ᴴ i) μ)
    (hsub : ∀ i, IsSubgaussianVector (fun ω => (X ω)ᴴ i) c μ)
    (hiso : ∀ i, IsIsotropic (fun ω => (X ω)ᴴ i) μ) (hX : AEMeasurable X μ) {k : ℕ} {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (hl : subgaussianEmbeddingDim c k (1 / 2) (δ / 2) ≤ Fintype.card l)
    (hl' : 8 * (16 * (c : ℝ) ^ 2 - 1) * k ≤ ε * δ * Fintype.card l) :
    μ.real {ω | (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - rsvd A (X ω)) ^ 2} ≤ δ
```

Its asymptotic form `exists_forall_measureReal_frobNorm_sub_rsvd_sq_gt_le_of_isSubgaussianVector`
quantifies `(c : ℝ≥0)` after `X` and has threshold `C * ((c : ℝ) ^ 2 * ((k : ℝ) / (ε * δ) +
Real.log (1 / δ)))`; the early-truncation pair
(`measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_isSubgaussianVector`, size hypotheses
`subgaussianEmbeddingDim c k (ε / 8) (δ / 3) ≤ Fintype.card l` and
`192 * (16 * (c : ℝ) ^ 2 - 1) * k ≤ ε ^ 2 * δ * Fintype.card l`, and its asymptotic form with
threshold `C * ((c : ℝ) ^ 2 * ((k : ℝ) / δ + Real.log (1 / δ)) / ε ^ 2)`) follows the Rademacher
pattern. The JL failure is $(16c^2 - 1)/(\ell\varepsilon_J^2)$
(`hasJLMoment_of_isSubgaussianVector`). The registry's `latex` for `subgaussianEmbeddingDim` carries
the symbol $C$ for `subgaussianJLConstant`; the docstrings write the value $1/64$ in its place
($4 \cdot 64 = 256$ above), which needs the registry template changed to match (Q11, flagged).

#### `LowRank/Oblivious/CountSketch.lean` (4, any field)

Hypothesis `hX : HasLaw (fun ω => (X ω)ᴴ) (countSketch l n) μ`.

```lean
/-- **The randomized SVD with a CountSketch test matrix, relative error**: for $\varepsilon,
\delta > 0$, <!-- value countSketchRows k (1/2) (\delta/2) -->
$\ell \ge (k^2 + k)/((\delta/2)(1/2)^2)$ and $\ell \ge 16k/(\varepsilon\delta)$,
$\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_{\mathsf{F}}^2 \le (1 + \varepsilon)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$ except with probability $\delta$, over
any `RCLike` field. Asymptotic form:
`NLAlib.exists_forall_measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_countSketch`.
[Woodruff2014, Remark 46]; there $O(k^2 + k/\varepsilon)$ rows at constant probability, real.
Result: randomized-svd-tail -/
theorem measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_countSketch (A : Matrix m n 𝕜)
    (hX : HasLaw (fun ω => (X ω)ᴴ) (countSketch l n) μ) {k : ℕ} {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) (hl : countSketchRows k (1 / 2) (δ / 2) ≤ Fintype.card l)
    (hl' : 16 * (k : ℝ) ≤ ε * δ * Fintype.card l) :
    μ.real {ω | (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - rsvd A (X ω)) ^ 2} ≤ δ

/-- **$O((k^2 + k/\varepsilon)/\delta)$ CountSketch columns suffice for the randomized SVD** to
relative error $1 + \varepsilon$ with probability $1 - \delta$. The asymptotic form of
`NLAlib.measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_countSketch`.
Asymptotic: NLAlib.measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_countSketch
Result: randomized-svd-tail -/
theorem exists_forall_measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_countSketch :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω 𝕜 m n l : Type} [MeasurableSpace Ω] [RCLike 𝕜]
      [Fintype m] [Fintype n] [Fintype l] [DecidableEq m] [DecidableEq n] [DecidableEq l]
      (μ : Measure Ω) (A : Matrix m n 𝕜) (X : Ω → Matrix n l 𝕜) (k : ℕ) (ε δ : ℝ),
      HasLaw (fun ω => (X ω)ᴴ) (countSketch l n) μ → 0 < ε → ε ≤ ε₀ → 0 < δ →
      C * ((((k : ℝ) ^ 2 + k) + k / ε) / δ) ≤ Fintype.card l →
      μ.real {ω | (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 <
        frobNorm (A - rsvd A (X ω)) ^ 2} ≤ δ
```

The early-truncation pair (`measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_countSketch`
with `countSketchRows k (ε / 8) (δ / 3) ≤ Fintype.card l` and
`384 * (k : ℝ) ≤ ε ^ 2 * δ * Fintype.card l`, $0 < \varepsilon \le 1$; asymptotic threshold
`C * (((k : ℝ) ^ 2 + k) / (ε ^ 2 * δ))`) is C2 with the two CountSketch multiplication tails
(`measureReal_frobNorm_conjTranspose_mul_sub_ge_le_of_hasLaw_countSketch`, failure
$2/(\ell\varepsilon_J^2)$ each, over `𝕜`). The RSVD statement is A8 with that tail at
$\varepsilon_J^2 = \varepsilon/(4k)$, then T3. Instances as the family's (`[DecidableEq l]` where
`countSketch` needs it).

#### `LowRank/Oblivious/SRHT.lean` (6, any field)

Hypotheses `hF : IsBoundedOrthonormal F β`, `hX : HasLaw (fun ω => (X ω)ᴴ) (srht l F) μ` with
`hln : Fintype.card l ≤ Fintype.card n` and `[Nonempty l]` (without replacement), or
`(srhtWithReplacement l F)` with `[Nonempty n]` (with replacement). No approximate multiplication
(D6): the OSI route, constant factor, and the bounded-sketch route.

```lean
/-- **The randomized SVD with an SRHT test matrix**: for $\delta, t > 0$ and $\ell$ at least the
injection size of the family at accuracy $1/2$ and failure $\delta/2$ (in the full docstring, the
value of `samplingInjectionSize` with the value of `srhtRowBound` as its second argument, two
value markers; Q11),
$\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_{\mathsf{F}}^2 \le (1 + 2t)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$ except with probability
$\delta + 1/t$. Its bounded-sketch neighbour, failure $\delta$ and factor $1 + 2n/\ell$, is
`NLAlib.SymmetricGauge.measureReal_matrixNorm_conjTranspose_mul_self_sub_rsvd_gt_le_of_hasLaw_srht`;
this one is better when $t < n/\ell$. Asymptotic form:
`NLAlib.exists_forall_measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_srht`.
[CamanoEpperlyMeyerTropp2025, Theorem 2.2]; [HalkoMartinssonTropp2011, Theorem 11.2].
Result: randomized-svd-tail -/
theorem measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_srht [Nonempty l] {F : Matrix n n 𝕜}
    {β : ℝ} (hF : IsBoundedOrthonormal F β) (A : Matrix m n 𝕜)
    (hX : HasLaw (fun ω => (X ω)ᴴ) (srht l F) μ) (hln : Fintype.card l ≤ Fintype.card n) {k : ℕ}
    {δ t : ℝ} (hδ : 0 < δ) (ht : 0 < t)
    (hl : samplingInjectionSize k (β * srhtRowBound (Fintype.card n) k (δ / 2)) (1 / 2) (δ / 2) ≤
      Fintype.card l) :
    μ.real {ω | (1 + 2 * t) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - rsvd A (X ω)) ^ 2} ≤ δ + 1 / t

/-- **$O(\beta(k + \log(n/\delta))\log(k/\delta))$ SRHT columns suffice for the randomized SVD to
a constant factor**: there is an absolute constant $C > 0$ such that for $0 < \delta \le 1/2$,
$t > 0$ and $\ell \ge C\beta(k + \log(n/\delta))\log(k/\delta)$, the error is at most
$(1 + 2t)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$ except with probability
$\delta + 1/t$. The asymptotic form of `NLAlib.measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_srht`;
a constant-factor result has no accuracy parameter, so no $\varepsilon_0$ (Q5).
Asymptotic: NLAlib.measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_srht
Result: randomized-svd-tail -/
theorem exists_forall_measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_srht :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω 𝕜 m n l : Type} [MeasurableSpace Ω] [RCLike 𝕜] [Fintype m]
      [Fintype n] [Fintype l] [DecidableEq m] [DecidableEq n] [Nonempty l] (μ : Measure Ω)
      (A : Matrix m n 𝕜) (X : Ω → Matrix n l 𝕜) (F : Matrix n n 𝕜) (β : ℝ) (k : ℕ) (δ t : ℝ),
      IsBoundedOrthonormal F β → HasLaw (fun ω => (X ω)ᴴ) (srht l F) μ →
      Fintype.card l ≤ Fintype.card n → 0 < δ → δ ≤ 1 / 2 → 0 < t →
      C * (β * (k + Real.log (Fintype.card n / δ)) * Real.log (k / δ)) ≤ Fintype.card l →
      μ.real {ω | (1 + 2 * t) * frobNorm (A - truncatedSVD A k) ^ 2 <
        frobNorm (A - rsvd A (X ω)) ^ 2} ≤ δ + 1 / t

/-- **The randomized SVD with an SRHT test matrix, bounded-sketch form** (HMT's SRFT theorem,
sharper): with the hypotheses above (without $t$), for every unitarily invariant norm
$$\bigl\|(\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega}))^{\mathsf{H}}
(\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega}))\bigr\|_{\Phi} \le
\Bigl(1 + \frac{2n}{\ell}\Bigr)\|\mathbf{E}^{\mathsf{H}}\mathbf{E}\|_{\Phi}$$
except with probability $\delta$: in spectral norm $\|\mathbf{A} - \mathsf{rsvd}\|_2^2 \le
(1 + 2n/\ell)\sigma_k(\mathbf{A})^2$, in Frobenius norm the same factor against
$\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$. Asymptotic form:
`NLAlib.exists_forall_measureReal_matrixNorm_conjTranspose_mul_self_sub_rsvd_gt_le_of_hasLaw_srht`.
[HalkoMartinssonTropp2011, Theorem 11.2]; there $1 + 7n/\ell$ and failure $O(k^{-1})$.
Result: randomized-svd-tail -/
theorem SymmetricGauge.measureReal_matrixNorm_conjTranspose_mul_self_sub_rsvd_gt_le_of_hasLaw_srht
    [Nonempty l] (Φ : SymmetricGauge) {F : Matrix n n 𝕜} {β : ℝ} (hF : IsBoundedOrthonormal F β)
    (A : Matrix m n 𝕜) (hX : HasLaw (fun ω => (X ω)ᴴ) (srht l F) μ)
    (hln : Fintype.card l ≤ Fintype.card n) {k : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (hl : samplingInjectionSize k (β * srhtRowBound (Fintype.card n) k (δ / 2)) (1 / 2) (δ / 2) ≤
      Fintype.card l) :
    μ.real {ω | (1 + 2 * Fintype.card n / Fintype.card l) *
        Φ.matrixNorm ((A - truncatedSVD A k)ᴴ * (A - truncatedSVD A k)) <
      Φ.matrixNorm ((A - rsvd A (X ω))ᴴ * (A - rsvd A (X ω)))} ≤ δ
```

Its asymptotic form is root-level, quantifies `(Φ : SymmetricGauge)` after the types, has the
threshold of the Frobenius form and no `t`. The with-replacement pair
(`measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_srhtWithReplacement` and its asymptotic form,
through `isObliviousSubspaceInjection_of_hasLaw_srhtWithReplacement_of_samplingInjectionSize_le`)
has no `hln` and no bounded-sketch twin: with replacement $\|\mathbf{\Omega}\|_2$ is not constant
(repeated rows). Routes: `isObliviousSubspaceInjection_of_hasLaw_srht_of_samplingInjectionSize_le`
at accuracy $1/2$; A2 (factor $1 + t/(1/2)$); A5 with `ae_specNorm_eq_of_hasLaw_srht`
($L^2 = n/\ell$, through `specNorm_conjTranspose` and the orthonormality in `IsBoundedOrthonormal`).

#### `LowRank/Oblivious/RowSampling.lean` and `WithoutReplacement.lean` (2 each, any field)

Sampling is not oblivious: the statements take the leverage scores of the rank-$k$ row space,
`leverageScore (truncatedSVD A k)ᴴ i`, which is the hypothesis of the one subspace the analysis
needs, with no frame (Q1).

```lean
/-- **Column sampling at the rank-$k$ leverage scores**: if the sketch samples $\ell$ columns of
$\mathbf{A}$ independently with positive probabilities $p_i$ summing to $1$, the leverage scores of
$\operatorname{range}\llbracket\mathbf{A}\rrbracket_k^{\mathsf{H}}$ satisfy $\tau_i \le Lp_i$, $\delta,
t > 0$ and <!-- value samplingInjectionSize k L (1/2) \delta -->
$\ell \ge 2 L \log(k/\delta)/(1/2)^2$, then
$\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_{\mathsf{F}}^2 \le (1 + 2t)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$ except with probability
$\delta + 1/t$. Asymptotic form:
`NLAlib.exists_forall_measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_samplingSketch`.
[CamanoEpperlyMeyerTropp2025, Theorem 2.2] with a fixed-subspace injection; the instance is not
stated there. Result: randomized-svd-tail -/
theorem measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_samplingSketch [Nonempty l]
    (A : Matrix m n 𝕜) {p : n → ℝ≥0} (hX : HasLaw (fun ω => (X ω)ᴴ) (samplingSketch l p) μ)
    (hp : ∑ i, p i = 1) (hpos : ∀ i, 0 < p i) {k : ℕ} {L δ t : ℝ}
    (hdom : ∀ i, leverageScore (truncatedSVD A k)ᴴ i ≤ L * p i) (hδ : 0 < δ) (ht : 0 < t)
    (hl : samplingInjectionSize k L (1 / 2) δ ≤ Fintype.card l) :
    μ.real {ω | (1 + 2 * t) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - rsvd A (X ω)) ^ 2} ≤ δ + 1 / t
```

The asymptotic form (`∃ C : ℝ, 0 < C ∧ ∀ …`, threshold `C * (L * Real.log (k / δ))`, Q5) instantiates
it through `samplingInjectionSize_mono` (the rank of the subspace is at most $k$). The
without-replacement pair
(`measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_samplingSketchWithoutReplacement`) takes
`HasLaw (fun ω => (X ω)ᴴ) (samplingSketchWithoutReplacement l n) μ`,
`hln : Fintype.card l ≤ Fintype.card n` and the coherence form
`hdom : ∀ i, leverageScore (truncatedSVD A k)ᴴ i ≤ L * (Fintype.card n : ℝ)⁻¹`. Routes:
`hasSubspaceInjection_of_hasLaw_samplingSketch_of_samplingInjectionSize_le` (resp. its
without-replacement twin) at $\mathbf{U} = \llbracket\mathbf{A}\rrbracket_k^{\mathsf{H}}$, accuracy
$1/2$; `isIsotropicSketch_of_hasLaw_samplingSketch` (resp. `…WithoutReplacement`, which needs
`hln`); A2.

#### HT1, `LowRank/Gaussian/RangeFinderTail.lean` (1, real; flagged, §4)

```lean
namespace SymmetricGauge

/-- **The tail of the randomized SVD with a Haar test matrix, Gram form**: the bound of
`NLAlib.SymmetricGauge.measureReal_not_matrixNorm_conjTranspose_mul_self_sub_rsvd_le_le_of_hasLaw_gaussianMatrix`
holds verbatim for an $n \times \ell$ Haar frame, outside probability <!-- value gaussianPinvFrobTail k d t -->
$e^{-(u-2)/4} + 2\sqrt{k}\,(d/(2t))^{d/2}/\Gamma(d/2 + 1)$: the range of
$\mathbf{A}\mathbf{\Omega}$ has the same law for both (`NLAlib.hasLaw_rangeProjector_mul_of_hasLaw_haarFrame`).
[TroppWebber2023, Theorem 8.1 (RSVD1)]; there Gaussian. Result: randomized-svd-tail -/
theorem measureReal_not_matrixNorm_conjTranspose_mul_self_sub_rsvd_le_le_of_hasLaw_haarFrame
    [DecidableEq l] (Φ : SymmetricGauge) (A : Matrix m n ℝ) (hX : HasLaw X (haarFrame n l) μ)
    {k d : ℕ} (hd : k + d = Fintype.card l + 1) (u : ℝ) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | ¬ Φ.matrixNorm ((A - rsvd A (X ω))ᴴ * (A - rsvd A (X ω))) ≤
        Φ.matrixNorm ((A - truncatedSVD A k)ᴴ * (A - truncatedSVD A k)) +
          Φ (Finsupp.single 0 1) * (u * t * k / d) * frobNorm (A - truncatedSVD A k) ^ 2} ≤
      Real.exp (-(u - 2) / 4) + gaussianPinvFrobTail k d t

end SymmetricGauge
```

Route: by `sub_rsvd` the event is $\{\mathbf{P} : \neg\,\Phi(\mathbf{A}^{\mathsf{H}}(\mathbf{I} -
\mathbf{P})\mathbf{A}) \le c\}$ at $\mathbf{P} = \mathbf{P}_{\mathbf{A}\mathbf{\Omega}}$, a closed set
(continuity of `Φ.matrixNorm`); its probability is the pushforward's
(`hasLaw_rangeProjector_mul_of_hasLaw_haarFrame`), which is the Gaussian probability, bounded by S3's
statement on the law space with `id` (`HasLaw id (gaussianMatrix n l) (gaussianMatrix n l)`). About
30 lines. Frobenius, spectral and Schatten corollaries are S3's corollaries at Haar, additive.

### 3.6 Arithmetic

- *RSVD $(1+\varepsilon)$* (A6 at $a = 1/2$, $\varepsilon_J^2 = \varepsilon/(4k)$): factor
  $1 + k\varepsilon_J^2/a^2 = 1 + \varepsilon$; JL failure $2/(\ell\varepsilon_J^2) = 8k/(\ell\varepsilon)
  \le \delta/2$ iff $16k \le \varepsilon\delta\ell$ (Gaussian, Rademacher, CountSketch); sub-Gaussian
  $(16c^2 - 1)\cdot 4k/(\ell\varepsilon) \le \delta/2$ iff $8(16c^2 - 1)k \le \varepsilon\delta\ell$. The
  OSI takes the other $\delta/2$. $k = 0$: trivial.
- *Early truncation $(1+\varepsilon)$* (C2: $a = 1 - x$, $\theta = x$, $x = \varepsilon/8$,
  $\sqrt{k}\,\varepsilon_J = x$): the factor of C1 at levels $\eta_w = (x/\sqrt{k})\mathrm{OPT}^2$,
  $\eta_\chi = x\,\mathrm{OPT}$ is
  $$f(x) = \frac{1 + x}{(1-x)^2} + \frac{x}{(1-x)^3}\,,$$
  and $f(x) \le 1 + 8x = 1 + \varepsilon$ for $0 \le x \le 1/8$ (checked numerically on
  $\varepsilon \in (0, 1]$: $(f - 1)/\varepsilon \le 0.656$; a `nlinarith` proof after clearing
  $(1-x)^3 \ge (7/8)^3$). JL failure $2/(\ell\varepsilon_J^2) = 128k/(\ell\varepsilon^2)$ per tail, two
  tails, plus the OSI at $\delta/3$: $384k \le \varepsilon^2\delta\ell$; sub-Gaussian
  $192(16c^2 - 1)k \le \varepsilon^2\delta\ell$; CountSketch's two tails $2/(\ell\varepsilon_J^2)$ each,
  the same $384$.
- *Late-truncated GN* (B3): $u^2 + (v + cu)^2 \le (1 + c)^2(u^2 + v^2)$ for $u, v, c \ge 0$
  (checked numerically, ratio at most $1$; proof: $(v + cu)^2 \le (\sqrt{u^2+v^2} + cu)^2 -
  u^2$ expands to $2cuv \le 2cu\sqrt{u^2+v^2}$).
- *SRHT bounded form* (A5 at $a = 1/2$, $L^2 = n/\ell$): $1 + L^2/a = 1 + 2n/\ell$.
- *Constant-factor OSI forms* (A2 at $a = 1/2$): $1 + t/a = 1 + 2t$.

## 4. Files

| # | File | Statements | Lines (est.) | Imports (new) | Depends on |
|---|---|---|---|---|---|
| 1 | `Sketching/Properties/LeastSquaresOblique.lean` (registered; side file `Sketching/Properties/LeastSquaresObliqueMultiplication.lean` until proved) | 1 (L1) | +40 | `Matrix/Norms/UnitarilyInvariant` if not transitive | none |
| 2 | `Sketching/Properties/Injection.lean` (registered; side file `Sketching/Properties/InjectionRandomDesign.lean`) | 3 (L2 to L4) | +120 | `Sketching/Properties/LeastSquaresOblique`, `Sketching/Properties/MatrixMultiplication`, `Probability/Measurability/Matrix`, `Matrix/Pseudoinverse/LeastSquares` | file 1 |
| 3 | `Matrix/Factorizations/SketchedLowRank.lean` (registered; side file `Matrix/Factorizations/SketchedLowRankSmul.lean`) | 1 (L5) | +8 | none | none |
| 4 | `Matrix/Spectral/LowRank.lean` (registered; side file `Matrix/Spectral/LowRankFrobenius.lean`) | 1 (L6) | +12 | none | none |
| 5 | `LowRank/Oblivious/RangeFinder.lean` (new) | 13 (A1 to A13) | 480 | `LowRank/Structural/RangeFinder`, `LowRank/Structural/Truncation`, `Sketching/Properties/Injection`, `Sketching/Properties/MatrixMultiplication`, `Matrix/Factorizations/NystromGram` | files 1, 2, 4 |
| 6 | `LowRank/Oblivious/GeneralizedNystrom.lean` (new) | 5 (B1 to B5) | 250 | file 5 | files 2, 4, 5 |
| 7 | `LowRank/Oblivious/EarlyTruncation.lean` (new; S9 appends U1, U2) | 6 (C1 to C6) | 340 (+55 for S9) | `LowRank/Structural/EarlyTruncation`, `Sketching/Properties/Injection`, `Probability/Measurability/Matrix` | file 2 |
| 8 | `LowRank/Oblivious/Gaussian.lean` (new) | 2 | 100 | file 7, `Sketching/Gaussian/Gaussian` | file 7 |
| 9 | `LowRank/Oblivious/Rademacher.lean` (new) | 4 | 190 | files 5, 7, `Sketching/Gaussian/Rademacher` | files 3, 5, 7 |
| 10 | `LowRank/Oblivious/SubGaussian.lean` (new) | 4 | 210 | files 5, 7, `Sketching/Gaussian/SubGaussian` | files 3, 5, 7 |
| 11 | `LowRank/Oblivious/CountSketch.lean` (new) | 4 | 220 | files 5, 7, `Sketching/Sparse/CountSketch` | files 5, 7 |
| 12 | `LowRank/Oblivious/SRHT.lean` (new) | 6 | 290 | file 5, `Sketching/Structured/SRHT` | file 5 |
| 13 | `LowRank/Oblivious/RowSampling.lean` (new) | 2 | 110 | file 5, `Sketching/Sampling/RowSampling` | file 5 |
| 14 | `LowRank/Oblivious/WithoutReplacement.lean` (new) | 2 | 100 | file 5, `Sketching/Sampling/WithoutReplacement` | file 5 |
| 15 | `LowRank/Gaussian/RangeFinderTail.lean` (registered, S3; side file `LowRank/Gaussian/RangeFinderTailHaar.lean`) | 1 (HT1) | +35 | `RandomMatrix/Haar/Transfer` if not transitive | none |

S7 is about 2,500 lines and 55 public declarations, no definition: 13, 5, 6 in the three generic
files, 24 in the seven family files, 7 added to registered files (L1 to L6, HT1). Every file stays
under 1000 lines and 25 statements; `Injection.lean` reaches about 340 lines, `RangeFinderTail.lean`
about 510.

**Order.** Files 1, 3, 4, 15 are independent; file 2 after 1. Then file 5; files 6 and 7 after 5
and 2 (7 does not need 5's statements but shares its imports, so the order 5, 6, 7 is a short
chain one proof agent may own). Files 8 to 14 are independent of one another after 5 and 7; two
proof agents at most (CONTRIBUTING §11), two or three family files each.

**Placement** (CONTRIBUTING §8 item 5; every declaration with its home and reason).
- **The rule for family instances: one file per Sketching family file,
  `LowRank/Oblivious/<F>.lean` for `Sketching/<Dir>/<F>.lean`** (Q3). A family statement answers
  "what does family $F$ buy for low-rank approximation"; it sits beside the other statements about
  $F$ at this layer, and a user who holds the Sketching file's predicate finds the LowRank file of
  the same name. Reasons over the alternative (beside the generic theorem in each algorithm file):
  (i) a new family (SparseStack, OSNAP; brief §0.2) adds one file and touches no generic file;
  (ii) the generic files stay small and import no family file, so a user of the generic theorems
  does not compile eight families' proofs; (iii) with all families beside the generic theorems,
  `RangeFinder.lean` would hold about 30 statements and pass the budget. The cost: a family
  statement is one file away from the generic theorem it instantiates, which its docstring names.
- Generic results, `LowRank/Oblivious/{RangeFinder,GeneralizedNystrom,EarlyTruncation}.lean`
  (D12's `Oblivious/`): consequences of a Sketching predicate for an algorithm, law-free. Not
  `LowRank/Structural/`: they are tails. Not `LowRank/Random/`: that directory holds law-free
  measurability and integrability.
- L1, `Sketching/Properties/LeastSquaresOblique.lean`: a deterministic bound on the oblique
  projector under an injection, beside its twin `frobNorm_obliqueProjector_mul_sq_le`.
- L2 to L4, `Sketching/Properties/Injection.lean`: sketch-and-solve tails under an injection, beside
  CEMT Theorem 2.7's fixed-design forms (their rule-4 neighbours). Not `MatrixMultiplication.lean`:
  approximate multiplication is an input of L3 and L4, not their subject. Not LowRank: they mention
  no low-rank output and Solvers consumes them.
- L5, `Matrix/Factorizations/SketchedLowRank.lean`: an identity of `rsvd`, beside its definition (S1
  §0 named this home).
- L6, `Matrix/Spectral/LowRank.lean`: a fact about `truncatedSVD`, beside `frobNorm_truncatedSVD_sq`.
- HT1, `LowRank/Gaussian/RangeFinderTail.lean`: the Haar case of S3's randomized SVD tail, proved
  from it by a law transfer; the subject is the Gaussian–Haar range finder tail, S3's topic. It is
  not an OSI-route statement and does not belong in `LowRank/Oblivious/Haar.lean` (there is no such
  file; Haar's OSI-route statements are deferred, D3).
- **Flags** (placed elsewhere until resolved; the stage report lists those still open):
  - Each registered home of files 1 to 4 and 15 takes its statements only proved and after its
    current owner (the Sketching asymptotic-forms agent for Sketching files; S9 for
    `MatrixMultiplication.lean`) has finished; until then the side files of the table, each saying
    it merges into its home.
  - L6 replaces S6's private real `frobNorm_truncatedSVD_le` in
    `LowRank/Gaussian/TruncatedGeneralizedNystrom.lean`: that private copy is deleted at the
    wrap-up (an edit to S6's proved file).
  - Docstring edits in registered files so that rule-4 neighbours name each other: S6b's
    `integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_one_add_mul_of_hasLaw_gaussianMatrix` (the
    Gaussian tail), `IsSubspaceInjection.frobNorm_obliqueProjector_mul_sq_le` (L1),
    `HasSubspaceInjection.measure_frobNorm_sub_mul_pinv_mul_sq_gt_le` (L3), S3's Gaussian Gram tail
    (HT1). Wrap-up, Sonnet.
  - `LowRank/Oblivious/EarlyTruncation.lean` is S7's; if S9's U1 is implemented first, S9 creates
    the file with U1 in its final home and S7 adds its sections before it (not a misplacement; Q9).
  - The registry's `latex` for `subgaussianEmbeddingDim` contains the symbol $C$; the sub-Gaussian
    docstrings need it replaced by its value (Q11). A `docs/constants.toml` edit outside S7's
    files, for the Sketching wrap-up.

## 5. Material

**Prototype** (`~/Documents/prove2me/lean/NLAlib/LowRank/`): no OSI or OSE route, no structured
families (brief §7: "no OSI route"). Nothing to port and nothing to ledger for S7.

**The maintainer's notes** (never cited; D13): `pcps-et-audited.tex` (`prop:et-deterministic`, the
core S2b proved; the OSE-plus-AMM tail it states is C1, C3 with explicit constants), the
formalization's `Theorems/*.lean` shapes (brief §4.4) for C4 to C6. Constants are this note's (§3.6).

**Literature**: the checks above. Citations; keys in `docs/references.bib` (no new key):
`CamanoEpperlyMeyerTropp2025`, `Woodruff2014`, `HalkoMartinssonTropp2011`, `TroppWebber2023`,
`CohenElderMuscoMuscoPersu2015`, `TroppYurtseverUdellCevher2017`.

| statement | citation | relation to the printed statement |
|---|---|---|
| L1 | [Woodruff2014, proof of Theorem 23] | there a basis and a $(1 \pm 1/2)$ embedding; here basis-free, any injection, every gauge |
| L2 | [CamanoEpperlyMeyerTropp2025, Theorem 2.7, proof of Corollary 2.8] | random design independent of the sketch; tail $\delta + 1/t$ |
| L3, L4 | [Woodruff2014, Theorem 23] | any injection and JL moment, matrix right-hand side, squared residual; L4 random design |
| A1 to A4 | [CamanoEpperlyMeyerTropp2025, Theorem 2.2, remark after Theorem 1.3]; A1 also [TroppWebber2023, Theorem 8.1] for the shape; A4 also [Woodruff2014, Lemma 48] | fixed subspace in place of an OSI; explicit $(1 + t/a)$ and $\delta + 1/t$; Gram form; truncation in Frobenius norm |
| A5 | [HalkoMartinssonTropp2011, Theorem 11.2] | any sketch with a spectral bound; every quadratic norm; factor $1 + L^2/a$ |
| A6 to A8 | [Woodruff2014, Lemmas 44, 45] | any injection constant, explicit; A8 any field with a raw multiplication tail |
| A9 to A12 | [CamanoEpperlyMeyerTropp2025, Corollary 2.5, Imported Theorem 2.4] | explicit; gauge and spectral forms; truncation |
| A13 | [Woodruff2014, Lemma 45] through [CamanoEpperlyMeyerTropp2025, Imported Theorem 2.4] | the Nyström form |
| B1, B2 | [CamanoEpperlyMeyerTropp2025, Corollary 2.8 and its proof] | over `𝕜`; co-range dimension $\min(\operatorname{rank}\mathbf{A}, \ell)$; explicit |
| B3 | proved without a literature source; comparison [CamanoEpperlyMeyerTropp2025, Remark 2.9] (a different estimator) | |
| B4, B5 | [Woodruff2014, Theorem 47, first part, and its proof] | explicit multiplication step |
| C1, C2, C3 | proved without a literature source (S2b's core); sketch conditions [CohenElderMuscoMuscoPersu2015, §7.2, proof of Theorem 12]; [Woodruff2014, Theorem 61] for the full-row-space form | |
| C4 to C6 | proved without a literature source, as a composition; algorithm [TroppYurtseverUdellCevher2017, §7.3.1, (7.3)] | |
| family RSVD statements | the generic theorem's source; CountSketch also [Woodruff2014, Remark 46]; SRHT also [HalkoMartinssonTropp2011, Theorem 11.2] | the instance with the family's explicit sizes |
| family early-truncation statements | [CohenElderMuscoMuscoPersu2015, §7.2] | explicit sizes and constants |
| HT1 | [TroppWebber2023, Theorem 8.1] | Haar by the range transfer |
| L5, L6 | helpers, no citation | |

**Result ids** (checked against `NLAlib/` and `explore/results.toml`): `randomized-svd-tail` (A1 to
A8, the family RSVD statements, HT1; existing, S3's), `randomized-nystrom-tail` (A9 to A13; S5's),
`generalized-nystrom-tail` (B1 to B5; new, the tail sibling of `generalized-nystrom-expected-error`),
`etrsvd` (C1, C2, C3, the family early-truncation statements), `etgn` (C4 to C6),
`sketch-and-solve-ls` (L2 to L4). L1, L5, L6 carry none.

## 6. Cut, and why

- **D1, per-family Nyström, generalized Nyström, truncated and early-truncated GN statements.**
  Nine families (counting SRHT and sampling twice) times five algorithms, each with an asymptotic
  form, is about 70 statements and 2,500 lines whose proofs are one application of a generic
  theorem to the family predicate. The generic theorems already take that predicate, and for
  generalized Nyström the two sketches may come from different families, which a per-family
  statement could not express without a product. Each family file's module docstring shows the two
  lines. Additive, family by family, if a consumer wants a named instance.
- **D2, the Gaussian RSVD instance.** S3's Tropp–Webber tail
  (`measureReal_not_frobNorm_sub_rsvd_sq_le_le_of_hasLaw_gaussianMatrix`) gives $1 + \varepsilon$ at
  $\ell = O(k\log(1/\delta)/\varepsilon)$; the OSI and multiplication routes give
  $O(k/(\varepsilon\delta))$. A dominated statement is not added (rule 6). The generic A2 and A6 apply
  to Gaussians in two lines.
- **D3, Haar OSI-route statements** (early truncation, the OSI forms): the Haar OSI exists only in
  tail form in $(t, s)$ (`isObliviousSubspaceInjection_of_hasLaw_haarFrame`); a size form is
  Sketching §6.1 item 5. About 150 lines after it. Haar RSVD is covered sharper by HT1, Haar
  co-range generalized Nyström by S6's identities.
- **D4, Woodruff Theorem 47's rank-$k$ clause**: Q8.
- **D5, late-truncated GN through approximate multiplication**: T10 with the Frobenius noise gives
  $1 + \varepsilon$ only at $p = O(k/\varepsilon^3)$, the triangle baseline S6 names; the spectral noise
  T11 needs spectral approximate multiplication (Sketching §6.1 item 3). About 60 lines; additive.
- **D6, SRHT and sampling early truncation**: the core needs the two multiplication tails. The SRHT
  has none in the library (a row-norm flattening under the transform, then sampling
  multiplication; about 150 lines, the S9 draft's D3); sampling multiplication needs probabilities
  dominating $\|\mathbf{E}_{:,i}\|\,\|\mathbf{P}_{i,:}\|$, which depend on the tail and are not
  the leverage scores. The row-space route exists through S2b's T7 and the S9 draft's C4.
- **D7, public orientation lemmas** (D2's "per-family orientation lemmas"): the family statements
  absorb the orientation and the scaling (§3.0 step 5); a public lemma per family would restate the
  family OSI with `Matrix.conjTranspose_smul`. About 60 lines; additive.
- **D8, the multiplication route over `𝕜` from the JL moment**: the library's JL-moment
  multiplication bound is real; CountSketch's own tail is over `𝕜`, so CountSketch has the route
  over `𝕜` now (A8, C2).
- **Spectral-norm generalized Nyström**: relative spectral bounds are impossible for one-pass
  methods (MT Remark 15.4; brief D4's table).
- **OSI corollaries of the fixed-subspace statements** (CEMT's literal shape): one term each
  (`h.hasSubspaceInjection _`, `h.isotropic`); stating them would double file 5. Q1.
- **HMT Theorem 11.2 as printed**: dominated by A5 and T2 ($1 + 2n/\ell$ against $1 + 7n/\ell$, failure
  $\delta$ against $O(k^{-1})$, both norms through the gauge).

## 7. Questions and decisions

Hard-to-reverse items are marked **(hard)**. Under the round's approval rule the maintainer decides
the hard ones; the rest proceed as recommended and are recorded here.

**Q1. The range-side hypothesis (hard).** Options: (a) the injection of the one subspace
$\operatorname{range}\llbracket\mathbf{A}\rrbracket_k^{\mathsf{H}}$,
`HasSubspaceInjection (fun ω => (X ω)ᴴ) (truncatedSVD A k)ᴴ a δ μ`, plus `IsIsotropicSketch` where a
Markov step needs it; Nyström and the co-range side take OSIs; (b) an OSI for dimension $k$
everywhere, as CEMT print it; (c) a frame $\mathbf{Z}$ with `HasOrthonormalCols Z` and
`A * Z * Zᴴ = truncatedSVD A k` as hypotheses. Recommendation (a): it is the hypothesis the proofs
use (CONTRIBUTING §5.2, minimal), it is exactly what row sampling satisfies, so sampling needs no
separate generic theorem, it involves no frame, and an OSI gives it in one term. (b) excludes
sampling and adds an unused "every subspace"; (c) puts a frame in every statement, which the
library's interfaces avoid. Nyström cannot use (a): its proof passes to a factor whose top-$k$
subspace is a different choice under ties (§3.0). Rework if reversed: every signature of files 5
to 7 and every family proof.

**Q2. Family-law spellings and the raw test matrix (hard).** Options: (a) Gaussian and Haar laws on
the test matrix (D2), every other law on the sketch `fun ω => (X ω)ᴴ` (the only orientation the
library states them in), and every conclusion about the output at the raw test matrix, with the
normalisation inside the proof (§3.0 step 5; early truncation through the projector form, so no
identification of outputs under ties is needed); (b) state the families at the normalised test
matrix, `rsvd A ((√ℓ)⁻¹ • X ω)`; (c) new test-matrix laws (`(countSketch l n).map conjTranspose`).
Recommendation (a): users run algorithms on the raw test matrix; (b) puts a scaling in every
conclusion and cannot be undone for early truncation under ties; (c) is a parallel object per
family. Rework if reversed: every family signature, and the pattern later families copy.

**Q3. The placement rule for family instances (not hard; the maintainer's attention).** Options:
(a) one LowRank file per Sketching family file (§4); (b) beside the generic theorem in each
algorithm file; (c) one LowRank file per Sketching family directory
(`LowRank/Oblivious/{Gaussian,Structured,Sparse,Sampling}.lean`). Recommendation (a), for §4's three
reasons; (c) is a variant with four files instead of seven and a less exact mirror (Haar,
Rademacher and sub-Gaussian would share a file named `Gaussian.lean`). Rework: file moves.

**Q4. Names of the approximate-multiplication route (not hard).** Brief D10 names the routes by a
suffix (`_of_hasJLMoment`). With that suffix `IsObliviousSubspaceInjection.measure_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_gt_mul_le_of_hasJLMoment`
is 110 characters and does not fit the 100-column limit, and two more pass 100. Recommendation:
the route's statements live in the namespace of the moment hypothesis, `HasJLMoment.measure_…`,
which names the hypothesis that distinguishes them (rule 4) and gives `hJL.measure_…`; the OSI
route keeps the injection namespaces. The suffix `_gt_mul_le` marks a bound that is a multiple of
another algorithm's error (B1, B4, C4, C5), as S6's `_le_mul_integral_`. Rework: renames.

**Q5. Asymptotic forms of constant-factor results (not hard; a reading of rule 3).** The SRHT and
sampling statements have no accuracy parameter: their factor is $1 + 2t$, from the injection
accuracy $1/2$. Options: (a) `∃ C : ℝ, 0 < C ∧ ∀ …` with no $\varepsilon_0$ and the conclusion as in
the explicit form; (b) a dummy $\varepsilon$ with factor $1 + t/(1 - \varepsilon)$; (c) no asymptotic
form. Recommendation (a): rule 3 asks for "$O(\cdot)$ suffices" for every sample-size result, and
$\varepsilon_0$ exists in the template only to bound an accuracy; (b) carries a parameter no reader
wants. `scripts/check_refs.py` checks the tag and the `exists_forall_` name, not the binder list.

**Q6. Which family statements (not hard).** Options: (a) §0.2's cut: the randomized SVD for every
family with a size form (by approximate multiplication where the family has it, by the OSI route
otherwise), early truncation for the four families with multiplication tails, SRHT's bounded form,
HT1; (b) the fallback of §0.2 (RSVD only, about 1,700 lines in total); (c) every algorithm for every
family (about 5,000 lines). Recommendation (a): the RSVD and early-truncation instances are where
the families' sizes differ in kind ($k^2$ for CountSketch, $\log n$ for SRHT, leverage for
sampling); the S9 draft's cut of its own per-family early truncation relies on S7 stating them;
(c) is compositions.

**Q7. Gaussian and Haar instances (not hard).** No Gaussian RSVD instance (D2, dominated). Haar:
HT1 in S3's file by law transfer, flagged; the OSI-route Haar statements wait for a Haar size form
(D3). Alternative: no Haar statement at all. Recommendation: HT1, 30 lines, since a user with a Haar
frame has no randomized-SVD tail otherwise.

**Q8. Woodruff Theorem 47's rank-$k$ clause: the D15 check (not hard).** The estimator is $\mathbf{Z}
\mathbf{S}\mathbf{A}$ with $\mathbf{Z}$ the best rank-$k$ solution of $\min\|\mathbf{Z}\mathbf{S}
\mathbf{A}\mathbf{R} - \mathbf{A}\mathbf{R}\|_{\mathsf{F}}$; $\mathbf{Z}$ depends on $\mathbf{R}$, so
the step "by the properties of an $\ell_2$-subspace embedding" needs $\mathbf{R}$ to preserve
$\|(\mathbf{Y}\mathbf{S}\mathbf{A} - \mathbf{A})\mathbf{R}\|_{\mathsf{F}}$ uniformly in $\mathbf{Y}$: an
affine embedding. Splitting $\mathbf{Y}\mathbf{S}\mathbf{A} - \mathbf{A}$ into its part in the row
space of $\mathbf{S}\mathbf{A}$ (dimension $s$, the rows of $\mathbf{S}$) and the fixed residual, the
uniform statement needs (i) a $(1 \pm \varepsilon)$ embedding of an $s$-dimensional space, (ii)
Frobenius preservation of the residual, and (iii) approximate multiplication between the residual and
that space at accuracy $\varepsilon/\sqrt{s}$; Woodruff's text states (i) and omits (iii). With (iii)
the clause holds, at $p = O(s/\varepsilon^2) = O(k/\varepsilon^3)$ for dense sketches, which is the
dimension Woodruff's $\mathbf{R}$ already has; the retracted "Lemma B" claimed $O(s/\varepsilon)$, where
(i) fails. So the published route avoids the false lemma by its larger dimension and an unstated
multiplication step. Recommendation: not ported. It is a new estimator with no named output
(rank-constrained sketched regression, S2a Q8), its $p = O(k/\varepsilon^3)$ is beaten by S6's TG5
($\varepsilon^{-2}$, Gaussian) and by C6 for early truncation ($p = O(k/\varepsilon)$), and no stage
consumes it. Recorded in brief §8's "not ported" list at the wrap-up.

**Q9. What S7 gives S9, and who owns `LowRank/Oblivious/EarlyTruncation.lean` (not hard;
coordination).** The S9 draft's U2 (early-truncated generalized Nyström through a PCP) needs "S7's
random-subspace completion tail" and its Q7 left the home to this note. S7 provides: (i) L2,
`IsObliviousSubspaceInjection.measure_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_indepFun`, the
completion tail for a general random design, in `Sketching/Properties/Injection.lean`; (ii) C4,
`IsObliviousSubspaceInjection.measure_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_gt_mul_le`, its
early-truncated GN instance, with exactly U2's co-range hypotheses (OSI for dimension $k$ on
`fun ω => (Ψ ω)ᴴ`, `IndepFun X Ψ μ`, `AEMeasurable` of both, `[IsProbabilityMeasure μ]`). U2 is then
the union of U1's and C4's events with $a \ge 0$, about 15 lines in place of the draft's 35, and
cites C4. S7 also provides the per-family early-truncation statements the S9 draft's §6 cut
relies on (Gaussian, Rademacher, sub-Gaussian, CountSketch; not SRHT, sampling or Haar, which S9
defers too). **Ownership: S7** creates and owns `LowRank/Oblivious/EarlyTruncation.lean` (its topic is
early truncation through sketch properties, and five of its eight statements are S7's); S9 appends
U1 and U2 in a final section importing `Sketching/Properties/ProjectionCost`. If S9's U1 lands first,
S9 creates the file with U1 and S7 inserts its sections before it. Recommended order: S7 before S9,
as the brief.

**Q10. Sketched regression in S7 (not hard).** The brief puts no stand-alone regression in S7 (D8:
deterministic facts in `Sketching/Properties/LeastSquares.lean`, Gaussian and Haar in S6); CEMT
Theorem 2.7 is already in `Injection.lean`. S7 adds the regression statements its generalized
Nyström results need and nothing else: L2 (random design, OSI), L3 (Woodruff Theorem 23 in matrix
form, any injection and JL moment) and L4 (its random-design form), in the Sketching layer, spelled
with `sketchAndSolve` per the maintainer's error rule; the existing raw-spelled neighbours are not
respelled (D1). Alternative: L3 only as a private step of L4. Recommendation: public, since Solvers
wants the fixed-design $(1+\varepsilon)$ form with structured sketches.

**Q11. Corrections of record (information).**
- Brief §7 S7: three files and 850 lines become ten new files, six additions and about 2,500 lines
  (§0.2); the growth is the family statements with rule 3's asymptotic forms, the
  multiplication route and HMT 11.2.
- Brief §4.3 and §9.3 ("early truncation by OSE plus AMM, Woodruff Theorem 61 shape"): Theorem 61 is
  the full-row-space route (S2b Q6); the head-plus-tail tails here cite CEMMP §7.2 and S2b's core.
- Brief §4.3 "HMT §11 … dominated by the OSI route": the Frobenius OSI route (factor $1 + 2t$, failure
  $\delta + 1/t$) does not dominate HMT's spectral bound; the bounded-sketch route A5 does, in both
  norms.
- Brief D10's suffix names: Q4.
- Brief §4.3 "GN (CEMT Corollary 2.8). $\mathbf{\Psi}^{\mathsf{H}}$ is an OSI of dimension $\ell$":
  dimension $\min(\operatorname{rank}\mathbf{A}, \ell)$ suffices (B1, B2).
- CEMT Corollary 2.8 is printed over $\mathbb{R}$; B1 to B3 are over `𝕜` (the proof is field-free).
- `docs/constants.toml`, `subgaussianEmbeddingDim`: its `latex` template contains the symbol $C$ for
  `subgaussianJLConstant`, which the maintainer's rule of 2026-10-15 (values inside the formula)
  forbids in a docstring; the template should read `256 #1^2 (#2 \log 9 + \log(2/#4))/#3^2` with a
  `previous_latex` update through `scripts/check_constants.py --update` (a Sketching wrap-up edit;
  the existing Sketching docstring "with $C = 1/64$" is the old style, replaced when touched).
- Nested named sizes: the SRHT size `samplingInjectionSize k (β * srhtRowBound n k (δ / 2)) …`
  shows one registered value inside another's argument, and its marker with the inner value
  written out exceeds the 100-column limit. Recommendation: allow the marker's argument to be the
  inner bound's LaTeX template name, or a marker split across lines, in `scripts/check_constants.py`
  (a tooling question for the orchestrator; the Sketching SRHT docstrings meet the same case).
- S1 Q6 ("OSI form only in squared Frobenius norm; additive if S7 finds a spectral consumer"): the
  consumer is Nyström preconditioning (A11), and the Gram form A1 costs about 20 lines over A2.

## 8. Amendments from the review (2026-10-16)

Review of this note (fifteen amendments: one high, item 5; one medium, item 1; eight low, items
2 to 4, 6 to 10 and 12; four for information, items 11, 13, 14, 15; besides them, the mathematics
checks and five verdicts), all fifteen accepted by the orchestrator; none rejected. Two points are
extended on inspection: amendment 2's Markov step stays in `Sketching/Properties/Injection.lean`,
with a placement flag, because its topic home `Probability/Tail.lean` is being extended by S9 now
(item 2); and amendment 1's union lemma is stated with the sketch $\mathbf{S}$ applied to the
residual, $\|\mathbf{S}(\mathbf{I} - \mathbf{P}_{\mathbf{Y}})\mathbf{B}\|_{\mathsf{F}}$, which in
the consumers' orientation $\mathbf{S} = \mathbf{\Psi}^{\mathsf{H}}$ is the reviewer's
$\|\mathbf{\Psi}^{\mathsf{H}}(\mathbf{I} - \mathbf{P}_{\mathbf{Y}})\mathbf{B}\|_{\mathsf{F}}$ (item 1).
The review found the mathematics sound: every statement true at every rank and shape, the
constants against CEMT (Theorem 2.2's $1 + t/a$ at $\delta + 1/t$, Corollary 2.8's product), the
orientation (every hypothesis on `fun ω => (X ω)ᴴ` or `fun ω => (Ψ ω)ᴴ`, every algorithm on the raw
test matrices), A1's chain including $k = 0$ and $k \ge \operatorname{rank}\mathbf{A}$, A5 without
isotropy, A6 to A8 against Woodruff Lemma 45, the Nyström tie argument, C2's arithmetic
($f(1/8) \approx 1.656$), the family arithmetic of §3.6, and the D15 check of Woodruff Theorem 47;
one proof route (B3) is restated (item 1). Q1 and Q2 are decided as (a) (item 16). Where an item
below contradicts §0 to §7, it supersedes them; §3's signatures stand except as amended here.

1. **Amendment 1, B3's route; a union-of-events lemma on a random design** (§3.1 L2, §3.3 B3, §3.0
   step 4). B1's good event is only the bound event and does not carry the rank identity
   $\operatorname{rank}(\mathbf{\Psi}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega}) =
   \operatorname{rank}(\mathbf{A}\mathbf{\Omega})$ that `frobNorm_sub_generalizedNystrom_sq` and
   T10 need. New public lemma in `Sketching/Properties/Injection.lean`, the random-design twin of
   the two events every OSI tail uses:
   ```lean
   theorem IsObliviousSubspaceInjection.measure_not_isSubspaceInjection_union_gt_le_of_indepFun
       [IsProbabilityMeasure μ] (h : IsObliviousSubspaceInjection S d a δ μ) (ht : 0 < t)
       {Y : Ω → Matrix n q 𝕜} {B : Ω → Matrix n r 𝕜} (hind : IndepFun S (fun ω => (Y ω, B ω)) μ)
       (hS : AEMeasurable S μ) (hY : AEMeasurable Y μ) (hB : AEMeasurable B μ)
       (hrank : ∀ᵐ ω ∂μ, (Y ω).rank ≤ d) :
       μ.real ({ω | ¬ IsSubspaceInjection (S ω) (Y ω) a} ∪
         {ω | t * frobNorm ((1 - rangeProjector (Y ω)) * B ω) ^ 2 <
           frobNorm (S ω * ((1 - rangeProjector (Y ω)) * B ω)) ^ 2}) ≤ δ + 1 / t
   ```
   Proof: §3.0 step 4, the section bound for fixed $(\mathbf{y}, \mathbf{b})$ of rank at most $d$
   being item 2's Markov step with the good set the injection event (`h.hasSubspaceInjection`) and
   the mean $\|(\mathbf{I} - \mathbf{P}_{\mathbf{y}})\mathbf{b}\|_{\mathsf{F}}^2$ (`h.isotropic`).
   L2, B1 and C4 are its corollaries through `IsSubspaceInjection.frobNorm_sub_mul_pinv_mul_sq_le`;
   B3 uses it directly: on the complement, `IsSubspaceInjection.rank_mul_eq` gives the rank
   identity and `IsSubspaceInjection.frobNorm_obliqueProjector_mul_sq_le` gives
   $\|\mathbf{\Pi}\mathbf{C}\|_{\mathsf{F}}^2 \le \|\mathbf{\Psi}^{\mathsf{H}}\mathbf{C}\|_{\mathsf{F}}^2/a'
   \le (t'/a')\|\mathbf{C}\|_{\mathsf{F}}^2$ for $\mathbf{C} = \mathbf{A} -
   \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})$, then L6 and §3.6's arithmetic, and A4's event for
   the range side. No result id (a helper of the tails); about 30 lines.
2. **Amendment 2, the Markov-plus-union step is public and reused** (§3.0 steps 2 and 3).
   `measureReal_le_add_one_div` (private in `Sketching/Properties/Injection.lean`) becomes public,
   with a docstring, unchanged in statement. A1 to A4, A9 to A12 and item 1's section bound call it
   instead of repeating Markov's inequality. Placement: its statement has no sketch in it, so its
   topic home is `Probability/Tail.lean` beside `measureReal_ge_le_integral_div`; that file is S9's
   now (S9 §8 item 14), so the lemma stays in `Injection.lean` and is flagged, to move at the
   wrap-up after S9 (§4 flags; item 17).
3. **Amendment 3, HT1's permanent home** (§3.5 HT1, §4 file 15 and its flag). HT1 goes to a new
   `LowRank/Gaussian/RangeFinderTailHaar.lean`, topic "the Haar case of the randomized SVD tail, by
   range transfer", mirroring `EarlyTruncationHaar.lean` (maintainer, 2026-10-16). No edit to S3's
   `RangeFinderTail.lean` and no open flag. Family half.
4. **Amendment 4, one OSI corollary of A2** (§6 "OSI corollaries", §3.2). Added to
   `LowRank/Oblivious/RangeFinder.lean` after A2, the citable CEMT Theorem 2.2 by name:
   ```lean
   theorem IsObliviousSubspaceInjection.measure_frobNorm_sub_rsvd_sq_gt_le [IsFiniteMeasure μ]
       {A : Matrix m n 𝕜} {k : ℕ} {a δ t : ℝ}
       (h : IsObliviousSubspaceInjection (fun ω => (X ω)ᴴ) k a δ μ) (ha : 0 < a) (ht : 0 < t) :
       μ.real {ω | (1 + t / a) * frobNorm (A - truncatedSVD A k) ^ 2 <
         frobNorm (A - rsvd A (X ω)) ^ 2} ≤ δ + 1 / t
   ```
   Docstring: [CamanoEpperlyMeyerTropp2025, Theorem 2.2]; Result: randomized-svd-tail. No Gram,
   spectral, truncated or generalized Nyström OSI forms (§6's bullet stands for those).
5. **Amendment 5, the family half cut to what differs in kind** (§0.2 items 8 to 10, §3.5, Q5,
   Q6; maintainer, 2026-10-16). (a) No asymptotic forms for constant-factor results: the SRHT
   (both models), the SRHT bounded form and both sampling statements have factor $1 + 2t$ or
   $1 + 2n/\ell$ and no accuracy parameter; their explicit docstrings name the family's OSI
   asymptotic form instead. Q5 is decided as (c). (b) No `LowRank/Oblivious/Rademacher.lean`: the
   sub-Gaussian statements instantiate at proxy $1$ in three lines, shown in `SubGaussian.lean`'s
   module docstring. (c) Kept: the explicit/asymptotic pairs, Gaussian early truncation (one pair),
   sub-Gaussian and CountSketch RSVD and early truncation (two pairs each); the SRHT explicit RSVD
   without and with replacement and the bounded form; the sampling explicit RSVD with and without
   replacement; HT1. Family half: 16
   declarations, about 800 lines, in `LowRank/Oblivious/{Gaussian,SubGaussian,CountSketch,SRHT,
   RowSampling,WithoutReplacement}.lean` and `LowRank/Gaussian/RangeFinderTailHaar.lean`.
6. **Amendment 6, generic half right-sized; B3 kept** (§0.2 items 1 to 7). About 1,250 lines after
   items 1, 2 and 4. B3 stays (maintainer scope, item 17).
7. **Amendment 7, HMT Theorem 11.2 wording** (opening list, §3.5 SRHT bounded form, §6 last
   bullet, Q11). "Ported in a sharper form" becomes "sharper factor ($1 + 2n/\ell$ against
   $1 + 7n/\ell$), explicit failure probability, incomparable size condition" (rule 4 wording), in
   the docstrings of A5 and of the SRHT bounded form and in Q11's correction of brief §4.3. §6's
   bullet "dominated by A5 and T2" is withdrawn: A5 and HMT 11.2 are incomparable, both kept as
   neighbours.
8. **Amendment 8, two tail-naming conventions recorded** (§2 "Tails"). S3 and S5 spell root-level
   tails `measureReal_not_…_le_le_of_hasLaw_gaussianMatrix`; S7 and the Sketching round spell
   `measure_…_gt_le` / `measureReal_…_gt_le_of_<law>` with the event $\{c < X\}$. Both are allowed by
   CONTRIBUTING §4. S7 keeps `_gt_le` (it composes with Sketching's events literally); the stage
   report records the split, so a later rename is one decision.
9. **Amendment 9, explicit casts** (every generic and family signature with a natural number in a
   real product or quotient). `(k : ℝ) * ε ^ 2 / a ^ 2`, `(d : ℝ) * ε ^ 2 / a ^ 2`,
   `(A.rank : ℝ) * ε ^ 2 / a ^ 2`, `√(k : ℝ)`, `(Fintype.card n : ℝ) / (Fintype.card l : ℝ)`;
   the signatures of §3.1 to §3.4 read so.
10. **Amendment 10, sampling's size monotonicity** (§3.5 RowSampling). `samplingInjectionSize_mono`
    needs `δ ≤ d'`; the family proof branches on `(truncatedSVD A k)ᴴ.rank = 0` and otherwise
    compares $\log(r/\delta) \le \log(k/\delta)$ for $1 \le r \le k$ directly. No `δ ≤ k`
    hypothesis is added. Family half.
11. **Amendment 11, Woodruff Theorem 47's rank-$k$ clause, the recorded reason** (Q8). The wrap-up
    entry in brief §8's "not ported" list reads: "provable at $O(k/\varepsilon^3)$, dominated by
    S6's TG5 ($\varepsilon^{-2}$) and by C6, no named output, no consumer", not "no rigorous
    source"; the claim that Woodruff's $\mathbf{R}$ already has $O(s/\varepsilon^2)$ columns is
    checked against pp. 66 to 67 when the entry is written.
12. **Amendment 12, no side files** (§4 files 1 to 4 and the first flag; maintainer, 2026-10-16).
    L1 to L6 and item 1's lemma land in their registered homes in the same PR, proved; the four
    side files and the flag are dropped. A registered file receives only proved declarations.
13. **Amendment 13, `hS : AEMeasurable S μ` kept** (L2, L4, B1, B4, C4, C5). It follows from
    isotropy (`MemLp` entries), and is kept for consistency with Sketching's
    `measure_not_isSubspaceInjection_le_of_indepFun`; a conscious exception to "nothing that
    follows from another hypothesis", shared with Sketching S1. B1, B4, C4, C5 take
    `hX : AEMeasurable X μ` and `hΨ : AEMeasurable Ψ μ` and derive the sketch's measurability.
14. **Amendment 14, result ids** (§5). "Checked against `explore/results.toml`" becomes "new id
    `generalized-nystrom-tail`, no registry entry needed"; result ids are free-form `Result:` lines.
15. **Amendment 15, tooling** (Q11). The `subgaussianEmbeddingDim` template and the nested SRHT
    marker are orchestrator items for the Sketching wrap-up; no change to S7's scope.
16. **Q1 and Q2 decided: (a)** (maintainer, 2026-10-16; review verdict 5). The range side takes the
    one fixed subspace $\operatorname{range}\llbracket\mathbf{A}\rrbracket_k^{\mathsf{H}}$ with
    isotropy where Markov is used; family laws stay in the sketch orientation, conclusions at the
    raw test matrix. *Nyström exception*: Nyström (A9 to A13) takes an OSI for dimension $k$,
    since under a tie $\lambda_{k-1}(\mathbf{H}) = \lambda_k(\mathbf{H})$ the top subspace of the
    factor $\mathbf{F}$ need not be the one of $\llbracket\mathbf{H}\rrbracket_k$. Q3, Q4, Q7 to
    Q11 stand as recommended; Q5 is (c) and Q6 is (a) as cut by item 5.
17. **Scope, files and count after the amendments** (maintainer, 2026-10-16; supersedes §0.2's
    cut and the §4 table and its size paragraph). About 2,050 lines and 48 public declarations.
    *Generic half* (32 declarations, about 1,250 lines; one agent):

    | File | Statements | Lines (est.) |
    |---|---|---|
    | `Sketching/Properties/LeastSquaresOblique.lean` (registered) | L1 | +45 |
    | `Sketching/Properties/Injection.lean` (registered) | item 1's lemma, L2 to L4; `measureReal_le_add_one_div` made public | +140 |
    | `Matrix/Factorizations/SketchedLowRank.lean` (registered) | L5 | +8 |
    | `Matrix/Spectral/LowRank.lean` (registered) | L6 | +12 |
    | `LowRank/Oblivious/RangeFinder.lean` (new) | A1 to A13 and item 4's OSI corollary (14) | 490 |
    | `LowRank/Oblivious/GeneralizedNystrom.lean` (new) | B1 to B5 | 250 |
    | `LowRank/Oblivious/EarlyTruncation.lean` (new) | C1 to C6 | 340 |

    *Family half* (16 declarations, about 800 lines; another agent, after the generic half):
    item 5's files, `Gaussian.lean` (100), `SubGaussian.lean` (210), `CountSketch.lean` (220),
    `SRHT.lean` (140), `RowSampling.lean` (50), `WithoutReplacement.lean` (45), and
    `LowRank/Gaussian/RangeFinderTailHaar.lean` (35). Every sample-size result of the family half
    that has an accuracy parameter gets its asymptotic form (CONTRIBUTING §5.2 rule 3) and each
    pair names the other; the generic half states tails only, so it has none.

    **Placement of every addition outside the new files** (CONTRIBUTING §8 item 5; supersedes §4's
    list):

    | Declaration | Home | Reason |
    |---|---|---|
    | L1 `IsSubspaceInjection.matrixNorm_obliqueProjector_mul_le` | `Sketching/Properties/LeastSquaresOblique.lean` | a deterministic bound on the oblique projector under an injection, beside its Frobenius twin |
    | `measureReal_le_add_one_div` (made public) | `Sketching/Properties/Injection.lean`, **flagged**: topic home `Probability/Tail.lean` | a Markov-plus-union tail with no sketch in it; Tail is S9's file now; moved at the wrap-up |
    | item 1's union lemma | `Sketching/Properties/Injection.lean` | the random-design form of the two events of CEMT Lemma 2.1 and Theorem 2.7, beside them |
    | L2 to L4 | `Sketching/Properties/Injection.lean` | sketch-and-solve tails under an injection, beside CEMT Theorem 2.7's fixed-design forms |
    | L5 `rsvd_smul_right` | `Matrix/Factorizations/SketchedLowRank.lean` | an identity of `rsvd`, beside its definition |
    | L6 `frobNorm_truncatedSVD_le` | `Matrix/Spectral/LowRank.lean` | a fact about `truncatedSVD`, beside `frobNorm_truncatedSVD_sq`; S6's private real copy in `TruncatedGeneralizedNystrom.lean` is deleted (item 19) |

    Open flags at S7's report: the home of `measureReal_le_add_one_div`; the rule-4 docstring
    edits of §4's third flag (wrap-up). (The deletion of S6's private `frobNorm_truncatedSVD_le`
    was done during implementation, item 19.)
18. **The S9 hand-off** (S9 §8 item 3; maintainer, 2026-10-16). S7 creates and owns
    `LowRank/Oblivious/EarlyTruncation.lean` with C1 to C6. S9 appends U1
    (`HasProjectionCostPreserving.measure_mul_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le`) and U2
    (`HasProjectionCostPreserving.measure_mul_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_gt_le`)
    in a final section of that file after S7, with S7's variables, importing
    `Sketching/Properties/ProjectionCost`; U2 is the union of U1's and C4's events. S7 provides L2,
    item 1's lemma and C4 for it. Q9 is settled so.
19. **Implementation of the generic half (2026-10-16; amends items 1, 4, 17 and §3.1 to §3.4).**
    All proved, no `sorry`, axioms `propext`, `Classical.choice`, `Quot.sound` only. Divergences:
    - *`hδ' : 0 ≤ δ'` on every JL-moment statement* (L3, L4, A6, A7, A13, B4, C3, C5; `hδ₁`,
      `hδ₂` on B5, C6). With an empty column index the JL moment property is vacuous and the
      event empty, so the bound $\delta + \delta'$ needs $\delta' \ge 0$; the precedent is
      `HasJLMoment.hasSubspaceEmbedding (hδ : 0 ≤ δ)`.
    - *`[IsFiniteMeasure μ]` added* to A5, A6 to A8, A13, C1 to C3 (`measureReal_mono`).
    - *One public lemma more*, in `LowRank/Oblivious/RangeFinder.lean`:
      `HasJLMoment.measure_frobNorm_sub_truncatedSVD_mul_mul_conjTranspose_mul_rangeProjector_gt_le`,
      the tail–head multiplication tail $\varepsilon\sqrt{k}\,\|\mathbf{E}\|_{\mathsf{F}}$ from the
      JL moment property, shared by A7 and C3 (and by the family half). The generic half has 33
      public declarations; `measureReal_le_add_one_div` is made public besides.
    - *The JL exponent is `q`* in `GeneralizedNystrom.lean` and `EarlyTruncation.lean`, where `p`
      is the co-range index type.
    - *S6's private `frobNorm_truncatedSVD_le`* (`LowRank/Gaussian/TruncatedGeneralizedNystrom.lean`)
      is deleted now, not at the wrap-up: the public L6 has the same name and signature, so the
      private copy no longer compiled. That flag of item 17 is closed.
    - *Sizes*: `RangeFinder.lean` 674 lines (15 statements), `GeneralizedNystrom.lean` 297 (5),
      `EarlyTruncation.lean` 448 (6); `Injection.lean` +237 (to 458), `LeastSquaresOblique.lean`
      +53, `SketchedLowRank.lean` +8, `Spectral/LowRank.lean` +11: about 1,730 lines against the
      estimate of 1,250, the excess being docstrings and the degenerate-case branches.
    - *U1, U2 and the Markov step (2026-10-16; items 17, 18).* S9's U1
      `HasProjectionCostPreserving.measure_mul_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le` and U2
      `HasProjectionCostPreserving.measure_mul_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_gt_le`
      are proved in a final section of `LowRank/Oblivious/EarlyTruncation.lean` (now 552 lines,
      8 statements), with the signatures of S9 §3.6 unchanged: U1 from
      `hasProjectionCostPreserving_conjTranspose_iff` and T6 under `measureReal_mono`, U2 as the
      union of U1's event and C4's. No new import (`ProjectionCost` comes through
      `LowRank/Structural/EarlyTruncation`); U2 carries `set_option linter.style.longLine false in`
      for its 101-character name. No per-family instance (cut, S9 §6 and Q6).
      `measureReal_le_add_one_div` is moved, statement and name unchanged, to
      `Probability/Tail.lean` beside `measureReal_ge_le_integral_div`; it is item 2's Markov step
      itself, so nothing else moves. `Injection.lean` already imported `Tail`. The flag of item 17
      on its home is closed.
