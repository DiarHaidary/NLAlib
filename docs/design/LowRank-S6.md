# Design note: LowRank stage S6, sketched regression and generalized Nyström, Gaussian and Haar

Status: drafted 2026-10-15 under `docs/PORT_LOWRANK.md` (maintainer decisions of 2026-10-15,
binding: every error spelled as the matrix minus the algorithm's named output,
`A - generalizedNystrom A (X ω) (Ψ ω)`, `B - A * sketchAndSolve A (S ω) B`; early-truncated
outputs named, `earlyTruncatedGeneralizedNystrom`, late truncation
`truncatedSVD (generalizedNystrom A (X ω) (Ψ ω)) k`; the maintainer's early-truncated GN bound with
$\varepsilon^{-2}$ dependence is the primary early-truncation statement, proved without a
literature source, TYUC SIMAX cited for the algorithm only; the Chen–Persson manuscript is never
cited; docstrings write outputs as $\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})$,
$\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})$, $\mathsf{earlyTruncatedGN}(\mathbf{A},
\mathbf{\Omega}, \mathbf{\Psi}, k)$, $\mathsf{sketchAndSolve}(\mathbf{A}, \mathbf{S},
\mathbf{B})$; named constants show their values through the registry markers of
`docs/constants.toml` and `scripts/check_constants.py`; D2, D3, D4, D8, D9 to D15; §4.3 "GN",
"Truncated GN", "Sketch-and-solve" and "Haar $\mathbf{\Psi}$"; the S6 entry of §7; §9.3), and
`docs/design/LowRank-S0.md` to `LowRank-S5.md` and `LowRank-S2c.md` (§8 of each overrides its
§3; all proved and registered). `docs/design/LowRank-S4.md` is being drafted in parallel and was
not on disk when this note was written; §0.2 states the division of Epperly and Webber's results
and the exact S4 statements S6 consumes, and Q7 the order. Real field for every probabilistic
statement (D3); the deterministic and law-free additions are over `𝕜`. Every shape, rank and
target rank; side conditions are those the proofs need and no more (§3.0). Reviewed 2026-10-15
(ten amendments: three medium, four low, three for information; no blocker), amendments in §8,
which overrides §0 to §7 where they disagree (§3 stays as drafted); all ten accepted, none
rejected, three points corrected on inspection (§8 items 2, 8 and 13: A2's marker count, A8's
threshold 3300, which is false, the slack closing at 6600 with 8000 kept, and V3's AMM constant).
S4 is now on disk: GN7 and GH5 take its free rank parameter and §0.2's provisional spellings
become its names (§8 item 1); `haarProjectionFactor` is registered and moves to
`RandomMatrix/Haar/Blocks.lean` (items 3, 6); early-truncated GN gets its own file (item 4); A11'
is public (item 7). Q1 and Q2 decided as (a) (items 11, 12). The maintainer scheduled **S6b**,
early-truncated RSVD in expectation, between the Gaussian and Haar halves, so the early-truncated GN
$\varepsilon^{-2}$ statement is unconditional (§8 item 13, which specifies S6b's twelve statements
and replaces a separate S6b note). 70 public declarations in 13 files: 58 for S6, 12 for S6b
(§8 item 15).

Departures from the brief, each argued below:
- **Three new files plus additions to six registered files and S4's Haar block file**, about 2200 lines and 57 public
  declarations (§4), against the brief's three files and 1150 lines. The growth: the Haar half
  (about 450 lines, the brief's "both laws" in full), the law-free-in-$\mathbf{X}$ forms that S7 and
  S9 compose with (about 200), the lower-layer moment infrastructure truncated GN needs and the
  library lacks (about 330), and integrability companions (D4).
- **The spectral second moment of $\mathbf{S}\mathbf{G}\mathbf{T}$ is reached through Gaussian
  concentration, not TW Lemma B.1.** The library proves Chevet's first moment by Sudakov–Fernique;
  TW's second-moment form needs a second-moment Slepian comparison the library does not have.
  Concentration gives $\mathbb{E}\|\mathbf{S}\mathbf{G}\mathbf{T}\|_2^2 \le (\|\mathbf{S}\|_2
  \|\mathbf{T}\|_{\mathsf{F}} + \|\mathbf{S}\|_{\mathsf{F}}\|\mathbf{T}\|_2)^2 + \|\mathbf{S}\|_2^2
  \|\mathbf{T}\|_2^2$ in about 40 lines from registered lemmas (Q3). Truncated GN's constants change
  accordingly: `truncatedGNFactor`'s body has $(25g + 484)/p$ where the brief has
  $(18g + 408)/p$ (Q2, §3.7).
- **Truncated GN needs no rank hypothesis and fewer size conditions** than the brief:
  $4k \le \ell$ and $4\ell \le p$, where the brief has $\ell \ge 4k + 2$, $p \ge 4\ell$ and
  $\operatorname{rank}\mathbf{A} \ge \ell$. The case $\operatorname{rank}\mathbf{A} \le \ell$ is the
  exact branch (the output is $\llbracket\mathbf{A}\rrbracket_k$ almost surely), handled inside the
  proof; $k = 0$ is trivial and needs no condition on $\ell$.
- **Truncated GN is stated directly on `truncatedSVD`**, with no selector hypothesis: S2c made
  `truncatedSVD` Borel measurable (`measurable_truncatedSVD`), and S2a's T11 holds for every choice
  of the truncation. S2c's template K20 is TG5 (§3.5).
- **The spectral core noise is a Sketching-layer statement** (A11), in projector form for every
  fixed basis $\mathbf{X}$ and every rank with $\operatorname{rank}\mathbf{X} + 2 \le p$; the
  brief's $p \ge 4\ell$ enters only in the assembly. Its subject is the sketch-and-solve excess,
  so by CONTRIBUTING §8 item 5 it sits with sketch-and-solve, not with truncated GN.
- **The early-truncated GN statement is a composition taking the early-truncated RSVD expectation on
  its right side** (ET3), with the conditional-on-$\mathbf{\Omega}$ identity beside it (ET1) and
  the maintainer's $(1+\varepsilon)$ form taking the early-truncated RSVD bound as a hypothesis
  (ET6). The $\varepsilon^{-2}$ lives in that hypothesis: early-truncated RSVD in expectation is
  deferred (brief §8, D15), as S2b §8 item 3(iii) says. Q4.
- **Unbiasedness of Gaussian sketch-and-solve at $\operatorname{rank}\mathbf{A} + 1 \le p$**, one
  less than EW's $r + 2 \le \ell$ (Q9).
- **A Frobenius-noise baseline for truncated GN** (TG7), the $k/\varepsilon^3$ bound the brief names
  only as a docstring comparison point, is stated as the rule-4 neighbour of TG5: at practical sizes
  ($\ell \lesssim 10^3 k$) its constants are far better (Q5).

**Literature checks** (PDFs: `/tmp/claude-1000/p0/papers/` for EW arXiv:2605.19096 v2 and TYUC
SIMAX arXiv:1609.00048; `~/Documents/prove2me/books/` for TW arXiv:2306.12418 v3 and CEMT; page
numbers are PDF pages, CEMT printed = PDF − 2):
- EW Theorem 2.1 (p. 3): $\mathbf{\Omega} \in \mathbb{K}^{n \times \ell}$ Gaussian or random
  orthonormal, $r = \operatorname{rank}\mathbf{A} < \ell - \alpha_{\mathbb{K}}$;
  $\mathbb{E}\hat{\mathbf{X}} = \mathbf{A}^{+}\mathbf{B}$ (either law);
  $\mathbb{E}\|\mathbf{B}-\mathbf{A}\hat{\mathbf{X}}\|_{\mathsf{F}}^2 = (1+\frac{r}{\ell-r-\alpha})
  \min$ (Gaussian), $(1+\frac{n-\ell}{n-r}\frac{r}{\ell-r-\alpha})\min$ (random orthonormal). An
  "embedding" is tall, $n \ge \ell$ (§1.1, p. 2): the Haar formula is false for $\ell > n$ (§3.0).
  Real Gaussian case credited to Bartan and Pilanci 2020, Lemma 2.1 (not in hand, not in
  `references.bib`).
- EW Lemma 5.1 (p. 11): the error decomposition under $\operatorname{rank}\mathbf{A} =
  \operatorname{rank}(\mathbf{\Omega}^{*}\mathbf{A})$, (5.1) and (5.2); in the library as S0's
  `sketchAndSolve_eq_pinv_mul_add` and `frobNorm_one_sub_obliqueProjector_mul_sq`.
- EW Proposition 5.4 (p. 13): $\mathbb{E}\|(\mathbf{\Omega}_1^{*})^{+}\mathbf{\Omega}_2^{*}
  \mathbf{B}\|_{\mathsf{F}}^2 = \frac{r}{\ell-r-\alpha}\|\mathbf{B}\|_{\mathsf{F}}^2$; registered as
  R4's `integral_frobNorm_pinv_mul_mul_sq_of_hasLaw_gaussianMatrix`.
- EW Proposition 5.6 (p. 13), the inverse Beta mean; Proposition 5.7 (p. 14), the random orthonormal
  sketching identity, equality at $\mathbf{R} = \mathbf{I}$, proved from $\mathbb{E}\mathbf{X} =
  [\mathbb{E}\operatorname{tr}\mathbf{X}/(n-r)]\mathbf{I}$ (the coupled conjugation average) and
  $\mathbf{\Omega}_1^{*}\mathbf{\Omega}_1 + \mathbf{\Omega}_2^{*}\mathbf{\Omega}_2 = \mathbf{I}$.
  The proof of Theorem 2.1 is §5.4 (p. 16).
- EW Definition 4.1 and Theorem 4.2(a) (p. 9): $\mathbf{\Psi} \in \mathbb{K}^{d \times k}$,
  $\ell + \alpha < k$, $\mathbf{\Omega}$ rotation-invariant, $\mathbf{\Psi}$ independent and
  Gaussian or random orthonormal, $r = \operatorname{rank}\mathbf{A} \ge k$:
  $\mathbb{E}\|\mathbf{A}-\mathbf{A}\langle\mathbf{\Omega},\mathbf{\Psi}\rangle\|_{\mathsf{F}}^2 \le
  (1+\gamma\frac{\ell}{k-\ell-\alpha})\min_{q<\ell-\alpha}\frac{r-\ell}{r-q}(1+\frac{q}{\ell-q-\alpha})
  \|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_q\|_{\mathsf{F}}^2$, $\gamma \in \{1,
  \frac{d-k}{d-\ell}\}$; its proof's first line is the identity $\mathbb{E}\|\cdot\|^2 =
  (1+\gamma\frac{\ell}{k-\ell-\alpha})\mathbb{E}\|\mathbf{A}-\mathbf{P}_{\mathbf{A}\mathbf{\Omega}}
  \mathbf{A}\|_{\mathsf{F}}^2$. In this note's letters EW's $(d, k)$ are $(m, p)$. The hypothesis
  $r \ge k$ is stronger than the proof needs ($r \ge \ell$, for the minimum of Theorem 3.2).
- TYUC SIMAX Theorem 4.3 (p. 10): sizes $k$ (range) and $\ell > k + \alpha$ (co-range), Gaussian,
  independent: $\mathbb{E}\|\mathbf{A}-\hat{\mathbf{A}}\|_{\mathsf{F}}^2 \le (1+f(k,\ell))\min_{\varrho
  <k-\alpha}(1+f(\varrho,k))\tau_{\varrho+1}^2$, $f(s,t) = s/(t-s-\alpha)$. Lemma A.3 (p. 29) is the
  split, Lemma A.5 (p. 29) the completion for fixed $\mathbf{Q}$ together with
  $\mathbb{E}_{\mathbf{\Psi}}[\mathbf{X}-\mathbf{Q}^{*}\mathbf{A}] = \mathbf{0}$ (the core is
  unbiased). Proposition 6.1 (p. 16), the constant-2 triangle lemma (S2a's
  `IsBestRankApprox.matrixNorm_sub_le_add_two_mul`), and Corollary 6.4 (p. 18), the fixed-rank
  first-moment bound $\mathbb{E}\|\mathbf{A}-\llbracket\hat{\mathbf{A}}\rrbracket_r\|_{\mathsf{F}}
  \le \tau_{r+1} + 2\sqrt{(1+f(k,\ell))\min_\varrho(1+f(\varrho,k))}\,\tau_{\varrho+1}$, the only
  published expectation bound on late-truncated GN. §7.3.1, (7.3) (p. 21): the early-truncated
  algorithm, no theorem (S2b §8 item 3).
- CEMT Corollary 2.8 (PDF p. 22, printed 20): GN with an $(r,\alpha)$-OSI $\mathbf{\Omega}$ and a
  $(k,\alpha)$-OSI $\mathbf{\Psi}$, $(C/\alpha)^2$ with probability $4/5$: S7's (Gaussian and Haar
  are OSIs there). Remark 2.9 (PDF p. 23): its "truncated generalized Nyström approximation
  [123, Thm. 4.3]" is Woodruff's core-truncated estimator ($[123]$ = Woodruff 2014), not
  $\llbracket\mathsf{gn}\rrbracket_k$; no theorem is stated, and CEMT "cannot endorse this algorithm".
  It is a comparison point in TG5's docstring only, with that reading (Q12).
- TW Lemma B.1 (p. 47): $\mathbb{E}\|\mathbf{S}\mathbf{G}\mathbf{T}\|_{\mathsf{F}}^2$ exact,
  $(\mathbb{E}\|\mathbf{S}\mathbf{G}\mathbf{T}\|^2)^{1/2} \le \|\mathbf{S}\|\|\mathbf{T}\|_{\mathsf{F}}
  + \|\mathbf{T}\|\|\mathbf{S}\|_{\mathsf{F}}$, by Slepian's lemma for $\mathbb{E}|\max|^p$. Lemma
  B.3 (p. 52), $\mathbb{E}\|(\mathbf{G}\mathbf{G}^{*})^{-1}\|^p$, is R4's spectral moment with a
  better constant (`gaussianPinvSpecNormBound`). **TW has no Theorem 5.1 and no generalized
  Nyström** (its Lemma 5.1 is "bigger projection, smaller error"): the brief's §9.3 citation "TW
  2023, proof of Theorem 5.1" for the completion identity, the assessment's and the prototype's,
  are wrong (Q12).
- HMT Propositions 10.1, 10.2 (the Gaussian moments behind R4), Theorem 10.6 (the first spectral
  moment whose second-moment form D1 is).

**Missing infrastructure, per result** (each a statement of this note):
- Gaussian completion, EW Theorem 2.1 (Gaussian), GN with Gaussian $\mathbf{\Psi}$, early-truncated
  GN (Gaussian): a Tonelli step for independent pairs (L1; the library repeats
  `indepFun_iff_map_prod_eq_prod_map_map` with `lintegral_prod` fourteen times) and the measurability
  of the early-truncated outputs in the test matrices (L2, L3). Everything else exists (S0's split,
  R4's block moment, R1's a.s. rank, S2c's `measurable_generalizedNystrom`).
- Unbiasedness (Gaussian): nothing beyond the sign-flip invariance
  (`hasLaw_mul_const_of_hasLaw_gaussianMatrix`) and R4's first spectral moment.
- Truncated GN: the spectral second moment of a Gaussian product (L5 to L7), the second spectral
  block moments (L8 to L11), the spectral core noise (A11), and the spectral second moment of the
  range finder at a split (D1). S2a's T11, S1's structural bound, S3's U1 and G2 and the tail
  flattening `natCast_mul_singularValues_add_sq_le_frobNorm_sub_truncatedSVD_sq` exist.
- Every Haar statement (A13 to A17, GH1 to GH5, ET2, ET5): EW Proposition 5.7 at $\mathbf{R} =
  \mathbf{I}$ (L12, L13), which needs two S4 results not yet in the library: the trace of the
  inverse Gram matrix of a Haar row block, $\mathbb{E}\operatorname{tr}((\mathbf{V}_1^{\mathsf{H}}
  \mathbf{Q}\mathbf{Q}^{\mathsf{H}}\mathbf{V}_1)^{-1}) = r(1+\frac{m-p}{p-r-1})$ (brief §4.3 (iii)),
  and the coupled conjugation average (§4.3 (iv)). §0.2.
- EW Theorem 4.2(a) (GN7, GH5): S4's EW Theorem 3.2.
- Not reached: TW Lemma B.1's second moment without the term $\|\mathbf{S}\|_2^2\|\mathbf{T}\|_2^2$
  (Q3); complex laws ($\alpha_{\mathbb{C}} = 0$, D3); truncated GN with Haar $\mathbf{\Psi}$ (no Haar
  spectral core noise; §6); early-truncated RSVD in expectation (brief §8).

## 0. Scope and consumers

### 0.1 Notation

$\mathbf{A}$ : `Matrix m n ℝ`; the range test matrix is `X : Ω → Matrix n l ℝ` on a sample space
`Ω` (S3 Q8), written $\mathbf{\Omega}$ in docstrings as the sources and the maintainer's notation
rule do, $\ell = \lvert l \rvert$; a fixed range test matrix is `X₀ : Matrix n l ℝ`; the co-range
test matrix is `Ψ : Ω → Matrix m p ℝ`, applied as $\mathbf{\Psi}^{\mathsf{H}}$ (D2), $p = \lvert p
\rvert$; the target rank is `k : ℕ`, a comparison rank `q : ℕ`. In the Sketching file the sketch is
`S : Ω → Matrix p m ℝ` (Gaussian, the Sketching round's orientation) or $\mathbf{Q}^{\mathsf{H}}$
for a Haar frame `Q : Ω → Matrix m p ℝ` (as `Sketching/Gaussian/Haar.lean`), the system is
`A : Matrix m n ℝ`, the right-hand side `B : Matrix m r ℝ`, and a fixed basis is
`X : Matrix m s ℝ` (no random `X` there). $\mathrm{OPT}_k = \|\mathbf{A}-\llbracket\mathbf{A}
\rrbracket_k\|_{\mathsf{F}}$ = `frobNorm (A - truncatedSVD A k)`. Singular values from $0$, as the
library ($\sigma_k$ = `singularValues A k` is the error of the best rank-$k$ approximation). The
named factors:
$$g_k(\ell) = \texttt{gaussianProjectionFactor}\ k\ \ell = 1 + \frac{k}{\ell-k-1},\qquad
h_d(p, q) = \texttt{haarProjectionFactor}\ d\ p\ q = 1 + \frac{d-p}{d-q}\cdot\frac{q}{p-q-1}.$$

### 0.2 Division of Epperly and Webber's results with S4

Brief §6 and the S6 and S4 entries of §7 assign them; this note confirms the assignment and takes:
- **S6 takes:** Theorem 2.1, both laws, residual and unbiasedness (A8, A9, A15, A16); Proposition
  5.4 as restated through R4 (inside A6); Proposition 5.7 at $\mathbf{R} = \mathbf{I}$ (L12, an
  equality); Theorem 4.2(a), both values of $\gamma$, in identity form (GN5, GH4) and in EW's bound
  form through S4's Theorem 3.2 (GN7, GH5); Lemma 5.1 is S0's, used.
- **S4 takes:** Proposition 5.6 in trace form, Lemma 6.2's pointwise inequality, Theorems 3.2 and
  3.6(a), the Haar block laws, the polar factor of a wide matrix, the signed-permutation average
  and the coupled law invariance (brief §4.3 (i) to (v)); Fact 6.1 is S0's.
- **S10 (or a later round, D6):** Theorems 2.2, 3.3, 3.6(b), 4.2(b), Lemma 5.8, Proposition 5.7 for
  general $\mathbf{R}$.
- **What S6 consumes from S4**, by content (names are S4's; the provisional spellings below are
  this note's and are replaced by S4's when its note is written, a mechanical change):
  1. *(S4-i)* For `Q` with `HasLaw Q (haarFrame m p) μ`, $p \le m$, and `V₁ : Matrix m r ℝ` with
     orthonormal columns, $r + 2 \le p$: `∫ ω, ((V₁ᴴ * Q ω * (Q ω)ᴴ * V₁)⁻¹).trace ∂μ =
     card r * (1 + (card m - card p) / (card p - card r - 1))`, with its integrability. This is
     brief §4.3 (iii) in the orientation of a Haar frame (EW's $\mathbf{\Omega}_1 =
     \mathbf{V}_1^{\mathsf{H}}\mathbf{Q}$).
  2. *(S4-ii)* The coupled conjugation average for a Haar frame: for `V₁`, `V₂` complementary frames
     ($\mathbf{V}_1\mathbf{V}_1^{\mathsf{H}} + \mathbf{V}_2\mathbf{V}_2^{\mathsf{H}} = \mathbf{I}$)
     and `F` measurable with $\mathbf{V}_2^{\mathsf{H}}\mathbf{Q}\,F(\mathbf{V}_1^{\mathsf{H}}
     \mathbf{Q})\,\mathbf{Q}^{\mathsf{H}}\mathbf{V}_2$ integrable,
     $\mathbb{E}[\mathbf{V}_2^{\mathsf{H}}\mathbf{Q}F(\mathbf{V}_1^{\mathsf{H}}\mathbf{Q})
     \mathbf{Q}^{\mathsf{H}}\mathbf{V}_2] = \frac{\mathbb{E}\operatorname{tr}(\cdot)}{\lvert s\rvert}
     \mathbf{I}$ (brief §4.3 (iv), EW's step $\mathbb{E}\mathbf{X} = [\mathbb{E}\operatorname{tr}
     \mathbf{X}/(n-r)]\mathbf{I}$).
  3. *(S4-iii)* EW Theorem 3.2 for a left-invariant law of full column rank, in the shape
     `∫ ω, frobNorm (A - rsvd A (X ω)) ^ 2 ∂μ ≤ rotationInvariantFactor A.rank (card l) q *
     frobNorm (A - truncatedSVD A q) ^ 2` under `card l ≤ A.rank` and `q + 2 ≤ card l`, with
     `rotationInvariantFactor r l q := (r - l) / (r - q) * gaussianProjectionFactor q l` (S3 §1).
     GN7 and GH5 take S4's hypotheses verbatim whatever they are.

  If S4 states (S4-i) as $\mathbb{E}\|(\mathbf{Q}^{\mathsf{H}}\mathbf{V}_1)^{+}\|_{\mathsf{F}}^2$
  instead of a trace, L12's proof takes one rewrite more (the squared Frobenius norm of the
  pseudoinverse of a full-column-rank matrix is the trace of its inverse Gram matrix); nothing in S6's statements changes.

### 0.3 Consumers

| Item | Consumers |
|---|---|
| Gaussian and Haar completion (A6, A13) and EW Theorem 2.1 (A8, A15) | GN (GN1 to GN5, GH1 to GH4), early-truncated GN (ET1 to ET5); Solvers (sketch-and-solve's exact MSE, the comparison point for sketch-and-precondition; EW's "orthogonality helps, but only a bit", A5); S10 (the matching lower bounds) |
| unbiasedness (A9, A16) | Solvers (iterative refinement and averaging estimators; EW §2.2); users |
| spectral core noise (A11) | truncated GN (TG5); S7 (an OSI analogue for truncated GN with structured $\mathbf{\Psi}$) |
| the second spectral moments (L5 to L11), D1 | TG5; Estimation; users (the second-moment form of HMT 10.6, missing in the library) |
| L1 (Tonelli for independent pairs) | every two-sketch expectation here; S7, S9 |
| L2, L3 (measurability of early-truncated outputs) | ET3, ET4; S7's and S9's early-truncation tails |
| law-free-in-$\mathbf{X}$ GN and early-truncated GN forms (GN2 to GN4, GH2, GH3, TG4, ET3 to ET5) | S7 (OSI and OSE-plus-AMM bounds on the RSVD and early-truncated RSVD compose with these to give GN and early-truncated GN with a structured $\mathbf{\Omega}$ and a Gaussian or Haar $\mathbf{\Psi}$); S9 (the uniform-PCP route); the deferred early-truncated RSVD expectation (brief §8) |
| GN headline bounds (GN6, GN7, GH5), exact recovery (GN8) | users of single-pass methods (TYUC's algorithm, MT §15); S7 (comparison with CEMT Corollary 2.8) |
| truncated GN (TG1 to TG7) | users of fixed-rank single-pass approximation; the atlas candidate `tgn-expected-error` |
| early-truncated GN (ET1 to ET6) | users; the atlas candidate `etgn`; brief §8's early-truncated RSVD expectation (ET6 becomes unconditional) |

Not in S6: the OSI and OSE routes (S7, CEMT Corollary 2.8 among them), PCP forms (S9), lower bounds
(S10), complex laws (D3), truncated GN with Haar $\mathbf{\Psi}$ (§6), tails of GN with Gaussian
sketches (S7's Gaussian-OSI corollary gives them), sample-size forms beyond TG6 and ET6.

## 1. Objects

Two named real quantities, no matrix definition, no new interface, no §5.3 row, no deviation from
Mathlib (named constants are of a kind Mathlib does not have; no entry in `Mathlib-deviations.md`,
as for S3's).

- **`haarProjectionFactor (d p q : ℕ) : ℝ := 1 + (d - p) / (d - q) * (q / (p - q - 1))`** (casts to
  ℝ), name and argument order fixed by S3 §1 and §8 item 12: a plain `def` with a `_def` simp
  lemma, because its body is EW's formula (D9, as `gaussianProjectionFactor`), and therefore not
  in the registry (`gaussianProjectionFactor` is not either). Docstring roles: the completion factor
  of a Haar sketch of size $p$ in ambient dimension $d$ for a basis of rank $q$ (A13), EW Theorem
  2.1's random orthonormal constant (A15), and EW Theorem 4.2(a)'s $1 + \gamma\frac{\ell}{p-\ell-1}$
  with $\gamma = \frac{d-p}{d-\ell}$ (GH4, GH5). Junk: for $p \le q + 1$ or $d \le q$ (Lean's
  $x/0 = 0$, signs); theorems carry `q + 2 ≤ p` and `p ≤ d`. API: `one_le_haarProjectionFactor`,
  monotonicity in `q` (ET5 at the actual rank, GH2 at $\operatorname{rank}(\mathbf{A}\mathbf{X})
  \le \ell$), and `haarProjectionFactor_le_gaussianProjectionFactor` (EW's "orthogonality helps").
  Home: the new `Sketching/Gaussian/LeastSquares.lean` (Q8): its first use, and the file a user with
  a Haar sketch looks in; `RandomMatrix/Haar/` would also do, since Sketching imports it.
- **`truncatedGNFactor (k l p : ℕ) : ℝ`**, an `irreducible_def` (rule 2: the constants are the
  proof's; no literature source has the statement) with body, writing $g = g_k(\ell)$ and
  $c = (25g + 484)/p$,
  $$\texttt{truncatedGNFactor}\ k\ \ell\ p := g + 4\sqrt{2kc} + 8kc.$$
  It is TG5's multiplier of $\mathrm{OPT}_k^2$. Registry entry (`docs/constants.toml`):
  `name = "NLAlib.truncatedGNFactor"`, `kind = "constant factor"`, `file =
  "NLAlib/LowRank/Gaussian/TruncatedGeneralizedNystrom.lean"`, `args = ["k", "l", "p"]`,
  `latex = 'g + 4\sqrt{2#1 c} + 8#1 c,\ g = 1 + #1/(#2 - #1 - 1),\ c = (25g + 484)/#3'`, `lean_body`
  and `body_hash` from `--update`. Every docstring that uses it writes its formula inline in the
  equation, with the marker `<!-- value truncatedGNFactor k \ell p -->` just before that math span
  (maintainer's docstring rule, 2026-10-15; §2). API, per rule 2: TG2
  (`one_le_truncatedGNFactor`) and TG3 (`truncatedGNFactor_le_one_add`, the explicit comparison
  $\le 1 + \varepsilon$ at $\ell \ge 6k/\varepsilon$, $p \ge 8000\ell/\varepsilon$). Its docstring
  gives: source value none (the maintainer's notes are not citable; their constants are $18$ and
  $408$ in place of $25$ and $484$, and $12500$ in place of $8000$, all unoptimized); value proved
  as above; the gap to TW Lemma B.1's sharp second moment (Q3). An improvement of the same shape
  changes the body, the registry and TG3's numbers, no statement and no name. Home: the new
  `LowRank/Gaussian/TruncatedGeneralizedNystrom.lean`.

**Used directly.** S0: `obliqueProjector`, `one_sub_obliqueProjector_mul`,
`frobNorm_one_sub_obliqueProjector_mul_sq`, `obliqueProjector_eq_of_range_eq`,
`obliqueProjector_smul_right`, `HasOrthonormalCols.obliqueProjector_mul_left`, `sketchAndSolve`,
`mul_sketchAndSolve`, `sketchAndSolve_eq_pinv_mul_add`, `HasOrthonormalCols.sketchAndSolve_eq_add`,
`rsvd`, `sub_rsvd`, `generalizedNystrom`, `sub_generalizedNystrom`,
`frobNorm_sub_generalizedNystrom_sq`, `generalizedNystrom_eq_self_of_rank_eq`,
`generalizedNystrom_eq_mul_sketchAndSolve`, `earlyTruncatedRSVD`, `earlyTruncatedGeneralizedNystrom`,
`sub_earlyTruncatedRSVD`, `sub_earlyTruncatedGeneralizedNystrom`,
`frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq` (S2b's E8). S1:
`HasOrthonormalCols.specNorm_sub_rsvd_sq_le`. S2a: `frobNorm_rsvd_sub_truncatedSVD_le`,
`frobNorm_sub_truncatedSVD_rsvd_sq` (T3), `frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_specNorm`
(T11), `frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_frobNorm_truncatedSVD` (T10),
`IsBestRankApprox.matrixNorm_sub_le_add_two_mul`, `isBestRankApprox_truncatedSVD`,
`frobNorm_truncatedSVD_sq`. S2c: `measurable_truncatedSVD`, `measurable_rsvd`,
`measurable_generalizedNystrom`, `measurable_pinv`, `measurable_rangeProjector`, `measurable_rank`.
S3: `integral_frobNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix` (G2),
`integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_hasLaw_gaussianMatrix` (U1),
`integrable_frobNorm_sub_rsvd_sq`, `integrable_specNorm_sub_rsvd_sq`,
`ae_rsvd_eq_self_of_hasLaw_gaussianMatrix`, `gaussianProjectionFactor` and its API,
`gaussianPinvSpecNormBound` and its API. Matrix layer:
`natCast_mul_singularValues_add_sq_le_frobNorm_sub_truncatedSVD_sq`, `rank_truncatedSVD_le`,
`truncatedSVD_of_rank_le`, `specNorm_conjTranspose`, `HasOrthonormalCols.singularValues_mul_left`,
`frobNorm_mul_le_specNorm_mul_frobNorm`, `specNorm_le_frobNorm`, `specNorm_le_one`,
`exists_hasOrthonormalCols_range_eq`. RandomMatrix: `ae_rank_mul_eq_min_of_hasLaw_gaussianMatrix`,
`ae_rank_conjTranspose_mul_eq_of_hasLaw_gaussianMatrix`, `hasLaw_conjTranspose_of_hasLaw_gaussianMatrix`,
`hasLaw_mul_const_of_hasLaw_gaussianMatrix`, `indepFun_conjTranspose_mul_of_hasLaw_gaussianMatrix`,
`integral_frobNorm_pinv_mul_mul_sq_of_hasLaw_gaussianMatrix` (and its integrable twin),
`integral_frobNorm_pinv_sq_of_hasLaw_gaussianMatrix`, `integral_specNorm_pinv_rpow_le_of_hasLaw_gaussianMatrix`,
`integrable_specNorm_pinv_rpow_of_hasLaw_gaussianMatrix`, `integral_specNorm_mul_mul_le_of_hasLaw_gaussianMatrix`,
`hasSubgaussianMGF_sub_integral_of_hasLaw_gaussianMatrix`, `ae_rank_mul_eq_min_of_hasLaw_haarFrame`,
`ae_hasOrthonormalCols_of_hasLaw_haarFrame`, `ae_specNorm_le_one_of_hasLaw_haarFrame`,
`hasLaw_const_mul_of_isLeftUnitarilyInvariant`, `isLeftUnitarilyInvariant_haarFrame` (an instance, `RandomMatrix/Haar/Basic.lean`). Probability:
`HasSubgaussianMGF.integral_sq_le` (`Probability/SubGaussian/Basic.lean`). Mathlib:
`indepFun_iff_map_prod_eq_prod_map_map`, `lintegral_prod`, `integral_mul_le_Lp_mul_Lq_of_nonneg`,
`IndepFun.integral_mul_eq_mul_integral`, `HasLaw.isProbabilityMeasure`, `integral_congr_ae`.

**Mathlib search** ("searched, none" unless named): sketch-and-solve, least-squares sketching,
Wishart and inverse-Wishart moments (Mathlib has none; R4 is the library's), Haar measure on Stiefel
manifolds (Mathlib has `Measure.haarMeasure` on compact groups, which R5 bridges), Tonelli for
independent pairs (Mathlib has `IndepFun.integral_mul_eq_mul_integral` and the bilinear forms, no
general $\int f(U, W)$; L1), second moments of Lipschitz functions of Gaussians (Mathlib has none;
the library's `HasSubgaussianMGF.integral_sq_le` with Gaussian concentration gives it).

## 2. Interfaces

No new predicate. Hypotheses, each an existing spelling:
- Laws: `HasLaw X (gaussianMatrix n l) μ` (D2); `HasLaw Ψ (gaussianMatrix m p) μ` or
  `HasLaw Ψ (haarFrame m p) μ` with `[DecidableEq p]` and `hpm : Fintype.card p ≤ Fintype.card m`;
  in the Sketching file `HasLaw S (gaussianMatrix p m) μ` and `HasLaw Q (haarFrame m p) μ`.
  Rotation-invariant range test matrices: S3's row, `HasLaw X ν μ` with `[IsProbabilityMeasure ν]
  [IsLeftUnitarilyInvariant ν]` and `hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec` (GN7, GH5).
- Two sketches: `hXΨ : IndepFun X Ψ μ` (D2). Where the range test matrix may have any law, it is
  `hX : AEMeasurable X μ` (S3 Q9's law-free style), and `[IsProbabilityMeasure μ]` comes from `hΨ`.
- Sizes: `k q : ℕ` with `k + 2 ≤ Fintype.card l` and `Fintype.card l + 2 ≤ Fintype.card p` (GN),
  `X.rank + 2 ≤ Fintype.card p` for a fixed basis, `4 * k ≤ Fintype.card l` and
  `4 * Fintype.card l ≤ Fintype.card p` (truncated GN), `k + 2 ≤ Fintype.card p` (early-truncated GN).
  No oversampling variable (D9).
- The rank hypothesis of the exact split, `(Ψᴴ * X).rank = X.rank`, never appears in an S6
  statement: it holds almost surely under every law here once $\operatorname{rank}\mathbf{X} \le p$,
  and the proofs derive it.

**Docstrings.** Outputs are $\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})$,
$\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})$, $\mathsf{earlyTruncatedGN}(\mathbf{A}, \mathbf{\Omega},
\mathbf{\Psi}, k)$, $\mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)$,
$\mathsf{sketchAndSolve}(\mathbf{A}, \mathbf{S}, \mathbf{B})$, $\llbracket\cdot\rrbracket_k$; never the
formula they unfold to. The module docstrings say that $\mathbf{\Omega}$ is the Lean `X` (and `X₀`
when fixed). **Named constants in docstrings** (maintainer's rule, 2026-10-15): the equation shows
the constant's current formula in place of the constant, and a marker
`<!-- value NAME ARGS -->` sits just before the math span that contains it; never a symbol $C$ or
$\beta$ followed by "with $C$ = `name`, that is …". The Lean statements keep the name. This applies
to `gaussianPinvSpecNormBound` (L9, L11, A11, D1) and `truncatedGNFactor` (TG1 to TG3, TG5, TG6),
whose formulas `scripts/check_constants.py` checks against the registry templates;
`gaussianProjectionFactor` and `haarProjectionFactor` are unregistered source formulas, written out
inline in the equations as well, without markers. The docstrings of §3 follow this rule.

## 3. Statement shapes

`namespace NLAlib`, `open MeasureTheory ProbabilityTheory`, `open scoped Matrix ENNReal`; the
unbiasedness statements (A9, A10, A16, A17) are matrix-valued Bochner integrals and sit under
`open scoped Matrix.Norms.L2Operator in` (CONTRIBUTING §5.1, as R4's
`integral_mul_conjTranspose_inv_of_hasLaw_gaussianMatrix`). Variables `{Ω : Type*}
{mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n l p r s : Type*}` with `[Fintype _]` and
`[DecidableEq m]` (for `1 - rangeProjector _`). Docstrings are shortened; the full ones carry §5's
citations, LaTeX throughout, Lean names in backticks, and the value markers of §2.

### 3.0 Degenerate cases, measurability, and the common steps

**Common steps** (every expectation of §3.2 to §3.6).
1. *The basis step* (brief §4.1 item 1, §4.3 (a)). For a fixed $\mathbf{X}$ of rank $q$, take
   $\mathbf{Q}_1$ : `Matrix m (Fin q) ℝ` with orthonormal columns and range $\operatorname{range}
   \mathbf{X}$ (`exists_hasOrthonormalCols_range_eq`) and $\mathbf{Q}_2$ completing it,
   $\mathbf{Q}_2\mathbf{Q}_2^{\mathsf{H}} = \mathbf{I} - \mathbf{P}_{\mathbf{X}}$. On the event
   $\operatorname{rank}(\mathbf{S}\mathbf{X}) = q$, `obliqueProjector_eq_of_range_eq` replaces
   $\mathbf{\Pi}_{\mathbf{X},\mathbf{S}}$ by $\mathbf{\Pi}_{\mathbf{Q}_1,\mathbf{S}}$, and
   $\mathbf{\Pi}_{\mathbf{Q}_1,\mathbf{S}}(\mathbf{I}-\mathbf{P}_{\mathbf{X}})\mathbf{B} =
   \mathbf{Q}_1\,(\mathbf{S}\mathbf{Q}_1)^{+}(\mathbf{S}\mathbf{Q}_2)\,\mathbf{Q}_2^{\mathsf{H}}
   \mathbf{B}$, whose Frobenius and spectral norms are those of the middle factor times
   $\mathbf{Q}_2^{\mathsf{H}}\mathbf{B}$ (`HasOrthonormalCols.singularValues_mul_left`), with
   $\|\mathbf{Q}_2^{\mathsf{H}}\mathbf{B}\| = \|(\mathbf{I}-\mathbf{P}_{\mathbf{X}})\mathbf{B}\|$ in
   both norms. With $\mathbf{S} = \mathbf{G}^{\mathsf{H}}$ the middle factor is R4's
   `pinv (Gᴴ * V₁) * (Gᴴ * V₂)`. The `Fin q` index is proof-internal (§5.1 permits it where the
   index carries content); no statement shows a basis.
2. *Conditioning* (brief §4.3 (a), "integrated over $\mathbf{\Omega}$, the rank stays inside the
   expectation"). For `IndepFun X Ψ μ` and a measurable $f \ge 0$ of the pair, L1 writes
   $\mathbb{E}f(\mathbf{X}, \mathbf{\Psi})$ as the $\mathbf{X}$-integral of the fixed-$\mathbf{X}_0$
   expectation, which is a statement of this note (A6, A11, A13, GN1, GH1, ET1, ET2); then
   `integral_eq_lintegral_of_nonneg_ae` returns to Bochner integrals. Measurability of every
   integrand in the pair: S2c's `measurable_generalizedNystrom`, `measurable_rsvd`,
   `measurable_truncatedSVD`, and L2, L3.
3. *Rank events.* `ae_rank_conjTranspose_mul_eq_of_hasLaw_gaussianMatrix` (Gaussian) and
   `ae_rank_mul_eq_min_of_hasLaw_haarFrame` with `Matrix.rank_conjTranspose` (Haar) give
   $\operatorname{rank}(\mathbf{\Psi}^{\mathsf{H}}\mathbf{X}_0) = \operatorname{rank}\mathbf{X}_0$
   almost surely whenever $\operatorname{rank}\mathbf{X}_0 \le p$ (and $p \le m$ for Haar), which
   is the rank hypothesis of every S0 identity used.

**Degenerate cases** (checked for every statement; the routes say where a case bites).
- *Sketch size at or below the rank plus one.* The Gaussian identities need
  $\operatorname{rank}\mathbf{X} + 2 \le p$: at $p = q + 1$ the integrand is not integrable
  ($\mathbb{E}\|\mathbf{G}^{+}\|_{\mathsf{F}}^2 = \infty$), Lean's integral is $0$, and A6 would claim
  $0 = (1 + q/0)\|(\mathbf{I}-\mathbf{P}_{\mathbf{X}})\mathbf{B}\|_{\mathsf{F}}^2$, false whenever the
  residual is nonzero; at $p \le q$ the rank hypothesis of the split fails surely. Rank $0$ needs
  nothing ($g_0 = 1$, both sides $\|\mathbf{B}\|_{\mathsf{F}}^2$), but the hypothesis is kept
  uniform. Unbiasedness needs only $\operatorname{rank}\mathbf{A} + 1 \le p$ (Gaussian): at $p = r$
  the solution is not integrable ($\mathbb{E}\|\mathbf{G}^{-1}\|_2 = \infty$ for square
  $\mathbf{G}$), and Lean's $0$ would contradict $\mathbf{A}^{+}\mathbf{B} \ne \mathbf{0}$.
- *Haar sketches wider than the dimension, $p > m$.* `haarFrame m p` is then the polar factor of a
  wide matrix: orthonormal rows, so $\mathbf{Q}^{\mathsf{H}}$ is an isometry, sketch-and-solve is exact
  (`HasOrthonormalCols.obliqueProjector_mul_left`, `obliqueProjector_one`) and the factor is $1$,
  while $h_m(p, q) < 1$ for $q \ge 1$. Example: $m = 2$, $p = 3$, $q = 1$ gives $h = 0$ and A13 would
  claim the error is $0$. Every Haar statement carries `hpm : Fintype.card p ≤ Fintype.card m` (EW's
  "an embedding is tall"). At $p = m$ the Haar sketch is orthogonal: $h_m(m, q) = 1$, exact, right.
  Gaussian statements need no such hypothesis ($p > m$ is a weighted least-squares problem, and the
  identities hold).
- *$k = 0$.* $\llbracket\cdot\rrbracket_0 = \mathbf{0}$, $\mathrm{OPT}_0 = \|\mathbf{A}\|_{\mathsf{F}}$,
  both early-truncated outputs are $\mathbf{0}$, $g_0 = h_d(p, 0) = 1$ and
  `truncatedGNFactor 0 l p = 1`. TG5 is $\|\mathbf{A}\|_{\mathsf{F}}^2 \le \|\mathbf{A}\|_{\mathsf{F}}^2$,
  ET1 and ET3 are equalities $\|\mathbf{A}\|_{\mathsf{F}}^2 = \|\mathbf{A}\|_{\mathsf{F}}^2$; TG5's
  `4 * k ≤ card l` puts no condition on $\ell$ there, and ET6's size hypothesis allows $p = 1$ at
  $k = 0$ (its proof branches on $k = 0$ before using ET3).
- *Low rank.* $\operatorname{rank}\mathbf{A} \le \min(\ell, p)$: GN is exact almost surely (GN8),
  and every GN identity has both sides equal to $0$. Truncated GN with $\operatorname{rank}
  \mathbf{A} \le \ell$ is TG5's exact branch: $\llbracket\mathsf{gn}\rrbracket_k =
  \llbracket\mathbf{A}\rrbracket_k$ almost surely and the error is $\mathrm{OPT}_k^2 \le$ the factor
  times it (TG2). The range finder's exactness at $\operatorname{rank}\mathbf{A} \le \ell$ is S3's
  `ae_rsvd_eq_self_of_hasLaw_gaussianMatrix`.
- *Rank of the truncated sketch below $k$.* $q = \operatorname{rank}\llbracket\mathbf{A}\mathbf{\Omega}
  \rrbracket_k < k$ (assessment A10): ET1, ET2 carry the factor at the actual $q$; ET3, ET5 bound it
  by the factor at $k$ (monotone, `gaussianProjectionFactor_le_gaussianProjectionFactor`, A4). The
  split's rank hypothesis at $q \le k \le p$ holds almost surely (common step 3).
- *More samples than the dimension, $\ell > n$.* Gaussian range test matrices: $\operatorname{rank}
  (\mathbf{A}\mathbf{X}) = \operatorname{rank}\mathbf{A}$ almost surely, the low-rank case. The
  rotation-invariant hypothesis `hXr` is unsatisfiable there (GN7, GH5 vacuous, as S3's).
- *Empty index types.* $l$ empty: $\mathbf{A}\mathbf{X}$ has no columns, rank $0$, all outputs
  $\mathbf{0}$, every identity is $\|\mathbf{A}\|_{\mathsf{F}}^2 = \|\mathbf{A}\|_{\mathsf{F}}^2$; GN6
  and TG5 are then excluded or trivial by their size hypotheses ($k + 2 \le 0$ is false; $4k \le 0$
  forces $k = 0$). $p$ empty: excluded by every size hypothesis except at rank $0$. $m$ or $n$ empty:
  $\mathbf{A} = \mathbf{0}$.
- *Ties* $\sigma_{k-1} = \sigma_k$ of $\mathsf{gn}$ or of $\mathbf{A}\mathbf{\Omega}$: `truncatedSVD` is
  the library's measurable choice; T11 and T10 hold for every best approximation, so TG5 and TG7
  hold for `truncatedSVD`; ET1 to ET6 use the same `truncatedSVD (A * X ω) k` on both sides.
- *Two sketches.* Independence is a hypothesis of every two-sketch expectation; without it GN's
  identity fails (e.g. $\mathbf{\Psi} = \mathbf{A}\mathbf{X}$ makes $\mathsf{gn}$ the RSVD).
  GN8 needs no independence (its route, §3.4).
- *Rank hypothesis of the split* (`(Ψᴴ * X).rank = X.rank`): never a hypothesis here (§2).

**Measurability.** All integrands are Borel functions of the test matrices (common step 2), so
every expectation comes with an `integrable_` companion (D4) and no selector appears. Integrability
of a GN error is law-specific, unlike S3's and S5's law-free companions: the oblique projector is
unbounded in $\mathbf{\Psi}$, and $\mathbb{E}\|\mathbf{A}-\mathsf{gn}\|_{\mathsf{F}}^2 = \infty$ for
Gaussian $\mathbf{\Psi}$ at $p = \operatorname{rank}(\mathbf{A}\mathbf{X}) + 1$. The companions
therefore carry the law of $\mathbf{\Psi}$ and the size condition, and leave $\mathbf{X}$ free.

### 3.1 Lower layers (13)

Labels L1 to L13. Homes and reasons in §4 (Placement).

```lean
/-- **Iterated integral against an independent pair** (Tonelli): for independent $U$, $W$ and a
measurable $f \ge 0$, $\int f(U, W)\,d\mu = \int\!\int f(u, w)\,d\mu_W(w)\,d\mu_U(u)$, with
$\mu_U$, $\mu_W$ the laws. Upstream candidate. -/
theorem _root_.ProbabilityTheory.IndepFun.lintegral_comp_eq_lintegral_lintegral {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {U : Ω → α} {W : Ω → β} (hUW : IndepFun U W μ)
    (hU : AEMeasurable U μ) (hW : AEMeasurable W μ) {f : α × β → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, f (U ω, W ω) ∂μ = ∫⁻ u, ∫⁻ w, f (u, w) ∂(μ.map W) ∂(μ.map U)

/-- The early-truncated randomized SVD
$\mathbf{\Omega} \mapsto \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)$ is a measurable
function of the test matrix. -/
theorem measurable_earlyTruncatedRSVD (A : Matrix m n 𝕜) (k : ℕ) :
    Measurable fun Ω : Matrix n l 𝕜 => earlyTruncatedRSVD A Ω k
/-- Early-truncated generalized Nyström is a measurable function of the two test matrices. -/
theorem measurable_earlyTruncatedGeneralizedNystrom (A : Matrix m n 𝕜) (k : ℕ) :
    Measurable fun ΩΨ : Matrix n l 𝕜 × Matrix m p 𝕜 =>
      earlyTruncatedGeneralizedNystrom A ΩΨ.1 ΩΨ.2 k

/-- Rescaling the sketch does not change the sketch-and-solve solution:
$\mathsf{sketchAndSolve}(\mathbf{A}, c\mathbf{S}, \mathbf{B}) =
\mathsf{sketchAndSolve}(\mathbf{A}, \mathbf{S}, \mathbf{B})$ for $c \ne 0$ (the normalisations
$\lvert k \rvert^{-1/2}\mathbf{G}$ and $\sqrt{\lvert n \rvert / \lvert k \rvert}\,\mathbf{Q}^{\mathsf{H}}$
of the Sketching round's Gaussian and Haar sketches). -/
theorem sketchAndSolve_smul_sketch (A : Matrix m n 𝕜) (S : Matrix k m 𝕜) (B : Matrix m p 𝕜)
    {c : 𝕜} (hc : c ≠ 0) : sketchAndSolve A (c • S) B = sketchAndSolve A S B

/-- The squared spectral norm of $\mathbf{S}\mathbf{G}\mathbf{T}$ is integrable for a standard
Gaussian $\mathbf{G}$. -/
theorem integrable_specNorm_mul_mul_sq_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix m n) μ) (S : Matrix a m ℝ) (T : Matrix n b ℝ) :
    Integrable (fun ω => specNorm (S * X ω * T) ^ 2) μ
/-- **The second spectral moment of a Gaussian product**: for a standard Gaussian $\mathbf{G}$,
$$\mathbb{E}\|\mathbf{S}\mathbf{G}\mathbf{T}\|_2^2 \le (\|\mathbf{S}\|_2\|\mathbf{T}\|_{\mathsf{F}} +
\|\mathbf{S}\|_{\mathsf{F}}\|\mathbf{T}\|_2)^2 + \|\mathbf{S}\|_2^2\|\mathbf{T}\|_2^2\,:$$
Chevet's first moment squared plus the variance, which Gaussian concentration bounds by the square
of the Lipschitz constant $\|\mathbf{S}\|_2\|\mathbf{T}\|_2$.
[TroppWebber2023, Lemma B.1]; there without the last term, by Slepian's lemma; here through
Gaussian concentration ([HalkoMartinssonTropp2011, Proposition 10.3]).
Result: chevet-inequality -/
theorem integral_specNorm_mul_mul_sq_le_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix m n) μ) (S : Matrix a m ℝ) (T : Matrix n b ℝ) :
    ∫ ω, specNorm (S * X ω * T) ^ 2 ∂μ ≤
      (specNorm S * frobNorm T + frobNorm S * specNorm T) ^ 2 + (specNorm S * specNorm T) ^ 2
/-- The same with random factors independent of the Gaussian matrix, conditionally. -/
theorem integral_specNorm_mul_mul_sq_le_of_hasLaw_gaussianMatrix_of_indepFun
    (hY : AEMeasurable Y μ) (hX : HasLaw X (gaussianMatrix m n) μ) (hXY : IndepFun Y X μ)
    (hS : Measurable S) (hT : Measurable T)
    (hST : Integrable (fun ω => (specNorm (S (Y ω)) * frobNorm (T (Y ω)) +
      frobNorm (S (Y ω)) * specNorm (T (Y ω))) ^ 2 + (specNorm (S (Y ω)) * specNorm (T (Y ω))) ^ 2) μ) :
    ∫ ω, specNorm (S (Y ω) * X ω * T (Y ω)) ^ 2 ∂μ ≤
      ∫ ω, ((specNorm (S (Y ω)) * frobNorm (T (Y ω)) + frobNorm (S (Y ω)) * specNorm (T (Y ω))) ^ 2 +
        (specNorm (S (Y ω)) * specNorm (T (Y ω))) ^ 2) ∂μ

/-- The squared spectral norm of the Gaussian block $\mathbf{S}\mathbf{G}_2\mathbf{G}_1^{+}$ is
integrable, for $\lvert r \rvert + 2 \le \lvert k \rvert$. -/
theorem integrable_specNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix [DecidableEq r]
    [DecidableEq s] (hX : HasLaw X (gaussianMatrix n k) μ) {V₁ : Matrix n r ℝ}
    {V₂ : Matrix n s ℝ} (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂)
    (h₁₂ : V₁ᴴ * V₂ = 0) (hrk : Fintype.card r + 2 ≤ Fintype.card k) (S : Matrix a s ℝ) :
    Integrable (fun ω => specNorm (S * (V₂ᴴ * X ω) * pinv (V₁ᴴ * X ω)) ^ 2) μ
/-- **The second spectral moment of a Gaussian block**: with
$\mathbf{G}_1 = \mathbf{V}_1^{\mathsf{H}}\mathbf{X}$, $\mathbf{G}_2 = \mathbf{V}_2^{\mathsf{H}}\mathbf{X}$
independent, $r = \lvert r \rvert$, $k = \lvert k \rvert$ and $r + 2 \le k$,
<!-- value gaussianPinvSpecNormBound r k -->
$$\mathbb{E}\|\mathbf{S}\mathbf{G}_2\mathbf{G}_1^{+}\|_2^2 \le \Bigl(\|\mathbf{S}\|_2
\sqrt{\tfrac{r}{k-r-1}} + \|\mathbf{S}\|_{\mathsf{F}}\,\tfrac{e}{k-r}\sqrt{\tfrac{k+r-1}{2}}\Bigr)^2
+ \|\mathbf{S}\|_2^2\,\frac{e^2(k+r-1)}{2(k-r)^2}\,,$$
the second-moment twin of `integral_specNorm_mul_mul_pinv_le_of_hasLaw_gaussianMatrix`.
[HalkoMartinssonTropp2011, proof of Theorem 10.6]; [TroppWebber2023, Lemmas B.1, B.3]; there the
first moment (HMT) or the second without the last term (TW). -/
theorem integral_specNorm_mul_mul_pinv_sq_le_of_hasLaw_gaussianMatrix [DecidableEq r]
    [DecidableEq s] (hX : HasLaw X (gaussianMatrix n k) μ) {V₁ : Matrix n r ℝ}
    {V₂ : Matrix n s ℝ} (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂)
    (h₁₂ : V₁ᴴ * V₂ = 0) (hrk : Fintype.card r + 2 ≤ Fintype.card k) (S : Matrix a s ℝ) :
    ∫ ω, specNorm (S * (V₂ᴴ * X ω) * pinv (V₁ᴴ * X ω)) ^ 2 ∂μ ≤
      (specNorm S * √((Fintype.card r : ℝ) / ((Fintype.card k : ℝ) - Fintype.card r - 1)) +
          frobNorm S * gaussianPinvSpecNormBound (Fintype.card r) (Fintype.card k)) ^ 2 +
        (specNorm S * gaussianPinvSpecNormBound (Fintype.card r) (Fintype.card k)) ^ 2
/-- Integrability of the transposed block (for the sketch-and-solve noise). -/
theorem integrable_specNorm_pinv_mul_mul_sq_of_hasLaw_gaussianMatrix [DecidableEq r]
    [DecidableEq s] (hX : HasLaw X (gaussianMatrix n k) μ) {V₁ : Matrix n r ℝ}
    {V₂ : Matrix n s ℝ} (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂)
    (h₁₂ : V₁ᴴ * V₂ = 0) (hrk : Fintype.card r + 2 ≤ Fintype.card k) (S : Matrix s a ℝ) :
    Integrable (fun ω => specNorm (pinv ((X ω)ᴴ * V₁) * ((X ω)ᴴ * V₂) * S) ^ 2) μ
/-- The transposed form: <!-- value gaussianPinvSpecNormBound r k -->
$\mathbb{E}\|\mathbf{G}_1^{\mathsf{H}+}\mathbf{G}_2^{\mathsf{H}}\mathbf{S}\|_2^2 \le
(\|\mathbf{S}\|_2\sqrt{r/(k-r-1)} + \|\mathbf{S}\|_{\mathsf{F}}\,e\sqrt{(k+r-1)/2}/(k-r))^2 +
\|\mathbf{S}\|_2^2 e^2(k+r-1)/(2(k-r)^2)$, the sketch-and-solve noise $(\mathbf{\Psi}^{\mathsf{H}}\mathbf{Q})^{+}
\mathbf{\Psi}^{\mathsf{H}}\mathbf{Q}_\perp\mathbf{S}$. -/
theorem integral_specNorm_pinv_mul_mul_sq_le_of_hasLaw_gaussianMatrix [DecidableEq r]
    [DecidableEq s] (hX : HasLaw X (gaussianMatrix n k) μ) {V₁ : Matrix n r ℝ}
    {V₂ : Matrix n s ℝ} (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂)
    (h₁₂ : V₁ᴴ * V₂ = 0) (hrk : Fintype.card r + 2 ≤ Fintype.card k) (S : Matrix s a ℝ) :
    ∫ ω, specNorm (pinv ((X ω)ᴴ * V₁) * ((X ω)ᴴ * V₂) * S) ^ 2 ∂μ ≤
      (specNorm S * √((Fintype.card r : ℝ) / ((Fintype.card k : ℝ) - Fintype.card r - 1)) +
          frobNorm S * gaussianPinvSpecNormBound (Fintype.card r) (Fintype.card k)) ^ 2 +
        (specNorm S * gaussianPinvSpecNormBound (Fintype.card r) (Fintype.card k)) ^ 2

/-- Integrability of the Haar block, for $\lvert r \rvert + 2 \le \lvert p \rvert \le \lvert m \rvert$. -/
theorem integrable_frobNorm_pinv_mul_mul_sq_of_hasLaw_haarFrame [DecidableEq p] [DecidableEq r]
    [DecidableEq s] {Q : Ω → Matrix m p ℝ} (hQ : HasLaw Q (haarFrame m p) μ)
    (hpm : Fintype.card p ≤ Fintype.card m) {V₁ : Matrix m r ℝ} {V₂ : Matrix m s ℝ}
    (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂) (h₁₂ : V₁ᴴ * V₂ = 0)
    (hrs : Fintype.card r + Fintype.card s = Fintype.card m)
    (hrp : Fintype.card r + 2 ≤ Fintype.card p) (B : Matrix s a ℝ) :
    Integrable (fun ω => frobNorm (pinv ((Q ω)ᴴ * V₁) * ((Q ω)ᴴ * V₂) * B) ^ 2) μ
/-- **The random orthonormal sketching identity**: for an $m \times p$ Haar frame $\mathbf{Q}$,
$p \le m$, complementary frames $\mathbf{V}_1$ ($r$ columns) and $\mathbf{V}_2$, and
$r + 2 \le p$,
$$\mathbb{E}\|(\mathbf{Q}^{\mathsf{H}}\mathbf{V}_1)^{+}\mathbf{Q}^{\mathsf{H}}\mathbf{V}_2\mathbf{B}
\|_{\mathsf{F}}^2 = \frac{m-p}{m-r}\cdot\frac{r}{p-r-1}\,\|\mathbf{B}\|_{\mathsf{F}}^2\,,$$
the Haar twin of `integral_frobNorm_pinv_mul_mul_sq_of_hasLaw_gaussianMatrix`, smaller by
$\frac{m-p}{m-r}$. The frames must be complementary (unlike the Gaussian case).
[EpperlyWebber2026, Proposition 5.7 at $\mathbf{R} = \mathbf{I}$]; real case.
Result: haar-sketching-identity -/
theorem integral_frobNorm_pinv_mul_mul_sq_of_hasLaw_haarFrame [DecidableEq p] [DecidableEq r]
    [DecidableEq s] {Q : Ω → Matrix m p ℝ} (hQ : HasLaw Q (haarFrame m p) μ)
    (hpm : Fintype.card p ≤ Fintype.card m) {V₁ : Matrix m r ℝ} {V₂ : Matrix m s ℝ}
    (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂) (h₁₂ : V₁ᴴ * V₂ = 0)
    (hrs : Fintype.card r + Fintype.card s = Fintype.card m)
    (hrp : Fintype.card r + 2 ≤ Fintype.card p) (B : Matrix s a ℝ) :
    ∫ ω, frobNorm (pinv ((Q ω)ᴴ * V₁) * ((Q ω)ᴴ * V₂) * B) ^ 2 ∂μ =
      frobNorm B ^ 2 * (((Fintype.card m : ℝ) - Fintype.card p) /
        ((Fintype.card m : ℝ) - Fintype.card r) *
          ((Fintype.card r : ℝ) / ((Fintype.card p : ℝ) - Fintype.card r - 1)))
```

Proof routes. *L1:* `indepFun_iff_map_prod_eq_prod_map_map` and `lintegral_map` to the product law,
then `lintegral_prod` (the pattern of `measureReal_not_le_add_mul_le_of_hasLaw_gaussianMatrix_of_indepFun`,
written once). *L2, L3:* unfold to `rangeProjector (truncatedSVD (A * Ω) k) * A` and
`truncatedSVD (A * Ω) k * pinv (Ψᴴ * truncatedSVD (A * Ω) k) * Ψᴴ * A`; `measurable_truncatedSVD`,
`measurable_rangeProjector`, `measurable_pinv`, `Measurable.matrix_mul`, as S2c's K10. *L4:*
`pinv_smul`, `Matrix.smul_mul`, `Matrix.mul_smul`, `inv_mul_cancel₀`, as `obliqueProjector_smul_right`.
*L5:* $\|\mathbf{S}\mathbf{G}\mathbf{T}\|_2 \le \|\mathbf{S}\|_2\|\mathbf{T}\|_2\|\mathbf{G}\|_{\mathsf{F}}$
and the Gaussian second moment of $\|\mathbf{G}\|_{\mathsf{F}}$ (`integral_frobNorm_mul_mul_sq_of_hasLaw_gaussianMatrix`
at identities), `Integrable.mono'`. *L6:* $f(\mathbf{G}) = \|\mathbf{S}\mathbf{G}\mathbf{T}\|_2$ is
$\|\mathbf{S}\|_2\|\mathbf{T}\|_2$-Lipschitz in the Frobenius distance (`specNorm_le_frobNorm`); then
`hasSubgaussianMGF_sub_integral_of_hasLaw_gaussianMatrix` and `HasSubgaussianMGF.integral_sq_le` give
$\mathbb{E}(f - \mathbb{E}f)^2 \le \|\mathbf{S}\|_2^2\|\mathbf{T}\|_2^2$; expand
$\mathbb{E}f^2 = (\mathbb{E}f)^2 + \mathbb{E}(f-\mathbb{E}f)^2$ and bound $\mathbb{E}f \ge 0$ by Chevet
(`integral_specNorm_mul_mul_le_of_hasLaw_gaussianMatrix`). About 40 lines. *L7:* L6 inside L1 on the
pair $(Y, \mathbf{G})$, as the first-moment `_of_indepFun` form. *L8, L9:* condition on
$\mathbf{G}_1$ (`indepFun_conjTranspose_mul_of_hasLaw_gaussianMatrix`) and apply L7 with
$\mathbf{T} = \mathbf{G}_1^{+}$; then
$\mathbb{E}(a\|\mathbf{T}\|_{\mathsf{F}} + b\|\mathbf{T}\|_2)^2 \le (a\sqrt{\mathbb{E}\|\mathbf{T}\|_{\mathsf{F}}^2}
+ b\sqrt{\mathbb{E}\|\mathbf{T}\|_2^2})^2$ (Cauchy–Schwarz, `integral_mul_le_Lp_mul_Lq_of_nonneg`), with
R4's `integral_frobNorm_pinv_sq_of_hasLaw_gaussianMatrix` ($= r/(k-r-1)$) and
`integral_specNorm_pinv_rpow_le_of_hasLaw_gaussianMatrix` at $q = 2$ ($\le \beta^2$, needs
$2 \le k - r$). *L10, L11:* L8, L9 at $\mathbf{S}^{\mathsf{H}}$ through `specNorm_conjTranspose` and
`pinv_conjTranspose` (as R4's Frobenius bridge). *L12, L13:* EW's proof of Proposition 5.7 at
$\mathbf{R} = \mathbf{I}$, with $\mathbf{\Omega}_1 = \mathbf{V}_1^{\mathsf{H}}\mathbf{Q}$,
$\mathbf{\Omega}_2 = \mathbf{V}_2^{\mathsf{H}}\mathbf{Q}$: the squared norm is
$\operatorname{tr}(\mathbf{B}^{\mathsf{H}}\mathbf{\Omega}_2\mathbf{Y}\mathbf{\Omega}_2^{\mathsf{H}}
\mathbf{B})$ with $\mathbf{Y}$ a function of $\mathbf{\Omega}_1$; (S4-ii) replaces
$\mathbb{E}[\mathbf{\Omega}_2\mathbf{Y}\mathbf{\Omega}_2^{\mathsf{H}}]$ by
$\frac{\mathbb{E}\operatorname{tr}(\mathbf{Y}\mathbf{\Omega}_2^{\mathsf{H}}\mathbf{\Omega}_2)}{m - r}
\mathbf{I}$; $\mathbf{\Omega}_1^{\mathsf{H}}\mathbf{\Omega}_1 + \mathbf{\Omega}_2^{\mathsf{H}}
\mathbf{\Omega}_2 = \mathbf{Q}^{\mathsf{H}}\mathbf{Q} = \mathbf{I}$ almost surely (`hrs`,
`ae_hasOrthonormalCols_of_hasLaw_haarFrame`) gives $\operatorname{tr}(\mathbf{Y}\mathbf{\Omega}_2^{\mathsf{H}}
\mathbf{\Omega}_2) = \operatorname{tr}((\mathbf{\Omega}_1\mathbf{\Omega}_1^{\mathsf{H}})^{-1}) - r$ on
the full-rank event; (S4-i) evaluates it. Integrability: $\|\mathbf{Q}^{\mathsf{H}}\mathbf{V}_2\|_2
\le 1$ (`ae_specNorm_le_one_of_hasLaw_haarFrame`) bounds the integrand by
$\|(\mathbf{Q}^{\mathsf{H}}\mathbf{V}_1)^{+}\|_{\mathsf{F}}^2\|\mathbf{B}\|_2^2$, integrable by (S4-i).
About 80 lines. Degenerate: $r = 0$, both sides $0$; $p = m$, both sides $0$
($\mathbf{Q}$ orthogonal, $\mathbf{Q}^{\mathsf{H}}\mathbf{V}_2$ has range orthogonal to that of
$\mathbf{Q}^{\mathsf{H}}\mathbf{V}_1$).

### 3.2 `Sketching/Gaussian/LeastSquares.lean`: Gaussian and Haar sketch-and-solve (17)

Real. Gaussian sketch `(hS : HasLaw S (gaussianMatrix p m) μ)`; Haar frame
`(hQ : HasLaw Q (haarFrame m p) μ) (hpm : Fintype.card p ≤ Fintype.card m)` with `[DecidableEq p]`
and the sketch $\mathbf{Q}^{\mathsf{H}}$. Labels A1 to A17.

```lean
/-- **The Haar completion factor**
$h_d(p, q) = 1 + \frac{d-p}{d-q}\cdot\frac{q}{p-q-1}$: the factor by which a Haar sketch of size $p$
in dimension $d$ inflates the least-squares error of a rank-$q$ basis (EW's random orthonormal
constant). Junk for $p \le q + 1$ or $d \le q$; theorems carry `q + 2 ≤ p` and `p ≤ d`.
[EpperlyWebber2026, Theorem 2.1]. -/
noncomputable def haarProjectionFactor (d p q : ℕ) : ℝ :=
  1 + ((d : ℝ) - p) / ((d : ℝ) - q) * ((q : ℝ) / ((p : ℝ) - q - 1))
@[simp] theorem haarProjectionFactor_def (d p q : ℕ) :
    haarProjectionFactor d p q = 1 + ((d : ℝ) - p) / ((d : ℝ) - q) * ((q : ℝ) / ((p : ℝ) - q - 1))
theorem one_le_haarProjectionFactor {d p q : ℕ} (hqp : q + 2 ≤ p) (hpd : p ≤ d) :
    1 ≤ haarProjectionFactor d p q
/-- Monotone in the rank: the completion factor at the actual rank is at most the factor at any
larger rank. -/
theorem haarProjectionFactor_le_haarProjectionFactor {d p q q' : ℕ} (hq : q ≤ q')
    (hq' : q' + 2 ≤ p) (hpd : p ≤ d) : haarProjectionFactor d p q ≤ haarProjectionFactor d p q'
/-- **Orthogonality helps, but only a bit**: the Haar factor is at most the Gaussian one,
$h_d(p, q) \le 1 + \frac{q}{p-q-1}$, with ratio of excesses $\frac{d-p}{d-q}$.
[EpperlyWebber2026, §2.1]. -/
theorem haarProjectionFactor_le_gaussianProjectionFactor {d p q : ℕ} (hqp : q + 2 ≤ p)
    (hpd : p ≤ d) : haarProjectionFactor d p q ≤ gaussianProjectionFactor q p

/-- **The Gaussian completion identity**: for a standard Gaussian $p \times m$ sketch $\mathbf{S}$,
every fixed $\mathbf{X}$ with $\operatorname{rank}\mathbf{X} + 2 \le p$ and every $\mathbf{B}$,
$$\mathbb{E}\|(\mathbf{I}-\mathbf{\Pi}_{\mathbf{X},\mathbf{S}})\mathbf{B}\|_{\mathsf{F}}^2 =
\Bigl(1 + \frac{q}{p-q-1}\Bigr)\|(\mathbf{I}-\mathbf{P}_{\mathbf{X}})\mathbf{B}\|_{\mathsf{F}}^2,
\qquad q = \operatorname{rank}\mathbf{X}\,:$$
the oblique projection inflates the orthogonal projection's error by exactly the factor
`gaussianProjectionFactor q p`. No full rank of $\mathbf{X}$ is assumed.
[EpperlyWebber2026, Theorem 2.1 and Lemma 5.1]; [TroppYurtseverUdellCevher2017, Lemma A.5];
there for $\mathbf{X} = \mathbf{A}$ (EW) or an orthonormal $\mathbf{Q}$ (TYUC), here any basis of
any rank. Result: sketch-and-solve-expected-error -/
theorem integral_frobNorm_one_sub_obliqueProjector_mul_sq_of_hasLaw_gaussianMatrix
    (hS : HasLaw S (gaussianMatrix p m) μ) (X : Matrix m s ℝ)
    (hX : X.rank + 2 ≤ Fintype.card p) (B : Matrix m r ℝ) :
    ∫ ω, frobNorm ((1 - obliqueProjector X (S ω)) * B) ^ 2 ∂μ =
      gaussianProjectionFactor X.rank (Fintype.card p) * frobNorm ((1 - rangeProjector X) * B) ^ 2
theorem integrable_frobNorm_one_sub_obliqueProjector_mul_sq_of_hasLaw_gaussianMatrix
    (hS : HasLaw S (gaussianMatrix p m) μ) (X : Matrix m s ℝ)
    (hX : X.rank + 2 ≤ Fintype.card p) (B : Matrix m r ℝ) :
    Integrable (fun ω => frobNorm ((1 - obliqueProjector X (S ω)) * B) ^ 2) μ
/-- **Exact mean squared residual of Gaussian sketch-and-solve**: for $r = \operatorname{rank}
\mathbf{A}$ with $r + 2 \le p$,
$$\mathbb{E}\|\mathbf{B} - \mathbf{A}\,\mathsf{sketchAndSolve}(\mathbf{A}, \mathbf{S}, \mathbf{B})
\|_{\mathsf{F}}^2 = \Bigl(1 + \frac{r}{p-r-1}\Bigr)\min_{\mathbf{Y}}\|\mathbf{B}-\mathbf{A}\mathbf{Y}
\|_{\mathsf{F}}^2\,,$$
the minimum being $\|(\mathbf{I}-\mathbf{P}_{\mathbf{A}})\mathbf{B}\|_{\mathsf{F}}^2$. Its integrand
is A6's (`mul_sketchAndSolve`), so A7 is its integrability.
[EpperlyWebber2026, Theorem 2.1 (Gaussian)]; real case, $\alpha_{\mathbb{R}} = 1$; first proved by
Bartan and Pilanci (as EW report). Result: sketch-and-solve-expected-error -/
theorem integral_frobNorm_sub_mul_sketchAndSolve_sq_of_hasLaw_gaussianMatrix
    (hS : HasLaw S (gaussianMatrix p m) μ) {A : Matrix m n ℝ}
    (hA : A.rank + 2 ≤ Fintype.card p) (B : Matrix m r ℝ) :
    ∫ ω, frobNorm (B - A * sketchAndSolve A (S ω) B) ^ 2 ∂μ =
      gaussianProjectionFactor A.rank (Fintype.card p) * frobNorm ((1 - rangeProjector A) * B) ^ 2
/-- **Gaussian sketch-and-solve is unbiased**: $\mathbb{E}\,\mathsf{sketchAndSolve}(\mathbf{A},
\mathbf{S}, \mathbf{B}) = \mathbf{A}^{+}\mathbf{B}$ for $\operatorname{rank}\mathbf{A} + 1 \le p$. At
$\mathbf{A} = \mathbf{Q}$ with orthonormal columns this is the unbiasedness of the sketched core of
generalized Nyström. [EpperlyWebber2026, Theorem 2.1]; [TroppYurtseverUdellCevher2017,
Lemma A.5]; there with $\operatorname{rank}\mathbf{A} + 2 \le p$.
Result: sketch-and-solve-expected-error -/
theorem integral_sketchAndSolve_of_hasLaw_gaussianMatrix (hS : HasLaw S (gaussianMatrix p m) μ)
    {A : Matrix m n ℝ} (hA : A.rank + 1 ≤ Fintype.card p) (B : Matrix m r ℝ) :
    ∫ ω, sketchAndSolve A (S ω) B ∂μ = pinv A * B
theorem integrable_sketchAndSolve_of_hasLaw_gaussianMatrix (hS : HasLaw S (gaussianMatrix p m) μ)
    {A : Matrix m n ℝ} (hA : A.rank + 1 ≤ Fintype.card p) (B : Matrix m r ℝ) :
    Integrable (fun ω => sketchAndSolve A (S ω) B) μ
/-- **The spectral norm of the Gaussian sketch-and-solve excess**: with
$\mathbf{E} = (\mathbf{I}-\mathbf{P}_{\mathbf{X}})\mathbf{B}$, $q = \operatorname{rank}\mathbf{X}$ and
$q + 2 \le p$, <!-- value gaussianPinvSpecNormBound q p -->
$$\mathbb{E}\|\mathbf{\Pi}_{\mathbf{X},\mathbf{S}}\mathbf{E}\|_2^2 \le
\Bigl(\|\mathbf{E}\|_2\sqrt{\tfrac{q}{p-q-1}} + \|\mathbf{E}\|_{\mathsf{F}}\,
\tfrac{e}{p-q}\sqrt{\tfrac{p+q-1}{2}}\Bigr)^2 + \|\mathbf{E}\|_2^2\,\frac{e^2(p+q-1)}{2(p-q)^2}\,.$$
For $p \ge 4q$ this is at most $\frac{25}{p}\|\mathbf{E}\|_{\mathsf{F}}^2 + \frac{4q}{p}\|\mathbf{E}\|_2^2$:
the excess is spectrally flat. It is the core noise of generalized Nyström in projector form.
Proved without a literature source; inputs [TroppWebber2023, Lemmas B.1, B.3] (in the forms of
this library); the algebra is [EpperlyWebber2026, Lemma 5.1] and [TroppYurtseverUdellCevher2017,
Lemma A.4]. -/
theorem integral_specNorm_obliqueProjector_mul_one_sub_rangeProjector_mul_sq_le_of_hasLaw_gaussianMatrix
    (hS : HasLaw S (gaussianMatrix p m) μ) (X : Matrix m s ℝ)
    (hX : X.rank + 2 ≤ Fintype.card p) (B : Matrix m r ℝ) :
    ∫ ω, specNorm (obliqueProjector X (S ω) * ((1 - rangeProjector X) * B)) ^ 2 ∂μ ≤
      (specNorm ((1 - rangeProjector X) * B) *
            √((X.rank : ℝ) / ((Fintype.card p : ℝ) - X.rank - 1)) +
          frobNorm ((1 - rangeProjector X) * B) *
            gaussianPinvSpecNormBound X.rank (Fintype.card p)) ^ 2 +
        (specNorm ((1 - rangeProjector X) * B) *
          gaussianPinvSpecNormBound X.rank (Fintype.card p)) ^ 2
theorem integrable_specNorm_obliqueProjector_mul_one_sub_rangeProjector_mul_sq_of_hasLaw_gaussianMatrix
    (hS : HasLaw S (gaussianMatrix p m) μ) (X : Matrix m s ℝ)
    (hX : X.rank + 2 ≤ Fintype.card p) (B : Matrix m r ℝ) :
    Integrable (fun ω => specNorm (obliqueProjector X (S ω) * ((1 - rangeProjector X) * B)) ^ 2) μ

/-- **The Haar completion identity**: for an $m \times p$ Haar frame $\mathbf{Q}$, $p \le m$,
the sketch $\mathbf{Q}^{\mathsf{H}}$, every fixed $\mathbf{X}$ with $\operatorname{rank}\mathbf{X} + 2
\le p$ and every $\mathbf{B}$,
$$\mathbb{E}\|(\mathbf{I}-\mathbf{\Pi}_{\mathbf{X},\mathbf{Q}^{\mathsf{H}}})\mathbf{B}\|_{\mathsf{F}}^2
= \Bigl(1 + \frac{m-p}{m-q}\cdot\frac{q}{p-q-1}\Bigr)
\|(\mathbf{I}-\mathbf{P}_{\mathbf{X}})\mathbf{B}\|_{\mathsf{F}}^2\,.$$
[EpperlyWebber2026, Theorem 2.1 and Proposition 5.7]; there for $\mathbf{X} = \mathbf{A}$.
Result: sketch-and-solve-expected-error -/
theorem integral_frobNorm_one_sub_obliqueProjector_mul_sq_of_hasLaw_haarFrame [DecidableEq p]
    (hQ : HasLaw Q (haarFrame m p) μ) (hpm : Fintype.card p ≤ Fintype.card m)
    (X : Matrix m s ℝ) (hX : X.rank + 2 ≤ Fintype.card p) (B : Matrix m r ℝ) :
    ∫ ω, frobNorm ((1 - obliqueProjector X (Q ω)ᴴ) * B) ^ 2 ∂μ =
      haarProjectionFactor (Fintype.card m) (Fintype.card p) X.rank *
        frobNorm ((1 - rangeProjector X) * B) ^ 2
theorem integrable_frobNorm_one_sub_obliqueProjector_mul_sq_of_hasLaw_haarFrame [DecidableEq p]
    (hQ : HasLaw Q (haarFrame m p) μ) (hpm : Fintype.card p ≤ Fintype.card m)
    (X : Matrix m s ℝ) (hX : X.rank + 2 ≤ Fintype.card p) (B : Matrix m r ℝ) :
    Integrable (fun ω => frobNorm ((1 - obliqueProjector X (Q ω)ᴴ) * B) ^ 2) μ
/-- **Exact mean squared residual of sketch-and-solve with a random orthonormal sketch**
[EpperlyWebber2026, Theorem 2.1 (random orthonormal)]; real case, the formula new in EW.
Result: sketch-and-solve-expected-error -/
theorem integral_frobNorm_sub_mul_sketchAndSolve_sq_of_hasLaw_haarFrame [DecidableEq p]
    (hQ : HasLaw Q (haarFrame m p) μ) (hpm : Fintype.card p ≤ Fintype.card m)
    {A : Matrix m n ℝ} (hA : A.rank + 2 ≤ Fintype.card p) (B : Matrix m r ℝ) :
    ∫ ω, frobNorm (B - A * sketchAndSolve A (Q ω)ᴴ B) ^ 2 ∂μ =
      haarProjectionFactor (Fintype.card m) (Fintype.card p) A.rank *
        frobNorm ((1 - rangeProjector A) * B) ^ 2
/-- **Sketch-and-solve with a random orthonormal sketch is unbiased**.
[EpperlyWebber2026, Theorem 2.1]. Result: sketch-and-solve-expected-error -/
theorem integral_sketchAndSolve_of_hasLaw_haarFrame [DecidableEq p]
    (hQ : HasLaw Q (haarFrame m p) μ) (hpm : Fintype.card p ≤ Fintype.card m)
    {A : Matrix m n ℝ} (hA : A.rank + 2 ≤ Fintype.card p) (B : Matrix m r ℝ) :
    ∫ ω, sketchAndSolve A (Q ω)ᴴ B ∂μ = pinv A * B
theorem integrable_sketchAndSolve_of_hasLaw_haarFrame [DecidableEq p]
    (hQ : HasLaw Q (haarFrame m p) μ) (hpm : Fintype.card p ≤ Fintype.card m)
    {A : Matrix m n ℝ} (hA : A.rank + 2 ≤ Fintype.card p) (B : Matrix m r ℝ) :
    Integrable (fun ω => sketchAndSolve A (Q ω)ᴴ B) μ
```

Proof routes. *A2 to A5:* `field_simp`, `div_le_div` monotonicity on $q \mapsto \frac{d-p}{d-q}$ and
$q \mapsto \frac{q}{p-q-1}$ (both nonnegative and nondecreasing on $q \le p - 2 < d$); A5 from
$\frac{d-p}{d-q} \le 1$. *A6, A7:* the split `frobNorm_one_sub_obliqueProjector_mul_sq` on the
full-rank event (common step 3, at `Z := X` with the Gaussian `Sᴴ` from
`hasLaw_conjTranspose_of_hasLaw_gaussianMatrix`), `integral_congr_ae`, `integral_add`; the second term
by common step 1 and R4's `integral_frobNorm_pinv_mul_mul_sq_of_hasLaw_gaussianMatrix` (with its
integrable twin) at $\mathbf{V}_1 = \mathbf{Q}_1$, $\mathbf{V}_2 = \mathbf{Q}_2$,
$\mathbf{S} = \mathbf{Q}_2^{\mathsf{H}}\mathbf{B}$; then `gaussianProjectionFactor_def`, `ring`. Rank $0$
is not special. *A8:* A6 at `X := A` after `mul_sketchAndSolve` and `Matrix.sub_mul`. *A9, A10:* on the
full-rank event `sketchAndSolve_eq_pinv_mul_add` writes the solution as $\mathbf{A}^{+}\mathbf{B} +
f(\mathbf{S})$ with $f(\mathbf{S}) = (\mathbf{S}\mathbf{A})^{+}\mathbf{S}\mathbf{E}$,
$\mathbf{E} = (\mathbf{I}-\mathbf{P}_{\mathbf{A}})\mathbf{B}$. The reflection
$\mathbf{D} = 2\mathbf{P}_{\mathbf{A}} - \mathbf{I}$ is orthogonal, fixes $\mathbf{A}$ and negates
$\mathbf{E}$, so $f(\mathbf{S}\mathbf{D}) = -f(\mathbf{S})$, and $\mathbf{S}\mathbf{D}$ has the law of
$\mathbf{S}$ (`hasLaw_mul_const_of_hasLaw_gaussianMatrix`): $\mathbb{E}f = -\mathbb{E}f = \mathbf{0}$.
No basis, no complement. Integrability (A10): through common step 1,
$\|f\| \le \|(\mathbf{G}^{\mathsf{H}}\mathbf{Q}_1)^{+}\|_2\,\|\mathbf{G}^{\mathsf{H}}\mathbf{Q}_2
\mathbf{Q}_2^{\mathsf{H}}\mathbf{E}\|_{\mathsf{F}}\,\|\mathbf{R}^{+}\|_2$ for $\mathbf{A} =
\mathbf{Q}_1\mathbf{R}$, a product of independent integrable factors
(`integrable_specNorm_pinv_rpow_of_hasLaw_gaussianMatrix` at exponent $1 \le p - r$, R2's first
moment, `IndepFun.integrable_mul`). *A11, A12:* common step 1 at the spectral norm, then L11 at
$\mathbf{V}_1 = \mathbf{Q}_1$, $\mathbf{V}_2 = \mathbf{Q}_2$, $\mathbf{S} = \mathbf{Q}_2^{\mathsf{H}}
\mathbf{B}$ ($\|\mathbf{S}\| = \|\mathbf{E}\|$ in both norms). The "$p \ge 4q$" sentence of the
docstring is arithmetic on `gaussianPinvSpecNormBound_def` ($\beta^2 \le 8.21/p$ and
$\frac{q}{p-q-1} \le \frac{2q}{p}$, §3.7); it is not a separate statement. *A13 to A17:* as A6 to A10
with L12, L13 in place of R4 and `hasLaw_const_mul_of_isLeftUnitarilyInvariant` (the reflection acts
on the left of the frame) in place of the Gaussian invariance; integrability of the solution from
(S4-i) by Cauchy–Schwarz. Degenerate: §3.0.

### 3.3 `LowRank/Gaussian/RangeFinder.lean`: the spectral second moment of the range finder (1)

Label D1. Added to S3's registered file, beside G4 and G5.

```lean
/-- **The expected squared spectral error of the randomized SVD, HMT 10.6 form**: for a standard
Gaussian $n \times \ell$ test matrix and $k + 2 \le \ell$, <!-- value gaussianPinvSpecNormBound k \ell -->
$$\mathbb{E}\|\mathbf{A}-\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_2^2 \le \sigma_k^2 +
\Bigl(\sigma_k\sqrt{\tfrac{k}{\ell-k-1}} + \tfrac{e}{\ell-k}\sqrt{\tfrac{\ell+k-1}{2}}\,
\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}\Bigr)^2 +
\sigma_k^2\,\frac{e^2(\ell+k-1)}{2(\ell-k)^2}\,,$$
singular values from $0$. With the last factor $O(1/\ell)$ the Frobenius tail enters with weight
$O(1/\ell)$, against $\frac{k}{\ell-k-1}$ in
`integral_specNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix`; incomparable with it (better when the
tail is heavy and $\ell \gg k$). Split at $k = \lceil\ell/2\rceil$ and with the tail flattening it
bounds the spectral error by $O(1/\ell)$ times the Frobenius tail at any $k \le \ell/4$.
[HalkoMartinssonTropp2011, Theorem 10.6]; there the first moment; proved without a literature source
in this second-moment form. Result: randomized-svd-average-spectral-error -/
theorem integral_specNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix_pinvSpecNormBound
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ}
    (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, specNorm (A - rsvd A (X ω)) ^ 2 ∂μ ≤
      singularValues A k ^ 2 +
        (singularValues A k * √((k : ℝ) / ((Fintype.card l : ℝ) - k - 1)) +
          gaussianPinvSpecNormBound k (Fintype.card l) * frobNorm (A - truncatedSVD A k)) ^ 2 +
        (singularValues A k * gaussianPinvSpecNormBound k (Fintype.card l)) ^ 2
```

Proof route. As S3's G4 and G5: for $k > \lvert n\rvert$ the error is $0$ almost surely and the right
side is nonnegative (S3's private exact branch, which the side file restates or S3 makes public;
§4 flag); otherwise $\mathbf{Z}$ the top-$k$ right singular frame, S1's
`HasOrthonormalCols.specNorm_sub_rsvd_sq_le` on the full-rank event, $\|\mathbf{A}-\mathbf{A}\mathbf{Z}
\mathbf{Z}^{\mathsf{H}}\|_2 = \sigma_k$, and L9 at $\mathbf{S} = (\mathbf{A}-\mathbf{A}\mathbf{Z}
\mathbf{Z}^{\mathsf{H}})\mathbf{Z}_\perp$ ($\|\mathbf{S}\|_2 = \sigma_k$, $\|\mathbf{S}\|_{\mathsf{F}} =
\mathrm{OPT}_k$). Integrability: S3's `integrable_specNorm_sub_rsvd_sq`. Degenerate: $k = 0$ gives
$\mathbb{E}\|\mathbf{A}-\mathsf{rsvd}\|_2^2 \le \|\mathbf{A}\|_2^2(1 + \beta^2) + \beta^2\|\mathbf{A}
\|_{\mathsf{F}}^2$, true (the error is at most $\|\mathbf{A}\|_2$).

### 3.4 `LowRank/Gaussian/GeneralizedNystrom.lean`: generalized Nyström in expectation (13)

Real. `(A : Matrix m n ℝ)`, `X : Ω → Matrix n l ℝ`, `Ψ : Ω → Matrix m p ℝ`, `X₀ : Matrix n l ℝ`.
Gaussian co-range sketch `(hΨ : HasLaw Ψ (gaussianMatrix m p) μ)`; Haar `(hΨ : HasLaw Ψ (haarFrame m p)
μ) (hpm : Fintype.card p ≤ Fintype.card m)` with `[DecidableEq p]`. Labels GN1 to GN8, GH1 to GH5.

```lean
/-- **Generalized Nyström conditionally on the range test matrix**: for a fixed test matrix
$\mathbf{\Omega}$, a standard Gaussian $m \times p$ co-range test matrix $\mathbf{\Psi}$ and
$q = \operatorname{rank}(\mathbf{A}\mathbf{\Omega})$ with $q + 2 \le p$,
$$\mathbb{E}_{\mathbf{\Psi}}\|\mathbf{A}-\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})
\|_{\mathsf{F}}^2 = \Bigl(1 + \frac{q}{p-q-1}\Bigr)\|\mathbf{A}-\mathsf{rsvd}(\mathbf{A},
\mathbf{\Omega})\|_{\mathsf{F}}^2\,.$$
[EpperlyWebber2026, proof of Theorem 4.2]; [TroppYurtseverUdellCevher2017, Lemmas A.3, A.5]; there
with $q$ the sketch size (full rank). Result: generalized-nystrom-expected-error -/
theorem integral_frobNorm_sub_generalizedNystrom_sq_of_hasLaw_gaussianMatrix (A : Matrix m n ℝ)
    (X₀ : Matrix n l ℝ) (hΨ : HasLaw Ψ (gaussianMatrix m p) μ)
    (hr : (A * X₀).rank + 2 ≤ Fintype.card p) :
    ∫ ω, frobNorm (A - generalizedNystrom A X₀ (Ψ ω)) ^ 2 ∂μ =
      gaussianProjectionFactor (A * X₀).rank (Fintype.card p) * frobNorm (A - rsvd A X₀) ^ 2
/-- **Generalized Nyström = randomized SVD × completion, for any law of the range test matrix**:
for $\mathbf{\Omega}$ independent of a standard Gaussian $\mathbf{\Psi}$, and
$\operatorname{rank}(\mathbf{A}\mathbf{\Omega}) + 2 \le p$ almost surely,
$$\mathbb{E}\|\mathbf{A}-\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})\|_{\mathsf{F}}^2 =
\mathbb{E}\Bigl[\Bigl(1 + \frac{q}{p-q-1}\Bigr)\|\mathbf{A}-\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})
\|_{\mathsf{F}}^2\Bigr],\qquad q = \operatorname{rank}(\mathbf{A}\mathbf{\Omega})\,:$$
the rank stays inside the expectation. [EpperlyWebber2026, proof of Theorem 4.2];
[TroppYurtseverUdellCevher2017, §A.3.4]. Result: generalized-nystrom-expected-error -/
theorem integral_frobNorm_sub_generalizedNystrom_sq_eq_integral_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : AEMeasurable X μ) (hΨ : HasLaw Ψ (gaussianMatrix m p) μ)
    (hXΨ : IndepFun X Ψ μ) (hr : ∀ᵐ ω ∂μ, (A * X ω).rank + 2 ≤ Fintype.card p) :
    ∫ ω, frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2 ∂μ =
      ∫ ω, gaussianProjectionFactor (A * X ω).rank (Fintype.card p) *
        frobNorm (A - rsvd A (X ω)) ^ 2 ∂μ
/-- **...bound form**, for any law of $\mathbf{\Omega}$ and $\ell + 2 \le p$:
$\mathbb{E}\|\mathbf{A}-\mathsf{gn}\|_{\mathsf{F}}^2 \le (1 + \frac{\ell}{p-\ell-1})\,
\mathbb{E}\|\mathbf{A}-\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_{\mathsf{F}}^2$. Any bound on the
randomized SVD (Gaussian, rotation-invariant, OSI) becomes a bound on generalized Nyström.
[CamanoEpperlyMeyerTropp2025, proof of Corollary 2.8]; [TroppYurtseverUdellCevher2017, §A.3.4].
Result: generalized-nystrom-expected-error -/
theorem integral_frobNorm_sub_generalizedNystrom_sq_le_mul_integral_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : AEMeasurable X μ) (hΨ : HasLaw Ψ (gaussianMatrix m p) μ)
    (hXΨ : IndepFun X Ψ μ) (hlp : Fintype.card l + 2 ≤ Fintype.card p) :
    ∫ ω, frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2 ∂μ ≤
      gaussianProjectionFactor (Fintype.card l) (Fintype.card p) *
        ∫ ω, frobNorm (A - rsvd A (X ω)) ^ 2 ∂μ
/-- The generalized Nyström error is integrable under a Gaussian co-range test matrix independent
of the range test matrix, when $\operatorname{rank}(\mathbf{A}\mathbf{\Omega}) + 2 \le p$ almost
surely. It need not be otherwise. -/
theorem integrable_frobNorm_sub_generalizedNystrom_sq_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : AEMeasurable X μ) (hΨ : HasLaw Ψ (gaussianMatrix m p) μ)
    (hXΨ : IndepFun X Ψ μ) (hr : ∀ᵐ ω ∂μ, (A * X ω).rank + 2 ≤ Fintype.card p) :
    Integrable (fun ω => frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2) μ
/-- **The generalized Nyström identity, Gaussian test matrices**: with
$\ell' = \min(\operatorname{rank}\mathbf{A}, \ell)$ (the almost sure rank of the sketch) and
$\ell' + 2 \le p$,
$$\mathbb{E}\|\mathbf{A}-\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})\|_{\mathsf{F}}^2 =
\Bigl(1 + \frac{\ell'}{p-\ell'-1}\Bigr)\,\mathbb{E}\|\mathbf{A}-\mathsf{rsvd}(\mathbf{A},
\mathbf{\Omega})\|_{\mathsf{F}}^2\,.$$
[EpperlyWebber2026, proof of Theorem 4.2(a), $\gamma = 1$]; there for $\operatorname{rank}\mathbf{A}
\ge p$. Result: generalized-nystrom-expected-error -/
theorem integral_frobNorm_sub_generalizedNystrom_sq_eq_mul_integral_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) (hΨ : HasLaw Ψ (gaussianMatrix m p) μ)
    (hXΨ : IndepFun X Ψ μ) (hr : min A.rank (Fintype.card l) + 2 ≤ Fintype.card p) :
    ∫ ω, frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2 ∂μ =
      gaussianProjectionFactor (min A.rank (Fintype.card l)) (Fintype.card p) *
        ∫ ω, frobNorm (A - rsvd A (X ω)) ^ 2 ∂μ
/-- **The expected error of generalized Nyström** (Gaussian test matrices): for $k + 2 \le \ell$ and
$\ell + 2 \le p$,
$$\mathbb{E}\|\mathbf{A}-\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})\|_{\mathsf{F}}^2 \le
\Bigl(1 + \frac{\ell}{p-\ell-1}\Bigr)\Bigl(1 + \frac{k}{\ell-k-1}\Bigr)
\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,.$$
[TroppYurtseverUdellCevher2017, Theorem 4.3]; there with a minimum over $k$ (not stated, rule 5).
Result: generalized-nystrom-expected-error -/
theorem integral_frobNorm_sub_generalizedNystrom_sq_le_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) (hΨ : HasLaw Ψ (gaussianMatrix m p) μ)
    (hXΨ : IndepFun X Ψ μ) {k : ℕ} (hk : k + 2 ≤ Fintype.card l)
    (hlp : Fintype.card l + 2 ≤ Fintype.card p) :
    ∫ ω, frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2 ∂μ ≤
      gaussianProjectionFactor (Fintype.card l) (Fintype.card p) *
        gaussianProjectionFactor k (Fintype.card l) * frobNorm (A - truncatedSVD A k) ^ 2
/-- **The sharp upper bound for generalized Nyström, Gaussian co-range**: for a rotation-invariant
$\mathbf{\Omega}$ of full column rank, a standard Gaussian $\mathbf{\Psi}$ independent of it,
$\ell \le \operatorname{rank}\mathbf{A} = r$, $\ell + 2 \le p$ and $q + 2 \le \ell$,
$$\mathbb{E}\|\mathbf{A}-\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})\|_{\mathsf{F}}^2 \le
\Bigl(1 + \frac{\ell}{p-\ell-1}\Bigr)\frac{r-\ell}{r-q}\Bigl(1 + \frac{q}{\ell-q-1}\Bigr)
\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_q\|_{\mathsf{F}}^2\,.$$
[EpperlyWebber2026, Theorem 4.2(a), $\gamma = 1$]; there $r \ge p$ and a minimum over $q$.
Result: generalized-nystrom-expected-error -/
theorem integral_frobNorm_sub_generalizedNystrom_sq_le_of_isLeftUnitarilyInvariant_of_hasLaw_gaussianMatrix
    [DecidableEq n] {ν : Measure (Matrix n l ℝ)} [IsProbabilityMeasure ν]
    [IsLeftUnitarilyInvariant ν] (A : Matrix m n ℝ) (hX : HasLaw X ν μ)
    (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) (hΨ : HasLaw Ψ (gaussianMatrix m p) μ)
    (hXΨ : IndepFun X Ψ μ) (hlA : Fintype.card l ≤ A.rank)
    (hlp : Fintype.card l + 2 ≤ Fintype.card p) {q : ℕ} (hq : q + 2 ≤ Fintype.card l) :
    ∫ ω, frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2 ∂μ ≤
      gaussianProjectionFactor (Fintype.card l) (Fintype.card p) *
        rotationInvariantFactor A.rank (Fintype.card l) q * frobNorm (A - truncatedSVD A q) ^ 2
/-- **Gaussian test matrices at least as wide as the rank make generalized Nyström exact**: if
$\operatorname{rank}\mathbf{A} \le \min(\ell, p)$ then $\mathsf{gn}(\mathbf{A}, \mathbf{\Omega},
\mathbf{\Psi}) = \mathbf{A}$ almost surely. No independence of the two test matrices is needed. -/
theorem ae_generalizedNystrom_eq_self_of_hasLaw_gaussianMatrix (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) (hΨ : HasLaw Ψ (gaussianMatrix m p) μ)
    (hAl : A.rank ≤ Fintype.card l) (hAp : A.rank ≤ Fintype.card p) :
    ∀ᵐ ω ∂μ, generalizedNystrom A (X ω) (Ψ ω) = A

/-- GN1 with a Haar co-range test matrix: factor
$1 + \frac{m-p}{m-q}\cdot\frac{q}{p-q-1}$. [EpperlyWebber2026, proof of Theorem 4.2].
Result: generalized-nystrom-expected-error -/
theorem integral_frobNorm_sub_generalizedNystrom_sq_of_hasLaw_haarFrame [DecidableEq p]
    (A : Matrix m n ℝ) (X₀ : Matrix n l ℝ) (hΨ : HasLaw Ψ (haarFrame m p) μ)
    (hpm : Fintype.card p ≤ Fintype.card m) (hr : (A * X₀).rank + 2 ≤ Fintype.card p) :
    ∫ ω, frobNorm (A - generalizedNystrom A X₀ (Ψ ω)) ^ 2 ∂μ =
      haarProjectionFactor (Fintype.card m) (Fintype.card p) (A * X₀).rank *
        frobNorm (A - rsvd A X₀) ^ 2
/-- GN3 with a Haar co-range test matrix, any law of $\mathbf{\Omega}$.
Result: generalized-nystrom-expected-error -/
theorem integral_frobNorm_sub_generalizedNystrom_sq_le_mul_integral_of_hasLaw_haarFrame
    [DecidableEq p] (A : Matrix m n ℝ) (hX : AEMeasurable X μ) (hΨ : HasLaw Ψ (haarFrame m p) μ)
    (hpm : Fintype.card p ≤ Fintype.card m) (hXΨ : IndepFun X Ψ μ)
    (hlp : Fintype.card l + 2 ≤ Fintype.card p) :
    ∫ ω, frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2 ∂μ ≤
      haarProjectionFactor (Fintype.card m) (Fintype.card p) (Fintype.card l) *
        ∫ ω, frobNorm (A - rsvd A (X ω)) ^ 2 ∂μ
theorem integrable_frobNorm_sub_generalizedNystrom_sq_of_hasLaw_haarFrame [DecidableEq p]
    (A : Matrix m n ℝ) (hX : AEMeasurable X μ) (hΨ : HasLaw Ψ (haarFrame m p) μ)
    (hpm : Fintype.card p ≤ Fintype.card m) (hXΨ : IndepFun X Ψ μ)
    (hr : ∀ᵐ ω ∂μ, (A * X ω).rank + 2 ≤ Fintype.card p) :
    Integrable (fun ω => frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2) μ
/-- GN5 with a Haar co-range test matrix: the factor is
$1 + \gamma\frac{\ell'}{p-\ell'-1}$ with $\gamma = \frac{m-p}{m-\ell'}$.
[EpperlyWebber2026, proof of Theorem 4.2(a), random orthonormal $\mathbf{\Psi}$].
Result: generalized-nystrom-expected-error -/
theorem integral_frobNorm_sub_generalizedNystrom_sq_eq_mul_integral_of_hasLaw_haarFrame
    [DecidableEq p] (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ)
    (hΨ : HasLaw Ψ (haarFrame m p) μ) (hpm : Fintype.card p ≤ Fintype.card m)
    (hXΨ : IndepFun X Ψ μ) (hr : min A.rank (Fintype.card l) + 2 ≤ Fintype.card p) :
    ∫ ω, frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2 ∂μ =
      haarProjectionFactor (Fintype.card m) (Fintype.card p) (min A.rank (Fintype.card l)) *
        ∫ ω, frobNorm (A - rsvd A (X ω)) ^ 2 ∂μ
/-- **The sharp upper bound for generalized Nyström, random orthonormal co-range**: GN7 with the
factor $1 + \frac{m-p}{m-\ell}\cdot\frac{\ell}{p-\ell-1}$.
[EpperlyWebber2026, Theorem 4.2(a), $\gamma = \frac{d-k}{d-\ell}$ in their letters].
Result: generalized-nystrom-expected-error -/
theorem integral_frobNorm_sub_generalizedNystrom_sq_le_of_isLeftUnitarilyInvariant_of_hasLaw_haarFrame
    [DecidableEq n] [DecidableEq p] {ν : Measure (Matrix n l ℝ)} [IsProbabilityMeasure ν]
    [IsLeftUnitarilyInvariant ν] (A : Matrix m n ℝ) (hX : HasLaw X ν μ)
    (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) (hΨ : HasLaw Ψ (haarFrame m p) μ)
    (hpm : Fintype.card p ≤ Fintype.card m) (hXΨ : IndepFun X Ψ μ)
    (hlA : Fintype.card l ≤ A.rank) (hlp : Fintype.card l + 2 ≤ Fintype.card p) {q : ℕ}
    (hq : q + 2 ≤ Fintype.card l) :
    ∫ ω, frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2 ∂μ ≤
      haarProjectionFactor (Fintype.card m) (Fintype.card p) (Fintype.card l) *
        rotationInvariantFactor A.rank (Fintype.card l) q * frobNorm (A - truncatedSVD A q) ^ 2
```

Proof routes. *GN1:* `sub_generalizedNystrom`, `sub_rsvd`, then A6 at `S := fun ω => (Ψ ω)ᴴ`
(`hasLaw_conjTranspose_of_hasLaw_gaussianMatrix`), `X := A * X₀`, `B := A`. *GN2:* common step 2: L1
on $f(\mathbf{x}, \mathbf{\psi}) = \|\mathbf{A}-\mathsf{gn}(\mathbf{A}, \mathbf{x}, \mathbf{\psi})
\|_{\mathsf{F}}^2$ (measurable by `measurable_generalizedNystrom`), the inner integral by GN1 at
$\mathbf{X}_0 = \mathbf{x}$ (for $\mathbf{x}$ in the full-measure set of `hr`), `lintegral_congr_ae`,
back to Bochner by `integral_eq_lintegral_of_nonneg_ae` on both sides (the right integrand is
bounded: $\|\mathbf{A}-\mathsf{rsvd}\| \le \|\mathbf{A}\|$ and the factor at most $g_\ell(p)$, so no
integrability hypothesis is needed). *GN3:* GN2 and `gaussianProjectionFactor_le_gaussianProjectionFactor`
(`Matrix.rank_le_card_width`), `integral_mono`. *GN4:* GN2's lintegral is finite. *GN5:* GN2 and
`ae_rank_mul_eq_min_of_hasLaw_gaussianMatrix`, `integral_congr_ae`, `integral_mul_left`. *GN6:* GN3
and S3's G2. *GN7:* GN3 and (S4-iii). *GN8:* almost surely
$\operatorname{rank}(\mathbf{A}\mathbf{X}) = \operatorname{rank}\mathbf{A}$ (so
$\operatorname{range}(\mathbf{A}\mathbf{X}) = \operatorname{range}\mathbf{A}$) and
$\operatorname{rank}(\mathbf{\Psi}^{\mathsf{H}}\mathbf{A}) = \operatorname{rank}\mathbf{A}$
(`ae_rank_conjTranspose_mul_eq_of_hasLaw_gaussianMatrix` at `Z := A`); on both events
$\operatorname{range}(\mathbf{\Psi}^{\mathsf{H}}\mathbf{A}\mathbf{X}) = \operatorname{range}
(\mathbf{\Psi}^{\mathsf{H}}\mathbf{A})$, so the two rank hypotheses of
`generalizedNystrom_eq_self_of_rank_eq` hold; no independence. *GH1 to GH5:* the same with A13 and
A4 (Haar monotonicity) in place of A6 and the Gaussian one. Degenerate: §3.0 ($\ell' = 0$: both sides
$\|\mathbf{A}\|_{\mathsf{F}}^2$ times $1$; GN7, GH5 vacuous for $\ell > n$).

### 3.5 `LowRank/Gaussian/TruncatedGeneralizedNystrom.lean`: late truncation (7)

Real, Gaussian test matrices `(hX : HasLaw X (gaussianMatrix n l) μ)`, `(hΨ : HasLaw Ψ
(gaussianMatrix m p) μ)`, `(hXΨ : IndepFun X Ψ μ)` unless stated. Labels TG1 to TG7.

```lean
/-- **The truncated generalized Nyström factor**, at present
<!-- value truncatedGNFactor k \ell p -->
$g + 4\sqrt{2kc} + 8kc$ with $g = 1 + k/(\ell-k-1)$ and $c = (25g + 484)/p$:
the multiplier of $\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$ in the expected
error of truncated generalized Nyström with Gaussian test matrices of sizes $\ell$ and $p$,
`integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_of_hasLaw_gaussianMatrix`. It tends to
$1 + \frac{k}{\ell-k-1}$ as $p/k \to \infty$, and is at most $1 + \varepsilon$ at
$\ell \ge 6k/\varepsilon$, $p \ge 8000\ell/\varepsilon$ (`truncatedGNFactor_le_one_add`). The
constants are those of this library's proof; no published statement has a value; the triangle
inequality gives at best $9$ (`IsBestRankApprox.matrixNorm_sub_le_add_two_mul`). Consumers use
`one_le_truncatedGNFactor` and `truncatedGNFactor_le_one_add`. -/
noncomputable irreducible_def truncatedGNFactor (k l p : ℕ) : ℝ :=
  gaussianProjectionFactor k l +
    4 * √(2 * k * ((25 * gaussianProjectionFactor k l + 484) / p)) +
      8 * k * ((25 * gaussianProjectionFactor k l + 484) / p)
/-- For $4k \le \ell$, with $g = 1 + k/(\ell-k-1)$ and $c = (25g + 484)/p$,
<!-- value truncatedGNFactor k \ell p -->
$1 \le g + 4\sqrt{2kc} + 8kc$ (the value of `truncatedGNFactor k l p`). -/
theorem one_le_truncatedGNFactor {k l p : ℕ} (h : 4 * k ≤ l) : 1 ≤ truncatedGNFactor k l p
/-- **The explicit comparison**: for $0 < \varepsilon \le 1$, $6k \le \varepsilon\ell$ and
$8000\,\ell \le \varepsilon p$, with $g = 1 + k/(\ell-k-1)$ and $c = (25g + 484)/p$,
<!-- value truncatedGNFactor k \ell p -->
$g + 4\sqrt{2kc} + 8kc \le 1 + \varepsilon$ (the value of `truncatedGNFactor k l p`). -/
theorem truncatedGNFactor_le_one_add {k l p : ℕ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hl : 6 * (k : ℝ) ≤ ε * l) (hp : 8000 * (l : ℝ) ≤ ε * p) :
    truncatedGNFactor k l p ≤ 1 + ε

/-- The squared Frobenius error of truncated generalized Nyström is integrable for any law of the
range test matrix independent of a Gaussian co-range test matrix, when $\ell + 2 \le p$. -/
theorem integrable_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : AEMeasurable X μ) (hΨ : HasLaw Ψ (gaussianMatrix m p) μ)
    (hXΨ : IndepFun X Ψ μ) (hlp : Fintype.card l + 2 ≤ Fintype.card p) (k : ℕ) :
    Integrable (fun ω => frobNorm (A - truncatedSVD (generalizedNystrom A (X ω) (Ψ ω)) k) ^ 2) μ
/-- **The expected error of truncated generalized Nyström**: for standard Gaussian independent
test matrices with $4k \le \ell$ and $4\ell \le p$, writing $g = 1 + \frac{k}{\ell-k-1}$ and
$c = \frac{25g + 484}{p}$, <!-- value truncatedGNFactor k \ell p -->
$$\mathbb{E}\|\mathbf{A}-\llbracket\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})
\rrbracket_k\|_{\mathsf{F}}^2 \le \bigl(g + 4\sqrt{2kc} + 8kc\bigr)
\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,,$$
the factor being `truncatedGNFactor k ℓ p`. So $(1+\varepsilon)$ relative
error at $\ell = O(k/\varepsilon)$, $p = O(k/\varepsilon^2)$ (TG6). Every rank of $\mathbf{A}$; the
truncation is `truncatedSVD`, and the bound holds for every best rank-$k$ approximation of the
output. Proved without a literature source; inputs [HalkoMartinssonTropp2011, Theorems 9.1, 10.5];
[TroppWebber2023, Lemmas B.1, B.3]; [HornJohnson2013, Theorem 7.4.1.1] (through the perturbed
truncation lemma). Comparison points: [TroppYurtseverUdellCevher2017, Corollary 6.4] (the
constant-2 triangle bound, first moment, never below $3\,\mathrm{OPT}$), the Frobenius-noise bound
`integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_sqrt_of_hasLaw_gaussianMatrix`
($(1+\varepsilon)$ only at $p = O(k/\varepsilon^3)$, better constants below $\ell \approx 10^3 k$);
[CamanoEpperlyMeyerTropp2025, Remark 2.9] concerns a different, core-truncated estimator and states
no bound. Result: tgn-expected-error -/
theorem integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ)
    (hΨ : HasLaw Ψ (gaussianMatrix m p) μ) (hXΨ : IndepFun X Ψ μ) {k : ℕ}
    (hkl : 4 * k ≤ Fintype.card l) (hlp : 4 * Fintype.card l ≤ Fintype.card p) :
    ∫ ω, frobNorm (A - truncatedSVD (generalizedNystrom A (X ω) (Ψ ω)) k) ^ 2 ∂μ ≤
      truncatedGNFactor k (Fintype.card l) (Fintype.card p) * frobNorm (A - truncatedSVD A k) ^ 2
/-- **Truncated generalized Nyström reaches relative error $1 + \varepsilon$** with
$\ell \ge 6k/\varepsilon$ and $p \ge 8000\,\ell/\varepsilon$, so $O(k/\varepsilon)$ products with
$\mathbf{A}$ and $O(k/\varepsilon^2)$ with $\mathbf{A}^{\mathsf{H}}$. Proved without a literature
source. Result: tgn-expected-error -/
theorem integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_one_add_mul_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ)
    (hΨ : HasLaw Ψ (gaussianMatrix m p) μ) (hXΨ : IndepFun X Ψ μ) {k : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hl : 6 * (k : ℝ) ≤ ε * Fintype.card l)
    (hp : 8000 * (Fintype.card l : ℝ) ≤ ε * Fintype.card p) :
    ∫ ω, frobNorm (A - truncatedSVD (generalizedNystrom A (X ω) (Ψ ω)) k) ^ 2 ∂μ ≤
      (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2
/-- **Truncated generalized Nyström, Frobenius core-noise form**: for $k + 2 \le \ell$ and
$\ell + 2 \le p$, with $g = 1 + \frac{k}{\ell-k-1}$ and $h = \frac{\ell}{p-\ell-1}$,
$$\mathbb{E}\|\mathbf{A}-\llbracket\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})
\rrbracket_k\|_{\mathsf{F}}^2 \le \bigl(g + 4\sqrt{hg} + 4hg\bigr)
\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,.$$
Incomparable with
`integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_of_hasLaw_gaussianMatrix`: milder size
conditions and better constants at practical sizes, but $(1+\varepsilon)$ only at
$p = O(k/\varepsilon^3)$. Proved without a literature source; [TroppYurtseverUdellCevher2017,
Corollary 6.4] is the published first-moment bound of this kind (constant 2, triangle inequality).
Result: tgn-expected-error -/
theorem integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_sqrt_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ)
    (hΨ : HasLaw Ψ (gaussianMatrix m p) μ) (hXΨ : IndepFun X Ψ μ) {k : ℕ}
    (hk : k + 2 ≤ Fintype.card l) (hlp : Fintype.card l + 2 ≤ Fintype.card p) :
    ∫ ω, frobNorm (A - truncatedSVD (generalizedNystrom A (X ω) (Ψ ω)) k) ^ 2 ∂μ ≤
      (gaussianProjectionFactor k (Fintype.card l) +
          4 * √((Fintype.card l : ℝ) / ((Fintype.card p : ℝ) - Fintype.card l - 1) *
            gaussianProjectionFactor k (Fintype.card l)) +
          4 * ((Fintype.card l : ℝ) / ((Fintype.card p : ℝ) - Fintype.card l - 1)) *
            gaussianProjectionFactor k (Fintype.card l)) *
        frobNorm (A - truncatedSVD A k) ^ 2
```

Proof routes. *TG2, TG3:* §3.7. *TG4:* pointwise $\|\mathbf{A}-\llbracket\mathsf{gn}\rrbracket_k
\|_{\mathsf{F}} \le 2\|\mathbf{A}-\mathsf{gn}\|_{\mathsf{F}} + \mathrm{OPT}_k$
(`IsBestRankApprox.matrixNorm_sub_le_add_two_mul` at `lpGauge 2` with
`isBestRankApprox_truncatedSVD`), squared, GN4 (with `hr` from `Matrix.rank_le_card_width`),
measurability from `measurable_truncatedSVD` composed with `measurable_generalizedNystrom`,
`Integrable.mono'`. *TG5* (the assembly; about 150 lines, split into a private residual lemma and a
private noise lemma, CONTRIBUTING §7's 80-line rule):
1. *Branches.* $k = 0$: both sides $\|\mathbf{A}\|_{\mathsf{F}}^2$ up to the factor (TG2).
   $\operatorname{rank}\mathbf{A} \le \ell$: GN8 ($\operatorname{rank}\mathbf{A} \le \ell \le p$) gives
   $\llbracket\mathsf{gn}\rrbracket_k = \llbracket\mathbf{A}\rrbracket_k$ almost surely, so the left side
   is $\mathrm{OPT}_k^2$, and TG2 closes. Otherwise $k \ge 1$, $\ell \ge 4$, $\operatorname{rank}\mathbf{A}
   > \ell$, and $\operatorname{rank}(\mathbf{A}\mathbf{X}) = \ell$ almost surely.
2. *Pointwise.* On the event $\operatorname{rank}(\mathbf{\Psi}^{\mathsf{H}}\mathbf{A}\mathbf{X}) = \ell$
   (common steps 2 and 3, using independence), T11 gives, with $\varphi = \|\mathbf{A}-\mathsf{rsvd}
   \|_{\mathsf{F}}$, $\gamma = \|\mathsf{rsvd}-\llbracket\mathsf{rsvd}\rrbracket_k\|_{\mathsf{F}}$ and
   $e = \|\mathbf{\Pi}_{\mathbf{A}\mathbf{X},\mathbf{\Psi}^{\mathsf{H}}}(\mathbf{A}-\mathsf{rsvd})\|_2$,
   $\|\mathbf{A}-\llbracket\mathsf{gn}\rrbracket_k\|_{\mathsf{F}}^2 \le \varphi^2 + \gamma^2 +
   4\sqrt{2k}\,\gamma e + 8ke^2$, with $\gamma \le \mathrm{OPT}_k$ (`frobNorm_rsvd_sub_truncatedSVD_le`)
   and $\varphi^2 + \gamma^2 = \|\mathbf{A}-\llbracket\mathsf{rsvd}\rrbracket_k\|_{\mathsf{F}}^2$ (T3).
3. *Expectations.* $\mathbb{E}(\varphi^2+\gamma^2) \le g\,\mathrm{OPT}_k^2$ (S3's U1);
   $\mathbb{E}e^2 \le c\,\mathrm{OPT}_k^2$ with $c = (25g + 484)/p$ (§3.7: A11 conditionally on
   $\mathbf{X}$ at rank $\ell$, then S3's G2 and the private residual lemma
   $\mathbb{E}\|\mathbf{A}-\mathsf{rsvd}\|_2^2 \le \frac{121}{\ell}\mathrm{OPT}_k^2$ from D1 at
   $\lceil\ell/2\rceil$ and the tail flattening); $\mathbb{E}[\gamma e] \le \mathrm{OPT}_k
   \sqrt{\mathbb{E}e^2}$ (Cauchy–Schwarz, `integral_mul_le_Lp_mul_Lq_of_nonneg`). Sum:
   $g + 4\sqrt{2kc} + 8kc$, which is `truncatedGNFactor_def`.

*TG6:* TG5 (its hypotheses follow: $4k \le 6k \le \varepsilon\ell \le \ell$ and
$4\ell \le 8000\ell/\varepsilon \le p$) and TG3,
`mul_le_mul_of_nonneg_right`. *TG7:* the branches of TG5 are not needed. T10 with
$\|\llbracket\mathbf{N}\rrbracket_{2k}\|_{\mathsf{F}} \le \|\mathbf{N}\|_{\mathsf{F}}$
(`frobNorm_truncatedSVD_sq` and the tail sum), expand
$(\gamma + 2\|\mathbf{N}\|_{\mathsf{F}})^2$; $\mathbb{E}\|\mathbf{N}\|_{\mathsf{F}}^2 =
\mathbb{E}[(g_{q}(p) - 1)\varphi^2] \le h\,\mathbb{E}\varphi^2 \le hg\,\mathrm{OPT}_k^2$ (GN2's
conditional identity for the excess, A6's split, `gaussianProjectionFactor_le_gaussianProjectionFactor`,
G2); Cauchy–Schwarz for the cross term; U1 for $\varphi^2 + \gamma^2$. Degenerate: §3.0; TG7 at
$k = 0$ is $\|\mathbf{A}\|_{\mathsf{F}}^2 \le (1 + 4\sqrt h + 4h)\|\mathbf{A}\|_{\mathsf{F}}^2$, true.

### 3.6 `LowRank/Gaussian/TruncatedGeneralizedNystrom.lean`: early truncation (6)

Labels ET1 to ET6. `X` of any law where stated (`hX : AEMeasurable X μ`).

```lean
/-- **Early-truncated generalized Nyström conditionally on the range test matrix**: for a fixed
$\mathbf{\Omega}$, a standard Gaussian $\mathbf{\Psi}$, $q = \operatorname{rank}\llbracket
\mathbf{A}\mathbf{\Omega}\rrbracket_k \le k$ and $k + 2 \le p$,
$$\mathbb{E}_{\mathbf{\Psi}}\|\mathbf{A}-\mathsf{earlyTruncatedGN}(\mathbf{A}, \mathbf{\Omega},
\mathbf{\Psi}, k)\|_{\mathsf{F}}^2 = \Bigl(1 + \frac{q}{p-q-1}\Bigr)\|\mathbf{A}-
\mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)\|_{\mathsf{F}}^2\,,$$
the factor at the actual rank $q$. Proved without a literature source, as a composition: the
completion step is [EpperlyWebber2026, Theorem 2.1]; the algorithm is
[TroppYurtseverUdellCevher2017, §7.3.1, (7.3)]. Result: etgn -/
theorem integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (X₀ : Matrix n l ℝ) (hΨ : HasLaw Ψ (gaussianMatrix m p) μ) {k : ℕ}
    (hkp : k + 2 ≤ Fintype.card p) :
    ∫ ω, frobNorm (A - earlyTruncatedGeneralizedNystrom A X₀ (Ψ ω) k) ^ 2 ∂μ =
      gaussianProjectionFactor (truncatedSVD (A * X₀) k).rank (Fintype.card p) *
        frobNorm (A - earlyTruncatedRSVD A X₀ k) ^ 2
/-- ET1 with a Haar co-range test matrix. Result: etgn -/
theorem integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_of_hasLaw_haarFrame
    [DecidableEq p] (A : Matrix m n ℝ) (X₀ : Matrix n l ℝ) (hΨ : HasLaw Ψ (haarFrame m p) μ)
    (hpm : Fintype.card p ≤ Fintype.card m) {k : ℕ} (hkp : k + 2 ≤ Fintype.card p) :
    ∫ ω, frobNorm (A - earlyTruncatedGeneralizedNystrom A X₀ (Ψ ω) k) ^ 2 ∂μ =
      haarProjectionFactor (Fintype.card m) (Fintype.card p) (truncatedSVD (A * X₀) k).rank *
        frobNorm (A - earlyTruncatedRSVD A X₀ k) ^ 2
/-- **Early-truncated generalized Nyström = early-truncated randomized SVD × completion**: for any
law of $\mathbf{\Omega}$ independent of a standard Gaussian $\mathbf{\Psi}$ and $k + 2 \le p$,
$$\mathbb{E}\|\mathbf{A}-\mathsf{earlyTruncatedGN}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi}, k)
\|_{\mathsf{F}}^2 \le \Bigl(1 + \frac{k}{p-k-1}\Bigr)\,\mathbb{E}\|\mathbf{A}-
\mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)\|_{\mathsf{F}}^2\,.$$
Every bound on the early-truncated randomized SVD (the subspace-embedding and PCP routes, and its
expectation at $\ell = O(k/\varepsilon^2)$ once proved) becomes one on early-truncated generalized
Nyström with $p = O(k/\varepsilon)$. Proved without a literature source, as a composition:
[EpperlyWebber2026, Theorem 2.1] for the completion; the algorithm is
[TroppYurtseverUdellCevher2017, §7.3.1, (7.3)]. Result: etgn -/
theorem integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_le_mul_integral_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : AEMeasurable X μ) (hΨ : HasLaw Ψ (gaussianMatrix m p) μ)
    (hXΨ : IndepFun X Ψ μ) {k : ℕ} (hkp : k + 2 ≤ Fintype.card p) :
    ∫ ω, frobNorm (A - earlyTruncatedGeneralizedNystrom A (X ω) (Ψ ω) k) ^ 2 ∂μ ≤
      gaussianProjectionFactor k (Fintype.card p) *
        ∫ ω, frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 ∂μ
theorem integrable_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : AEMeasurable X μ) (hΨ : HasLaw Ψ (gaussianMatrix m p) μ)
    (hXΨ : IndepFun X Ψ μ) {k : ℕ} (hkp : k + 2 ≤ Fintype.card p) :
    Integrable (fun ω => frobNorm (A - earlyTruncatedGeneralizedNystrom A (X ω) (Ψ ω) k) ^ 2) μ
/-- ET3 with a Haar co-range test matrix: factor $1 + \frac{m-p}{m-k}\cdot\frac{k}{p-k-1}$.
Result: etgn -/
theorem integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_le_mul_integral_of_hasLaw_haarFrame
    [DecidableEq p] (A : Matrix m n ℝ) (hX : AEMeasurable X μ) (hΨ : HasLaw Ψ (haarFrame m p) μ)
    (hpm : Fintype.card p ≤ Fintype.card m) (hXΨ : IndepFun X Ψ μ) {k : ℕ}
    (hkp : k + 2 ≤ Fintype.card p) :
    ∫ ω, frobNorm (A - earlyTruncatedGeneralizedNystrom A (X ω) (Ψ ω) k) ^ 2 ∂μ ≤
      haarProjectionFactor (Fintype.card m) (Fintype.card p) k *
        ∫ ω, frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 ∂μ
/-- **Early-truncated generalized Nyström reaches relative error $1 + \varepsilon$ with
$p = O(k/\varepsilon)$**: if the early-truncated randomized SVD with the same $\mathbf{\Omega}$ has
expected error at most $(1 + \varepsilon/2)\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k
\|_{\mathsf{F}}^2$ and $p \ge k + 1 + (2+\varepsilon)k/\varepsilon$, then
$$\mathbb{E}\|\mathbf{A}-\mathsf{earlyTruncatedGN}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi}, k)
\|_{\mathsf{F}}^2 \le (1+\varepsilon)\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,.$$
The hypothesis holds for a Gaussian $\mathbf{\Omega}$ with $\ell = O(k/\varepsilon^2)$ columns; that
theorem is not yet in the library, so the hypothesis is explicit. Proved without a literature
source. Result: etgn -/
theorem integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_le_one_add_mul_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : AEMeasurable X μ) (hΨ : HasLaw Ψ (gaussianMatrix m p) μ)
    (hXΨ : IndepFun X Ψ μ) {k : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hp : (k : ℝ) + 1 + (2 + ε) * k / ε ≤ Fintype.card p)
    (hRSVD : ∫ ω, frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 ∂μ ≤
      (1 + ε / 2) * frobNorm (A - truncatedSVD A k) ^ 2) :
    ∫ ω, frobNorm (A - earlyTruncatedGeneralizedNystrom A (X ω) (Ψ ω) k) ^ 2 ∂μ ≤
      (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2
```

Proof routes. *ET1:* `sub_earlyTruncatedGeneralizedNystrom`, `sub_earlyTruncatedRSVD`, then A6 at
`X := truncatedSVD (A * X₀) k` (rank at most $k$, `rank_truncatedSVD_le`, so `hX` from `hkp`),
`B := A`; the right side is E8's first term. *ET2:* A13 likewise. *ET3, ET4:* common step 2 with L3
and L2, ET1 inside, and `gaussianProjectionFactor_le_gaussianProjectionFactor` at $q \le k$; the right
integrand is bounded by $\|\mathbf{A}\|_{\mathsf{F}}^2$, so ET4 follows from the finite lintegral.
*ET5:* ET2 and A4. *ET6:* $k = 0$: both outputs are $\mathbf{0}$ and the claim is
$\|\mathbf{A}\|_{\mathsf{F}}^2 \le (1+\varepsilon)\|\mathbf{A}\|_{\mathsf{F}}^2$. $k \ge 1$: `hp` gives
$k + 2 \le p$ and $\frac{k}{p-k-1} \le \frac{\varepsilon}{2+\varepsilon}$; ET3, `hRSVD` and
$(1+\frac{\varepsilon}{2})(1+\frac{\varepsilon}{2+\varepsilon}) = 1+\varepsilon$ (`field_simp`, `ring`).
Degenerate: §3.0.

**The $\varepsilon^{-2}$ statement, exactly.** The maintainer's early-truncated GN theorem reads,
in the library: for every law of $\mathbf{\Omega}$ independent of a standard Gaussian
$\mathbf{\Psi}$ with $k + 2 \le p$, $\mathbb{E}\|\mathbf{A}-\mathsf{earlyTruncatedGN}\|_{\mathsf{F}}^2
\le (1 + \frac{k}{p-k-1})\,\mathbb{E}\|\mathbf{A}-\mathsf{earlyTruncatedRSVD}\|_{\mathsf{F}}^2$ (ET3,
the primary statement), with ET1 its conditional identity and ET6 the $(1+\varepsilon)$ form at
$p \ge k + 1 + (2+\varepsilon)k/\varepsilon$. The notes' $(1+\eta)\mathrm{OPT}^2$ at
$\ell \ge 900k/\eta^2$ for the early-truncated RSVD is the hypothesis `hRSVD` at $\eta = \varepsilon/2$
(their $\ell \ge 3600k/\varepsilon^2$); it becomes a theorem when brief §8's deferral is lifted, and
ET6 then has an unconditional corollary of one line. Meanwhile ET3 composes with S7's and S9's
early-truncated RSVD tails (OSE plus AMM, uniform PCP) into tails for early-truncated GN.

### 3.7 The arithmetic of `truncatedGNFactor`

Constants, with $\beta(r, k)$ = `gaussianPinvSpecNormBound r k` $= \frac{e}{k-r}\sqrt{(k+r-1)/2}$:
- **Core noise** (A11 at rank $\ell$, $p \ge 4\ell$, $\ell \ge 1$): $p + \ell - 1 \le \frac54 p$ and
  $p - \ell \ge \frac34 p$ give $\beta(\ell, p)^2 \le \frac{10e^2}{9p} \le \frac{8.21}{p}$; and
  $\frac{\ell}{p-\ell-1} \le \frac{2\ell}{p}$ since $p \ge 2\ell + 2$. With
  $(a\sqrt h + b\beta)^2 + a^2\beta^2 \le 2a^2h + 3b^2\beta^2$ ($a = \|\mathbf{E}\|_2 \le
  b = \|\mathbf{E}\|_{\mathsf{F}}$): $\mathbb{E}e^2 \le \frac{4\ell}{p}\mathbb{E}\|\mathbf{A}-
  \mathsf{rsvd}\|_2^2 + \frac{25}{p}\mathbb{E}\|\mathbf{A}-\mathsf{rsvd}\|_{\mathsf{F}}^2$
  ($3 \times 8.21 \le 25$; checked numerically over $1 \le \ell \le 300$, $4\ell \le p \le 4\ell + 400$:
  maximum $24.62$).
- **Spectral residual** (D1 at $j = \lceil\ell/2\rceil$, $4k \le \ell$, $\ell \ge 4$): $j - k \ge \ell/4$,
  so the tail flattening gives $\sigma_j^2 \le \frac{4}{\ell}\mathrm{OPT}_k^2$; $\|\mathbf{A}-
  \llbracket\mathbf{A}\rrbracket_j\|_{\mathsf{F}} \le \mathrm{OPT}_k$; $\frac{j}{\ell-j-1} \le 3$ (worst
  $\ell = 5$); $\ell\,\beta(j,\ell)^2 \le 32.4$ (worst $\ell = 5$, $32.33$). D1 gives
  $\mathbb{E}\|\mathbf{A}-\mathsf{rsvd}\|_2^2 \le \frac{1}{\ell}\bigl(4 + (\sqrt{12} + \sqrt{32.4})^2 +
  4 \cdot 8.1\bigr)\mathrm{OPT}_k^2 \le \frac{121}{\ell}\mathrm{OPT}_k^2$ (the exact supremum over
  $\ell \ge 4$ of the left coefficient is $113.6$, at $\ell = 5$).
- **Noise constant:** $\mathbb{E}e^2 \le \frac{4\ell}{p}\cdot\frac{121}{\ell}\mathrm{OPT}_k^2 +
  \frac{25}{p}g\,\mathrm{OPT}_k^2 = c\,\mathrm{OPT}_k^2$, $c = (25g + 484)/p$, by S3's G2
  ($\mathbb{E}\varphi^2 \le g\,\mathrm{OPT}_k^2$).
- **TG2:** $g \ge 1$ for $k = 0$ or $\ell \ge k + 2$ (here $\ell \ge 4k \ge k + 3$ when $k \ge 1$), and
  the other two terms are nonnegative.
- **TG3:** for $k \ge 1$, $\ell - k - 1 \ge 6k/\varepsilon - 2k \ge 4k/\varepsilon$, so
  $g \le 1 + \varepsilon/4 \le \frac54$, $c \le 515.25/p$ and $k/p \le \varepsilon^2/48000$; then
  $4\sqrt{2kc} \le 52.5\,\varepsilon/\sqrt{8000} \le 0.587\,\varepsilon$ and $8kc \le
  687\,\varepsilon^2/8000 \le 0.086\,\varepsilon$, total $g + \dots \le 1 + 0.922\,\varepsilon$ (checked
  numerically at $k \in \{1, \dots, 200\}$, $\varepsilon \in [0.01, 1]$: worst $0.922$). For $k = 0$ the
  factor is $1$.

These replace the brief's $c = (18g + 408)/p$ (TW's sharp second moment: $2\beta^2 \le 16.4/p$ and
$102/\ell$) and the notes' $12500$; Q2, Q3.

## 4. Files

| # | File | Statements | Lines (est.) | Imports (new) | Depends on |
|---|---|---|---|---|---|
| 1 | `ForMathlib/Probability/Independence/Basic.lean` (registered; side file `ForMathlib/Probability/Independence/Tonelli.lean` until proved) | 1 (L1) | +30 | Mathlib `Probability.Independence.Basic`, `MeasureTheory.Constructions.Prod.Integral` if not transitive | none |
| 2 | `Probability/Measurability/Matrix.lean` (registered; side file `Probability/Measurability/EarlyTruncation.lean`) | 2 (L2, L3) | +25 | none | none |
| 3 | `Matrix/Pseudoinverse/LeastSquares.lean` (registered; side file `Matrix/Pseudoinverse/SketchAndSolveSmul.lean`) | 1 (L4) | +12 | none | none |
| 4 | `RandomMatrix/Gaussian/SpectralNorm.lean` (registered; side file `RandomMatrix/Gaussian/SpectralNormSq.lean`) | 3 (L5 to L7) | +90 | `Probability/SubGaussian/Basic` if not transitive | file 1 |
| 5 | `RandomMatrix/Gaussian/BlockMoments.lean` (registered; side file `RandomMatrix/Gaussian/BlockMomentsSpectral.lean`) | 4 (L8 to L11) | +130 | `RandomMatrix/Gaussian/SpectralNorm` | file 4 |
| 6 | S4's Haar block file (provisionally `RandomMatrix/Haar/Blocks.lean`) | 2 (L12, L13) | +90 | S4's | S4 (S4-i, S4-ii) |
| 7 | `Sketching/Gaussian/LeastSquares.lean` (new) | 17 (A1 to A17) | 600 | `Sketching/Gaussian/Haar`, `Matrix/Pseudoinverse/LeastSquares`, `Matrix/Subspaces/ObliqueProjector`, `RandomMatrix/Gaussian/BlockMoments`, file 6 | files 1, 5, 6 |
| 8 | `LowRank/Gaussian/RangeFinder.lean` (registered, S3; side file `LowRank/Gaussian/RangeFinderSpectral.lean`) | 1 (D1) | +50 | none | file 5 |
| 9 | `LowRank/Gaussian/GeneralizedNystrom.lean` (new) | 13 (GN1 to GN8, GH1 to GH5) | 520 | file 7, `LowRank/Gaussian/RangeFinder`, `LowRank/Gaussian/RotationInvariant` (for `rotationInvariantFactor` and S4's EW 3.2), `Probability/Measurability/Matrix` | files 1, 7; S4 for GN7, GH5 |
| 10 | `LowRank/Gaussian/TruncatedGeneralizedNystrom.lean` (new) | 13 (TG1 to TG7, ET1 to ET6) | 650 | file 9, `LowRank/Structural/Truncation`, `Matrix/Factorizations/SketchedLowRank` | files 2, 7, 8, 9 |

S6 is about 2200 lines and 57 public declarations (two definitions, 55 theorems): 17, 13 and 13 in
the three new files, 14 added to lower layers. Every file stays under 1000 lines and 25 statements.
The split is by topic: sketched least squares with Gaussian and Haar sketches (a Sketching topic,
D8; Solvers imports it), generalized Nyström in expectation, and its truncations, late and early (Q6).

**Order.** Files 1 to 5 are independent of each other except 4 after 1 and 5 after 4. The
**Gaussian half** (files 1 to 5, 8, the Gaussian statements of 7, 9, 10) does not depend on S4 and
goes first. The **Haar half** (file 6; A13 to A17; GH1 to GH5; ET2, ET5) and GN7 wait for S4's
(S4-i), (S4-ii) and (S4-iii). Within file 7 the Haar statements are the last section, so the file is
first written with the Gaussian section only and extended after S4; the same for files 9 and 10
(Q7). Files 9 and 10 can be given to one proof agent after 7 (a short import chain, CONTRIBUTING §11).

**Placement** (CONTRIBUTING §8 item 5): every addition outside files 7, 9, 10, with its home and
reason.
- L1, `ForMathlib/Probability/Independence/Basic.lean`: a fact about independent random variables
  with no NLAlib vocabulary, in Mathlib's namespace, an upstream candidate.
- L2, L3, `Probability/Measurability/Matrix.lean`: measurability of named outputs lives there,
  beside S2c's `measurable_rsvd` and `measurable_generalizedNystrom`.
- L4, `Matrix/Pseudoinverse/LeastSquares.lean`: a deterministic fact about `sketchAndSolve`, beside
  its definition.
- L5 to L7, `RandomMatrix/Gaussian/SpectralNorm.lean`: spectral moments of Gaussian products, beside
  Chevet's inequality, whose second-moment form they are.
- L8 to L11, `RandomMatrix/Gaussian/BlockMoments.lean`: the second spectral moments of the blocks
  whose Frobenius moments and first spectral moment live there.
- L12, L13, S4's Haar block file: EW Proposition 5.7 is a Haar block identity, beside the block laws
  and the trace mean it is proved from. If S4 places (S4-i) elsewhere (e.g. `RandomMatrix/Haar/Moments.lean`),
  L12 and L13 go with it.
- D1, `LowRank/Gaussian/RangeFinder.lean`: a range-finder expectation, beside S3's G4 and G5.
- `haarProjectionFactor` (A1), in file 7 itself: the Haar sketch-and-solve factor; listed because
  S3 §1 anticipated a home and did not fix one.
- **Flags** (placed elsewhere until the wrap-up): each registered home (files 1 to 5, 8) takes its
  statements only proved; until then they sit in the side files of the table, each saying it merges
  into its home. D1's proof uses S3's private exact-branch lemma (`card n < k`); the side file
  restates it privately and the duplicate is removed at the merge (or S3's lemma is made public,
  the reviewer's choice). File 6 is S4's; if S4's note names no such file, L12 and L13 go to a side
  file `RandomMatrix/Haar/SketchingIdentity.lean`, flagged with the home S4 fixes. No other flag.

## 5. Material

**Prototype** (read-only, `~/Documents/prove2me/lean/NLAlib/LowRank/Nystrom/`; ledger dispositions):
- `SketchedRegression.lean` (`sketchedCore`, `sketchedOutput`, `coreNoise`, `sketch_decomp`,
  `error_decomp`, `frobSq_error`, `coreNoise_eq`, `specNorm_transpose_mul_residual`, …): already
  replaced by S0's `obliqueProjector`, `sketchAndSolve`, the split and the core-noise form (S0 §5);
  nothing for S6 beyond the cut confirmed. The `Fin`-indexed complement frame and the hypothesis
  `Q * Qᵀ + Qp * Qpᵀ = 1` are not reproduced: the basis step is proof-internal (§3.0).
- `GeneralizedNystrom.lean`: `completion_reduction` → A6 (the Gaussian facts that were hypotheses,
  `hG₁`, `hG₂`, `hG₁m`, `hGi`, are now proved from R1 and R4); `gn_main`, `gn_main_of_completion` →
  GN3, GN6 (the SVD blocks `U₁, S₁, V₁, …`, `hinv`, `hcond`, `hYi`, `hZi` are not reproduced; the
  prototype's "trust boundary" is closed).
- `GaussianNystrom.lean`: `integrable_and_integral_frobSq_sub_sketchedOutput_le_rank_factor_gaussian`
  → GN2 and GN4 (split, D4: an `∧` of integrability and bound is two statements); `gn_main_gaussian`
  → GN6.
- `RawGaussianNystrom.lean`: `ae_rawGeneralizedNystrom_eq_self_of_rank_le` → GN8 (same hypotheses,
  no independence, as the prototype noted); `integrable_and_integral_frobSq_rawGeneralizedNystrom_le_bestRankFrobSq`
  → GN5 and GN6 (its `min A.rank t` survives in GN5); `measurableSet_hasOrthonormalCols_of_entries`,
  `ae_isUnit_gaussian_compression_of_indep`, `sketchedOutput_eq_of_projector_eq`, the
  `…_of_exact_rank_frame` and `…_of_sketch_cols_le_rank` variants: cut (the library's a.s. rank
  lemmas and the projector carrier replace the measurable random frame; D1).
- `RawNystromBridge.lean`: S0's (four representations collapsed).

**The maintainer's notes** (never cited, D13): `main.tex` (`lem:moments`, `lem:invmom`,
`lem:completion`, `thm:GN`), `tGN_replacement.tex` (`thm:tGN`, `lem:tGN-perturb` already S2a's B18,
`lem:tGN-core` → A11, `lem:tGN-residual` → D1 and TG5's private residual step, `lem:tGN-baseline` →
U1 and T12, the assembly → TG5), `GN_truncated.tex` (the remark on the exponent: TG7 is the
$k/\varepsilon^3$ route it describes), `pcps-et-audited.tex` (`thm:etGN` → ET1, ET3, ET6; `thm:etRSVD`
deferred). The formalization `formal/LRA/Probability/Assembly.lean` (`gn_assembly`, `tGN_assembly`,
`etGN_size_condition`, `etGN_identity`) is arithmetic with expectations as hypotheses: proof material
for TG5's step 3, TG3 and ET6's identity, not ported as statements. The notes' constants ($444/s$,
$102/t$, $12500$) are not the library's (§3.7).

**Literature** (§0's checks). Citations; keys in `docs/references.bib`: `EpperlyWebber2026`,
`TroppYurtseverUdellCevher2017`, `TroppWebber2023`, `CamanoEpperlyMeyerTropp2025`,
`HalkoMartinssonTropp2011`, `HornJohnson2013`; no new key (Bartan and Pilanci 2020 is named in A8's
docstring without a key, as EW's attribution; Q10).

| statement | citation | relation to the printed statement |
|---|---|---|
| A6, A13 | [EpperlyWebber2026, Theorem 2.1 and Lemma 5.1]; [TroppYurtseverUdellCevher2017, Lemma A.5] | any basis of any rank, not only $\mathbf{A}$ or an orthonormal $\mathbf{Q}$ |
| A8, A15 | [EpperlyWebber2026, Theorem 2.1] | real, $\alpha = 1$ |
| A9, A16 | [EpperlyWebber2026, Theorem 2.1]; [TroppYurtseverUdellCevher2017, Lemma A.5] | Gaussian at $r + 1 \le p$, there $r + 2 \le p$ |
| A11 | proved without a literature source; inputs [TroppWebber2023, Lemmas B.1, B.3]; algebra [EpperlyWebber2026, Lemma 5.1], [TroppYurtseverUdellCevher2017, Lemma A.4] | |
| A5 | [EpperlyWebber2026, §2.1] | the comparison stated there in words |
| L6, L7 | [TroppWebber2023, Lemma B.1]; [HalkoMartinssonTropp2011, Proposition 10.3] | an extra variance term |
| L9, L11 | [HalkoMartinssonTropp2011, proof of Theorem 10.6]; [TroppWebber2023, Lemmas B.1, B.3] | second moment |
| L13 | [EpperlyWebber2026, Proposition 5.7] | at $\mathbf{R} = \mathbf{I}$, an equality |
| D1 | [HalkoMartinssonTropp2011, Theorem 10.6] | second moment; proved without a literature source in this form |
| GN1 to GN5, GH1 to GH4 | [EpperlyWebber2026, proof of Theorem 4.2]; [TroppYurtseverUdellCevher2017, Lemmas A.3, A.5, §A.3.4]; GN3 also [CamanoEpperlyMeyerTropp2025, proof of Corollary 2.8] | identity form; any law of $\mathbf{\Omega}$ |
| GN6 | [TroppYurtseverUdellCevher2017, Theorem 4.3] | one comparison rank (rule 5) |
| GN7, GH5 | [EpperlyWebber2026, Theorem 4.2(a)] | $\operatorname{rank}\mathbf{A} \ge \ell$ in place of $\ge p$; one $q$ |
| GN8 | helper, no citation | |
| TG5, TG6, TG7 | proved without a literature source; inputs as in TG5's docstring; comparison points [TroppYurtseverUdellCevher2017, Corollary 6.4], [CamanoEpperlyMeyerTropp2025, Remark 2.9] (a different estimator) | |
| ET1 to ET6 | proved without a literature source, as a composition; [EpperlyWebber2026, Theorem 2.1] for the completion; algorithm [TroppYurtseverUdellCevher2017, §7.3.1, (7.3)] | |
| L1 to L5, L8, L10, L12, A1 to A4, A7, A10, A12, A14, A17, GN4, GH3, TG1 to TG4, ET4 | helpers or definitions, no citation | |

**Result ids** (D11; checked against `NLAlib/` and `explore/results.toml`, which has no entry for any
of them): `sketch-and-solve-expected-error` (new: A6, A8, A9, A13, A15, A16), `haar-sketching-identity`
(new: L13), `generalized-nystrom-expected-error` (new, brief D11: GN1 to GN3, GN5 to GN7, GH1, GH2,
GH4, GH5), `tgn-expected-error` (the atlas candidate: TG5 to TG7), `etgn` (the atlas candidate: ET1 to
ET3, ET5, ET6); L6 joins `chevet-inequality`, D1 joins `randomized-svd-average-spectral-error`
(HMT 10.6's id). A11 carries none (a step).

## 6. Cut, and why

- *Truncated GN with a Haar co-range test matrix*: needs a Haar spectral core noise
  ($\mathbb{E}\|(\mathbf{Q}^{\mathsf{H}}\mathbf{V}_1)^{+}\mathbf{Q}^{\mathsf{H}}\mathbf{V}_2\mathbf{B}\|_2^2$),
  for which neither the library nor EW has a route (the conjugation average gives the Frobenius
  moment only). TG7's Haar twin is cheap (A13, L12) and additive; TG5's is not.
- *Rotation-invariant co-range test matrices other than Gaussian and Haar*: the oblique projector
  depends on $\mathbf{\Psi}\mathbf{\Psi}^{\mathsf{H}}$, not only on $\operatorname{range}\mathbf{\Psi}$
  (S0's `obliqueProjector` docstring); EW Proposition 5.7 for general $\mathbf{R}$ is an inequality
  in the wrong direction for an upper bound (S10).
- *Tails of GN and truncated GN with Gaussian sketches*: CEMT Corollary 2.8's Gaussian instance comes
  from S7's OSI route with the Gaussian OSI corollary; an expectation-to-tail Markov step adds
  nothing.
- *The minimum over the comparison rank* (TYUC Theorem 4.3, EW Theorem 4.2(a)): rule 5, as S3, S5.
- *Spectral-norm GN bounds*: impossible in relative form for one-pass methods (MT Remark 15.4; brief
  D4's table).
- *GN in every unitarily invariant norm*: the completion identity is a Frobenius (trace) identity;
  the Gram-form gauge bound of the split (S0) has no Gaussian expectation with a source constant.
- *Sample-size forms beyond TG6 and ET6* (GN at $\ell = O(k/\varepsilon)$, $p = O(\ell/\varepsilon)$):
  parameter choices in GN6; no consumer.
- *TYUC Corollary 6.4 as stated* (first moment, constant 2): dominated by TG7 except when $p$ is
  within a constant of $\ell$; named in TG5's and TG7's docstrings. Additive (rule 4) if a user wants
  the first-moment form.
- *An integrability companion for the residual forms A8, A15*: their integrands are A6's and A13's
  after `mul_sketchAndSolve`; the docstrings say so (D4 is met by A7, A14).
- *Haar integrability companion of ET5*: from GH3 at the truncated sketch in three lines; additive.
- *Woodruff Theorem 47's core-truncated GN* (CEMT Remark 2.9's estimator): D15's caution, S2a and S7.
- *Complex laws* ($\alpha_{\mathbb{C}} = 0$): D3, S8.

## 7. Questions and decisions

Hard-to-reverse items are marked **(hard)**. Under the round's approval rule the maintainer decides
the hard ones; the rest proceed as recommended and are recorded here.

**Q1. Orientation and law spelling of the sketch-and-solve statements (hard).** Options: (a) the
Sketching round's spelling in `Sketching/Gaussian/LeastSquares.lean`: a Gaussian sketch
`S : Ω → Matrix p m ℝ` with `HasLaw S (gaussianMatrix p m) μ`, a Haar frame `Q : Ω → Matrix m p ℝ`
used as $\mathbf{Q}^{\mathsf{H}}$ (as `Sketching/Gaussian/Haar.lean`), unscaled; GN keeps D2's test
matrix $\mathbf{\Psi}$ and bridges with `hasLaw_conjTranspose_of_hasLaw_gaussianMatrix` (one term);
(b) D2's test-matrix spelling everywhere, `Ψ : Ω → Matrix m p ℝ` and `sketchAndSolve A (Ψ ω)ᴴ B`;
(c) the scaled sketches of the Sketching round ($\lvert p\rvert^{-1/2}\mathbf{G}$,
$\sqrt{m/p}\,\mathbf{Q}^{\mathsf{H}}$). Recommendation (a): D14 put the sketch on the left in
`obliqueProjector` and `sketchAndSolve`, so the Sketching file reads `obliqueProjector X (S ω)` with no
`conjTranspose_conjTranspose`, matching `IsSubspaceInjection.frobNorm_sub_mul_pinv_mul_sq_le` and the
Sketching round's Gaussian files; scaling is irrelevant (`obliqueProjector_smul_right`, L4), and (c)
would add a constant to every statement. Rework if reversed: every signature of file 7 and the
bridge step of GN1, GH1, ET1, ET2.

**Q2. `truncatedGNFactor` (hard: a name and arity S7 will mirror).** Options: (a) as §1: arity
`(k l p : ℕ)`, an `irreducible_def` with the proof's body $g + 4\sqrt{2kc} + 8kc$,
$c = (25g + 484)/p$, registered, API TG2 and TG3 ($\ell \ge 6k/\varepsilon$,
$p \ge 8000\ell/\varepsilon$); (b) the brief's body with $(18g + 408)/p$, which needs TW's sharp second
moment (Q3 (b)); (c) no name, the expression inline in TG5. Recommendation (a): rule 2 requires a
name for a proof constant; (b) waits for infrastructure the library lacks and changes only the body
later; (c) repeats a three-term expression in TG5, TG6 and any S7 twin. Rework if reversed: the name
in TG5, TG6 and S7's twin; the body and TG3's numbers are free to change.

**Q3. The second spectral moment of a Gaussian product (not hard).** Options: (a) Gaussian
concentration, L6 with the extra term $\|\mathbf{S}\|_2^2\|\mathbf{T}\|_2^2$, about 40 lines from
`HasSubgaussianMGF.integral_sq_le`; (b) TW Lemma B.1's form without it, through a second-moment
Slepian comparison (TW's proof via $\mathbb{E}|\max|^p$ with equal variances), new Probability
infrastructure of a few hundred lines; (c) only the Frobenius core noise, giving up the
$\varepsilon^{-2}$ rate of truncated GN. Recommendation (a): the extra term is of lower order
($\le \|\mathbf{S}\|_2^2\|\mathbf{T}\|_{\mathsf{F}}^2$), it costs $25/p$ in place of about $17/p$ in
the core noise and $121$ in place of about $102$ in the residual, and every downstream constant sits
in `truncatedGNFactor`. (b) later is a new theorem dominating L6 (rule 6: L6 reproved from it) and
a body change of the factor.

**Q4. The form of the early-truncated GN statement (not hard).** The maintainer made the
$\varepsilon^{-2}$ bound primary; its range-finder half (early-truncated RSVD in expectation at
$\ell = O(k/\varepsilon^2)$) is deferred (brief §8). Options: (a) ET3, the composition with the
early-truncated RSVD expectation on the right, as primary, ET1 its conditional identity, ET6 the
$(1+\varepsilon)$ form with the early-truncated RSVD bound as hypothesis `hRSVD`; (b) also the
unconditional $(1+\varepsilon)$ theorem at $\ell \ge 3600k/\varepsilon^2$ in `NLAlibScaffold` with a
`sorry` until brief §8; (c) only ET1. Recommendation (a): ET3 is what every early-truncation route
(S7's OSE plus AMM, S9's PCP, the deferred expectation) composes with, and ET6 makes the maintainer's
statement one line once the deferral is lifted. (b) parks the hard half in the scaffold, which
CONTRIBUTING §7 forbids ("not a place to park the hard part").

**Q5. The Frobenius-noise truncated GN bound TG7 (not hard).** Options: (a) state it beside TG5
(rule 4); (b) leave it to TG5's docstring as a comparison point (brief §9.3). Recommendation (a): at $k = 10$,
$\ell = 200$, $p = 2\cdot 10^4$ TG7's factor is $1.51$ and TG5's $5.95$; at $p = 2\cdot 10^6$ they are
$1.09$ and $1.36$; the two meet near $\ell \approx 10^3 k$, above which TG5 wins (its rate);
TG7 also needs neither $4k \le \ell$ nor $4\ell \le p$. About 40 lines.

**Q6. Where early-truncated GN goes (not hard).** Options: (a) `TruncatedGeneralizedNystrom.lean`,
both truncations of GN; (b) `GeneralizedNystrom.lean`; (c) a new `LowRank/Gaussian/EarlyTruncation.lean`.
Recommendation (a): one topic ("truncated generalized Nyström, late and early") under 1000 lines;
(b) mixes truncated outputs into the untruncated file; (c) is a 250-line file for six statements, and
S7's `LowRank/Oblivious/EarlyTruncation.lean` holds early-truncated RSVD and GN together, which (a)
mirrors less well than (c). Either (a) or (c) is fine; rework is a file move.

**Q7. Sequencing with S4 (not hard; coordination).** S4 was not on disk. Recommendation: S6's
Gaussian half first (§4 Order); the Haar half and GN7, GH5 after S4 proves (S4-i), (S4-ii), (S4-iii),
with this note's provisional spellings of §0.2 replaced by S4's. If S4 drops a Haar block result,
L12, L13 and the Haar statements are deferred with it and recorded in the S6 report.

**Q8. `haarProjectionFactor`: home and registration (not hard).** As §1: file 7, a plain `def`
(EW's formula), unregistered like `gaussianProjectionFactor`; S3 fixed the name and argument order
`(d p q)`. Alternative home `RandomMatrix/Haar/Moments.lean`. Rework: a move.

**Q9. Unbiasedness at $\operatorname{rank}\mathbf{A} + 1 \le p$ (not hard).** The reflection proof
needs only integrability, which holds at $r + 1 \le p$ for Gaussian sketches (R4's first spectral
moment at exponent $1 \le p - r$). Recommendation: the minimal hypothesis; the Haar form keeps
$r + 2 \le p$ (its integrability comes from (S4-i)).

**Q10. Names and ids (not hard).** D1 is
`integral_specNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix_pinvSpecNormBound`, told apart from S3's
G4 by the parameter its bound is in (rule 4's `_intrinsicDim` pattern); TG7 is
`…_sq_le_add_sqrt_of_hasLaw_gaussianMatrix` (its right side), L4 `sketchAndSolve_smul_sketch`. The
identity forms are `…_sq_of_…` (fixed $\mathbf{\Omega}$), `…_sq_eq_integral_of_…` (factor inside),
`…_sq_eq_mul_integral_of_…` (Gaussian $\mathbf{\Omega}$), bounds `…_sq_le_mul_integral_of_…`. New
ids `sketch-and-solve-expected-error`, `haar-sketching-identity`; Bartan and Pilanci 2020 gets no
key (not in hand). Rework: renames.

**Q11. Statements law-free in the range test matrix (not hard).** GN2 to GN4, GH2, GH3, TG4, ET3 to
ET5 take any `AEMeasurable X` independent of $\mathbf{\Psi}$. Options: (a) as drafted; (b) Gaussian
$\mathbf{X}$ only, as the brief's §4.3 shapes. Recommendation (a): the proofs never use the law of
$\mathbf{X}$ (common step 2), and S7's and S9's GN and early-truncated GN results become compositions
of their range-finder bounds with these (brief §5.1's table, "S6, S7, S9").

**Q12. Corrections of record (information).**
- Brief §9.3 (rows "Gaussian completion identity" and its use), the assessment (§5) and the
  prototype cite "TW 2023, proof of Theorem 5.1": TW has no Theorem 5.1 and no generalized Nyström.
  The completion identity is cited to [EpperlyWebber2026, Theorem 2.1, Lemma 5.1] and
  [TroppYurtseverUdellCevher2017, Lemma A.5].
- Brief §9.1 and §9.3: CEMT Remark 2.9's "truncated generalized Nyström" is Woodruff's core-truncated
  estimator ([123, Thm. 4.3] = Woodruff 2014), not $\llbracket\mathsf{gn}\rrbracket_k$; it states no
  bound and CEMT do not endorse it.
- Brief §4.3 "Truncated GN in expectation": conditions $\ell \ge 4k + 2$, $p \ge 4\ell$,
  $\operatorname{rank}\mathbf{A} \ge \ell$ become $4k \le \ell$, $4\ell \le p$ and no rank condition;
  $c = (18g + 408)/p$ becomes $(25g + 484)/p$; the spectral core noise needs only $q + 2 \le p$ in
  general (A11), $p \ge 4\ell$ only for its numerical form.
- Brief §4.3 (b) and §5.1's table: EW Theorem 4.2(a) assumes $\operatorname{rank}\mathbf{A} \ge p$
  (their $k$); the identity needs no rank condition beyond $\ell' + 2 \le p$ with
  $\ell' = \min(\operatorname{rank}\mathbf{A}, \ell)$ (GN5), and the sharp bound only S4's condition
  for Theorem 3.2 ($\operatorname{rank}\mathbf{A} \ge \ell$).
- Brief §4.3 "Haar $\mathbf{\Psi}$": the Haar statements need $p \le m$ (§3.0's example); this half
  depends on S4's trace mean and coupled average, which in turn use the row-block law.
- Brief §2, RandomMatrix: "the second spectral moment ... follows by integrating the tail; S6 checks
  whether it exists": it does not exist; the tail would give $\mathbb{E}X^2 \le M^2 + \sqrt{2\pi}M\sigma +
  2\sigma^2$, and concentration with `HasSubgaussianMGF.integral_sq_le` gives the better
  $M^2 + \sigma^2$ (L6).
- S2c §3.7's template K20 is TG5, stated on `truncatedSVD` directly (S2c §8 item 8).

## 8. Amendments from the review (2026-10-15)

Review of this note (ten amendments: three medium, A1 to A3; four low, A4 to A7; three for
information, A8 to A10; four verdicts), all ten accepted by the orchestrator; none rejected. Three
points are corrected on inspection: A2 counts five markers at the start of a line where there are
four, and the same marker pass has two further defects (item 2); A8's threshold 3300 drops the
factor 2 of $\sqrt{2kc}$, and the slack closes at 6600 (item 8); V3's expectation that the
library's route cannot reproduce the notes' 900 and 3600 does not hold, since the JL-moment AMM at
$p = 2$ gives the notes' second moment exactly (item 13). The review found the mathematics sound:
the 57 statements at every rank and shape, the constants against EW, TYUC, TW and the notes
(§3.7's arithmetic recomputed, L13's factor rederived, A9's and Q9's integrability at exponent 1
covered by R4), the S4/S6 division with nothing duplicated, the placement of every lower-layer
addition, the count and the line estimates; nothing is dominated. Q1 and Q2 are decided as (a),
which the review found dominant (items 11, 12). The maintainer scheduled S6b between the two
halves (item 13). Where an item below contradicts §0 to §7, it supersedes them; §3 stays as
drafted.

1. **A1, GN7 and GH5 take S4's free rank parameter** (§0.2 (S4-iii), §3.4 GN7 and GH5, §5 row
   GN7, GH5). S4 is on disk and decided its Q1 as (a) (S4 §8 items 11, 12): `hlA : Fintype.card l
   ≤ A.rank` and the factor `rotationInvariantFactor A.rank (Fintype.card l) q` become
   `{r q : ℕ} (hr : A.rank ≤ r) (hlr : Fintype.card l ≤ r) (hq : q + 2 ≤ Fintype.card l)` and
   `rotationInvariantFactor r (Fintype.card l) q`, which also cover $\operatorname{rank}\mathbf{A}
   < \ell$ and the rank-free instance $r = \lvert n\rvert$. Names, with S4's suffix for the same
   hypothesis (S4 §3.5 writes the composition so; the two notes' conventions aligned):
   GN7 `integral_frobNorm_sub_generalizedNystrom_sq_le_of_isLeftUnitarilyInvariant_of_hasLaw_gaussianMatrix_of_rank_le`,
   GH5 `integral_frobNorm_sub_generalizedNystrom_sq_le_of_isLeftUnitarilyInvariant_of_hasLaw_haarFrame_of_rank_le`,
   each with `theorem` on its own line and `set_option linter.style.longLine false in` with a
   comment, since the name alone exceeds 100 characters (S5 §8 item 12). GN7 reads
   ```lean
   theorem
       integral_frobNorm_sub_generalizedNystrom_sq_le_of_isLeftUnitarilyInvariant_of_hasLaw_gaussianMatrix_of_rank_le
       [DecidableEq n] {ν : Measure (Matrix n l ℝ)} [IsProbabilityMeasure ν]
       [IsLeftUnitarilyInvariant ν] (A : Matrix m n ℝ) (hX : HasLaw X ν μ)
       (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) (hΨ : HasLaw Ψ (gaussianMatrix m p) μ)
       (hXΨ : IndepFun X Ψ μ) {r q : ℕ} (hr : A.rank ≤ r) (hlr : Fintype.card l ≤ r)
       (hq : q + 2 ≤ Fintype.card l) (hlp : Fintype.card l + 2 ≤ Fintype.card p) :
       ∫ ω, frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2 ∂μ ≤
         gaussianProjectionFactor (Fintype.card l) (Fintype.card p) *
           rotationInvariantFactor r (Fintype.card l) q * frobNorm (A - truncatedSVD A q) ^ 2
   ```
   and GH5 the same with `[DecidableEq p]`, `(hΨ : HasLaw Ψ (haarFrame m p) μ)
   (hpm : Fintype.card p ≤ Fintype.card m)` and `haarProjectionFactor (Fintype.card m)
   (Fintype.card p) (Fintype.card l)`. Docstrings: "$\operatorname{rank}\mathbf{A} \le r$,
   $\ell \le r$" in place of "$\ell \le \operatorname{rank}\mathbf{A} = r$"; "there
   $r = \operatorname{rank}\mathbf{A} \ge p$ and a minimum over $q$". Proof unchanged: GN3 (GH3),
   then E2, which holds as stated at $\operatorname{rank}\mathbf{A} < \ell$, so no branch. §0.2's
   provisional spellings become S4's names: (S4-i) is B4,
   `integral_frobNorm_pinv_const_mul_sq_of_hasLaw_haarFrame` with
   `integrable_frobNorm_pinv_const_mul_sq_of_hasLaw_haarFrame`, at $\mathbf{W} :=
   \mathbf{V}_1^{\mathsf{H}}$, $\mathbf{X} := \mathbf{Q}$, plus `pinv_conjTranspose` and
   `frobNorm_conjTranspose` (the rewrite §0.2 anticipated; B4's `hkn`, `hpk` are L12's $p \le m$
   and $r + 2 \le p$); (S4-ii) is U2,
   `integral_conjTranspose_mul_mul_mul_conjTranspose_of_isLeftUnitarilyInvariant`, whose
   hypotheses ($\mathbf{V}_2$ orthonormal, $\mathbf{V}_1^{\mathsf{H}}\mathbf{V}_2 = \mathbf{0}$, $F$
   measurable, the product integrable) are weaker than "complementary frames"; (S4-iii) is E2,
   `integral_frobNorm_sub_rsvd_sq_le_of_isLeftUnitarilyInvariant_of_rank_le`. S4 put
   `rotationInvariantFactor` in the new `LowRank/Gaussian/RotationInvariantFactor.lean` (S4 §8
   item 5); file 9 imports `LowRank/Gaussian/RotationInvariant.lean` for E2, which brings it.
2. **A2, a value marker never begins a line; corrected in its count and extended on inspection**
   (§1 `truncatedGNFactor` paragraph, §2 "Named constants in docstrings", the §3 docstrings of L9,
   TG1, TG2, TG3). The authority is the live `scripts/check_constants.py`, CONTRIBUTING §5.2
   rule 2 and §6 item 5, now final: the marker follows the text before it on its line,
   immediately before the math span (whitespace and at most one line break between), never at the
   start of a line. §1's "just before that math span" and §2's "sits just before the math span"
   read so. Four drafted markers begin a line (L9, TG1, TG2, TG3), not five: TG5's already trails
   "$c = \frac{25g + 484}{p}$,". The S4 note had the same slip; S4 §8 item 1 already corrected it,
   so nothing is left for S4. Two further defects of the same pass, found on inspection:
   - *Spelling of `gaussianPinvSpecNormBound`.* The spans of L9, A11 and D1 write
     $\tfrac{e}{k-r}\sqrt{\tfrac{k+r-1}{2}}$, which contains neither the registry's `latex`
     (`e\sqrt{(#2 + #1 - 1)/2}/(#2 - #1)`) nor its `display`
     (`\frac{e}{#2 - #1}\sqrt{(#2 + #1 - 1)/2}`), so the checker would fail. They are rewritten in
     the display form, $\frac{e}{k - r}\sqrt{(k + r - 1)/2}$ (L11 already uses the `latex` form),
     and the squared occurrence $\frac{e^2(k+r-1)}{2(k-r)^2}$ becomes
     $\bigl(\frac{e}{k - r}\sqrt{(k + r - 1)/2}\bigr)^2$, so that `--update` rewrites every
     occurrence when the bound improves.
   - *`truncatedGNFactor`'s template, decided once.* The value is written out in full, with no $g$
     or $c$ named by a sentence (the checker could not then see the 25 and the 484, and the rule
     forbids a symbol defined by a sentence):
     ```toml
     kind = "factor"
     latex = '1 + #1/(#2 - #1 - 1) + 4\sqrt{2#1 (25(1 + #1/(#2 - #1 - 1)) + 484)/#3} + 8#1 (25(1 + #1/(#2 - #1 - 1)) + 484)/#3'
     display = '1 + \frac{#1}{#2 - #1 - 1} + 4\sqrt{\frac{2#1}{#3}\Bigl(25\Bigl(1 + \frac{#1}{#2 - #1 - 1}\Bigr) + 484\Bigr)} + \frac{8#1}{#3}\Bigl(25\Bigl(1 + \frac{#1}{#2 - #1 - 1}\Bigr) + 484\Bigr)'
     ```
     (`kind` is S4's word; the other fields as §1). Filled with `k \ell p`, the inline form is 108
     characters, over the 100-character limit for a one-line `$…$` span, so TG1, TG2, TG3 and TG5
     show the value in a `$$…$$` display broken across lines; the reading
     "$g + 4\sqrt{2kc} + 8kc$, $g = 1 + k/(\ell - k - 1)$, $c = (25g + 484)/p$" may follow the
     display as an explanation. TG7's $g$ is `gaussianProjectionFactor k ℓ`'s value, which item 3
     makes a registered constant, and is written out with its marker in the same way. §3.7's prose
     keeps $g$ and $c$ (prose about the constant itself, CONTRIBUTING §6 item 5).
3. **A3, `haarProjectionFactor` is registered** (§1, §2 last paragraph, Q8). S4 registers
   `gaussianProjectionFactor` (S4 §8 item 4; the entry lands with S4's commit and is not yet in
   `docs/constants.toml`), and its item 4 supersedes this note's §2 sentence "unregistered source
   formulas, written out inline … without markers". `haarProjectionFactor` is registered the same
   way, in the commit that defines it:
   ```toml
   [[constant]]
   name = "NLAlib.haarProjectionFactor"
   kind = "factor"
   file = "NLAlib/RandomMatrix/Haar/Blocks.lean"
   args = ["d", "p", "q"]
   latex = '1 + (#1 - #2)/(#1 - #3) \cdot (#3/(#2 - #3 - 1))'
   display = '1 + \frac{#1 - #2}{#1 - #3}\cdot\frac{#3}{#2 - #3 - 1}'
   lean_body = 'haarProjectionFactor (d p q : ℕ) : ℝ := 1 + ((d : ℝ) - p) / ((d : ℝ) - q) * ((q : ℝ) / ((p : ℝ) - q - 1))'
   ```
   (`file` per item 6, `body_hash` by `--update`). It stays a plain `def` with its `_def` lemma,
   its body being EW's formula: registration is about display, not opacity. Every backticked
   mention of either factor carries a marker: A6's "`gaussianProjectionFactor q p`" (§3.2) and the
   definition's own docstring, which writes the value inline in the `latex` form,
   $1 + (d - p)/(d - q) \cdot (q/(p - q - 1))$, since an inline span is matched against `latex`
   only. Beyond what the checker enforces, every docstring whose Lean statement names a
   registered constant (`gaussianProjectionFactor`, `haarProjectionFactor`,
   `rotationInvariantFactor`, `gaussianPinvSpecNormBound`, `truncatedGNFactor`, and item 13's two)
   puts its marker before the display that shows the value, as S4 §8 item 1 does for E1 to E4.
   The drafted displays already contain the `display` forms (A6's
   $\Bigl(1 + \frac{q}{p-q-1}\Bigr)$, A13's $1 + \frac{m-p}{m-q}\cdot\frac{q}{p-q-1}$), so this
   is a marker pass (Sonnet), done before file 7 is written.
4. **A4 and Q6 decided: (c), early-truncated GN in its own file** (§3.6, §4 file 10, Q6).
   `LowRank/Gaussian/EarlyTruncation.lean` (new) holds ET1 to ET6 and S6b's assembly (item 13):
   early-truncated RSVD and GN in expectation with Gaussian test matrices, mirroring S7's
   `LowRank/Oblivious/EarlyTruncation.lean`. Imports: file 7, `LowRank/Structural/EarlyTruncation`,
   `Probability/Measurability/Matrix`, and item 13's. `TruncatedGeneralizedNystrom.lean` keeps
   TG1 to TG7 (about 400 lines) and drops the `LowRank/Structural/EarlyTruncation` import.
5. **A5, what the deferred result needs, corrected of record** (§0 "Missing infrastructure" and
   "Not reached", Q4, Q12). The list repeated from brief §8 ("Gordon's inequality with Gaussian
   concentration, a chi-square small-ball bound, inverse moments of $\min\{1, \lambda\}$ up to
   order four by a layer-cake integral, decoupling") is out of date. In the library, each checked
   by name on 2026-10-15:
   - Gordon's lower bound and the one-sided $\sigma_{\min}$ tail $e^{-u^2/2}$:
     `le_integral_singularValues_of_hasLaw_gaussianMatrix`,
     `measureReal_singularValues_le_le_of_hasLaw_gaussianMatrix`
     (`RandomMatrix/Gaussian/ExtremeSingularValues.lean`);
   - the chi-square small ball $(eu/d)^{d/2}$ and the real moments of $\chi^2_d$ (hence
     $\mathbb{E}\|\mathbf{\Omega}_1\|_{\mathsf{F}}^4 = (k\ell)^2 + 2k\ell$):
     `measureReal_norm_sq_le_le_rpow_of_hasLaw_gaussianVector`
     (`Probability/Distributions/ChiSquare.lean`), `integral_norm_sq_rpow_of_hasLaw_gaussianVector`
     (`ChiSquareMoments.lean`);
   - the layer-cake bound $\mathbb{E}f \le a + \int_a^\infty F$: `integral_le_of_measureReal_ge_le`
     (`Probability/Tail.lean`);
   - AMM from the JL moment: `HasJLMoment.integral_frobNorm_conjTranspose_mul_sub_rpow_le`
     (`Sketching/Properties/MatrixMultiplication.lean`) with `hasJLMoment_of_hasLaw_gaussianMatrix`
     (`Sketching/Gaussian/Gaussian.lean`), $\delta = 2/(\ell\varepsilon^2)$ at $p = 2$;
   - block independence and the conditional Frobenius moment:
     `indepFun_conjTranspose_mul_of_hasLaw_gaussianMatrix`,
     `integral_frobNorm_mul_mul_sq_of_hasLaw_gaussianMatrix_of_indepFun`; R4's spectral inverse
     moments `integral_specNorm_pinv_rpow_le_of_hasLaw_gaussianMatrix` ($0 < q \le k - r$);
   - S2b's deterministic core in the $\min\{1, \lambda\}$ form,
     `IsSubspaceInjection.frobNorm_sub_earlyTruncatedRSVD_sq_le`, and its projector form
     `IsSubspaceInjection.frobNorm_sub_mul_sq_le` (`LowRank/Structural/EarlyTruncation.lean`);
     L1 of this note for the Tonelli steps.

   What was missing is one lemma, the clipped inverse moments, now item 13's ER5. "Not reached"
   drops early-truncated RSVD in expectation; the S2b note's "smallest-singular-value tails" item
   is done.
6. **A6 and Q8 decided: `haarProjectionFactor` lives in `RandomMatrix/Haar/Blocks.lean`** (§1
   "Home", §4 placement bullet, Q8). The mirror of `gaussianProjectionFactor`, which the S3 note put
   in `RandomMatrix/Gaussian/BlockMoments.lean` beside the block moment whose value it packages:
   $h_d(p, q) - 1$ is L13's coefficient, and L12, L13 and B4 are in that file. A1 to A4 (the
   definition, `haarProjectionFactor_def`, `one_le_haarProjectionFactor`,
   `haarProjectionFactor_le_haarProjectionFactor`) move there. A5,
   `haarProjectionFactor_le_gaussianProjectionFactor`, stays in file 7: `Haar/Blocks.lean` does not
   import `Gaussian/BlockMoments.lean` (S4 §4 lists `Gaussian/Moments` and
   `Gaussian/InverseMoments/Frobenius`), and file 7 imports both. The factor's consumers are all
   Haar statements, so it is written with the Haar half.
7. **A7, A11' is public** (§3.2 A11, §3.7). A11's docstring sentence "For $p \ge 4q$ this is at
   most …" becomes a statement, in file 7 after A12, and A11's docstring names it:
   ```lean
   /-- **The Gaussian sketch-and-solve excess is spectrally flat**: with
   $\mathbf{E} = (\mathbf{I}-\mathbf{P}_{\mathbf{X}})\mathbf{B}$, $q = \operatorname{rank}\mathbf{X}$
   and $4q \le p$,
   $$\mathbb{E}\|\mathbf{\Pi}_{\mathbf{X},\mathbf{S}}\mathbf{E}\|_2^2 \le
   \frac{25}{p}\|\mathbf{E}\|_{\mathsf{F}}^2 + \frac{4q}{p}\|\mathbf{E}\|_2^2\,:$$
   the core noise of generalized Nyström is $O(1/p)$ times the Frobenius residual. Proved without
   a literature source. -/
   theorem
       integral_specNorm_obliqueProjector_mul_one_sub_rangeProjector_mul_sq_le_div_card_of_hasLaw_gaussianMatrix
       (hS : HasLaw S (gaussianMatrix p m) μ) (X : Matrix m s ℝ)
       (hX : 4 * X.rank ≤ Fintype.card p) (B : Matrix m r ℝ) :
       ∫ ω, specNorm (obliqueProjector X (S ω) * ((1 - rangeProjector X) * B)) ^ 2 ∂μ ≤
         25 / (Fintype.card p : ℝ) * frobNorm ((1 - rangeProjector X) * B) ^ 2 +
           4 * (X.rank : ℝ) / Fintype.card p * specNorm ((1 - rangeProjector X) * B) ^ 2
   ```
   The suffix `_le_div_card` (the review's) tells it from A11 by its right side (rule 4). Route:
   $q = 0$ makes the oblique projector $\mathbf{0}$ and the left side $0$; otherwise $4q \le p$
   gives $q + 2 \le p$, then A11 and §3.7's first bullet ($\beta^2 \le 8.21/p$,
   $\frac{q}{p-q-1} \le \frac{2q}{p}$, $3 \times 8.21 \le 25$); about 20 lines. Its 25 and 4 are
   an explicit comparison of A11's named bound, as TG3's numbers are of TG1's (rule 2): an
   improvement of `gaussianPinvSpecNormBound` leaves it true. TG5's private noise lemma uses it, and
   S7's structured-$\mathbf{\Psi}$ analogue has its shape to mirror.
8. **A8, TG3's threshold, recorded and corrected on inspection** (§1, §3.5 TG3 and TG6, §3.7).
   The review's 3300 drops the factor 2 of $\sqrt{2kc}$: with $k \le \varepsilon\ell/6$,
   $p \ge C\ell/\varepsilon$ and $c \le 515.25/p$, $4\sqrt{2kc} \le 4\varepsilon\sqrt{171.75/C}$,
   which is $0.91\,\varepsilon$ at $C = 3300$, and there the factor reaches $1 + 1.37\,\varepsilon$
   (at $k = 1$, $\varepsilon = 1$, with the ceilings), so the claim is false. The same chain of
   estimates closes at $C = 6600$ ($0.25 + 4\sqrt{171.75/C} + 687/C \le 1$); the exact factor,
   checked at $k \le 200$ and $\varepsilon \in [0.01, 1]$, needs about the same. **Kept at 8000**
   (worst $1 + 0.922\,\varepsilon$): the margin absorbs the rounding in TG3's proof, and 8000
   already beats the notes' 12500. A later pass lowering it changes TG3's and TG6's numbers and
   nothing else (rule 2); 6600 is the floor of this route, so a pass below it needs a sharper
   input (Q3 (b)).
9. **A9, names and paths** (§3.3 D1, §5, Q10). D1 keeps
   `integral_specNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix_pinvSpecNormBound`; its docstring
   adds "the bound is written in `gaussianPinvSpecNormBound k ℓ`, whence the name's suffix" (the
   marker D1 already carries covers the mention). The result-id check of §5 ran against
   `results.toml` of the sibling repository, `NLA-lib/explore/results.toml`, not inside `nlalib/`.
10. **A10, consumers** (§0.3). New row: "S4's U1 | not consumed by S6: A16 uses
    `hasLaw_const_mul_of_isLeftUnitarilyInvariant` directly; U2's proof consumes U1, and S6
    consumes U2 (L12)". S4 Q5's "only S6 consumes U1" should read "U2's proof consumes U1; S6
    consumes U2": a correction to the S4 note, for the orchestrator (this note does not edit S4's).
11. **Q1 decided: (a)** (review V1, dominant). The Sketching round states every Gaussian sketch
    as `S : Ω → Matrix k n` on the left and every Haar sketch as `(Q ω)ᴴ` for
    `Q ∼ haarFrame n k` (`Sketching/Gaussian/Gaussian.lean`, `Haar.lean`), and D14 put the sketch
    on the left in `obliqueProjector X S`: (a) is the only option under which file 7 reads like
    its neighbours; (b) would write `obliqueProjector A (Ψ ω)ᴴ` in a Sketching file; (c) adds a
    scale that L4 makes irrelevant. GN keeps D2 and bridges with
    `hasLaw_conjTranspose_of_hasLaw_gaussianMatrix`, as `BlockMoments.lean` already does.
12. **Q2 decided: (a); the notes' constants recorded** (review V2, dominant). Rule 2 requires a
    named definition for the proof's constant, with API that survives improvements (TG2, TG3);
    the arity `(k l p)` matches `gaussianProjectionFactor k l` and
    `rotationInvariantFactor r l q`. The one alternative, naming only the noise constant
    (`truncatedGNNoiseConstant k l p`) and keeping $g + 4\sqrt{2kc} + 8kc$ visible in TG5, would
    lock a shape that TW's second moment might change. Measurability is settled (TG4's integrand
    is `measurable_truncatedSVD` composed with `measurable_generalizedNystrom`), so TG5 is stated
    on `truncatedSVD` with no selector, as S2c §8 item 8 asked for K20.
    **Where the maintainer's notes' constants differ from ours, and why** (`tGN_replacement.tex`;
    in the notes' letters $t$ is the range size, our $\ell$, and $s$ the co-range size, our $p$):
    the noise constant $444/s = (36 + 4 \cdot 102)/s$ ($18/s$ times $\mathbb{E}\varphi^2 \le
    2\,\mathrm{OPT}^2$, plus $4t/s$ times the residual) against ours $c = (25g + 484)/p \le
    515.25/p$; the spectral residual $102/t$ against ours $121/\ell$; the threshold
    $s \ge 12500\,t/\varepsilon$ against ours $p \ge 8000\,\ell/\varepsilon$. The cause is one
    lemma: the notes' `lem:moments` is TW Lemma B.1's second moment,
    $(\mathbb{E}\|\mathbf{S}\mathbf{G}\mathbf{T}\|_2^2)^{1/2} \le \|\mathbf{S}\|_2
    \|\mathbf{T}\|_{\mathsf{F}} + \|\mathbf{S}\|_{\mathsf{F}}\|\mathbf{T}\|_2$, proved by a
    second-moment Slepian comparison the library does not have. L6 reaches it through Gaussian
    concentration with the extra term $\|\mathbf{S}\|_2^2\|\mathbf{T}\|_2^2$, which turns
    $2\beta^2 \le 16.4/p$ (the notes' 18) into $3\beta^2 \le 24.63/p$ (our 25), and 102 into 121
    (Q3). Our threshold is nevertheless smaller, because TG3 bounds $g \le 1 + \varepsilon/4$ where
    the notes spend $\mathbb{E}\varphi^2 \le 2\,\mathrm{OPT}^2$. TW's comparison added later
    (Q3 (b)) changes `truncatedGNFactor`'s body and TG3's numbers only. S6b's constants (item 13)
    are the notes' 900 and 3600: that route does not use `lem:moments`.
13. **S6b, early-truncated RSVD in expectation** (maintainer decision, 2026-10-15; supersedes
    Q4's deferral, the "Not reached" entry, §3.6's last paragraph and brief §8's deferral of this
    item). The $(1 + \varepsilon/2)$ bound that ET6 takes as `hRSVD` becomes a theorem, so that the
    early-truncated GN $\varepsilon^{-2}$ statement is unconditional within this round.
    **Stage order:** (i) S6's Gaussian half: files 1 to 5 and 8, the Gaussian sections of files 7,
    9 and 10, and ET1, ET3, ET4, ET6 of file 11; (ii) **S6b**: ER1 to ER12 below; (iii) S6's Haar
    half: file 6 with `haarProjectionFactor`, the Haar sections of files 7, 9 and 11 (A5, A13 to
    A17, GH1 to GH5, ET2, ET5) and GN7, which waits for S4's E2 with GH5. S6b depends on S6's L1,
    L2 and ET6, on S2b's core, S3, R1, R2, R4 and the inputs of item 5; not on S4. About 500
    lines, one proof agent; with this item a separate S6b note is not needed (a short brief for the
    proof agent suffices). The notes' `thm:etRSVD`, `lem:et-decoupling`, `lem:et-smallball`,
    `lem:et-inverse-moments` and `thm:etGN` (`pcps-et-audited.tex`) are proof material, never
    cited (D13).

    *ER1 to ER5*, `RandomMatrix/Gaussian/ExtremeSingularValues.lean` (registered, 445 lines, about
    +260; side file `RandomMatrix/Gaussian/ClippedInverseMoments.lean` until proved; new imports
    `RandomMatrix/Gaussian/InverseMoments/Spectral` and `Probability/Tail`, no cycle). A fact about
    the smallest singular value of a Gaussian matrix, beside Gordon's bound and the
    $\sigma_{\min}$ tail it is proved from (CONTRIBUTING §8 item 5); this is why S6b touches this
    file as well as file 11, rather than putting the lemma in the assembly file.
    ```lean
    /-- **The clipped inverse-moment constant** <!-- value gaussianClippedInvMomentConstant q -->
    $$2q (0.9)^{-(2q + 1)} e^{(2q + 1)^2/50}\sqrt{2\pi} + 1$$
    of `integral_min_one_singularValues_sq_div_inv_pow_le_of_hasLaw_gaussianMatrix`; proved
    without a literature source. API: `gaussianClippedInvMomentConstant_one_le_10`,
    `gaussianClippedInvMomentConstant_four_le_263`. -/
    noncomputable irreducible_def gaussianClippedInvMomentConstant (q : ℕ) : ℝ :=
      2 * q * 0.9 ^ (-(2 * q + 1 : ℤ)) * Real.exp ((2 * q + 1) ^ 2 / 50) * √(2 * π) + 1
    theorem gaussianClippedInvMomentConstant_one_le_10 : gaussianClippedInvMomentConstant 1 ≤ 10
    theorem gaussianClippedInvMomentConstant_four_le_263 :
        gaussianClippedInvMomentConstant 4 ≤ 263
    theorem integrable_min_one_singularValues_sq_div_inv_pow_of_hasLaw_gaussianMatrix
        (hX : HasLaw X (gaussianMatrix m n) μ) {k : ℕ} (hk : k + 1 = Fintype.card n) {q : ℕ}
        (hq : 2 * q + Fintype.card n ≤ Fintype.card m) :
        Integrable (fun ω => (min 1 (singularValues (X ω) k ^ 2 / Fintype.card m))⁻¹ ^ q) μ
    /-- **Clipped inverse moments of the smallest singular value**: for a standard Gaussian
    $m \times n$ matrix $\mathbf{G}$, $\bar\lambda = \min\{1, \sigma_{\min}(\mathbf{G})^2/m\}$,
    $100n \le m$, $900 \le m$ and $1 \le q \le 4$, <!-- value gaussianClippedInvMomentConstant q -->
    $$\mathbb{E}\,\bar\lambda^{-q} \le \bigl(1 - \sqrt{n/m}\bigr)^{-2q} +
    \frac{2q (0.9)^{-(2q + 1)} e^{(2q + 1)^2/50}\sqrt{2\pi} + 1}{\sqrt{m}}\,.$$
    Proved without a literature source; inputs [Vershynin2018, Exercise 7.3.4, Corollary 7.3.3]
    and [HalkoMartinssonTropp2011, Proposition 10.4] (in the forms of this library). -/
    theorem integral_min_one_singularValues_sq_div_inv_pow_le_of_hasLaw_gaussianMatrix
        (hX : HasLaw X (gaussianMatrix m n) μ) {k : ℕ} (hk : k + 1 = Fintype.card n)
        (hnm : 100 * Fintype.card n ≤ Fintype.card m) (hm : 900 ≤ Fintype.card m)
        {q : ℕ} (hq1 : 1 ≤ q) (hq4 : q ≤ 4) :
        ∫ ω, (min 1 (singularValues (X ω) k ^ 2 / Fintype.card m))⁻¹ ^ q ∂μ ≤
          ((1 - √((Fintype.card n : ℝ) / Fintype.card m)) ^ (2 * q))⁻¹ +
            gaussianClippedInvMomentConstant q / √(Fintype.card m)
    ```
    Letters as Gordon's statement (tall $m \times n$, $\sigma_k$ with $k + 1 = \lvert n\rvert$).
    Registry: `kind = "constant"`, `args = ["q"]`,
    `latex = '2#1 (0.9)^{-(2#1 + 1)} e^{(2#1 + 1)^2/50}\sqrt{2\pi} + 1'`. Values:
    $c_1 = 9.234$, $c_4 = 262.55$. Route of ER5: $f = \bar\lambda^{-q} \ge 1$; split
    $f = \min(f, u_0) + (f - u_0)^{+}$ at $u_0 = (\sqrt m/s_0)^{2q}$, $s_0 = \frac12\sqrt{m/n}$
    ($\ge 5$). The first part by the layer-cake bound with $a = (1 - \sqrt{n/m})^{-2q}$: for
    $u > a$ the event $\{u \le f\}$ is $\{\sigma \le \sqrt m\,u^{-1/(2q)}\}$, a threshold in
    $[s_0, \sqrt m - \sqrt n]$, where the Gordon tail and $s^{-(2q+1)} \le
    (\sqrt m - \sqrt n)^{-(2q+1)}e^{(2q+1)v/5}$ ($v$ the distance below the mean bound) give the
    middle term exactly as the notes' (eq:et-inverse-middle). The second part by Cauchy–Schwarz
    in place of the notes' row small ball (eq:et-smallball, not in the library):
    $\mathbb{E}f^2 \le 1 + m^{2q}\,\mathbb{E}\|\mathbf{G}^{+}\|_2^{4q} \le 1 +
    (m\beta(n,m)^2)^{2q} \le 1 + 3.81^{2q}$ (R4 on $\mathbf{G}^{\mathsf{H}}$, $4q \le m - n$) and
    $\mathbb{P}(\sigma \le s_0) \le e^{-(0.4\sqrt m)^2/2}$ ($\sqrt m - \sqrt n - s_0 \ge
    0.4\sqrt m$), so the part is below $211\,e^{-36} \le m^{-1/2}$: the "$+1$" of $c_q$. Both
    estimates need $m \ge 900$ and $m \ge 100n$, the notes' hypotheses. ER4: $f \le 1 +
    m^q\|\mathbf{G}^{+}\|_2^{2q}$ and `integrable_specNorm_pinv_rpow_of_hasLaw_gaussianMatrix` at
    $2q \le m - n$. ER2, ER3: `norm_num` with bounds on $e^{9/50}$, $e^{81/50}$, $\sqrt{2\pi}$.

    *ER6*, `LowRank/Random/RangeFinder.lean` (registered; written proved in place), the law-free
    companion beside `integrable_frobNorm_sub_rsvd_sq`:
    ```lean
    theorem integrable_frobNorm_sub_earlyTruncatedRSVD_sq [IsFiniteMeasure μ] (A : Matrix m n 𝕜)
        (hX : AEMeasurable X μ) (k : ℕ) :
        Integrable (fun ω => frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2) μ
    ```
    (bounded by $\|\mathbf{A}\|_{\mathsf{F}}^2$, measurable by L2; about 10 lines).

    *ER7 to ER12*, `LowRank/Gaussian/EarlyTruncation.lean` (item 4), after ET6. Real; new imports
    `RandomMatrix/Gaussian/ExtremeSingularValues`, `Sketching/Properties/MatrixMultiplication`,
    `Sketching/Gaussian/Gaussian`. A named factor, its API, the expectation bound and its sample-size
    corollary, as TG1 to TG3, TG5, TG6 (rule 2: the proof's constants, an expectation stated with a
    closed-form factor first):
    ```lean
    /-- **The early-truncated randomized SVD factor**, at present, with $y = \sqrt{k/\ell}$,
    <!-- value earlyTruncatedRSVDFactor k \ell -->
    $$\frac{(1 + \sqrt{2k/\ell})\bigl((1 - \sqrt{k/\ell})^{-2} + 10/\sqrt{\ell}\bigr) +
    \frac{1}{4}\sqrt{k/\ell}\sqrt{1 + 2/(k \ell)}\sqrt{(1 - \sqrt{k/\ell})^{-8} +
    263/\sqrt{\ell}}}{1 - 4\sqrt{k/\ell}}$$
    … at most $1 + \varepsilon$ at $\ell \ge 900k/\varepsilon^2$
    (`earlyTruncatedRSVDFactor_le_one_add`). Proved without a literature source. -/
    noncomputable irreducible_def earlyTruncatedRSVDFactor (k l : ℕ) : ℝ :=
      ((1 + √(2 * k / l)) * (((1 - √(k / l)) ^ 2)⁻¹ + 10 / √l) +
          √(k / l) / 4 * √(1 + 2 / (k * l)) * √(((1 - √(k / l)) ^ 8)⁻¹ + 263 / √l)) /
        (1 - 4 * √(k / l))
    theorem one_le_earlyTruncatedRSVDFactor {k l : ℕ} (h : 100 * k ≤ l) :
        1 ≤ earlyTruncatedRSVDFactor k l
    theorem earlyTruncatedRSVDFactor_le_one_add {k l : ℕ} {ε : ℝ} (hk : 1 ≤ k) (hε : 0 < ε)
        (hε1 : ε ≤ 1) (hl : 900 * (k : ℝ) ≤ ε ^ 2 * l) : earlyTruncatedRSVDFactor k l ≤ 1 + ε
    /-- **The expected error of the early-truncated randomized SVD**: for a standard Gaussian
    $n \times \ell$ test matrix, $100k \le \ell$ and $900 \le \ell$, (ER7's marker here)
    $$\mathbb{E}\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)
    \|_{\mathsf{F}}^2 \le (\cdots)\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
    with ER7's display in place of $(\cdots)$ (shortened here).
    Every rank and shape; every choice of the truncation. Proved without a literature source;
    the sketch quantities are those of [CohenElderMuscoMuscoPersu2015, proof of Theorem 12];
    the algorithm is [TroppYurtseverUdellCevher2017, §7.3.1]. Result: etrsvd -/
    theorem integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_of_hasLaw_gaussianMatrix
        (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ}
        (hkl : 100 * k ≤ Fintype.card l) (hl : 900 ≤ Fintype.card l) :
        ∫ ω, frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 ∂μ ≤
          earlyTruncatedRSVDFactor k (Fintype.card l) * frobNorm (A - truncatedSVD A k) ^ 2
    /-- **The early-truncated randomized SVD reaches relative error $1 + \varepsilon$** with
    $\ell \ge 900k/\varepsilon^2$ Gaussian samples and $k$ products with
    $\mathbf{A}^{\mathsf{H}}$. Proved without a literature source. Result: etrsvd -/
    theorem integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_one_add_mul_of_hasLaw_gaussianMatrix
        (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ} {ε : ℝ} (hε : 0 < ε)
        (hε1 : ε ≤ 1) (hl : 900 * (k : ℝ) ≤ ε ^ 2 * Fintype.card l) :
        ∫ ω, frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 ∂μ ≤
          (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2
    /-- **Early-truncated generalized Nyström reaches relative error $1 + \varepsilon$**: for
    independent standard Gaussian test matrices with $\ell \ge 3600k/\varepsilon^2$ and
    $p \ge k + 1 + (2+\varepsilon)k/\varepsilon$,
    $$\mathbb{E}\|\mathbf{A}-\mathsf{earlyTruncatedGN}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi},
    k)\|_{\mathsf{F}}^2 \le (1+\varepsilon)\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k
    \|_{\mathsf{F}}^2\,:$$
    $O(k/\varepsilon^2)$ products with $\mathbf{A}$, $O(k/\varepsilon)$ with
    $\mathbf{A}^{\mathsf{H}}$, rank at most $k$. Proved without a literature source; the
    algorithm is [TroppYurtseverUdellCevher2017, §7.3.1, (7.3)]. Result: etgn -/
    theorem
        integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_le_one_add_mul_of_hasLaw_gaussianMatrix
        (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ)
        (hΨ : HasLaw Ψ (gaussianMatrix m p) μ) (hXΨ : IndepFun X Ψ μ) {k : ℕ} {ε : ℝ}
        (hε : 0 < ε) (hε1 : ε ≤ 1) (hl : 3600 * (k : ℝ) ≤ ε ^ 2 * Fintype.card l)
        (hp : (k : ℝ) + 1 + (2 + ε) * k / ε ≤ Fintype.card p) :
        ∫ ω, frobNorm (A - earlyTruncatedGeneralizedNystrom A (X ω) (Ψ ω) k) ^ 2 ∂μ ≤
          (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2
    ```
    ER12 is the maintainer's primary early-truncation statement, unconditional. It takes the name
    TG6's pattern gives; **ET6 is renamed**
    `integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_le_one_add_mul_of_hasLaw_gaussianMatrix_of_integral_le`
    (its `hRSVD`, any law of $\mathbf{\Omega}$) and kept: S7's and S9's early-truncated RSVD bounds
    compose with it. Registry for ER7: `kind = "factor"`, `args = ["k", "l"]`,
    `latex = '((1 + \sqrt{2#1/#2})((1 - \sqrt{#1/#2})^{-2} + 10/\sqrt{#2}) + (\sqrt{#1/#2}/4)\sqrt{1 + 2/(#1 #2)}\sqrt{(1 - \sqrt{#1/#2})^{-8} + 263/\sqrt{#2}})/(1 - 4\sqrt{#1/#2})'`,
    `display` the `\frac` form of the docstring above; 176 characters filled, so displays only.
    ER10's docstring shows the factor's display with its marker (shortened above).

    Routes. *ER10:* $k = 0$: both sides $\|\mathbf{A}\|_{\mathsf{F}}^2$ up to the factor (ER8).
    $k \ge \lvert n\rvert$ or $\operatorname{rank}\mathbf{A} \le k$: $\mathrm{OPT}_k = 0$ and the
    core gives error $0$ almost surely. Otherwise $\mathbf{Z}$ the top-$k$ right singular frame
    (`exists_hasOrthonormalCols_mul_mul_conjTranspose_eq_truncatedSVD`), $\mathbf{E} = \mathbf{A} -
    \llbracket\mathbf{A}\rrbracket_k$, the normalised sketch $\mathbf{S} = \ell^{-1/2}\mathbf{X}$,
    $\bar\lambda = \min\{1, \sigma_{k-1}(\mathbf{X}^{\mathsf{H}}\mathbf{Z})^2/\ell\}$ (positive
    almost surely, R1) with `HasOrthonormalCols.isSubspaceInjection_iff_le_sq_singularValues`, and
    the projector form `IsSubspaceInjection.frobNorm_sub_mul_sq_le` at $\mathbf{P} =
    \mathbf{P}_{\llbracket\mathbf{A}\mathbf{X}\rrbracket_k}$ and $\theta = 4\sqrt{k/\ell}$; its
    `hopt` for $\mathbf{S}$ is the scaled optimality of the truncation, so no `truncatedSVD_smul`
    is needed (the measurable choice is not scale-equivariant under ties). Expectations, by L1:
    $\mathbb{E}[\mathrm{OPT}^2/\bar\lambda]$ by ER5 at $q = 1$; $\mathbb{E}[w/\bar\lambda] =
    \mathbb{E}w\,\mathbb{E}\bar\lambda^{-1}$ ($w$ is a function of
    $\mathbf{Z}_\perp^{\mathsf{H}}\mathbf{X}$, $\bar\lambda$ of $\mathbf{Z}^{\mathsf{H}}\mathbf{X}$,
    independent by `indepFun_conjTranspose_mul_of_hasLaw_gaussianMatrix`) with
    $\mathbb{E}w \le (\mathbb{E}w^2)^{1/2} \le \sqrt{2/\ell}\,\mathrm{OPT}^2$ (the JL-moment AMM at
    $p = 2$, $\mathbf{A} = \mathbf{B} = \mathbf{E}^{\mathsf{H}}$: $(\varepsilon\|\mathbf{E}\|^2)^2
    \cdot 2/(\ell\varepsilon^2)$, the notes' exact-identity bound, which corrects V3);
    $\mathbb{E}[\chi^2/\bar\lambda^2] \le \ell^{-2}\mathrm{OPT}^2\sqrt{(k\ell)^2 + 2k\ell}\,
    (\mathbb{E}\bar\lambda^{-4})^{1/2}$ (the conditional Frobenius moment, Cauchy–Schwarz, the
    $\chi^2_{k\ell}$ moment at $s = 2$, ER5 at $q = 4$); then ER2, ER3 and monotonicity give the
    factor's body. Private lemmas per CONTRIBUTING §7's 80-line rule; about 200 lines. *ER11:*
    $k = 0$ trivial; else $\ell \ge 900k \ge 100k$, $\ell \ge 900$, ER10 and ER9. *ER9:* the
    arithmetic: worst $1 + 0.727\,\varepsilon$ over $k \le 1000$, $\varepsilon \in [0.005, 1]$
    (checked numerically with the ceilings). *ER12:* ER11 at $\varepsilon/2$
    ($3600k \le \varepsilon^2\ell$ is $900k \le (\varepsilon/2)^2\ell$) is the renamed ET6's
    `hRSVD`, with `hX.aemeasurable`; about 15 lines. Degenerate: §3.0's list, plus $k = 0$ and
    $k \ge \lvert n\rvert$ as above; $\ell > n$ allowed.

    **Constants against the notes.** S6b reaches the notes' 900 (`thm:etRSVD`) and 3600
    (`thm:etGN`) and their $c_q$: the AMM bound is the same (above), the middle tail integral is
    the same, and the small-ball piece, by Cauchy–Schwarz here and by a row-distance argument in the
    notes, is below $m^{-1/2}$ either way. One difference: the notes take $\theta = \varepsilon/8$;
    here $\theta = 4\sqrt{k/\ell}$, a function of the sizes so that the factor is one of $(k,\ell)$
    alone ($0.133\,\varepsilon$ at $\ell = 900k/\varepsilon^2$, the notes' $0.125\,\varepsilon$ up
    to rounding). On the factor alone the threshold would close near 520, but ER5 needs
    $\ell \ge 900$, so 900 stays; a lower threshold needs ER5 below $m = 900$.

    *Cut:* the Haar-$\mathbf{\Psi}$ twin of ER12 (ET5 with ER11, three lines; additive), and an
    early-truncated RSVD tail with Gaussian sketches (S7's OSE plus AMM route gives tails).
14. **The other questions** stand as recommended, with these changes: Q4 is superseded by item 13
    (ET3 stays the primary composition, ET6 is renamed and kept, ER12 is the unconditional form;
    Q4's option (b) is moot); Q6 is decided as (c) (item 4); Q7: S4 is on disk, the order is item
    13's; Q8 is decided by items 3 and 6; Q10's names stand with item 1's and item 13's additions.
    Q3, Q5, Q9, Q11 and Q12 stand.
15. **Files and count after the amendments** (supersedes the §4 table and its size paragraph).

    | # | File | Statements | Lines (est.) | Half |
    |---|---|---|---|---|
    | 1 | `ForMathlib/Probability/Independence/Basic.lean` (registered) | 1 (L1) | +30 | Gaussian |
    | 2 | `Probability/Measurability/Matrix.lean` (registered) | 2 (L2, L3) | +25 | Gaussian |
    | 3 | `Matrix/Pseudoinverse/LeastSquares.lean` (registered) | 1 (L4) | +12 | Gaussian |
    | 4 | `RandomMatrix/Gaussian/SpectralNorm.lean` (registered) | 3 (L5 to L7) | +90 | Gaussian |
    | 5 | `RandomMatrix/Gaussian/BlockMoments.lean` (registered) | 4 (L8 to L11) | +130 | Gaussian |
    | 6 | `RandomMatrix/Haar/Blocks.lean` (S4's) | 6 (A1 to A4, L12, L13) | +130 | Haar |
    | 7 | `Sketching/Gaussian/LeastSquares.lean` (new) | 14 (A5 to A17, A11') | 580 | Gaussian: A6 to A12, A11'; Haar: A5, A13 to A17 |
    | 8 | `LowRank/Gaussian/RangeFinder.lean` (registered) | 1 (D1) | +50 | Gaussian |
    | 9 | `LowRank/Gaussian/GeneralizedNystrom.lean` (new) | 13 (GN1 to GN8, GH1 to GH5) | 520 | Gaussian: GN1 to GN6, GN8; Haar: GN7, GH1 to GH5 |
    | 10 | `LowRank/Gaussian/TruncatedGeneralizedNystrom.lean` (new) | 7 (TG1 to TG7) | 400 | Gaussian |
    | 11 | `LowRank/Gaussian/EarlyTruncation.lean` (new, item 4) | 12 (ET1 to ET6, ER7 to ER12) | 470 | Gaussian: ET1, ET3, ET4, ET6; S6b: ER7 to ER12; Haar: ET2, ET5 |
    | 12 | `RandomMatrix/Gaussian/ExtremeSingularValues.lean` (registered) | 5 (ER1 to ER5) | +260 | S6b |
    | 13 | `LowRank/Random/RangeFinder.lean` (registered) | 1 (ER6) | +10 | S6b |

    70 public declarations: S6 58 (two definitions, 56 theorems; the drafted 57 plus A11') in files
    1 to 11, about 2220 lines; S6b 12 (two definitions, 10 theorems) in files 11 to 13, about 500
    lines. By file: 1, 2, 1, 3, 4, 6, 14, 1, 13, 7, 12, 5, 1. Every file stays under 1000 lines
    and 25 statements (`ExtremeSingularValues.lean` reaches about 705, `EarlyTruncation.lean`
    about 470). Four registry entries, each in the commit that defines its constant:
    `truncatedGNFactor` (item 2), `haarProjectionFactor` (item 3),
    `gaussianClippedInvMomentConstant` and `earlyTruncatedRSVDFactor` (item 13). Side files: as §4
    for files 1 to 5 and 8, `RandomMatrix/Gaussian/ClippedInverseMoments.lean` for file 12; file 6
    takes L12, L13 and A1 to A4 proved (S4's file, after S4). New result id `etrsvd` (the atlas
    id of brief §1) for ER10, ER11; ER12 joins `etgn`; ER1 to ER9 carry none.
