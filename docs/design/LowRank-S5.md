# Design note: LowRank stage S5, Nyström by the Gram correspondence

Status: drafted 2026-10-15 under `docs/PORT_LOWRANK.md` (maintainer decisions of 2026-10-15,
binding: Nyström results are proved through the Gram correspondence wherever that gives the same
constants, by transferring the range-finder results; every error spelled $\mathbf{H}$ minus the
named output, `H - nystrom H (X ω)`; late truncation written `truncatedSVD (nystrom H (X ω)) k`;
D3, D4 expectations first and tails second with `integrable_…` companions; D9 to D13; §4.2, §4.3
"Nyström (S5)", the S5 entry of §7, §9.3), `docs/design/LowRank-S0.md` to `LowRank-S3.md` (§8 of
each overrides its §3; S0 to S2a proved and registered; S3's `LowRank/Gaussian/{RangeFinder,
RotationInvariant}.lean` and `LowRank/Random/RangeFinder.lean` registered,
`LowRank/Gaussian/RangeFinderTail.lean` being finished, relied on through the names of S3 §3.7 and
§8, which match the file as it stands). Real field for every probabilistic statement (D3); the
law-free companions and the deterministic additions are over `𝕜`. Every shape, rank and target
rank; side conditions are those the sources need and no more (§3.0). Docstrings follow the
notation rule of 2026-10-15: named outputs are written $\mathsf{nystrom}(\mathbf{H}, \mathbf{X})$,
$\mathsf{rsvd}(\mathbf{A}, \mathbf{X})$, never the formula they unfold to; the prose of this note
keeps the sources' $\hat{\mathbf{H}}$ and $\mathbf{P}\mathbf{F}$. Reviewed 2026-10-15 (9 low, no
high or medium), amendments in §8, which overrides §0 to §7 where they disagree (§3 stays as
drafted); all nine accepted, none rejected, one corrected on inspection (§8 item 9, the scope of
the common step). Q1 decided as (a) (§8 item 10); Q2 to Q9 as recommended (§8 item 11). NI0 moves
to `LowRank/Gaussian/RotationInvariant.lean` (§8 item 1), so S5 adds to four registered files,
not five.

Departures from the brief, each argued below:
- **More than one file.** The brief has one file, `LowRank/Gaussian/Nystrom.lean`, about 400
  lines. S5 follows S3's split: law-free companions and the selector reduction
  (`LowRank/Random/Nystrom.lean`), Gaussian expectations (`LowRank/Gaussian/Nystrom.lean`),
  Gaussian tails (`LowRank/Gaussian/NystromTail.lean`), and the rotation-invariant twins beside
  S3's and S4's rotation-invariant statements in `LowRank/Gaussian/RotationInvariant.lean` (Q4).
  About 1070 lines, 36 public statements (§4).
- **MT Theorem 14.1 is promised with its constant** ($\lambda_{k+1}$, not $2\lambda_{k+1}$), as S2a
  Q6 already corrected: it is TYUC NeurIPS's own route, the trace bound plus reverse
  Eckart–Young (S2a's B16). The brief's "$2\lambda_{k+1}$" bound survives only as the $q = k$ case
  of a spectral-decay bound (TYUC NeurIPS Theorem 4.2 with constant one in place of two, NU4).
- **The square root never appears in a statement, and the proofs avoid it too.** Every statement
  is about a positive semidefinite $\mathbf{H}$ and its own best errors
  (`Φ.matrixNorm (H - truncatedSVD H k)`, `nuclearNorm (H - truncatedSVD H k)`,
  `singularValues H k`). The proofs write $\mathbf{H} = \mathbf{F}^{\mathsf{H}}\mathbf{F}$ for some
  factor (`CStarAlgebra.nonneg_iff_eq_star_mul_self`, S1's route) and apply S3 at $\mathbf{F}$.
  The best errors of $\mathbf{F}$ become those of $\mathbf{H}$ through a new choice-free Matrix
  lemma (M1, the gauge form of S2a's B20), which answers S1 §8 item 2's objection to the
  $\mathbf{H}^{1/2}$ route (the choice-dependent `truncatedSVD (CFC.sqrt H) k ^ 2 = truncatedSVD H k`
  is never used).
- **The spectral error of truncated Nyström is reached by reverse Eckart–Young, not by
  transferring S3's spectral truncated statements.** The constants agree, but S3's U2, P6 and P7
  are about best approximations of `rsvd F (X ω)`, and the spectral error of truncated Nyström is
  choice-dependent (§3.0's example), so no pointwise identity carries one to the other. One new
  deterministic inequality (D1) makes the trace route work for every choice.
- **TYUC NeurIPS Theorem 4.2 is added beyond the brief** (its two spectral-decay bounds),
  with constant one instead of two, from S2a's constant-one Nyström lemma (Q6).
- **S0 §8 item 14(d)'s handoff is met**: "Nyström helps" at the sample $\mathbf{H}\mathbf{\Omega}_0$
  (X1, X2) is stated, deterministic only (Q8).

**Literature checks** (PDFs: `~/Documents/prove2me/books/`, `/tmp/claude-1000/p0/papers/`;
TYUC NeurIPS arXiv:1706.05736 v1, EW arXiv:2605.19096 v2, TW arXiv:2306.12418 v3, MT printed page
= PDF + 402):
- TW Corollary 8.2 (p. 33, NysSVD1 and NysSVD2): real psd $\mathbf{A}$, target $r \ge 1$,
  $1 \le p \le \infty$, $k \ge r$ (tail), $k \ge r + 2$ (expectation),
  $\|\mathbf{A}-\hat{\mathbf{A}}\|_p \le \|\mathbf{A}-\lfloor\mathbf{A}\rfloor_r\|_p +
  \frac{utr}{k-r+1}\|\mathbf{A}-\lfloor\mathbf{A}\rfloor_r\|_*$ with failure
  $e^{-(u-2)/4} + \sqrt{\pi r}\,(t/e)^{-(k-r+1)/2}$, and the expectation with $\frac{r}{k-r-1}$.
  "The result for NysSVD is a corollary of the result for RSVD."
- TW Corollary 8.8 (p. 38): the trace bound $1 + \frac{r}{k-r-1}$ for $k \ge r + 2$, logarithmic and
  square-root bounds at $k \in \{r, r+1\}$, a spectral bound $(1 + \frac{2r}{k-r-1})\|\cdot\| +
  \frac{e^2}{k-r}\|\cdot\|_*$, and second-moment bounds for $k \ge r + 4$. Its proof is the
  $\mathbf{A}^{1/2}$ identity $\|\mathbf{A}-\mathbf{A}\langle\mathbf{\Omega}\rangle\|_p =
  \|(\mathbf{I}-\mathbf{\Pi})\mathbf{A}^{1/2}\|_{2p}^2$ applied to Theorem 8.7. Only the first case
  is in reach (S3 Q7 deferred Theorem 8.7).
- MT §14.2 to §14.4 (pp. 495 to 497): (14.1), $\mathbf{A}/\mathbf{X} = \mathbf{A} -
  \mathbf{A}\langle\mathbf{X}\rangle$, $\hat{\mathbf{A}}_k$ "a best rank-$k$ approximation of
  $\hat{\mathbf{A}}$ with respect to the Frobenius norm" (p. 496), Theorem 14.1 (p. 496):
  $1 \le k < \ell \le n$, standard normal over $\mathbb{F}$,
  $\mathbb{E}\|\mathbf{A}-\hat{\mathbf{A}}_k\| \le \lambda_{k+1} + \frac{k}{\ell-k-1}\sum_{j>k}
  \lambda_j$, credited to TYUC 2017a Theorem 4.1.
- TYUC NeurIPS: Theorem 4.1 (p. 5), $1 \le r < k \le n$, Gaussian **or orthonormal** test matrix,
  (4.1) $\mathbb{E}\|\mathbf{A}-\hat{\mathbf{A}}_r\|_1 \le (1+\frac{r}{k-r-\alpha})\|\mathbf{A}-
  \llbracket\mathbf{A}\rrbracket_r\|_1$, (4.2) $\mathbb{E}\|\mathbf{A}-\hat{\mathbf{A}}_r\|_\infty \le
  \|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_r\|_\infty + \frac{r}{k-r-\alpha}\|\mathbf{A}-
  \llbracket\mathbf{A}\rrbracket_r\|_1$, $\alpha(\mathbb{R}) = 1$; Theorem 4.2 (p. 6), (4.3), (4.4):
  the same with $2\min_{\varrho<k-\alpha}(1+\frac{\varrho}{k-\varrho-\alpha})\|\mathbf{A}-
  \llbracket\mathbf{A}\rrbracket_\varrho\|_1$ added to the best rank-$r$ error; Theorem A.1 (p. 9),
  the untruncated trace bound with $\min_\varrho$; Proposition A.2 (p. 9), the square-root form;
  Remark A.3 (p. 10), the spectral **half** moment from HMT 10.6; Remark A.4, high-probability
  bounds from HMT 10.7, 10.8, "We omit the details"; Proposition A.6 (p. 10); App. A.5 (p. 11), the
  proof of (4.1) through Gu's Theorem 3.5 and $\mathbb{E}\|(\mathbf{I}-\mathbf{P})
  \llbracket\mathbf{A}^{1/2}\rrbracket_r\|_2^2$; Proposition A.8 (p. 12) and the derivation of (4.2)
  from (4.1). App. A.5 asserts "With probability one, the nonzero eigenvalues of
  $\hat{\mathbf{A}}_{\mathrm{nys}}$ are all distinct": false for $\mathbf{A} = \mathbf{I}$, where
  $\hat{\mathbf{A}}_{\mathrm{nys}} = \mathbf{P}_{\mathbf{\Omega}}$ has $\ell$ eigenvalues equal to
  $1$ for every $\mathbf{\Omega}$ (Q10); the argument does not need it.
- EW: Definition 3.4 and Fact 3.5 (p. 8, the Gram correspondence in trace form); Theorem 3.1
  (p. 6, HMT 10.5 for full-rank rotation-invariant embeddings, a minimum over $q$); Theorem 3.6
  (p. 9), (a) the sharp Nyström upper bound (S4), (b) the lower bound (S10); Conjecture 7.1(c)
  (minimax over algorithms) is not a theorem. EW state no Nyström result beyond 3.6; "Theorems 3.2
  and 3.3 are equivalent to the following result for Nyström approximation". The Nyström twin of
  their Theorem 3.1 is NI2, by Fact 3.5.
- CEMT Imported Theorem 2.4 and Corollary 2.5 (p. 17): the Gram correspondence in trace form, and
  Nyström with an OSI; the latter is S7's.
- HMT §5.4 (Algorithm 5.5, p. 33): no error bound. Gittens 2011 and Gittens–Mahoney 2016 are not in
  hand and are not needed (S1's provenance note).

**Missing infrastructure, per result** (each is a statement of this note unless marked "not
reached"):
- Every untruncated expectation and tail (TW Corollary 8.2 for $1 \le p \le \infty$, the trace
  case of Corollary 8.8, TYUC Theorem A.1, their gauge generalisations, the rotation-invariant
  twins): one Matrix-layer identity, M1,
  $\|\mathbf{G}^{\mathsf{H}}\mathbf{G}-\llbracket\mathbf{G}^{\mathsf{H}}\mathbf{G}\rrbracket_k\|_\Phi
  = \|(\mathbf{G}-\llbracket\mathbf{G}\rrbracket_k)^{\mathsf{H}}(\mathbf{G}-
  \llbracket\mathbf{G}\rrbracket_k)\|_\Phi$. Everything else exists (S0's correspondence, S2a's
  B20, S3's G1, G2, G4, P1, P3, P4, I1, I2, P10).
- Truncated Nyström in trace (TYUC (4.1)): nothing (S2a's T7, S3's U1, P5, I4).
- MT Theorem 14.1 = TYUC (4.2), and the truncated spectral tails: one deterministic inequality, D1
  ($\|\mathbf{H}-\mathbf{Y}\|_* \le \|\mathbf{H}-\llbracket\hat{\mathbf{H}}\rrbracket_k\|_*$ for every
  best approximation $\mathbf{Y}$ of $\hat{\mathbf{H}}$), plus S2a's B16. The expectation needs a
  **measurable best-approximation selector**, which neither the library nor Mathlib has: the
  expectation statements are not instantiable now (§3.0, as S3's U2). The tails are.
- TYUC Theorem 4.2 with constant one: nothing (S2a's T2, B13, N1).
- Exact recovery and the rotation-invariant law of the output: nothing (S3's H2, H3; S0's
  `Matrix.PosSemidef.nystrom_eq`, `nystrom_eq_self_of_rank_eq`).
- Not reached: TW Corollary 8.8 at $k \in \{r, r+1\}$ (parallel sums, S3 Q7), its spectral bound
  (TW Lemma B.1, S6's to add, then about 20 lines here), its $k \ge r + 4$ bounds (fourth moments);
  complex test matrices, $\alpha(\mathbb{C}) = 0$ (D3); EW Theorem 3.6(a) (S4).

## 0. Scope and consumers

$\mathbf{H}$ : `Matrix n n ℝ`, positive semidefinite (`hH : H.PosSemidef`); the random test matrix
is `X : Ω → Matrix n l ℝ` on a sample space `Ω` (S3 Q8), $\ell = \lvert l\rvert$; the target or
comparison rank is `k : ℕ` (and `q : ℕ` where two ranks appear). Throughout,
$$\hat{\mathbf{H}} = \mathbf{H}\langle\mathbf{X}\rangle = \texttt{nystrom H (X ω)},\qquad
\operatorname{tr}_k := \|\mathbf{H}-\llbracket\mathbf{H}\rrbracket_k\|_* = \sum_{i \ge k}
\lambda_i(\mathbf{H}),\qquad \|\mathbf{H}-\llbracket\mathbf{H}\rrbracket_k\|_2 = \sigma_k(\mathbf{H})
= \lambda_k(\mathbf{H}),$$
indexed from $0$ as the library (MT's $\lambda_{k+1}$ is $\lambda_k$ here). The errors are
`H - nystrom H (X ω)` and `H - truncatedSVD (nystrom H (X ω)) k` (maintainer's rules). $d = \ell -
k + 1$ is `hd : k + d = Fintype.card l + 1` in the tails (S3).

| Item | Consumers |
|---|---|
| Gram-form Nyström expectation (NG1) and its trace, Schatten, spectral, Frobenius corollaries (NG2 to NG5) | Solvers (Nyström PCG, whose analysis uses the spectral error of the Nyström approximation, NG4); Estimation (Nyström trace estimators, NG2); S4 (EW 3.6(a) lands beside NG2 as a sharpening); users with kernel and Gram matrices (no square root in any statement) |
| truncated trace (NU1), MT 14.1 (NU2), the spectral-decay forms (NU3, NU4) | users of fixed-rank Nyström (TYUC NeurIPS's algorithm, MT Algorithm 16); Solvers (rank-$k$ Nyström preconditioners) |
| tails (NP1 to NP7) | users; S7 (comparison with CEMT Corollary 2.5's OSI tail) |
| law-free companions and the selector reduction (NL1 to NL8) | every expectation here; S4, S7 (any law: S4's 3.6(a) composes with NL8 to give the sharp MT 14.1 for rotation-invariant laws at no cost) |
| exact recovery (NE1, NI6) | users; S6 (the pattern of GN's a.s. exact branch) |
| rotation-invariant law of the output (NI0) and twins (NI1 to NI6) | S4 (EW 3.6(a) has the same hypotheses), users with Haar test matrices |
| M1 (gauge Gram truncation) | every gauge-form Nyström statement here (S4's trace transfer of EW 3.6(a) to 3.2 needs only its nuclear case, B20) |
| D1 (trace error under any choice) | NL7, NL8, NP6; S7 (the OSI form of MT 14.1) |
| X1, X2 ("Nyström helps" at the sample $\mathbf{H}\mathbf{\Omega}_0$) | S0 §8 item 14(d)'s handoff; docstrings comparing Nyström with the RSVD on the same data; Solvers |

Not in S5: EW's sharp bounds (S4), GN (S6), OSI routes (S7, CEMT Corollary 2.5), Nyström with power
iteration or Krylov (NysSI, NysBKI; brief §8), complex laws (D3), sample-size corollaries (no
consumer).

## 1. Objects

No definition, no new interface, no §5.3 row, no deviation from Mathlib. The objects are S0's
`nystrom`, S2a's `IsBestRankApprox`, S3's `gaussianProjectionFactor` and `gaussianPinvFrobTail`.
S3's two rows ("rotation-invariant random test matrix", "measurable best approximation of a random
output") are used verbatim; the second is instantiated at `nystrom H (X ω)` in place of
`rsvd A (X ω)`, which its wording ("a random output") covers.

**Used directly.** S0: `nystrom`, `conjTranspose_mul_self_sub_nystrom`,
`nuclearNorm_conjTranspose_mul_self_sub_nystrom`, `Matrix.PosSemidef.nystrom_eq`,
`Matrix.PosSemidef.sub_nystrom_eq` (docstrings; the proofs use the general factor),
`Matrix.PosSemidef.nystrom`, `.nystrom_le`, `.nystrom_eq_self_of_rank_eq`, `sub_rsvd`. S1:
`SymmetricGauge.matrixNorm_sub_nystrom_le_of_hasOrthonormalCols` (docstring comparison; its
`CStarAlgebra.nonneg_iff_eq_star_mul_self` step is the common step here). S2a:
`isBestRankApprox_truncatedSVD`, `IsBestRankApprox.rank_le`, `.matrixNorm_sub`,
`.matrixNorm_sub_le_add_of_singularValues_le` (B13),
`specNorm_sub_add_nuclearNorm_sub_truncatedSVD_le_of_rank_le` (B16),
`nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD` (B20),
`SymmetricGauge.matrixNorm_sub_truncatedSVD_nystrom_le` (T2),
`nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD_nystrom` (T7),
`Matrix.PosSemidef.truncatedSVD_nystrom_le` (T9), `Matrix.PosSemidef.singularValues_nystrom_le`
(N1), `Matrix.PosSemidef.singularValues_sub_nystrom_le`, `Matrix.PosSemidef.truncatedSVD`,
`Matrix.PosSemidef.truncatedSVD_le`. S3: `SymmetricGauge.integrable_matrixNorm_conjTranspose_mul_self_sub_rsvd`
(L1), `integrable_frobNorm_sub_truncatedSVD_rsvd_sq` (L7),
`SymmetricGauge.integral_matrixNorm_conjTranspose_mul_self_sub_rsvd_le_of_hasLaw_gaussianMatrix`
(G1), `integral_frobNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix` (G2),
`integral_specNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix` (G4),
`integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_hasLaw_gaussianMatrix` (U1),
`SymmetricGauge.measureReal_not_matrixNorm_conjTranspose_mul_self_sub_rsvd_le_le_of_hasLaw_gaussianMatrix`
(P1), `measureReal_not_frobNorm_sub_rsvd_sq_le_le_of_hasLaw_gaussianMatrix` (P3),
`measureReal_not_specNorm_sub_rsvd_sq_le_le_of_hasLaw_gaussianMatrix` (P4),
`measureReal_not_frobNorm_sub_truncatedSVD_rsvd_sq_le_le_of_hasLaw_gaussianMatrix` (P5), and the
rotation-invariant I1, I2, I4, P10 (`…_of_isLeftUnitarilyInvariant`),
`hasLaw_rangeProjector_mul_of_isLeftUnitarilyInvariant` (H2),
`ae_rank_mul_eq_min_of_isLeftUnitarilyInvariant` (H3), `gaussianProjectionFactor_def`,
`lpGauge_apply_single_zero`. Matrix layer: `singularValues_conjTranspose_mul_self`,
`singularValues_sub_truncatedSVD`, `specNorm_sub_truncatedSVD`, `specNorm_conjTranspose_mul_self`,
`nuclearNorm_conjTranspose_mul_self`, `schattenNorm_conjTranspose_mul_self`,
`specNorm_le_nuclearNorm`, `nuclearNorm_add_le`, `Matrix.PosSemidef.nuclearNorm_eq_re_trace`,
`SymmetricGauge.matrixNorm_congr`, `lpGauge_matrixNorm`, `lpGauge_one_matrixNorm`,
`lpGauge_top_matrixNorm`, `Matrix.star_eq_conjTranspose`. RandomMatrix:
`ae_rank_mul_eq_min_of_hasLaw_gaussianMatrix`. Mathlib: `CStarAlgebra.nonneg_iff_eq_star_mul_self`,
`MeasureTheory.integral_mono_ae`, `integral_add`, `integral_const`, `measureReal_mono`,
`HasLaw.comp`, `Measure.map_map`.

**Mathlib search** ("searched, none" unless named): Nyström approximation, Schur-complement error
bounds, randomized low-rank approximation of PSD matrices; a Gram identity for truncated SVDs (M1;
Mathlib has `LinearMap.singularValues` with `sq_singularValues_of_lt`, nothing on truncation).

## 2. Interfaces

No new predicate. Hypotheses, each an existing spelling:
- `hH : H.PosSemidef`, first explicit argument, so non-gauge statements live in
  `Matrix.PosSemidef` (CONTRIBUTING §5.2, dot notation; S2a's T8, T9 precedent) and gauge statements
  in `SymmetricGauge` with `Φ` first (S1 Q5, S3). Positive semidefiniteness is needed by the route
  ($\mathbf{H} = \mathbf{F}^{\mathsf{H}}\mathbf{F}$) and for boundedness: for Hermitian indefinite
  $\mathbf{H}$, $\|\hat{\mathbf{H}}\|_2$ is unbounded in $\mathbf{\Omega}$ (S2a §3's N1 example), so
  the integrability companions fail in general. A kernel matrix $\mathbf{F}^{\mathsf{H}}\mathbf{F}$
  is an instance (`Matrix.posSemidef_conjTranspose_mul_self F`); no general-factor twins (Q1).
- `HasLaw X (gaussianMatrix n l) μ` (D2); rotation-invariant: S3's row, `HasLaw X ν μ` with
  `[IsProbabilityMeasure ν] [IsLeftUnitarilyInvariant ν]` and
  `hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec`.
- `k + 2 ≤ Fintype.card l` for expectations, `hd : k + d = Fintype.card l + 1`, `u : ℝ`, `0 < t` for
  tails (S3); `q + 2 ≤ Fintype.card l` for the comparison rank of NU3, NU4.
- `IsBestRankApprox (nystrom H (X ω)) k (Y ω)` with `AEStronglyMeasurable Y μ` for the
  choice-dependent spectral expectations (S2a §8 item 15, S3 §3.0).
- `AEMeasurable X μ`, `[IsFiniteMeasure μ]` for the law-free companions.

## 3. Statement shapes

`namespace NLAlib`, `open MeasureTheory ProbabilityTheory`, `open scoped Matrix ENNReal`. Variables
`{Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n l : Type*} [Fintype n] [Fintype l]`,
`{H : Matrix n n ℝ} {X : Ω → Matrix n l ℝ}` (over `𝕜` in §3.2 and the Matrix additions). No
statement displays `1`, `CFC.sqrt` or a frame, so no `[DecidableEq]` except `[DecidableEq n]` with
`IsLeftUnitarilyInvariant` (its class needs it); proofs use `classical`. Docstrings are shortened;
the full ones carry §5's citations, LaTeX throughout, Lean names in backticks.

### 3.0 Degenerate cases, measurability, and the common step

**The common step** (every proof of §3.3 to §3.6). `obtain ⟨F, rfl⟩ :=
CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hH.nonneg`, `rw [Matrix.star_eq_conjTranspose]`; then
$\mathbf{H} = \mathbf{F}^{\mathsf{H}}\mathbf{F}$ with $\mathbf{F}$ : `Matrix n n ℝ`, and five
choice-free rewrites move every quantity to $\mathbf{F}$:

| | identity | lemma |
|---|---|---|
| R1 | $\mathbf{H}-\hat{\mathbf{H}} = (\mathbf{F}-\mathbf{P}_{\mathbf{F}\mathbf{X}}\mathbf{F})^{\mathsf{H}}(\mathbf{F}-\mathbf{P}_{\mathbf{F}\mathbf{X}}\mathbf{F})$ | `conjTranspose_mul_self_sub_nystrom F (X ω)` (S0) |
| R2 | $\Phi(\mathbf{H}-\llbracket\mathbf{H}\rrbracket_k) = \Phi((\mathbf{F}-\llbracket\mathbf{F}\rrbracket_k)^{\mathsf{H}}(\mathbf{F}-\llbracket\mathbf{F}\rrbracket_k))$ | M1 (new, §3.1) |
| R3 | $\operatorname{tr}_k = \|\mathbf{F}-\llbracket\mathbf{F}\rrbracket_k\|_{\mathsf{F}}^2$ | `nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD F k` (B20) |
| R4 | $\|\mathbf{H}-\llbracket\hat{\mathbf{H}}\rrbracket_k\|_* = \|\mathbf{F}-\llbracket\mathbf{P}_{\mathbf{F}\mathbf{X}}\mathbf{F}\rrbracket_k\|_{\mathsf{F}}^2$ | `nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD_nystrom F (X ω) k` (T7) |
| R5 | $\sigma_k(\mathbf{H}) = \sigma_k(\mathbf{F})^2$ | `singularValues_conjTranspose_mul_self F k` |

With them each Nyström statement is a range-finder statement of S3 at $\mathbf{A} = \mathbf{F}$,
rewritten under the integral or inside the event (`integral_congr`, `Set.ext` by `simp only`);
§3.7's table lists which.

**Degenerate cases** (checked for every statement; the per-section routes say where a case bites).
- *$\ell \in \{k, k+1\}$.* The expectations need `k + 2 ≤ card l`: S3 §3.0's counterexample
  transfers verbatim. For $\mathbf{F} = \operatorname{diag}(1, \delta, \delta)$,
  $\mathbf{H} = \operatorname{diag}(1, \delta^2, \delta^2)$, $k = 1$, $\ell = 2$: $\|\mathbf{H} -
  \hat{\mathbf{H}}\|_* = \|\mathbf{F}-\mathbf{P}\mathbf{F}\|_{\mathsf{F}}^2$, whose expectation is not
  bounded by any multiple of $\operatorname{tr}_1 = 2\delta^2$ as $\delta \to 0$; Lean's $k/0 = 0$
  would make NG2 claim the multiple $1$. The tails need only `hd` (S3); at $d = 0$ the failure
  bound is at least $2$.
- *$k = 0$.* $\llbracket\mathbf{H}\rrbracket_0 = \mathbf{0}$, $\operatorname{tr}_0 =
  \|\mathbf{H}\|_*$, $\sigma_0(\mathbf{H}) = \|\mathbf{H}\|_2$, excess terms $0$. Untruncated
  statements reduce to $\|\mathbf{H}-\hat{\mathbf{H}}\|_\Phi \le \|\mathbf{H}\|_\Phi$, true pointwise
  ($\mathbf{0} \preceq \mathbf{H}-\hat{\mathbf{H}} \preceq \mathbf{H}$, Weyl). Truncated: the output is
  $\mathbf{0}$ and every best rank-$0$ approximation is $\mathbf{0}$, so NU1 is the equality
  $\|\mathbf{H}\|_* = \|\mathbf{H}\|_*$, NU2 is $\|\mathbf{H}\|_2 \le \sigma_0(\mathbf{H})$, equality.
- *$\operatorname{rank}\mathbf{H} \le k$.* Every right side is $0$ ($\sigma_k = 0$,
  $\operatorname{tr}_k = 0$). Since $k \le \ell$, $\operatorname{rank}(\mathbf{H}\mathbf{X}) =
  \operatorname{rank}\mathbf{H}$ a.s. (RandomMatrix's a.s. rank), so $\hat{\mathbf{H}} = \mathbf{H}$ a.s.
  (NE1), $\llbracket\mathbf{H}\rrbracket_k = \mathbf{H}$, and every best approximation $\mathbf{Y}$ of
  $\mathbf{H}$ is $\mathbf{H}$ (S2a B7): left sides $0$ a.s. The tails' failure events are written
  $\neg(\text{error} \le \text{bound})$ for this reason (S3 Q10). In the tails `hd` admits
  $k = \ell + 1$, where $\operatorname{rank}\mathbf{H} \le k$ no longer forces exactness, but
  $d = 0$ makes the bound at least $2$.
- *$k > \lvert n\rvert$.* Then $\operatorname{rank}\mathbf{H} < k$, the previous case; inherited
  from S3 (no `k ≤ card n` hypothesis).
- *More samples than the dimension, $\ell > \lvert n\rvert$.* Gaussian statements hold (exact a.s.);
  the rotation-invariant hypothesis `hXr` is unsatisfiable there, so NI1 to NI6 are vacuous, as S3's.
- *Empty index types.* $n$ empty: $\mathbf{H} = \mathbf{0}$, statements $0 \le 0$ or empty events.
  $l$ empty: excluded from expectations by `hk`; in the tails `hd` forces $(k, d) \in \{(0,1),
  (1,0)\}$, both handled above.
- *Ties* $\lambda_{k-1}(\hat{\mathbf{H}}) = \lambda_k(\hat{\mathbf{H}})$: below.
- *Hermitian but not PSD $\mathbf{H}$.* Excluded by `hH` (§2). For the expectations a counterexample
  would need an integrable failure (the integral of a non-integrable function is $0$ in Lean); none
  is claimed. The hypothesis is the sources' and the route's.
- *Tail parameters.* `0 < t` as S3 (at $t = 0$ the failure term is Lean's $0$); $u$ free.
- *Two ranks* (NU3, NU4): `q + 2 ≤ card l` is necessary for the same reason as `hk`; $k$ is free
  ($k \ge \ell$ makes $\llbracket\hat{\mathbf{H}}\rrbracket_k = \hat{\mathbf{H}}$, and T2 reduces to
  $\|\mathbf{H}-\hat{\mathbf{H}}\| \le \|\mathbf{H}-\llbracket\mathbf{H}\rrbracket_k\| +
  \|\mathbf{H}-\hat{\mathbf{H}}\|$).
- *Schatten order* $p < 1$: excluded (`hp : 1 ≤ p`, `lpGauge` needs it); TW's range is
  $1 \le p \le \infty$.

**Measurability of truncated outputs** (S2a §8 item 15, S3 §3.0; decided there).
1. **Choice-free, stated on the named output with `integrable_` companions.** Every untruncated
   error (a measurable function of $\mathbf{X}$ through R1 and S3's L1); the trace error of
   truncated Nyström, by R4 (T7) equal to S3's choice-free truncated Frobenius error of the RSVD of
   $\mathbf{F}$ (L7). Affected statements: none. NU1, NU3, NP5, NI3 are on
   `H - truncatedSVD (nystrom H (X ω)) k` directly.
2. **Choice-dependent expectations take a measurable selector and are not instantiable now.** The
   spectral error of truncated Nyström (MT 14.1) depends on the choice. Example (S2a §8 item 2's,
   through the correspondence): $\mathbf{F} = \begin{bmatrix} 1 & 0 & 0 \\ 0 & 1 & \tfrac12 \\ 0 & 0
   & \tfrac12 \end{bmatrix}$, $\mathbf{H} = \mathbf{F}^{\mathsf{H}}\mathbf{F} = \begin{bmatrix} 1 & 0 &
   0 \\ 0 & 1 & \tfrac12 \\ 0 & \tfrac12 & \tfrac12 \end{bmatrix}$, $\mathbf{\Omega} =
   [\mathbf{e}_1\ \mathbf{e}_3]$, $k = 1$. Then $\hat{\mathbf{H}} = (\mathbf{P}\mathbf{F})^{\mathsf{H}}
   \mathbf{P}\mathbf{F} = \mathbf{e}_1\mathbf{e}_1^{\mathsf{H}} + \mathbf{u}\mathbf{u}^{\mathsf{H}}$,
   $\mathbf{u} = (0, 1, 1)/\sqrt2$, eigenvalues $(1, 1, 0)$. The best rank-1 approximations
   $\mathbf{e}_1\mathbf{e}_1^{\mathsf{H}}$ and $\mathbf{u}\mathbf{u}^{\mathsf{H}}$ give spectral errors
   $(3+\sqrt5)/4 \approx 1.309$ and $1$ (the eigenvalues of $\begin{bmatrix} 1 & \frac12 \\ \frac12 &
   \frac12\end{bmatrix}$, and $\operatorname{diag}(1, \frac12, 0)$), and trace errors $\frac32$ both
   (T7). Checked by hand. So NU2, NU4, NI4 take `(hY : ∀ ω, IsBestRankApprox (nystrom H (X ω)) k
   (Y ω)) (hYm : AEStronglyMeasurable Y μ)`, with companion NL7 and the law-free reduction NL8;
   each docstring says that no such `Y` can be exhibited yet. **No bound-only expectation of
   `specNorm (H - truncatedSVD (nystrom H (X ω)) k)` is stated** (S3 §3.0 item 2:
   `MeasureTheory.integral_undef`).
3. **Choice-dependent tails need no selector and are instantiable.** NP6 (any best approximation,
   no measurability) and NP7 (`truncatedSVD`) include their failure event in NP5's measurable one,
   so `μ.real` (the outer measure) is bounded by NP5's bound; each docstring says so and that the
   success-set form does not follow without measurability (S3 §8 item 5).

### 3.1 Matrix layer and lower layers (5)

Labels M1, D1, X1, X2, NI0. Homes and reasons in §4; each home is a registered, proved file, so each
statement is written proved there or goes to the side file named in §4 (S3 §8 item 15's rule).

```lean
/-- **Truncation commutes with the Gram map in every unitarily invariant norm**:
$$\|\mathbf{G}^{\mathsf{H}}\mathbf{G}-\llbracket\mathbf{G}^{\mathsf{H}}\mathbf{G}\rrbracket_k\|_{\Phi}
= \|(\mathbf{G}-\llbracket\mathbf{G}\rrbracket_k)^{\mathsf{H}}(\mathbf{G}-
\llbracket\mathbf{G}\rrbracket_k)\|_{\Phi}\,,$$
for every choice of either truncation: both matrices have the singular values
$\sigma_{k+i}(\mathbf{G})^2$. The nuclear case is
`nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD`.
[TroppYurtseverUdellCevher2017a, App. A.5]; [TroppWebber2023, proof of Corollary 8.8]; there the
trace and the Schatten forms implicitly inside proofs, with $\mathbf{G} = \mathbf{A}^{1/2}$. -/
theorem SymmetricGauge.matrixNorm_conjTranspose_mul_self_sub_truncatedSVD (Φ : SymmetricGauge)
    (G : Matrix m n 𝕜) (k : ℕ) :
    Φ.matrixNorm (Gᴴ * G - truncatedSVD (Gᴴ * G) k) =
      Φ.matrixNorm ((G - truncatedSVD G k)ᴴ * (G - truncatedSVD G k))

/-- **The trace error of truncated Nyström under any choice of the truncation**: for positive
semidefinite $\mathbf{H}$ and any best rank-$k$ approximation $\mathbf{Y}$ of
$\mathsf{nystrom}(\mathbf{H}, \mathbf{\Omega})$,
$\|\mathbf{H}-\mathbf{Y}\|_* \le \|\mathbf{H}-\llbracket\mathsf{nystrom}(\mathbf{H}, \mathbf{\Omega})
\rrbracket_k\|_*$, the choice-free value of
`nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD_nystrom`. (Equality holds, since every best
approximation of a positive semidefinite matrix is positive semidefinite; it is not needed.) -/
theorem _root_.Matrix.PosSemidef.nuclearNorm_sub_le_nuclearNorm_sub_truncatedSVD_nystrom_of_isBestRankApprox
    {H : Matrix n n 𝕜} (hH : H.PosSemidef) {Ω : Matrix n l 𝕜} {k : ℕ} {Y : Matrix n n 𝕜}
    (hY : IsBestRankApprox (nystrom H Ω) k Y) :
    nuclearNorm (H - Y) ≤ nuclearNorm (H - truncatedSVD (nystrom H Ω) k)

/-- **Nyström helps, on the randomized SVD's data**: for positive semidefinite $\mathbf{H}$, the
Nyström approximation with test matrix $\mathbf{H}\mathbf{\Omega}$ is at least as accurate as the
randomized SVD of $\mathbf{H}$ with test matrix $\mathbf{\Omega}$, at every singular value:
$\sigma_k(\mathbf{H}-\mathsf{nystrom}(\mathbf{H}, \mathbf{H}\mathbf{\Omega})) \le
\sigma_k(\mathbf{H}-\mathsf{rsvd}(\mathbf{H}, \mathbf{\Omega}))$.
[TroppWebber2023, Lemma 5.2]. Result: nystrom-helps -/
theorem _root_.Matrix.PosSemidef.singularValues_sub_nystrom_mul_le_singularValues_sub_rsvd
    {H : Matrix n n 𝕜} (hH : H.PosSemidef) (Ω : Matrix n l 𝕜) (k : ℕ) :
    singularValues (H - nystrom H (H * Ω)) k ≤ singularValues (H - rsvd H Ω) k
/-- The same in every unitarily invariant norm. [TroppWebber2023, Lemma 5.2].
Result: nystrom-helps -/
theorem SymmetricGauge.matrixNorm_sub_nystrom_mul_le_matrixNorm_sub_rsvd (Φ : SymmetricGauge)
    {H : Matrix n n 𝕜} (hH : H.PosSemidef) (Ω : Matrix n l 𝕜) :
    Φ.matrixNorm (H - nystrom H (H * Ω)) ≤ Φ.matrixNorm (H - rsvd H Ω)

/-- **Nyström with a rotation-invariant test matrix has the Gaussian law**: for positive
semidefinite $\mathbf{H}$ and $\mathbf{X}$ with a left unitarily invariant law and full column rank
almost surely, $\mathsf{nystrom}(\mathbf{H}, \mathbf{X})$ has the law of
$\mathsf{nystrom}(\mathbf{H}, \mathbf{G})$ for a standard Gaussian $\mathbf{G}$. Nyström depends on the
test matrix only through $\mathbf{P}_{\mathbf{H}^{1/2}\mathbf{X}}$.
[TroppYurtseverUdellCevher2017a, Proposition A.2 and proof of Theorem A.1];
[EpperlyWebber2026, Fact 6.1(b)]. Result: gaussian-haar-range-transfer -/
theorem _root_.Matrix.PosSemidef.hasLaw_nystrom_of_isLeftUnitarilyInvariant [DecidableEq n]
    {ν : Measure (Matrix n l ℝ)} [IsProbabilityMeasure ν] [IsLeftUnitarilyInvariant ν]
    {H : Matrix n n ℝ} (hH : H.PosSemidef) {X : Ω → Matrix n l ℝ} (hX : HasLaw X ν μ)
    (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) :
    HasLaw (fun ω => nystrom H (X ω)) ((gaussianMatrix n l).map (nystrom H)) μ
```

Proof routes. *M1:* `Φ.matrixNorm_congr`, `funext i`; left
$\sigma_i = \sigma_{k+i}(\mathbf{G}^{\mathsf{H}}\mathbf{G})$ (`singularValues_sub_truncatedSVD`)
$= \sigma_{k+i}(\mathbf{G})^2$ (`singularValues_conjTranspose_mul_self`), right
$\sigma_i(\mathbf{G}-\llbracket\mathbf{G}\rrbracket_k)^2 = \sigma_{k+i}(\mathbf{G})^2$; B20's proof
already does it inside a sum. B20 then reads as M1 at `lpGauge 1` (kept, rule 6: S2a and T7 cite
it). Degenerate: $k = 0$ gives $\Phi(\mathbf{G}^{\mathsf{H}}\mathbf{G}) = \Phi(\mathbf{G}^{\mathsf{H}}
\mathbf{G})$. *D1:* `nuclearNorm_add_le` on $(\mathbf{H}-\hat{\mathbf{H}}) + (\hat{\mathbf{H}}-
\mathbf{Y})$; `hY.matrixNorm_sub (lpGauge 1 le_rfl)` with `lpGauge_one_matrixNorm` replaces
$\|\hat{\mathbf{H}}-\mathbf{Y}\|_*$ by $\|\hat{\mathbf{H}}-\llbracket\hat{\mathbf{H}}\rrbracket_k\|_*$;
the two pieces $\mathbf{H}-\hat{\mathbf{H}}$ (`hH.nystrom_le`) and $\hat{\mathbf{H}}-
\llbracket\hat{\mathbf{H}}\rrbracket_k$ (`(hH.nystrom Ω).truncatedSVD_le k`) are PSD, so their
nuclear norms add (`Matrix.PosSemidef.nuclearNorm_eq_re_trace` three times, `Matrix.trace_add`), the
step of T7's proof. Degenerate: $k = 0$, $\mathbf{Y} = \mathbf{0}$: equality. *X1:* S0 §8 item
14(d): `hH.singularValues_sub_nystrom_le (H * Ω) k`, then `sub_rsvd` (under `classical`). *X2:*
`Φ.matrixNorm_le_of_singularValues_le` and X1. *NI0:* `hH.nystrom_eq` writes
`nystrom H Ω = g (rangeProjector (CFC.sqrt H * Ω))` for every $\mathbf{\Omega}$, with $g(\mathbf{P}) =
\mathbf{H}^{1/2}\mathbf{P}\mathbf{H}^{1/2}$ continuous; H2 at $\mathbf{A} = \mathbf{H}^{1/2}$ and
`HasLaw.comp` give the law `((gaussianMatrix n l).map fun G => rangeProjector (CFC.sqrt H * G)).map g`,
which `Measure.map_map` (`measurable_rangeProjector`) and `funext` with `hH.nystrom_eq` turn into
`(gaussianMatrix n l).map (nystrom H)`. The square root is internal (`classical` for its
instance). Degenerate: $l$ empty, both laws are Dirac masses.

### 3.2 `LowRank/Random/Nystrom.lean`: law-free companions and the selector reduction (8)

Over `𝕜`, any law: `{H : Matrix n n 𝕜} {X : Ω → Matrix n l 𝕜}`. Labels NL1 to NL8.

```lean
/-- The Nyström error of a positive semidefinite matrix is integrable in every unitarily invariant
norm, for every measurable test matrix: it is measurable and bounded by $\|\mathbf{H}\|_{\Phi}$. -/
theorem SymmetricGauge.integrable_matrixNorm_sub_nystrom (Φ : SymmetricGauge) [IsFiniteMeasure μ]
    (hH : H.PosSemidef) (hX : AEMeasurable X μ) :
    Integrable (fun ω => Φ.matrixNorm (H - nystrom H (X ω))) μ
theorem _root_.Matrix.PosSemidef.integrable_schattenNorm_sub_nystrom [IsFiniteMeasure μ]
    (hH : H.PosSemidef) {q : ℝ≥0∞} (hq : 1 ≤ q) (hX : AEMeasurable X μ) :
    Integrable (fun ω => schattenNorm q (H - nystrom H (X ω))) μ
theorem _root_.Matrix.PosSemidef.integrable_nuclearNorm_sub_nystrom [IsFiniteMeasure μ]
    (hH : H.PosSemidef) (hX : AEMeasurable X μ) :
    Integrable (fun ω => nuclearNorm (H - nystrom H (X ω))) μ
theorem _root_.Matrix.PosSemidef.integrable_frobNorm_sub_nystrom [IsFiniteMeasure μ]
    (hH : H.PosSemidef) (hX : AEMeasurable X μ) :
    Integrable (fun ω => frobNorm (H - nystrom H (X ω))) μ
theorem _root_.Matrix.PosSemidef.integrable_specNorm_sub_nystrom [IsFiniteMeasure μ]
    (hH : H.PosSemidef) (hX : AEMeasurable X μ) :
    Integrable (fun ω => specNorm (H - nystrom H (X ω))) μ
/-- The trace error of truncated Nyström is integrable for every measurable test matrix. It does
not depend on the choice made by `truncatedSVD`
(`nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD_nystrom`), which is what makes it
measurable. -/
theorem _root_.Matrix.PosSemidef.integrable_nuclearNorm_sub_truncatedSVD_nystrom
    [IsFiniteMeasure μ] (hH : H.PosSemidef) (hX : AEMeasurable X μ) (k : ℕ) :
    Integrable (fun ω => nuclearNorm (H - truncatedSVD (nystrom H (X ω)) k)) μ
/-- For a measurable choice $\mathbf{Y}$ of best rank-$k$ approximations of
$\mathsf{nystrom}(\mathbf{H}, \mathbf{X})$, $\|\mathbf{H}-\mathbf{Y}\|_2$ is integrable (bounded by
$\|\mathbf{H}\|_*$). The library has no measurable selector yet, so this cannot be applied to
`truncatedSVD (nystrom H (X ω)) k`. -/
theorem _root_.Matrix.PosSemidef.integrable_specNorm_sub_of_isBestRankApprox_nystrom
    [IsFiniteMeasure μ] (hH : H.PosSemidef) {k : ℕ} {Y : Ω → Matrix n n 𝕜}
    (hY : ∀ ω, IsBestRankApprox (nystrom H (X ω)) k (Y ω)) (hYm : AEStronglyMeasurable Y μ) :
    Integrable (fun ω => specNorm (H - Y ω)) μ
/-- **Reverse Eckart–Young for truncated Nyström, in expectation**: for every law and a measurable
choice $\mathbf{Y}$ of best rank-$k$ approximations of $\mathsf{nystrom}(\mathbf{H}, \mathbf{X})$,
$$\mathbb{E}\|\mathbf{H}-\mathbf{Y}\|_2 + \|\mathbf{H}-\llbracket\mathbf{H}\rrbracket_k\|_* \le
\sigma_k(\mathbf{H}) + \mathbb{E}\|\mathbf{H}-\llbracket\mathsf{nystrom}(\mathbf{H}, \mathbf{X})
\rrbracket_k\|_*\,:$$
a trace bound for truncated Nyström becomes a spectral one at no cost. Not instantiable until a
measurable selector exists. [TroppYurtseverUdellCevher2017a, Proposition A.8 and App. A.6];
[Gu2015, Theorem 3.4]. -/
theorem _root_.Matrix.PosSemidef.integral_specNorm_sub_add_nuclearNorm_sub_truncatedSVD_le_of_isBestRankApprox_nystrom
    [IsProbabilityMeasure μ] (hH : H.PosSemidef) (hX : AEMeasurable X μ) {k : ℕ}
    {Y : Ω → Matrix n n 𝕜} (hY : ∀ ω, IsBestRankApprox (nystrom H (X ω)) k (Y ω))
    (hYm : AEStronglyMeasurable Y μ) :
    ∫ ω, specNorm (H - Y ω) ∂μ + nuclearNorm (H - truncatedSVD H k) ≤
      singularValues H k + ∫ ω, nuclearNorm (H - truncatedSVD (nystrom H (X ω)) k) ∂μ
```

Proof routes. *NL1:* the common step; the integrand is, by R1 under `funext`, S3's L1 integrand at
$\mathbf{A} = \mathbf{F}$. *NL2 to NL5:* NL1 at `lpGauge q`, `lpGauge 1`, `lpGauge 2`, `lpGauge ⊤`
(`lpGauge_matrixNorm`, `lpGauge_one_matrixNorm`, `schattenNorm_two`, `lpGauge_top_matrixNorm`).
*NL6:* the common step and R4 turn the integrand into L7's at $\mathbf{F}$. *NL7:* measurability
from `hYm` and continuity of $\mathbf{M} \mapsto \|\mathbf{H}-\mathbf{M}\|_2$; the bound
$\|\mathbf{H}-\mathbf{Y}\|_2 \le \|\mathbf{H}-\mathbf{Y}\|_*$ (`specNorm_le_nuclearNorm`)
$\le \|\mathbf{H}-\llbracket\hat{\mathbf{H}}\rrbracket_k\|_*$ (D1) $= \operatorname{Re}\operatorname{tr}
(\mathbf{H}-\llbracket\hat{\mathbf{H}}\rrbracket_k) \le \operatorname{Re}\operatorname{tr}\mathbf{H} =
\|\mathbf{H}\|_*$ (T9, `Matrix.PosSemidef.truncatedSVD` at `hH.nystrom`); `Integrable.of_bound`; no
measurability of `X` is used. *NL8:* pointwise B16 at $\mathbf{B} = \mathbf{Y}(\omega)$
(`(hY ω).rank_le`), then D1; integrate (`integral_add`, `integral_const`, `integral_mono` with NL7,
NL6). Degenerate: $k = 0$, $\mathbf{Y} = \mathbf{0}$: $\|\mathbf{H}\|_2 + \|\mathbf{H}\|_* \le
\sigma_0(\mathbf{H}) + \|\mathbf{H}\|_*$, equality.

### 3.3 `LowRank/Gaussian/Nystrom.lean`: Gaussian expectations (10)

Real, `(hX : HasLaw X (gaussianMatrix n l) μ)`. Labels NE1, NG1 to NG5, NU1 to NU4.

```lean
/-- **A Gaussian sketch at least as wide as the rank makes Nyström exact**: if
$\operatorname{rank}\mathbf{H} \le \ell$, then $\mathsf{nystrom}(\mathbf{H}, \mathbf{X}) = \mathbf{H}$
almost surely. -/
theorem _root_.Matrix.PosSemidef.ae_nystrom_eq_self_of_hasLaw_gaussianMatrix (hH : H.PosSemidef)
    (hX : HasLaw X (gaussianMatrix n l) μ) (hHl : H.rank ≤ Fintype.card l) :
    ∀ᵐ ω ∂μ, nystrom H (X ω) = H

/-- **The expected error of randomized Nyström, every unitarily invariant norm**: for positive
semidefinite $\mathbf{H}$, a standard Gaussian $n \times \ell$ test matrix and $k + 2 \le \ell$,
$$\mathbb{E}\|\mathbf{H}-\mathsf{nystrom}(\mathbf{H}, \mathbf{X})\|_{\Phi} \le
\|\mathbf{H}-\llbracket\mathbf{H}\rrbracket_k\|_{\Phi} + \Phi(\mathbf{e}_0)\,\frac{k}{\ell-k-1}\,
\|\mathbf{H}-\llbracket\mathbf{H}\rrbracket_k\|_*\,,$$
with $\Phi(\mathbf{e}_0) = 1$ for every Schatten norm. The Gram form of the randomized SVD's
expected error, transferred by the Gram correspondence with the same constant; no square root.
[TroppWebber2023, Corollary 8.2 (NysSVD2)]; [MartinssonTropp2020, §14.4];
[TroppYurtseverUdellCevher2017a, Theorem A.1]; there Schatten $1 \le p \le \infty$ (TW) or the
trace (TYUC), here every unitarily invariant norm, with the factor $\Phi(\mathbf{e}_0)$.
Result: randomized-nystrom-expected-error -/
theorem SymmetricGauge.integral_matrixNorm_sub_nystrom_le_of_hasLaw_gaussianMatrix
    (Φ : SymmetricGauge) (hH : H.PosSemidef) (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ}
    (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, Φ.matrixNorm (H - nystrom H (X ω)) ∂μ ≤
      Φ.matrixNorm (H - truncatedSVD H k) +
        Φ (Finsupp.single 0 1) * ((k : ℝ) / ((Fintype.card l : ℝ) - k - 1)) *
          nuclearNorm (H - truncatedSVD H k)
/-- **..., trace** (TYUC Theorem A.1 at one rank; TW Corollary 8.8, first case):
$$\mathbb{E}\|\mathbf{H}-\mathsf{nystrom}(\mathbf{H}, \mathbf{X})\|_* \le
\Bigl(1+\frac{k}{\ell-k-1}\Bigr)\|\mathbf{H}-\llbracket\mathbf{H}\rrbracket_k\|_*\,;$$
the error is positive semidefinite, so this is $\mathbb{E}\operatorname{tr}(\mathbf{H}-
\mathsf{nystrom}(\mathbf{H}, \mathbf{X}))$. The minimum over $k$ of the sources is not stated.
Result: randomized-nystrom-expected-error -/
theorem _root_.Matrix.PosSemidef.integral_nuclearNorm_sub_nystrom_le_of_hasLaw_gaussianMatrix
    (hH : H.PosSemidef) (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ}
    (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, nuclearNorm (H - nystrom H (X ω)) ∂μ ≤
      gaussianProjectionFactor k (Fintype.card l) * nuclearNorm (H - truncatedSVD H k)
/-- **..., Schatten norms** (TW Corollary 8.2 (NysSVD2), $1 \le p \le \infty$).
Result: randomized-nystrom-expected-error -/
theorem _root_.Matrix.PosSemidef.integral_schattenNorm_sub_nystrom_le_of_hasLaw_gaussianMatrix
    (hH : H.PosSemidef) (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ}
    (hk : k + 2 ≤ Fintype.card l) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    ∫ ω, schattenNorm p (H - nystrom H (X ω)) ∂μ ≤
      schattenNorm p (H - truncatedSVD H k) +
        (k : ℝ) / ((Fintype.card l : ℝ) - k - 1) * nuclearNorm (H - truncatedSVD H k)
/-- **..., spectral norm**: $\mathbb{E}\|\mathbf{H}-\mathsf{nystrom}(\mathbf{H}, \mathbf{X})\|_2 \le
\lambda_k(\mathbf{H}) + \frac{k}{\ell-k-1}\|\mathbf{H}-\llbracket\mathbf{H}\rrbracket_k\|_*$
(eigenvalues from $0$), the second moment of the randomized SVD's spectral error of a factor.
[TroppWebber2023, Corollary 8.2 (NysSVD2) at $p = \infty$].
Result: randomized-nystrom-expected-error -/
theorem _root_.Matrix.PosSemidef.integral_specNorm_sub_nystrom_le_of_hasLaw_gaussianMatrix
    (hH : H.PosSemidef) (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ}
    (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, specNorm (H - nystrom H (X ω)) ∂μ ≤
      singularValues H k +
        (k : ℝ) / ((Fintype.card l : ℝ) - k - 1) * nuclearNorm (H - truncatedSVD H k)
/-- **..., Frobenius norm** (TW Corollary 8.2 (NysSVD2) at $p = 2$).
Result: randomized-nystrom-expected-error -/
theorem _root_.Matrix.PosSemidef.integral_frobNorm_sub_nystrom_le_of_hasLaw_gaussianMatrix
    (hH : H.PosSemidef) (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ}
    (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, frobNorm (H - nystrom H (X ω)) ∂μ ≤
      frobNorm (H - truncatedSVD H k) +
        (k : ℝ) / ((Fintype.card l : ℝ) - k - 1) * nuclearNorm (H - truncatedSVD H k)

/-- **The expected trace error of truncated Nyström** (fixed-rank Nyström): for every choice of the
truncation,
$$\mathbb{E}\|\mathbf{H}-\llbracket\mathsf{nystrom}(\mathbf{H}, \mathbf{X})\rrbracket_k\|_* \le
\Bigl(1+\frac{k}{\ell-k-1}\Bigr)\|\mathbf{H}-\llbracket\mathbf{H}\rrbracket_k\|_*\,.$$
[TroppYurtseverUdellCevher2017a, Theorem 4.1 (4.1)]; there with $1 \le k$ and $\ell \le n$, neither
needed here, and through Gu's Theorem 3.5, here through Woodruff's truncation for free.
Result: randomized-nystrom-expected-error -/
theorem _root_.Matrix.PosSemidef.integral_nuclearNorm_sub_truncatedSVD_nystrom_le_of_hasLaw_gaussianMatrix
    (hH : H.PosSemidef) (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ}
    (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, nuclearNorm (H - truncatedSVD (nystrom H (X ω)) k) ∂μ ≤
      gaussianProjectionFactor k (Fintype.card l) * nuclearNorm (H - truncatedSVD H k)
/-- **The expected spectral error of truncated Nyström** (MT Theorem 14.1), for a measurable
choice $\mathbf{Y}$ of best rank-$k$ approximations of $\mathsf{nystrom}(\mathbf{H}, \mathbf{X})$:
$$\mathbb{E}\|\mathbf{H}-\mathbf{Y}\|_2 \le \lambda_k(\mathbf{H}) + \frac{k}{\ell-k-1}
\|\mathbf{H}-\llbracket\mathbf{H}\rrbracket_k\|_*\,,$$
eigenvalues from $0$ (MT's $\lambda_{k+1}$). Not instantiable yet: no measurable selector can be
exhibited, and `truncatedSVD (nystrom H (X ω)) k` is not known to be measurable; the expectation of
its spectral error is not stated (the integral of a non-integrable function is $0$).
[MartinssonTropp2020, Theorem 14.1]; [TroppYurtseverUdellCevher2017a, Theorem 4.1 (4.2)]; there with
$1 \le k < \ell \le n$; here $k + 2 \le \ell$, any $n$.
Result: randomized-nystrom-expected-error -/
theorem _root_.Matrix.PosSemidef.integral_specNorm_sub_le_of_isBestRankApprox_nystrom_of_hasLaw_gaussianMatrix
    (hH : H.PosSemidef) (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ}
    (hk : k + 2 ≤ Fintype.card l) {Y : Ω → Matrix n n ℝ}
    (hY : ∀ ω, IsBestRankApprox (nystrom H (X ω)) k (Y ω)) (hYm : AEStronglyMeasurable Y μ) :
    ∫ ω, specNorm (H - Y ω) ∂μ ≤
      singularValues H k +
        (k : ℝ) / ((Fintype.card l : ℝ) - k - 1) * nuclearNorm (H - truncatedSVD H k)
/-- **Truncated Nyström exploits spectral decay, trace**: for any target rank $k$ and any
comparison rank $q$ with $q + 2 \le \ell$,
$$\mathbb{E}\|\mathbf{H}-\llbracket\mathsf{nystrom}(\mathbf{H}, \mathbf{X})\rrbracket_k\|_* \le
\|\mathbf{H}-\llbracket\mathbf{H}\rrbracket_k\|_* + \Bigl(1+\frac{q}{\ell-q-1}\Bigr)
\|\mathbf{H}-\llbracket\mathbf{H}\rrbracket_q\|_*\,.$$
Incomparable with `Matrix.PosSemidef.integral_nuclearNorm_sub_truncatedSVD_nystrom_le_of_hasLaw_gaussianMatrix`:
better when the spectrum decays past $k$ and $q > k$.
[TroppYurtseverUdellCevher2017a, Theorem 4.2 (4.3)]; there with the constant $2$ and a minimum over
$q$, here the constant $1$ (Nyström does not increase singular values) at each $q$.
Result: randomized-nystrom-expected-error -/
theorem _root_.Matrix.PosSemidef.integral_nuclearNorm_sub_truncatedSVD_nystrom_le_add_of_hasLaw_gaussianMatrix
    (hH : H.PosSemidef) (hX : HasLaw X (gaussianMatrix n l) μ) (k : ℕ) {q : ℕ}
    (hq : q + 2 ≤ Fintype.card l) :
    ∫ ω, nuclearNorm (H - truncatedSVD (nystrom H (X ω)) k) ∂μ ≤
      nuclearNorm (H - truncatedSVD H k) +
        gaussianProjectionFactor q (Fintype.card l) * nuclearNorm (H - truncatedSVD H q)
/-- **Truncated Nyström exploits spectral decay, spectral norm**, for a measurable choice
$\mathbf{Y}$ of best rank-$k$ approximations:
$$\mathbb{E}\|\mathbf{H}-\mathbf{Y}\|_2 \le \lambda_k(\mathbf{H}) + \lambda_q(\mathbf{H}) +
\frac{q}{\ell-q-1}\|\mathbf{H}-\llbracket\mathbf{H}\rrbracket_q\|_*\,.$$
At $q = k$ it is dominated by MT Theorem 14.1; for $q > k$ the two are incomparable. Not
instantiable yet (no measurable selector).
[TroppYurtseverUdellCevher2017a, Theorem 4.2 (4.4)]; there $2(1+\frac{q}{\ell-q-1})
\|\mathbf{H}-\llbracket\mathbf{H}\rrbracket_q\|_*$ in place of the last two terms.
Result: randomized-nystrom-expected-error -/
theorem _root_.Matrix.PosSemidef.integral_specNorm_sub_le_add_of_isBestRankApprox_nystrom_of_hasLaw_gaussianMatrix
    (hH : H.PosSemidef) (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ} {Y : Ω → Matrix n n ℝ}
    (hY : ∀ ω, IsBestRankApprox (nystrom H (X ω)) k (Y ω)) (hYm : AEStronglyMeasurable Y μ)
    {q : ℕ} (hq : q + 2 ≤ Fintype.card l) :
    ∫ ω, specNorm (H - Y ω) ∂μ ≤
      singularValues H k + singularValues H q +
        (q : ℝ) / ((Fintype.card l : ℝ) - q - 1) * nuclearNorm (H - truncatedSVD H q)
```

Proof routes. *NE1:* `ae_rank_mul_eq_min_of_hasLaw_gaussianMatrix H hX`, `min_eq_left hHl`,
`hH.nystrom_eq_self_of_rank_eq`. *NG1:* the common step; G1 at $\mathbf{A} = \mathbf{F}$; R1 on the
integrand, R2 and R3 on the right side. *NG2:* NG1 at `lpGauge 1` (`lpGauge_one_matrixNorm`,
`lpGauge_apply_single_zero`), `gaussianProjectionFactor_def`, `ring`. *NG3:* NG1 at `lpGauge p`
(`lpGauge_matrixNorm`, `lpGauge_apply_single_zero hp`). *NG4:* NG1 at `lpGauge ⊤`,
`specNorm_sub_truncatedSVD`. *NG5:* NG3 at $p = 2$ (`schattenNorm_two`). No integrability argument is
needed: the transfer is an equality of integrands, and G1 carries its own. *NU1:* the common step; U1 at $\mathbf{F}$, R4 on the integrand, R3 on
the right side. *NU2:* NL8 (with `hX.aemeasurable`) and NU1, `gaussianProjectionFactor_def`,
`linarith`. *NU3:* pointwise T2 at `lpGauge 1`, then `integral_mono` (NL6 on the left, NL3 plus a
constant on the right) and NG2 at $q$. *NU4:* pointwise B13 at $\mathbf{Y}(\omega)$ with N1
(`(hY ω).matrixNorm_sub_le_add_of_singularValues_le (hH.singularValues_nystrom_le _)` at
`lpGauge ⊤`, `specNorm_sub_truncatedSVD`), then `integral_mono` (NL7, NL5) and NG4 at $q$.
Degenerate: §3.0.

### 3.4 `LowRank/Gaussian/NystromTail.lean`: Gaussian tails (7)

Labels NP1 to NP7. TW's letters: `hd : k + d = Fintype.card l + 1`, `u : ℝ`, `0 < t`; failure
$e^{-(u-2)/4} + $ `gaussianPinvFrobTail k d t`, below TW's $\sqrt{\pi k}\,(t/e)^{-d/2}$ (S3 §8
item 2).

```lean
/-- **The tail of randomized Nyström, every unitarily invariant norm** (TW Corollary 8.2
(NysSVD1)): for $k \le \ell + 1$, any $u$ and $t > 0$,
$$\|\mathbf{H}-\mathsf{nystrom}(\mathbf{H}, \mathbf{X})\|_{\Phi} \le
\|\mathbf{H}-\llbracket\mathbf{H}\rrbracket_k\|_{\Phi} + \Phi(\mathbf{e}_0)\,\frac{utk}{\ell-k+1}\,
\|\mathbf{H}-\llbracket\mathbf{H}\rrbracket_k\|_*$$
outside probability $e^{-(u-2)/4}$ + `gaussianPinvFrobTail k (ℓ - k + 1) t`. TW have Schatten
$1 \le p \le \infty$ and the larger failure term $\sqrt{\pi k}\,(t/e)^{-(\ell-k+1)/2}$.
Result: randomized-nystrom-tail -/
theorem SymmetricGauge.measureReal_not_matrixNorm_sub_nystrom_le_le_of_hasLaw_gaussianMatrix
    (Φ : SymmetricGauge) (hH : H.PosSemidef) (hX : HasLaw X (gaussianMatrix n l) μ) {k d : ℕ}
    (hd : k + d = Fintype.card l + 1) (u : ℝ) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | ¬ Φ.matrixNorm (H - nystrom H (X ω)) ≤
        Φ.matrixNorm (H - truncatedSVD H k) +
          Φ (Finsupp.single 0 1) * (u * t * k / d) * nuclearNorm (H - truncatedSVD H k)} ≤
      Real.exp (-(u - 2) / 4) + gaussianPinvFrobTail k d t
/-- ..., Schatten norms, $1 \le p \le \infty$ (TW (NysSVD1) as printed, up to the failure term).
Result: randomized-nystrom-tail -/
theorem _root_.Matrix.PosSemidef.measureReal_not_schattenNorm_sub_nystrom_le_le_of_hasLaw_gaussianMatrix
    (hH : H.PosSemidef) (hX : HasLaw X (gaussianMatrix n l) μ) {k d : ℕ}
    (hd : k + d = Fintype.card l + 1) {p : ℝ≥0∞} (hp : 1 ≤ p) (u : ℝ) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | ¬ schattenNorm p (H - nystrom H (X ω)) ≤
        schattenNorm p (H - truncatedSVD H k) + u * t * k / d * nuclearNorm (H - truncatedSVD H k)} ≤
      Real.exp (-(u - 2) / 4) + gaussianPinvFrobTail k d t
/-- ..., trace. Result: randomized-nystrom-tail -/
theorem _root_.Matrix.PosSemidef.measureReal_not_nuclearNorm_sub_nystrom_le_le_of_hasLaw_gaussianMatrix
    (hH : H.PosSemidef) (hX : HasLaw X (gaussianMatrix n l) μ) {k d : ℕ}
    (hd : k + d = Fintype.card l + 1) (u : ℝ) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | ¬ nuclearNorm (H - nystrom H (X ω)) ≤
        (1 + u * t * k / d) * nuclearNorm (H - truncatedSVD H k)} ≤
      Real.exp (-(u - 2) / 4) + gaussianPinvFrobTail k d t
/-- ..., spectral norm: $\|\mathbf{H}-\mathsf{nystrom}(\mathbf{H}, \mathbf{X})\|_2 \le \lambda_k(\mathbf{H})
+ \frac{utk}{d}\|\mathbf{H}-\llbracket\mathbf{H}\rrbracket_k\|_*$. Result: randomized-nystrom-tail -/
theorem _root_.Matrix.PosSemidef.measureReal_not_specNorm_sub_nystrom_le_le_of_hasLaw_gaussianMatrix
    (hH : H.PosSemidef) (hX : HasLaw X (gaussianMatrix n l) μ) {k d : ℕ}
    (hd : k + d = Fintype.card l + 1) (u : ℝ) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | ¬ specNorm (H - nystrom H (X ω)) ≤
        singularValues H k + u * t * k / d * nuclearNorm (H - truncatedSVD H k)} ≤
      Real.exp (-(u - 2) / 4) + gaussianPinvFrobTail k d t
/-- **The tail of truncated Nyström, trace**: the bound of the untruncated trace tail holds for
$\llbracket\mathsf{nystrom}(\mathbf{H}, \mathbf{X})\rrbracket_k$, every choice.
[TroppYurtseverUdellCevher2017a, Remark A.4] (announced, "We omit the details").
Result: randomized-nystrom-tail -/
theorem _root_.Matrix.PosSemidef.measureReal_not_nuclearNorm_sub_truncatedSVD_nystrom_le_le_of_hasLaw_gaussianMatrix
    (hH : H.PosSemidef) (hX : HasLaw X (gaussianMatrix n l) μ) {k d : ℕ}
    (hd : k + d = Fintype.card l + 1) (u : ℝ) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | ¬ nuclearNorm (H - truncatedSVD (nystrom H (X ω)) k) ≤
        (1 + u * t * k / d) * nuclearNorm (H - truncatedSVD H k)} ≤
      Real.exp (-(u - 2) / 4) + gaussianPinvFrobTail k d t
/-- **The tail of truncated Nyström, spectral norm** (MT Theorem 14.1 in tail form), for any best
rank-$k$ approximations $\mathbf{Y}(\omega)$ of $\mathsf{nystrom}(\mathbf{H}, \mathbf{X})$, no
measurability: $\|\mathbf{H}-\mathbf{Y}\|_2 \le \lambda_k(\mathbf{H}) + \frac{utk}{d}
\|\mathbf{H}-\llbracket\mathbf{H}\rrbracket_k\|_*$ outside the stated probability. The event may be
non-measurable; `μ.real` is then the outer measure, so the bound says that the failure event lies in
a measurable event of at most this probability; the success-set form does not follow.
Result: randomized-nystrom-tail -/
theorem _root_.Matrix.PosSemidef.measureReal_not_specNorm_sub_le_le_of_isBestRankApprox_nystrom_of_hasLaw_gaussianMatrix
    (hH : H.PosSemidef) (hX : HasLaw X (gaussianMatrix n l) μ) {k d : ℕ}
    (hd : k + d = Fintype.card l + 1) {Y : Ω → Matrix n n ℝ}
    (hY : ∀ ω, IsBestRankApprox (nystrom H (X ω)) k (Y ω)) (u : ℝ) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | ¬ specNorm (H - Y ω) ≤
        singularValues H k + u * t * k / d * nuclearNorm (H - truncatedSVD H k)} ≤
      Real.exp (-(u - 2) / 4) + gaussianPinvFrobTail k d t
/-- The same for `truncatedSVD (nystrom H (X ω)) k`, the maintainer's spelling of the output; the
success-set form does not follow without measurability. Result: randomized-nystrom-tail -/
theorem _root_.Matrix.PosSemidef.measureReal_not_specNorm_sub_truncatedSVD_nystrom_le_le_of_hasLaw_gaussianMatrix
    (hH : H.PosSemidef) (hX : HasLaw X (gaussianMatrix n l) μ) {k d : ℕ}
    (hd : k + d = Fintype.card l + 1) (u : ℝ) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | ¬ specNorm (H - truncatedSVD (nystrom H (X ω)) k) ≤
        singularValues H k + u * t * k / d * nuclearNorm (H - truncatedSVD H k)} ≤
      Real.exp (-(u - 2) / 4) + gaussianPinvFrobTail k d t
```

Proof routes. *NP1:* the common step; P1 at $\mathbf{F}$; the two events are equal (R1 inside,
R2 and R3 on the bound; `Set.ext`), so the probabilities are. *NP2:* NP1 at `lpGauge p`. *NP3:* P3 at
$\mathbf{F}$ with `nuclearNorm_conjTranspose_mul_self` after R1, and R3. *NP4:* P4 at $\mathbf{F}$,
`specNorm_conjTranspose_mul_self` after R1, R5, R3. *NP5:* P5 at $\mathbf{F}$, R4, R3. *NP6:* event
inclusion into NP5's failure event: on its success set, B16 at $\mathbf{Y}(\omega)$ and D1 give
$\|\mathbf{H}-\mathbf{Y}\|_2 \le \sigma_k + \|\mathbf{H}-\llbracket\hat{\mathbf{H}}\rrbracket_k\|_* -
\operatorname{tr}_k \le \sigma_k + \frac{utk}{d}\operatorname{tr}_k$; `measureReal_mono` (no
measurability). *NP7:* NP6 at `isBestRankApprox_truncatedSVD`. Degenerate: §3.0.

### 3.5 `LowRank/Gaussian/RotationInvariant.lean`: rotation-invariant twins (6)

Added to S3's registered file (Q4), after its tails. Hypotheses as S3 §3.6: `[DecidableEq n]
{ν : Measure (Matrix n l ℝ)} [IsProbabilityMeasure ν] [IsLeftUnitarilyInvariant ν] (hX : HasLaw X ν μ)
(hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec)`, written `(hX) (hXr)` below. Labels NI1 to NI6.

```lean
/-- The Gram-form Nyström expectation for every full-rank rotation-invariant test matrix
(Gaussian, Haar, ...). [TroppWebber2023, Corollary 8.2 (NysSVD2)];
[TroppYurtseverUdellCevher2017a, Theorem A.1]; [EpperlyWebber2026, Theorem 3.1 and Fact 3.5].
Result: randomized-nystrom-expected-error -/
theorem SymmetricGauge.integral_matrixNorm_sub_nystrom_le_of_isLeftUnitarilyInvariant
    (Φ : SymmetricGauge) (hH : H.PosSemidef) (hX) (hXr) {k : ℕ} (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, Φ.matrixNorm (H - nystrom H (X ω)) ∂μ ≤
      Φ.matrixNorm (H - truncatedSVD H k) +
        Φ (Finsupp.single 0 1) * ((k : ℝ) / ((Fintype.card l : ℝ) - k - 1)) *
          nuclearNorm (H - truncatedSVD H k)
/-- **HMT's bound for Nyström with rotation-invariant test matrices**: the Nyström twin of
[EpperlyWebber2026, Theorem 3.1], by their Fact 3.5, at one $q$; [TroppYurtseverUdellCevher2017a,
Theorem A.1] (orthonormal test matrices). Result: randomized-nystrom-expected-error -/
theorem _root_.Matrix.PosSemidef.integral_nuclearNorm_sub_nystrom_le_of_isLeftUnitarilyInvariant
    (hH : H.PosSemidef) (hX) (hXr) {k : ℕ} (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, nuclearNorm (H - nystrom H (X ω)) ∂μ ≤
      gaussianProjectionFactor k (Fintype.card l) * nuclearNorm (H - truncatedSVD H k)
/-- [TroppYurtseverUdellCevher2017a, Theorem 4.1 (4.1)] (orthonormal test matrices).
Result: randomized-nystrom-expected-error -/
theorem _root_.Matrix.PosSemidef.integral_nuclearNorm_sub_truncatedSVD_nystrom_le_of_isLeftUnitarilyInvariant
    (hH : H.PosSemidef) (hX) (hXr) {k : ℕ} (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, nuclearNorm (H - truncatedSVD (nystrom H (X ω)) k) ∂μ ≤
      gaussianProjectionFactor k (Fintype.card l) * nuclearNorm (H - truncatedSVD H k)
/-- MT Theorem 14.1 for rotation-invariant test matrices, under a measurable selector (not
instantiable yet). [TroppYurtseverUdellCevher2017a, Theorem 4.1 (4.2)] (orthonormal test matrices).
Result: randomized-nystrom-expected-error -/
theorem _root_.Matrix.PosSemidef.integral_specNorm_sub_le_of_isBestRankApprox_nystrom_of_isLeftUnitarilyInvariant
    (hH : H.PosSemidef) (hX) (hXr) {k : ℕ} (hk : k + 2 ≤ Fintype.card l) {Y : Ω → Matrix n n ℝ}
    (hY : ∀ ω, IsBestRankApprox (nystrom H (X ω)) k (Y ω)) (hYm : AEStronglyMeasurable Y μ) :
    ∫ ω, specNorm (H - Y ω) ∂μ ≤
      singularValues H k +
        (k : ℝ) / ((Fintype.card l : ℝ) - k - 1) * nuclearNorm (H - truncatedSVD H k)
/-- The Gram-form Nyström tail for every full-rank rotation-invariant test matrix.
[TroppWebber2023, Corollary 8.2 (NysSVD1)]; there Gaussian and Schatten.
Result: randomized-nystrom-tail -/
theorem SymmetricGauge.measureReal_not_matrixNorm_sub_nystrom_le_le_of_isLeftUnitarilyInvariant
    (Φ : SymmetricGauge) (hH : H.PosSemidef) (hX) (hXr) {k d : ℕ}
    (hd : k + d = Fintype.card l + 1) (u : ℝ) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | ¬ Φ.matrixNorm (H - nystrom H (X ω)) ≤
        Φ.matrixNorm (H - truncatedSVD H k) +
          Φ (Finsupp.single 0 1) * (u * t * k / d) * nuclearNorm (H - truncatedSVD H k)} ≤
      Real.exp (-(u - 2) / 4) + gaussianPinvFrobTail k d t
/-- **A rotation-invariant sketch at least as wide as the rank makes Nyström exact.** -/
theorem _root_.Matrix.PosSemidef.ae_nystrom_eq_self_of_isLeftUnitarilyInvariant
    (hH : H.PosSemidef) (hX) (hXr) (hHl : H.rank ≤ Fintype.card l) :
    ∀ᵐ ω ∂μ, nystrom H (X ω) = H
```

Proof routes. *NI1, NI2, NI3, NI5:* the common step, then S3's I1, I2, I4, P10 at $\mathbf{F}$ with
R1 to R4 (as NG1, NG2, NU1, NP1). *NI4:* NL8 and NI3. *NI6:* H3 at $\mathbf{H}$ and
`hH.nystrom_eq_self_of_rank_eq`. Alternatively each follows from NI0 and its Gaussian twin; the
route through S3's I-statements needs no measurability argument, because S3 already transferred
the choice-free forms. Degenerate: §3.0 ($\ell > n$ makes `hXr` unsatisfiable).

### 3.6 What transfers, and with which constant

Precisely, for $\mathbf{H} = \mathbf{F}^{\mathsf{H}}\mathbf{F}$:
- **Equal constants, by the correspondence alone** (R1 to R5; no inequality is lost): every
  statement of S3 whose left side is a function of the Gram matrix of the error, that is, every
  Gram-form, squared-Frobenius and squared-spectral statement: G1, G2, G3 (via NG1), G4, U1, P1 to
  P5, I1, I2, I4, P10. They give NG1 to NG5, NU1, NP1 to NP5, NI1 to NI3, NI5 with the source
  constants of TW Corollary 8.2 (both parts), the trace case of TW Corollary 8.8, TYUC Theorem A.1
  and Theorem 4.1 (4.1). The failure probability is the library's, smaller than TW's. The Nyström
  Schatten range $1 \le p < 2$ comes for free from the range finder's $2 \le 2p < 4$.
- **Equal constants, through one deterministic step on top of the transfer**: MT Theorem 14.1 = TYUC
  (4.2) (NU2, NI4) and the truncated spectral tails (NP6, NP7), by reverse Eckart–Young (B16) and D1
  applied to the trace results. S3's spectral truncated statements (U2, P6, P7) have the same
  numbers ($\sigma_k(\mathbf{F})^2 = \lambda_k(\mathbf{H})$) but do **not** transfer as statements:
  they concern best approximations of $\mathbf{P}\mathbf{F}$, and
  $\mathbf{H}-\mathbf{Y}^{\mathsf{H}}\mathbf{Y} = (\mathbf{F}-\mathbf{Y})^{\mathsf{H}}(\mathbf{F}-
  \mathbf{Y})$ holds for $\mathbf{Y} = \llbracket\mathbf{P}\mathbf{F}\rrbracket_k$ only for the
  particular best approximation $\mathbf{Y}^{\mathsf{H}}\mathbf{Y}$ of $\hat{\mathbf{H}}$, not for
  `truncatedSVD (nystrom H (X ω)) k` or another choice (§3.0's example).
- **Better constant than the source**: TYUC Theorem 4.2's decay bounds (NU3, NU4), constant one in
  place of two, from S2a's constant-one Nyström lemma (T2, B13 with N1); in the spectral form also
  $\lambda_q + \frac{q}{\ell-q-1}\operatorname{tr}_q$ in place of
  $2(1+\frac{q}{\ell-q-1})\operatorname{tr}_q$.
- **No useful twin** (the error is a square root of the Nyström quantity): the unsquared statements
  G5 and I3 (HMT 10.6), G6 and I6 (HMT 10.5 as printed), P8 and P9 (HMT 10.7, 10.8), and S1's
  triangle form. They transfer with equal constants only as $\mathbb{E}\|\mathbf{H}-
  \hat{\mathbf{H}}\|_2^{1/2}$ (TYUC Remark A.3) or as squared-sum tails (TYUC Remark A.4); cut (§6).
- **Not reached, would transfer with equal constants once the range-finder statement exists**: TW
  Corollary 8.8's cases $k \in \{r, r+1\}$, its spectral bound and its $k \ge r + 4$ bounds (S3 Q7's
  deferral of TW Theorem 8.7).

### 3.7 Transfer table

| Nyström statement | range-finder (or deterministic) source | rewrites |
|---|---|---|
| NL1 to NL5 | L1 at $\mathbf{F}$ | R1; gauges for NL2 to NL5 |
| NL6 | L7 at $\mathbf{F}$ | R4 |
| NL7, NL8 | B16, D1, T9 | none (deterministic, then integrate) |
| NE1, NI6 | `ae_rank_mul_eq_min_…` (RandomMatrix's a.s. rank, H3) | `nystrom_eq_self_of_rank_eq` |
| NG1, NI1 | G1, I1 | R1, R2, R3 |
| NG2, NG3, NG4, NG5 | NG1 at `lpGauge 1`, `p`, `⊤`, `2` | `lpGauge_*_matrixNorm`, `specNorm_sub_truncatedSVD` |
| NI2 | I2 | R1 with `nuclearNorm_conjTranspose_mul_self`, R3 |
| NU1, NI3 | U1, I4 | R4, R3 |
| NU2, NI4 | NL8 with NU1, NI3 | none |
| NU3 | T2 at `lpGauge 1`, NG2 at $q$ | none |
| NU4 | B13 with N1 at `lpGauge ⊤`, NG4 at $q$ | none |
| NP1, NI5 | P1, P10 | R1, R2, R3 (event equality) |
| NP2 | NP1 at `lpGauge p` | |
| NP3 | P3 | R1, `nuclearNorm_conjTranspose_mul_self`, R3 |
| NP4 | P4 | R1, `specNorm_conjTranspose_mul_self`, R5, R3 |
| NP5 | P5 | R4, R3 |
| NP6, NP7 | NP5's event | B16, D1 (inclusion) |
| NI0 | H2 at $\mathbf{H}^{1/2}$ | `Matrix.PosSemidef.nystrom_eq` |

## 4. Files

| # | File | Statements | Lines (est.) | Imports (new) | Depends on |
|---|---|---|---|---|---|
| 1 | `Matrix/Spectral/BestRankApprox.lean` (registered; side file `Matrix/Spectral/BestRankApproxGram.lean` until proved) | 1 (M1) | +15 | none | none |
| 2 | `LowRank/Structural/Truncation.lean` (registered; side file `LowRank/Structural/TruncationNystrom.lean`) | 1 (D1) | +30 | none | none |
| 3 | `Matrix/Factorizations/NystromOrder.lean` (registered; side file `Matrix/Factorizations/NystromHelps.lean`) | 2 (X1, X2) | +20 | `Matrix/Factorizations/SketchedLowRank` if not transitive | none |
| 4 | `RandomMatrix/Haar/Transfer.lean` (registered; side file `RandomMatrix/Haar/TransferNystrom.lean`) | 1 (NI0) | +30 | `Matrix/Factorizations/NystromGram` | none |
| 5 | `LowRank/Random/Nystrom.lean` (new) | 8 (NL1 to NL8) | 220 | `LowRank/Random/RangeFinder`, `LowRank/Structural/Truncation`, `Matrix/Spectral/BestRankApprox` | files 1, 2 |
| 6 | `LowRank/Gaussian/Nystrom.lean` (new) | 10 (NE1, NG1 to NG5, NU1 to NU4) | 330 | `LowRank/Gaussian/RangeFinder`, file 5 | files 1, 5 |
| 7 | `LowRank/Gaussian/NystromTail.lean` (new) | 7 (NP1 to NP7) | 260 | `LowRank/Gaussian/RangeFinderTail`, file 5 | files 1, 2, 5; S3's tail file finished |
| 8 | `LowRank/Gaussian/RotationInvariant.lean` (registered, S3; S4 extends it; side file `LowRank/Gaussian/RotationInvariantNystrom.lean`) | 6 (NI1 to NI6) | +170 | file 5 | files 1, 5 |

S5 is about 1075 lines and 36 public declarations, all theorems, against the brief's 400 lines in one
file. The growth: law-free companions and the selector reduction (file 5, D4 and S2a Q3, about
220), the tails (file 7, which the brief folded into "and tails", about 260), the rotation-invariant
twins and the law transfer (files 4, 8, about 200), the decay forms and "Nyström helps" (about 70).
Every new file is under 1000 lines and 25 statements; file 8 reaches about 440 lines before S4.
Order: files 1 to 4 are independent; 5 after 1, 2; 6 after 5; 7 after 5 and S3's tail file; 8 after
5. File 6 does not import the tail machinery or the Haar layer.

**Placement** (CONTRIBUTING §8 item 5): every addition outside files 5 to 7, with its home and
reason.
- M1, `Matrix/Spectral/BestRankApprox.lean`: the gauge form of B20
  (`nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD`), which lives there; a statement about
  truncated SVDs and Gram matrices, no algorithm.
- D1, `LowRank/Structural/Truncation.lean`: a deterministic fact about truncated Nyström, beside T7
  and T8 (the choice-free trace error it compares with).
- X1, X2, `Matrix/Factorizations/NystromOrder.lean`: "Nyström helps" at a particular test matrix,
  beside `Matrix.PosSemidef.singularValues_sub_nystrom_le` and `SymmetricGauge.matrixNorm_sub_nystrom_le`
  (S0 §8 item 14(d) assigned the statement to S5's note, not its file).
- NI0, `RandomMatrix/Haar/Transfer.lean`: the Nyström twin of H2
  (`hasLaw_rangeProjector_mul_of_isLeftUnitarilyInvariant`), the Gaussian–Haar law transfer, which
  lives there; `nystrom` is a Matrix-layer object, so the import goes downward.
- NI1 to NI6, `LowRank/Gaussian/RotationInvariant.lean`: rotation-invariant test matrices, beside
  S3's RSVD twins and where S4 puts EW Theorem 3.6(a), the sharp rotation-invariant Nyström bound
  (Q4).
- **Flags** (placed elsewhere until the wrap-up): each of the five registered homes takes its
  statements only proved; until then they sit in the side files named in the table, each saying it
  merges into its home. No other flag.

## 5. Material

**Prototype** (read-only, `~/Documents/prove2me/lean/NLAlib/LowRank/Nystrom/`; ledger
dispositions):
- `Structural.lean`: `integrable_and_integral_trace_sub_nystrom_le` → NG2 with NL3 (split, D4;
  `hA : A = Fᵀ * F` replaced by `hH : H.PosSemidef`, a factor being an instance; the right side
  `bestRankFrobSq F k`, which the prototype says it never identified with $\sum_{i>k}\lambda_i$, is
  $\operatorname{tr}_k$ by R3; `Fin` indices and the measurable range frame not reproduced). The
  rest of the file is S0's (S0 §5).
- `GaussianNystrom.lean`, `RawGaussianNystrom.lean`, `GeneralizedNystrom.lean`,
  `SketchedRegression.lean`, `RawNystromBridge.lean`: generalized Nyström; S6 (S0 §5). Nothing for
  S5; `ae_rawGeneralizedNystrom_eq_self_of_rank_le` is S6's twin of NE1.
- `Cholesky/` (Nyström residual after pivoted Cholesky): out of scope (brief §8).

**The maintainer's notes** (never cited, D13): nothing Nyström-specific beyond the completion step
S3 already uses.

**Literature** (§0's checks). Citations, all keys in `docs/references.bib` (`TroppWebber2023`,
`MartinssonTropp2020`, `TroppYurtseverUdellCevher2017a`, `EpperlyWebber2026`, `Gu2015`,
`HalkoMartinssonTropp2011`); no new key:

| statement | citation | relation to the printed statement |
|---|---|---|
| NG1, NI1 | [TroppWebber2023, Corollary 8.2 (NysSVD2)]; [MartinssonTropp2020, §14.4]; [TroppYurtseverUdellCevher2017a, Theorem A.1] | there Schatten $p \ge 1$ or trace; here every unitarily invariant norm with $\Phi(\mathbf{e}_0)$ |
| NG2, NI2 | [TroppYurtseverUdellCevher2017a, Theorem A.1]; [TroppWebber2023, Corollary 8.8]; [EpperlyWebber2026, Theorem 3.1 and Fact 3.5] (NI2) | at one rank, not the minimum (rule 5); TYUC also orthonormal (NI2) |
| NG3, NG4, NG5 | [TroppWebber2023, Corollary 8.2 (NysSVD2)] | $p \in [1, \infty]$, $p = \infty$, $p = 2$ |
| NU1, NI3 | [TroppYurtseverUdellCevher2017a, Theorem 4.1 (4.1)] | no $1 \le k$, no $\ell \le n$; Woodruff's truncation for free (S1) in place of Gu's Theorem 3.5 |
| NU2, NI4 | [MartinssonTropp2020, Theorem 14.1]; [TroppYurtseverUdellCevher2017a, Theorem 4.1 (4.2)] | under a measurable selector; real |
| NU3, NU4 | [TroppYurtseverUdellCevher2017a, Theorem 4.2 (4.3), (4.4)] | constant one in place of two; each $q$, not the minimum |
| NP1 to NP4, NI5 | [TroppWebber2023, Corollary 8.2 (NysSVD1)] | Gram form, every gauge; `gaussianPinvFrobTail` below TW's failure term |
| NP5 to NP7 | [TroppWebber2023, Corollary 8.2 (NysSVD1)] with [TroppYurtseverUdellCevher2017a, Proposition A.8] (NP6, NP7); [TroppYurtseverUdellCevher2017a, Remark A.4] | composition |
| NL8 | [TroppYurtseverUdellCevher2017a, Proposition A.8, App. A.6]; [Gu2015, Theorem 3.4] | in expectation, any law |
| M1 | [TroppYurtseverUdellCevher2017a, App. A.5]; [TroppWebber2023, proof of Corollary 8.8] | inside proofs there |
| X1, X2 | [TroppWebber2023, Lemma 5.2] | at the test matrix $\mathbf{H}\mathbf{\Omega}$ |
| NI0 | [TroppYurtseverUdellCevher2017a, Proposition A.2, proof of Theorem A.1]; [EpperlyWebber2026, Fact 6.1(b)] | as a law statement |
| NE1, NI6, D1, NL1 to NL7 | helpers, no citation | |

**Result ids** (D11; checked against the ids in `NLAlib/` and `explore/results.toml`, which has no
Nyström entry): `randomized-nystrom-expected-error` (NG1 to NG5, NU1 to NU4, NI1 to NI4; the atlas
candidate `nystrom-randomized`), `randomized-nystrom-tail` (NP1 to NP7, NI5), both new; X1, X2 join
`nystrom-helps`; NI0 joins `gaussian-haar-range-transfer`. The fixed-rank (truncated) results share
the first id, as S3's truncated RSVD shares `randomized-svd-expected-error`.

## 6. Cut, and why

- *A bound-only expectation of `specNorm (H - truncatedSVD (nystrom H (X ω)) k)`*: §3.0 item 2.
- *General-factor twins* (`Fᴴ * F` in place of `H`, right sides in $\mathbf{F}$): each is the PSD
  statement at $\mathbf{H} := \mathbf{F}^{\mathsf{H}}\mathbf{F}$ followed by R2, R3 (Q1). Additive.
- *Trace twins* (`(H - nystrom H (X ω)).trace` in place of the nuclear norm): one rewrite by
  `Matrix.PosSemidef.nuclearNorm_eq_re_trace` and `hH.nystrom_le` (Q2). Additive.
- *Nyström twins of the unsquared range-finder statements* (HMT 10.6 as TYUC Remark A.3's half
  moment $\mathbb{E}\|\mathbf{H}-\hat{\mathbf{H}}\|_2^{1/2} \le (1+\sqrt{\tfrac{k}{\ell-k-1}})
  \lambda_k^{1/2} + C\operatorname{tr}_k^{1/2}$; HMT 10.7, 10.8 as squared-sum tails, TYUC Remark
  A.4): equal constants, awkward shapes, no consumer. Additive, one line each from G5, P8, P9.
- *Frobenius and Schatten tails of the truncated output, and truncated expectations in other
  gauges*: choice-dependent outside the trace; S3 §6's reason. Additive under a selector.
- *Rotation-invariant twins of the remaining statements* (Schatten, spectral, Frobenius
  expectations, decay forms, trace and truncated tails): NI0 or the I-statements in three lines
  each; the headline ones are stated. Additive.
- *Probabilistic forms of "Nyström helps"* ($\mathbb{E}\|\mathbf{H}-\mathbf{H}\langle\mathbf{H}
  \mathbf{X}\rangle\|_\Phi \le \mathbb{E}\|\mathbf{H}-\mathbf{P}_{\mathbf{H}\mathbf{X}}\mathbf{H}
  \|_\Phi$ and the bounds it inherits): Nyström from the sample $\mathbf{H}^2\mathbf{\Omega}$ is one
  step of Nyström subspace iteration (NysSI, TW §9), deferred with power methods (brief §8; Q8).
- *The monotonicity in the range in expectation* (more columns, smaller expected error): pointwise
  from `nystrom_le_nystrom_of_range_le`, no consumer.
- *The minimum over the comparison rank* (TYUC Theorems A.1, 4.2; EW Theorem 3.1): rule 5, as S3.
- *Sample-size forms* (TYUC's $k = (1+\varepsilon^{-1})r + \alpha$): rule "tails, not sample sizes";
  a parameter choice in NU1. Additive.
- *TW Corollary 8.8 beyond the first case*: §3.6, last item.

## 7. Questions and decisions

Hard-to-reverse items are marked **(hard)**. Under the round's approval rule the maintainer decides
the hard ones; the rest proceed as recommended and are recorded here.

**Q1. The carrier and the spelling of best errors (hard).** Options: (a) a positive semidefinite
`H` with `hH : H.PosSemidef`, right sides in $\mathbf{H}$'s own best errors through the §5.3 row
(`Φ.matrixNorm (H - truncatedSVD H k)`, `nuclearNorm (H - truncatedSVD H k)`, `singularValues H k`),
eigenvalues in docstrings; (b) a factor, `Fᴴ * F` for any `F`, right sides
`frobNorm (F - truncatedSVD F k) ^ 2` and `singularValues F k ^ 2`, no PSD hypothesis; (c) (a) with
eigenvalue spellings, `eigenvalue H k` and `∑ i ∈ Finset.Ico k (Fintype.card n), eigenvalue H i`.
Recommendation (a): the sources state Nyström for psd $\mathbf{A}$ with best errors of
$\mathbf{A}$ (TW, MT, TYUC, EW 3.6); a kernel matrix is an instance by one term; (a) matches S0 to
S2a's Nyström statements (`Matrix.PosSemidef.nuclearNorm_sub_truncatedSVD_nystrom`, B16 in
`singularValues`); (b) makes users translate every bound by R2, R3; (c) leaves the vocabulary row
for the best rank-$k$ approximation and needs a sum bridge in every proof
(`Matrix.PosSemidef.singularValues_eq_eigenvalue` is one rewrite away for $\lambda_k$). Rework if
reversed: the hypotheses and right sides of all 36 statements, of S4's Theorem 3.6(a) and of S7's
CEMT Corollary 2.5.

**Q2. The trace is spelled `nuclearNorm` (not hard).** Options: (a) `nuclearNorm (H - …)`; (b)
`(H - …).trace` (real); (c) both. Recommendation (a): the error is positive semidefinite, so the two
agree (`Matrix.PosSemidef.nuclearNorm_eq_re_trace` with `hH.nystrom_le`, T9); (a) is what S0's
correspondence, T7 and T8 already state, and what the gauge form specialises to (`lpGauge 1`).
Docstrings say "trace". Trace twins are additive if a consumer (Estimation's trace estimators)
wants them.

**Q3. Namespaces and names (not hard).** `hH` first, so non-gauge statements are
`Matrix.PosSemidef.…` (CONTRIBUTING §5.2, dot notation; T8, T9); gauge statements are
`SymmetricGauge.…` with `Φ` first (S1, S3). Tails keep the root prefix `measureReal_` inside
`Matrix.PosSemidef` (S3 Q10's reading: the `measure_` prefix is for probabilistic interfaces).
Selector statements end `…_of_isBestRankApprox_nystrom_of_…`, naming the output the hypothesis is
about; S3's L8, L9, U2 leave `rsvd` implicit (their conclusions differ from these, so nothing
collides). The decay forms NU3, NU4 are told apart from NU1, NU2 by `_le_add_` (their right side is
a sum over two ranks; rule 4's "the parameter its bound is in"). Rework if changed: renames only.

**Q4. Where the rotation-invariant twins live (not hard).** Options: (a)
`LowRank/Gaussian/RotationInvariant.lean`, beside S3's twins and S4's EW Theorem 3.6(a); (b) a new
`LowRank/Gaussian/NystromRotationInvariant.lean`; (c) inside files 6 and 7. Recommendation (a): a
user with a Haar test matrix finds every rotation-invariant result in one file, and the sharp
Nyström bound S4 adds sits beside the HMT-type one it sharpens (NI2). The file stays under 1000
lines with S4 (about 440 before it). Rework: a file move.

**Q5. The law of the Nyström output under rotation invariance, NI0 (not hard).** Options: (a) state
it, beside H2; (b) leave it out, every twin going through S3's I-statements. Recommendation (a): it
is the Nyström form of H2 in about 30 lines, it makes every further rotation-invariant Nyström
statement a three-line corollary (including the cut ones of §6), and it is TYUC's "we may assume
that $\mathbf{\Omega}$ is Gaussian" made a theorem. Drop it if the reviewer finds no consumer;
nothing else depends on it.

**Q6. TYUC Theorem 4.2's spectral-decay forms, NU3 and NU4 (not hard).** Options: (a) state them
at each comparison rank $q$, constant one; (b) leave them out. Recommendation (a): they are TYUC
NeurIPS's second theorem, about 40 lines from T2, B13 and N1, and better than printed; NU4 at
$q = k$ is the brief's "$2\lambda_{k+1}$" bound, so the brief's promise is kept in its strongest
form.

**Q7. D1, the trace error of truncated Nyström under any choice (not hard).** Options: (a) public, in
`Truncation.lean`, as an inequality; (b) the equality (every best approximation of a PSD matrix is
PSD), which needs the equality case of Eckart–Young in eigenvector form, not in the library; (c)
private in file 5. Recommendation (a): files 5 and 7 and S7 use it (a private lemma cannot cross
files); the inequality is all the uses need; upgrading to the equality later is additive (a new
`_eq` lemma, this one reproved from it, rule 6).

**Q8. "Nyström helps" at the sample $\mathbf{H}\mathbf{\Omega}_0$ (not hard).** S0 §8 item
14(d) asked this note to state it. Options: (a) X1, X2 deterministic only; (b) also their
probabilistic forms. Recommendation (a): the probabilistic forms are a step of Nyström subspace
iteration (the sample is $\mathbf{H}^2\mathbf{\Omega}_0$), deferred with power methods by the
maintainer's instruction (brief §8).

**Q9. Integrability companions per norm (not hard).** NL1 to NL6 give one companion per stated
expectation integrand (D4), law-free over `𝕜` (S3 Q9), with the gauge one primary. Rework if
reversed: per-law twins.

**Q10. Corrections of record (information).**
- Brief §4.2, row "spectral" and the policy paragraph: "HMT 10.6's first moment ... no Nyström
  twin" reads "a twin only for the half moment $\mathbb{E}\|\mathbf{H}-\hat{\mathbf{H}}\|_2^{1/2}$
  (TYUC NeurIPS Remark A.3), not stated".
- Brief §4.2, row "Frobenius": "No source bounds the range finder in $S_4$ except TW Theorem 8.7"
  reads "TW Theorem 8.1 (RSVD2) at $p = 4$ does (S3's G3), and TW Corollary 8.2 at $p = 2$ is its
  Nyström form (NG5), with equal constants".
- Brief §4.3 "Nyström (S5)" and §7's S5 entry: the spectral bound "$2\lambda_{k+1}$" and "MT Theorem
  14.1's constant only after TYUC NeurIPS is read, and then as an S2a lemma" are superseded (S2a Q6):
  MT 14.1 is NU2, from S2a's B16 and the new D1; "$2\lambda_{k+1}$" is NU4 at $q = k$. "Every
  Nyström bound of TW Corollaries 8.2 and 8.8" reads "all of Corollary 8.2 and the first case of
  Corollary 8.8".
- Brief §7, S5 entry: three new files plus additions to five registered files, about 1075 lines
  (§4), not one file of 400.
- TYUC NeurIPS App. A.5: "With probability one, the nonzero eigenvalues of
  $\hat{\mathbf{A}}_{\mathrm{nys}}$ are all distinct" is false at $\mathbf{A} = \mathbf{I}$ (S2a §8
  item 1's argument for the RSVD, here $\hat{\mathbf{A}}_{\mathrm{nys}} = \mathbf{P}_{\mathbf{\Omega}}$).
  Their (4.1) does not need it (choice-free); their (4.2) holds for every choice through
  Proposition A.8, which is how NU2 and NP6 are stated.
- S1 §8 item 2's remark that the $\mathbf{H}^{1/2}$ route needs the choice-dependent
  `truncatedSVD (CFC.sqrt H) k ^ 2 = truncatedSVD H k`: M1 (choice-free, through singular values)
  removes the need; S5 uses neither that identity nor the square root in any proof except NI0's.

## 8. Amendments from the review (2026-10-15)

Review of this note (nine low amendments, no high or medium, eight verdicts), all nine accepted by
the orchestrator; none rejected. One is corrected on inspection: A9's premise that the common step
needs the C*-algebra instance of the L2-operator scope is wrong (item 9). The review found nothing
mathematically wrong; it rechecked every transfer claim of §3.6 and §3.7 against the code, the
statements at every rank and shape, the measurability discipline, the count (36 statements, all
theorems, no definition), the placement of M1, D1, X1 and X2, and the literature quotations
against the PDFs; it confirmed that TYUC Theorem 4.2 holds with constant one (S2a's T2, B13 with
N1), that U2, P6 and P7 do not transfer as statements, and that the unsquared HMT twins are rightly
cut. Q1 is decided as (a), which the review found dominant rather than a trade-off (item 10);
Q2 to Q9 stand as recommended (item 11). Where an item below contradicts §0 to §7, it supersedes
them; §3 stays as drafted.

1. **A1, NI0 moves to `LowRank/Gaussian/RotationInvariant.lean`** (§3.1, §4 file 4, the placement
   bullet, Q5). `Matrix.PosSemidef.hasLaw_nystrom_of_isLeftUnitarilyInvariant` is a statement
   about the law of the Nyström output, so by CONTRIBUTING §8 item 5 it sits with the other
   rotation-invariant Nyström results, before NI1, as Q4's own argument says ("every
   rotation-invariant result in one file"). `RandomMatrix/Haar/Transfer.lean` keeps H2, the
   range-projector law it is proved from. File 4 of §4 is dropped; file 8 holds NI0 to NI6 (7
   statements, about 200 lines added), with side file `LowRank/Gaussian/RotationInvariantNystrom.lean`
   until proved. No new import for `Transfer.lean`. The result id stays
   `gaussian-haar-range-transfer`.
2. **A2, X1 and X2 are "Nyström from the randomized SVD's sketch"** (§3.1 docstrings, §5 row X1,
   X2). `nystrom H (H * Ω)` takes the sketch $\mathbf{H}\mathbf{\Omega}$ as its test matrix, so it
   costs one more multiplication by $\mathbf{H}$ (its own sketch is $\mathbf{H}^2\mathbf{\Omega}$,
   one NysSI step, §6); the docstrings say so, so that X1 is not read as a comparison on identical
   data. Citation: [TroppWebber2023, Lemma 5.2] "at $\mathbf{M} = \mathbf{H}\mathbf{\Omega}$"; TW
   state it for any $\mathbf{M}$, $p \in [1, \infty]$ and every unitarily invariant norm, which is
   S0's `Matrix.PosSemidef.singularValues_sub_nystrom_le` in general.
3. **A3, instance corollaries kept by rule 6** (§3.3, §3.4, §6). NG2, NG4, NG5 are NG3 (or NG1) at
   $p = 1, \infty, 2$ (`schattenNorm_one`, `schattenNorm_top`, `schattenNorm_two`, or the gauges
   `lpGauge 1`, `lpGauge ⊤`), NP3 and NP4 are NP1 at the same gauges, NP7 is NP6 at
   `isBestRankApprox_truncatedSVD`, and X2 is X1 under `matrixNorm_le_of_singularValues_le`. Each is
   kept under CONTRIBUTING §5.2 rule 6: consumers cite the simpler spelling (S3's G2, G3, P3, P4
   precedent). No other statement of the 36 is dominated (review B4); NU4 at $q = k$ is dominated
   by NU2 but is a family in $q$, incomparable for $q > k$ (rule 4), as its docstring says.
4. **A4, M1's docstring and why its home is `BestRankApprox.lean`** (§3.1, the placement bullet).
   The docstring reads "independent of the choice `truncatedSVD` makes on either side (both error
   matrices have singular values $\sigma_{k+i}(\mathbf{G})^2$)", not "for every choice of either
   truncation", which reads as a quantifier over best approximations. Placement:
   `Matrix/Spectral/LowRank.lean` cannot state a gauge (`Matrix/Norms/UnitarilyInvariant.lean`
   imports it), so B20's file is the only Matrix-layer home that can; S2a's placement-refactor rule
   ("truncated-SVD facts with no predicate go to `LowRank.lean`") does not apply.
5. **A5, D1's docstring** (§3.1, Q7). "(Equality holds, since every best approximation of a
   positive semidefinite matrix is positive semidefinite; it is not needed.)" becomes "Equality is
   expected (Q7) but not proved; the inequality is all that is used." The note's prose asserted an
   unproved fact.
6. **A6, the probability space of NU2, NU3, NU4, NI4** (§3.3 and §3.5 routes). They do not carry
   `[IsProbabilityMeasure μ]`; it is derived from `hX : HasLaw X ν μ` with `[IsProbabilityMeasure ν]`
   (`HasLaw.isProbabilityMeasure`, as S3's U2 does), and is what NL8, `integral_const` and
   `integral_add` need. The signatures are unchanged.
7. **A7, tail parameters against TW** (§3.4 docstrings). TW Corollary 8.2 takes $u, t \ge 0$; the
   library takes $t > 0$ and $u$ free (S3 §3.0: at $t = 0$ Lean's $0^{d/2} = 0$ would make the
   deterministic part alone a claim). NP1's docstring says "there $u, t \ge 0$; here $t > 0$ and any
   $u$".
8. **A8, the orthonormal case of TYUC Theorem 4.1 is checkable** (§5 rows NI2, NI3; their
   docstrings). The NI2 and NI3 docstrings name the two facts a user with a Haar frame needs: the
   instance `NLAlib.isLeftUnitarilyInvariant_haarFrame` (`RandomMatrix/Haar/Basic.lean`) and
   `hXr` from `NLAlib.ae_rank_mul_eq_min_of_hasLaw_haarFrame` at $\mathbf{A} = \mathbf{I}$ when
   $\ell \le n$.
9. **A9, the scope of the common step, corrected on inspection** (§3.0). The review says
   `CStarAlgebra.nonneg_iff_eq_star_mul_self` on `Matrix n n ℝ` needs the C*-algebra instance of
   the L2-operator scope. It does not: S1's `RangeFinder.lean` (line 430) opens only
   `MatrixOrder`, the step elaborates over any `RCLike` field with `open scoped MatrixOrder` (for
   `hH.nonneg`) and `classical` (the continuous functional calculus on matrices needs
   `DecidableEq n`), and Mathlib's `Matrix.instCStarAlgebra` is in any case only for `ℂ`. Checked
   by compiling the step (2026-10-15). Files 5 to 8 open `Matrix ComplexOrder MatrixOrder` and
   no norm scope, as CONTRIBUTING §5.1 requires.
10. **Q1 decided: (a)** (review B7). The sources state Nyström for a positive semidefinite matrix
    with its own best errors, S0 to S2a's Nyström API already takes `hH : H.PosSemidef`, (b) would
    cost every positive semidefinite user a factor they do not have, and a kernel user pays one
    instance (`Matrix.posSemidef_conjTranspose_mul_self F`) plus M1 and B20; general-factor twins
    stay additive (§6). Nothing in (a) is hard to reverse in practice.
11. **Q2 to Q9 stand as recommended**: the trace spelled `nuclearNorm` (Q2); `Matrix.PosSemidef`
    and `SymmetricGauge` namespaces with the names of §3 (Q3); the rotation-invariant twins in
    `RotationInvariant.lean` (Q4), now with NI0 (item 1); NI0 stated (Q5); NU3, NU4 at each $q$
    with constant one (Q6); D1 public, an inequality, in `Truncation.lean` (Q7); X1, X2
    deterministic only (Q8); one law-free integrability companion per integrand (Q9).
12. **Implementation record** (2026-10-15). All 36 statements are proved, with §3's names and
    signatures and no statement change; NI0 to NI6 went through the side file of item 1 and were
    merged into `RotationInvariant.lean` once proved, and the side file is deleted. Thirteen names
    exceed the 100-character line with the `_root_.Matrix.PosSemidef.` prefix; each is written
    with `theorem` on its own line, and the nine still too long there (NL8, NU2, NU3, NU4, NP5,
    NP6, NP7, NI3, NI4) carry `set_option linter.style.longLine false in` with a comment. The
    common step is `CStarAlgebra.nonneg_iff_eq_star_mul_self` under `classical` (item 9); NI0 uses
    `Matrix.PosSemidef.nystrom_eq` only through an existential, so that no square root is
    elaborated against a second `DecidableEq` instance.
