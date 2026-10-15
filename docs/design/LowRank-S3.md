# Design note: LowRank stage S3, the Gaussian and rotation-invariant range finder and randomized SVD

Status: drafted 2026-10-15 under `docs/PORT_LOWRANK.md` (maintainer decisions of 2026-10-15,
binding: D4 expectations first, tails second, each expectation with its `integrable_…`
companion; every error spelled $\mathbf{A}$ minus the named output; late truncation written
`truncatedSVD (rsvd A Ω) k`; real Gaussian and Haar laws now, D3; also D2, D9 to D13; §4.2, §4.3
"Gaussian test matrices" and "Haar and rotation-invariant test matrices", §5.1, the S3 entry of
§7, §9.3), `docs/design/LowRank-S0.md`, `LowRank-S1.md` and `LowRank-S2a.md` (§8 of each
overrides its §3; all proved and registered: `Matrix/Subspaces/ObliqueProjector.lean`,
`Matrix/Factorizations/{SketchedLowRank,NystromGram,NystromOrder}.lean`,
`LowRank/Structural/{RangeFinder,Truncation}.lean`, `Matrix/Spectral/{LowRank,BestRankApprox}.lean`),
and the RandomMatrix layer as `docs/design/Probability-REPORT.md` §2 and
`docs/design/RandomMatrix-R4.md` §8 describe it. Real field for every probabilistic statement;
the law-free integrability and selector lemmas are over `𝕜`. Every shape, rank and target rank;
the side conditions are the ones the sources need and no more (§3.0). Reviewed 2026-10-15 (2 medium, 6 low, 2
information), amendments in §8, which overrides §0 to §7 where they disagree (§3 stays as
drafted); all ten accepted, none rejected, three corrected on inspection. Q1, Q2 (with
`gaussianProjectionFactor` in `RandomMatrix/Gaussian/BlockMoments.lean`) and Q5 accepted as
recommended (§8 items 11 to 13). The RSVD1 tail now beats TW's failure constant by the exact
χ² small ball (§8 item 2). S3 is 62 public declarations in 13 files, about 1725 lines (§8 item 16).

Departures from the brief, each argued below:
- **Rotation-invariant laws through the interface, not `haarFrame`.** The Haar and
  rotation-invariant versions take `HasLaw X ν μ` with `[IsLeftUnitarilyInvariant ν]` and
  almost-sure full column rank (EW's "full-rank rotation-invariant embedding"); the Haar frame and
  the Gaussian are instances (CONTRIBUTING §5.4, "parametrise over the interface"). One new
  RandomMatrix lemma carries them: the polar factor of such a matrix is Haar (§3.3, Q5).
- **TW (RSVD1) is reached with a different failure constant.** TW's $\sqrt{\pi k}$ in front of
  $(t/e)^{-(\ell-k+1)/2}$ becomes $2\sqrt{k}$ by an elementary route (the χ² small ball already in
  the library and a layer-cake integral), so the failure term is a named tail function under
  CONTRIBUTING §5.2 rule 2, `gaussianPinvFrobTail` (§3.2, Q3).
- **HMT 10.7 and 10.8 sit beside TW (RSVD1), not as corollaries**: they are incomparable with it
  (rule 4). They are stated with the constants the library's moments reach (R4's spectral
  constant in place of $e\sqrt{k+p}/(p+1)$, the inverse-Wishart trace tail in place of HMT
  Proposition 10.4's $\sqrt{12k/p}$ and $4t^{-p}$) (§3.6, Q6).
- **TW Theorem 8.7 is not ported** (the brief's "optionally"): its $\ell \in \{k, k+1\}$ cases need
  parallel sums and S1's parallel-sum structural form (cut there), its spectral bound needs the
  Gaussian spectral second moment (TW Lemma B.1) that S6 also needs, its Schatten-4 bounds need
  fourth moments the library lacks (§6, Q7).
- **The integrability companions are law-free.** The integrands are bounded and measurable for
  every measurable test matrix, so each companion is stated once, with `AEMeasurable X μ` and a
  finite measure, over `𝕜`, and serves Gaussian, rotation-invariant and (S7) every other law
  (Q9).
- **The RandomMatrix layer grows** by the tails the brief assumed in passing ("a chi-square-type
  tail ... and an HMT 10.4-type tail"): the inverse-Wishart trace tail, Lipschitz concentration with
  an independent random factor, the Gaussian block tail (TW Proposition 8.6, (8.9)), and the
  spectral pseudoinverse tail. About 600 of S3's lines are there (§4).

**Literature checks** (PDFs in `~/Documents/prove2me/books/`; printed page = PDF page for HMT
arXiv v2 and TW arXiv v3):
- HMT §10: Propositions 10.1 to 10.4 (pp. 55 to 56); Theorem 10.5 (p. 56: real $\mathbf{A}$,
  $k \ge 2$, $p \ge 2$, $k + p \le \min\{m, n\}$, the bound on $\mathbb{E}\|\cdot\|_{\mathsf{F}}$
  through Hölder; the proof bounds $\mathbb{E}\|\cdot\|_{\mathsf{F}}^2$); Theorem 10.6 (p. 57);
  Theorems 10.7, 10.8 (pp. 58 to 59, $p \ge 4$, $u, t \ge 1$, failure $5t^{-p} + 2e^{-u^2/2}$
  and $5t^{-p} + e^{-u^2/2}$); Corollary 10.9 (p. 59); the proof of 10.8 (pp. 59 to 60) conditions
  on $\mathbf{\Omega}_1$ and applies Proposition 10.3 to $\mathbf{\Omega}_2$ with Lipschitz constant
  $\|\mathbf{\Sigma}_2\|\|\mathbf{\Omega}_1^{\dagger}\|$.
- TW §8: Theorem 8.1 (p. 33): (RSVD1) for $2 \le p \le \infty$, $u, t \ge 0$, $k \ge r$ (their $r$ is
  our target rank $k$, their $k$ our $\ell$), failure $e^{-(u-2)/4} + \sqrt{\pi r}\,
  (t/e)^{-(k-r+1)/2}$; (RSVD2) for $k \ge r + 2$. Proposition 8.5 (p. 35), Proposition 8.6 (p. 36),
  Theorem 8.7 (pp. 37 to 38), Lemmas B.1 (p. 47), B.2 (p. 50, with (B.3): $\mathbb{P}\{\operatorname{tr}
  (\mathbf{G}\mathbf{G}^{*})^{-1} > etr/(k-r+1)\} \le \sqrt{\pi r/(k-r+1)}\,t^{-(k-r+1)/2}$), B.3
  (p. 52), the proof of Proposition 8.6 (pp. 53 to 54: conditional Lipschitz concentration of
  $\mathbf{G} \mapsto \|\mathbf{S}\mathbf{G}\mathbf{H}^{\dagger}\|_{\mathsf{F}}$ with constant
  $\|\mathbf{S}\|_{\mathsf{F}}\|\mathbf{H}^{\dagger}\|_{\mathsf{F}}$ and $e^{-(\sqrt{u}-1)^2/2} \le
  e^{-(u-2)/4}$), the proof of Theorem 8.7 (pp. 54 to 56). TW's (B.3) has $\sqrt{\pi r/(k-r+1)}$;
  Theorem 8.1 prints the weaker $\sqrt{\pi r}$.
- MT Theorem 11.5 (p. 473): HMT 10.6 with $(\mathbb{E}Z^2)^{1/2}$, $Z = \|\mathbf{\Gamma}^{\dagger}\|$.
- EW (arXiv:2605.19096 v2) Theorem 3.1 (p. 6): HMT 10.5 for a "full-rank random embedding such that
  $\mathbf{\Omega} \sim \mathbf{U}\mathbf{\Omega}$ for each unitary $\mathbf{U}$", with
  $\alpha_{\mathbb{R}} = 1$ and a minimum over $q$; an embedding is tall ($n \ge \ell$, p. 2).
- Mathlib has no measurable-selection theorem (`Mathlib/Probability/Decision/BayesEstimator.lean`:
  "Once Mathlib has measurable selection theorems, ..."); the library has none either (§3.0).

**Missing infrastructure, per result** (each is a statement of this note unless marked "not
ported"):
- HMT 10.5, TW (RSVD2) in the Gram form and its Schatten, Frobenius and spectral corollaries:
  nothing below the Matrix layer. Three Matrix-layer bridges: $\|\mathbf{B}^{\mathsf{H}}
  \mathbf{B}\|_* = \|\mathbf{B}\|_{\mathsf{F}}^2$, $\|\mathbf{B}^{\mathsf{H}}\mathbf{B}\|_{S_q} =
  \|\mathbf{B}\|_{S_{2q}}^2$, and $\Phi_{\ell^q}(\mathbf{e}_0) = 1$ (M1 to M3). Inputs exist: S1's
  Gram form, L2's frame, R1's block independence and a.s. rank, R4's block moment.
- HMT 10.6, MT 11.5: nothing (R4's spectral block bound is the step).
- Truncated RSVD in Frobenius with HMT's constant: nothing (S1's truncation for free, S2a's T3, T5
  and `IsBestRankApprox.frobNorm_sub_sq_eq_frobNorm_sub_rsvd_sq_add`).
- Truncated RSVD in the spectral norm, expectation: a measurable best-approximation selector,
  which neither the library nor Mathlib has. The statements take one as a hypothesis and are not
  instantiable now (§3.0).
- TW (RSVD1): (i) the law of the diagonal entries of $(\mathbf{G}\mathbf{G}^{\mathsf{H}})^{-1}$
  (proved, but `private`, in `InverseMoments.lean`: `hasLaw_inv_mul_conjTranspose_apply_self`);
  (ii) the inverse-Wishart trace tail (TW (B.3)); (iii) Lipschitz concentration of a Gaussian
  matrix with an independent random factor (the fixed-factor form exists); (iv)
  $\mathbb{E}\|\mathbf{S}\mathbf{G}\mathbf{T}\|_{\mathsf{F}} \le \|\mathbf{S}\|_{\mathsf{F}}
  \|\mathbf{T}\|_{\mathsf{F}}$; (v) the block tail, TW Proposition 8.6 (8.9). TW's constant
  $\sqrt{\pi k}$ is not reached ($2\sqrt{k}$ is).
- HMT 10.7, 10.8: (ii) to (iv) above, and the spectral pseudoinverse tail (Markov on R4's spectral
  moments). HMT Proposition 10.4's two tails are not reached in HMT's form; library forms replace
  them.
- TW 8.7, not ported: parallel sums and the bound $\mathbb{E}[a : \operatorname{tr}
  (\mathbf{G}\mathbf{G}^{\mathsf{H}})^{-1}]$ through the $1/\chi^2_1$ and $1/\chi^2_2$ densities
  ($\ell \in \{k, k+1\}$); the Gaussian spectral second moment $\mathbb{E}\|\mathbf{S}\mathbf{G}
  \mathbf{T}\|_2^2$ (TW Lemma B.1, also S6's need); for Schatten 4, Lemma B.1's
  $\mathbb{E}\|\mathbf{S}\mathbf{G}\mathbf{T}\|_{S_4}^4$ identity and Lemma B.2's
  $\mathbb{E}\|(\mathbf{G}\mathbf{G}^{\mathsf{H}})^{-1}\|_{\mathsf{F}}^2$ (the library has
  $\mathbb{E}\|\mathbf{G}^{+}\|_{\mathsf{F}}^4$ only).
- Rotation-invariant versions (EW Theorem 3.1 and the rest): the Haar law of the polar factor of a
  full-rank left-invariant random matrix, the resulting range transfer and a.s. rank (H1 to H3),
  from R5's characterization, `polarFactor_mul_left` and `rangeProjector_mul_polarFactor`. R5's
  Haar block laws (S4's) are not needed.

## 0. Scope and consumers

$\mathbf{A}$ : `Matrix m n ℝ`; the random test matrix $\mathbf{\Omega}$ is `X : Ω → Matrix n l ℝ` on
a sample space `Ω` (the library's spelling; Q8), with $\ell = \lvert l \rvert$, multiplied on the
right (D2); the target rank is `k : ℕ`. Throughout,
$$\mathbf{E} = \mathbf{A} - \llbracket\mathbf{A}\rrbracket_k,\qquad
\mathrm{OPT} = \|\mathbf{E}\|_{\mathsf{F}},\qquad \sigma_k(\mathbf{A}) = \|\mathbf{E}\|_2
\ \ (\text{library indexing from } 0),\qquad d = \ell - k + 1\ \ (\texttt{hd : k + d = card l + 1}).$$
The error is `A - rsvd A (X ω)`; the late-truncated error is `A - truncatedSVD (rsvd A (X ω)) k`
(maintainer's rules). Prose indexes singular values from $0$, as the library.

| Item | Consumers |
|---|---|
| Gram-form expectation (G1) and its Schatten, Frobenius, spectral corollaries (G2 to G4) | S5 (every Nyström expectation by `conjTranspose_mul_self_sub_nystrom`, one `rw`: TW Corollary 8.2 (NysSVD2), the trace bound of 8.8); S6 (GN in expectation, shape (b): completion factor times G2); S4 (EW 3.2 lands beside G2 as a sharpening); users |
| HMT 10.6 (G5) | users (the first spectral moment, better than $\sqrt{\text{G4}}$ for large $k$, D10); no Nyström twin (brief §4.2) |
| truncated Frobenius expectation (U1) | S5 (truncated Nyström in trace with $1 + \frac{k}{\ell-k-1}$, by S2a's T8 at $\mathbf{F} = \mathbf{H}^{1/2}$, and MT 14.1 through S2a's B16); S6 (truncated-GN baseline $\mathbb{E}(\|\mathbf{A}_\perp\|_{\mathsf{F}}^2 + \gamma^2)$); users |
| selector forms (L8, L9, U2) | S5 and S6 (the template for their choice-dependent expectations); users holding a measurable best approximation |
| tails (P1 to P7) | S5 (NysSVD1 and truncated Nyström tails, by squaring the event); S7 (comparison with the OSI tail); users |
| HMT 10.7, 10.8 forms (P8, P9) | users (sub-Gaussian deviation scaled by $\sigma_k$) |
| rotation-invariant forms (I1 to I5, P10) | S4 (EW 3.2, 3.6(a) are stated for the same hypotheses); S6 (GN with rotation-invariant $\mathbf{\Omega}$); users with Haar or other rotation-invariant test matrices |
| exact recovery (E1, I5) | S5, S6 (the a.s. exact branch at $\operatorname{rank}\mathbf{A} \le \ell$) |
| law-free integrability (L1 to L8) | every expectation of S3; S5, S6, S7 (any law) |
| `gaussianProjectionFactor` | S5, S6 (the completion factor $1 + \frac{q}{p-q-1}$ is `gaussianProjectionFactor q p`, D9; `Sketching/Gaussian/LeastSquares.lean`, hence its RandomMatrix home), S4 (`rotationInvariantFactor` is written through it) |
| `gaussianPinvFrobTail`, `gaussianPinvSpecNormBound` | P1 to P10, S5's tails; later stages' tails |
| RandomMatrix tails (R8 to R10, R14 to R16), independent-factor concentration (R11), Frobenius mean (R12, R13) | P1 to P10; S6, S9 (any conditional Gaussian step with a random factor) |
| H1 to H3 | I1 to I5, P10; S4 (EW's reduction of rotation-invariant laws to Haar); S6 |
| M1 to M3 | G1 to G4, P1 to P4; S5 (trace forms) |

Not in S3: Nyström (S5), GN and sketch-and-solve (S6), EW's sharp bounds (S4), the OSI routes
(S7), early truncation (S2b, S7), complex laws (D3), power and block Krylov methods (brief §8),
sample-size corollaries (none has a consumer; §6).

## 1. Objects

Three named real quantities, no matrix definition, no deviation from Mathlib (they are named
constants, CONTRIBUTING §4 and §5.2, of a kind Mathlib does not have; no entry in
`Mathlib-deviations.md`).

- **`gaussianProjectionFactor (k l : ℕ) : ℝ := 1 + k / (l - k - 1)`** (casts to ℝ), a plain
  `def` with a `_def` simp lemma, because its body is the source's formula (brief D9). Two
  docstring roles (D9, assessment A9): $1 + \mathbb{E}\|\mathbf{G}^{+}\|_{\mathsf{F}}^2$ for a real
  $k \times \ell$ standard Gaussian $\mathbf{G}$ (HMT 10.5's factor), and the completion factor
  $1 + \frac{q}{p-q-1}$ of S6. Junk: for $l \le k + 1$ the denominator is $\le 0$ (Lean's
  $x/0 = 0$ at $l = k + 1$); theorems carry `k + 2 ≤ l`. Home: `RandomMatrix/Gaussian/BlockTail.lean`
  (file 3), because S6's `Sketching/Gaussian/LeastSquares.lean` (D8) sits below `LowRank`. Names
  fixed here for the later factors (D9): `rotationInvariantFactor r l q := (r - l) / (r - q) *
  gaussianProjectionFactor q l` (S4) and `haarProjectionFactor d p q := 1 + (d - p) / (d - q) *
  (q / (p - q - 1))` (S6), both named for the law they belong to, never for how good they are.
- **`gaussianPinvFrobTail (k d : ℕ) (t : ℝ) : ℝ`**, an `irreducible_def` (rule 2: the proved
  constant is not the source's) with body $2\sqrt{k}\,(e/t)^{d/2}$. It bounds
  $\mathbb{P}\{\|\mathbf{G}^{+}\|_{\mathsf{F}}^2 > tk/d\}$ for a real $k \times (k + d - 1)$
  standard Gaussian. Docstring: source value $\sqrt{\pi k/d}\,(e/t)^{d/2}$ (TW (B.3)), printed as
  $\sqrt{\pi k}\,(e/t)^{d/2}$ in TW Theorem 8.1; proved value $2\sqrt{k}\,(e/t)^{d/2}$; gap
  factor $2/\sqrt{\pi} \approx 1.13$ against Theorem 8.1, $2\sqrt{d/\pi}$ against (B.3). API:
  `gaussianPinvFrobTail_nonneg`, `gaussianPinvFrobTail_le` (the explicit upper comparison). An
  improvement to TW's constant changes the body and the comparison only.
- **`gaussianPinvSpecNormBound (r k : ℕ) : ℝ`**, an `irreducible_def` with body
  $\frac{e}{k-r}\sqrt{(k+r-1)/2}$, R4's constant for $(\mathbb{E}\|\mathbf{G}^{+}\|_2^q)^{1/q}$
  (R4 Q1: what the probe proof reaches, not HMT's $e\sqrt{k}/(k-r)$). S3 would write R4's
  expression seven more times (G5, I3, R10, R15, R16, P8, P9), which CONTRIBUTING §4 forbids. API:
  `gaussianPinvSpecNormBound_nonneg`, `gaussianPinvSpecNormBound_le` (against HMT's
  $e\sqrt{k}/(k - r)$, for $r < k$). R4's three statements that inline it are restated with the
  name at S3's wrap-up (Q8).

**§5.3 rows** (added by the PR that adds file 5; two reviews, CONTRIBUTING §9):

| Concept | Spelling | Bridge |
|---|---|---|
| rotation-invariant random test matrix (new row) | `HasLaw X ν μ` with `[IsProbabilityMeasure ν] [IsLeftUnitarilyInvariant ν]` and full column rank almost surely, `∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec`; the Gaussian and the Haar frame (for $\ell \le n$) are instances | `hasLaw_polarFactor_of_isLeftUnitarilyInvariant` (H1); `isLeftUnitarilyInvariant_haarFrame`, `HasOrthonormalCols.mulVec_injective` |
| measurable best approximation of a random output (new row) | `(hY : ∀ ω, IsBestRankApprox (rsvd A (X ω)) k (Y ω)) (hYm : AEStronglyMeasurable Y μ)`, only where the quantity depends on the choice (S2a §8 item 15); never a bound-only expectation of a choice-dependent `truncatedSVD` error | `isBestRankApprox_truncatedSVD` (pointwise, no measurability) |

**Used directly.** S0: `rsvd`, `sub_rsvd`, `rsvd_eq_self_of_rank_eq`. S1: `SymmetricGauge.matrixNorm_conjTranspose_mul_self_sub_rsvd_le`,
`SymmetricGauge.matrixNorm_sub_rsvd_le`, `HasOrthonormalCols.specNorm_sub_rsvd_le`,
`HasOrthonormalCols.frobNorm_sub_rsvd_sq_le`, `HasOrthonormalCols.frobNorm_sub_mul_truncatedSVD_sq_le`
(truncation for free), `exists_hasOrthonormalCols_mul_mul_conjTranspose_eq_truncatedSVD` (L2).
S2a: `HasOrthonormalCols.frobNorm_sub_truncatedSVD_rsvd` (T5), `frobNorm_sub_truncatedSVD_rsvd_sq`
(T3), `IsBestRankApprox.frobNorm_sub_sq_eq_frobNorm_sub_rsvd_sq_add`,
`specNorm_sub_sq_add_frobNorm_sub_truncatedSVD_sq_le_of_rank_le` (B15), `isBestRankApprox_truncatedSVD`,
`IsBestRankApprox.frobNorm_sub`, `.rank_le`. Matrix layer: `frobNorm_sub_truncatedSVD_sq`,
`specNorm_sub_truncatedSVD`, `truncatedSVD_of_rank_le`, `HasOrthonormalCols.exists_fromCols`,
`HasOrthonormalCols.mul_conjTranspose_add_mul_conjTranspose`, `exists_hasOrthonormalCols_range_eq`,
`HasOrthonormalCols.mulVec_injective`, `mulVec_injective_iff_rank_eq`, `rank_rangeProjector`,
`IsStarProjection.singularValues_mul_le`, `singularValues_conjTranspose_mul_self`,
`matrixNorm_le_of_singularValues_le`, `matrixNorm_le_apply_single_mul_nuclearNorm`,
`SymmetricGauge.apply_single_pos`, `SymmetricGauge.continuous_matrixNorm`,
`lpGauge_matrixNorm`, `lpGauge_one_matrixNorm`, `lpGauge_top_matrixNorm`, `continuous_schattenNorm`,
`continuous_singularValues`, `Matrix.PosSemidef.nuclearNorm_eq_re_trace`, `frobNorm_sq_eq_re_trace`,
`frobNorm_pinv_sq_eq_re_trace_inv_of_injective_conjTranspose`, `polarFactor_mul_left`,
`rangeProjector_mul_polarFactor`, `hasOrthonormalCols_polarFactor_iff`. Measurability:
`measurable_rangeProjector`, `measurable_pinv`, `measurable_singularValues`, `measurable_frobNorm`,
`measurable_specNorm`, `measurable_polarFactor`. RandomMatrix: `ae_rank_mul_eq_min_of_hasLaw_gaussianMatrix`,
`ae_rank_eq_min_of_hasLaw_gaussianMatrix`, `indepFun_conjTranspose_mul_of_hasLaw_gaussianMatrix`,
`hasLaw_const_mul_of_hasLaw_gaussianMatrix`, `integral_frobNorm_mul_mul_sq_of_hasLaw_gaussianMatrix`,
`integral_frobNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix` and its `integrable_` twin,
`integral_specNorm_mul_mul_pinv_le_of_hasLaw_gaussianMatrix` and its `integrable_` twin,
`integral_specNorm_mul_mul_le_of_hasLaw_gaussianMatrix` (Chevet),
`integral_specNorm_pinv_rpow_le_of_hasLaw_gaussianMatrix`, `integrable_specNorm_pinv_rpow_of_hasLaw_gaussianMatrix`,
`measureReal_integral_add_le_of_hasLaw_gaussianMatrix`, `integrable_comp_of_hasLaw_gaussianMatrix`,
`measureReal_norm_sq_le_le_rpow_of_hasLaw_gaussianVector` (χ² small ball),
`hasLaw_haarFrame_of_isLeftUnitarilyInvariant`, `hasLaw_rangeProjector_mul_of_hasLaw_haarFrame`,
`ae_rank_mul_eq_min_of_hasLaw_haarFrame`, `isLeftUnitarilyInvariant_gaussianMatrix`,
`isLeftUnitarilyInvariant_haarFrame`, `ae_hasOrthonormalCols_of_hasLaw_haarFrame`. Mathlib:
`MeasureTheory.integral_mono_ae`, `integral_mono_of_nonneg`, `measureReal_mono`, `measureReal_union_le`,
`HasLaw.integral_comp`, `indepFun_iff_map_prod_eq_prod_map_map`, `Measure.prod_apply`,
`MeasureTheory.lintegral_eq_lintegral_meas_lt` and `Integrable.integral_eq_integral_meas_lt`
(layer cake), `pow_sum_div_card_le_sum_pow`, `MeasureTheory.integral_undef`.

**Mathlib search** ("searched, none" unless named): randomized SVD or range-finder bounds;
inverse-Wishart laws or trace tails; Lipschitz concentration conditional on an independent
variable (Mathlib's Gaussian concentration is for fixed functions; the library's is
`measureReal_integral_add_le_of_hasLaw_gaussianMatrix`); measurable selection (none, cited
above); rotation-invariant laws on matrices (the library's classes, deviation 14).

## 2. Interfaces

No new predicate. Hypotheses, each an existing spelling:
- `HasLaw X (gaussianMatrix n l) μ` (D2); `IsProbabilityMeasure μ` follows (`hX.isProbabilityMeasure`)
  and is not repeated (CONTRIBUTING §5.2).
- Rotation-invariant: the §5.3 row of §1 (Q5).
- `k + 2 ≤ Fintype.card l` for expectations ($\ell \ge k + 2$, HMT's $p \ge 2$, TW's $k \ge r + 2$);
  `hd : k + d = Fintype.card l + 1` for the TW tails (the §5.3 index-shift row: $d = \ell - k + 1$
  is the χ² degree of freedom); `k + 1 ≤ Fintype.card l` added for the HMT 10.7, 10.8 forms.
- `IsBestRankApprox` (S2a) for choice-dependent statements.
- `AEMeasurable X μ`, `[IsFiniteMeasure μ]` for the law-free companions.

## 3. Statement shapes

`namespace NLAlib`, `open MeasureTheory ProbabilityTheory`, `open scoped Matrix ENNReal`.
Variables `{Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n l : Type*} [Fintype m]
[Fintype n] [Fintype l]`; `{X : Ω → Matrix n l ℝ}` in the Gaussian and rotation-invariant
sections, over `𝕜` in §3.1. No statement displays a `1` or an `HasOrthonormalCols` (S1 Q4), so no
`[DecidableEq]` except `[DecidableEq n]` with `IsLeftUnitarilyInvariant` (its class needs it) and
`[DecidableEq l]` with `haarFrame` and `polarFactor` (file 5); proofs use `classical`. Docstrings
are shortened; the full ones carry §5's citations, LaTeX throughout (CONTRIBUTING §6 item 5).

### 3.0 Degenerate cases and measurability

**Degenerate cases** (checked for every statement; the proof routes say where a case bites).
- *$\ell \in \{k, k+1\}$.* HMT's and TW's expectations diverge there. The hypothesis
  `k + 2 ≤ card l` is necessary, not cosmetic: at $\ell = k + 1$ Lean reads $k/(\ell - k - 1)$ as
  $k/0 = 0$, and G2 would claim $\mathbb{E}\|\mathbf{A} - \mathbf{P}_{\mathbf{Y}}\mathbf{A}
  \|_{\mathsf{F}}^2 \le \mathrm{OPT}^2$, false: for $\mathbf{A} = \operatorname{diag}(1, \delta,
  \delta)$, $k = 1$, $\ell = 2$, the error is about $\delta^2(1 + X^2/(Y^2 + Z^2))$ with
  $(Y, Z) = \mathbf{M}\mathbf{a}$ for a standard Gaussian $\mathbf{a} \in \mathbb{R}^2$ independent of
  $\mathbf{M}$ and $\det\mathbf{M} = X$, so the ratio to $\mathrm{OPT}^2 = 2\delta^2$
  grows without bound as $\delta \to 0$ (an inverse $\chi^2_2$ factor; TW 8.7's logarithmic
  bound there is consistent with it). The tails need only
  $\ell \ge k$, as TW. `hd` also admits $d = 0$, that is $k = \ell + 1$; there the threshold is
  Lean's $x/0 = 0$ but the failure bound contains `gaussianPinvFrobTail k 0 t` $= 2\sqrt{k} \ge 2$,
  so the statements hold trivially and need no further hypothesis (the proofs split off $d = 0$).
- *$k = 0$.* $\llbracket\mathbf{A}\rrbracket_0 = \mathbf{0}$, $\mathbf{E} = \mathbf{A}$, the excess
  terms vanish (`k / … = 0`, $\sqrt{0} = 0$, `gaussianPinvFrobTail 0 d t = 0`), and every statement
  reduces to the contraction $\|(\mathbf{I}-\mathbf{P})\mathbf{A}\|_\Phi \le \|\mathbf{A}\|_\Phi$:
  the tail events are empty, the expectations hold pointwise. The proofs need no case split (the
  frame is `Fin 0`, R4's block moment is $0$).
- *$\operatorname{rank}\mathbf{A} \le k$.* $\mathbf{E} = \mathbf{0}$ and every right side is $0$
  (or $\sigma_k = 0$). Since $k \le \ell$, $\operatorname{rank}(\mathbf{A}\mathbf{X}) =
  \operatorname{rank}\mathbf{A}$ a.s. (R1), so the error is $\mathbf{0}$ a.s. (E1). This is why the
  tail events are written $\neg(\text{error} \le \text{bound})$: a non-strict event
  $\{\text{bound} \le \text{error}\}$ would have probability one here while the bound can be below
  one (Q10).
- *$k > \lvert n\rvert$.* No frame of size $k$ exists (L2 needs `k ≤ card n`), but then
  $\operatorname{rank}\mathbf{A} \le \lvert n\rvert < k \le \ell$, the previous case. Every Gaussian
  proof splits on `k ≤ card n` once; no statement carries the hypothesis (HMT's
  $k + p \le \min\{m, n\}$ is not needed anywhere).
- *More samples than the dimension, $\ell > \lvert n\rvert$.* Gaussian statements hold as stated
  (R1's a.s. rank is shape-free). The rotation-invariant hypothesis "full column rank a.s." is then
  unsatisfiable (an embedding is tall, EW p. 2), so those statements are vacuous there; the Haar
  frame with $\ell > n$ has orthonormal rows and is exact a.s. by `ae_rank_mul_eq_min_of_hasLaw_haarFrame`.
- *Empty index types.* $l$ empty forces $k = 0$ in the tails and is excluded from the expectations
  by `k + 2 ≤ card l`; $m$ or $n$ empty makes $\mathbf{A} = \mathbf{0}$ and every statement $0 \le 0$
  or an empty event.
- *$\mathbf{V}_1^{\mathsf{H}}\mathbf{\Omega}$ without full row rank.* For the Gaussian it has full
  row rank a.s. when $k \le \ell$ (`ae_rank_mul_eq_min_of_hasLaw_gaussianMatrix Zᴴ`); for a
  rotation-invariant law by H3 at $\mathbf{Z}^{\mathsf{H}}$. S1's hypothesis
  `(Xᴴ * Z).rank = Z.rank` is supplied a.s. and the pointwise bounds are integrated with
  `integral_mono_ae`.
- *Ties* $\sigma_{k-1}(\mathbf{P}\mathbf{A}) = \sigma_k(\mathbf{P}\mathbf{A})$: below.
- *Tail parameters.* `0 < t` is necessary: at $t = 0$, $(e/t)^{d/2}$ is Lean's $0^{d/2} = 0$ and P1
  would claim the deterministic part alone with failure $e^{-(u-2)/4}$, false for large $u$. $u$ is
  free: for $u < 2$ (P1 to P7) or $u = 0$ (P8, P9) the bound is at least one.

**Measurability of truncated outputs, plainly** (S2a §7 Q3 and §8 item 15, decided there as
option (a)). `truncatedSVD` is a choice (a `Classical.choose` of an SVD), so `fun ω =>
truncatedSVD (rsvd A (X ω)) k` is not known to be measurable, and under a Gaussian law it is not
unique (for $\mathbf{A} = \mathbf{I}$ the tie holds with probability one, S2a §8 item 1). Three
consequences for S3:
1. **Choice-free quantities are stated on the named output, with their `integrable_` companions.**
   The squared Frobenius error of the truncated RSVD is choice-free: by S2a's T3 and
   `frobNorm_sub_truncatedSVD_sq` it equals $\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{\mathsf{F}}^2 +
   \sum_{i \ge k}\sigma_i(\mathbf{P}\mathbf{A})^2$, a measurable function of $\omega$. Affected
   statements: none. L7, U1, I4 and the tail P5 are on `A - truncatedSVD (rsvd A (X ω)) k`
   directly.
2. **Choice-dependent expectations take a measurable selector and are not instantiable now.** The
   spectral error of the truncated RSVD depends on the choice (S2a §8 item 2's example). Its
   expectation is stated for any `Y` with `hY : ∀ ω, IsBestRankApprox (rsvd A (X ω)) k (Y ω)` and
   `hYm : AEStronglyMeasurable Y μ`. The library cannot yet exhibit such a `Y`: there is no
   measurable-selection theorem in the library or in Mathlib, and `truncatedSVD` itself is not known
   to be measurable. So **L8, L9 and U2 cannot be applied to any concrete algorithm today**; each
   docstring says so. They are stated because they are the form a measurable `truncatedSVD`
   (S2a Q3's option (c)) or a measurable selection theorem will instantiate, and because S5 and S6
   follow the same pattern. S3 states **no** bound-only expectation of
   `specNorm (A - truncatedSVD (rsvd A (X ω)) k)`: it would be provable
   (`integral_mono_of_nonneg` needs only the dominating side integrable), but a Bochner integral of
   a non-integrable function is $0$ in Lean (`MeasureTheory.integral_undef`), so for a possibly
   non-measurable integrand such a bound says nothing about the algorithm. The prototype's
   `integral_specNorm_residual_le_of_gaussian` relied on exactly that ("the left side is 0 if not
   integrable"); it is not reproduced.
3. **Choice-dependent tails need no selector and are instantiable.** `μ.real s` is defined for every
   set: for a non-measurable $s$ it is the outer measure, which is monotone (`measureReal_mono`).
   The truncated spectral tails P6 (for any best approximation `Y`, no measurability) and P7 (for
   `truncatedSVD (rsvd A (X ω)) k`) are proved by including the failure event in the measurable
   failure event of the block tail R14, so their statement says exactly what a user needs: the
   failure event lies inside a measurable event of the stated probability
   (`exists_measurable_superset`). Each docstring says this.

So the measurability-affected S3 statements are exactly L8, L9 and U2 (selector hypotheses, not
instantiable); P6 and P7 are choice-dependent but unaffected; U1, L7, I4, P5 are choice-free.

### 3.1 `LowRank/Gaussian/RangeFinder.lean`: law-free integrability and the selector reduction (9)

Over `𝕜`, any law. `{X : Ω → Matrix n l 𝕜}`. Labels, in order: L1 to L9.

```lean
/-- The Gram matrix of the range finder's error in any unitarily invariant norm is integrable
for every measurable test matrix: it is measurable and bounded by
$\|\mathbf{A}^{\mathsf{H}}\mathbf{A}\|_{\Phi}$. -/
theorem SymmetricGauge.integrable_matrixNorm_conjTranspose_mul_self_sub_rsvd (Φ : SymmetricGauge)
    [IsFiniteMeasure μ] (A : Matrix m n 𝕜) (hX : AEMeasurable X μ) :
    Integrable (fun ω => Φ.matrixNorm ((A - rsvd A (X ω))ᴴ * (A - rsvd A (X ω)))) μ
theorem SymmetricGauge.integrable_matrixNorm_sub_rsvd (Φ : SymmetricGauge) [IsFiniteMeasure μ]
    (A : Matrix m n 𝕜) (hX : AEMeasurable X μ) :
    Integrable (fun ω => Φ.matrixNorm (A - rsvd A (X ω))) μ
theorem integrable_schattenNorm_sub_rsvd_sq [IsFiniteMeasure μ] {q : ℝ≥0∞} (hq : 1 ≤ q)
    (A : Matrix m n 𝕜) (hX : AEMeasurable X μ) :
    Integrable (fun ω => schattenNorm q (A - rsvd A (X ω)) ^ 2) μ
theorem integrable_frobNorm_sub_rsvd_sq [IsFiniteMeasure μ] (A : Matrix m n 𝕜)
    (hX : AEMeasurable X μ) : Integrable (fun ω => frobNorm (A - rsvd A (X ω)) ^ 2) μ
theorem integrable_specNorm_sub_rsvd_sq [IsFiniteMeasure μ] (A : Matrix m n 𝕜)
    (hX : AEMeasurable X μ) : Integrable (fun ω => specNorm (A - rsvd A (X ω)) ^ 2) μ
theorem integrable_specNorm_sub_rsvd [IsFiniteMeasure μ] (A : Matrix m n 𝕜)
    (hX : AEMeasurable X μ) : Integrable (fun ω => specNorm (A - rsvd A (X ω))) μ
/-- The squared Frobenius error of the late-truncated randomized SVD is integrable for every
measurable test matrix. It does not depend on the choice made by `truncatedSVD`
(`frobNorm_sub_truncatedSVD_rsvd_sq`), which is what makes it measurable. -/
theorem integrable_frobNorm_sub_truncatedSVD_rsvd_sq [IsFiniteMeasure μ] (A : Matrix m n 𝕜)
    (hX : AEMeasurable X μ) (k : ℕ) :
    Integrable (fun ω => frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2) μ
/-- For a measurable choice $\mathbf{Y}$ of best rank-$k$ approximations of the randomized SVD,
$\|\mathbf{A} - \mathbf{Y}\|_2^2$ is integrable. The library has no measurable selector yet, so
this cannot be applied to `truncatedSVD (rsvd A (X ω)) k` (whose measurability is unknown). -/
theorem integrable_specNorm_sub_sq_of_isBestRankApprox [IsFiniteMeasure μ] (A : Matrix m n 𝕜)
    {k : ℕ} {Y : Ω → Matrix m n 𝕜} (hY : ∀ ω, IsBestRankApprox (rsvd A (X ω)) k (Y ω))
    (hYm : AEStronglyMeasurable Y μ) : Integrable (fun ω => specNorm (A - Y ω) ^ 2) μ
/-- **Reverse Eckart–Young in expectation**: for a measurable choice $\mathbf{Y}$ of best rank-$k$
approximations of $\mathbf{P}_{\mathbf{A}\mathbf{X}}\mathbf{A}$,
$$\mathbb{E}\|\mathbf{A} - \mathbf{Y}\|_2^2 + \|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k
\|_{\mathsf{F}}^2 \le \sigma_k(\mathbf{A})^2 + \mathbb{E}\|\mathbf{A} -
\llbracket\mathbf{P}_{\mathbf{A}\mathbf{X}}\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,,$$
for every law: a Frobenius bound for the truncated output becomes a spectral one at no cost.
Not instantiable until a measurable selector exists. [Gu2015, Theorem 3.4];
[TroppYurtseverUdellCevher2017a, Proposition A.8]; [TroppWebber2023, p. 42]. -/
theorem integral_specNorm_sub_sq_add_frobNorm_sub_truncatedSVD_sq_le_of_isBestRankApprox
    [IsProbabilityMeasure μ] (A : Matrix m n 𝕜) (hX : AEMeasurable X μ) {k : ℕ}
    {Y : Ω → Matrix m n 𝕜} (hY : ∀ ω, IsBestRankApprox (rsvd A (X ω)) k (Y ω))
    (hYm : AEStronglyMeasurable Y μ) :
    ∫ ω, specNorm (A - Y ω) ^ 2 ∂μ + frobNorm (A - truncatedSVD A k) ^ 2 ≤
      singularValues A k ^ 2 + ∫ ω, frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 ∂μ
```

Proof routes. *L1:* measurability from `measurable_rangeProjector` composed with `hX` (`rsvd` is
`rangeProjector (A * X) * A`) and `Φ.continuous_matrixNorm`; the bound
$\sigma_i(((\mathbf{I}-\mathbf{P})\mathbf{A})^{\mathsf{H}}(\mathbf{I}-\mathbf{P})\mathbf{A}) =
\sigma_i((\mathbf{I}-\mathbf{P})\mathbf{A})^2 \le \sigma_i(\mathbf{A})^2$
(`singularValues_conjTranspose_mul_self`, `sub_rsvd`, `IsStarProjection.singularValues_mul_le`),
`matrixNorm_le_of_singularValues_le`; `Integrable.of_bound`. *L2:* the same without the square.
*L3:* L2 at `lpGauge q`, `lpGauge_matrixNorm`, then the square of a bounded measurable function.
*L4, L5:* L3 at $q = 2$, $\top$ (`schattenNorm_two`, `schattenNorm_top`). *L6:* L2 at `lpGauge ⊤`.
*L7:* `frobNorm_sub_truncatedSVD_rsvd_sq` and `frobNorm_sub_truncatedSVD_sq` rewrite the integrand,
by `funext`, to $\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{\mathsf{F}}^2 + \sum_{i \in [k,
\min(m,n))}\sigma_i(\mathbf{P}\mathbf{A})^2$, measurable by `measurable_singularValues`; bounded by
$2\|\mathbf{A}\|_{\mathsf{F}}^2$. *L8:* bound $\|\mathbf{A} - \mathbf{Y}\|_2 \le \|\mathbf{A}\|_2 +
\|\mathbf{Y}\|_{\mathsf{F}}$ and $\|\mathbf{Y}\|_{\mathsf{F}} \le \|\mathbf{C}\|_{\mathsf{F}} +
\|\mathbf{C} - \mathbf{Y}\|_{\mathsf{F}} \le 2\|\mathbf{C}\|_{\mathsf{F}} \le 2\|\mathbf{A}\|_{\mathsf{F}}$
($\mathbf{C} = \mathbf{P}\mathbf{A}$; `hY.frobNorm_sub_le` against $\mathbf{0}$); measurability
from `hYm`; no measurability of `X` is needed. *L9:* pointwise B15 at $\mathbf{B} = \mathbf{Y}(\omega)$
(`(hY ω).rank_le`); $\|\mathbf{A} - \mathbf{Y}\|_{\mathsf{F}}^2 = \|\mathbf{A} -
\llbracket\mathbf{P}\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$ by
`IsBestRankApprox.frobNorm_sub_sq_eq_frobNorm_sub_rsvd_sq_add` at both best approximations and
`IsBestRankApprox.frobNorm_sub`; integrate (`integral_add`, `integral_const`, `integral_mono` with
L7 and L8). Degenerate: $k = 0$ forces $\mathbf{Y} = \mathbf{0}$ and L9 reads
$\|\mathbf{A}\|_2^2 + \|\mathbf{A}\|_{\mathsf{F}}^2 \le \sigma_0^2 + \|\mathbf{A}\|_{\mathsf{F}}^2$,
equality; $k \ge \operatorname{rank}\mathbf{A}$: $\sigma_k = 0$.

### 3.2 `RandomMatrix/Gaussian/BlockTail.lean` and two registered files: the RandomMatrix additions (19 + 1)

Real, `{r k s a : Type*}` finite, `{X : Ω → Matrix r k ℝ}` or `Matrix n k ℝ` as R4 writes them (R4's
letters: $r \times k$ for the block, $k$ its number of columns). Labels, in order: N1 to N10 for the
three named quantities and their API; then R8 to R16 (the numbering starts at R8 because R1 to R5
name the RandomMatrix stages, which this note cites).

```lean
/-! Named quantities -/
/-- **The Gaussian projection factor** $1 + \frac{k}{l - k - 1}$: HMT's factor
$1 + \mathbb{E}\|\mathbf{G}^{+}\|_{\mathsf{F}}^2$ for a $k \times l$ standard Gaussian, and the
completion factor of Gaussian sketch-and-solve. Junk for $l \le k + 1$. -/
noncomputable def gaussianProjectionFactor (k l : ℕ) : ℝ := 1 + (k : ℝ) / ((l : ℝ) - k - 1)
@[simp] theorem gaussianProjectionFactor_def (k l : ℕ) :
    gaussianProjectionFactor k l = 1 + (k : ℝ) / ((l : ℝ) - k - 1)
theorem one_le_gaussianProjectionFactor {k l : ℕ} (h : k + 2 ≤ l) : 1 ≤ gaussianProjectionFactor k l
theorem gaussianProjectionFactor_le_gaussianProjectionFactor {k k' l : ℕ} (hk : k ≤ k')
    (h : k' + 2 ≤ l) : gaussianProjectionFactor k l ≤ gaussianProjectionFactor k' l
/-- The tail of $\|\mathbf{G}^{+}\|_{\mathsf{F}}^2$ at level $tk/d$ for a $k \times (k + d - 1)$
standard Gaussian. Source: $\sqrt{\pi k/d}\,(e/t)^{d/2}$ [TroppWebber2023, Lemma B.2 (B.3)]
($\sqrt{\pi k}$ in their Theorem 8.1); proved: $2\sqrt{k}\,(e/t)^{d/2}$. -/
noncomputable irreducible_def gaussianPinvFrobTail (k d : ℕ) (t : ℝ) : ℝ :=
  2 * √(k : ℝ) * (Real.exp 1 / t) ^ ((d : ℝ) / 2)
theorem gaussianPinvFrobTail_nonneg (k d : ℕ) {t : ℝ} (ht : 0 < t) : 0 ≤ gaussianPinvFrobTail k d t
theorem gaussianPinvFrobTail_le (k d : ℕ) {t : ℝ} (ht : 0 < t) :
    gaussianPinvFrobTail k d t ≤ 2 * √(k : ℝ) * (Real.exp 1 / t) ^ ((d : ℝ) / 2)
/-- R4's bound on the spectral moments of $\mathbf{G}^{+}$ for an $r \times k$ standard Gaussian,
$\frac{e}{k - r}\sqrt{(k + r - 1)/2}$; HMT Proposition 10.2 has $e\sqrt{k}/(k - r)$. -/
noncomputable irreducible_def gaussianPinvSpecNormBound (r k : ℕ) : ℝ :=
  Real.exp 1 / ((k : ℝ) - r) * √(((k : ℝ) + r - 1) / 2)
theorem gaussianPinvSpecNormBound_nonneg {r k : ℕ} (h : r < k) : 0 ≤ gaussianPinvSpecNormBound r k
theorem gaussianPinvSpecNormBound_le {r k : ℕ} (h : r < k) :
    gaussianPinvSpecNormBound r k ≤ Real.exp 1 * √(k : ℝ) / ((k : ℝ) - r)

/-! Tails of the pseudoinverse -/
/-- The diagonal entries of $(\mathbf{G}\mathbf{G}^{\mathsf{H}})^{-1}$ are $1/\chi^2_d$, so for
$s > 0$, $\mathbb{P}\{s \le (\mathbf{G}\mathbf{G}^{\mathsf{H}})^{-1}_{ii}\} \le (e/(sd))^{d/2}$,
$d = \lvert k\rvert - \lvert r\rvert + 1$. -/
theorem measureReal_le_inv_mul_conjTranspose_apply_self_le_of_hasLaw_gaussianMatrix
    [DecidableEq r] (hX : HasLaw X (gaussianMatrix r k) μ) {d : ℕ}
    (hd : Fintype.card r + d = Fintype.card k + 1) (i : r) {s : ℝ} (hs : 0 < s) :
    μ.real {ω | s ≤ (X ω * (X ω)ᴴ)⁻¹ i i} ≤ (Real.exp 1 / (s * d)) ^ ((d : ℝ) / 2)
/-- **The trace tail of an inverse Wishart matrix**: for an $r \times k$ standard Gaussian,
$d = \lvert k\rvert - \lvert r\rvert + 1$ and $t > 0$,
$\mathbb{P}\{\|\mathbf{G}^{+}\|_{\mathsf{F}}^2 > t\lvert r\rvert/d\}$ is at most
`gaussianPinvFrobTail`. Result: inverse-wishart-trace-tail -/
theorem measureReal_not_frobNorm_pinv_sq_le_le_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix r k) μ) {d : ℕ} (hd : Fintype.card r + d = Fintype.card k + 1)
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | ¬ frobNorm (pinv (X ω)) ^ 2 ≤ t * Fintype.card r / d} ≤
      gaussianPinvFrobTail (Fintype.card r) d t
/-- The spectral tail of $\mathbf{G}^{+}$, by Markov's inequality at R4's moment of order
$\lvert k\rvert - \lvert r\rvert$: $\mathbb{P}\{\|\mathbf{G}^{+}\|_2 > tC\} \le
t^{-(\lvert k\rvert - \lvert r\rvert)}$ with $C$ = `gaussianPinvSpecNormBound`. -/
theorem measureReal_not_specNorm_pinv_le_le_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix r k) μ) (hrk : Fintype.card r < Fintype.card k) {t : ℝ}
    (ht : 0 < t) :
    μ.real {ω | ¬ specNorm (pinv (X ω)) ≤
        t * gaussianPinvSpecNormBound (Fintype.card r) (Fintype.card k)} ≤
      t ^ (-((Fintype.card k : ℝ) - Fintype.card r))

/-! Concentration with an independent factor (home: `Gaussian/Concentration.lean`) -/
/-- **Gaussian concentration with an independent random factor**: if $\mathbf{G}$ is a standard
Gaussian matrix independent of $Y$ and, for each $y$, $f(y, \cdot)$ is $L(y)$-Lipschitz for the
Frobenius distance with Gaussian mean at most $c(y)$, then
$\mathbb{P}\{f(Y, \mathbf{G}) > c(Y) + L(Y)t\} \le e^{-t^2/2}$.
Result: gaussian-lipschitz-concentration -/
theorem measureReal_not_le_add_mul_le_of_hasLaw_gaussianMatrix_of_indepFun {β : Type*}
    [MeasurableSpace β] {X : Ω → Matrix m n ℝ} {Y : Ω → β} (hX : HasLaw X (gaussianMatrix m n) μ)
    (hY : AEMeasurable Y μ) (hXY : IndepFun Y X μ) {f : β → Matrix m n ℝ → ℝ}
    (hf : Measurable (Function.uncurry f)) {L c : β → ℝ} (hL : Measurable L) (hc : Measurable c)
    (hlip : ∀ y A B, |f y A - f y B| ≤ L y * frobNorm (A - B))
    (hmean : ∀ y, ∫ A, f y A ∂(gaussianMatrix m n) ≤ c y) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | ¬ f (Y ω) (X ω) ≤ c (Y ω) + L (Y ω) * t} ≤ Real.exp (-t ^ 2 / 2)

/-! The Frobenius mean (home: `Gaussian/Moments.lean`) -/
theorem integrable_frobNorm_mul_mul_of_hasLaw_gaussianMatrix {X : Ω → Matrix m n ℝ}
    (hX : HasLaw X (gaussianMatrix m n) μ) (S : Matrix a m ℝ) (T : Matrix n b ℝ) :
    Integrable (fun ω => frobNorm (S * X ω * T)) μ
/-- $\mathbb{E}\|\mathbf{S}\mathbf{G}\mathbf{T}\|_{\mathsf{F}} \le \|\mathbf{S}\|_{\mathsf{F}}
\|\mathbf{T}\|_{\mathsf{F}}$. [HalkoMartinssonTropp2011, Proposition 10.1] with Jensen. -/
theorem integral_frobNorm_mul_mul_le_of_hasLaw_gaussianMatrix {X : Ω → Matrix m n ℝ}
    (hX : HasLaw X (gaussianMatrix m n) μ) (S : Matrix a m ℝ) (T : Matrix n b ℝ) :
    ∫ ω, frobNorm (S * X ω * T) ∂μ ≤ frobNorm S * frobNorm T

/-! The block tails -/
/-- **The range finder's block tail** (TW Proposition 8.6, (8.9)): with the hypotheses of
`integral_frobNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix`, $d = \lvert k\rvert - \lvert r
\rvert + 1$, any $u$ and $t > 0$,
$$\mathbb{P}\Bigl\{\|\mathbf{S}\mathbf{G}_2\mathbf{G}_1^{+}\|_{\mathsf{F}}^2 >
\frac{ut\lvert r\rvert}{d}\|\mathbf{S}\|_{\mathsf{F}}^2\Bigr\} \le e^{-(u-2)/4} +
\texttt{gaussianPinvFrobTail}\,\lvert r\rvert\,d\,t\,. $$ -/
theorem measureReal_not_frobNorm_mul_mul_pinv_sq_le_le_of_hasLaw_gaussianMatrix [DecidableEq r]
    [DecidableEq s] {X : Ω → Matrix n k ℝ} (hX : HasLaw X (gaussianMatrix n k) μ)
    {V₁ : Matrix n r ℝ} {V₂ : Matrix n s ℝ} (hV₁ : HasOrthonormalCols V₁)
    (hV₂ : HasOrthonormalCols V₂) (h₁₂ : V₁ᴴ * V₂ = 0) {d : ℕ}
    (hd : Fintype.card r + d = Fintype.card k + 1) (S : Matrix a s ℝ) (u : ℝ) {t : ℝ}
    (ht : 0 < t) :
    μ.real {ω | ¬ frobNorm (S * (V₂ᴴ * X ω) * pinv (V₁ᴴ * X ω)) ^ 2 ≤
        u * t * Fintype.card r / d * frobNorm S ^ 2} ≤
      Real.exp (-(u - 2) / 4) + gaussianPinvFrobTail (Fintype.card r) d t
/-- The spectral block tail in the shape of HMT's proof of Theorem 10.8, with $C$ =
`gaussianPinvSpecNormBound |r| |k|`:
$\|\mathbf{S}\mathbf{G}_2\mathbf{G}_1^{+}\|_2 \le t(\|\mathbf{S}\|_2\sqrt{\lvert r\rvert/d} +
\|\mathbf{S}\|_{\mathsf{F}}C) + utC\|\mathbf{S}\|_2$ outside probability
$t^{-(\lvert k\rvert - \lvert r\rvert)} + \texttt{gaussianPinvFrobTail}\,\lvert r\rvert\,d\,t^2 +
e^{-u^2/2}$. -/
theorem measureReal_not_specNorm_mul_mul_pinv_le_le_of_hasLaw_gaussianMatrix [DecidableEq r]
    [DecidableEq s] {X : Ω → Matrix n k ℝ} (hX : HasLaw X (gaussianMatrix n k) μ)
    {V₁ : Matrix n r ℝ} {V₂ : Matrix n s ℝ} (hV₁ : HasOrthonormalCols V₁)
    (hV₂ : HasOrthonormalCols V₂) (h₁₂ : V₁ᴴ * V₂ = 0) {d : ℕ}
    (hd : Fintype.card r + d = Fintype.card k + 1) (hrk : Fintype.card r < Fintype.card k)
    (S : Matrix a s ℝ) {u t : ℝ} (hu : 0 ≤ u) (ht : 0 < t) :
    μ.real {ω | ¬ specNorm (S * (V₂ᴴ * X ω) * pinv (V₁ᴴ * X ω)) ≤
        t * (specNorm S * √((Fintype.card r : ℝ) / d) +
          frobNorm S * gaussianPinvSpecNormBound (Fintype.card r) (Fintype.card k)) +
        u * t * gaussianPinvSpecNormBound (Fintype.card r) (Fintype.card k) * specNorm S} ≤
      t ^ (-((Fintype.card k : ℝ) - Fintype.card r)) +
        gaussianPinvFrobTail (Fintype.card r) d (t ^ 2) + Real.exp (-u ^ 2 / 2)
/-- The Frobenius block tail in the same shape (HMT, proof of Theorem 10.7). -/
theorem measureReal_not_frobNorm_mul_mul_pinv_le_le_of_hasLaw_gaussianMatrix [DecidableEq r]
    [DecidableEq s] {X : Ω → Matrix n k ℝ} (hX : HasLaw X (gaussianMatrix n k) μ)
    {V₁ : Matrix n r ℝ} {V₂ : Matrix n s ℝ} (hV₁ : HasOrthonormalCols V₁)
    (hV₂ : HasOrthonormalCols V₂) (h₁₂ : V₁ᴴ * V₂ = 0) {d : ℕ}
    (hd : Fintype.card r + d = Fintype.card k + 1) (hrk : Fintype.card r < Fintype.card k)
    (S : Matrix a s ℝ) {u t : ℝ} (hu : 0 ≤ u) (ht : 0 < t) :
    μ.real {ω | ¬ frobNorm (S * (V₂ᴴ * X ω) * pinv (V₁ᴴ * X ω)) ≤
        t * √((Fintype.card r : ℝ) / d) * frobNorm S +
        u * t * gaussianPinvSpecNormBound (Fintype.card r) (Fintype.card k) * specNorm S} ≤
      t ^ (-((Fintype.card k : ℝ) - Fintype.card r)) +
        gaussianPinvFrobTail (Fintype.card r) d (t ^ 2) + Real.exp (-u ^ 2 / 2)
```

Plus one change to a registered file: `hasLaw_inv_mul_conjTranspose_apply_self`
(`InverseMoments.lean`, private) becomes public as
`hasLaw_inv_mul_conjTranspose_apply_self_of_hasLaw_gaussianMatrix`, with its law written out,
`(gaussianVector (Fin d)).map fun z => (‖WithLp.toLp 2 z‖ ^ 2)⁻¹`, instead of the private abbrev
`invChiSq` (Q11). It is proved; nothing new goes into that file (1017 lines, over budget).

Proof routes. *Factors:* `field_simp`, `div_le_div_iff₀` (the prototype's `completion_factor_mono`);
the tail and constant comparisons by the bodies (`_def` of the `irreducible_def`s), and
$\frac{k+r-1}{2} \le k$ for $r < k$. *R8:* the published law and the χ² small ball at
$u = 1/s$: $\{s \le 1/\chi^2_d\} \subseteq \{\chi^2_d \le 1/s\}$ (at $\chi^2_d = 0$, Lean's
$0^{-1} = 0 < s$). *R9:* a.s. $\|\mathbf{G}^{+}\|_{\mathsf{F}}^2 = T := \sum_i D_i$ with
$D_i = (\mathbf{G}\mathbf{G}^{\mathsf{H}})^{-1}_{ii}$ (a.s. full row rank,
`frobNorm_pinv_sq_eq_re_trace_inv_of_injective_conjTranspose`). With $v = t\lvert r\rvert/d$ and
$a = v^d/\lvert r\rvert^{d-1}$: Markov at $\min(v^d, T^d)$; $T^d \le \lvert r\rvert^{d-1}\sum_i D_i^d$
(`pow_sum_div_card_le_sum_pow`); $\min(v^d, \sum_i x_i) \le \sum_i\min(v^d, x_i)$; the layer cake
$\mathbb{E}\min(a, D_i^d) = \int_0^a \mathbb{P}\{D_i^d > s\}\,ds \le \int_0^a (e/d)^{d/2}s^{-1/2}\,ds
= 2(e/d)^{d/2}\sqrt{a}$ by R8; together $\mathbb{P}\{T > v\} \le 2\lvert r\rvert^{(d+1)/2}
(e/d)^{d/2}v^{-d/2} = 2\sqrt{\lvert r\rvert}\,(e/t)^{d/2}$. This is TW's argument with
$\min(a, \cdot)$ in place of the parallel sum $a : \cdot$ (no parallel-sum API, no Gamma-function
integral, no Stirling bound), which costs the factor $2/\sqrt{\pi}$. A union bound over $i$ would
give $\lvert r\rvert\,(e/t)^{d/2}$ with one line less; the def hides the choice (Q3). $r$ empty:
$T = 0$ and the event is empty. *R10:* Markov (`measureReal_ge_le_integral_div` on the
$(\lvert k\rvert - \lvert r\rvert)$-th power) and `integral_specNorm_pinv_rpow_le_of_hasLaw_gaussianMatrix`.
*R11:* push $\mu$ to the joint law, which is the product of the laws
(`indepFun_iff_map_prod_eq_prod_map_map`); the event is measurable (`hf`, `hL`, `hc`); by
`Measure.prod_apply` its measure is $\int \mathbb{P}_{\mathbf{G}}\{f(y,\mathbf{G}) > c(y) + L(y)t\}
\,d\mu_Y(y)$, and for each $y$ the fixed-function tail
`measureReal_integral_add_le_of_hasLaw_gaussianMatrix` (with `hmean` and deviation $L(y)t$)
bounds the inner probability by $e^{-t^2/2}$; at $L(y) = 0$, $f(y,\cdot)$ is constant at its mean
$\le c(y)$ and the inner event is empty. *R12, R13:* R2's second moment and Jensen
($\mathbb{E}Z \le (\mathbb{E}Z^2)^{1/2}$, as R4's `integral_frobNorm_pinv_le_of_hasLaw_gaussianMatrix`).
*R14:* $\mathbf{G}_i = \mathbf{V}_i^{\mathsf{H}}\mathbf{X}$ independent, $\mathbf{G}_2$ Gaussian
(R1); with $\mathbf{T} = \mathbf{G}_1^{+}$ the event lies in $\{\|\mathbf{T}\|_{\mathsf{F}}^2 >
t\lvert r\rvert/d\} \cup \{\|\mathbf{S}\mathbf{G}_2\mathbf{T}\|_{\mathsf{F}} > \sqrt{u}\,
\|\mathbf{S}\|_{\mathsf{F}}\|\mathbf{T}\|_{\mathsf{F}}\}$ (for $u \ge 1$; for $u < 1$ the bound
exceeds one); R9 for the first; R11 for the second with $Y = \mathbf{T}$, $f(\mathbf{T},\mathbf{G}) =
\|\mathbf{S}\mathbf{G}\mathbf{T}\|_{\mathsf{F}}$, $L = c = \|\mathbf{S}\|_{\mathsf{F}}
\|\mathbf{T}\|_{\mathsf{F}}$ (R13 at fixed $\mathbf{T}$; the Lipschitz bound by
$\|\mathbf{S}\mathbf{M}\mathbf{T}\|_{\mathsf{F}} \le \|\mathbf{S}\|_{\mathsf{F}}\|\mathbf{M}
\|_{\mathsf{F}}\|\mathbf{T}\|_{\mathsf{F}}$), $t = \sqrt{u} - 1$, and $e^{-(\sqrt{u}-1)^2/2} \le
e^{-(u-2)/4}$ ($(\sqrt{u} - 2)^2 \ge 0$); `measureReal_union_le`. $\mathbf{S} = \mathbf{0}$: empty
event. *R15, R16:* the same split with the event $\{\|\mathbf{T}\|_2 \le tC,\ \|\mathbf{T}
\|_{\mathsf{F}}^2 \le t^2\lvert r\rvert/d\}$ (R10, R9 at $t^2$) and R11 with $f$ the spectral
(Frobenius) norm, $L = \|\mathbf{S}\|_2\|\mathbf{T}\|_2$, $c = \|\mathbf{S}\|_2\|\mathbf{T}
\|_{\mathsf{F}} + \|\mathbf{S}\|_{\mathsf{F}}\|\mathbf{T}\|_2$ (Chevet at fixed factors) or
$c = \|\mathbf{S}\|_{\mathsf{F}}\|\mathbf{T}\|_{\mathsf{F}}$ (R13), deviation $u$. Degenerate:
$t < 1$ makes $t^{-(\lvert k\rvert - \lvert r\rvert)} > 1$; $r$ empty: $\mathbf{G}_1^{+} =
\mathbf{0}$, empty events.

### 3.3 RandomMatrix Haar additions (home `Haar/Transfer.lean`; 3)

Labels, in order: H1 to H3.

```lean
/-- **The polar factor of a full-rank rotation-invariant random matrix is Haar**: if the law of
$\mathbf{X}$ is invariant under $\mathbf{X} \mapsto \mathbf{U}\mathbf{X}$ for orthogonal
$\mathbf{U}$ and $\mathbf{X}$ has full column rank almost surely, its polar factor has the law
`haarFrame n l`. [EpperlyWebber2026, §6] (the reduction to random orthonormal matrices; locator to
confirm). -/
theorem hasLaw_polarFactor_of_isLeftUnitarilyInvariant [DecidableEq n] [DecidableEq l]
    {ν : Measure (Matrix n l ℝ)} [IsProbabilityMeasure ν] [IsLeftUnitarilyInvariant ν]
    {X : Ω → Matrix n l ℝ} (hX : HasLaw X ν μ)
    (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) :
    HasLaw (fun ω => polarFactor (X ω)) (haarFrame n l) μ
/-- **Every full-rank rotation-invariant test matrix has the Gaussian law of the range**:
$\mathbf{P}_{\mathbf{A}\mathbf{X}}$ has the law of $\mathbf{P}_{\mathbf{A}\mathbf{G}}$ for a
standard Gaussian $\mathbf{G}$. Result: gaussian-haar-range-transfer -/
theorem hasLaw_rangeProjector_mul_of_isLeftUnitarilyInvariant [DecidableEq n]
    {ν : Measure (Matrix n l ℝ)} [IsProbabilityMeasure ν] [IsLeftUnitarilyInvariant ν]
    {X : Ω → Matrix n l ℝ} (A : Matrix m n ℝ) (hX : HasLaw X ν μ)
    (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) :
    HasLaw (fun ω => rangeProjector (A * X ω))
      ((gaussianMatrix n l).map fun G => rangeProjector (A * G)) μ
theorem ae_rank_mul_eq_min_of_isLeftUnitarilyInvariant [DecidableEq n]
    {ν : Measure (Matrix n l ℝ)} [IsProbabilityMeasure ν] [IsLeftUnitarilyInvariant ν]
    {X : Ω → Matrix n l ℝ} (A : Matrix m n ℝ) (hX : HasLaw X ν μ)
    (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) :
    ∀ᵐ ω ∂μ, (A * X ω).rank = min A.rank (Fintype.card l)
```

Proof routes. *H1:* the law of `polarFactor ∘ X` is `ν.map polarFactor` (`measurable_polarFactor`);
it is left-invariant because `polarFactor (U * M) = U * polarFactor M` for orthogonal $\mathbf{U}$
(`polarFactor_mul_left`, `isLeftUnitarilyInvariant_iff`) and $\nu$ is; orthonormal columns a.s. by
`hasOrthonormalCols_polarFactor_iff` and `hXr`; then `hasLaw_haarFrame_of_isLeftUnitarilyInvariant`.
*H2:* `rangeProjector_mul_polarFactor` rewrites pointwise, then H1 and
`hasLaw_rangeProjector_mul_of_hasLaw_haarFrame`. *H3:* `rank_rangeProjector` turns the rank of
$\mathbf{A}\mathbf{X}$ into a function of $\mathbf{P}_{\mathbf{A}\mathbf{X}}$; H2 and
`ae_rank_mul_eq_min_of_hasLaw_gaussianMatrix`. Degenerate: $l$ empty: both laws are the Dirac
mass at the empty matrix. A Haar user supplies `isLeftUnitarilyInvariant_haarFrame` and
`(ae_hasOrthonormalCols_of_hasLaw_haarFrame hX hl).mono fun _ h => h.mulVec_injective`; a
Gaussian user `isLeftUnitarilyInvariant_gaussianMatrix` and R1's a.s. rank (for $\ell \le n$).

### 3.4 Matrix layer (homes `Norms/Nuclear.lean`, `Norms/Schatten.lean`, `Norms/GaugeExamples.lean`; 3)

Labels, in order: M1 to M3.

```lean
/-- $\|\mathbf{B}^{\mathsf{H}}\mathbf{B}\|_* = \|\mathbf{B}\|_{\mathsf{F}}^2$. -/
theorem nuclearNorm_conjTranspose_mul_self (B : Matrix m n 𝕜) :
    nuclearNorm (Bᴴ * B) = frobNorm B ^ 2
/-- $\|\mathbf{B}^{\mathsf{H}}\mathbf{B}\|_{S_q} = \|\mathbf{B}\|_{S_{2q}}^2$ for $q \ne 0$: the
Gram form at the $\ell^q$ gauge is the squared Schatten $2q$-norm. -/
theorem schattenNorm_conjTranspose_mul_self {q : ℝ≥0∞} (hq : q ≠ 0) (B : Matrix m n 𝕜) :
    schattenNorm q (Bᴴ * B) = schattenNorm (2 * q) B ^ 2
/-- The $\ell^q$ gauge takes the value $1$ at a unit coordinate sequence. -/
theorem lpGauge_apply_single_zero {q : ℝ≥0∞} (hq : 1 ≤ q) :
    lpGauge q hq (Finsupp.single 0 1) = 1
```

Routes: `Matrix.PosSemidef.nuclearNorm_eq_re_trace` and `frobNorm_sq_eq_re_trace` (the step inside
S0's `nuclearNorm_conjTranspose_mul_self_sub_nystrom`); `singularValues_conjTranspose_mul_self`
with `schattenNorm_eq_sum_rpow` ($q$ finite) or `schattenNorm_top`; `lpGauge_apply_of_ne_top`,
`lpGauge_top_apply`. $q = 0$ is excluded because `schattenNorm 0` is the rank. Written proved
(registered files) or in a side file `Matrix/Norms/GramNorms.lean` merged at wrap-up (S2a §8 item
18).

### 3.5 `LowRank/Gaussian/RangeFinder.lean`: Gaussian expectations (8)

Labels, in order: G1 to G5, U1, U2, E1.

```lean
/-- **The expected error of the randomized SVD, Gram form**: for a standard Gaussian
$n \times \ell$ test matrix, $k + 2 \le \ell$ and every unitarily invariant norm,
$$\mathbb{E}\bigl\|(\mathbf{A} - \mathbf{P}_{\mathbf{A}\mathbf{X}}\mathbf{A})^{\mathsf{H}}
(\mathbf{A} - \mathbf{P}_{\mathbf{A}\mathbf{X}}\mathbf{A})\bigr\|_{\Phi} \le
\|\mathbf{E}^{\mathsf{H}}\mathbf{E}\|_{\Phi} + \Phi(\mathbf{e}_0)\,\frac{k}{\ell - k - 1}\,
\|\mathbf{E}\|_{\mathsf{F}}^2\,,\qquad \mathbf{E} = \mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\,.$$
Every quadratic unitarily invariant norm: squared Schatten $p$ for $p \ge 2$, squared Frobenius at the
nuclear gauge, squared spectral. [TroppWebber2023, Theorem 8.1 (RSVD2)];
[HalkoMartinssonTropp2011, Theorem 10.5 (proof)]; [MartinssonTropp2020, Theorem 11.4 and remark].
Result: randomized-svd-expected-error -/
theorem SymmetricGauge.integral_matrixNorm_conjTranspose_mul_self_sub_rsvd_le_of_hasLaw_gaussianMatrix
    (Φ : SymmetricGauge) (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ}
    (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, Φ.matrixNorm ((A - rsvd A (X ω))ᴴ * (A - rsvd A (X ω))) ∂μ ≤
      Φ.matrixNorm ((A - truncatedSVD A k)ᴴ * (A - truncatedSVD A k)) +
        Φ (Finsupp.single 0 1) * ((k : ℝ) / ((Fintype.card l : ℝ) - k - 1)) *
          frobNorm (A - truncatedSVD A k) ^ 2
/-- **The expected error of the randomized SVD, Frobenius norm** (HMT Theorem 10.5):
$\mathbb{E}\|\mathbf{A} - \mathbf{P}_{\mathbf{A}\mathbf{X}}\mathbf{A}\|_{\mathsf{F}}^2 \le
\bigl(1 + \frac{k}{\ell - k - 1}\bigr)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$.
There for $\mathbb{E}\|\cdot\|_{\mathsf{F}}$, which follows by Jensen, with $k \ge 2$ and
$k + p \le \min\{m, n\}$, both unneeded. Result: randomized-svd-expected-error -/
theorem integral_frobNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ} (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, frobNorm (A - rsvd A (X ω)) ^ 2 ∂μ ≤
      gaussianProjectionFactor k (Fintype.card l) * frobNorm (A - truncatedSVD A k) ^ 2
/-- **..., Schatten norms** (TW (RSVD2) for $2 \le p \le \infty$). -/
theorem integral_schattenNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ} (hk : k + 2 ≤ Fintype.card l) {p : ℝ≥0∞}
    (hp : 2 ≤ p) :
    ∫ ω, schattenNorm p (A - rsvd A (X ω)) ^ 2 ∂μ ≤
      schattenNorm p (A - truncatedSVD A k) ^ 2 +
        (k : ℝ) / ((Fintype.card l : ℝ) - k - 1) * frobNorm (A - truncatedSVD A k) ^ 2
/-- **..., squared spectral norm**: $\mathbb{E}\|\mathbf{A} - \mathbf{P}_{\mathbf{A}\mathbf{X}}
\mathbf{A}\|_2^2 \le \sigma_k(\mathbf{A})^2 + \frac{k}{\ell - k - 1}\|\mathbf{E}\|_{\mathsf{F}}^2$.
Incomparable with `integral_specNorm_sub_rsvd_le_of_hasLaw_gaussianMatrix` (rule 4; brief D10):
this one is better for small $k$ and is the one with a Nyström twin. -/
theorem integral_specNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ} (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, specNorm (A - rsvd A (X ω)) ^ 2 ∂μ ≤
      singularValues A k ^ 2 +
        (k : ℝ) / ((Fintype.card l : ℝ) - k - 1) * frobNorm (A - truncatedSVD A k) ^ 2
/-- **The average spectral error of the randomized SVD** (HMT Theorem 10.6, MT Theorem 11.5):
$$\mathbb{E}\|\mathbf{A} - \mathbf{P}_{\mathbf{A}\mathbf{X}}\mathbf{A}\|_2 \le
\Bigl(1 + \sqrt{\tfrac{k}{\ell - k - 1}}\Bigr)\sigma_k(\mathbf{A}) +
C\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}\,,$$
$C$ = `gaussianPinvSpecNormBound k ℓ` $= \frac{e}{\ell - k}\sqrt{(\ell + k - 1)/2}$, at most HMT's
$e\sqrt{\ell}/(\ell - k)$. Result: randomized-svd-average-spectral-error -/
theorem integral_specNorm_sub_rsvd_le_of_hasLaw_gaussianMatrix (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ} (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, specNorm (A - rsvd A (X ω)) ∂μ ≤
      (1 + √((k : ℝ) / ((Fintype.card l : ℝ) - k - 1))) * singularValues A k +
        gaussianPinvSpecNormBound k (Fintype.card l) * frobNorm (A - truncatedSVD A k)
/-- **The expected error of the truncated randomized SVD, Frobenius norm**: the late truncation
keeps HMT's constant,
$\mathbb{E}\|\mathbf{A} - \llbracket\mathbf{P}_{\mathbf{A}\mathbf{X}}\mathbf{A}\rrbracket_k
\|_{\mathsf{F}}^2 \le \bigl(1 + \frac{k}{\ell - k - 1}\bigr)\|\mathbf{A} -
\llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$, for every choice of the truncation.
[HalkoMartinssonTropp2011, Theorem 10.5]; [Woodruff2014, Lemma 48].
Result: randomized-svd-expected-error -/
theorem integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_hasLaw_gaussianMatrix (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ} (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 ∂μ ≤
      gaussianProjectionFactor k (Fintype.card l) * frobNorm (A - truncatedSVD A k) ^ 2
/-- **The expected spectral error of the truncated randomized SVD**, for a measurable choice
$\mathbf{Y}$ of best rank-$k$ approximations of $\mathbf{P}_{\mathbf{A}\mathbf{X}}\mathbf{A}$:
$\mathbb{E}\|\mathbf{A} - \mathbf{Y}\|_2^2 \le \sigma_k(\mathbf{A})^2 + \frac{k}{\ell - k - 1}
\|\mathbf{E}\|_{\mathsf{F}}^2$, the bound of the untruncated output. The library has no measurable
selector yet, so this statement cannot be applied now; the expectation of the spectral error of
`truncatedSVD (rsvd A (X ω)) k` itself is not stated (its measurability is unknown, and the integral
of a non-integrable function is $0$). -/
theorem integral_specNorm_sub_sq_le_of_isBestRankApprox_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ}
    (hk : k + 2 ≤ Fintype.card l) {Y : Ω → Matrix m n ℝ}
    (hY : ∀ ω, IsBestRankApprox (rsvd A (X ω)) k (Y ω)) (hYm : AEStronglyMeasurable Y μ) :
    ∫ ω, specNorm (A - Y ω) ^ 2 ∂μ ≤
      singularValues A k ^ 2 +
        (k : ℝ) / ((Fintype.card l : ℝ) - k - 1) * frobNorm (A - truncatedSVD A k) ^ 2
/-- **A Gaussian sketch at least as wide as the rank recovers the matrix**: if
$\operatorname{rank}\mathbf{A} \le \ell$, then $\mathbf{P}_{\mathbf{A}\mathbf{X}}\mathbf{A} =
\mathbf{A}$ almost surely. -/
theorem ae_rsvd_eq_self_of_hasLaw_gaussianMatrix (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) (hA : A.rank ≤ Fintype.card l) :
    ∀ᵐ ω ∂μ, rsvd A (X ω) = A
```

Proof routes. **The common step** (G1, U1, G5, and the tails): if `k ≤ card n`, L2 gives
$\mathbf{Z}$ : `Matrix n (Fin k) ℝ` with `HasOrthonormalCols Z` and `A * Z * Zᴴ = truncatedSVD A k`;
`HasOrthonormalCols.exists_fromCols` completes it by $\mathbf{V}_2$ (columns `Fin (card n - k)`,
proof-internal) with $\mathbf{Z}\mathbf{Z}^{\mathsf{H}} + \mathbf{V}_2\mathbf{V}_2^{\mathsf{H}} =
\mathbf{I}$ and $\mathbf{Z}^{\mathsf{H}}\mathbf{V}_2 = \mathbf{0}$; so $\mathbf{E} =
\mathbf{A}(\mathbf{I} - \mathbf{Z}\mathbf{Z}^{\mathsf{H}}) = (\mathbf{E}\mathbf{V}_2)
\mathbf{V}_2^{\mathsf{H}}$ and S1's $\mathbf{M} = \mathbf{E}\mathbf{X}(\mathbf{Z}^{\mathsf{H}}
\mathbf{X})^{+} = \mathbf{S}(\mathbf{V}_2^{\mathsf{H}}\mathbf{X})(\mathbf{Z}^{\mathsf{H}}
\mathbf{X})^{+}$ with $\mathbf{S} = \mathbf{E}\mathbf{V}_2$, $\|\mathbf{S}\|_{\mathsf{F}} =
\mathrm{OPT}$, $\|\mathbf{S}\|_2 = \sigma_k(\mathbf{A})$ (`specNorm_sub_truncatedSVD`). The rank
hypothesis `(Xᴴ * Z).rank = Z.rank` of S1 holds a.s. (`ae_rank_mul_eq_min_of_hasLaw_gaussianMatrix Zᴴ`,
`Matrix.rank_conjTranspose`, $k \le \ell$). That is the "completion" step of the manuscript's
Lemma `lem:completion`, applied to $\mathbf{Z}$; S1 §3.2's usage note is its plan. If
`card n < k`, E1 and `truncatedSVD_of_rank_le` make both sides $0$ a.e. (§3.0).
*G1:* a.e. S1's `Φ.matrixNorm_conjTranspose_mul_self_sub_rsvd_le` rewritten by `hZA`;
$\|\mathbf{M}^{\mathsf{H}}\mathbf{M}\|_\Phi \le \Phi(\mathbf{e}_0)\|\mathbf{M}^{\mathsf{H}}\mathbf{M}\|_*
= \Phi(\mathbf{e}_0)\|\mathbf{M}\|_{\mathsf{F}}^2$ (`matrixNorm_le_apply_single_mul_nuclearNorm`,
M1); `integral_mono_ae` with L1 and R4's `integrable_` block twin; R4's block moment gives
$\|\mathbf{S}\|_{\mathsf{F}}^2\,k/(\ell - k - 1)$. *G2:* G1 at `lpGauge 1`
(`lpGauge_one_matrixNorm`, M1, M3), `gaussianProjectionFactor_def`, `ring`. *G3:* G1 at
`lpGauge (p / 2)` ($1 \le p/2$), `lpGauge_matrixNorm`, M2 with $2 \cdot (p/2) = p$, M3. *G4:* G1 at
`lpGauge ⊤`, `specNorm_conjTranspose_mul_self`, `specNorm_sub_truncatedSVD`. *G5:* a.e. S1's
`HasOrthonormalCols.specNorm_sub_rsvd_le`, `hZA`, `specNorm_sub_truncatedSVD`; R4's
`integral_specNorm_mul_mul_pinv_le_of_hasLaw_gaussianMatrix` at $\mathbf{S}$; L6 and R4's
integrable twin; `gaussianPinvSpecNormBound_def` (until Q8's R4 restatement). *U1:* a.e., with
$\mathbf{Q}$ an orthonormal basis of $\operatorname{range}(\mathbf{A}\mathbf{X}(\omega))$
(`exists_hasOrthonormalCols_range_eq`, pointwise, no measurability needed), S2a's T5 turns the
named output into $\mathbf{Q}\llbracket\mathbf{Q}^{\mathsf{H}}\mathbf{A}\rrbracket_k$, and S1's
truncation for free (`HasOrthonormalCols.frobNorm_sub_mul_truncatedSVD_sq_le`, `hk : card (Fin k) ≤ k`)
bounds it by $\mathrm{OPT}^2 + \|\mathbf{M}\|_{\mathsf{F}}^2$; then as G2, with L7. *U2:* L9 and U1
(`gaussianProjectionFactor_def`, `linarith`). *E1:* `ae_rank_mul_eq_min_of_hasLaw_gaussianMatrix A`
and `rsvd_eq_self_of_rank_eq`. Degenerate: §3.0; $\mathbf{A} = \mathbf{0}$: all sides $0$.

### 3.6 `LowRank/Gaussian/RangeFinder.lean`: rotation-invariant expectations (5)

Labels, in order: I1 to I5. Hypotheses `[DecidableEq n] {ν : Measure (Matrix n l ℝ)} [IsProbabilityMeasure ν]
[IsLeftUnitarilyInvariant ν] (hX : HasLaw X ν μ) (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec)`,
written `(hX) (hXr)` below as an abbreviation of that binder list (the skeleton writes it out).

```lean
/-- The Gram form of `…_of_hasLaw_gaussianMatrix` for every full-rank rotation-invariant test
matrix (Gaussian, Haar, ...). Result: randomized-svd-expected-error -/
theorem SymmetricGauge.integral_matrixNorm_conjTranspose_mul_self_sub_rsvd_le_of_isLeftUnitarilyInvariant
    (Φ : SymmetricGauge) (A : Matrix m n ℝ) (hX) (hXr) {k : ℕ} (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, Φ.matrixNorm ((A - rsvd A (X ω))ᴴ * (A - rsvd A (X ω))) ∂μ ≤
      Φ.matrixNorm ((A - truncatedSVD A k)ᴴ * (A - truncatedSVD A k)) +
        Φ (Finsupp.single 0 1) * ((k : ℝ) / ((Fintype.card l : ℝ) - k - 1)) *
          frobNorm (A - truncatedSVD A k) ^ 2
/-- **HMT's bound for rotation-invariant test matrices** (EW Theorem 3.1, real case, one $q$).
Result: randomized-svd-expected-error -/
theorem integral_frobNorm_sub_rsvd_sq_le_of_isLeftUnitarilyInvariant (A : Matrix m n ℝ) (hX) (hXr)
    {k : ℕ} (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, frobNorm (A - rsvd A (X ω)) ^ 2 ∂μ ≤
      gaussianProjectionFactor k (Fintype.card l) * frobNorm (A - truncatedSVD A k) ^ 2
/-- Result: randomized-svd-average-spectral-error -/
theorem integral_specNorm_sub_rsvd_le_of_isLeftUnitarilyInvariant (A : Matrix m n ℝ) (hX) (hXr)
    {k : ℕ} (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, specNorm (A - rsvd A (X ω)) ∂μ ≤
      (1 + √((k : ℝ) / ((Fintype.card l : ℝ) - k - 1))) * singularValues A k +
        gaussianPinvSpecNormBound k (Fintype.card l) * frobNorm (A - truncatedSVD A k)
/-- Result: randomized-svd-expected-error -/
theorem integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_isLeftUnitarilyInvariant
    (A : Matrix m n ℝ) (hX) (hXr) {k : ℕ} (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 ∂μ ≤
      gaussianProjectionFactor k (Fintype.card l) * frobNorm (A - truncatedSVD A k) ^ 2
theorem ae_rsvd_eq_self_of_isLeftUnitarilyInvariant (A : Matrix m n ℝ) (hX) (hXr)
    (hA : A.rank ≤ Fintype.card l) : ∀ᵐ ω ∂μ, rsvd A (X ω) = A
```

Proof routes. Each integrand is $g(\mathbf{P}_{\mathbf{A}\mathbf{X}(\omega)})$ for a continuous
$g$ on `Matrix m m ℝ`: by `sub_rsvd`, $g(\mathbf{P}) = \Phi(((\mathbf{I}-\mathbf{P})\mathbf{A})^{\mathsf{H}}
(\mathbf{I}-\mathbf{P})\mathbf{A})$, $\|(\mathbf{I}-\mathbf{P})\mathbf{A}\|_{\mathsf{F}}^2$,
$\|(\mathbf{I}-\mathbf{P})\mathbf{A}\|_2$; for I4 the choice-free form of §3.0 item 1,
$g(\mathbf{P}) = \|(\mathbf{I}-\mathbf{P})\mathbf{A}\|_{\mathsf{F}}^2 + \sum_{i \in [k, \min(m,n))}
\sigma_i(\mathbf{P}\mathbf{A})^2$ (`continuous_singularValues`), which equals the integrand where
$\mathbf{P}$ is an orthogonal projector and is used instead of the choice-dependent
$\mathbf{P} \mapsto \|\mathbf{A} - \llbracket\mathbf{P}\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$, whose
measurability on all of `Matrix m m ℝ` is unknown. H2 and `HasLaw.integral_comp` move the integral to
`gaussianMatrix n l`, where G1, G2, G5, U1 apply to the identity map (`HasLaw.id`). I5: H3 and
`rsvd_eq_self_of_rank_eq`. Degenerate: §3.0 ($\ell > n$ makes `hXr` unsatisfiable).

### 3.7 `LowRank/Gaussian/RangeFinderTail.lean`: tails (10)

Labels, in order: P1 to P10. TW's letters: `hd : k + d = card l + 1` ($d = \ell - k + 1$), `u : ℝ`,
`0 < t`.

```lean
/-- **The tail of the randomized SVD, Gram form** (TW Theorem 8.1 (RSVD1)): for a standard
Gaussian test matrix, $k \le \ell$, every unitarily invariant norm, any $u$ and $t > 0$,
$$\bigl\|(\mathbf{A} - \mathbf{P}_{\mathbf{A}\mathbf{X}}\mathbf{A})^{\mathsf{H}}
(\mathbf{A} - \mathbf{P}_{\mathbf{A}\mathbf{X}}\mathbf{A})\bigr\|_{\Phi} \le
\|\mathbf{E}^{\mathsf{H}}\mathbf{E}\|_{\Phi} + \Phi(\mathbf{e}_0)\,\frac{utk}{\ell - k + 1}\,
\|\mathbf{E}\|_{\mathsf{F}}^2$$
outside probability $e^{-(u-2)/4} + $ `gaussianPinvFrobTail k (ℓ - k + 1) t`. TW have
$\sqrt{\pi k}\,(t/e)^{-(\ell-k+1)/2}$ for the second term and Schatten $p \ge 2$ only.
Result: randomized-svd-tail -/
theorem SymmetricGauge.measureReal_not_matrixNorm_conjTranspose_mul_self_sub_rsvd_le_le_of_hasLaw_gaussianMatrix
    (Φ : SymmetricGauge) (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {k d : ℕ}
    (hd : k + d = Fintype.card l + 1) (u : ℝ) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | ¬ Φ.matrixNorm ((A - rsvd A (X ω))ᴴ * (A - rsvd A (X ω))) ≤
        Φ.matrixNorm ((A - truncatedSVD A k)ᴴ * (A - truncatedSVD A k)) +
          Φ (Finsupp.single 0 1) * (u * t * k / d) * frobNorm (A - truncatedSVD A k) ^ 2} ≤
      Real.exp (-(u - 2) / 4) + gaussianPinvFrobTail k d t
/-- ..., Schatten norms, $2 \le p \le \infty$ (TW (RSVD1) as printed, up to the failure constant). -/
theorem measureReal_not_schattenNorm_sub_rsvd_sq_le_le_of_hasLaw_gaussianMatrix (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) {k d : ℕ} (hd : k + d = Fintype.card l + 1)
    {p : ℝ≥0∞} (hp : 2 ≤ p) (u : ℝ) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | ¬ schattenNorm p (A - rsvd A (X ω)) ^ 2 ≤
        schattenNorm p (A - truncatedSVD A k) ^ 2 +
          u * t * k / d * frobNorm (A - truncatedSVD A k) ^ 2} ≤
      Real.exp (-(u - 2) / 4) + gaussianPinvFrobTail k d t
theorem measureReal_not_frobNorm_sub_rsvd_sq_le_le_of_hasLaw_gaussianMatrix (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) {k d : ℕ} (hd : k + d = Fintype.card l + 1) (u : ℝ)
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | ¬ frobNorm (A - rsvd A (X ω)) ^ 2 ≤
        (1 + u * t * k / d) * frobNorm (A - truncatedSVD A k) ^ 2} ≤
      Real.exp (-(u - 2) / 4) + gaussianPinvFrobTail k d t
theorem measureReal_not_specNorm_sub_rsvd_sq_le_le_of_hasLaw_gaussianMatrix (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) {k d : ℕ} (hd : k + d = Fintype.card l + 1) (u : ℝ)
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | ¬ specNorm (A - rsvd A (X ω)) ^ 2 ≤
        singularValues A k ^ 2 + u * t * k / d * frobNorm (A - truncatedSVD A k) ^ 2} ≤
      Real.exp (-(u - 2) / 4) + gaussianPinvFrobTail k d t
/-- **The tail of the truncated randomized SVD, Frobenius norm**: the bound of
`measureReal_not_frobNorm_sub_rsvd_sq_le_le_of_hasLaw_gaussianMatrix` holds for
$\llbracket\mathbf{P}_{\mathbf{A}\mathbf{X}}\mathbf{A}\rrbracket_k$, every choice. -/
theorem measureReal_not_frobNorm_sub_truncatedSVD_rsvd_sq_le_le_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {k d : ℕ}
    (hd : k + d = Fintype.card l + 1) (u : ℝ) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | ¬ frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 ≤
        (1 + u * t * k / d) * frobNorm (A - truncatedSVD A k) ^ 2} ≤
      Real.exp (-(u - 2) / 4) + gaussianPinvFrobTail k d t
/-- **The tail of the truncated randomized SVD, spectral norm**, for any best rank-$k$
approximations $\mathbf{Y}(\omega)$ of $\mathbf{P}_{\mathbf{A}\mathbf{X}}\mathbf{A}$ (no
measurability): $\|\mathbf{A} - \mathbf{Y}\|_2^2 \le \sigma_k(\mathbf{A})^2 + \frac{utk}{d}
\|\mathbf{E}\|_{\mathsf{F}}^2$ outside the stated probability. The event may be non-measurable;
`μ.real` is then the outer measure, so the statement says that it lies inside a measurable event of
that probability. -/
theorem measureReal_not_specNorm_sub_sq_le_le_of_isBestRankApprox_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {k d : ℕ}
    (hd : k + d = Fintype.card l + 1) {Y : Ω → Matrix m n ℝ}
    (hY : ∀ ω, IsBestRankApprox (rsvd A (X ω)) k (Y ω)) (u : ℝ) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | ¬ specNorm (A - Y ω) ^ 2 ≤
        singularValues A k ^ 2 + u * t * k / d * frobNorm (A - truncatedSVD A k) ^ 2} ≤
      Real.exp (-(u - 2) / 4) + gaussianPinvFrobTail k d t
/-- The same for `truncatedSVD (rsvd A (X ω)) k`, the maintainer's spelling of the output. -/
theorem measureReal_not_specNorm_sub_truncatedSVD_rsvd_sq_le_le_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {k d : ℕ}
    (hd : k + d = Fintype.card l + 1) (u : ℝ) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | ¬ specNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 ≤
        singularValues A k ^ 2 + u * t * k / d * frobNorm (A - truncatedSVD A k) ^ 2} ≤
      Real.exp (-(u - 2) / 4) + gaussianPinvFrobTail k d t
/-- **Deviation bound for the Frobenius error** (HMT Theorem 10.7, the library's constants): for
$k < \ell$, $u \ge 0$, $t > 0$, with $C$ = `gaussianPinvSpecNormBound k ℓ`,
$\|\mathbf{A} - \mathbf{P}_{\mathbf{A}\mathbf{X}}\mathbf{A}\|_{\mathsf{F}} \le
(1 + t\sqrt{k/d})\,\|\mathbf{E}\|_{\mathsf{F}} + utC\,\sigma_k(\mathbf{A})$ outside probability
$t^{-(\ell-k)} + $ `gaussianPinvFrobTail k d (t ^ 2)` $+ e^{-u^2/2}$. HMT: $\sqrt{12k/p}$,
$e\sqrt{k+p}/(p+1)$, $5t^{-p} + 2e^{-u^2/2}$, $p \ge 4$, $u, t \ge 1$. Incomparable with TW (RSVD1)
(rule 4): better when $\sigma_k \ll \|\mathbf{E}\|_{\mathsf{F}}$ and small failure probabilities
are wanted. Result: randomized-svd-deviation-bound -/
theorem measureReal_not_frobNorm_sub_rsvd_le_le_of_hasLaw_gaussianMatrix (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) {k d : ℕ} (hd : k + d = Fintype.card l + 1)
    (hkl : k < Fintype.card l) {u t : ℝ} (hu : 0 ≤ u) (ht : 0 < t) :
    μ.real {ω | ¬ frobNorm (A - rsvd A (X ω)) ≤
        (1 + t * √((k : ℝ) / d)) * frobNorm (A - truncatedSVD A k) +
          u * t * gaussianPinvSpecNormBound k (Fintype.card l) * singularValues A k} ≤
      t ^ (-((Fintype.card l : ℝ) - k)) + gaussianPinvFrobTail k d (t ^ 2) + Real.exp (-u ^ 2 / 2)
/-- **Deviation bound for the spectral error** (HMT Theorem 10.8, the library's constants):
$\|\mathbf{A} - \mathbf{P}_{\mathbf{A}\mathbf{X}}\mathbf{A}\|_2 \le (1 + t\sqrt{k/d})\,\sigma_k(\mathbf{A})
+ tC\,\|\mathbf{E}\|_{\mathsf{F}} + utC\,\sigma_k(\mathbf{A})$, same failure probability.
Result: randomized-svd-deviation-bound -/
theorem measureReal_not_specNorm_sub_rsvd_le_le_of_hasLaw_gaussianMatrix (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) {k d : ℕ} (hd : k + d = Fintype.card l + 1)
    (hkl : k < Fintype.card l) {u t : ℝ} (hu : 0 ≤ u) (ht : 0 < t) :
    μ.real {ω | ¬ specNorm (A - rsvd A (X ω)) ≤
        (1 + t * √((k : ℝ) / d)) * singularValues A k +
          t * gaussianPinvSpecNormBound k (Fintype.card l) * frobNorm (A - truncatedSVD A k) +
          u * t * gaussianPinvSpecNormBound k (Fintype.card l) * singularValues A k} ≤
      t ^ (-((Fintype.card l : ℝ) - k)) + gaussianPinvFrobTail k d (t ^ 2) + Real.exp (-u ^ 2 / 2)
/-- The Gram-form tail for every full-rank rotation-invariant test matrix.
Result: randomized-svd-tail -/
theorem SymmetricGauge.measureReal_not_matrixNorm_conjTranspose_mul_self_sub_rsvd_le_le_of_isLeftUnitarilyInvariant
    (Φ : SymmetricGauge) (A : Matrix m n ℝ) (hX) (hXr) {k d : ℕ} (hd : k + d = Fintype.card l + 1)
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | ¬ Φ.matrixNorm ((A - rsvd A (X ω))ᴴ * (A - rsvd A (X ω))) ≤
        Φ.matrixNorm ((A - truncatedSVD A k)ᴴ * (A - truncatedSVD A k)) +
          Φ (Finsupp.single 0 1) * (u * t * k / d) * frobNorm (A - truncatedSVD A k) ^ 2} ≤
      Real.exp (-(u - 2) / 4) + gaussianPinvFrobTail k d t
```

Proof routes. *P1:* §3.5's common step (with `k ≤ card l` from `hd`); a.e. the Gram bound
$\Phi(\cdot) \le \Phi(\mathbf{E}^{\mathsf{H}}\mathbf{E}) + \Phi(\mathbf{e}_0)\|\mathbf{M}\|_{\mathsf{F}}^2$,
so, as $\Phi(\mathbf{e}_0) > 0$ (`apply_single_pos`), the failure event lies in R14's event at
$\mathbf{S} = \mathbf{E}\mathbf{V}_2$ union a null set (`measureReal_mono`); `card n < k`: exact
a.s., event null. *P2 to P4:* P1 at `lpGauge (p/2)`, `lpGauge 1`, `lpGauge ⊤` with M1 to M3 (P3 at
the nuclear gauge, rearranged). *P5:* U1's pointwise bound $\le \mathrm{OPT}^2 +
\|\mathbf{M}\|_{\mathsf{F}}^2$, then R14. *P6:* pointwise B15 at $\mathbf{Y}(\omega)$, the
choice-free Frobenius identity of L9's route and U1's pointwise bound give
$\|\mathbf{A} - \mathbf{Y}\|_2^2 \le \sigma_k^2 + \|\mathbf{M}\|_{\mathsf{F}}^2$; then R14 by
inclusion (no measurability of the event is used). *P7:* P6 at `isBestRankApprox_truncatedSVD`.
*P8:* a.e. $\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{\mathsf{F}} \le \mathrm{OPT} + \|\mathbf{M}
\|_{\mathsf{F}}$ (S1's `HasOrthonormalCols.frobNorm_sub_rsvd_sq_le`, $\sqrt{a^2+b^2} \le a + b$), then
R16. *P9:* S1's triangle form `HasOrthonormalCols.specNorm_sub_rsvd_le`, then R15. *P10:* the event is
$\{g(\mathbf{P}_{\mathbf{A}\mathbf{X}}) > c\}$ with $g$ continuous, a measurable set; H2 moves its
probability to the Gaussian, P1. Degenerate: §3.0 (rank $\le k$, $k = 0$, $t > 0$, $u$ free); P8,
P9 need $k < \ell$ for R10's moment order $\ell - k > 0$.

## 4. Files

| # | File | Statements | Lines (est.) | Imports (new) | Depends on |
|---|---|---|---|---|---|
| 1 | `Matrix/Norms/{Nuclear,Schatten,GaugeExamples}.lean` (registered; written proved, or side file `Matrix/Norms/GramNorms.lean`) | 3 (M1 to M3) | +40 | none | none |
| 2 | `RandomMatrix/Gaussian/InverseMoments.lean` (registered) | 1 made public (the diagonal law) | +10 | none | none |
| 3 | `RandomMatrix/Gaussian/{Concentration,Moments}.lean` (registered; written proved, or side files `Gaussian/ConcentrationIndep.lean`, `Gaussian/MomentsFrob.lean`) | 3 (R11 to R13) | +110 | `Probability/Law` (product law) | none |
| 4 | `RandomMatrix/Gaussian/BlockTail.lean` (new) | 16 (N1 to N10: 3 defs with 7 API lemmas; R8 to R10; R14 to R16) | 450 | files 2, 3, `Gaussian/BlockMoments`, `Distributions/ChiSquare` | files 2, 3 |
| 5 | `RandomMatrix/Haar/Transfer.lean` (registered; written proved, or side file `Haar/TransferInvariant.lean`) | 3 (H1 to H3) | +90 | `RandomMatrix/UnitaryInvariance`, `Factorizations/PolarFrames` | none |
| 6 | `LowRank/Gaussian/RangeFinder.lean` (new) | 22 (§3.1: 9; §3.5: 8; §3.6: 5) | 620 | files 1, 4, 5, `LowRank/Structural/{RangeFinder,Truncation}` | files 1 to 5 |
| 7 | `LowRank/Gaussian/RangeFinderTail.lean` (new) | 10 (P1 to P10) | 400 | file 6 | file 6 |

S3 is about 1720 lines and 58 public declarations (57 new, 3 of them definitions, plus the one
made public) against the brief's 800 lines. The growth: the RandomMatrix tails the brief took as
given (files 3, 4: about 560), the rotation-invariant parametrisation (files 5 and §3.6: about
220), the law-free companions and the selector reduction (§3.1: about 200), and HMT 10.7, 10.8
(R15, R16, P8, P9: about 160, dropped if Q6 is decided the other way). File 4 is one topic, the
tails of the range finder's Gaussian block. Order: files 1 to 5 are independent of each other
except file 4 on 2 and 3; file 6 in the order §3.1, §3.5, §3.6; file 7 as §3.7. S3 needs nothing
from S2b. The statements in registered files go there only proved (S2a §8 item 18); a skeleton
puts them in the named side files, merged at the wrap-up.

## 5. Material

**Prototype** (read-only, `~/Documents/prove2me/lean/NLAlib/LowRank/`; ledger dispositions):
- `RandomizedSVD/GaussianSketch.lean`: `ae_isUnit_block` → reached (R1's
  `ae_rank_mul_eq_min_of_hasLaw_gaussianMatrix`); `integrable_pinvR_block`, `integral_pinvR_block`
  → exist (R4); `rsvd_gaussian_inputs`, `rsvd_bound_nonneg` → cut (assembly helpers);
  `rsvd_main_gaussian` → G2; `rsvd_truncated_main_gaussian` → U1; `completion_gaussian_inputs`,
  `completion_reduction_gaussian_integrable`, `completion_reduction_gaussian`,
  `completion_gaussian_of_orthonormal`, `measurable_frobSq_sub_sketchedOutput` → S6.
- `RandomizedSVD/OptimalError.lean` (Gaussian half; the truncation half is S2a's):
  `integrable_frobSq_residual_of_measurable_frame` → L4 (law-free, no frame);
  `ae_gaussian_projection_reproduces_of_width_le` → E1 (rank in place of width);
  `integrable_and_integral_frobSq_residual_le_bestRankFrobSq_gaussian` → G2 with L4 (split, D4);
  `integrable_frobSq_truncatedRsvdOutput_of_measurable_frame` → L7;
  `integrable_and_integral_frobSq_truncatedRsvdOutput_le_bestRankFrobSq_gaussian` → U1 with L7;
  `integrable_and_integral_frobSq_residual_gaussianRangeFrame_le_bestRankFrobSq`,
  `integrable_and_integral_frobSq_truncatedRsvdOutput_gaussianRangeFrame_le_bestRankFrobSq` → cut
  (measurable range frames: D1's projector carrier makes them unnecessary).
- `RandomizedSVD/RSVD.lean`: `rsvd_assembly_ae`, `rsvd_truncated_main`, `rsvd_main` → cut
  (expectations as hypotheses; S3 states the Gaussian forms directly);
  `frobSq_sub_mul_transpose_mul_le_frobSq_sub_mul` → exists (S2a).
- `RandomizedSVD/Assembly.lean`: `completion_factor_mono` →
  `gaussianProjectionFactor_le_gaussianProjectionFactor`; `rsvd_assembly`, `rsvd_explicit` → cut
  (brief §4.4); `gn_assembly`, `gn_explicit` → S6.
- `RangeFinding/SpectralRangeFinder.lean`: `specNorm_residual_sq_le_of_range_subset`,
  `specNorm_residual_le_of_range_subset` → exist (S1);
  `integrable_and_integral_frobNorm_pinvR_gaussianMatrix_le`,
  `integrable_and_integral_specNorm_mul_block_mul_pinvR_block_le` → exist (R4);
  `integral_specNorm_residual_le_of_gaussian`, `integral_specNorm_residual_le_singularValues_of_gaussian`
  → G5 with L6 (no unmeasured frame `Q`, whose junk integral the prototype relied on);
  `exists_svd_right_blocks_specNorm` → cut (L2); `integral_specNorm_residual_gaussianRangeFrame_le`
  → cut. Not reproduced anywhere: `Fin`-indexed sizes, `projResidual`, `frobSq`, `bestRankFrobSq`,
  the `pinvR` blocks.

**The maintainer's manuscript** (`~/Documents/Papers/LRA-paper/main.tex`, read-only, never cited,
D13): Theorem `thm:RSVD` and Proposition `prop:hmt-struct` are G2 and U1 by the route of §3.5
(the third inequality of `prop:hmt-struct` is S1's truncation for free); Lemma `lem:completion`
(completing an orthonormal $\mathbf{Q}$ to an orthogonal matrix, then conditioning) is S6's; its
completion step is the one §3.5 applies to $\mathbf{Z}$. Nothing in it is new to S3.

**Literature** (§0's checks). Citations (all keys in `docs/references.bib`; no new key):

| statement | citation | relation to the printed statement |
|---|---|---|
| G1, I1 | [TroppWebber2023, Theorem 8.1 (RSVD2)]; [MartinssonTropp2020, Theorem 11.4 and remark]; [HalkoMartinssonTropp2011, Theorem 10.5 (proof)] | there Schatten $p \ge 2$; here every quadratic unitarily invariant norm, with $\Phi(\mathbf{e}_0)$ |
| G2, I2 | [HalkoMartinssonTropp2011, Theorem 10.5]; [TroppWebber2023, Theorem 8.7]; [EpperlyWebber2026, Theorem 3.1] (I2) | squared form (HMT state $\mathbb{E}\|\cdot\|_{\mathsf{F}}$), no $k \ge 2$, no $k + p \le \min\{m,n\}$; EW's minimum over $q$ not stated (rule 5) |
| G3, G4 | [TroppWebber2023, Theorem 8.1 (RSVD2)] | $p \in [2, \infty]$, $p = \infty$ |
| G5, I3 | [HalkoMartinssonTropp2011, Theorem 10.6]; [MartinssonTropp2020, Theorem 11.5] | R4's constant in place of $e\sqrt{k+p}/p$ |
| U1, I4 | [HalkoMartinssonTropp2011, Theorem 10.5]; [Woodruff2014, Lemma 48]; [CamanoEpperlyMeyerTropp2025, remark after Theorem 2.2] | the Frobenius truncation the CEMT remark obtains through the spectral HMT 9.3 |
| L9, U2 | [Gu2015, Theorem 3.4]; [TroppYurtseverUdellCevher2017a, Proposition A.8]; [TroppWebber2023, p. 42] | there a remark on truncated outputs; here explicit, under a selector |
| P1 to P4, P10 | [TroppWebber2023, Theorem 8.1 (RSVD1)] | Gram form, every gauge; `gaussianPinvFrobTail` in place of $\sqrt{\pi k}(t/e)^{-d/2}$ |
| P5 to P7 | [TroppWebber2023, Theorem 8.1 (RSVD1)] with [Woodruff2014, Lemma 48] (P5), [Gu2015, Theorem 3.4] (P6, P7) | composition |
| P8, P9 | [HalkoMartinssonTropp2011, Theorems 10.7, 10.8] | the library's constants (§3.7 docstrings) |
| R8, R9 | [TroppWebber2023, Lemma B.2 and proof] | min in place of the parallel sum; $2\sqrt{k}$ |
| R10 | [HalkoMartinssonTropp2011, Proposition 10.4] | Markov form at R4's moment, $t^{-(k-r)}$ |
| R11 | [HalkoMartinssonTropp2011, Proposition 10.3]; [TroppWebber2023, proof of Proposition 8.6] | with an independent random factor |
| R12, R13 | [HalkoMartinssonTropp2011, Proposition 10.1] | first moment by Jensen |
| R14 to R16 | [TroppWebber2023, Proposition 8.6 (8.9)]; [HalkoMartinssonTropp2011, proof of Theorem 10.8] | as stated |
| H1 to H3 | [EpperlyWebber2026, §6] (locator to confirm) | the polar-factor reduction |
| factors, M1 to M3, L1 to L8, E1, I5 | helpers, no citation | |

**Result ids** (D11; defined by `Result:` lines; checked against `explore/results.toml`,
`synonyms.toml` and the ids now in `NLAlib/`): `randomized-svd-expected-error` (G1 to G4, U1, I1,
I2, I4; one node titled from the shared bold head "The expected error of the randomized SVD"),
`randomized-svd-average-spectral-error` (G5, I3), `randomized-svd-tail` (P1 to P7, P10),
`randomized-svd-deviation-bound` (P8, P9), `inverse-wishart-trace-tail` (R9), all new; R11 joins
`gaussian-lipschitz-concentration` and H2 joins `gaussian-haar-range-transfer`. The atlas
candidate `rsvd-tail` (brief §1) is `randomized-svd-tail`.

## 6. Cut, and why

- *A bound-only expectation of `specNorm (A - truncatedSVD (rsvd A (X ω)) k)`* (or of any
  choice-dependent truncated error): weak in the precise sense of §3.0 item 2. Not stated.
- *Truncated expectations in other gauges* (Schatten $p \notin \{2, \infty\}$, nuclear): the error is
  choice-dependent and there is no reverse Eckart–Young for them; the selector forms of S2a's T1
  ($\mathbb{E}\|\mathbf{A} - \mathbf{Y}\|_\Phi \le \|\mathbf{E}\|_\Phi + \mathbb{E}\|\mathbf{A} -
  \mathbf{P}\mathbf{A}\|_\Phi$) are one line from it and have no consumer. Additive.
- *The truncated spectral first moment* $\mathbb{E}\|\mathbf{A} - \mathbf{Y}\|_2 \le \sigma_k +
  \mathbb{E}\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_2$ (HMT 9.3 plus G5): one line under a selector, no
  consumer. Additive.
- *HMT's form of G5* ($e\sqrt{\ell}/(\ell - k)$): dominated by G5 and new (rule 6: kept only when
  consumers cite the simpler form; none does). `gaussianPinvSpecNormBound_le` gives it in one step.
- *A gauge (unsquared) first moment* $\mathbb{E}\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_\Phi$: S1's
  triangle form needs $\mathbb{E}\|\mathbf{M}\|_\Phi$, which the RandomMatrix layer has only for
  $\Phi$ spectral and Frobenius. Recorded as a gap (nuclear-norm expectation of a Gaussian block).
- *TW Theorem 8.7* (Q7): the $\ell \in \{k, k+1\}$ bounds, the alternative spectral second moment
  $(1 + \frac{2k}{\ell-k-1})\sigma_k^2 + \frac{e^2}{\ell-k}\mathrm{OPT}^2$ (incomparable with G4, rule 4),
  and the Schatten-4 bounds; missing pieces in the header.
- *Corollary 10.9 and sample-size forms* (rule: tails, not sample sizes; corollaries only): no
  consumer; each is a parameter choice in P9 or P3. Additive.
- *Rotation-invariant twins of the remaining statements* (Schatten, spectral second moment,
  truncated spectral tails and selector forms, HMT 10.7, 10.8 forms): each is H2 plus the Gaussian
  statement in three lines; the headline ones are stated (§3.6, P10). Additive.
- *`haarFrame`-specific statements* (`…_of_hasLaw_haarFrame`): instances of §3.6 (Q5).
- *Per-law integrability companions*: the law-free L1 to L8 cover them (Q9).

## 7. Questions and decisions

Hard-to-reverse items are marked **(hard)**. Under the round's approval rule the maintainer decides
the hard ones; the rest proceed as recommended and are recorded here.

**Q1. The shape of the Gaussian statements (hard).** Options: (a) the Gram-form gauge theorem as the
primary expectation and tail, right side $\|\mathbf{E}^{\mathsf{H}}\mathbf{E}\|_\Phi +
\Phi(\mathbf{e}_0)\cdot\text{excess}\cdot\|\mathbf{E}\|_{\mathsf{F}}^2$, with Schatten, Frobenius and
spectral corollaries; (b) per-norm theorems only (HMT's and TW's printed forms). Recommendation (a):
it is D4 (confirmed by the maintainer); one proof gives every quadratic norm; S5 reads every
Nyström bound off it by one `rw` (`conjTranspose_mul_self_sub_nystrom`), which is the reason for the
form (brief §4.2). The factor $\Phi(\mathbf{e}_0)$ is what the proof reaches through the nuclear
norm and equals $1$ for every Schatten gauge (M3). Also fixed here: the random test matrix is `X` on
a sample space `Ω` (Q8), TW's $\ell - k + 1$ is `d` with `hd`, and tails are failure events
$\neg(\text{error} \le \text{bound})$ (Q10). Rework if reversed: the left and right sides of every S3
statement and of S5's, S6's and S7's copies.

**Q2. `gaussianProjectionFactor`: name, arity, home, and the inline excess (hard: a naming scheme
that S4 to S7 use).** Options for the excess $k/(\ell - k - 1)$ in G1, G3, G4, U2, I1: (a) inline, as
R4's `integral_frobNorm_pinv_sq_of_hasLaw_gaussianMatrix` writes the same expectation; (b)
`gaussianProjectionFactor k ℓ - 1`; (c) a second definition for the excess. Recommendation:
`gaussianProjectionFactor (k l : ℕ)`, a plain `def` with a `_def` simp lemma (D9), in
`RandomMatrix/Gaussian/BlockTail.lean` (S6's Sketching file must see it); the multiplicative forms
(G2, U1, I2, I4) use it; the excess is inline (a), because it is literally R4's expectation and a
subtraction of the factor reads worse than the source. Fixed with it, for S4 and S6:
`rotationInvariantFactor r l q` and `haarProjectionFactor d p q` (§1). Rework if reversed: the right
sides of the Frobenius statements of S3, S5, S6.

**Q3. TW's tail constant (not hard).** Options: (a) `gaussianPinvFrobTail` as an `irreducible_def`
with the proved body $2\sqrt{k}(e/t)^{d/2}$ (min trick and layer cake, §3.2 R9); (b) port TW's
parallel-sum computation with the Beta integral and Stirling's bound to reach $\sqrt{\pi k/d}$ (more
analysis, no other consumer); (c) the union bound, body $k(e/t)^{d/2}$. Recommendation (a), per
CONTRIBUTING §5.2 rule 2: consumers use only `_nonneg` and `_le`; reaching TW's constant later
changes the body and the comparison, no statement and no name.

**Q4. Measurability (decided in S2a §8 item 15; S3's own choices not hard).** S3 applies S2a's
decision: choice-free quantities on the named output with companions (L7, U1, I4, P5), choice-dependent
expectations under a measurable selector (L8, L9, U2), stated as not instantiable now and with no
bound-only twin. S3's own choices: (i) one law-free selector reduction (L9) instead of a selector
statement per law, so S4's and later sharpenings of U1 give spectral truncated bounds for free;
(ii) choice-dependent tails stated on the named output and in hypothesis form with no selector (P6,
P7), on the outer measure, which is honest and instantiable today. Recommendation: as stated. The
open item stays S2a's option (c) (a measurable `truncatedSVD`), which would make L8, L9 and U2
applicable to `truncatedSVD (rsvd A (X ω)) k` without restating them.

**Q5. Rotation-invariant laws through `IsLeftUnitarilyInvariant` (moderately hard: a §5.3 row S4
and S6 reuse).** Options: (a) hypotheses `HasLaw X ν μ`, `[IsLeftUnitarilyInvariant ν]`, a.s. full
column rank, with Haar and Gaussian as instances; (b) `HasLaw X (haarFrame n l) μ` statements
(`_of_hasLaw_haarFrame`), as R5's transfer is stated; (c) both. Recommendation (a): CONTRIBUTING
§5.4 ("parametrise over the interface"); it is EW's hypothesis literally; it costs one RandomMatrix
lemma (H1). Haar-specific corollaries, if a consumer wants them, are additive. Rework if reversed:
the hypotheses of §3.6 and P10 and of S4's statements.

**Q6. HMT 10.7 and 10.8 (not hard).** Options: (a) state them beside TW (RSVD1) with the library's
constants (R15, R16, P8, P9; about 160 lines); (b) defer to a consumer. Recommendation (a): the brief
lists them; they are incomparable with RSVD1 (rule 4) and the only tails whose deviation is scaled
by $\sigma_k$; they reuse R9 to R11. They are not corollaries of RSVD1, and HMT's Proposition 10.4
constants are not reached, so they cannot be stated in HMT's printed form now.

**Q7. TW Theorem 8.7 deferred (not hard).** Recommendation: defer. Its $\ell \in \{k, k+1\}$ cases
need parallel sums and S1's parallel-sum structural form (cut there for want of a consumer), and
$\mathbb{E}[a : \operatorname{tr}(\mathbf{G}\mathbf{G}^{\mathsf{H}})^{-1}]$ through the $1/\chi^2_1$,
$1/\chi^2_2$ densities; its spectral bound needs $\mathbb{E}\|\mathbf{S}\mathbf{G}\mathbf{T}\|_2^2$
(TW Lemma B.1), which S6 needs anyway: once S6 adds it, the spectral bound of 8.7 is an S3
addendum of about 40 lines; its Schatten-4 bounds need two fourth-moment identities the library
lacks. The brief §1's degenerate checklist ($\ell = k$, $k + 1$) is met by the tails P1 to P7, which
hold there.

**Q8. Identifier of the random test matrix, and naming R4's spectral constant (not hard).** (i) `X`
for the random test matrix on the library's sample space `Ω` (R4, R5 use `X`; `Ω` cannot be both);
docstrings keep $\mathbf{\Omega}$ where the sources do, or write $\mathbf{X}$ with "the test matrix".
(ii) `gaussianPinvSpecNormBound r k` (rule 2: R4's probe constant is not HMT's), with R4's three
statements that inline it (`integral_specNorm_pinv_rpow_le_of_hasLaw_gaussianMatrix`,
`integral_specNorm_pinv_le_of_hasLaw_gaussianMatrix`,
`integral_specNorm_mul_mul_pinv_le_of_hasLaw_gaussianMatrix`) restated with the name at S3's
wrap-up (one `rw [gaussianPinvSpecNormBound_def]` each; no consumer outside LowRank). Alternative:
keep R4's inline expression, written seven more times in S3. Recommendation: the name.

**Q9. Law-free integrability companions over `𝕜` (not hard).** D4's "each expectation with its
`integrable_…` companion" is met once per integrand (L1 to L8), not once per law: the integrands are
bounded and measurable for every measurable test matrix, and S7's OSI laws over `𝕜` reuse them.
Rework if reversed: per-law one-line twins.

**Q10. Tail spelling and names (not hard).** Failure events $\neg(\text{error} \le \text{bound})$
(CONTRIBUTING §5.3 "tail" row), forced by the $\operatorname{rank}\mathbf{A} \le k$ case (§3.0);
names `measureReal_not_<event>_le_of_…`, as R3's `measureReal_not_conjTranspose_mul_self_le_smul_one_le_…`.
Gauge statements live in `SymmetricGauge` with `Φ` first (S1 Q5) and keep the root prefix
`measureReal_`: the tail-prefix rule's `measure_` is for namespaces of probabilistic interfaces
(`HasSubgaussianMGF`, `IsSubgaussianVector`), and `SymmetricGauge` is a Matrix-layer norm.

**Q11. Publishing R4's private diagonal law (not hard).** `hasLaw_inv_mul_conjTranspose_apply_self`
is proved but `private`, with a private abbrev `invChiSq`. Options: (a) make it public under
`hasLaw_inv_mul_conjTranspose_apply_self_of_hasLaw_gaussianMatrix` with the law written out;
(b) state R8 inside `InverseMoments.lean` (1017 lines, already over the budget). Recommendation (a):
the law is the reusable fact (S6's and the Haar layer's inverse-Wishart steps), and R8 and R9 then
live in the new file 4.

**Q12. Corrections of record (information).**
- Brief §4.3, TW (RSVD1)'s proof: "an HMT 10.4-type tail on $\|(\mathbf{Z}^{\mathsf{H}}
  \mathbf{\Omega})^{+}\|$" reads "the inverse-Wishart trace tail TW (B.3) on
  $\|(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^{+}\|_{\mathsf{F}}^2$"; TW's failure constant is
  $\sqrt{\pi k}$ in Theorem 8.1 and $\sqrt{\pi k/(\ell - k + 1)}$ in (B.3).
- Brief §4.3, "HMT 10.7 and 10.8 (R1's Lipschitz concentration plus R4's moments) sit beside it or
  follow as corollaries": they sit beside it (Q6), and need, beyond R1 and R4, the
  independent-factor concentration R11 and the trace tail R9.
- Brief §7, S3 entry: the Haar versions need H1 (not only R5's transfer, which is for `haarFrame`
  only), and S3 is about 1720 lines, not 800 (§4).
- Brief §2, "R1 Lipschitz concentration in Frobenius (HMT Proposition 10.3)": fixed functions only;
  the conditional form HMT's and TW's proofs use is R11.

## 8. Amendments from the review (2026-10-15)

Review of this note (2 medium, 6 low, 2 information), all ten amendments accepted by the
orchestrator; none rejected. Three are corrected on inspection: item 3's crossover is in $t^2$, not
$t$; item 7's "either is fine" for `gaussianPinvSpecNormBound` is not, because Q8's wrap-up
restatement forces `InverseMoments/Spectral.lean`; item 2's new small ball joins the existing
result id instead of taking its own. Q1, Q2 and Q5 accepted as recommended (items 11 to 13; Q2 with
the home of item 7); Q3, Q4 and Q6 to Q12 stand (item 14). The review found every statement true
as written except R11 in a degenerate shape (item 1); checked the degenerate cases of §3.0 and the
$\ell = k + 1$ counterexample; recomputed R9's constant along the min route, R14's
$\sqrt{u} - 1$ step and $e^{-(\sqrt{u}-1)^2/2} \le e^{-(u-2)/4}$; matched R15, R16, P8, P9 against
HMT's proof of Theorem 10.8; checked G3's `ℝ≥0∞` arithmetic at $p = \top$; confirmed that every
library and Mathlib name §1 and §3 rely on exists with the stated shape; and verified the
literature locators from the PDFs (TW (B.3) reads $\sqrt{\pi r/(k-r+1)}\,t^{-(k-r+1)/2}$ at threshold
$etr/(k-r+1)$; Theorem 8.1 prints $\sqrt{\pi r}\,(t/e)^{-(k-r+1)/2}$; HMT (10.5) reads
$\mathbb{P}\{\|\mathbf{G}^{\dagger}\|_{\mathsf{F}} \ge \sqrt{12k/p}\cdot t\} \le 4t^{-p}$, rechecked
here). Where an item below contradicts §0 to §7, it supersedes them; §3 stays as drafted.

1. **A1, R11 is false when $m$ or $n$ is empty** (§3.2, R11). On a subsingleton `Matrix m n ℝ`,
   `hlip` holds for every $L$, including $L(y) < 0$; with $f(y, \cdot) = c(y)$ and $L(y)t < 0$ the
   failure event is the whole space and $e^{-t^2/2} < 1$ fails. R11 gains
   `(hL0 : ∀ y, 0 ≤ L y)` after `hL`; the docstring says "$L \ge 0$". The consumers R14 to R16 supply
   it by `positivity` ($L = \|\mathbf{S}\|_{\mathsf{F}}\|\mathbf{T}\|_{\mathsf{F}}$ or
   $\|\mathbf{S}\|_2\|\mathbf{T}\|_2$). The route is unchanged; the case $L(y) = 0$ stays as drafted.
2. **A2, the exact-density χ² small ball, and the RSVD1 tail beats TW** (amends §1's
   `gaussianPinvFrobTail` entry, §3.2 R8, R9 and the factor routes, Q3, the second departure bullet,
   "Missing infrastructure" for TW (RSVD1), §5's rows R8, R9 and P1 to P4). The whole loss against
   (B.3) was the Chernoff small ball $(eu/d)^{d/2}$. A new statement C1 in
   `Probability/Distributions/ChiSquareMoments.lean` (about 50 lines):
   ```lean
   /-- **Small-ball bound for $\chi^2$, exact density**: for a standard Gaussian vector
   $\mathbf{g}$ of dimension $d = \lvert n \rvert$ and $u \ge 0$,
   $\mathbb{P}(\|\mathbf{g}\|^2 \le u) \le (u/2)^{d/2} / \Gamma(d/2 + 1)$. Below
   `measureReal_norm_sq_le_le_rpow_of_hasLaw_gaussianVector` by $\Gamma(x + 1) \ge (x/e)^x$.
   Result: chi-square-small-ball -/
   theorem measureReal_norm_sq_le_le_rpow_div_Gamma_of_hasLaw_gaussianVector
       (hg : HasLaw g (gaussianVector n) μ) {u : ℝ} (hu : 0 ≤ u) :
       μ.real {ω | ‖WithLp.toLp 2 (g ω)‖ ^ 2 ≤ u} ≤
         (u / 2) ^ (Fintype.card n / 2 : ℝ) / Real.Gamma (Fintype.card n / 2 + 1)
   ```
   Route: the private `integral_radial_gaussianVector` at the indicator of $[0, \sqrt{u}]$, drop
   $e^{-y^2/2} \le 1$, $\int_0^{\sqrt{u}} y^{d-1}\,dy = u^{d/2}/d$, and the normalisation as in the
   proof of `integral_norm_sq_rpow_of_hasLaw_gaussianVector` (the case $\varphi = 1$), which gives
   $u^{d/2}/(d\,2^{d/2-1}\Gamma(d/2)) = (u/2)^{d/2}/\Gamma(d/2+1)$; $d = 0$: both sides $1$. The
   private lemma fixes the home; the result id is the existing node's (the same result with the
   exact constant; D11 gives one node per result), not a new one as the review suggested.
   Consequences, along the note's own min-and-layer-cake route:
   - **R8 is restated** with the exact constant (its right side changes; R9 needs it):
     `μ.real {ω | s ≤ (X ω * (X ω)ᴴ)⁻¹ i i} ≤ (1 / (2 * s)) ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2 + 1)`,
     by C1 at $u = 1/s$.
   - **The body of `gaussianPinvFrobTail` becomes**
     `2 * √(k : ℝ) * ((d : ℝ) / (2 * t)) ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2 + 1)`, that is
     $2\sqrt{k}\,(d/(2t))^{d/2}/\Gamma(d/2 + 1)$ (R9's layer cake now gives
     $\mathbb{E}\min(a, D_i^d) \le 2\,(1/2)^{d/2}\sqrt{a}/\Gamma(d/2+1)$). It stays an
     `irreducible_def` (rule 2: the proved value is not the source's). §3.0's degenerate values
     are unchanged: $0$ at $k = 0$, $2\sqrt{k} \ge 2$ at $d = 0$, and $0 < t$ is still needed.
   - **`gaussianPinvFrobTail_le` keeps its statement** ($\le 2\sqrt{k}\,(e/t)^{d/2}$), proved from
     the body by $\Gamma(x + 1) \ge (x/e)^x$ at $x = d/2$, a private lemma of `BlockTail.lean`
     (`Real.Gamma_eq_integral`, integrate over $[x, \infty)$; a ForMathlib candidate at the
     wrap-up). `gaussianPinvFrobTail_nonneg` keeps `0 < t` (item 10(d)).
   - **Docstring of `gaussianPinvFrobTail`**: proved value $2\sqrt{k}\,(d/(2t))^{d/2}/
     \Gamma(d/2+1)$; source value $\sqrt{\pi k/d}\,(e/t)^{d/2}$ [TroppWebber2023, Lemma B.2 (B.3)],
     printed as $\sqrt{\pi k}\,(e/t)^{d/2}$ in their Theorem 8.1; the proved value is smaller for
     every $d \ge 1$, at most $2/\pi$ times (B.3)'s and $2/(\pi\sqrt{d})$ times Theorem 8.1's (by
     $\Gamma(x+1) \ge \sqrt{2\pi x}\,(x/e)^x$), and asymptotically $2/\pi$ times (B.3)'s as $d$ grows. §1's
     "gap factor" sentence and "an improvement to TW's constant changes the body" are superseded;
     the departure bullet reads "TW (RSVD1) is reached with a smaller failure constant".
   - **Gap recorded**: displaying the $\frac{2}{\pi}\sqrt{\pi k/d}\,(e/t)^{d/2}$ form as a lemma
     needs Stirling's lower bound for $\Gamma$ at half-integers (real $x > 0$), which Mathlib has
     only for factorials (`Stirling.le_factorial_stirling`, `Stirling.sqrt_pi_le_stirlingSeq`;
     they cover even $d$ only). Until it exists the comparison lemma stays at
     $2\sqrt{k}\,(e/t)^{d/2}$; adding it later is one new `_le` lemma, no statement changes.
   - **Q3** reads: "(a') adopted: the exact small ball and the min route; the body beats (B.3) by
     $2/\pi$. The displayed comparison waits for Stirling at half-integers." §5's R8, R9 row reads
     "exact small ball, min in place of the parallel sum; below (B.3) for every $d$"; P1 to P4's
     docstrings say the library's second failure term is smaller than TW's.
3. **A3, HMT Proposition 10.4 is not reachable, and R9 dominates its (10.5) in practice**
   (docstrings of R9, R10, P8, P9; Q6; §5 rows R10 and P8, P9). Recorded as not reachable now:
   (10.6), $\mathbb{P}\{\|\mathbf{G}^{\dagger}\| \ge e\sqrt{k+p}/(p+1)\cdot t\} \le t^{-(p+1)}$, is
   Markov at the $(p+1)$-th spectral moment, which R4's probe route cannot produce (the probes are
   $1/\chi^2_{p+1}$, whose moment of order $(p+1)/2$ diverges; that is why R4 stops at
   $q \le k - r$); HMT prove it from the smallest-singular-value density (their Proposition A.3).
   (10.5) is their Theorem A.6, a bidiagonalisation argument (HMT p. 66: "rather lengthy"). Neither
   is modest. What the library has instead:
   - **R9 against (10.5).** At HMT's threshold $\sqrt{12k/p}\,t$ ($d = p + 1$, R9 at
     $t' = 12(p+1)t^2/p$), R9 gives at most $2\sqrt{k}\,(e/12)^{(p+1)/2}t^{-(p+1)}$ against HMT's
     $4t^{-p}$: smaller unless $k > 4(12/e)^{p+1}t^2$ (for $p = 4$, $k$ above about $6700\,t^2$),
     and with the better exponent. **Correction on inspection:** the review's crossover
     "$4(12/e)^{p+1}t$" squares $\sqrt{k} < 2(12/e)^{(p+1)/2}t$ wrongly; it is $t^2$, which only
     widens the regime (HMT take $t \ge 1$).
   - **R10 against (10.6)** is the one true loss: $t^{-p}$ in place of $t^{-(p+1)}$, at threshold
     `gaussianPinvSpecNormBound` $\le e\sqrt{k+p}/p$, at most $(p+1)/p$ times HMT's threshold
     constant (the review's comparison is with Proposition 10.2's $e\sqrt{k+p}/p$; against 10.4 the
     factor $(p+1)/p$ is added here).
   - **Docstrings.** R9 adds: "Compare [HalkoMartinssonTropp2011, Proposition 10.4 (10.5)],
     $4t^{-p}$ at $\sqrt{12k/p}\,t$, which this bound is below unless $k > 4(12/e)^{p+1}t^2$." R10
     adds: "HMT's (10.6) has $t^{-(p+1)}$ through the smallest-singular-value density, not reached
     by moments." P8 and P9 replace "the library's constants" by: "HMT print $\sqrt{12k/p}$,
     $e\sqrt{k+p}/(p+1)$ and $5t^{-p} + 2e^{-u^2/2}$ ($e^{-u^2/2}$ for 10.8) from their
     Proposition 10.4, whose tails are not reached here; the Frobenius part of this failure term is
     below HMT's in every practical regime, the spectral part loses one power of $t$." Q6's last
     sentence reads the same.
4. **A4, H1's citation, home and H3's route** (§3.3; §4 file 5; §5 row H1 to H3). EW §6 contains
   no polar-factor reduction (§6.3, §6.4 apply $\mathbf{Q}^{*}\mathbf{\Omega} \sim \mathbf{\Omega}$
   directly). H1 is a standard corollary of the Haar frame's characterization: its docstring drops
   "[EpperlyWebber2026, §6] (... locator to confirm)" and says "the hypothesis class is EW's
   full-rank rotation-invariant embedding [EpperlyWebber2026, p. 2]". §5's row reads "H1 to H3:
   helpers, no citation (the class: EW p. 2)". **Home:** H1 goes beside
   `hasLaw_haarFrame_of_isLeftUnitarilyInvariant` in `RandomMatrix/Haar/Uniqueness.lean` (326 lines;
   new import `Matrix/Factorizations/Polar` if not transitive); H2 and H3 stay in `Haar/Transfer.lean`,
   which gains the import of `Haar/Uniqueness` (no cycle: `Uniqueness` imports only `Haar/Basic`).
   **H3's route:** H1, `ae_rank_mul_eq_min_of_hasLaw_haarFrame` at the polar factor, and
   $\operatorname{rank}(\mathbf{A}\,\mathrm{polar}(\mathbf{X})) = \operatorname{rank}(\mathbf{A}
   \mathbf{X})$ (`rangeProjector_mul_polarFactor`, ranges equal for every $\mathbf{X}$), in place of
   the route through `rank_rangeProjector`, H2 and the Gaussian a.s. rank.
5. **A5, outer-measure semantics in P6 and P7** (§3.0 item 3; P6, P7 docstrings). Both halves are
   said. P6's last sentence becomes: "The event may be non-measurable; `μ.real` is then the outer
   measure, so this bound says exactly that the failure event lies in a measurable event of at most
   this probability (`exists_measurable_superset`), and such bounds compose by
   `measureReal_union_le`. The success-set form, probability at least $1 - \delta$ for the good
   event, does not follow without measurability (`measureReal_compl` needs `MeasurableSet`)." P7's
   docstring repeats the last sentence. §3.0 item 3's "Each docstring says this" reads "Each
   docstring says this and that the success-set form does not follow". The review confirmed the
   rest of §3.0 (the selector only for spectral truncated expectations, `integral_undef`); L8, L9,
   U2 are kept.
6. **A6, the law-free lemmas get their own file** (§3.1; §4 file 6; §0's row "law-free
   integrability"; Q9). L1 to L9 (and L10, item 8) move to **`LowRank/Random/RangeFinder.lean`**
   (name proposed here, the orchestrator's to change): over `𝕜`, any law, importing only
   `LowRank/Structural/{RangeFinder,Truncation}`, `Matrix/Spectral/BestRankApprox` and
   `Probability/Measurability/Matrix`. S7's `LowRank/Oblivious` files import it without the
   Gaussian block tail, χ² and Haar transfer. Correction of record for the brief: D12's
   `LowRank/` list gains "`Random/`: law-free facts about a random test matrix (integrability,
   selector reductions)". **The review's optional split is taken:** I1 to I5 (and I6, item 8) and
   P10 open `LowRank/Gaussian/RotationInvariant.lean`, the file S4 extends (brief §7), so S4's
   sharpenings land beside the statements they sharpen and `Gaussian/RangeFinder.lean` no longer
   imports the Haar layer.
7. **A7, homes of the two RandomMatrix constants** (§1; §3.2 "Named quantities"; §4 file 4; Q2;
   Q8). N1 to N4 (`gaussianProjectionFactor`, `_def`, `one_le_…`, `…_le_…`) go into
   `RandomMatrix/Gaussian/BlockMoments.lean` (213 lines), which S6's
   `Sketching/Gaussian/LeastSquares.lean` imports anyway for
   `integral_frobNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix`. **Correction on inspection:** the
   review leaves `gaussianPinvSpecNormBound` (N8 to N10) to either `BlockTail.lean` or
   `InverseMoments/Spectral.lean`; only the second works. Q8 restates R4's
   `integral_specNorm_pinv_rpow_le_of_hasLaw_gaussianMatrix`,
   `integral_specNorm_pinv_le_of_hasLaw_gaussianMatrix` (both in `InverseMoments/Spectral.lean`)
   and `integral_specNorm_mul_mul_pinv_le_of_hasLaw_gaussianMatrix` (`BlockMoments.lean`) with the
   name at the wrap-up, and both files sit below `BlockTail.lean`. N8 to N10 go into
   `InverseMoments/Spectral.lean` (702 lines). `BlockTail.lean` keeps N5 to N7, R8 to R10, R14 to
   R16.
8. **A8, HMT 10.5's printed form** (§3.5 after G2; §3.6 after I2; §3.1). Added, about ten lines
   each, by Jensen from the squared form ($\mathbb{E}Z \le (\mathbb{E}Z^2)^{1/2}$, the pattern of
   R4's `integral_frobNorm_pinv_le_of_hasLaw_gaussianMatrix`); §6's cut of unsquared gauge
   moments (for want of $\mathbb{E}\|\mathbf{M}\|_\Phi$) does not apply here.
   ```lean
   /-- **The expected error of the randomized SVD, Frobenius norm, as printed** (HMT Theorem 10.5):
   $\mathbb{E}\|\mathbf{A} - \mathbf{P}_{\mathbf{A}\mathbf{X}}\mathbf{A}\|_{\mathsf{F}} \le
   \bigl(1 + \frac{k}{\ell - k - 1}\bigr)^{1/2}\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k
   \|_{\mathsf{F}}$, by Jensen from the squared form; there with $k \ge 2$ and
   $k + p \le \min\{m, n\}$, both unneeded. [HalkoMartinssonTropp2011, Theorem 10.5].
   Result: randomized-svd-expected-error -/
   theorem integral_frobNorm_sub_rsvd_le_of_hasLaw_gaussianMatrix (A : Matrix m n ℝ)
       (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ} (hk : k + 2 ≤ Fintype.card l) :
       ∫ ω, frobNorm (A - rsvd A (X ω)) ∂μ ≤
         √(gaussianProjectionFactor k (Fintype.card l)) * frobNorm (A - truncatedSVD A k)
   ```
   G6 is this; I6, `integral_frobNorm_sub_rsvd_le_of_isLeftUnitarilyInvariant`, is its
   rotation-invariant twin (from I2, [EpperlyWebber2026, Theorem 3.1]). D4's companion is a new
   law-free L10, `integrable_frobNorm_sub_rsvd [IsFiniteMeasure μ] (A : Matrix m n 𝕜)
   (hX : AEMeasurable X μ) : Integrable (fun ω => frobNorm (A - rsvd A (X ω))) μ` (L2 at the
   Frobenius gauge, as L6 is at the spectral one). §5's G2, I2 row covers G6, I6.
9. **A9, one skeleton for R15, R16, P8, P9** (§3.2 and §3.7 routes; §4 sizes; Q6). R15 and R16 are
   both "good event of $\mathbf{G}_1^{+}$ (R9 at $t^2$, R10), then R11 with $(f, L, c)$": one private
   lemma of `BlockTail.lean`, parametrised by $(f, L, c)$, the Lipschitz bound and the Gaussian mean
   (R13 or Chevet), proves both. P8 and P9 share a private lemma of `RangeFinderTail.lean` that
   turns an a.e. pointwise bound by the block quantity into the block tail. About 80 of the
   160 lines go. Q6 stands as recommended (the brief lists 10.7 and 10.8), but these four are the
   first to drop if the stage runs long: nothing in S5 to S7 consumes them.
10. **A10, minor record items.** (a) R15, R16, P8, P9: given `hd`, `hrk` (`hkl`) is $d \ge 2$;
    neither follows from the other alone (§5.2 met), and each docstring adds "`hrk` is $d \ge 2$"
    ("`hkl`" in P8, P9). (b) §1's gap factors are superseded by item 2 (the gap is now negative for
    every $d \ge 1$). (c) Q12's correction of brief §4.3 ((B.3) is the sharper source than
    Theorem 8.1's $\sqrt{\pi k}$) is confirmed. (d) `gaussianPinvFrobTail_nonneg` keeps `0 < t`: for
    $t \le 0$ the real power of a negative base is not sign-controlled; its docstring says so.
11. **Q1 accepted as recommended, (a).** The Gram form is primary (D4, already the shape of S1's
    proved structural bound); S5 reads every Nyström expectation and tail off it by one rewrite;
    $\Phi(\mathbf{e}_0) = 1$ for every Schatten gauge (M3); the printed HMT and TW forms are G2 to
    G4, G6 and P2 to P4, so no searchable statement is lost.
12. **Q2 accepted as recommended, with the home of item 7.** `gaussianProjectionFactor (k l : ℕ)`,
    a plain `def` with a `_def` simp lemma, in `RandomMatrix/Gaussian/BlockMoments.lean`; the
    multiplicative forms (G2, G6, U1, I2, I4, I6) use it, the excess $k/(\ell - k - 1)$ stays inline
    (one simp call from "factor minus one"). The names fixed for S4 and S6,
    `rotationInvariantFactor r l q` and `haarProjectionFactor d p q`, stand.
13. **Q5 accepted as recommended, (a).** `HasLaw X ν μ` with `[IsLeftUnitarilyInvariant ν]` and
    a.s. full column rank (CONTRIBUTING §5.4; EW Theorem 3.1's class); Haar and Gaussian are
    instances; the cost is H1. Unsatisfiable for $\ell > n$, harmlessly (exact a.s. by
    `ae_rank_mul_eq_min_of_hasLaw_haarFrame`). Haar-specific corollaries stay additive.
14. **Q3, Q4 and Q6 to Q12 stand as recommended**, Q3 amended by item 2, Q6 by items 3 and 9,
    Q8 by item 7 (the name lives in `InverseMoments/Spectral.lean`), Q9 by items 6 and 8 (L1 to
    L10, in their own file).
15. **Placement for the proof stage** (amends §3.4's last sentence and §4's last paragraph, as S2a
    §8 item 18). A statement whose home is an existing proved file goes there only once proved; a
    statement still `sorry` goes into a side file that says it merges into its home at the wrap-up.
    Homes and side files: M1 to M3, `Matrix/Norms/{Nuclear,Schatten,GaugeExamples}.lean`, side
    `Matrix/Norms/GramNorms.lean`; C1, `Probability/Distributions/ChiSquareMoments.lean`, side
    `Probability/Distributions/ChiSquareSmallBall.lean` (a placeholder only: C1's proof uses the
    private `integral_radial_gaussianVector`, so it is proved in its home); N1 to N4,
    `RandomMatrix/Gaussian/BlockMoments.lean`, side `RandomMatrix/Gaussian/ProjectionFactor.lean`;
    N8 to N10, `RandomMatrix/Gaussian/InverseMoments/Spectral.lean`, side
    `RandomMatrix/Gaussian/InverseMoments/SpectralBound.lean`; R11, `Gaussian/Concentration.lean`,
    side `Gaussian/ConcentrationIndep.lean`; R12, R13, `Gaussian/Moments.lean`, side
    `Gaussian/MomentsFrob.lean`; H1, `Haar/Uniqueness.lean`, side `Haar/PolarFactorLaw.lean`; H2,
    H3, `Haar/Transfer.lean`, side `Haar/TransferInvariant.lean`. The diagonal law of
    `InverseMoments.lean` is already proved; making it public is the only change there. The five new
    files (`BlockTail`, `LowRank/Random/RangeFinder`, `LowRank/Gaussian/{RangeFinder,RangeFinderTail,
    RotationInvariant}`) may take `sorry` statements.
16. **Files and statements** (amends §4):

    | # | File | Statements | Lines (est.) | Imports (new) | Depends on |
    |---|---|---|---|---|---|
    | 1 | `Matrix/Norms/{Nuclear,Schatten,GaugeExamples}.lean` (registered; or side file, item 15) | 3 (M1 to M3) | +40 | none | none |
    | 2 | `Probability/Distributions/ChiSquareMoments.lean` (registered; item 15) | 1 (C1) | +50 | none | none |
    | 3 | `RandomMatrix/Gaussian/InverseMoments.lean` (registered) | 1 made public (the diagonal law) | +10 | none | none |
    | 4 | `RandomMatrix/Gaussian/InverseMoments/Spectral.lean` (registered; or side file) | 3 (N8 to N10) | +25 | none | none |
    | 5 | `RandomMatrix/Gaussian/BlockMoments.lean` (registered; or side file) | 4 (N1 to N4) | +30 | none | none |
    | 6 | `RandomMatrix/Gaussian/{Concentration,Moments}.lean` (registered; or side files) | 3 (R11 to R13) | +110 | `Probability/Law` (product law) | none |
    | 7 | `RandomMatrix/Gaussian/BlockTail.lean` (new) | 9 (N5 to N7, R8 to R10, R14 to R16) | 350 | files 2 to 6 | files 2 to 6 |
    | 8 | `RandomMatrix/Haar/Uniqueness.lean` (registered; or side file) | 1 (H1) | +50 | `Factorizations/Polar` if not transitive | none |
    | 9 | `RandomMatrix/Haar/Transfer.lean` (registered; or side file) | 2 (H2, H3) | +35 | file 8, `Factorizations/PolarFrames` | file 8 |
    | 10 | `LowRank/Random/RangeFinder.lean` (new) | 10 (L1 to L10) | 205 | `LowRank/Structural/{RangeFinder,Truncation}`, `Probability/Measurability/Matrix` | none |
    | 11 | `LowRank/Gaussian/RangeFinder.lean` (new) | 9 (G1 to G6, U1, U2, E1) | 320 | files 1, 4, 5, 10 | files 1, 4, 5, 10 |
    | 12 | `LowRank/Gaussian/RangeFinderTail.lean` (new) | 9 (P1 to P9) | 360 | files 7, 11 | files 7, 11 |
    | 13 | `LowRank/Gaussian/RotationInvariant.lean` (new; S4 extends it) | 7 (I1 to I6, P10) | 140 | files 9, 11, 12 | files 9, 11, 12 |

    S3 is about 1725 lines and 62 public declarations (61 new, 3 of them definitions, plus the one
    made public): the draft's 58, plus C1, L10, G6, I6. Item 9 saves about 80 lines; C1, the
    restated R8 with the private Gamma bound, L10, G6 and I6 add about 85. Every file stays under the
    1000-line limit (`InverseMoments/Spectral.lean` reaches about 730, `ChiSquareMoments.lean` about
    530). Order: files 1 to 6 and 10 are independent; file 7 after 2 to 6; file 9 after 8; file 11
    after 1, 4, 5, 10; file 12 after 7 and 11; file 13 last. The expectations (file 11) no longer
    import the tail machinery or the Haar layer. S3 needs nothing from S2b.
17. **Docstrings are LaTeX** (CONTRIBUTING §6 item 5), with the notation table; Lean names in
    backticks, never inside `$…$`; the manuscript is never cited (D13). The degenerate and
    measurability sentences of items 2, 3, 5 and 10 are part of the docstrings, not comments.
18. **Gaps recorded** (each additive when filled; none blocks S3): (i) Stirling's lower bound for
    $\Gamma$ at real arguments, for the displayed $\frac{2}{\pi}\sqrt{\pi k/d}$ comparison (item 2);
    (ii) HMT Proposition 10.4's constants, which need the smallest-singular-value density (HMT
    Proposition A.3) and HMT Theorem A.6 (item 3); (iii) a measurable best-approximation selector,
    for L8, L9, U2 (§3.0, unchanged); (iv) $\mathbb{E}\|\mathbf{M}\|_\Phi$ for the nuclear gauge, for
    unsquared gauge moments (§6, unchanged).

### Orchestrator addendum (2026-10-15): placement of the χ² small ball

Item 2 is amended on placement. The two χ² files split by method: `ChiSquareMoments.lean` holds
the density-level facts (the exact real moments through $\Gamma$), `ChiSquare.lean` the Laplace
transform and the tails. The exact small ball C1 is a tail, so it goes in `ChiSquare.lean`, which
gains the import of `ChiSquareMoments.lean` (no cycle: `ChiSquareMoments.lean` imports only
`Distributions/Gaussian`). The Chernoff small ball
`measureReal_norm_sq_le_le_rpow_of_hasLaw_gaussianVector` is dominated by C1
($\Gamma(x + 1) \ge (x/e)^x$), so it is reproved as C1's corollary and keeps its name and statement
(CONTRIBUTING §5.2, rule 6). Every χ² tail is then in one file. If the density step C1 needs is
general (the law of $\|\mathbf{g}\|^2$ as a pushforward with a density), it is a public lemma of
`ChiSquareMoments.lean`.
