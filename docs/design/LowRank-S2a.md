# Design note: LowRank stage S2a, late truncation (deterministic)

Status: drafted 2026-10-15 under `docs/PORT_LOWRANK.md` (maintainer decisions of 2026-10-15, with
the error-spelling rule: every error is $\mathbf{A}$ minus the named output, truncated outputs
included; D1, D3, D4, D5, D9 to D11, D13, D15; §4.1 item 7, §4.2, §4.3 "Nyström" and "Truncated GN",
§5.1, §5.2, the S2a entry of §7, §9.3), `docs/design/LowRank-S0.md` (§3 as amended by §8; proved and
registered) and `docs/design/LowRank-S1.md` (§8 overrides §3; proved and registered: L1, L2, L5a,
L5b in `Matrix/Spectral/LowRank.lean`, `LowRank/Structural/RangeFinder.lean` in `NLAlib.lean`).
Deterministic, over `𝕜`, every shape, rank and truncation rank. Reviewed 2026-10-15, amendments in
§8, which overrides §0 to §7 where they disagree (§3 stays as drafted); Q1 to Q3 decided (§8 items
13 to 15), with the naming of truncated outputs, late and early, one joint question for the
maintainer at the S2b checkpoint.

Departures from the brief, each argued below:
- **Two files, one per layer.** The statements about a general matrix and a general approximation
  (the optimality predicate, the constant-1 and constant-2 lemmas, reverse Eckart–Young, perturbed
  truncation, the Gram truncation identity) are deterministic matrix analysis and go to a new
  Matrix-layer file `Matrix/Spectral/BestRankApprox.lean`; `LowRank/Structural/Truncation.lean`
  keeps the statements about the named outputs `rsvd`, `nystrom`, `generalizedNystrom` (Q4; S1 Q7
  is the precedent).
- **D5's predicate is added**: `IsBestRankApprox C k Y`. D5's threshold ("more than three
  statements") is passed by ten (§2, Q2).
- **The perturbed-truncation lemma is stated in the sharper parameter**
  $\|\llbracket\mathbf{E}\rrbracket_{2k}\|_{\mathsf{F}}$, the quantity the manuscript's own proof
  passes through; $2\sqrt{2k}\,\|\mathbf{E}\|_2$ is its corollary. In Frobenius norm it dominates
  both bounds of D10's late-truncation pair, so the pair becomes one lemma and two corollaries. No
  `RankTraceBound` interface (Q5).
- **MT Theorem 14.1's constant is reachable.** TYUC NeurIPS reach it from the trace bound by a
  deterministic "reversed Eckart–Young" inequality (their Proposition A.8, after Gu 2015 Theorem
  3.4). S2a adds it in two forms (squared Frobenius and nuclear). Brief §4.3 ("This brief's route
  does not reach it") and §9.1 are corrected; S5 can promise MT 14.1 (Q6).
- **The deterministic assembly of truncated GN moves from S6 to S2a**, basis-free: the core noise
  appears as $\mathbf{\Pi}_{\mathbf{A}\mathbf{\Omega},\mathbf{\Psi}^{\mathsf{H}}}
  (\mathbf{A}-\mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A})$, S0's second term (Q7).
- **Item 7.7 (Woodruff Theorem 47's rank-$k$ clause) is not in S2a.** It is rank-constrained
  sketched regression, a different estimator from $\llbracket\mathbf{A}\langle\mathbf{\Omega},
  \mathbf{\Psi}\rangle\rrbracket_k$; it goes to S7 with the D15 check (Q8).
- **No new names for truncated outputs**: `truncatedSVD (rsvd A Ω) k`, as the brief's D1 table
  and S0 §1 say. Recorded as a hard-to-reverse naming decision for the maintainer (Q1).

**Literature checks.** TYUC SIMAX's constant-2 lemma is confirmed: arXiv v2 Proposition 6.1
(p. 16), $\|\mathbf{A}-\llbracket\hat{\mathbf{A}}\rrbracket_r\|_{\mathsf{F}} \le \tau_{r+1}(\mathbf{A})
+ 2\|\mathbf{A}-\hat{\mathbf{A}}\|_{\mathsf{F}}$, with Remark 6.2 (p. 17) for the spectral norm;
arXiv v1 numbers it Proposition 7.1, and TYUC NeurIPS Proposition A.6 (p. 10) restates it for every
Schatten norm. MT Theorem 14.1 (p. 496) is TYUC NeurIPS Theorem 4.1 (4.2) (p. 5); its proof (App.
A.5, A.6, pp. 11 to 12) is the Schatten-1 bound (4.1) plus Proposition A.8, both within reach (B16;
T8 with S1's truncation for free, §3.6).

**Missing infrastructure.** Below the Matrix layer: nothing. In the Matrix layer: the predicate and
its API (§3.1), the pairing of a rank-$r$ matrix with $\llbracket\mathbf{E}\rrbracket_r$ (B17),
reverse Eckart–Young (B15, B16), the trace of a truncated Gram matrix (B20), the Loewner bound
$\llbracket\mathbf{A}\rrbracket_k \preceq \mathbf{A}$ for PSD $\mathbf{A}$ (B21), and the
singular-value domination of Nyström (N1). From S1, in `LowRank.lean` and being proved: L1
`mul_rangeProjector_conjTranspose_truncatedSVD` (T6), L2
`exists_hasOrthonormalCols_mul_mul_conjTranspose_eq_truncatedSVD` and L5b
`Matrix.PosSemidef.one_sub_mul_mul_one_sub_eq_sub_truncatedSVD` (B21). From S0: nothing missing.
S2a does not import S1's `RangeFinder.lean`. Not S2a's to fill, flagged for S3, S5, S6: the
measurability of choice-dependent truncated errors (Q3).

## 0. Scope and consumers

$\mathbf{A}$ : `Matrix m n 𝕜`, an approximation $\hat{\mathbf{A}}$ of the same shape, a truncation
rank $k : \mathbb{N}$ (any value; at or above the rank the truncation is the identity),
$\llbracket\mathbf{A}\rrbracket_k$ = `truncatedSVD A k` (a choice under ties, D5). The named outputs
are S0's: `rsvd A Ω`, `nystrom H Ω`, `generalizedNystrom A Ω Ψ`, with the test matrix
$\mathbf{\Omega}$ : `Matrix n l 𝕜` on the right and $\mathbf{\Psi}$ : `Matrix m p 𝕜` applied as
$\mathbf{\Psi}^{\mathsf{H}}$ (D2, D14). Late truncation is `truncatedSVD` of the output.

| Item | Consumers |
|---|---|
| `IsBestRankApprox` and its API (B1 to B11) | S6 (truncated GN: $\llbracket\mathbf{Q}\hat{\mathbf{X}}\rrbracket_k = \mathbf{Q}\mathbf{Y}$ with $\mathbf{Y}$ a best approximation of the core); S7 (truncated OSI GN); S3, S5, S6 (expectations over a measurable best-approximation selector, Q3); users holding an algorithm's $\mathbf{Q}\llbracket\mathbf{X}\rrbracket_k$ |
| tail domination, constant-1 lemma (B12, B13) | S3 (HMT 9.3, spectral tails of truncated RSVD); S5 (truncated Nyström pointwise and tail forms); S6 ($\gamma \le \mathrm{OPT}$, T12) |
| constant-2 lemma (B14) | S6, S7 (GN in every gauge, where no domination holds); users truncating any approximation |
| reverse Eckart–Young (B15, B16) | S5 (MT Theorem 14.1 from the trace bound); S3 (spectral second moment of truncated RSVD from the Frobenius one) |
| perturbed truncation (B17 to B19) | T10, T11; S6 (truncated GN in expectation, the $\varepsilon^{-3}$ to $\varepsilon^{-2}$ step); S7 (truncated GN under an OSI) |
| Gram truncation identity, PSD order (B20, B21, N1) | T2, T7 to T9; S5 |
| HMT 9.3 and its Frobenius forms for `rsvd` (T1, T3, T4, T12) | S3 (truncated RSVD with HMT's constant, spectral and Frobenius); S7 (CEMT's truncation remark in Frobenius) |
| choice-free bridge (T5) | S3, S5, S6 (S1's truncation for free, stated for $\mathbf{Q}\llbracket\mathbf{Q}^{\mathsf{H}}\mathbf{A}\rrbracket_k$, rewritten to the named output) |
| Gu's projected form (T6) | S5 docstring (TYUC NeurIPS's route); users without S1's rank hypothesis |
| truncated Nyström: gauge, trace, order (T2, T7 to T9) | S5 (trace bound with $1+\frac{k}{\ell-k-1}$, MT 14.1); Solvers (Nyström PCG uses $\llbracket\hat{\mathbf{H}}\rrbracket_k \preceq \mathbf{H}$) |
| truncated GN deterministic assembly (T10, T11) | S6 (spectral core noise and residual plug in); S7 |

Not in S2a: early truncation and PCPs (S2b); anything probabilistic (S3 to S7); S1's truncation for
free (proved there, consumed through T5); Woodruff Theorem 47's rank-$k$ clause (S7, Q8); the
two-sided estimator and rank-constrained GN (D15, not ported).

## 1. Objects

One new predicate, `IsBestRankApprox` (§2). No new function, so no truncated-output names (Q1). No
deviation from Mathlib: Mathlib has no low-rank approximation, so the predicate joins the list
"Additions where Mathlib has nothing" in `docs/design/Mathlib-deviations.md` (one name added to the
paragraph, in the commit that adds it; no numbered entry). The Matrix-Spectral note removed the
prototype's `IsBestFrobRankApprox` because `truncatedSVD` sufficed for Eckart–Young; it returns here
for the reason D5 gives, which that note did not face: `truncatedSVD (Q * X) k` equals
$\mathbf{Q}\mathbf{Y}$ only for *some* best approximation $\mathbf{Y}$ of $\mathbf{X}$.

**§5.3 rows** (added by the PR that adds B1; two reviews):

| Concept | Spelling | Bridge |
|---|---|---|
| best rank-$k$ approximation (amended row) | as now (`truncatedSVD A k`, optimal errors `singularValues A k` and `frobNorm (A - truncatedSVD A k)`); **any** Frobenius-best approximation, when the one at hand is not `truncatedSVD` of the same matrix (an algorithm's $\mathbf{Q}\llbracket\mathbf{X}\rrbracket_k$, a selector): `IsBestRankApprox A k Y`; it is then optimal in every unitarily invariant norm | `isBestRankApprox_truncatedSVD`; `isBestRankApprox_iff_isMinOn`; `IsBestRankApprox.matrixNorm_sub` |
| truncated outputs (amends S0's "low-rank approximations from sketches" row, which already says "no names") | late: `truncatedSVD (rsvd A Ω) k`, `truncatedSVD (nystrom H Ω) k`, `truncatedSVD (generalizedNystrom A Ω Ψ) k`; errors `A - truncatedSVD (rsvd A Ω) k` and so on (maintainer's rule); docstrings $\llbracket\mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A}\rrbracket_k$, $\llbracket\mathbf{H}\langle\mathbf{\Omega}\rangle\rrbracket_k$, $\llbracket\mathbf{A}\langle\mathbf{\Omega},\mathbf{\Psi}\rangle\rrbracket_k$ | `HasOrthonormalCols.frobNorm_sub_truncatedSVD_rsvd` (to $\mathbf{Q}\llbracket\mathbf{Q}^{\mathsf{H}}\mathbf{A}\rrbracket_k$); `HasOrthonormalCols.mul_conjTranspose_mul_truncatedSVD` |

**Used directly.** Library: `truncatedSVD` API (`rank_truncatedSVD_le`, `singularValues_truncatedSVD`,
`truncatedSVD_of_rank_le`, `truncatedSVD_zero`, `singularValues_sub_truncatedSVD`,
`frobNorm_sub_truncatedSVD_sq`, `specNorm_sub_truncatedSVD`, `frobNorm_sq_eq_truncatedSVD_add`,
`range_mulVecLin_truncatedSVD_le`, `frobNorm_sub_truncatedSVD_le_of_rank_le`); S1's L1, L2, L5b;
`singularValues_add_le_singularValues_sub_of_rank_le`; `SymmetricGauge.matrixNorm_le_of_singularValues_le`,
`.matrixNorm_add_le`, `.matrixNorm_neg`, `.matrixNorm_sub_truncatedSVD_le_of_rank_le`,
`lpGauge_two_matrixNorm`, `lpGauge_top_matrixNorm`; `IsStarProjection.singularValues_mul_le`,
`isStarProjection_rangeProjector`, `rangeProjector_mul_eq_self_iff`, `HasOrthonormalCols.rangeProjector_eq`,
`HasOrthonormalCols.singularValues_mul_left`, `HasOrthonormalCols.frobNorm_mul_left`,
`HasOrthonormalCols.frobNorm_sub_mul_sq` (`ProjectedLowRank.lean`), `frobNorm_add_sq_of_frobInner_eq_zero`;
`abs_frobInner_le_sum_singularValues_mul` (von Neumann), `frobInner_le_sqrt_mul_frobNorm_mul_specNorm_of_rank_le`,
`frobNorm_sq_eq_sum_range_singularValues_sq`, `frobNorm_le_sqrt_rank_mul_specNorm`,
`nuclearNorm_eq_sum_range`, `Matrix.PosSemidef.nuclearNorm_eq_re_trace`,
`Matrix.PosSemidef.singularValues_eq_eigenvalue`, `singularValues_conjTranspose_mul_self`,
`eigenvalue_le_eigenvalue_of_le`; `Matrix.rank_sub_le` (`ForMathlib/LinearAlgebra/Matrix/Rank.lean`).
S0: `rsvd`, `sub_rsvd`, `range_rsvd_le`, `nystrom_conjTranspose_mul_self`,
`conjTranspose_mul_self_sub_nystrom`, `nuclearNorm_conjTranspose_mul_self_sub_nystrom`,
`Matrix.PosSemidef.nystrom`, `.nystrom_le`, `.sub_nystrom_eq`, `generalizedNystrom_eq_mul_sketchAndSolve`,
`HasOrthonormalCols.sketchAndSolve_eq_add`, `mul_sketchAndSolve`, `obliqueProjector_eq_of_range_eq`,
`rank_mul_eq_iff_injOn`. Mathlib: `IsMinOn`, `Finset.sum_eq_sum_iff_of_le`,
`Finset.inner_mul_le_norm_mul_norm`, `Real.sqrt` API; library `exists_hasOrthonormalCols_range_eq`
(proof-internal basis in T10).

**Mathlib search** ("searched, none" unless named): a best low-rank approximation predicate or any
Eckart–Young statement; reverse Eckart–Young; a perturbation bound for a truncated SVD; the trace of
a truncated Gram matrix. `IsMinOn` is the notion B4 bridges to, as `isLeastSquaresSolution_iff_isMinOn`
does for least squares.

## 2. Interfaces

**New: `IsBestRankApprox C k Y`** (§5.4 review; S0 §8 item 2 places D5's hypothesis on the predicate
side, a conjunction through a library construction, so the threshold applies).
- *Bundles:* `rank_le : Y.rank ≤ k` and `frobNorm_sub_le : ∀ B, B.rank ≤ k → frobNorm (C - Y) ≤
  frobNorm (C - B)`. A `structure`, as `IsSVD`, `IsPinv`, `IsLocalMaxVolume`.
- *Leaves separate:* the norm. Frobenius optimality is the definition because it is what an SVD
  truncation has and what an algorithm computes; B5 shows it pins the singular values of the error,
  so it gives optimality in every gauge (B6). Spectral-only optimality (HMT Theorem 9.3's literal
  hypothesis) is weaker and is not covered (§6).
- *Constructors:* `isBestRankApprox_truncatedSVD` (B2); D5's one-line form
  `Y.rank ≤ k ∧ frobNorm (C - Y) ≤ frobNorm (C - truncatedSVD C k)` as the iff B3; the isometry
  transfer B9; the factored form B10.
- *Mathlib bridge:* `isBestRankApprox_iff_isMinOn` (B4).
- *API:* B5 to B8.
- *Statements taking it* (ten, against D5's threshold of three): B5 to B8, B13, B14, B18, B19, and
  the iff B9; downstream S6's truncated-GN expectation and S7.

**Existing spellings used as hypotheses:** `HasOrthonormalCols Q`; range equality
`LinearMap.range Q.mulVecLin = LinearMap.range (A * Ω).mulVecLin` (as S0's
`generalizedNystrom_eq_mul_sketchAndSolve`); S0's rank hypothesis `(Ψᴴ * (A * Ω)).rank = (A * Ω).rank`;
`H.PosSemidef`; singular-value domination `∀ i, singularValues Â i ≤ singularValues A i` (a raw
quantified condition, written twice, B12 and B13; it is the hypothesis of the library's
`matrixNorm_le_of_singularValues_le`, so it is that lemma's spelling, not a new interface; it is
meant to hold of the zero padding, where both sides are $0$, CONTRIBUTING §5.2).

**Not introduced:** `RankTraceBound` (Q5); a predicate for "singular values dominated" (above);
a per-norm optimality predicate (§6).

## 3. Statement shapes

`namespace NLAlib`, `open scoped Matrix MatrixOrder`. Variables `{𝕜 : Type*} [RCLike 𝕜]
{m n l p q : Type*}`, `[Fintype _]` on each; `[DecidableEq q]` with `Q`; `[DecidableEq n]` where
`CFC.sqrt` appears (or `open scoped Classical in`, S0's skeleton note); no statement displays `1`.
Docstrings are shortened; the full ones carry the citations of §5 and are LaTeX throughout.

**Degenerate cases** (checked for every statement; the per-section notes say where a case bites).
- *Ties* $\sigma_{k-1} = \sigma_k$. `truncatedSVD` is a choice made separately for each matrix, so
  `truncatedSVD (Q * X) k = Q * truncatedSVD X k` is not provable (both sides are best
  approximations, chosen independently). Every statement below holds for every choice: the general
  ones take `IsBestRankApprox`, the named-output ones are about `truncatedSVD` and are proved through
  B2. Choice-free quantities (they depend on singular values only): every gauge of
  $\mathbf{C}-\mathbf{Y}$ for a best $\mathbf{Y}$ (B6); the Frobenius error of the truncated RSVD (T3,
  T5); the nuclear error of truncated Nyström (T7). Choice-dependent: the spectral error of a
  truncated output. Example: $\mathbf{A} = \begin{bmatrix} 1 & 0 \\ 0 & 1 \\ 1 & 1\end{bmatrix}$,
  $\mathbf{P}$ the projector onto the first two coordinates, $k = 1$: $\mathbf{P}\mathbf{A}$ has the
  tie $\sigma_0 = \sigma_1 = 1$, and $\llbracket\mathbf{P}\mathbf{A}\rrbracket_1 =
  \mathbf{v}\mathbf{v}^{\mathsf{H}}$ (padded) gives $\|\mathbf{A}-\llbracket\mathbf{P}\mathbf{A}
  \rrbracket_1\|_2^2 = 2$ for $\mathbf{v} = (1,1)/\sqrt2$ and $3$ for $\mathbf{v} = (1,-1)/\sqrt2$;
  the Frobenius errors are both $3$. Consequence for S3 to S6: Q3.
- *$k = 0$.* `truncatedSVD _ 0 = 0` and a best approximation is $\mathbf{0}$; every bound reduces to
  an equality or to the triangle inequality (checked per statement below).
- *$k$ at or above the rank.* `truncatedSVD_of_rank_le`: the truncation is the identity, a best
  approximation is the matrix itself (B7 forces zero error); the bounds reduce to the untruncated
  ones (T4 to S0's split; T10 to S0's GN split up to the $2k$ term).
- *Empty index types.* Every matrix is $\mathbf{0}$ or the statements are $0 \le 0$; B17 with an empty
  shape is $0 \le 0$.
- *Hermitian but not PSD inputs to Nyström.* T2, T8, T9 and N1 take `hH`. N1 fails without it: for
  $\mathbf{H} = \begin{bmatrix} 1 & 1 \\ 1 & 0\end{bmatrix}$ and $\mathbf{\Omega} = (1, t)$,
  $\mathbf{\Omega}^{\mathsf{H}}\mathbf{H}\mathbf{\Omega} = 1 + 2t$ and $\lVert\mathbf{H}\langle
  \mathbf{\Omega}\rangle\rVert_2 = \lVert(1+t, 1)\rVert^2/\lvert 1+2t\rvert$ is unbounded as
  $t \to -\tfrac12$, so the constant-1 instance is unavailable and B14 (constant 2) is the lemma
  that applies. T8 fails without it: $\mathbf{H} = [-1]$, $\mathbf{\Omega} = [1]$, $k = 0$ gives
  $1$ on the left and $0$ on the right (`CFC.sqrt` of a negative matrix is $\mathbf{0}$). T7 needs no
  PSD hypothesis: $\mathbf{F}^{\mathsf{H}}\mathbf{F}$ is PSD.
- *Rank hypothesis of GN* (T10, T11): necessary. With $\mathbf{\Psi} = \mathbf{0}$, $\mathbf{A} =
  \mathbf{\Omega} = \mathbf{I}_2$, $k = 2$: the output is $\mathbf{0}$, the left side is $2$, and the
  right side is $0$ (the oblique projector is $\mathbf{0}$, $\mathbf{P}\mathbf{A} = \mathbf{A}$).
- *Singular-value domination* (B13): necessary. $\mathbf{A} = \operatorname{diag}(1, 0)$,
  $\hat{\mathbf{A}} = \operatorname{diag}(1, 1+\delta)$, $\delta > 0$, $k = 1$:
  $\llbracket\hat{\mathbf{A}}\rrbracket_1 = \operatorname{diag}(0, 1+\delta)$, and in Frobenius norm
  the left side is $\sqrt{1+(1+\delta)^2}$, the right side $0 + (1+\delta)$. B14 holds there.
- *Padded indices.* B5, B12, B13, N1 hold at every index, including the padding (both sides $0$).

### 3.1 `Matrix/Spectral/BestRankApprox.lean`: the predicate and approximations inside a range (11)

```lean
/-- $\mathbf{Y}$ is a **best approximation of $\mathbf{C}$ of rank at most $k$**: it has rank at
most $k$ and no matrix of rank at most $k$ is closer to $\mathbf{C}$ in the Frobenius norm. Then the
error has the singular values $\sigma_{k+i}(\mathbf{C})$ (`IsBestRankApprox.singularValues_sub`), so
$\mathbf{Y}$ is a best approximation in every unitarily invariant norm. The truncated SVD is one
(`isBestRankApprox_truncatedSVD`); under ties $\sigma_{k-1} = \sigma_k$ there are others, and an
algorithm's $\mathbf{Q}\llbracket\mathbf{X}\rrbracket_k$ need not be `truncatedSVD (Q * X) k`.
[GolubVanLoan2013, Theorem 2.4.8]; [HalkoMartinssonTropp2011, §2.1]. -/
structure IsBestRankApprox (C : Matrix m n 𝕜) (k : ℕ) (Y : Matrix m n 𝕜) : Prop where
  rank_le : Y.rank ≤ k
  frobNorm_sub_le : ∀ B : Matrix m n 𝕜, B.rank ≤ k → frobNorm (C - Y) ≤ frobNorm (C - B)
/-- **Eckart–Young**: the truncated SVD is a best approximation of rank at most $k$. -/
theorem isBestRankApprox_truncatedSVD (C : Matrix m n 𝕜) (k : ℕ) :
    IsBestRankApprox C k (truncatedSVD C k)
/-- A matrix of rank at most $k$ is a best approximation as soon as it does as well as the truncated
SVD. -/
theorem isBestRankApprox_iff {C Y : Matrix m n 𝕜} {k : ℕ} :
    IsBestRankApprox C k Y ↔ Y.rank ≤ k ∧ frobNorm (C - Y) ≤ frobNorm (C - truncatedSVD C k)
/-- Bridge to Mathlib's minimizers. -/
theorem isBestRankApprox_iff_isMinOn {C Y : Matrix m n 𝕜} {k : ℕ} :
    IsBestRankApprox C k Y ↔
      Y.rank ≤ k ∧ IsMinOn (fun B : Matrix m n 𝕜 => frobNorm (C - B)) {B | B.rank ≤ k} Y
/-- **The error of a best approximation has the tail singular values**:
$\sigma_i(\mathbf{C} - \mathbf{Y}) = \sigma_{k+i}(\mathbf{C})$ for every $i$. -/
theorem IsBestRankApprox.singularValues_sub {C Y : Matrix m n 𝕜} {k : ℕ}
    (h : IsBestRankApprox C k Y) (i : ℕ) : singularValues (C - Y) i = singularValues C (k + i)
/-- A best approximation in the Frobenius norm is a best approximation in every unitarily invariant
norm: $\|\mathbf{C} - \mathbf{Y}\|_{\Phi} = \|\mathbf{C} - \llbracket\mathbf{C}\rrbracket_k\|_{\Phi}$. -/
theorem IsBestRankApprox.matrixNorm_sub {C Y : Matrix m n 𝕜} {k : ℕ}
    (h : IsBestRankApprox C k Y) (Φ : SymmetricGauge) :
    Φ.matrixNorm (C - Y) = Φ.matrixNorm (C - truncatedSVD C k)
theorem IsBestRankApprox.frobNorm_sub {C Y : Matrix m n 𝕜} {k : ℕ}
    (h : IsBestRankApprox C k Y) : frobNorm (C - Y) = frobNorm (C - truncatedSVD C k)
/-- A best approximation lies in the column space: $\mathbf{P}_{\mathbf{C}}\mathbf{Y} = \mathbf{Y}$. -/
theorem IsBestRankApprox.rangeProjector_mul {C Y : Matrix m n 𝕜} {k : ℕ}
    (h : IsBestRankApprox C k Y) : rangeProjector C * Y = Y
/-- Best approximations are preserved by an isometry on the left:
$\mathbf{Q}\mathbf{Y}$ is a best approximation of $\mathbf{Q}\mathbf{X}$ if and only if $\mathbf{Y}$
is one of $\mathbf{X}$. -/
theorem HasOrthonormalCols.isBestRankApprox_mul_iff {Q : Matrix m q 𝕜} (hQ : HasOrthonormalCols Q)
    {X Y : Matrix q n 𝕜} {k : ℕ} : IsBestRankApprox (Q * X) k (Q * Y) ↔ IsBestRankApprox X k Y
/-- **The factored form of a truncation** (D5): $\mathbf{Q}^{\mathsf{H}}\llbracket\mathbf{Q}\mathbf{X}
\rrbracket_k$ is a best approximation of $\mathbf{X}$ … -/
theorem HasOrthonormalCols.isBestRankApprox_conjTranspose_mul_truncatedSVD {Q : Matrix m q 𝕜}
    (hQ : HasOrthonormalCols Q) (X : Matrix q n 𝕜) (k : ℕ) :
    IsBestRankApprox X k (Qᴴ * truncatedSVD (Q * X) k)
/-- … and $\llbracket\mathbf{Q}\mathbf{X}\rrbracket_k = \mathbf{Q}(\mathbf{Q}^{\mathsf{H}}
\llbracket\mathbf{Q}\mathbf{X}\rrbracket_k)$. [TroppYurtseverUdellCevher2017, (6.3)]; there "there is
a best rank-$r$ approximation of $\mathbf{Q}\mathbf{X}$" with this property. -/
theorem HasOrthonormalCols.mul_conjTranspose_mul_truncatedSVD {Q : Matrix m q 𝕜}
    (hQ : HasOrthonormalCols Q) (X : Matrix q n 𝕜) (k : ℕ) :
    Q * (Qᴴ * truncatedSVD (Q * X) k) = truncatedSVD (Q * X) k
```

Proof routes. *B2:* `rank_truncatedSVD_le`, `frobNorm_sub_truncatedSVD_le_of_rank_le`. *B3:* (⇐) the
truncated SVD is no worse than any $\mathbf{B}$ (Eckart–Young). *B4:* unfold. *B5:* termwise
$\sigma_{k+i}(\mathbf{C}) \le \sigma_i(\mathbf{C}-\mathbf{Y})$
(`singularValues_add_le_singularValues_sub_of_rank_le`), and the sums of squares agree
($\|\mathbf{C}-\mathbf{Y}\|_{\mathsf{F}} = \|\mathbf{C}-\llbracket\mathbf{C}\rrbracket_k\|_{\mathsf{F}}$
by optimality both ways; `frobNorm_sq_eq_sum_range_singularValues_sq` on both errors and
`singularValues_sub_truncatedSVD`); `Finset.sum_eq_sum_iff_of_le` gives termwise equality of the
squares. This is the proof of `singularValues_sub_truncatedSVD` with a general $\mathbf{Y}$, and it
needs no private lemma. *B6:* `matrixNorm_le_of_singularValues_le` both ways, B5 and
`singularValues_sub_truncatedSVD`. *B7:* B6 at `lpGauge 2`, `lpGauge_two_matrixNorm`. *B8:* with
$\mathbf{P} = \mathbf{P}_{\mathbf{C}}$, $\|\mathbf{C}-\mathbf{Y}\|_{\mathsf{F}}^2 =
\|\mathbf{C}-\mathbf{P}\mathbf{Y}\|_{\mathsf{F}}^2 + \|(\mathbf{I}-\mathbf{P})\mathbf{Y}\|_{\mathsf{F}}^2$
(Pythagoras, $\mathbf{P}\mathbf{C} = \mathbf{C}$), and $\mathbf{P}\mathbf{Y}$ has rank at most $k$,
so optimality forces $(\mathbf{I}-\mathbf{P})\mathbf{Y} = \mathbf{0}$. *B9:* rank is unchanged by
$\mathbf{Q}$ (`Matrix.rank_mul_le_right` twice, $\mathbf{Q}^{\mathsf{H}}\mathbf{Q} = \mathbf{I}$),
Frobenius norm too (`hQ.frobNorm_mul_left`); (⇐) a competitor $\mathbf{B}$ of
$\mathbf{Q}\mathbf{X}$ is beaten by $\mathbf{Q}\mathbf{Q}^{\mathsf{H}}\mathbf{B}$ (Pythagoras), which
is $\mathbf{Q}$ times a competitor of $\mathbf{X}$. *B11:* $\operatorname{range}\llbracket
\mathbf{Q}\mathbf{X}\rrbracket_k \subseteq \operatorname{range}(\mathbf{Q}\mathbf{X}) \subseteq
\operatorname{range}\mathbf{Q}$ (`range_mulVecLin_truncatedSVD_le`), `hQ.rangeProjector_eq`,
`rangeProjector_mul_eq_self_iff`. *B10:* B2 at $\mathbf{Q}\mathbf{X}$, rewritten by B11, then B9.
Degenerate: B8 at $\mathbf{C} = \mathbf{0}$ forces $\mathbf{Y} = \mathbf{0}$, as it should; B9 to B11
at `q` empty are about zero matrices.

### 3.2 `Matrix/Spectral/BestRankApprox.lean`: truncating an approximation (5)

```lean
/-- **Domination passes to the tails**: if $\sigma_i(\hat{\mathbf{A}}) \le \sigma_i(\mathbf{A})$
for every $i$, then in every unitarily invariant norm
$\|\hat{\mathbf{A}} - \llbracket\hat{\mathbf{A}}\rrbracket_k\|_{\Phi} \le
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\Phi}$. -/
theorem SymmetricGauge.matrixNorm_sub_truncatedSVD_le_of_singularValues_le (Φ : SymmetricGauge)
    {A Â : Matrix m n 𝕜} (h : ∀ i, singularValues Â i ≤ singularValues A i) (k : ℕ) :
    Φ.matrixNorm (Â - truncatedSVD Â k) ≤ Φ.matrixNorm (A - truncatedSVD A k)
/-- **The truncation lemma, constant one.** If $\sigma_i(\hat{\mathbf{A}}) \le \sigma_i(\mathbf{A})$
for every $i$ and $\mathbf{Y}$ is a best rank-$k$ approximation of $\hat{\mathbf{A}}$, then in every
unitarily invariant norm
$$\|\mathbf{A} - \mathbf{Y}\|_{\Phi} \le \|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\Phi} +
\|\mathbf{A} - \hat{\mathbf{A}}\|_{\Phi}\,.$$
The hypothesis holds for $\hat{\mathbf{A}} = \mathbf{P}\mathbf{A}$ with $\mathbf{P}$ an orthogonal
projector (`IsStarProjection.singularValues_mul_le`) and for Nyström of a positive semidefinite
matrix. Result: truncation-lemma -/
theorem IsBestRankApprox.matrixNorm_sub_le_add_of_singularValues_le {A Â Y : Matrix m n 𝕜} {k : ℕ}
    (hY : IsBestRankApprox Â k Y) (h : ∀ i, singularValues Â i ≤ singularValues A i)
    (Φ : SymmetricGauge) :
    Φ.matrixNorm (A - Y) ≤ Φ.matrixNorm (A - truncatedSVD A k) + Φ.matrixNorm (A - Â)
/-- **The truncation lemma, constant two.** For any $\hat{\mathbf{A}}$ and any best rank-$k$
approximation $\mathbf{Y}$ of it, in every unitarily invariant norm
$$\|\mathbf{A} - \mathbf{Y}\|_{\Phi} \le \|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\Phi} +
2\|\mathbf{A} - \hat{\mathbf{A}}\|_{\Phi}\,.$$
Result: truncation-lemma -/
theorem IsBestRankApprox.matrixNorm_sub_le_add_two_mul {Â Y : Matrix m n 𝕜} {k : ℕ}
    (hY : IsBestRankApprox Â k Y) (Φ : SymmetricGauge) (A : Matrix m n 𝕜) :
    Φ.matrixNorm (A - Y) ≤ Φ.matrixNorm (A - truncatedSVD A k) + 2 * Φ.matrixNorm (A - Â)
/-- **Reverse Eckart–Young, Frobenius form.** For $\mathbf{B}$ of rank at most $k$, the spectral
error exceeds the optimal one by at most the Frobenius excess:
$$\|\mathbf{A} - \mathbf{B}\|_2^2 + \|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2
\le \sigma_k(\mathbf{A})^2 + \|\mathbf{A} - \mathbf{B}\|_{\mathsf{F}}^2\,.$$
Result: reverse-eckart-young -/
theorem specNorm_sub_sq_add_frobNorm_sub_truncatedSVD_sq_le_of_rank_le (A : Matrix m n 𝕜)
    {B : Matrix m n 𝕜} {k : ℕ} (hB : B.rank ≤ k) :
    specNorm (A - B) ^ 2 + frobNorm (A - truncatedSVD A k) ^ 2 ≤
      singularValues A k ^ 2 + frobNorm (A - B) ^ 2
/-- **Reverse Eckart–Young, nuclear form.** For $\mathbf{B}$ of rank at most $k$,
$$\|\mathbf{A} - \mathbf{B}\|_2 + \|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_*
\le \sigma_k(\mathbf{A}) + \|\mathbf{A} - \mathbf{B}\|_*\,.$$
Result: reverse-eckart-young -/
theorem specNorm_sub_add_nuclearNorm_sub_truncatedSVD_le_of_rank_le (A : Matrix m n 𝕜)
    {B : Matrix m n 𝕜} {k : ℕ} (hB : B.rank ≤ k) :
    specNorm (A - B) + nuclearNorm (A - truncatedSVD A k) ≤
      singularValues A k + nuclearNorm (A - B)
```

Proof routes. *B12:* `matrixNorm_le_of_singularValues_le` with `singularValues_sub_truncatedSVD` on
both sides: $\sigma_i(\hat{\mathbf{A}}-\llbracket\hat{\mathbf{A}}\rrbracket_k) =
\sigma_{k+i}(\hat{\mathbf{A}}) \le \sigma_{k+i}(\mathbf{A})$. *B13:* $\mathbf{A}-\mathbf{Y} =
(\mathbf{A}-\hat{\mathbf{A}}) + (\hat{\mathbf{A}}-\mathbf{Y})$, `matrixNorm_add_le`, B6, B12. HMT's
proof (Theorem 9.3) uses $\mathbf{P}\llbracket\mathbf{A}\rrbracket_k$ as a competitor and the
contraction of $\mathbf{P}$; domination is the same fact for every gauge and covers Nyström. *B14:*
triangle inequality, B6, then Eckart–Young for $\hat{\mathbf{A}}$ against the competitor
$\llbracket\mathbf{A}\rrbracket_k$ (`matrixNorm_sub_truncatedSVD_le_of_rank_le`), then the triangle
inequality again; TYUC's proof. *B15, B16:* $\sigma_{k+i}(\mathbf{A}) \le \sigma_i(\mathbf{A}-\mathbf{B})$
for $i \ge 1$ (`singularValues_add_le_singularValues_sub_of_rank_le`), keep the $i = 0$ term
($\sigma_0 = \|\cdot\|_2$), sum squares (`frobNorm_sq_eq_sum_range_singularValues_sq`) or values
(`nuclearNorm_eq_sum_range`), and recognise $\sum_{i \ge 1}\sigma_{k+i}(\mathbf{A})^2 =
\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2 - \sigma_k(\mathbf{A})^2$
(`singularValues_sub_truncatedSVD`). Degenerate: B13, B14 at $k = 0$: triangle inequality; B15, B16
at $k = 0$, $\mathbf{B} = \mathbf{0}$: equality; at $k \ge \operatorname{rank}\mathbf{A}$:
$\sigma_k = 0$ and the statements are $\|\cdot\|_2 \le \|\cdot\|_{\mathsf{F}}$,
$\|\cdot\|_2 \le \|\cdot\|_*$; both sides of B15, B16 are choice-free. Necessity of the domination
in B13: §3 list.

Why the reverse forms are subtraction-free: the additive shape composes with `add_le_add` and
integrates without an integrability side condition on a difference; S5 reads off
$\mathbb{E}\|\mathbf{H}-\llbracket\hat{\mathbf{H}}\rrbracket_k\|_2 \le \lambda_k(\mathbf{H}) +
\mathbb{E}\|\mathbf{H}-\llbracket\hat{\mathbf{H}}\rrbracket_k\|_* - \|\mathbf{H}-
\llbracket\mathbf{H}\rrbracket_k\|_*$ by `linarith` after integrating.

### 3.3 `Matrix/Spectral/BestRankApprox.lean`: perturbed truncation, Gram matrices, PSD order (5)

```lean
/-- The Frobenius inner product with a matrix of rank at most $r$ only sees the $r$ leading singular
values: if $\operatorname{rank}\mathbf{X} \le r$ then
$\langle\mathbf{X}, \mathbf{E}\rangle_{\mathsf{F}} \le \|\mathbf{X}\|_{\mathsf{F}}
\|\llbracket\mathbf{E}\rrbracket_r\|_{\mathsf{F}}$, and
$\|\llbracket\mathbf{E}\rrbracket_r\|_{\mathsf{F}} \le \sqrt{r}\,\|\mathbf{E}\|_2$ recovers
`NLAlib.frobInner_le_sqrt_mul_frobNorm_mul_specNorm_of_rank_le`.
[HornJohnson2013, Theorem 7.4.1.1]; von Neumann's trace inequality and Cauchy–Schwarz. -/
theorem frobInner_le_frobNorm_mul_frobNorm_truncatedSVD_of_rank_le {X : Matrix m n 𝕜} {r : ℕ}
    (hX : X.rank ≤ r) (E : Matrix m n 𝕜) :
    frobInner X E ≤ frobNorm X * frobNorm (truncatedSVD E r)
/-- **Perturbed truncation.** For any $\mathbf{C}$, $\mathbf{E}$ and any best rank-$k$ approximation
$\mathbf{Y}$ of $\mathbf{C} + \mathbf{E}$,
$$\|\mathbf{C} - \mathbf{Y}\|_{\mathsf{F}} \le \|\mathbf{C} - \llbracket\mathbf{C}\rrbracket_k\|_{\mathsf{F}}
+ 2\,\|\llbracket\mathbf{E}\rrbracket_{2k}\|_{\mathsf{F}}\,:$$
truncating a perturbed matrix pays only the $2k$ leading singular values of the perturbation. It
dominates the constant-two lemma in the Frobenius norm
($\|\llbracket\mathbf{E}\rrbracket_{2k}\|_{\mathsf{F}} \le \|\mathbf{E}\|_{\mathsf{F}}$).
Proved without a literature source; the input is von Neumann's trace inequality
[HornJohnson2013, Theorem 7.4.1.1]. Related: [TroppYurtseverUdellCevher2017, Proposition 6.1].
Result: perturbed-truncation -/
theorem IsBestRankApprox.frobNorm_sub_le_add_frobNorm_truncatedSVD {C E Y : Matrix m n 𝕜} {k : ℕ}
    (hY : IsBestRankApprox (C + E) k Y) :
    frobNorm (C - Y) ≤ frobNorm (C - truncatedSVD C k) + 2 * frobNorm (truncatedSVD E (2 * k))
/-- **Perturbed truncation, spectral form**:
$$\|\mathbf{C} - \mathbf{Y}\|_{\mathsf{F}} \le \|\mathbf{C} - \llbracket\mathbf{C}\rrbracket_k\|_{\mathsf{F}}
+ 2\sqrt{2k}\,\|\mathbf{E}\|_2\,.$$
Better than the constant-two lemma when $\mathbf{E}$ has stable rank above $2k$, the case of the
core noise of sketched regression. Proved without a literature source. Result: perturbed-truncation -/
theorem IsBestRankApprox.frobNorm_sub_le_add_specNorm {C E Y : Matrix m n 𝕜} {k : ℕ}
    (hY : IsBestRankApprox (C + E) k Y) :
    frobNorm (C - Y) ≤ frobNorm (C - truncatedSVD C k) + 2 * √(2 * (k : ℝ)) * specNorm E
/-- **Truncation commutes with the Gram map in trace**: the nuclear error of truncating
$\mathbf{G}^{\mathsf{H}}\mathbf{G}$ is the squared Frobenius error of truncating $\mathbf{G}$,
$$\|\mathbf{G}^{\mathsf{H}}\mathbf{G} - \llbracket\mathbf{G}^{\mathsf{H}}\mathbf{G}\rrbracket_k\|_*
= \|\mathbf{G} - \llbracket\mathbf{G}\rrbracket_k\|_{\mathsf{F}}^2\,,$$
for every choice of either truncation. -/
theorem nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD (G : Matrix m n 𝕜) (k : ℕ) :
    nuclearNorm (Gᴴ * G - truncatedSVD (Gᴴ * G) k) = frobNorm (G - truncatedSVD G k) ^ 2
/-- The truncated SVD of a positive semidefinite matrix lies below it:
$\llbracket\mathbf{A}\rrbracket_k \preceq \mathbf{A}$. -/
theorem _root_.Matrix.PosSemidef.truncatedSVD_le {A : Matrix n n 𝕜} (hA : A.PosSemidef) (k : ℕ) :
    truncatedSVD A k ≤ A
```

Proof routes. *B17:* `abs_frobInner_le_sum_singularValues_mul`; $\sigma_i(\mathbf{X}) = 0$ for
$i \ge r$ (`singularValues_eq_zero_iff`); Cauchy–Schwarz on the first $r$ terms
(`Finset.inner_mul_le_norm_mul_norm`); $\sum_i\sigma_i(\mathbf{X})^2 = \|\mathbf{X}\|_{\mathsf{F}}^2$
and $\sum_{i<r}\sigma_i(\mathbf{E})^2 = \|\llbracket\mathbf{E}\rrbracket_r\|_{\mathsf{F}}^2$
(`singularValues_truncatedSVD`, `frobNorm_sq_eq_sum_range_singularValues_sq`). It is the
formalization's `RankTraceBound` step, sharpened by stopping before $\sigma_i(\mathbf{E}) \le
\|\mathbf{E}\|_2$. *B18:* the formalization's proof (`frobNorm_sub_bestRankApprox_perturb`): with
$\mathbf{Y}_0 = \llbracket\mathbf{C}\rrbracket_k$, $\Delta = \|\mathbf{C}-\mathbf{Y}_0\|_{\mathsf{F}}$,
$x = \|\mathbf{C}-\mathbf{Y}\|_{\mathsf{F}}$: optimality of $\mathbf{Y}$ against $\mathbf{Y}_0$
(`hY.frobNorm_sub_le`) and two expansions (`frobNorm_add_sq`, `frobNorm_sub_sq`) give
$x^2 \le \Delta^2 + 2\langle\mathbf{Y}-\mathbf{Y}_0, \mathbf{E}\rangle_{\mathsf{F}}$; B17 at
$r = 2k$ (`Matrix.rank_sub_le`, `rank_truncatedSVD_le`) and the triangle inequality give
$x^2 \le \Delta^2 + 2\beta(x+\Delta)$ with $\beta = \|\llbracket\mathbf{E}\rrbracket_{2k}\|_{\mathsf{F}}$;
the right root ($(x+\Delta)(x-\Delta-2\beta) \le 0$, `nlinarith`). *B19:* B18 and
$\|\llbracket\mathbf{E}\rrbracket_{2k}\|_{\mathsf{F}} \le \sqrt{2k}\,\|\mathbf{E}\|_2$
(`frobNorm_le_sqrt_rank_mul_specNorm` at $\llbracket\mathbf{E}\rrbracket_{2k}$, whose rank is at most
$2k$ and spectral norm at most $\|\mathbf{E}\|_2$ by `singularValues_truncatedSVD`). *B20:* both sides
are $\sum_i\sigma_{k+i}(\mathbf{G})^2$: `nuclearNorm_eq_sum_range`, `singularValues_sub_truncatedSVD`,
`singularValues_conjTranspose_mul_self`, `frobNorm_sub_truncatedSVD_sq`; the two index ranges differ
($\lvert n\rvert$ against $\min(\lvert m\rvert,\lvert n\rvert)$) and the padding absorbs it. *B21:* if
$k \le \lvert n\rvert$, L2 gives a frame $\mathbf{Z}$ with $\mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}}
= \llbracket\mathbf{A}\rrbracket_k$, L5b gives $\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k =
(\mathbf{I}-\mathbf{Z}\mathbf{Z}^{\mathsf{H}})\mathbf{A}(\mathbf{I}-\mathbf{Z}\mathbf{Z}^{\mathsf{H}})$,
a congruence of a PSD matrix (`Matrix.PosSemidef.conjTranspose_mul_mul_same`); otherwise
$\llbracket\mathbf{A}\rrbracket_k = \mathbf{A}$ (`truncatedSVD_of_rank_le`). Public API only.
Degenerate: B18 at $k = 0$: $\mathbf{Y} = \mathbf{0}$ and equality; at $\mathbf{C} = \mathbf{0}$ it
reads $\|\mathbf{Y}\|_{\mathsf{F}} \le 2\|\llbracket\mathbf{E}\rrbracket_{2k}\|_{\mathsf{F}}$, true
(a best $\mathbf{Y}$ of $\mathbf{E}$ has $\|\mathbf{Y}\|_{\mathsf{F}} = \|\llbracket\mathbf{E}
\rrbracket_k\|_{\mathsf{F}}$); at $k \ge \operatorname{rank}(\mathbf{C}+\mathbf{E})$: $\mathbf{Y} =
\mathbf{C}+\mathbf{E}$ by B7, and the bound reads $\|\mathbf{E}\|_{\mathsf{F}} \le
\|\mathbf{C}-\llbracket\mathbf{C}\rrbracket_k\|_{\mathsf{F}} + 2\|\llbracket\mathbf{E}\rrbracket_{2k}
\|_{\mathsf{F}}$; B20 at $k \ge$ rank: $0 = 0$; B21 at $k = 0$: $\mathbf{0} \preceq \mathbf{A}$.

### 3.4 `Matrix/Factorizations/NystromOrder.lean` (1)

```lean
/-- **Nyström does not increase any singular value**: for positive semidefinite $\mathbf{H}$,
$\sigma_i(\mathbf{H}\langle\mathbf{\Omega}\rangle) \le \sigma_i(\mathbf{H})$ for every $i$, since
$\mathbf{0} \preceq \mathbf{H}\langle\mathbf{\Omega}\rangle \preceq \mathbf{H}$. False for Hermitian
$\mathbf{H}$ that is not positive semidefinite. -/
theorem _root_.Matrix.PosSemidef.singularValues_nystrom_le {H : Matrix n n 𝕜} (hH : H.PosSemidef)
    (Ω : Matrix n l 𝕜) (i : ℕ) : singularValues (nystrom H Ω) i ≤ singularValues H i
```

Proof: `Matrix.PosSemidef.singularValues_eq_eigenvalue` at `hH.nystrom Ω` and `hH`, then
`eigenvalue_le_eigenvalue_of_le (hH.nystrom_le Ω)`. Placed after
`Matrix.PosSemidef.singularValues_sub_nystrom_le`, written proved (the file is registered).

### 3.5 `LowRank/Structural/Truncation.lean`: truncated RSVD (6)

```lean
/-- **The truncated randomized SVD in every unitarily invariant norm**:
$$\|\mathbf{A} - \llbracket\mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A}\rrbracket_k\|_{\Phi} \le
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\Phi} +
\|\mathbf{A} - \mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A}\|_{\Phi}\,.$$
In the spectral norm this is HMT Theorem 9.3. Result: truncation-lemma -/
theorem SymmetricGauge.matrixNorm_sub_truncatedSVD_rsvd_le (Φ : SymmetricGauge) (A : Matrix m n 𝕜)
    (Ω : Matrix n l 𝕜) (k : ℕ) :
    Φ.matrixNorm (A - truncatedSVD (rsvd A Ω) k) ≤
      Φ.matrixNorm (A - truncatedSVD A k) + Φ.matrixNorm (A - rsvd A Ω)
/-- The optimal error of the projected matrix is at most that of the matrix:
$\|\mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A} - \llbracket\mathbf{P}_{\mathbf{A}\mathbf{\Omega}}
\mathbf{A}\rrbracket_k\|_{\mathsf{F}} \le \|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}$. -/
theorem frobNorm_rsvd_sub_truncatedSVD_le (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) (k : ℕ) :
    frobNorm (rsvd A Ω - truncatedSVD (rsvd A Ω) k) ≤ frobNorm (A - truncatedSVD A k)
/-- **The truncated randomized SVD error splits exactly**:
$$\|\mathbf{A} - \llbracket\mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2
= \|\mathbf{A} - \mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A}\|_{\mathsf{F}}^2 +
\|\mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A} - \llbracket\mathbf{P}_{\mathbf{A}\mathbf{\Omega}}
\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,,$$
for every choice of the truncation. -/
theorem frobNorm_sub_truncatedSVD_rsvd_sq (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) (k : ℕ) :
    frobNorm (A - truncatedSVD (rsvd A Ω) k) ^ 2 =
      frobNorm (A - rsvd A Ω) ^ 2 + frobNorm (rsvd A Ω - truncatedSVD (rsvd A Ω) k) ^ 2
/-- **The truncation lemma, Frobenius-squared form**:
$$\|\mathbf{A} - \llbracket\mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2
\le \|\mathbf{A} - \mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A}\|_{\mathsf{F}}^2 +
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,,$$
sharper than squaring the gauge form. Result: truncation-lemma -/
theorem frobNorm_sub_truncatedSVD_rsvd_sq_le_frobNorm_sub_rsvd_sq_add (A : Matrix m n 𝕜)
    (Ω : Matrix n l 𝕜) (k : ℕ) :
    frobNorm (A - truncatedSVD (rsvd A Ω) k) ^ 2 ≤
      frobNorm (A - rsvd A Ω) ^ 2 + frobNorm (A - truncatedSVD A k) ^ 2
/-- **The truncated randomized SVD through a basis**: for any $\mathbf{Q}$ with orthonormal columns
spanning $\operatorname{range}(\mathbf{A}\mathbf{\Omega})$, the algorithm's
$\mathbf{Q}\llbracket\mathbf{Q}^{\mathsf{H}}\mathbf{A}\rrbracket_k$ has the Frobenius error of
$\llbracket\mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A}\rrbracket_k$, whatever the two
truncations choose. -/
theorem HasOrthonormalCols.frobNorm_sub_truncatedSVD_rsvd {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜}
    {Q : Matrix m q 𝕜} (hQ : HasOrthonormalCols Q)
    (hQY : LinearMap.range Q.mulVecLin = LinearMap.range (A * Ω).mulVecLin) (k : ℕ) :
    frobNorm (A - truncatedSVD (rsvd A Ω) k) = frobNorm (A - Q * truncatedSVD (Qᴴ * A) k)
/-- **Gu's projected form**: with $\mathbf{T} = \llbracket\mathbf{A}\rrbracket_k$,
$$\|\mathbf{A} - \llbracket\mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2
\le \|\mathbf{A} - \mathbf{T}\|_{\mathsf{F}}^2 + \|\mathbf{T} - \mathbf{P}_{\mathbf{A}\mathbf{\Omega}}
\mathbf{T}\|_{\mathsf{F}}^2\,,$$
for every test matrix (no rank hypothesis). Under S1's hypothesis the last term is at most
$\|\mathbf{M}\|_{\mathsf{F}}^2$, so this is at least as sharp as truncation for free. -/
theorem frobNorm_sub_truncatedSVD_rsvd_sq_le_frobNorm_sub_truncatedSVD_sq_add (A : Matrix m n 𝕜)
    (Ω : Matrix n l 𝕜) (k : ℕ) :
    frobNorm (A - truncatedSVD (rsvd A Ω) k) ^ 2 ≤
      frobNorm (A - truncatedSVD A k) ^ 2 +
        frobNorm (truncatedSVD A k - rangeProjector (A * Ω) * truncatedSVD A k) ^ 2
```

Proof routes. Throughout $\mathbf{P} = \mathbf{P}_{\mathbf{A}\mathbf{\Omega}}$, `rsvd A Ω = P * A`
(definition). *T1:* B13 at $\hat{\mathbf{A}} = \mathbf{P}\mathbf{A}$, B2, and
`IsStarProjection.singularValues_mul_le`. *T12:* B12 at `lpGauge 2` with the same domination.
*T3:* $\mathbf{P}\llbracket\mathbf{P}\mathbf{A}\rrbracket_k = \llbracket\mathbf{P}\mathbf{A}\rrbracket_k$
(B8 at $\mathbf{C} = \mathbf{P}\mathbf{A}$, then `range_rsvd_le`), so $\mathbf{A} -
\llbracket\mathbf{P}\mathbf{A}\rrbracket_k = (\mathbf{A}-\mathbf{P}\mathbf{A}) + \mathbf{P}(\mathbf{P}\mathbf{A}
- \llbracket\mathbf{P}\mathbf{A}\rrbracket_k)$ with orthogonal terms
(`frobNorm_add_sq_of_frobInner_eq_zero`); the proof holds for any best approximation of
$\mathbf{P}\mathbf{A}$ (B7, B8), which T5 uses. *T4:* T3 and T12. *T5:* $\mathbf{P} =
\mathbf{Q}\mathbf{Q}^{\mathsf{H}}$ (`hQ.rangeProjector_eq`, `rangeProjector_inj` with `hQY`); by B9 and
B2, $\mathbf{Q}\llbracket\mathbf{Q}^{\mathsf{H}}\mathbf{A}\rrbracket_k$ is a best approximation of
$\mathbf{Q}(\mathbf{Q}^{\mathsf{H}}\mathbf{A}) = \mathbf{P}\mathbf{A}$; the hypothesis form of T3
gives both sides the same value. *T6:* by S1's L1, $(\mathbf{A}-\mathbf{T})\mathbf{T}^{\mathsf{H}} =
\mathbf{0}$ ($\mathbf{A}\mathbf{P}_{\mathbf{T}^{\mathsf{H}}} = \mathbf{T}$); T3 and
$\|\mathbf{P}\mathbf{A}-\llbracket\mathbf{P}\mathbf{A}\rrbracket_k\|_{\mathsf{F}} \le
\|\mathbf{P}\mathbf{A}-\mathbf{P}\mathbf{T}\|_{\mathsf{F}}$ (Eckart–Young, $\operatorname{rank}
\mathbf{P}\mathbf{T} \le k$) give $\|\mathbf{A}-\llbracket\mathbf{P}\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2
\le \|\mathbf{A}-\mathbf{P}\mathbf{T}\|_{\mathsf{F}}^2$ (Pythagoras back), and
$\mathbf{A}-\mathbf{P}\mathbf{T} = (\mathbf{A}-\mathbf{T}) + (\mathbf{T}-\mathbf{P}\mathbf{T})$ has
cross term $\operatorname{Re}\operatorname{tr}((\mathbf{I}-\mathbf{P})\mathbf{T}(\mathbf{A}-\mathbf{T})^{\mathsf{H}})
= 0$. Degenerate: $\mathbf{\Omega} = \mathbf{0}$ (`rsvd = 0`): T3 reads $\|\mathbf{A}\|^2 =
\|\mathbf{A}\|^2 + 0$, T6 reads $\|\mathbf{A}\|^2 \le \|\mathbf{A}-\mathbf{T}\|^2 +
\|\mathbf{T}\|^2$, an equality (`frobNorm_sq_eq_truncatedSVD_add`); $k = 0$: T1 to T6 reduce to
identities or to $\|\mathbf{A}\| \le \|\mathbf{A}\| + \|\cdot\|$; `q` empty in T5 forces
$\mathbf{A}\mathbf{\Omega} = \mathbf{0}$, both sides $\|\mathbf{A}\|_{\mathsf{F}}$.

### 3.6 `LowRank/Structural/Truncation.lean`: truncated Nyström (4)

```lean
/-- **Truncated Nyström in every unitarily invariant norm**: for positive semidefinite $\mathbf{H}$,
$$\|\mathbf{H} - \llbracket\mathbf{H}\langle\mathbf{\Omega}\rangle\rrbracket_k\|_{\Phi} \le
\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_{\Phi} +
\|\mathbf{H} - \mathbf{H}\langle\mathbf{\Omega}\rangle\|_{\Phi}\,.$$
Result: truncation-lemma -/
theorem SymmetricGauge.matrixNorm_sub_truncatedSVD_nystrom_le (Φ : SymmetricGauge)
    {H : Matrix n n 𝕜} (hH : H.PosSemidef) (Ω : Matrix n l 𝕜) (k : ℕ) :
    Φ.matrixNorm (H - truncatedSVD (nystrom H Ω) k) ≤
      Φ.matrixNorm (H - truncatedSVD H k) + Φ.matrixNorm (H - nystrom H Ω)
/-- **Truncation under the Gram correspondence**: the trace error of truncated Nyström of
$\mathbf{F}^{\mathsf{H}}\mathbf{F}$ is the squared Frobenius error of the truncated randomized SVD of
$\mathbf{F}$,
$$\|\mathbf{F}^{\mathsf{H}}\mathbf{F} - \llbracket(\mathbf{F}^{\mathsf{H}}\mathbf{F})\langle\mathbf{\Omega}
\rangle\rrbracket_k\|_* = \|\mathbf{F} - \llbracket\mathbf{P}_{\mathbf{F}\mathbf{\Omega}}\mathbf{F}
\rrbracket_k\|_{\mathsf{F}}^2\,,$$
for every factor, test matrix, rank and choice of truncation.
Result: truncated-gram-correspondence -/
theorem nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD_nystrom (F : Matrix m n 𝕜)
    (Ω : Matrix n l 𝕜) (k : ℕ) :
    nuclearNorm (Fᴴ * F - truncatedSVD (nystrom (Fᴴ * F) Ω) k) =
      frobNorm (F - truncatedSVD (rsvd F Ω) k) ^ 2
/-- The same for positive semidefinite $\mathbf{H}$, with $\mathbf{F} = \mathbf{H}^{1/2}$.
Result: truncated-gram-correspondence -/
theorem _root_.Matrix.PosSemidef.nuclearNorm_sub_truncatedSVD_nystrom {H : Matrix n n 𝕜}
    (hH : H.PosSemidef) (Ω : Matrix n l 𝕜) (k : ℕ) :
    nuclearNorm (H - truncatedSVD (nystrom H Ω) k) =
      frobNorm (CFC.sqrt H - truncatedSVD (rsvd (CFC.sqrt H) Ω) k) ^ 2
/-- **Truncated Nyström stays below the matrix**: for positive semidefinite $\mathbf{H}$,
$\llbracket\mathbf{H}\langle\mathbf{\Omega}\rangle\rrbracket_k \preceq \mathbf{H}$, so the trace of
the error is its nuclear norm. -/
theorem _root_.Matrix.PosSemidef.truncatedSVD_nystrom_le {H : Matrix n n 𝕜} (hH : H.PosSemidef)
    (Ω : Matrix n l 𝕜) (k : ℕ) : truncatedSVD (nystrom H Ω) k ≤ H
```

Proof routes. *T2:* B13 at $\hat{\mathbf{H}} = \mathbf{H}\langle\mathbf{\Omega}\rangle$, B2, N1. *T7:*
with $\mathbf{G} = $ `rsvd F Ω`, $\hat{\mathbf{H}} = \mathbf{G}^{\mathsf{H}}\mathbf{G}$
(`nystrom_conjTranspose_mul_self`); $\mathbf{F}^{\mathsf{H}}\mathbf{F} - \llbracket\hat{\mathbf{H}}
\rrbracket_k = (\mathbf{F}^{\mathsf{H}}\mathbf{F} - \hat{\mathbf{H}}) + (\hat{\mathbf{H}} -
\llbracket\hat{\mathbf{H}}\rrbracket_k)$, both PSD (`conjTranspose_mul_self_sub_nystrom`; B21 at
$\hat{\mathbf{H}}$), so the nuclear norm is additive (`Matrix.PosSemidef.nuclearNorm_eq_re_trace`
three times, `Matrix.trace_add`); the first term is $\|\mathbf{F}-\mathbf{G}\|_{\mathsf{F}}^2$
(`nuclearNorm_conjTranspose_mul_self_sub_nystrom`), the second
$\|\mathbf{G}-\llbracket\mathbf{G}\rrbracket_k\|_{\mathsf{F}}^2$ (B20), and T3 adds them. *T8:* T7 at
$\mathbf{F} = \mathbf{H}^{1/2}$, with $\mathbf{H} = (\mathbf{H}^{1/2})^{\mathsf{H}}\mathbf{H}^{1/2}$
(`CFC.sqrt_mul_sqrt_self`, Hermitian square root; S0's private `eq_conjTranspose_sqrt_mul_sqrt` is
reproved in two lines or made public at S0's wrap-up). *T9:* B21 at `hH.nystrom Ω`, then
`hH.nystrom_le Ω`. Degenerate: §3 list (non-PSD); $\mathbf{\Omega} = \mathbf{0}$: Nyström is
$\mathbf{0}$, T7 reads $\|\mathbf{F}\|_{\mathsf{F}}^2 = \|\mathbf{F}\|_{\mathsf{F}}^2$; $k = 0$: T7 is S0's
trace correspondence.

S5's two truncated Nyström bounds from these, for the record (not S2a statements): trace,
$\mathbb{E}\|\mathbf{H}-\llbracket\hat{\mathbf{H}}\rrbracket_k\|_* \le (1+\frac{k}{\ell-k-1})
\|\mathbf{H}-\llbracket\mathbf{H}\rrbracket_k\|_*$ by T8, T5 and S1's truncation for free at
$\mathbf{F} = \mathbf{H}^{1/2}$; spectral (MT Theorem 14.1), B16 at $\mathbf{A} = \mathbf{H}$,
$\mathbf{B} = \llbracket\hat{\mathbf{H}}\rrbracket_k$, then the trace bound: $\mathbb{E}\|\mathbf{H}-
\llbracket\hat{\mathbf{H}}\rrbracket_k\|_2 \le \lambda_{k+1} + \frac{k}{\ell-k-1}\sum_{j>k}\lambda_j$
(prose indexing from $1$). This is TYUC NeurIPS's proof, with Gu's Theorem 3.5 replaced by S1's
competitor.

### 3.7 `LowRank/Structural/Truncation.lean`: truncated generalized Nyström (2)

```lean
/-- **The truncated generalized Nyström error, deterministic form.** When
$\operatorname{rank}(\mathbf{\Psi}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega}) =
\operatorname{rank}(\mathbf{A}\mathbf{\Omega})$, with $\mathbf{P} = \mathbf{P}_{\mathbf{A}\mathbf{\Omega}}$
and the core noise $\mathbf{N} = \mathbf{\Pi}_{\mathbf{A}\mathbf{\Omega},\mathbf{\Psi}^{\mathsf{H}}}
(\mathbf{A} - \mathbf{P}\mathbf{A})$,
$$\|\mathbf{A} - \llbracket\mathbf{A}\langle\mathbf{\Omega},\mathbf{\Psi}\rangle\rrbracket_k\|_{\mathsf{F}}^2
\le \|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{\mathsf{F}}^2 + \bigl(\|\mathbf{P}\mathbf{A} -
\llbracket\mathbf{P}\mathbf{A}\rrbracket_k\|_{\mathsf{F}} + 2\,\|\llbracket\mathbf{N}\rrbracket_{2k}
\|_{\mathsf{F}}\bigr)^2\,.$$
Proved without a literature source. Result: perturbed-truncation -/
theorem frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_frobNorm_truncatedSVD
    {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜} {Ψ : Matrix m p 𝕜}
    (h : (Ψᴴ * (A * Ω)).rank = (A * Ω).rank) (k : ℕ) :
    frobNorm (A - truncatedSVD (generalizedNystrom A Ω Ψ) k) ^ 2 ≤
      frobNorm (A - rsvd A Ω) ^ 2 +
        (frobNorm (rsvd A Ω - truncatedSVD (rsvd A Ω) k) +
          2 * frobNorm (truncatedSVD (obliqueProjector (A * Ω) Ψᴴ * (A - rsvd A Ω)) (2 * k))) ^ 2
/-- Spectral form: the last term is $2\sqrt{2k}\,\|\mathbf{N}\|_2$. This is the shape truncated GN
in expectation consumes (S6): $\mathbb{E}\|\mathbf{N}\|_2^2$ is the spectral core noise.
Proved without a literature source. Result: perturbed-truncation -/
theorem frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_specNorm
    {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜} {Ψ : Matrix m p 𝕜}
    (h : (Ψᴴ * (A * Ω)).rank = (A * Ω).rank) (k : ℕ) :
    frobNorm (A - truncatedSVD (generalizedNystrom A Ω Ψ) k) ^ 2 ≤
      frobNorm (A - rsvd A Ω) ^ 2 +
        (frobNorm (rsvd A Ω - truncatedSVD (rsvd A Ω) k) +
          2 * √(2 * (k : ℝ)) * specNorm (obliqueProjector (A * Ω) Ψᴴ * (A - rsvd A Ω))) ^ 2
```

Proof route (T10; T11 is the same with B19). Take $\mathbf{Q}$ with orthonormal columns and
$\operatorname{range}\mathbf{Q} = \operatorname{range}(\mathbf{A}\mathbf{\Omega})$
(`exists_hasOrthonormalCols_range_eq`, indexed by `Fin (A * Ω).rank`, proof-internal). The rank
hypothesis transfers to $\mathbf{Q}$ (`rank_mul_eq_iff_injOn`: it is injectivity of
$\mathbf{\Psi}^{\mathsf{H}}$ on the common range). Then:
1. $\mathbf{A}\langle\mathbf{\Omega},\mathbf{\Psi}\rangle = \mathbf{Q}\hat{\mathbf{X}}$ with
   $\hat{\mathbf{X}} = $ `sketchAndSolve Q Ψᴴ A` (`generalizedNystrom_eq_mul_sketchAndSolve`), and
   $\hat{\mathbf{X}} = \mathbf{Q}^{\mathsf{H}}\mathbf{A} + \mathbf{N}_0$ with $\mathbf{N}_0 = $
   `sketchAndSolve Q Ψᴴ ((1 - Q * Qᴴ) * A)` (`HasOrthonormalCols.sketchAndSolve_eq_add`);
2. $\llbracket\mathbf{Q}\hat{\mathbf{X}}\rrbracket_k = \mathbf{Q}\mathbf{Y}$ with $\mathbf{Y}$ a best
   approximation of $\hat{\mathbf{X}}$ (B10, B11);
3. core split `HasOrthonormalCols.frobNorm_sub_mul_sq`: $\|\mathbf{A}-\mathbf{Q}\mathbf{Y}\|_{\mathsf{F}}^2
   = \|(\mathbf{I}-\mathbf{Q}\mathbf{Q}^{\mathsf{H}})\mathbf{A}\|_{\mathsf{F}}^2 +
   \|\mathbf{Q}^{\mathsf{H}}\mathbf{A}-\mathbf{Y}\|_{\mathsf{F}}^2$, the first term `A - rsvd A Ω`
   (`sub_rsvd`);
4. B18 at $\mathbf{C} = \mathbf{Q}^{\mathsf{H}}\mathbf{A}$, $\mathbf{E} = \mathbf{N}_0$;
5. back to basis-free terms: $\|\mathbf{Q}^{\mathsf{H}}\mathbf{A}-\llbracket\mathbf{Q}^{\mathsf{H}}
   \mathbf{A}\rrbracket_k\|_{\mathsf{F}} = \|\mathbf{P}\mathbf{A}-\llbracket\mathbf{P}\mathbf{A}
   \rrbracket_k\|_{\mathsf{F}}$ (B9 and B7) and $\|\llbracket\mathbf{N}_0\rrbracket_{2k}\|_{\mathsf{F}}
   = \|\llbracket\mathbf{Q}\mathbf{N}_0\rrbracket_{2k}\|_{\mathsf{F}}$ (`singularValues_truncatedSVD`,
   `HasOrthonormalCols.singularValues_mul_left`), with $\mathbf{Q}\mathbf{N}_0 =
   \mathbf{\Pi}_{\mathbf{Q},\mathbf{\Psi}^{\mathsf{H}}}(\mathbf{I}-\mathbf{Q}\mathbf{Q}^{\mathsf{H}})
   \mathbf{A} = \mathbf{N}$ (`mul_sketchAndSolve`, `obliqueProjector_eq_of_range_eq`).

S6 then expands $(\gamma + 2\sqrt{2k}\,e)^2 = \gamma^2 + 4\sqrt{2k}\,\gamma e + 8ke^2$ with
$\gamma \le \mathrm{OPT}$ from T12, and uses $\|\mathbf{N}\|_2 = \|\mathbf{N}_0\|_2$ in its fixed-basis
core-noise lemma. Degenerate: rank hypothesis necessary (§3 list); $k = 0$: both sides
$\|\mathbf{A}\|_{\mathsf{F}}^2$ (Pythagoras); $\mathbf{\Omega} = \mathbf{0}$: everything is
$\|\mathbf{A}\|_{\mathsf{F}}^2 \le \|\mathbf{A}\|_{\mathsf{F}}^2$; $\mathbf{\Psi} = \mathbf{I}$: GN is the
RSVD, $\mathbf{N} = \mathbf{0}$, and T10 is T3 with equality.

## 4. Files

| # | File | Statements | Lines (est.) | Imports (new) | Depends on |
|---|---|---|---|---|---|
| 1 | `Matrix/Spectral/BestRankApprox.lean` (new) | 21 (11 + 5 + 5; B1 to B21) | 520 | `Matrix/Spectral/LowRank`, `Matrix/Spectral/ProjectedLowRank`, `Matrix/Norms/UnitarilyInvariant`, `Matrix/Norms/Nuclear`, `ForMathlib/LinearAlgebra/Matrix/Rank` | S1's L2 and L5b (B21 only) |
| 2 | `Matrix/Factorizations/NystromOrder.lean` (extended) | 1 (N1) | +15 | none | none |
| 3 | `LowRank/Structural/Truncation.lean` (new) | 12 (6 + 4 + 2; T1 to T12) | 380 | file 1, `Matrix/Factorizations/SketchedLowRank`, `Matrix/Factorizations/NystromOrder` (with `NystromGram`) | files 1, 2; S1's L1 (T6) |

S2a is about 915 lines and 34 public declarations (brief: 550). The growth is the predicate's API
(about 150 lines, which D5 left conditional), reverse Eckart–Young (about 60, new, for MT 14.1), and
the truncated-GN assembly (about 80, moved from S6, which shrinks by as much). File 1's statement count
(21) is below the line budget; it is one topic, best approximations and their perturbation. Order in
file 1: §3.1, §3.2, §3.3; file 3: §3.5, §3.6, §3.7. File 1 is independent of S1's `RangeFinder.lean`,
so S2a can be proved before S1 finishes, except B21 (and T7 to T9 through it), which waits for L2 and
L5b. N1 is short and is written proved in its registered file; nothing else touches a registered file.

## 5. Material

**Prototype** (read-only, `~/Documents/prove2me/lean/NLAlib/`; ledger dispositions):
- `Matrix/Subspaces/Projections.lean`: `IsBestFrobRankApprox` → `IsBestRankApprox` (renamed,
  structure, `frobNorm` not `frobSq`); `exists_isBestFrobRankApprox` → `isBestRankApprox_truncatedSVD`.
- `LowRank/RandomizedSVD/OptimalError.lean` (truncation half): `truncatedRsvdOutput` → cut (Q1;
  `truncatedSVD (rsvd A Ω) k`, and the algorithm's `Q * truncatedSVD (Qᴴ * A) k` through T5);
  `rank_truncatedRsvdOutput_le` → cut (`rank_truncatedSVD_le`); `frobSq_truncatedRsvdOutput_eq` →
  `frobNorm_sub_truncatedSVD_rsvd_sq` with T5;
  `IsBestFrobRankApprox.frobSq_sub_mul_le_bestRankFrobSq_add_frobSq_residual` and
  `frobSq_sub_truncatedRsvdOutput_le_bestRankFrobSq_add_frobSq_residual` →
  `frobNorm_sub_truncatedSVD_rsvd_sq_le_frobNorm_sub_rsvd_sq_add`; the two `…_two_mul_…` variants →
  cut (dominated, rule 6, no consumer); `bestRankFrobSq_eq_zero_of_width_le` → cut
  (`truncatedSVD_of_rank_le`); the `integrable_…` and Gaussian statements → S3.
- `LowRank/RandomizedSVD/RSVD.lean`: `frobSq_sub_mul_transpose_mul_le_frobSq_sub_mul` → exists
  (`HasOrthonormalCols.frobNorm_sub_mul_sq`); `rsvd_truncated_main` → S3.
- No prototype file has truncated Nyström, truncated GN, reverse Eckart–Young or perturbed truncation.

**The maintainer's formalization** (read-only material, never cited, not ledgered; D13):
`~/Documents/Papers/LRA-paper/formal/LRA/Deterministic/PerturbedTruncation.lean`: `IsBestRankApprox`
→ B1 (same shape, over `𝕜`); `RankTraceBound` → not introduced (B17 is its sharpened instance);
`quadratic_root_bound` → proof-internal; `frobNorm_sub_bestRankApprox_perturb` → B18 (sharper
parameter) and B19; `frobSq_sub_bestRankApprox_perturb` → cut (square of B19); `frobSq_sub_mul_split`
→ exists (`HasOrthonormalCols.frobNorm_sub_mul_sq`); `tGN_assembly` → T10, T11 (basis-free). The
notes `tGN_replacement.tex` (Lemma `lem:tGN-perturb`, the assembly (`eq:tGN-split`,
`eq:tGN-assembly`), the baseline `lem:tGN-baseline` with $\gamma \le \mathrm{OPT}$, here T12) and
`GN_truncated.tex` (Lemma `lem:pert` and Corollary `cor:vN`, whose display (`eq:vNstep`) passes
through $(\sum_{i \le 2k}\sigma_i(\mathbf{E})^2)^{1/2} = \|\llbracket\mathbf{E}\rrbracket_{2k}\|_{\mathsf{F}}$,
the parameter of B18) were read; `main.tex` holds no other late-truncation result.

**Literature**, locators confirmed against the PDFs (`~/Documents/prove2me/books/`,
`/tmp/claude-1000/p0/papers/`):
- TYUC SIMAX (arXiv:1609.00048 v2, the version in hand, printed pages): Proposition 6.1, (6.1)
  (p. 16): $\|\mathbf{A}-\llbracket\hat{\mathbf{A}}_{\mathrm{in}}\rrbracket_r\|_{\mathsf{F}} \le
  \tau_{r+1}(\mathbf{A}) + 2\|\mathbf{A}-\hat{\mathbf{A}}_{\mathrm{in}}\|_{\mathsf{F}}$, with
  $\llbracket\cdot\rrbracket_r$ "a best rank-$r$ approximation with respect to Frobenius norm" (any
  choice, as B14); Remark 6.2 (p. 17): the same in spectral norm; §6.2, (6.2) and (6.3) (p. 17):
  "there is also a best rank-$r$ approximation of $\mathbf{Q}\mathbf{X}$ that satisfies
  $\llbracket\mathbf{Q}\mathbf{X}\rrbracket_r = \mathbf{Q}\llbracket\mathbf{X}\rrbracket_r$", D5's
  factored form; Corollary 6.4 (p. 18), the constant 2 inside a Gaussian expectation. arXiv v1
  numbers the proposition 7.1 (TYUC NeurIPS cites "[36, Prop. 7.1]", v1).
- TYUC NeurIPS (arXiv:1706.05736 v1): Theorem 4.1 (p. 5), (4.1) Schatten-1 with
  $1+\frac{r}{k-r-\alpha}$ and (4.2) Schatten-$\infty$ $\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_r\|_\infty
  + \frac{r}{k-r-\alpha}\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_r\|_1$; Theorem 4.2 (p. 6, the
  constant-2 route); Proposition A.6 (p. 10), the constant-2 lemma for every Schatten $p$;
  App. A.5 (p. 11): $\|\mathbf{A}-\hat{\mathbf{A}}_r\|_1 = \|\mathbf{A}^{1/2}-\mathbf{P}\llbracket
  \mathbf{P}\mathbf{A}^{1/2}\rrbracket_r\|_{\mathsf{F}}^2$ (T8) and Gu's Theorem 3.5 (T6's shape);
  Proposition A.8 (p. 12), "Reversed Eckart–Young": $\|\mathbf{A}-\mathbf{B}\|_\infty \le
  \sigma_{r+1}(\mathbf{A}) + [\|\mathbf{A}-\mathbf{B}\|_1 - \sigma^{(1)}_{r+1}(\mathbf{A})]$ for
  $\operatorname{rank}\mathbf{B} \le r$ (B16), "a minor change to [Gu, Thm. 3.4]"; (4.2) follows from
  (4.1) and A.8 (p. 12). So MT 14.1's constant is reached by deterministic algebra on top of the
  trace bound, which the brief already has.
- MT (printed = PDF + 402): §14.2 (p. 495), §14.3 (p. 496: $\hat{\mathbf{A}}_k$ "a best rank-$k$
  approximation of $\hat{\mathbf{A}}$ with respect to the Frobenius norm"), Theorem 14.1 (p. 496:
  $\mathbb{E}\|\mathbf{A}-\hat{\mathbf{A}}_k\| \le \lambda_{k+1} + \frac{k}{\ell-k-1}\sum_{j>k}\lambda_j$,
  spectral, real or complex standard normal, credited to TYUC 2017a Theorem 4.1).
- HMT (arXiv v2): §9.4, Theorem 9.3 (p. 54, proof to p. 55): spectral, $\hat{\mathbf{A}}_{(k)}$ "a
  best rank-$k$ approximation of $\mathbf{P}_{\mathbf{Z}}\mathbf{A}$ with respect to the spectral
  norm", any $\mathbf{Z}$, "proposed by Ming Gu"; Remark 9.1.
- TW (arXiv:2306.12418 v3): p. 42, truncated outputs: "due to the reverse Eckart–Young inequality
  [Gu, Thm. 3.4]".
- Woodruff 2014: Lemma 44 (p. 63, Pythagoras in a row space: T3, T4's mechanism); Theorem 47
  (p. 66 to 67, Q8).
- CEMT: the remarks after Theorem 1.3 and after Theorem 2.2 (p. 16) promote rank-$k$ to rank-$r$
  "by a standard truncation technique [HMT Thm. 9.3]", which is spectral; T4 is the Frobenius
  statement those Frobenius results need (brief §9.1).
- Gu 2015 is not in hand. Its Theorems 3.4 and 3.5 are cited only through TYUC NeurIPS and TW,
  with "to confirm" (§9.2's nice-to-have list); B15 is presented as the Frobenius twin of TYUC's
  Proposition A.8 and attributed to Gu only after the paper is read.

**Citations** (keys: `TroppYurtseverUdellCevher2017` and `TroppWebber2023` enter with S0's first PR;
`TroppYurtseverUdellCevher2017a` (NeurIPS) is new and enters with file 1; `Gu2015` not until read):

| statement | citation | relation to the printed statement |
|---|---|---|
| B1 to B8 | [GolubVanLoan2013, Theorem 2.4.8]; [HornJohnson2013, §7.4.9] | definition and Eckart–Young; B5's characterization is the equality case, proved here |
| B9 to B11 | [TroppYurtseverUdellCevher2017, §6.2, (6.3)] | there "there is a best approximation" with the property; here the explicit one |
| B12, B13 | [HalkoMartinssonTropp2011, Theorem 9.3] | there spectral, projections, spectral-best $\mathbf{Y}$; here every gauge, any dominated $\hat{\mathbf{A}}$, Frobenius-best $\mathbf{Y}$ |
| B14 | [TroppYurtseverUdellCevher2017, Proposition 6.1, Remark 6.2]; [TroppYurtseverUdellCevher2017a, Proposition A.6] | there Frobenius, spectral, Schatten $p$; here every gauge |
| B15 | [TroppYurtseverUdellCevher2017a, Proposition A.8 (proof)]; [TroppWebber2023, §9.1, p. 42] | Frobenius-squared twin of the nuclear form; attributed to Gu 2015 Theorem 3.4 after confirmation |
| B16 | [TroppYurtseverUdellCevher2017a, Proposition A.8] | same statement, subtraction-free, 0-indexed |
| B17 | [HornJohnson2013, Theorem 7.4.1.1] | helper; generalizes `frobInner_le_sqrt_mul_frobNorm_mul_specNorm_of_rank_le` |
| B18, B19, T10, T11 | proved without a literature source; input [HornJohnson2013, Theorem 7.4.1.1]; related [TroppYurtseverUdellCevher2017, Proposition 6.1] | D13 |
| B20, T7, T8 | [TroppYurtseverUdellCevher2017a, App. A.5]; [MartinssonTropp2020, §14.2] | there in the proof of Theorem 4.1 for $\mathbf{A}^{1/2}$ and Gaussian $\mathbf{\Omega}$; here any factor, deterministic |
| B21, N1, T9 | [MartinssonTropp2020, §14.3]; [EpperlyWebber2026, Fact 6.1(a)] (N1) | there PSD of the approximation; order and domination stated here |
| T1 | [HalkoMartinssonTropp2011, Theorem 9.3] | there spectral; here every gauge |
| T2 | [MartinssonTropp2020, §14.3]; [TroppYurtseverUdellCevher2017a, Theorem 4.2 (proof)] | there inside an expectation with constant 2; here constant 1 by domination |
| T3, T4, T12 | [Woodruff2014, Lemma 44]; [HalkoMartinssonTropp2011, Theorem 9.3] | there the optimality of $[\mathbf{A}\mathbf{U}]_k\mathbf{U}^{\mathsf{T}}$ in a row space; here the exact split for the named output |
| T5 | [TroppYurtseverUdellCevher2017, (6.3)] | the algorithm's form against the definition |
| T6 | [TroppYurtseverUdellCevher2017a, App. A.5] (Gu's Theorem 3.5 as applied there) | there for $\mathbf{A}^{1/2}$; here any matrix and test matrix |

Port provenance lines on B1, B2 and T4 (prototype). **Result ids** (D11; ids are defined by
`Result:` lines; checked against `explore/results.toml` and `synonyms.toml`, no collision with the
`eckart-young-*`, `mirsky-inequality`, `von-neumann-trace-inequality`, S0's and S1's ids):
`truncation-lemma` (B13, B14, T1, T2, T4; one node, titled from the shared bold head "The truncation
lemma"), `perturbed-truncation` (B18, B19, T10, T11), `reverse-eckart-young` (B15, B16, new),
`truncated-gram-correspondence` (T7, T8, new). The predicate, helpers and bridges carry none.

## 6. Cut, and why

- *Named instances with no content beyond B14*: GN constant two
  (`matrixNorm_sub_truncatedSVD_generalizedNystrom_le`) is `hY.matrixNorm_sub_le_add_two_mul` at
  `isBestRankApprox_truncatedSVD`; one term, no rewrite (Q9). Likewise the Nyström instance of B16
  (S5 applies B16 with `rank_truncatedSVD_le`).
- *A general orthogonal-projector form of T1 and T3* ($\llbracket\mathbf{P}\mathbf{A}\rrbracket_k$
  for any `IsStarProjection P`): B13 with `IsStarProjection.singularValues_mul_le` is the general
  form, and every consumer has `rsvd` (the maintainer's spelling rule).
- *A per-norm optimality predicate* ($\mathbf{Y}$ best in $\Phi$ only, HMT 9.3's spectral-best
  hypothesis): algorithms compute SVD truncations, which are Frobenius-best; a spectral-best
  $\mathbf{Y}$ is covered by the one-line triangle argument if a user needs it. Additive.
- *`RankTraceBound`*: one instance (the spectral norm), now a corollary (Q5).
- *Squared forms of B18, B19 and the manuscript's `lem:pert` inner-product form*: `pow_le_pow_left₀`,
  and the inner product is proof-internal; S6 expands the square of T11.
- *Woodruff Theorem 47's rank-$k$ clause* (brief item 7.7): S7 (Q8).
- *The spectral twin of truncation for free with $\|\mathbf{M}\|_2^2$* (brief item 7.8's
  conjecture): not established and no source in hand. What S2a gives is
  $\|\mathbf{A}-\llbracket\mathbf{P}\mathbf{A}\rrbracket_k\|_2^2 \le \sigma_{k+1}^2 +
  \|\mathbf{M}\|_{\mathsf{F}}^2$, from B15, T3 and S1's truncation for free, composed in S3.
- *Ky Fan generalization of B16* ($\|\mathbf{A}-\mathbf{B}\|_{(j)} \le \sum_{k\le i<k+j}
  \sigma_i(\mathbf{A}) + \|\mathbf{A}-\mathbf{B}\|_* - \|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k\|_*$):
  same proof, no consumer. Additive.
- *Measurability of truncated outputs*: not an S2a statement (Q3).

## 7. Questions and decisions

Hard-to-reverse items are marked **(hard)**. Under the round's approval rule (serious, hard-to-reverse
decisions go to the maintainer), Q1 is one; Q2 and Q3 are interface decisions recorded for the
checkpoint after S2b.

**Q1. No names for truncated outputs (hard; for the maintainer, a naming scheme).** Options:
(a) none: `truncatedSVD (rsvd A Ω) k`, `truncatedSVD (nystrom H Ω) k`,
`truncatedSVD (generalizedNystrom A Ω Ψ) k` (brief D1 table, S0 §1); (b) `def`s
`truncatedRSVD A Ω k`, `truncatedNystrom H Ω k`, `truncatedGeneralizedNystrom A Ω Ψ k` with `_def`
lemmas; (c) the algorithms' factored forms as definitions (`Q * truncatedSVD (Qᴴ * A) k`, the
prototype's `truncatedRsvdOutput`), which need a basis argument. Recommendation (a): the composite
already reads as the sources' $\llbracket\hat{\mathbf{A}}\rrbracket_k$ and satisfies the maintainer's
rule (the error is $\mathbf{A}$ minus a named output); every general lemma (B13, B14, B18) applies
with no unfolding; a `def` would need its own rank, range and error API mirroring `truncatedSVD`'s,
the bridge-file pattern D1 removed; and (c) fixes a basis, which D1 rejected for measurability. Cost:
users searching "truncated randomized SVD" find the module docstring and the docstrings, not a
declaration. Rework if reversed after S3: the statement shape of every truncated result of S3 to S7
(by the spelling rule, statements would have to use the new names). Decide before S3's skeleton.
S2b faces the same question for early truncation, whose outputs are not compositions of a named
output with `truncatedSVD`.

**Q2. The predicate `IsBestRankApprox C k Y` (moderately hard; interface).** Options: (a) a
structure, Frobenius optimality against every competitor, D5's one-line form as an iff (B3);
(b) D5's one-line hypothesis spelled inline, no predicate; (c) definition by singular values
(`∀ i, singularValues (C - Y) i = singularValues C (k + i)`). Recommendation (a): ten statements take
it (D5's threshold is three); it is the textbook definition, bridges to Mathlib's `IsMinOn` (B4), and
does not mention `truncatedSVD`; (c) is B5, a consequence, and less recognizable as a hypothesis.
Name: `IsBestRankApprox`, not the prototype's `IsBestFrobRankApprox`, because B6 makes it optimal in
every gauge; the docstring says the definition is Frobenius. Rework if changed: the hypothesis line of
about ten S2a statements and of S6's truncated GN.

**Q3. Measurability of choice-dependent truncated errors (moderately hard; for the S3, S5, S6
notes).** `truncatedSVD` is a choice per matrix, with no measurability. The choice-free errors are
measurable as functions of the output: the Frobenius error of truncated RSVD by T3 (and
`SymmetricGauge.continuous_matrixNorm_sub_truncatedSVD`), the nuclear error of truncated Nyström by
T7, every bound of S2a's right-hand sides. The spectral errors (S3's spectral truncated RSVD, S5's MT
14.1) are not known to be measurable; a Bochner integral of them is provable as an upper bound
(`integral_mono_of_nonneg` needs only the dominating function integrable) but their `integrable_…`
companion (D4) is not. Options: (a) state those expectations with a measurable selector:
`(hY : ∀ ω, IsBestRankApprox (Â ω) k (Y ω)) (hYm : AEStronglyMeasurable Y μ)`, the named-output form
as a bound only; (b) prove a.s. uniqueness of the truncation under Gaussian laws (no ties a.s.):
heavy; (c) redefine `truncatedSVD` through a measurable selection: a Matrix-layer change, hard to
reverse. Recommendation (a), with Frobenius and trace results on the named outputs directly. S2a's
hypothesis forms are what make (a) possible.

**Q4. A Matrix-layer file for the general lemmas (not hard).** The brief puts everything in
`LowRank/Structural/Truncation.lean`. B1 to B21 mention no algorithm and are matrix analysis
(CONTRIBUTING §2, layer 0); S1's tail flattening set the precedent (S1 Q7). The name is the topic,
best approximations of rank at most $k$. Rework: a file move.

**Q5. Perturbed truncation in the parameter $\|\llbracket\mathbf{E}\rrbracket_{2k}\|_{\mathsf{F}}$, no
`RankTraceBound` (not hard).** B18 dominates the spectral form ($\le\sqrt{2k}\|\mathbf{E}\|_2$) and,
in the Frobenius norm, the constant-two lemma ($\le\|\mathbf{E}\|_{\mathsf{F}}$), so D10's
late-truncation pair is one statement with two corollaries (rule 6: B19 kept, consumers cite it; B14
kept because it holds in every gauge). The formalization's `RankTraceBound` has one instance and is
replaced by B17. The assessment's (R2) stands: no gauge version is attempted.

**Q6. MT Theorem 14.1 in S5 (information; not hard).** Reachable (literature checks above): S2a adds
B16, and S5 promises $\lambda_{k+1} + \frac{k}{\ell-k-1}\sum_{j>k}\lambda_j$, not only
$2\lambda_{k+1} + \dots$. The brief's §4.3 Nyström bullet, §7 S5 entry ("MT Theorem 14.1's constant
only after TYUC NeurIPS is read, and then as an S2a lemma") and §9.1 are updated by this note. The
constant-1 Nyström lemma (T2) stays: it is pointwise, every gauge, and serves tails.

**Q7. The truncated-GN assembly in S2a, basis-free (not hard).** It is deterministic, so it belongs
to the deterministic stage; stating it with
$\mathbf{\Pi}_{\mathbf{A}\mathbf{\Omega},\mathbf{\Psi}^{\mathsf{H}}}(\mathbf{A}-\mathbf{P}\mathbf{A})$
keeps $\mathbf{Q}$ out of the statement, as the maintainer's rule and D1's carrier want, and S0's
range invariance gives S6 its fixed-basis $\mathbf{N}_0$ in one rewrite. S6 keeps the probabilistic
inputs and the arithmetic.

**Q8. Woodruff Theorem 47's rank-$k$ clause goes to S7 (information; not hard).** Read on pp. 66 to
67: the output $[\mathbf{A}\mathbf{R}\mathbf{U}]_k\mathbf{U}^{\mathsf{T}}(\mathbf{S}\mathbf{A}
\mathbf{R})^{+}\mathbf{S}\mathbf{A}$ is the minimizer of a rank-constrained sketched regression, not
the late truncation of GN, and its probabilistic step ("by the properties of an $\ell_2$-subspace
embedding") needs $\mathbf{R}$ to control $\|(\mathbf{Y}\mathbf{S}\mathbf{A}-\mathbf{A})\mathbf{R}\|$
uniformly in $\mathbf{Y}$, which a subspace embedding of the row space of $\mathbf{S}\mathbf{A}$
alone does not give: an affine-embedding (AMM) term for the residual is needed. That term does not
depend on $\mathbf{Y}$, so the uniformity over rank-$k$ cores may come for free at Woodruff's
dimension ($\mathbf{R}$ a $(1+O(\varepsilon))$ embedding of a space of dimension $O(k/\varepsilon)$);
the retracted "Lemma B" claimed a smaller dimension. The D15 check belongs to S7, which owns the
probabilistic step; its deterministic half (the rank-constrained least-squares formula) has no S2a
to S6 consumer.

**Q9. Gu's projected form T6 kept; no further named instances (not hard).** T6 has the weakest
consumer case (S5 can use S1's competitor instead), but it is the hypothesis-free, sharper form of
truncation for free and the literal step of TYUC NeurIPS's proof of their Theorem 4.1. The GN
constant-two and Nyström reverse-Eckart–Young instances are not stated (§6). All additive.

**Q10. Corrections of record (information).** Brief §3(b) D10 and §5.2: the late-truncation pair is
resolved by Q5. Brief §4.1 item 7.2: the attribution to TYUC SIMAX is confirmed, Proposition 6.1 in
the version in hand (7.1 in arXiv v1). Brief §4.1 item 7.8 and §9.2: Gu's Theorem 3.4 is the reverse
Eckart–Young inequality (TW p. 42, TYUC NeurIPS p. 12); the conjectured $\|\mathbf{M}\|_2^2$ twin is
not what it gives (§6). Brief §4.3 and §9.1 on MT 14.1: Q6. S1 §5's statement that TYUC NeurIPS
Proposition A.6 is "S2a's constant-2 lemma" stands; its Proposition A.8 is S2a's B16.

## 8. Amendments from the review (2026-10-15)

Review of this note (1 high, 1 medium, 10 low), all twelve amendments accepted by the orchestrator,
one corrected on inspection (A1's generalization, item 1); none rejected. One further correction on
inspection, to the drafted §3 and to the review's Q3 verdict: the Frobenius error of truncated GN is
choice-dependent (item 15). Q1, Q2 and Q3 decided as (a) (items 13 to 15), Q3's option (b)
recorded as false; Q4 to Q10 stand as recommended (the review raised no objection; Q9 is amended by
item 4). The review verified by hand, at $k = 0$, $k$ at or
above the rank, ties, empty index types and non-PSD Nyström inputs, all 34 statements B1 to B21, N1,
T1 to T12, and numerically B15, B16, B18, T6, T10 and the tie examples; the constants match the
sources (TYUC SIMAX Proposition 6.1 and Remark 6.2, TYUC NeurIPS Propositions A.6 and A.8 with the
0-indexing shift, MT Theorem 14.1 reached as §3.6 says). Where an item below contradicts §0 to §7, it
supersedes them; §3 stays as drafted. Skeletons: the files of item 19.

1. **A1, Q3's option (b) is false, not heavy** (amends §7 Q3). For $\mathbf{A} = \mathbf{I}_n$,
   `rsvd A Ω` $= \mathbf{P}_{\mathbf{\Omega}}$ is an orthogonal projector, whose singular values are
   $1$ and $0$, so the tie $\sigma_{k-1} = \sigma_k = 1$ holds for every $\mathbf{\Omega}$ with
   $1 \le k < \operatorname{rank}\mathbf{\Omega}$, hence with probability one under a Gaussian law:
   almost-sure uniqueness of `truncatedSVD (rsvd A Ω) k` fails in general. A version under a
   hypothesis on $\mathbf{A}$ would need a measure-zero argument the library does not have. Q3's (b)
   reads: "false for $\mathbf{A} = \mathbf{I}$; not an option". **Corrected on inspection:** the
   review extends the failure to "any $\mathbf{A}$ with a repeated singular value". That is broader
   than the argument: for $\mathbf{A} = \operatorname{diag}(1, 1, \tfrac12)$ and $\ell = 2$, the
   projected matrix has squared singular values $1$ and the other eigenvalue of the compression of
   $\operatorname{diag}(1, 1, \tfrac14)$ to $\operatorname{range}(\mathbf{A}\mathbf{\Omega})$, which
   equals $1$ only when that range is $\operatorname{span}\{\mathbf{e}_1, \mathbf{e}_2\}$, a null
   event. Ties are almost sure when the projected matrix inherits the repeated value with positive
   probability ($\mathbf{A} = \mathbf{I}$; a repeated value with $\ell \ge n$). One counterexample
   suffices to drop (b); the conclusion stands.
2. **A2, the tie example is a range-finder instance** (replaces the example in §3's "Ties" bullet;
   Q3 refers to it). The drafted example takes $\mathbf{P}$ onto $\operatorname{span}\{\mathbf{e}_1,
   \mathbf{e}_2\}$, which is not contained in $\operatorname{range}\mathbf{A}$, so $\mathbf{P}$ is no
   $\mathbf{P}_{\mathbf{A}\mathbf{\Omega}}$: it shows choice dependence in B13's abstract setting
   only. Replacement, which shows it for `rsvd` itself:
   $\mathbf{A} = \begin{bmatrix} 1 & 0 & 0 \\ 0 & 1 & \tfrac12 \\ 0 & 0 & \tfrac12 \end{bmatrix}$,
   $\mathbf{\Omega} = [\mathbf{e}_1\ \mathbf{e}_3]$, $k = 1$. Then $\operatorname{range}
   (\mathbf{A}\mathbf{\Omega}) = \operatorname{span}\{\mathbf{e}_1, \mathbf{u}\}$ with $\mathbf{u} =
   (0, 1, 1)/\sqrt2$, and $\mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A} = \mathbf{e}_1
   \mathbf{e}_1^{\mathsf{H}} + \mathbf{u}\mathbf{u}^{\mathsf{H}}$ has singular values $(1, 1, 0)$.
   Its best rank-1 approximations include $\mathbf{e}_1\mathbf{e}_1^{\mathsf{H}}$ and
   $\mathbf{u}\mathbf{u}^{\mathsf{H}}$ (in general $(a\mathbf{e}_1 + b\mathbf{u})(a\mathbf{e}_1 +
   b\mathbf{u})^{\mathsf{H}}$, $a^2 + b^2 = 1$). The spectral error squared is $(3+\sqrt5)/4 \approx
   1.309$ for the first and $1$ for the second; the Frobenius error squared is $\tfrac32$ for every
   choice ($\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{\mathsf{F}}^2 = \tfrac12$ plus the tail $1$, T3).
   Checked by hand here and numerically by the review. The bullet ends: "so the spectral error of
   `A - truncatedSVD (rsvd A Ω) k` depends on the choice; consequence for S3 to S6: Q3".
3. **A3, S1's lemmas exist** (amends the status line, "Missing infrastructure", §2's "Used
   directly", §4's "Depends on" column and its last paragraph). L1
   `mul_rangeProjector_conjTranspose_truncatedSVD`, L2
   `exists_hasOrthonormalCols_mul_mul_conjTranspose_eq_truncatedSVD` and L5b
   `Matrix.PosSemidef.one_sub_mul_mul_one_sub_eq_sub_truncatedSVD` (with L5a
   `Matrix.PosSemidef.truncatedSVD`) are proved in `Matrix/Spectral/LowRank.lean`, which is
   registered; S1's `RangeFinder.lean` is registered too. "In `LowRank.lean` and being proved" reads
   "in `LowRank.lean`, proved". B21, and T7 to T9 through it, wait for nothing: file 1 depends only
   on registered files, and S2a can be proved in any order.
4. **A4, T6 dominates T4 for every test matrix** (§3.5 docstrings of T4 and T6; §6; Q9). With
   $\mathbf{T} = \llbracket\mathbf{A}\rrbracket_k$, L1 gives $\mathbf{T} = \mathbf{A}
   \mathbf{P}_{\mathbf{T}^{\mathsf{H}}}$, so $(\mathbf{I}-\mathbf{P})\mathbf{T} = (\mathbf{I}-\mathbf{P})
   \mathbf{A}\mathbf{P}_{\mathbf{T}^{\mathsf{H}}}$ and $\|\mathbf{T} - \mathbf{P}\mathbf{T}\|_{\mathsf{F}}
   \le \|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{\mathsf{F}}$ for every orthogonal projector
   $\mathbf{P}$: T6's right side is at most T4's, with no rank hypothesis. T6's docstring states this
   and replaces "under S1's hypothesis ... at least as sharp as truncation for free" by "for every
   test matrix it is at least as sharp as the Frobenius-squared truncation lemma
   (`frobNorm_sub_truncatedSVD_rsvd_sq_le_frobNorm_sub_rsvd_sq_add`) and, under S1's hypothesis, as
   truncation for free". T4's docstring adds "dominated by
   `frobNorm_sub_truncatedSVD_rsvd_sq_le_frobNorm_sub_truncatedSVD_sq_add`, kept because S3 and S7
   cite this simpler form" (CONTRIBUTING §5.2 rule 6). T4's route stays T3 and T12 (no L1 needed);
   the domination is a docstring claim backed by T6 and the inequality above, which T6's proof does
   not need. Q9's "T6 has the weakest consumer case" is replaced by "T6 is the sharpest Frobenius
   form of truncated RSVD in S2a".
5. **A5, the singular-value characterization as an iff** (+1 in file 1, after B5; Q2's option (c)
   becomes a theorem):
   ```lean
   /-- A matrix of rank at most $k$ is a best approximation of $\mathbf{C}$ exactly when its error
   has the tail singular values: $\sigma_i(\mathbf{C} - \mathbf{Y}) = \sigma_{k+i}(\mathbf{C})$ for
   every $i$. -/
   theorem isBestRankApprox_iff_singularValues_sub {C Y : Matrix m n 𝕜} {k : ℕ} :
       IsBestRankApprox C k Y ↔
         Y.rank ≤ k ∧ ∀ i, singularValues (C - Y) i = singularValues C (k + i)
   ```
   Route: (⇒) `h.rank_le` and B5; (⇐) the singular values give $\|\mathbf{C}-\mathbf{Y}
   \|_{\mathsf{F}}^2 = \sum_i\sigma_{k+i}(\mathbf{C})^2 = \|\mathbf{C}-\llbracket\mathbf{C}
   \rrbracket_k\|_{\mathsf{F}}^2$ (`frobNorm_sq_eq_sum_range_singularValues_sq` on both errors,
   `singularValues_sub_truncatedSVD`), then B3. Label B22. B5 stays as the projection users reach
   for; it replaces nothing.
6. **A6, the Frobenius norm of a truncation as a head sum, public** (+1, label B23; home
   `Matrix/Spectral/LowRank.lean`, after `frobNorm_sub_truncatedSVD_sq`, placement by item 18).
   B17's route needs it, and S6's measurability of T10's and T11's right sides needs continuity of
   $\mathbf{E} \mapsto \|\llbracket\mathbf{E}\rrbracket_r\|_{\mathsf{F}}$, which follows from it and
   `continuous_singularValues` (`Matrix/Perturbation/Continuity.lean`); Q3's "every bound of S2a's
   right-hand sides is measurable" relies on it:
   ```lean
   /-- The truncated SVD keeps the leading singular values in the Frobenius norm:
   $\|\llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2 = \sum_{i<k}\sigma_i(\mathbf{A})^2$, for every
   choice of the truncation. -/
   theorem frobNorm_truncatedSVD_sq (A : Matrix m n 𝕜) (k : ℕ) :
       frobNorm (truncatedSVD A k) ^ 2 = ∑ i ∈ Finset.range k, singularValues A i ^ 2
   ```
   Route: `frobNorm_sq_eq_sum_range_singularValues_sq` at $N = k$ (`rank_truncatedSVD_le`), then
   `singularValues_truncatedSVD` and `if_pos` on `Finset.range k`. Indices at or above
   $\min(\lvert m\rvert, \lvert n\rvert)$ contribute $0$ (padding). The continuity lemma is S6's to
   state if S6 needs it as a declaration.
7. **A7, T8 does not touch a registered file** (§3.6 T8 route; §4 last paragraph). S0's private
   `eq_conjTranspose_sqrt_mul_sqrt` (`NystromGram.lean`) is reproved in two lines inside T8's proof:
   $(\mathbf{H}^{1/2})^{\mathsf{H}} = \mathbf{H}^{1/2}$ from `CFC.sqrt_nonneg` and
   `Matrix.nonneg_iff_posSemidef`, then `CFC.sqrt_mul_sqrt_self`. Making it public is left to S0's
   wrap-up, outside S2a. With item 18, N1 and B23 are the only statements whose home is a registered
   file.
8. **A8, a departure from D5 recorded** (adds a bullet to "Departures from the brief"): "**No
   generic `truncatedSVD` corollaries of B13 and B14.** D5 promised the `truncatedSVD` forms as
   corollaries; the named-output instances T1, T2 are stated, and the generic instance is one term,
   `(isBestRankApprox_truncatedSVD _ _).matrixNorm_sub_le_add_two_mul` (rule 6, §6)."
9. **A9, B11 for any $\mathbf{Q}$** (§3.1 docstring of B11). $\operatorname{range}
   \llbracket\mathbf{Q}\mathbf{X}\rrbracket_k \subseteq \operatorname{range}(\mathbf{Q}\mathbf{X})
   \subseteq \operatorname{range}\mathbf{Q}$ gives $\mathbf{P}_{\mathbf{Q}}\llbracket\mathbf{Q}
   \mathbf{X}\rrbracket_k = \llbracket\mathbf{Q}\mathbf{X}\rrbracket_k$ for every $\mathbf{Q}$; B11
   is that with `hQ.rangeProjector_eq`, which is already its route. B11 is kept as stated, its
   docstring adds "the projector form $\mathbf{P}_{\mathbf{Q}}\llbracket\mathbf{Q}\mathbf{X}
   \rrbracket_k = \llbracket\mathbf{Q}\mathbf{X}\rrbracket_k$ holds for every $\mathbf{Q}$", and the
   general form is not a declaration (no consumer; additive).
10. **A10, the composed spectral bound in §0's table** (§0, row "reverse Eckart–Young"; §6). The S3
    entry reads: "S3 (spectral second moment of truncated RSVD: under S1's hypothesis,
    $\|\mathbf{A} - \llbracket\mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A}\rrbracket_k\|_2^2 \le
    \sigma_k(\mathbf{A})^2 + \|\mathbf{M}\|_{\mathsf{F}}^2$, by B15 at $\mathbf{B} =
    \llbracket\mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A}\rrbracket_k$, then S1's truncation for
    free through T5, whose first term $\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k
    \|_{\mathsf{F}}^2$ cancels; not through T4, which leaves $\|\mathbf{A} -
    \mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A}\|_{\mathsf{F}}^2$)". §6's bullet uses 0-indexed
    $\sigma_k(\mathbf{A})$ in place of its prose $\sigma_{k+1}$.
11. **A11, "the pair becomes one lemma and two corollaries" in the Frobenius norm** (the third
    departure bullet). It reads: "In the Frobenius norm it dominates both bounds of D10's
    late-truncation pair ($\|\llbracket\mathbf{E}\rrbracket_{2k}\|_{\mathsf{F}} \le \min(\|\mathbf{E}
    \|_{\mathsf{F}}, \sqrt{2k}\,\|\mathbf{E}\|_2)$), so there the pair is one lemma and two
    corollaries; B14 stays for every other gauge", as Q5 already says. The brief's "incomparable"
    (D10) is wrong in the Frobenius norm only.
12. **A12, the predicate's count** (§2 "Statements taking it"; §0; Q2). As hypothesis: B5, B6, B7,
    B8, B9 (both directions), B13, B14, B18, B19, nine, plus S6 and S7 downstream; as conclusion:
    B2, B3, B4, B10, and B22 (item 5). Nine against D5's threshold of three. §0's "passed by ten"
    and Q2's "ten statements take it" read "nine".
13. **Q1 decided as (a) for S2a: no new names.** The late truncations are `truncatedSVD (rsvd A Ω)
    k`, `truncatedSVD (nystrom H Ω) k`, `truncatedSVD (generalizedNystrom A Ω Ψ) k`, as D1's table
    (confirmed by the maintainer) and S0 §1 have them; the maintainer's spelling rule is satisfied,
    since the review reads "likewise for the truncated outputs" against that table. **The naming of
    truncated outputs, late and early together, is one joint question for the maintainer at the S2b
    checkpoint**: whether S2b's early-truncated outputs (raw formulas mirroring `rsvd`'s own
    definition, for which D1's reasons to name `rsvd` apply) get names, and if so whether the late
    ones get names for symmetry ("late = `truncatedSVD` of a named output, early = a named
    algorithm" is consistent without them). The checkpoint precedes S3's skeleton, so a reversal then
    costs three `def`s, their `_def` lemmas and restatements of T1 to T12; after S3 it costs what
    Q1 says. **S2a's statements are written so that a later `def` with a `_def` lemma is additive**:
    each spells the composite literally, and no statement or proof relies on the absence of a name,
    so `def truncatedRSVD A Ω k := truncatedSVD (rsvd A Ω) k` with `truncatedRSVD_def` would add
    declarations and name-spelled restatements without changing any S2a declaration. Q1's
    "a `def` would need its own rank, range and error API" is overstated (a `_def` simp lemma covers
    most of it); the direction stands.
14. **Q2 decided as (a): the structure `IsBestRankApprox`**, two fields `rank_le`,
    `frobNorm_sub_le`, argument order `(C, k, Y)` as `IsLeastSquaresSolution A b x`, Frobenius as
    the defining norm (B6 gives every gauge), the name without "Frob" because of B6. D5's one-line
    form is the iff B3, the Mathlib bridge B4, and option (c) is now the iff B22 (item 5).
    `docs/design/Mathlib-deviations.md`: the name joins "Additions where Mathlib has nothing", as §1
    says (confirmed by the review).
15. **Q3 decided as (a); (b) is false; (c) not now.** Expectations of choice-dependent truncated
    errors (the spectral error of truncated RSVD in S3, MT Theorem 14.1's spectral error in S5, the
    Frobenius and spectral errors of truncated GN in S6, below) are stated with measurable-selector hypotheses,
    `(hY : ∀ ω, IsBestRankApprox (Â ω) k (Y ω)) (hYm : AEStronglyMeasurable Y μ)`. (b) is false
    for the reason of item 1 ($\mathbf{A} = \mathbf{I}$: the tie holds with probability one, so the
    truncation is almost surely non-unique). (c), redefining `truncatedSVD` through a measurable
    selection, is not done now: it changes a finished Matrix-layer object, needs a measurable
    eigenvector selection under multiplicities (the Matrix layer has no measure theory, so the
    definition would be an explicit formula whose measurability is proved in the Probability
    layer), and falls under the rule to defer very complex material; (a) is what a measurable
    `truncatedSVD` would instantiate, so (a) is forward-compatible with (c). `truncatedSVD` is a
    `Classical.choose` of an SVD, so its Borel measurability is not provable from the definition.
    **Frobenius and trace errors are choice-free** (T3, T5, T7) and are stated on the named
    outputs directly, with their `integrable_` companions (D4). **Corrected on inspection:** this
    covers the Frobenius error of truncated RSVD and the trace error of truncated Nyström, not the
    Frobenius error of truncated GN, which is choice-dependent. Example: $\mathbf{A} =
    \begin{bmatrix} \tfrac12 & 0 & -1 \\ 0 & 1 & 0 \\ \tfrac12 & 0 & 1 \end{bmatrix}$,
    $\mathbf{\Omega} = \mathbf{A}^{-1}[\mathbf{e}_1\ \mathbf{e}_2]$, $\mathbf{\Psi}^{\mathsf{H}} =
    \begin{bmatrix} 1 & 0 & 1 \\ 0 & 1 & 0 \end{bmatrix}$ (rank hypothesis holds,
    $\mathbf{\Psi}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega} = \mathbf{I}_2$), $k = 1$: the output is
    $\operatorname{diag}(1, 1, 0)$, and the best rank-1 approximations $\mathbf{e}_1
    \mathbf{e}_1^{\mathsf{H}}$ and $\mathbf{e}_2\mathbf{e}_2^{\mathsf{H}}$ give Frobenius errors
    squared $\tfrac72$ and $\tfrac52$ (spectral $\tfrac52$ and $2$); checked by hand and numerically.
    T10 and T11 hold for every choice (they are proved through B10 and B11), but S6's expectation
    of the truncated-GN Frobenius error falls under the selector form, like the spectral errors.
    §3's "Ties" bullet adds this case to "Choice-dependent". Two facts the S3, S5 and S6 notes
    must record:
    - *The library cannot yet exhibit a measurable selector.* No measurable-selection theorem
      (Kuratowski–Ryll-Nardzewski or a measurable eigenvector choice) is in the library; check
      Mathlib before S3. Until one exists, theorems with a selector hypothesis are not instantiable:
      no `Y` satisfying `hY` and `hYm` can be produced. Each note says so beside them.
    - *A Bochner integral of a non-integrable function is $0$ in Lean* (`MeasureTheory.integral_undef`).
      An expectation upper bound on a named output's spectral error stated without an integrability
      companion is provable (`integral_mono_of_nonneg` needs only the dominating side integrable),
      but it is weak for exactly these errors: if the error is not integrable (in particular, not
      a.e.-strongly measurable) its integral is $0$ and the bound says nothing about the algorithm.
      Such a bound-only form, if a note keeps it beside the selector theorem, says this in its
      docstring and is not counted as the result.
16. **Q4 to Q10 stand as recommended.** The review checked Q4's placement (no algorithm appears,
    CONTRIBUTING layer 0; `LowRank.lean` at 535 lines plus file 1 would pass 1000), Q5's domination
    (with item 11), Q6's derivation of MT 14.1, Q7's basis-free assembly (the rank hypothesis
    transfers by `rank_mul_eq_iff_injOn`; the $\mathbf{\Psi} = \mathbf{0}$ necessity example is
    right), Q8 and Q10. Q9 is amended by item 4.
17. **Docstrings are LaTeX** (CONTRIBUTING §6 item 5): every docstring of the skeleton, including
    items 5 and 6, writes its mathematics as `$…$` and `$$…$$` with the notation table; Lean names
    stay in backticks.
18. **Placement in proved files.** `Matrix/Spectral/LowRank.lean` and
    `Matrix/Factorizations/NystromOrder.lean` are registered and proved; a statement goes into them
    only once proved. B23 (item 6) and N1 are written there proved if they are proved at the
    skeleton; a statement still `sorry` goes into a side file beside its home
    (`Matrix/Spectral/LowRankNorms.lean` for B23, `Matrix/Factorizations/NystromSingularValues.lean`
    for N1), which says it merges into its home at the wrap-up; file 1 imports the first and file 4
    the second meanwhile. Files 1 and 4 are new and take `sorry` statements. This replaces §3.4's
    "written proved (the file is registered)" as a rule.
19. **Files and statements for the skeleton** (amends §4):

    | # | File | Statements | Lines (est.) | Imports (new) | Depends on |
    |---|---|---|---|---|---|
    | 1 | `Matrix/Spectral/BestRankApprox.lean` (new) | 22 (12 + 5 + 5; B1 to B22) | 535 | `Matrix/Spectral/LowRank` (or with file 2's side file), `Matrix/Spectral/ProjectedLowRank`, `Matrix/Norms/UnitarilyInvariant`, `Matrix/Norms/Nuclear`, `ForMathlib/LinearAlgebra/Matrix/Rank` | file 2 (B17 uses B23) |
    | 2 | `Matrix/Spectral/LowRank.lean` (or its side file, item 18) | 1 (B23) | +10 | none | none |
    | 3 | `Matrix/Factorizations/NystromOrder.lean` (or its side file) | 1 (N1) | +15 | none | none |
    | 4 | `LowRank/Structural/Truncation.lean` (new) | 12 (6 + 4 + 2; T1 to T12) | 380 | file 1, `Matrix/Factorizations/SketchedLowRank`, `Matrix/Factorizations/NystromOrder` (with `NystromGram`; or file 3's side file) | files 1, 3 |

    S2a is about 940 lines and 36 public declarations. Order within file 1: §3.1 with B22 after B5,
    §3.2, §3.3; file 4: §3.5, §3.6, §3.7. S1's L1, L2, L5a, L5b come with `LowRank.lean` (item 3);
    nothing waits on S1, and S2a does not import `RangeFinder.lean`.
