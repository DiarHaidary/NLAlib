# Design note: LowRank stage S4, sharp bounds for rotation-invariant test matrices

Status: drafted 2026-10-15 under `docs/PORT_LOWRANK.md` (maintainer decisions of 2026-10-15,
binding: D6, Epperly and Webber's lower bounds are a later round, so S4 states only their upper
bounds and the infrastructure the exact formulas of S6 need; every error spelled as the matrix
minus the named output, `H - nystrom H (X ω)`, `A - rsvd A (X ω)`; docstrings write outputs as
$\mathsf{nystrom}(\mathbf{H}, \mathbf{X})$, $\mathsf{rsvd}(\mathbf{A}, \mathbf{X})$; named
constants show their value through the registry markers of CONTRIBUTING §5.2 rule 2,
`docs/constants.toml` and `scripts/check_constants.py`; D3 real laws; D9 to D13; §4.3 "Haar and
rotation-invariant test matrices (real; S3, S4, S6)" items (i) to (v); §6; the S4 entry of §7) and
its review `/tmp/claude-1000/p0/review_lowrank_brief.txt` (A4: no limit, no random permutations,
no matrix Beta moment). Builds on S0 to S3, S2c and S5 (all proved and registered). Reviewed
2026-10-15 (eleven amendments: one must-fix, one medium, six minor, one process, two for the
record; no blocker), amendments in §8, which overrides §0 to §7 where they disagree (§3 stays as
drafted); all eleven accepted, none rejected, two points corrected on inspection (§8 items 1 and
7). Q1 decided as (a), a free rank parameter that S6 carries too (§8 item 12); Q2 as the review's
hybrid (item 13); Q9 as recommended, `gaussianProjectionFactor` registered (item 4); the rest as
recommended (item 14). The split of `RotationInvariant.lean` is named: F0 to F4 and L-a go to the
new `LowRank/Gaussian/RotationInvariantFactor.lean` (item 5); 20 declarations in six files (item
15). Real field for every probabilistic statement; the Matrix-layer additions and the
law-invariance lemmas are over `𝕜`. Epperly and Webber 2026 is cited "EW" below; arXiv:2605.19096
v2, read in full.

Departures from the brief and the review, each argued below:
- **EW Theorem 4.2(a) and Theorem 2.1 stay in S6**, as the brief's §6 table assigns them. S4 states
  the factor S6 composes with (EW Theorem 3.2, E2 below) and the two Haar inputs S6's Haar half
  needs (the Beta trace B4 and the coupled conjugation average U2). §3.5 writes S6's 4.2(a) shape
  so that the composition is checked now (Q3).
- **No signed-permutation Matrix lemma.** The review's "average of $\mathbf{S}\mathbf{M}
  \mathbf{S}^{\mathsf{H}}$ over signed permutations is scalar" already exists in fixed-point form,
  `eq_smul_one_of_forall_mul_mul_conjTranspose_eq` (`Matrix/Factorizations/PolarFrames.lean`, proved
  by sign changes and transpositions), and that is what the coupled average U2 needs. The finite
  group average of §4.3 (ii) needs less still: after the eigendecomposition the matrix is diagonal,
  the top block is handled by monotonicity (the bound does not depend on its value), and the tail
  block is averaged over its $d$ cyclic shifts inside the proof of E1 (Q4).
- **A free rank parameter.** EW state Theorems 3.2 and 3.6(a) for $r = \operatorname{rank} \ge
  \ell$. The library states them for every $r$ with $\operatorname{rank} \le r$ and $\ell \le r$:
  the factor $\frac{r-\ell}{r-q}$ increases with $r$, the rank-deficient case is exact recovery,
  and $r = n$ gives a bound with no rank hypothesis at all, which dominates HMT's (Q1, hard).
- **Two Haar block laws, not three.** Of the brief's §4.3 (v), the column block (a) is the existing
  `hasLaw_mul_const_of_hasLaw_haarFrame` and the polar factor of a wide matrix (c) is the existing
  `polarFactor_eq_pinv_sqrt_mul`. New: the row block (B1) and the corner block (B2).
- **Nyström first, the randomized SVD by the correspondence.** EW's order: the proof lives on Schur
  complements of a positive semidefinite matrix, and 3.2 is 3.6(a) at
  $\mathbf{H} = \mathbf{A}^{\mathsf{H}}\mathbf{A}$, through the same two correspondence lemmas S5
  used in the other direction (Q7).
- **One sharpening of S5 added**: TYUC NeurIPS Theorem 4.2 (4.3) with EW's factor (E7). Gaussian
  twins of the two headline statements are added for discoverability (E3, E4; Q6).

**Literature checks** (EW printed pages, arXiv v2):
- Theorem 3.1 (p. 6): HMT 10.5 for full-rank rotation-invariant $\mathbf{\Omega}$, minimum over
  $q < \ell - \alpha_{\mathbb{K}}$; in the library as S3's I2 and S5's NI2.
- Theorem 3.2 (p. 6): for full-rank $\mathbf{\Omega} \sim \mathbf{U}\mathbf{\Omega}$ and
  $r = \operatorname{rank}\mathbf{A} \ge \ell$,
  $\mathbb{E}\|\mathbf{A} - \mathbf{\Pi}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A}\|_{\mathsf{F}}^2 \le
  \min_{q < \ell - \alpha_{\mathbb{K}}} \frac{r-\ell}{r-q}\bigl(1 + \frac{q}{\ell - q -
  \alpha_{\mathbb{K}}}\bigr)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_q\|_{\mathsf{F}}^2$;
  $\alpha_{\mathbb{R}} = 1$, so $q + 2 \le \ell$. Theorem 3.3 (p. 6) is its lower bound (S10).
- Definition 3.4 and Fact 3.5 (p. 8): Nyström and the trace form of the Gram correspondence (S0).
- Theorem 3.6 (p. 9): (a) the same factor for $\mathbb{E}\operatorname{tr}(\mathbf{H} -
  \mathbf{H}\langle\mathbf{\Omega}\rangle)$, psd $\mathbf{H}$ with $r = \operatorname{rank} \ge \ell$;
  (b) the lower bound (S10). "Theorems 3.2 and 3.3 are equivalent to the following result for
  Nyström approximation."
- Definition 4.1, Theorem 4.2 (pp. 9 to 10): $\mathbf{\Omega}$ rotation-invariant,
  $\mathbf{\Psi} \in \mathbb{K}^{d \times k}$ Gaussian or random orthonormal and independent,
  $\ell + \alpha_{\mathbb{K}} < k$, $\operatorname{rank}\mathbf{A} \ge k$; (a) factor
  $(1 + \gamma\frac{\ell}{k-\ell-\alpha_{\mathbb{K}}})$ times Theorem 3.2's, $\gamma = 1$ or
  $\frac{d-k}{d-\ell}$; its proof (p. 10) is Theorem 2.1's identity followed by Theorem 3.2. The
  hypothesis $\operatorname{rank}\mathbf{A} \ge k$ is the lower bound's; the upper bound needs
  only what Theorem 3.2 needs (§3.5).
- Lemma 5.1 (pp. 11 to 12), Fact 5.3 and Proposition 5.4 (p. 13): S0 and R4, in the library.
- Definition 5.5 and Proposition 5.6 (p. 13): $\mathbb{E}\mathbf{X}^{-1} = (1 + \frac{n-\ell}{\ell -
  r - \alpha})\mathbf{I}$ for $\mathbf{X} \sim \mathrm{Beta}(r, \ell, n)$, through $\operatorname{tr}
  \mathbf{X}^{-1} = r + \operatorname{tr}(\mathbf{W}_1^{-1}\mathbf{W}_2)$. P. 14: "$\mathbf{\Omega}_1$
  can be realized as the top left submatrix of a random unitary matrix", then the polar decomposition
  of $[\mathbf{G}_1\ \mathbf{G}_3]$. B1, B2, B4 below are exactly these three steps, trace only.
- Proposition 5.7 (p. 14) and Lemma 5.8 (p. 15): $R = \mathbf{I}$ is S6; the general $R$ and Lemma
  5.8 are S10 (review A5).
- Fact 6.1 (pp. 17 to 18): (a) to (d), all in the library (S0).
- Lemma 6.2 (pp. 18 to 19): for $a > b$, "$\operatorname{tr}(\ldots) = \operatorname{tr}(b\mathbf{R}_2
  \mathbf{R}_2^{*}(\mathbf{R}_1\mathbf{R}_1^{*} + \frac{b}{a-b}\mathbf{R}_2\mathbf{R}_2^{*})^{-1}) +
  b(r - \ell)$", then the limit by monotone convergence. The final display writes
  $\mathbb{E}\operatorname{tr}(\mathbf{R}_1^{*}\mathbf{R}_1)^{-1}$ where the line before has
  $\mathbf{R}_1\mathbf{R}_1^{*}$; the traces agree ($\mathbf{R}_1$ is square). The QR factor
  $\mathbf{R}$ is not needed: M3 below is the same identity written with
  $\mathbf{\Psi}_1\mathbf{\Psi}_1^{\mathsf{H}}$.
- §6.3 (pp. 19 to 20): a random block permutation "independent from $\mathbf{\Omega}$", then
  "$\mathbb{E}[(\mathbf{P}^{*}\mathbf{\Lambda}\mathbf{P})/\mathbf{\Omega} \mid \mathbf{\Omega}]
  \preceq \mathbb{E}[\mathbf{P}^{*}\mathbf{\Lambda}\mathbf{P}]/\mathbf{\Omega}$", monotonicity,
  Lemma 6.2's limit; "By invoking the Gram correspondence (Fact 3.5), Theorem 3.2 follows."
- No other source is needed. TYUC NeurIPS Theorem 4.2 (p. 6) is the comparison point of E7.

**What is missing, per result** (everything not listed exists and is named in §1 or §3):
- **EW Theorem 3.6(a)** (E1, with E3, E7): (i) the conjugation identity of Nyström for an arbitrary
  factor, M1 (the library has only `HasOrthonormalCols.nystrom_mul_mul_conjTranspose`, where the
  test matrix must be $\mathbf{U}\mathbf{\Omega}$); (ii) the two-level trace identity and its
  inequality, M3 and M4 (the push-through step comes from Mathlib's Woodbury identity
  `Matrix.add_mul_mul_inv_eq_sub`; Loewner antitonicity of the inverse is
  `Matrix.PosDef.inv_le_inv_of_le`; the full-row-rank trace formula is
  `frobNorm_pinv_sq_eq_re_trace_inv_of_injective_conjTranspose`); (iii) the Haar row block B1 and
  corner block B2; (iv) the Beta trace B4 with its integrability B3; (v) the hard instance L-a;
  (vi) the named factor `rotationInvariantFactor` and its registry entry. Fact 6.1(c), (d), the
  sorted spectral decomposition `Matrix.IsHermitian.exists_eq_mul_diagonal_mul_conjTranspose`, the
  Gaussian transfer and the R1, R2, R4 moments exist.
- **EW Theorem 3.2** (E2, E4): nothing beyond E1; the correspondence lemmas
  `nuclearNorm_conjTranspose_mul_self_sub_nystrom` and
  `nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD` and Mathlib's
  `Matrix.rank_conjTranspose_mul_self` exist.
- **EW Theorem 4.2(a)** (S6): Gaussian $\mathbf{\Psi}$, S6's GN identity in shape (b) (missing; its
  algebra `frobNorm_sub_generalizedNystrom_sq` and the block moment
  `integral_frobNorm_pinv_mul_mul_sq_of_hasLaw_gaussianMatrix` exist, the conditioning on
  $\mathbf{\Omega}$ does not); Haar $\mathbf{\Psi}$, additionally EW Proposition 5.7 at
  $\mathbf{R} = \mathbf{I}$ (missing, S6), whose inputs B4 and U2 are S4's.
- **EW Theorem 2.1** (S6): Gaussian, the block moment exists; random orthonormal, Proposition 5.7
  at $\mathbf{R} = \mathbf{I}$ (S6) from B4 and U2 (S4); unbiasedness from U1 (S4).
- **EW Lemma 5.1**: exists (S0: `sketchAndSolve_eq_pinv_mul_add`,
  `frobNorm_one_sub_obliqueProjector_mul_sq`, `conjTranspose_mul_self_one_sub_obliqueProjector_mul`).
- **EW Fact 6.1**: exists (S0: `Matrix.PosSemidef.nystrom`, `.nystrom_le`, `.nystrom_eq_of_range_eq`,
  `sum_smul_sub_nystrom_le`, `Matrix.PosSemidef.sub_nystrom_le_sub_nystrom`).
- **EW Proposition 5.6**, trace form: B4. Its matrix form and the Beta law: not stated (§6).
- **EW Lemma 6.2** at finite $a$, upper half: M3, M4, L-a. The limit: S10.

## 0. Scope and consumers

$\mathbf{H}$ : `Matrix n n ℝ` positive semidefinite (`hH : H.PosSemidef`) or $\mathbf{A}$ :
`Matrix m n ℝ`; the random test matrix `X : Ω → Matrix n l ℝ` with $\ell = \lvert l\rvert$, either
standard Gaussian or with a left unitarily invariant law $\nu$ and full column rank almost surely
(S3's row "rotation-invariant random test matrix"); $q$ the comparison rank, $r$ the rank parameter
(`hr : H.rank ≤ r`, `hlr : Fintype.card l ≤ r`, `hq : q + 2 ≤ Fintype.card l`). Indexing from $0$:
$\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_q\|_* = \sum_{i \ge q}\lambda_i(\mathbf{H})$. The
factor of EW is
$$\rho(r, \ell, q) := \frac{r - \ell}{r - q}\Bigl(1 + \frac{q}{\ell - q - 1}\Bigr) =
\texttt{rotationInvariantFactor r ℓ q}.$$

| Item | Consumers |
|---|---|
| E1 (EW 3.6(a)) and E3 | E2, E7; users with kernel and Gram matrices (the best constant known for Gaussian and Haar test matrices, attained in the worst case); Estimation (trace of the Nyström residual) |
| E2 (EW 3.2) and E4 | S6 (EW 4.2(a) is S6's completion identity times E2, §3.5); S7 (comparison point of CEMT Theorem 2.2's OSI bound); users |
| E7 (TYUC NeurIPS (4.3) with $\rho$) | users of fixed-rank Nyström |
| `rotationInvariantFactor` and its API | E1 to E7, L-a; S6 (4.2(a)); S10 (the matching lower bounds have the same factor) |
| L-a (EW Lemma 6.2, upper half at finite $a$) | E1; S10 (the hard instance) |
| M1 (conjugation of Nyström) | E1's reduction and its cyclic average; S10 ($\tilde{\mathbf{H}} = \mathbf{U}\mathbf{H}\mathbf{U}^{\mathsf{H}}$); reproves the existing equivariance lemma |
| M3, M4 (two-level trace identity and bound) | L-a; S10 (the limit $a \to \infty$ of M3) |
| B1, B2 (Haar row and corner blocks) | B4; S6 (Haar $\mathbf{\Psi}$); S10 (blocks of a Haar unitary) |
| B3, B4 (Beta trace) | L-a; S6 (EW Proposition 5.7 at $\mathbf{R} = \mathbf{I}$, hence EW 2.1 random orthonormal and EW 4.2(a) with Haar $\mathbf{\Psi}$) |
| U1 (coupled law invariance), U2 (coupled conjugation average) | S6 (Proposition 5.7; unbiasedness in EW 2.1). No S4 consumer (Q5) |

Not in S4: the lower bounds, Lemma 6.2's limit, Lemma 5.8, Proposition 5.7 for general $\mathbf{R}$
(S10, D6); EW 2.1, Proposition 5.7 at $\mathbf{R} = \mathbf{I}$, 4.2(a) (S6); complex laws,
$\alpha_{\mathbb{C}} = 0$ (D3); the minimum over $q$ (rule 5).

## 1. Objects

One new definition, no new interface, no §5.3 row, no deviation from Mathlib (no entry in
`Mathlib-deviations.md`).

- **`rotationInvariantFactor (r l q : ℕ) : ℝ := ((r : ℝ) - l) / ((r : ℝ) - q) *
  gaussianProjectionFactor q l`**, the name and body fixed by S3 §1 (D9). A plain `def` with a
  `_def` lemma, because the body is the source's formula. Junk: $r = q$ gives $0$ (Lean's
  $x / 0$); $\ell = q + 1$ makes `gaussianProjectionFactor` junk; theorems carry `hq : q + 2 ≤ l`
  and `hlr : l ≤ r`, which exclude both. API, chosen for the consumers: `rotationInvariantFactor_def`,
  `rotationInvariantFactor_nonneg`, `rotationInvariantFactor_le_gaussianProjectionFactor` (EW's
  factor is at most HMT's), `rotationInvariantFactor_le_rotationInvariantFactor` (monotone in $r$;
  E1's reduction to $r \le n$ uses it). Home: `LowRank/Gaussian/RotationInvariant.lean`, the file
  of its statements (S6's GN file imports it).
- **Registry entry** (`docs/constants.toml`, in the commit that defines it):

  ```toml
  [[constant]]
  name = "NLAlib.rotationInvariantFactor"
  kind = "factor"
  file = "NLAlib/LowRank/Gaussian/RotationInvariant.lean"
  args = ["r", "l", "q"]
  latex = '(#1 - #2)/(#1 - #3) \cdot (1 + #3/(#2 - #3 - 1))'
  lean_body = 'rotationInvariantFactor (r l q : ℕ) : ℝ := ((r : ℝ) - l) / ((r : ℝ) - q) * gaussianProjectionFactor q l'
  ```

  `body_hash` is written by `python3 scripts/check_constants.py --update
  NLAlib.rotationInvariantFactor`. While the definition sits in the side file of §4, `file` names
  the side file; it is changed at the merge. **Docstrings** follow the maintainer's rule of
  2026-10-15 (received while drafting): the value is written inline, in place of the constant,
  inside the equation that uses it, and the marker `<!-- value rotationInvariantFactor r \ell q -->`
  stands on its own line just before that math span; there is never a symbol $C$ with
  "with $C$ = `rotationInvariantFactor r ℓ q`". The Lean statements keep the name. The inline text
  is the filled template, `(r - \ell)/(r - q) \cdot (1 + q/(\ell - q - 1))`, so that the check can
  find it; each docstring passes its own letters (L-a passes `r \ell q` after defining
  $r = \lvert s\rvert + \lvert t\rvert$, $q = \lvert s\rvert$ in words). `gaussianProjectionFactor`
  is not registered (S3 predates the registry rule); Q9.

**Used directly.** Matrix: `nystrom`, `nystrom_def`, `HasOrthonormalCols.nystrom_mul_mul_conjTranspose`,
`Matrix.PosSemidef.nystrom`, `.nystrom_le`, `.nystrom_eq`, `.nystrom_eq_of_range_eq`,
`.sub_nystrom_le_sub_nystrom`, `sum_smul_sub_nystrom_le`, `nuclearNorm_conjTranspose_mul_self_sub_nystrom`,
`nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD`, `nuclearNorm_eq_sum_range`,
`singularValues_sub_truncatedSVD`, `Matrix.PosSemidef.singularValues_eq_eigenvalue`,
`Matrix.PosSemidef.nuclearNorm_eq_re_trace`, `Matrix.IsHermitian.exists_eq_mul_diagonal_mul_conjTranspose`,
`SymmetricGauge.matrixNorm_mul_left_of_hasOrthonormalCols`,
`SymmetricGauge.matrixNorm_mul_conjTranspose_right_of_hasOrthonormalCols`, `lpGauge_one_matrixNorm`,
`Matrix.PosDef.inv_le_inv_of_le`, `frobNorm_pinv_sq_eq_re_trace_inv_of_injective_conjTranspose`,
`polarFactor_eq_pinv_sqrt_mul`, `polarFactor_mul_sqrt`, `hasOrthonormalCols_polarFactor_iff`,
`HasOrthonormalCols.exists_fromCols`, `selectionMatrix`, `hasOrthonormalCols_selectionMatrix`,
`conjTranspose_selectionMatrix_mul`, `eq_smul_one_of_forall_mul_mul_conjTranspose_eq`,
`SymmetricGauge.matrixNorm_sub_truncatedSVD_nystrom_le` (S2a's T2). RandomMatrix: `haarFrame`,
`hasLaw_polarFactor_of_hasLaw_gaussianMatrix`, `hasLaw_conjTranspose_of_hasLaw_haarFrame`,
`hasLaw_mul_const_of_hasLaw_haarFrame`, `hasLaw_polarFactor_of_isLeftUnitarilyInvariant`,
`ae_rank_mul_eq_min_of_hasLaw_haarFrame`, `hasLaw_const_mul_of_isLeftUnitarilyInvariant`,
`integral_eq_integral_gaussianMatrix_of_isLeftUnitarilyInvariant`,
`isLeftUnitarilyInvariant_gaussianMatrix`, `hasLaw_const_mul_of_hasLaw_gaussianMatrix`,
`hasLaw_conjTranspose_of_hasLaw_gaussianMatrix`, `indepFun_conjTranspose_mul_of_hasLaw_gaussianMatrix`,
`ae_rank_eq_min_of_hasLaw_gaussianMatrix`, `integral_frobNorm_mul_mul_sq_of_hasLaw_gaussianMatrix_of_indepFun`,
`integrable_frobNorm_mul_mul_sq_iff_of_hasLaw_gaussianMatrix_of_indepFun`,
`integral_frobNorm_pinv_sq_of_hasLaw_gaussianMatrix`, `integrable_frobNorm_pinv_sq_of_hasLaw_gaussianMatrix`,
`gaussianProjectionFactor_def`. LowRank: `Matrix.PosSemidef.integrable_nuclearNorm_sub_nystrom`,
`Matrix.PosSemidef.integrable_nuclearNorm_sub_truncatedSVD_nystrom`,
`Matrix.PosSemidef.ae_nystrom_eq_self_of_hasLaw_gaussianMatrix`, `ae_rsvd_eq_self_of_hasLaw_gaussianMatrix`.
Mathlib: `Matrix.add_mul_mul_inv_eq_sub` (Woodbury), `Matrix.rank_conjTranspose_mul_self`,
`Matrix.toRows₁`, `Matrix.fromRows_toRows`, `finSumFinEquiv`, `Equiv.addRight`, `Equiv.sumCongr`,
`HasLaw.integral_comp`, `Measure.map_map`, `integral_mono_ae`, `integral_finset_sum`.

**Mathlib search** ("searched, none" unless named): matrix Beta distribution, inverse Wishart
traces, blocks of Haar measure on the orthogonal group, Schur-complement trace formulas,
conjugation of a generalized inverse sandwich (M1), averages of conjugates by permutation matrices
(the permutation-matrix API `Equiv.Perm.permMatrix` has no averaging lemma; not needed, §3.0).

## 2. Interfaces

No new predicate. Hypotheses, each an existing spelling:
- rotation invariance: `HasLaw X ν μ` with `[IsProbabilityMeasure ν] [IsLeftUnitarilyInvariant ν]`
  and `hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec` (S3's row); the Gaussian twins take
  `HasLaw X (gaussianMatrix n l) μ` and no full-rank hypothesis;
- Haar frames: `HasLaw X (haarFrame n k) μ`; a fixed matrix with orthonormal rows is
  `hW : HasOrthonormalCols Wᴴ` (§5.3 "rows are `HasOrthonormalCols Qᴴ`"), one with orthonormal
  columns `hV : HasOrthonormalCols V`; two orthogonal frames `h₁₂ : V₁ᴴ * V₂ = 0`;
- full row rank: `Function.Injective (Ψ.toRows₁)ᴴ.mulVec` (§5.3);
- the rank parameter: `hr : H.rank ≤ r` with `hlr : Fintype.card l ≤ r` (Q1);
- the two-level matrix: `Matrix.fromBlocks (a • (1 : Matrix s s 𝕜)) 0 0 (b • 1)` with real `a b`,
  §5.3's scalar multiple of the identity, inline (Q8).

## 3. Statement shapes

`namespace NLAlib`, `open MeasureTheory ProbabilityTheory`, `open scoped Matrix ComplexOrder
MatrixOrder`. Docstrings are shortened; the full ones carry §5's citations, LaTeX throughout, Lean
names in backticks, and, wherever `rotationInvariantFactor` enters an equation, its value inline
with the marker on the line before the math span (§1).

### 3.0 Degenerate cases and the route of E1

**The route of E1** (the only long proof; private helpers in its file):

| step | content | lemmas |
|---|---|---|
| R0 | reduce to $r \le n$: if $r > \lvert n\rvert$ apply the case $r' = \lvert n\rvert$ (`hXr` gives $\ell \le n$ on a probability space) and monotonicity in $r$ | `rotationInvariantFactor_le_rotationInvariantFactor` |
| R1 | pass to a standard Gaussian: the integrand is $g(\mathbf{P}_{\mathbf{H}^{1/2}\mathbf{X}})$ with $g(\mathbf{P}) = \|\mathbf{H} - \mathbf{H}^{1/2}\mathbf{P}\mathbf{H}^{1/2}\|_*$ | `integral_eq_integral_gaussianMatrix_of_isLeftUnitarilyInvariant`, `Matrix.PosSemidef.nystrom_eq` (under `classical`) |
| R2 | $\mathbf{H} = \mathbf{B}^{\mathsf{H}}\mathbf{D}\mathbf{B}$, $\mathbf{B}$ with orthonormal rows indexed by `Fin q ⊕ Fin d` ($d = r - q \ge 2$), $\mathbf{D} = \operatorname{diag}(\boldsymbol{\sigma}_1, \boldsymbol{\sigma}_2)$, $\sigma_{1,i} = \lambda_i$, $\sigma_{2,j} = \lambda_{q+j}$: the first $r$ sorted eigenvectors, the rest have eigenvalue $0$ | `Matrix.IsHermitian.exists_eq_mul_diagonal_mul_conjTranspose`, `Matrix.PosSemidef.singularValues_eq_eigenvalue`, `finSumFinEquiv` |
| R3 | $\|\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{G})\|_* = \|\mathbf{D} - \mathsf{nystrom}(\mathbf{D}, \mathbf{B}\mathbf{G})\|_*$ and $\mathbf{B}\mathbf{G}$ is a standard Gaussian | M1, gauge invariance at `lpGauge 1`, `hasLaw_const_mul_of_hasLaw_gaussianMatrix` |
| R4 | top block by monotonicity: $\mathbf{D} \preceq \mathbf{D}_a := \operatorname{diag}(\lambda_0\mathbf{1}, \boldsymbol{\sigma}_2)$ | `Matrix.PosSemidef.sub_nystrom_le_sub_nystrom`, trace monotone on PSD |
| R5 | tail block by the cyclic average: for $k \in$ `Fin d`, $\mathbf{P}_k$ the selection matrix of `Equiv.sumCongr (Equiv.refl _) (Equiv.addRight k)`; $\mathbf{P}_k^{\mathsf{H}}\mathbf{B}\mathbf{G}$ has the law of $\mathbf{B}\mathbf{G}$, so by M1 every $\mathbf{P}_k\mathbf{D}_a\mathbf{P}_k^{\mathsf{H}}$ has the expected error of $\mathbf{D}_a$; $\frac1d\sum_k \mathbf{P}_k\mathbf{D}_a\mathbf{P}_k^{\mathsf{H}} = \begin{bmatrix}\lambda_0\mathbf{I} & \mathbf{0}\\ \mathbf{0} & b_0\mathbf{I}\end{bmatrix}$, $b_0 = \frac1d\sum_j\sigma_{2,j}$; concavity | `hasLaw_const_mul_of_isLeftUnitarilyInvariant`, `hasOrthonormalCols_selectionMatrix`, `Fintype.sum_equiv (Equiv.addLeft j)`, `sum_smul_sub_nystrom_le`, `integral_finset_sum` |
| R6 | L-a at $a = \lambda_0$, $b = b_0$; $b_0 d = \sum_j \sigma_{2,j} = \|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_q\|_*$ | L-a, `nuclearNorm_eq_sum_range`, `singularValues_sub_truncatedSVD` |

Integrability at each step: `Matrix.PosSemidef.integrable_nuclearNorm_sub_nystrom` (law-free).
This is EW §6.3 with the review's simplifications: the permutation is fixed, not random (R5); the
average is a finite convex combination of $d$ conjugates, not an expectation (no product space, no
conditional expectation); the top block uses monotonicity instead of averaging, because the bound of
L-a does not depend on $a$; no limit (L-a is at finite $a$).

**The route of L-a** (EW Lemma 6.2 at finite $a$, upper half): (a) by monotonicity replace $a$ by
$\max(a, b)$; (b) $\mathbf{\Psi} := $ `polarFactor (Y ω)` is a Haar frame
(`hasLaw_polarFactor_of_isLeftUnitarilyInvariant`) with orthonormal columns a.s., and
$\mathsf{nystrom}(\mathbf{D}, \mathbf{Y}) = \mathsf{nystrom}(\mathbf{D}, \mathbf{\Psi})$ (equal
ranges, `Matrix.PosSemidef.nystrom_eq_of_range_eq`); (c) $\mathbf{\Psi}_1 = \mathbf{W}\mathbf{\Psi}$
with $\mathbf{W} = $ `(selectionMatrix Sum.inl)ᴴ`, of full row rank a.s.
(`ae_rank_mul_eq_min_of_hasLaw_haarFrame` at $\mathbf{A} = \mathbf{W}$); (d) M4 pointwise, B4 for
the mean, B3 and `integrable_nuclearNorm_sub_nystrom` for `integral_mono_ae`; (e) the algebra
$bq(1 + \frac{r-\ell}{\ell-q-1}) + b(d - \ell) = \rho(r, \ell, q)\,bd$, $r = q + d$.

**Degenerate cases** (checked for every statement; brief §1's checklist):
- *$\ell \in \{q, q+1\}$.* `hq : q + 2 ≤ ℓ` is necessary. At $q = \ell - 1$ the true value of
  $\mathbb{E}\operatorname{tr}((\mathbf{\Psi}_1\mathbf{\Psi}_1^{\mathsf{H}})^{-1})$ is infinite
  (B4's denominator $\ell - q - 1 = 0$), and for the two-level matrix with $a \to \infty$ the
  expected error is unbounded (EW Lemma 6.2's limit), while Lean's $q/0 = 0$ would make E1 claim the
  finite factor $\frac{r-\ell}{r-\ell+1}$. Checked numerically on the hard instance.
- *$r < \ell$.* `hlr` is necessary: for $q < \operatorname{rank}\mathbf{H} \le r < \ell$ the error is
  $0$ a.s. but $\rho < 0$ and the tail is positive, so the right side is negative.
- *$\operatorname{rank}\mathbf{H} > r$.* `hr` is necessary: EW's lower bound (Theorem 3.6(b)) at rank
  $r' > r$ exceeds $\rho(r, \ell, q)$, since $\rho$ increases in $r$.
- *$\operatorname{rank}\mathbf{H} < \ell \le r$.* Exact recovery a.s.; E1 holds with left side $0$
  and $\rho \ge 0$. The route of §3.0 needs no case split (the tail $\boldsymbol{\sigma}_2$ may
  contain zeros; L-a needs only $b \ge 0$).
- *$q \ge \operatorname{rank}\mathbf{H}$.* The tail is $0$ and the error is $0$ a.s. ($q < \ell$).
- *$q = 0$.* $\rho = \frac{r-\ell}{r}$; at the hard instance $b\mathbf{I}_r$ the bound is the exact
  value $b(r - \ell)$.
- *$\ell = r$.* $\rho = 0$, and the error is $0$ a.s. (rank at most $\ell$).
- *$r > n$.* Allowed; R0. *$r = n$*: the bound needs no rank knowledge and is at most HMT's.
- *$\ell > n$.* `hXr` is unsatisfiable (the rotation-invariant statements are vacuous, as S3's);
  the Gaussian twins E3, E4 hold by exact recovery (`ae_nystrom_eq_self_of_hasLaw_gaussianMatrix`,
  `ae_rsvd_eq_self_of_hasLaw_gaussianMatrix`).
- *Empty index types.* $l$ empty is excluded by `hq`. $n$ empty makes `hXr` unsatisfiable. In
  M3, M4: $s$ empty gives the exact value $b(\lvert t\rvert - \ell)$; $t$ empty forces $\ell = q$
  in M4 and both sides are $0$; $l$ empty in M3 gives $aq + b\lvert t\rvert$ on both sides. In
  B1 to B4, $p$ empty gives $0 = 0$.
- *Ties* among eigenvalues: every statement is choice-free (the tail is a sum of eigenvalues,
  Nyström makes no choice; E7's truncated error is choice-free by S2a's T7).
- *Hermitian, not PSD $\mathbf{H}$.* Excluded by `hH`; the route ($\mathbf{H}^{1/2}$, Fact 6.1) and
  the integrability need it; it is the sources' hypothesis.
- *$a < b$ or $a = 0$ in L-a, M4.* Allowed: the bound does not depend on $a$, and
  $b\mathbf{I} + (a-b)\mathbf{X} - a\mathbf{X} = b(\mathbf{I} - \mathbf{X}) \succeq \mathbf{0}$ for
  any $a$. M3 needs $a, b > 0$ (its inverse is junk otherwise). All checked numerically.

### 3.1 Matrix layer (3)

```lean
/-- **Conjugation of Nyström**: for every $\mathbf{B}$, $\mathbf{D}$ and $\mathbf{\Omega}$,
$$\mathsf{nystrom}(\mathbf{B}^{\mathsf{H}}\mathbf{D}\mathbf{B}, \mathbf{\Omega}) =
\mathbf{B}^{\mathsf{H}}\,\mathsf{nystrom}(\mathbf{D}, \mathbf{B}\mathbf{\Omega})\,\mathbf{B}\,:$$
Nyström of a compressed matrix is the compression of Nyström with the compressed test matrix. No
hypothesis; with $\mathbf{B}$ of orthonormal rows the two errors have the same singular values.
[EpperlyWebber2026, §6.3 and proof of Lemma 6.2]; there for unitary and block-selection
$\mathbf{B}$. -/
theorem nystrom_conjTranspose_mul_mul [Fintype p] (B : Matrix p n 𝕜) (D : Matrix p p 𝕜)
    (Ω : Matrix n l 𝕜) : nystrom (Bᴴ * D * B) Ω = Bᴴ * nystrom D (B * Ω) * B

/-- **The trace error of Nyström for a matrix with two eigenvalues**: for $\mathbf{\Psi}$ with
orthonormal columns, rows split as $\mathbf{\Psi}_1$ (indexed by $s$) and $\mathbf{\Psi}_2$, and
$a, b > 0$,
$$\Bigl\|\mathbf{D} - \mathsf{nystrom}(\mathbf{D}, \mathbf{\Psi})\Bigr\|_* =
b(\lvert t\rvert - \ell) + ab\operatorname{tr}\bigl(b\mathbf{I} + (a-b)\mathbf{\Psi}_1
\mathbf{\Psi}_1^{\mathsf{H}}\bigr)^{-1},\qquad
\mathbf{D} = \begin{bmatrix} a\mathbf{I} & \mathbf{0} \\ \mathbf{0} & b\mathbf{I}\end{bmatrix}.$$
[EpperlyWebber2026, proof of Lemma 6.2]; there with $a > b$ through a QR factor of
$\mathbf{\Psi}^{\mathsf{H}}$, here basis-free and for all $a, b > 0$. -/
theorem HasOrthonormalCols.nuclearNorm_fromBlocks_sub_nystrom [DecidableEq l]
    {s t : Type*} [Fintype s] [Fintype t] [DecidableEq s] [DecidableEq t]
    {Ψ : Matrix (s ⊕ t) l 𝕜} (hΨ : HasOrthonormalCols Ψ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    nuclearNorm (Matrix.fromBlocks (a • (1 : Matrix s s 𝕜)) 0 0 (b • 1) -
        nystrom (Matrix.fromBlocks (a • (1 : Matrix s s 𝕜)) 0 0 (b • 1)) Ψ) =
      b * ((Fintype.card t : ℝ) - Fintype.card l) +
        a * b * RCLike.re ((b • (1 : Matrix s s 𝕜) + (a - b) • (Ψ.toRows₁ * (Ψ.toRows₁)ᴴ))⁻¹).trace

/-- **The pointwise bound behind Epperly and Webber's sharp bounds**: with the notation of
`HasOrthonormalCols.nuclearNorm_fromBlocks_sub_nystrom`, $\mathbf{\Psi}_1$ of full row rank and
any $a, b \ge 0$,
$$\|\mathbf{D} - \mathsf{nystrom}(\mathbf{D}, \mathbf{\Psi})\|_* \le
b\,\|\mathbf{\Psi}_1^{+}\|_{\mathsf{F}}^2 + b(\lvert t\rvert - \ell)\,,$$
independent of $a$: the error of the two-level matrix is at most its limit as $a \to \infty$.
[EpperlyWebber2026, proof of Lemma 6.2]; there as a limit under monotone convergence, here a
pointwise inequality at every $a$ (Loewner antitonicity of the inverse). -/
theorem HasOrthonormalCols.nuclearNorm_fromBlocks_sub_nystrom_le [DecidableEq l]
    {s t : Type*} [Fintype s] [Fintype t] [DecidableEq s] [DecidableEq t]
    {Ψ : Matrix (s ⊕ t) l 𝕜} (hΨ : HasOrthonormalCols Ψ)
    (hΨ₁ : Function.Injective (Ψ.toRows₁)ᴴ.mulVec) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    nuclearNorm (Matrix.fromBlocks (a • (1 : Matrix s s 𝕜)) 0 0 (b • 1) -
        nystrom (Matrix.fromBlocks (a • (1 : Matrix s s 𝕜)) 0 0 (b • 1)) Ψ) ≤
      b * frobNorm (pinv Ψ.toRows₁) ^ 2 + b * ((Fintype.card t : ℝ) - Fintype.card l)
```

Proof routes. *M1:* `nystrom_def` on both sides, `Matrix.conjTranspose_mul`, `Matrix.mul_assoc`;
two lines. `HasOrthonormalCols.nystrom_mul_mul_conjTranspose` is M1 at $\mathbf{B} =
\mathbf{U}^{\mathsf{H}}$ and test matrix $\mathbf{U}\mathbf{\Omega}$ ($\mathbf{U}^{\mathsf{H}}
\mathbf{U}\mathbf{\Omega} = \mathbf{\Omega}$) and is reproved from it, name kept (rule 6). *M3:*
`Matrix.fromRows_toRows`; $\mathbf{\Psi}^{\mathsf{H}}\mathbf{D}\mathbf{\Psi} = b\mathbf{I} + (a-b)
\mathbf{\Psi}_1^{\mathsf{H}}\mathbf{\Psi}_1$ (from $\mathbf{\Psi}_1^{\mathsf{H}}\mathbf{\Psi}_1 +
\mathbf{\Psi}_2^{\mathsf{H}}\mathbf{\Psi}_2 = \mathbf{I}$), positive definite because its
eigenvalues lie in $[\min(a,b), \max(a,b)]$, so `pinv` is the inverse; $\mathbf{\Psi}^{\mathsf{H}}
\mathbf{D}^2\mathbf{\Psi} = (a+b)\mathbf{\Psi}^{\mathsf{H}}\mathbf{D}\mathbf{\Psi} - ab\mathbf{I}$,
so $\operatorname{tr}\mathsf{nystrom} = (a+b)\ell - ab\operatorname{tr}(\mathbf{\Psi}^{\mathsf{H}}
\mathbf{D}\mathbf{\Psi})^{-1}$; the push-through identity $\operatorname{tr}(b\mathbf{I}_l +
c\mathbf{K}^{\mathsf{H}}\mathbf{K})^{-1} = \frac{\ell - \lvert s\rvert}{b} + \operatorname{tr}
(b\mathbf{I}_s + c\mathbf{K}\mathbf{K}^{\mathsf{H}})^{-1}$ (private, from Mathlib's Woodbury
`Matrix.add_mul_mul_inv_eq_sub` and trace cyclicity, valid while both are invertible); the nuclear
norm is the real trace (`Matrix.PosSemidef.nuclearNorm_eq_re_trace`, the error being PSD). About 80
lines in three private helpers. *M4:* $b = 0$: Nyström is exact, since
$\operatorname{rank}(\mathbf{D}\mathbf{\Psi}) = \operatorname{rank}\mathbf{\Psi}_1 = \lvert s\rvert =
\operatorname{rank}\mathbf{D}$ (`Matrix.PosSemidef.nystrom_eq_self_of_rank_eq`), and both sides are
$0$; $a = 0 < b$: monotonicity, $\mathbf{D} \preceq b\mathbf{I}$, whose error is
$b(\lvert s\rvert + \lvert t\rvert - \ell)$, and $\|\mathbf{\Psi}_1^{+}\|_{\mathsf{F}}^2 \ge
\lvert s\rvert$ since $\mathbf{X} := \mathbf{\Psi}_1\mathbf{\Psi}_1^{\mathsf{H}} \preceq \mathbf{I}$;
otherwise M3 and
$b\mathbf{I} + (a-b)\mathbf{X} \succeq a\mathbf{X} \succ \mathbf{0}$ (the difference is
$b(\mathbf{I} - \mathbf{X})$), `Matrix.PosDef.inv_le_inv_of_le`, trace monotonicity, and
`frobNorm_pinv_sq_eq_re_trace_inv_of_injective_conjTranspose`. About 40 lines.

### 3.2 `RandomMatrix/Haar/Blocks.lean` (new): blocks of a Haar frame (4)

Real; `{n k p : Type*} [Fintype n] [Fintype k] [Fintype p] {X : Ω → Matrix n k ℝ}`.

```lean
/-- **Row blocks of a Haar frame with orthonormal rows**: for an $n \times k$ Haar frame
$\mathbf{Q}$ with $\lvert n\rvert \le \lvert k\rvert$ (orthonormal rows; a Haar orthogonal matrix
for $n = k$) and a fixed $\mathbf{W}$ with orthonormal rows, $\mathbf{W}\mathbf{Q}$ is a $p \times k$
Haar frame. The row twin of `hasLaw_mul_const_of_hasLaw_haarFrame`.
[Meckes2019, Ch. 1]; [EpperlyWebber2026, p. 14], there the first rows of a Haar unitary.
Result: haar-frame-block-law -/
theorem hasLaw_const_mul_of_hasLaw_haarFrame [DecidableEq n] [DecidableEq k] [DecidableEq p]
    (hX : HasLaw X (haarFrame n k) μ) (hnk : Fintype.card n ≤ Fintype.card k)
    {W : Matrix p n ℝ} (hW : HasOrthonormalCols Wᴴ) :
    HasLaw (fun ω => W * X ω) (haarFrame p k) μ

/-- **Corner blocks of a Haar frame**: for an $n \times k$ Haar frame $\mathbf{Q}$, a fixed
$\mathbf{W}$ with orthonormal rows and any fixed frame $\mathbf{V}$ ($n \times k$, orthonormal
columns), $\mathbf{W}\mathbf{Q}$ has the law of $\mathbf{P}\mathbf{V}$ for a $p \times n$ Haar frame
$\mathbf{P}$ (orthonormal rows), that is of $(\mathbf{G}\mathbf{G}^{\mathsf{H}})^{-1/2}\mathbf{G}
\mathbf{V}$ for a standard Gaussian $\mathbf{G}$. The top left block of a Haar orthogonal matrix,
seen through its rows. [EpperlyWebber2026, p. 14].
Result: haar-frame-block-law -/
theorem hasLaw_const_mul_of_hasLaw_haarFrame_of_hasOrthonormalCols [DecidableEq n]
    [DecidableEq k] [DecidableEq p] (hX : HasLaw X (haarFrame n k) μ) {W : Matrix p n ℝ}
    (hW : HasOrthonormalCols Wᴴ) {V : Matrix n k ℝ} (hV : HasOrthonormalCols V) :
    HasLaw (fun ω => W * X ω) ((haarFrame p n).map (· * V)) μ

/-- $\|(\mathbf{W}\mathbf{Q})^{+}\|_{\mathsf{F}}^2$ is integrable for a Haar frame $\mathbf{Q}$
with $\lvert k\rvert \le \lvert n\rvert$, $\mathbf{W}$ with orthonormal rows and
$\lvert p\rvert + 2 \le \lvert k\rvert$. -/
theorem integrable_frobNorm_pinv_const_mul_sq_of_hasLaw_haarFrame [DecidableEq n]
    [DecidableEq k] [DecidableEq p] (hX : HasLaw X (haarFrame n k) μ)
    (hkn : Fintype.card k ≤ Fintype.card n) {W : Matrix p n ℝ} (hW : HasOrthonormalCols Wᴴ)
    (hpk : Fintype.card p + 2 ≤ Fintype.card k) :
    Integrable (fun ω => frobNorm (pinv (W * X ω)) ^ 2) μ

/-- **The inverse mean of a Beta matrix, trace form**: for an $n \times k$ Haar frame
$\mathbf{Q}$, $\mathbf{W}$ with $p$ orthonormal rows and $p + 2 \le k \le n$,
$$\mathbb{E}\|(\mathbf{W}\mathbf{Q})^{+}\|_{\mathsf{F}}^2 =
\mathbb{E}\operatorname{tr}\bigl((\mathbf{W}\mathbf{Q}\mathbf{Q}^{\mathsf{H}}
\mathbf{W}^{\mathsf{H}})^{-1}\bigr) = p\Bigl(1 + \frac{n-k}{k-p-1}\Bigr).$$
$\mathbf{W}\mathbf{Q}\mathbf{Q}^{\mathsf{H}}\mathbf{W}^{\mathsf{H}}$ is a Beta matrix; its law is
not used. At $n = k$ the value is $p$ ($\mathbf{W}\mathbf{Q}$ has orthonormal rows).
[EpperlyWebber2026, Proposition 5.6]; there the matrix $\mathbb{E}\mathbf{X}^{-1}$ over
$\mathbb{R}$ and $\mathbb{C}$, here its trace over $\mathbb{R}$, the only part their Proposition 5.7
and Lemma 6.2 use.
Result: beta-matrix-inverse-mean -/
theorem integral_frobNorm_pinv_const_mul_sq_of_hasLaw_haarFrame [DecidableEq n]
    [DecidableEq k] [DecidableEq p] (hX : HasLaw X (haarFrame n k) μ)
    (hkn : Fintype.card k ≤ Fintype.card n) {W : Matrix p n ℝ} (hW : HasOrthonormalCols Wᴴ)
    (hpk : Fintype.card p + 2 ≤ Fintype.card k) :
    ∫ ω, frobNorm (pinv (W * X ω)) ^ 2 ∂μ =
      Fintype.card p * (1 + ((Fintype.card n : ℝ) - Fintype.card k) /
        ((Fintype.card k : ℝ) - Fintype.card p - 1))
```

Proof routes. *B1:* `hasLaw_conjTranspose_of_hasLaw_haarFrame` ($\mathbf{Q}^{\mathsf{H}}$ is a
$k \times n$ Haar frame, tall), `hasLaw_mul_const_of_hasLaw_haarFrame` with $\mathbf{V} =
\mathbf{W}^{\mathsf{H}}$, conjugate transpose back. *B2:* the sub-frame lemma at
$\mathbf{Q} = $ `id` on `haarFrame n n` gives `haarFrame n k = (haarFrame n n).map (· * V)`; then
`(haarFrame n k).map (W * ·) = ((haarFrame n n).map (W * ·)).map (· * V)` (`Measure.map_map`) and
B1 at $n = k$. *B4:* complete $\mathbf{V}$ by $\mathbf{V}'$ (`HasOrthonormalCols.exists_fromCols`);
by B2 and the definition of `haarFrame`, the expectation is that of $f(\mathbf{G}) =
\|(\operatorname{polar}(\mathbf{G})\mathbf{V})^{+}\|_{\mathsf{F}}^2$ for a $p \times n$ standard
Gaussian $\mathbf{G}$; with $\mathbf{K} = \mathbf{G}\mathbf{V}$, $\mathbf{L} = \mathbf{G}\mathbf{V}'$
(independent standard Gaussians, `indepFun_conjTranspose_mul_of_hasLaw_gaussianMatrix` on
$\mathbf{G}^{\mathsf{H}}$) and `polarFactor_eq_pinv_sqrt_mul`, a private Matrix identity gives
$f(\mathbf{G}) = p + \|\mathbf{K}^{+}\mathbf{L}\|_{\mathsf{F}}^2$ whenever $\mathbf{K}$ has full row
rank (a.s.): $\operatorname{tr}\bigl((\mathbf{K}\mathbf{K}^{\mathsf{H}})^{-1}(\mathbf{K}
\mathbf{K}^{\mathsf{H}} + \mathbf{L}\mathbf{L}^{\mathsf{H}})\bigr)$; then
`integral_frobNorm_mul_mul_sq_of_hasLaw_gaussianMatrix_of_indepFun` ($\mathbf{S} = \mathbf{K}^{+}$,
$\mathbf{T} = \mathbf{I}_{n-k}$) and `integral_frobNorm_pinv_sq_of_hasLaw_gaussianMatrix` give
$p + (n - k)\frac{p}{k-p-1}$. This is the brief's §4.3 (iii) with $\mathbf{W}_1 = \mathbf{K}
\mathbf{K}^{\mathsf{H}}$, $\mathbf{W}_2 = \mathbf{L}\mathbf{L}^{\mathsf{H}}$. *B3:* the same
reduction and `integrable_frobNorm_mul_mul_sq_iff_of_hasLaw_gaussianMatrix_of_indepFun`. About
220 lines; B4 is the longest proof of the stage after E1.

### 3.3 `RandomMatrix/UnitaryInvariance.lean` (registered): coupled invariance (2)

Over `𝕜`; frames $\mathbf{V}_1$ ($n \times s$), $\mathbf{V}_2$ ($n \times t$, orthonormal columns),
$\mathbf{V}_1^{\mathsf{H}}\mathbf{V}_2 = \mathbf{0}$; $\mathbf{V}_1$ need not be a frame.

```lean
/-- **Rotating one block keeps the joint law**: for $\mathbf{X}$ with a left unitarily invariant
law and every unitary $\mathbf{U}$ on $t$, $(\mathbf{V}_1^{\mathsf{H}}\mathbf{X},
\mathbf{U}\mathbf{V}_2^{\mathsf{H}}\mathbf{X})$ has the law of $(\mathbf{V}_1^{\mathsf{H}}\mathbf{X},
\mathbf{V}_2^{\mathsf{H}}\mathbf{X})$. The block-diagonal rotation
$\mathbf{I} - \mathbf{V}_2\mathbf{V}_2^{\mathsf{H}} + \mathbf{V}_2\mathbf{U}\mathbf{V}_2^{\mathsf{H}}$
is unitary and fixes the first block.
[EpperlyWebber2026, proofs of Theorem 2.1 and Proposition 5.7]. -/
theorem hasLaw_prodMk_conjTranspose_mul_of_isLeftUnitarilyInvariant [DecidableEq n]
    {s t : Type*} [Fintype s] [Fintype t] [DecidableEq t] {ν : Measure (Matrix n k 𝕜)}
    [IsLeftUnitarilyInvariant ν] {X : Ω → Matrix n k 𝕜} (hX : HasLaw X ν μ)
    {V₁ : Matrix n s 𝕜} {V₂ : Matrix n t 𝕜} (hV₂ : HasOrthonormalCols V₂) (h₁₂ : V₁ᴴ * V₂ = 0)
    {U : Matrix t t 𝕜} (hU : HasOrthonormalCols U) :
    HasLaw (fun ω => (V₁ᴴ * X ω, U * (V₂ᴴ * X ω))) (ν.map fun x => (V₁ᴴ * x, V₂ᴴ * x)) μ

/-- **The coupled conjugation average**: for $\mathbf{X}$ with a left unitarily invariant law and
measurable $F$, if $\mathbf{Z} = \mathbf{V}_2^{\mathsf{H}}\mathbf{X}\,F(\mathbf{V}_1^{\mathsf{H}}
\mathbf{X})\,(\mathbf{V}_2^{\mathsf{H}}\mathbf{X})^{\mathsf{H}}$ is integrable then
$$\mathbb{E}\mathbf{Z} = \frac{\mathbb{E}\operatorname{tr}\mathbf{Z}}{\lvert t\rvert}\,\mathbf{I}\,,$$
although the middle factor depends on $\mathbf{X}$. The case of a fixed middle factor is
`integral_mul_mul_conjTranspose_of_isLeftUnitarilyInvariant`.
[EpperlyWebber2026, proof of Proposition 5.7]; there for a random orthonormal matrix. -/
theorem integral_conjTranspose_mul_mul_mul_conjTranspose_of_isLeftUnitarilyInvariant
    [DecidableEq n] {s t : Type*} [Fintype s] [Fintype t] [DecidableEq t]
    {ν : Measure (Matrix n k 𝕜)} [IsLeftUnitarilyInvariant ν] {X : Ω → Matrix n k 𝕜}
    (hX : HasLaw X ν μ) {V₁ : Matrix n s 𝕜} {V₂ : Matrix n t 𝕜} (hV₂ : HasOrthonormalCols V₂)
    (h₁₂ : V₁ᴴ * V₂ = 0) {F : Matrix s k 𝕜 → Matrix k k 𝕜} (hF : Measurable F)
    (hint : Integrable (fun ω => V₂ᴴ * X ω * F (V₁ᴴ * X ω) * (V₂ᴴ * X ω)ᴴ) μ) :
    ∫ ω, V₂ᴴ * X ω * F (V₁ᴴ * X ω) * (V₂ᴴ * X ω)ᴴ ∂μ =
      ((∫ ω, (V₂ᴴ * X ω * F (V₁ᴴ * X ω) * (V₂ᴴ * X ω)ᴴ).trace ∂μ) / Fintype.card t) •
        (1 : Matrix t t 𝕜)
```

Proof routes. *U1:* $\mathbf{R} := \mathbf{I} - \mathbf{V}_2\mathbf{V}_2^{\mathsf{H}} +
\mathbf{V}_2\mathbf{U}\mathbf{V}_2^{\mathsf{H}}$ has orthonormal columns, $\mathbf{V}_1^{\mathsf{H}}
\mathbf{R} = \mathbf{V}_1^{\mathsf{H}}$, $\mathbf{V}_2^{\mathsf{H}}\mathbf{R} = \mathbf{U}
\mathbf{V}_2^{\mathsf{H}}$; `hasLaw_const_mul_of_isLeftUnitarilyInvariant` and `HasLaw.fun_comp`.
*U2:* as `integral_mul_mul_conjTranspose_of_isLeftUnitarilyInvariant`: U1 shows
$\mathbf{U}(\mathbb{E}\mathbf{Z})\mathbf{U}^{\mathsf{H}} = \mathbb{E}\mathbf{Z}$ for every unitary
$\mathbf{U}$, then `eq_smul_one_of_forall_mul_mul_conjTranspose_eq` (the signed-permutation
argument, already in the library) and `Matrix.integral_trace`. About 70 lines.

### 3.4 `LowRank/Gaussian/RotationInvariant.lean` (registered; S5 extended it): the sharp bounds (11)

Hypotheses as S3 §3.6 for the section variables: `[DecidableEq n] {ν : Measure (Matrix n l ℝ)}
[IsProbabilityMeasure ν] [IsLeftUnitarilyInvariant ν] (hX : HasLaw X ν μ)
(hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec)`, written `(hX) (hXr)` below. L-a has its own
law on `Matrix (s ⊕ t) l ℝ` and sits in a section before those variables. Labels F0 to F4, L-a,
E1 to E4, E7.

```lean
/-- **Epperly and Webber's factor**
<!-- value rotationInvariantFactor r \ell q -->
$(r - \ell)/(r - q) \cdot (1 + q/(\ell - q - 1))$: the sharp expected
squared Frobenius error of the randomized SVD, relative to the best rank-$q$ error, over matrices
of rank $r$ and full-rank rotation-invariant test matrices with $\ell$ columns. A plain definition,
because its body is the source's formula. Junk: $0$ at $r = q$; theorems carry
$q + 2 \le \ell \le r$. [EpperlyWebber2026, Theorems 3.2, 3.3]. -/
noncomputable def rotationInvariantFactor (r l q : ℕ) : ℝ :=
  ((r : ℝ) - l) / ((r : ℝ) - q) * gaussianProjectionFactor q l
theorem rotationInvariantFactor_def (r l q : ℕ) :
    rotationInvariantFactor r l q =
      ((r : ℝ) - l) / ((r : ℝ) - q) * (1 + (q : ℝ) / ((l : ℝ) - q - 1))
theorem rotationInvariantFactor_nonneg {r l q : ℕ} (hq : q + 2 ≤ l) (hl : l ≤ r) :
    0 ≤ rotationInvariantFactor r l q
/-- Epperly and Webber's factor is at most HMT's, `gaussianProjectionFactor q l`. -/
theorem rotationInvariantFactor_le_gaussianProjectionFactor {r l q : ℕ} (hq : q + 2 ≤ l)
    (hl : l ≤ r) : rotationInvariantFactor r l q ≤ gaussianProjectionFactor q l
/-- Epperly and Webber's factor increases with the rank parameter. -/
theorem rotationInvariantFactor_le_rotationInvariantFactor {r r' l q : ℕ} (hq : q + 2 ≤ l)
    (hl : l ≤ r) (hr : r ≤ r') : rotationInvariantFactor r l q ≤ rotationInvariantFactor r' l q

/-- **Nyström for a matrix with two eigenvalues** (the hard instance): for $\mathbf{Y}$ on
$(s \oplus t) \times l$ with a left unitarily invariant law and full column rank almost surely,
$q = \lvert s\rvert$, $r = \lvert s\rvert + \lvert t\rvert$, $q + 2 \le \ell$ and $a, b \ge 0$,
<!-- value rotationInvariantFactor r \ell q -->
$$\mathbb{E}\Bigl\|\mathbf{D} - \mathsf{nystrom}(\mathbf{D}, \mathbf{Y})\Bigr\|_* \le
(r - \ell)/(r - q) \cdot (1 + q/(\ell - q - 1))\,b\,\lvert t\rvert,\qquad
\mathbf{D} = \begin{bmatrix} a\mathbf{I} & \mathbf{0} \\ \mathbf{0} & b\mathbf{I}\end{bmatrix},$$
that is $b(r - \ell)(1 + \frac{q}{\ell-q-1})$; $b\lvert t\rvert$ is the best rank-$q$ trace error
when $a \ge b$. [EpperlyWebber2026, Lemma 6.2]; there the limit as
$a \to \infty$ (an equality), here the upper bound at every $a$.
Result: nystrom-two-eigenvalue-instance -/
theorem integral_nuclearNorm_fromBlocks_sub_nystrom_le_of_isLeftUnitarilyInvariant
    {s t : Type*} [Fintype s] [Fintype t] [DecidableEq s] [DecidableEq t]
    {ν' : Measure (Matrix (s ⊕ t) l ℝ)} [IsProbabilityMeasure ν'] [IsLeftUnitarilyInvariant ν']
    {Y : Ω → Matrix (s ⊕ t) l ℝ} (hY : HasLaw Y ν' μ)
    (hYr : ∀ᵐ ω ∂μ, Function.Injective (Y ω).mulVec) (hsl : Fintype.card s + 2 ≤ Fintype.card l)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∫ ω, nuclearNorm (Matrix.fromBlocks (a • (1 : Matrix s s ℝ)) 0 0 (b • 1) -
        nystrom (Matrix.fromBlocks (a • (1 : Matrix s s ℝ)) 0 0 (b • 1)) (Y ω)) ∂μ ≤
      rotationInvariantFactor (Fintype.card s + Fintype.card t) (Fintype.card l)
        (Fintype.card s) * (b * Fintype.card t)

/-- **The sharp expected trace error of randomized Nyström, rotation-invariant test matrices**:
for positive semidefinite $\mathbf{H}$ of rank at most $r$, a test matrix $\mathbf{X}$ with a left
unitarily invariant law and full column rank almost surely (Gaussian, Haar, ...),
$\ell \le r$ and $q + 2 \le \ell$,
<!-- value rotationInvariantFactor r \ell q -->
$$\mathbb{E}\|\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{X})\|_* \le
(r - \ell)/(r - q) \cdot (1 + q/(\ell - q - 1))\,\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_q\|_*\,.$$
At $r = \operatorname{rank}
\mathbf{H}$ it is attained in the worst case ([EpperlyWebber2026, Theorem 3.6(b)]); at $r = n$ it
needs no knowledge of the rank. It is at most HMT's factor
(`rotationInvariantFactor_le_gaussianProjectionFactor`), so it sharpens
`Matrix.PosSemidef.integral_nuclearNorm_sub_nystrom_le_of_isLeftUnitarilyInvariant`.
[EpperlyWebber2026, Theorem 3.6(a)]; there over $\mathbb{R}$ and $\mathbb{C}$ with
$r = \operatorname{rank}\mathbf{H} \ge \ell$ and a minimum over $q$; here over $\mathbb{R}$, any
$r \ge \max(\operatorname{rank}\mathbf{H}, \ell)$, at each $q$.
Result: randomized-nystrom-expected-error -/
theorem
    _root_.Matrix.PosSemidef.integral_nuclearNorm_sub_nystrom_le_of_isLeftUnitarilyInvariant_of_rank_le
    {H : Matrix n n ℝ} (hH : H.PosSemidef) (hX) (hXr) {r q : ℕ} (hr : H.rank ≤ r)
    (hlr : Fintype.card l ≤ r) (hq : q + 2 ≤ Fintype.card l) :
    ∫ ω, nuclearNorm (H - nystrom H (X ω)) ∂μ ≤
      rotationInvariantFactor r (Fintype.card l) q * nuclearNorm (H - truncatedSVD H q)

/-- **The sharp expected error of the randomized SVD, rotation-invariant test matrices**: for
$\mathbf{A}$ of rank at most $r$, $\ell \le r$ and $q + 2 \le \ell$,
<!-- value rotationInvariantFactor r \ell q -->
$$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X})\|_{\mathsf{F}}^2 \le
(r - \ell)/(r - q) \cdot (1 + q/(\ell - q - 1))\,\|\mathbf{A} -
\llbracket\mathbf{A}\rrbracket_q\|_{\mathsf{F}}^2\,;$$
the factor is at most HMT's, so it
sharpens `integral_frobNorm_sub_rsvd_sq_le_of_isLeftUnitarilyInvariant`. The Nyström bound at
$\mathbf{H} = \mathbf{A}^{\mathsf{H}}\mathbf{A}$, by the Gram correspondence.
[EpperlyWebber2026, Theorem 3.2]; there with $r = \operatorname{rank}\mathbf{A} \ge \ell$ and a
minimum over $q$, over $\mathbb{R}$ and $\mathbb{C}$.
Result: randomized-svd-expected-error -/
theorem integral_frobNorm_sub_rsvd_sq_le_of_isLeftUnitarilyInvariant_of_rank_le
    (A : Matrix m n ℝ) (hX) (hXr) {r q : ℕ} (hr : A.rank ≤ r) (hlr : Fintype.card l ≤ r)
    (hq : q + 2 ≤ Fintype.card l) :
    ∫ ω, frobNorm (A - rsvd A (X ω)) ^ 2 ∂μ ≤
      rotationInvariantFactor r (Fintype.card l) q * frobNorm (A - truncatedSVD A q) ^ 2

/-- The same for a standard Gaussian test matrix, every $\ell$ (for $\ell > n$ Nyström is exact
almost surely). [EpperlyWebber2026, Theorem 3.6(a)].
Result: randomized-nystrom-expected-error -/
theorem
    _root_.Matrix.PosSemidef.integral_nuclearNorm_sub_nystrom_le_of_hasLaw_gaussianMatrix_of_rank_le
    {H : Matrix n n ℝ} (hH : H.PosSemidef) (hX : HasLaw X (gaussianMatrix n l) μ) {r q : ℕ}
    (hr : H.rank ≤ r) (hlr : Fintype.card l ≤ r) (hq : q + 2 ≤ Fintype.card l) :
    ∫ ω, nuclearNorm (H - nystrom H (X ω)) ∂μ ≤
      rotationInvariantFactor r (Fintype.card l) q * nuclearNorm (H - truncatedSVD H q)

/-- The same for a standard Gaussian test matrix. [EpperlyWebber2026, Theorem 3.2].
Result: randomized-svd-expected-error -/
theorem integral_frobNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix_of_rank_le
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {r q : ℕ} (hr : A.rank ≤ r)
    (hlr : Fintype.card l ≤ r) (hq : q + 2 ≤ Fintype.card l) :
    ∫ ω, frobNorm (A - rsvd A (X ω)) ^ 2 ∂μ ≤
      rotationInvariantFactor r (Fintype.card l) q * frobNorm (A - truncatedSVD A q) ^ 2

/-- **Truncated Nyström exploits spectral decay, with Epperly and Webber's factor**: for any target
rank $k$ and comparison rank $q$ with $q + 2 \le \ell \le r$, every choice of the truncation,
<!-- value rotationInvariantFactor r \ell q -->
$$\mathbb{E}\|\mathbf{H} - \llbracket\mathsf{nystrom}(\mathbf{H}, \mathbf{X})\rrbracket_k\|_* \le
\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_* + (r - \ell)/(r - q) \cdot (1 + q/(\ell - q - 1))
\,\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_q\|_*\,.$$
Better than
`Matrix.PosSemidef.integral_nuclearNorm_sub_truncatedSVD_nystrom_le_add_of_hasLaw_gaussianMatrix`'s
$1 + \frac{q}{\ell-q-1}$ by the factor $\frac{r-\ell}{r-q}$; at $q = k$ dominated by the
truncated trace bound with $1 + \frac{k}{\ell-k-1}$, incomparable for $q > k$.
[TroppYurtseverUdellCevher2017a, Theorem 4.2 (4.3)]; [EpperlyWebber2026, Theorem 3.6(a)]; there
with the constant $2$ and HMT's factor.
Result: randomized-nystrom-expected-error -/
theorem
    _root_.Matrix.PosSemidef.integral_nuclearNorm_sub_truncatedSVD_nystrom_le_add_of_isLeftUnitarilyInvariant_of_rank_le
    {H : Matrix n n ℝ} (hH : H.PosSemidef) (hX) (hXr) (k : ℕ) {r q : ℕ} (hr : H.rank ≤ r)
    (hlr : Fintype.card l ≤ r) (hq : q + 2 ≤ Fintype.card l) :
    ∫ ω, nuclearNorm (H - truncatedSVD (nystrom H (X ω)) k) ∂μ ≤
      nuclearNorm (H - truncatedSVD H k) +
        rotationInvariantFactor r (Fintype.card l) q * nuclearNorm (H - truncatedSVD H q)
```

Proof routes. *F1 to F4:* `field_simp`, `gaussianProjectionFactor_def`; F4 from
$\frac{r-\ell}{r-q} = 1 - \frac{\ell-q}{r-q}$ increasing in $r$. *L-a, E1:* §3.0. *E2:* E1 at
$\mathbf{H} = \mathbf{A}^{\mathsf{H}}\mathbf{A}$ (`Matrix.posSemidef_conjTranspose_mul_self`,
`Matrix.rank_conjTranspose_mul_self`), the integrand by
`nuclearNorm_conjTranspose_mul_self_sub_nystrom`, the right side by
`nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD`; S5's common step read backwards. *E3, E4:*
by cases on $\ell \le n$: E1, E2 with $\nu$ = `gaussianMatrix n l`
(`isLeftUnitarilyInvariant_gaussianMatrix`; `hXr` from `ae_rank_eq_min_of_hasLaw_gaussianMatrix`);
otherwise exact recovery and F2. *E7:* pointwise T2 at `lpGauge 1`
(`SymmetricGauge.matrixNorm_sub_truncatedSVD_nystrom_le`, `lpGauge_one_matrixNorm`), then
`integral_mono` (`integrable_nuclearNorm_sub_truncatedSVD_nystrom`, `integrable_nuclearNorm_sub_nystrom`
plus a constant) and E1. The names of E1 and E7 exceed 100 characters with their prefix; `theorem`
on its own line and, where still too long, `set_option linter.style.longLine false in` with a
comment (S5 §8 item 12).

### 3.5 The composition S6 will state (not S4's; recorded for the consumer check)

EW Theorem 4.2(a), Gaussian $\mathbf{\Psi}$, in the library's letters ($\mathbf{A}$ : `Matrix m n ℝ`,
`Ψ : Ω → Matrix m p ℝ` independent of `X`):

```lean
theorem integral_frobNorm_sub_generalizedNystrom_sq_le_of_isLeftUnitarilyInvariant_of_rank_le
    (A : Matrix m n ℝ) (hX) (hXr) (hΨ : HasLaw Ψ (gaussianMatrix m p) μ) (hXΨ : IndepFun X Ψ μ)
    {r q : ℕ} (hr : A.rank ≤ r) (hlr : Fintype.card l ≤ r) (hq : q + 2 ≤ Fintype.card l)
    (hlp : Fintype.card l + 2 ≤ Fintype.card p) :
    ∫ ω, frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2 ∂μ ≤
      gaussianProjectionFactor (Fintype.card l) (Fintype.card p) *
        rotationInvariantFactor r (Fintype.card l) q * frobNorm (A - truncatedSVD A q) ^ 2
```

It is S6's shape (b) identity (with $\operatorname{rank}(\mathbf{A}\mathbf{X}) = \ell$ a.s. when
$\operatorname{rank}\mathbf{A} \ge \ell$, and exact recovery otherwise) followed by E2. EW's
hypothesis $\operatorname{rank}\mathbf{A} \ge p$ is not needed for the upper bound. The Haar twin
replaces `gaussianProjectionFactor ℓ p` by `haarProjectionFactor m p ℓ` and needs EW Proposition
5.7 at $\mathbf{R} = \mathbf{I}$, which S6 proves from B4 (at $\mathbf{W} = \mathbf{Q}^{\mathsf{H}}$)
and U2 (at $\mathbf{V}_1 = \mathbf{Q}$, $\mathbf{V}_2 = \mathbf{Q}_\perp$, $F(\mathbf{M}) =
\mathbf{M}^{+}(\mathbf{M}^{+})^{\mathsf{H}}$); EW Theorem 2.1's random orthonormal case is the same
computation, its unbiasedness U1 at $\mathbf{U} = -\mathbf{I}$.

### 3.6 Dependency table

| statement | inputs |
|---|---|
| M1 | `nystrom_def` |
| M3 | Woodbury (Mathlib), `Matrix.PosSemidef.nuclearNorm_eq_re_trace`, `Matrix.PosSemidef.nystrom_le` |
| M4 | M3, `Matrix.PosDef.inv_le_inv_of_le`, `frobNorm_pinv_sq_eq_re_trace_inv_of_injective_conjTranspose`, `Matrix.PosSemidef.sub_nystrom_le_sub_nystrom` |
| B1 | `hasLaw_conjTranspose_of_hasLaw_haarFrame`, `hasLaw_mul_const_of_hasLaw_haarFrame` |
| B2 | B1, `hasLaw_mul_const_of_hasLaw_haarFrame` |
| B3, B4 | B2, `polarFactor_eq_pinv_sqrt_mul`, R1 block independence, R2 independent-factor moment, R4 $\mathbb{E}\|\mathbf{G}^{+}\|_{\mathsf{F}}^2$ |
| U1 | `hasLaw_const_mul_of_isLeftUnitarilyInvariant` |
| U2 | U1, `eq_smul_one_of_forall_mul_mul_conjTranspose_eq` |
| F0 to F4 | `gaussianProjectionFactor_def` |
| L-a | M4, B3, B4, `hasLaw_polarFactor_of_isLeftUnitarilyInvariant`, `ae_rank_mul_eq_min_of_hasLaw_haarFrame`, `Matrix.PosSemidef.nystrom_eq_of_range_eq`, F1 |
| E1 | §3.0 R0 to R6: L-a, M1, F4, Fact 6.1(c), (d), the Gaussian transfer |
| E2 | E1, correspondence (S0, S2a) |
| E3, E4 | E1, E2, exact recovery (S3, S5) |
| E7 | E1, S2a's T2, S5's NL3, NL6 |

## 4. Files

| # | File | Statements | Lines (est.) | Imports (new) | Depends on |
|---|---|---|---|---|---|
| 1 | `Matrix/Factorizations/NystromGram.lean` (registered; written proved in place) | 1 (M1) | +15 | none | none |
| 2 | `Matrix/Factorizations/NystromOrder.lean` (registered; side file `Matrix/Factorizations/NystromTwoLevel.lean` until proved) | 2 (M3, M4) | +120 | `Matrix/Pseudoinverse/NormBounds`, `Matrix/Inequalities/Order` if not transitive | file 1 |
| 3 | `RandomMatrix/Haar/Blocks.lean` (new) | 4 (B1 to B4) | 220 | `RandomMatrix/Haar/Uniqueness`, `RandomMatrix/Gaussian/Moments`, `RandomMatrix/Gaussian/InverseMoments/Frobenius`, `Matrix/Factorizations/Polar` | none |
| 4 | `RandomMatrix/UnitaryInvariance.lean` (registered; side file `RandomMatrix/UnitaryInvarianceBlocks.lean`) | 2 (U1, U2) | +70 | none | none |
| 5 | `LowRank/Gaussian/RotationInvariant.lean` (registered; side file `LowRank/Gaussian/RotationInvariantRank.lean`) | 11 (F0 to F4, L-a, E1 to E4, E7) | +330 | file 3, file 2 | files 1 to 3 |

About 755 lines and 20 public declarations (19 theorems, 1 definition), against the brief's 650:
the Beta trace (B4) is longer than the brief's estimate, and the Gaussian twins, E7 and U1 are
additions. `RotationInvariant.lean` reaches about 815 lines (485 now), under the limit. Order:
files 1, 3, 4 independent; 2 after 1; 5 after 1 to 3. File 4 has no S4 consumer and can be done
last or deferred to S6 (Q5).

**Placement** (CONTRIBUTING §8 item 5): every addition outside file 3, the only new file.
- M1, `NystromGram.lean`: a Nyström identity beside the Gram correspondence and the equivariance
  lemma it generalises (which is reproved from it there).
- M3, M4, `NystromOrder.lean`: trace facts about the Nyström residual (Schur complement), proved
  through the Loewner order, beside monotonicity and concavity, which L-a and E1 use with them.
- U1, U2, `UnitaryInvariance.lean`: consequences of left unitary invariance, beside
  `integral_mul_mul_conjTranspose_of_isLeftUnitarilyInvariant`, which U2 generalises.
- F0 to F4, L-a, E1, E2, E7, `RotationInvariant.lean`: rotation-invariant test matrices, beside the
  HMT-type statements they sharpen (S5 Q4's reason).
- `docs/constants.toml`: the registry entry (§1).
- **Flags.** (1) E3 and E4, the Gaussian twins, are in `RotationInvariant.lean`; their intended
  homes are `LowRank/Gaussian/Nystrom.lean` and `LowRank/Gaussian/RangeFinder.lean`, which a Gaussian
  user browses, but their proofs go through E1 and E2 and `RangeFinder.lean` is imported by
  `RotationInvariant.lean`; the docstrings of `integral_frobNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix`
  and `Matrix.PosSemidef.integral_nuclearNorm_sub_nystrom_le_of_hasLaw_gaussianMatrix` get one
  sentence naming them (a docstring edit in two registered files). This flag stays open by design
  unless Q6 decides otherwise. (2) The side files of files 2, 4, 5 merge into their homes when
  proved, as in S5.

## 5. Material

**Prototype** (read-only, `~/Documents/prove2me/lean/NLAlib/`): `RandomMatrix/Haar/{HaarFrameMeasure,
HaarQR}.lean` and `RandomMatrix/Gaussian/Wishart*` were checked: Haar frames and inverse Wishart
moments, already ported by R4 and R5; nothing on Beta matrices, Haar blocks, Schur-complement
traces or Epperly and Webber. No prototype material and no ledger entries for S4.

**The maintainer's notes:** none (D13).

**Literature.** All keys are in `docs/references.bib` (`EpperlyWebber2026`, `Meckes2019`,
`TroppYurtseverUdellCevher2017a`, `HalkoMartinssonTropp2011`); no new key.

| statement | citation | relation to the printed statement |
|---|---|---|
| E1, E3 | [EpperlyWebber2026, Theorem 3.6(a)] | real; any $r \ge \max(\operatorname{rank}, \ell)$; each $q$, not the minimum |
| E2, E4 | [EpperlyWebber2026, Theorem 3.2] | as E1 |
| E7 | [TroppYurtseverUdellCevher2017a, Theorem 4.2 (4.3)]; [EpperlyWebber2026, Theorem 3.6(a)] | constant one and EW's factor in place of $2(1 + \frac{q}{\ell-q-1})$ |
| L-a | [EpperlyWebber2026, Lemma 6.2] | upper bound at every $a$, not the limit |
| M3, M4 | [EpperlyWebber2026, proof of Lemma 6.2] | basis-free; all $a, b$ |
| M1 | [EpperlyWebber2026, §6.3] | general $\mathbf{B}$ |
| B1, B2 | [Meckes2019, Ch. 1]; [EpperlyWebber2026, p. 14] | row and corner blocks |
| B4, B3 | [EpperlyWebber2026, Proposition 5.6] | trace of the inverse mean, real, no Beta law |
| U1, U2 | [EpperlyWebber2026, proofs of Theorem 2.1 and Proposition 5.7] | frame form, any left-invariant law, over `𝕜` |
| F0 to F4 | [EpperlyWebber2026, Theorems 3.2, 3.3] | |

**Result ids** (checked against `NLAlib/` and `explore/results.toml`, which has no entry for any of
them): E1, E3, E7 join `randomized-nystrom-expected-error` and E2, E4 join
`randomized-svd-expected-error` (S3 and S5 put HMT, TW and EW 3.1 under these ids); new:
`haar-frame-block-law` (B1, B2), `beta-matrix-inverse-mean` (B4), `nystrom-two-eigenvalue-instance`
(L-a). M1, M3, M4, U1, U2, B3, F0 to F4 are helpers or API and carry none.

## 6. Cut, and why

- *A signed-permutation conjugation-average lemma* (review A4 (iv), brief §4.3 (iv)): no consumer.
  U2 uses the existing `eq_smul_one_of_forall_mul_mul_conjTranspose_eq`, whose proof is that
  argument; E1's average is over $d$ cyclic shifts of a diagonal block, inside its proof (Q4).
- *A public symmetrisation lemma* ($\mathbb{E}\|\mathbf{H}/\mathbf{X}\|_* \le \mathbb{E}\|(\sum_k
  \theta_k\mathbf{U}_k\mathbf{H}\mathbf{U}_k^{\mathsf{H}})/\mathbf{X}\|_*$): a private step of E1;
  made public when S10 or a second consumer wants it. Additive.
- *The minimum over $q$*: rule 5, as S3 and S5.
- *EW's printed hypothesis forms* ($r = \operatorname{rank} \ge \ell$) as separate statements: the
  instance `hr := le_rfl` of E1, E2 (Q1).
- *The Beta law and the matrix $\mathbb{E}\mathbf{X}^{-1}$* (EW Proposition 5.6 as printed): no
  consumer (review A4 (iii)). Additive.
- *Lemma 6.2's limit, the lower bounds, Lemma 5.8, Proposition 5.7 for general $\mathbf{R}$*: S10
  (D6).
- *Proposition 5.7 at $\mathbf{R} = \mathbf{I}$, Theorems 2.1 and 4.2(a)*: S6 (§3.5, Q3).
- *Rotation-invariant and Gaussian twins of L-a and E7, Haar instances*: instances of the stated
  forms (a Haar frame is `isLeftUnitarilyInvariant_haarFrame` with `hXr` from
  `ae_rank_mul_eq_min_of_hasLaw_haarFrame` at $\mathbf{A} = \mathbf{I}$). Additive.
- *A spectral bound for truncated Nyström with EW's factor*, $\mathbb{E}\|\mathbf{H} -
  \llbracket\hat{\mathbf{H}}\rrbracket_k\|_2 \le \lambda_k + \rho\,\|\mathbf{H} -
  \llbracket\mathbf{H}\rrbracket_q\|_*$ (S5's NL8 with E7): at $q = k$ it beats MT Theorem 14.1
  only when $(r-\ell)(\ell-1) < k(r-k)$, i.e. rank close to $\ell$; no consumer. Additive, about 15
  lines.
- *Sharpened truncated RSVD and Gram-form (Schatten, spectral) bounds*: EW bound only the untruncated
  Frobenius and trace errors; S3's truncated RSVD constant comes from the rank-$k$ competitor, which
  EW's argument does not touch. No source.
- *The unsquared $\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X})\|_{\mathsf{F}} \le
  \sqrt{\rho}\,\|\cdot\|_{\mathsf{F}}$*: EW print the squared form. Additive by Jensen.
- *Complex laws*: D3.

## 7. Questions and decisions

Hard-to-reverse items are marked **(hard)**. Under the round's approval rule the maintainer
decides the hard ones; the rest proceed as recommended and are recorded here.

**Q1. The rank parameter of EW's bounds (hard).** Options: (a) a free `r` with `hr : H.rank ≤ r`
and `hlr : Fintype.card l ≤ r`, factor `rotationInvariantFactor r ℓ q`; (b) EW's form,
`hl : Fintype.card l ≤ H.rank` and factor at `H.rank`; (c) both. Recommendation (a): (b) is (a) at
`hr := le_rfl`; (a) also covers $\operatorname{rank} < \ell$ (exact recovery) and, at $r = n$, gives
a bound with no rank knowledge that dominates HMT's, which a user who knows only the dimensions
needs; the proof is the same (R0 is four lines). Hard because S6's 4.2(a) (§3.5) and S10's lower
bounds will be stated in the same shape, and five statements here carry it. Rework if reversed:
hypotheses of E1 to E4, E7 and their consumers.

**Q2. Rule 6 and the dominated HMT forms (maintainer's rule; not hard).** E1 to E4 at $r = n$
dominate S3's `integral_frobNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix` (G2) and
`integral_frobNorm_sub_rsvd_sq_le_of_isLeftUnitarilyInvariant` (I2) and S5's NG2 and NI2
(`gaussianProjectionFactor` in place of `rotationInvariantFactor n ℓ q`). CONTRIBUTING §5.2 rule 6
says a dominated result is reproved from the new one. Options: (a) keep their names and proofs,
since each is the Frobenius or trace instance of the Gram-form family G1, I1, NG1, NI1 that EW do
not dominate, and G2, NG2 cannot be reproved from E3, E4 without an import cycle (their files are
below `RotationInvariant.lean`); docstrings name the sharper statement both ways; (b) reprove I2 and
NI2 from E2 and E1 and move G2, NG2 above. Recommendation (a), recorded as a reading of rule 6 for
the maintainer to confirm.

**Q3. Where EW Theorem 4.2(a) lives (not hard).** The orchestrator's brief for this note lists
4.2(a) with 3.2 and 3.6(a); the port brief's §6 table assigns it to S6, and its proof needs S6's GN
identity (conditioning on $\mathbf{\Omega}$, missing) and, for Haar $\mathbf{\Psi}$, Proposition 5.7
at $\mathbf{R} = \mathbf{I}$ (S6). Options: (a) S6, with §3.5's shape checked now; (b) pull S6's
Gaussian GN identity into S4. Recommendation (a): (b) would move about 150 lines of S6 and its
conditioning machinery into a stage whose risk the brief already flags; Theorem 2.1 likewise stays
in S6, with S4 supplying B4, U1 and U2.

**Q4. No signed-permutation Matrix lemma (not hard).** Options: (a) the brief's lemma (average of
$\mathbf{S}\mathbf{M}\mathbf{S}^{\mathsf{H}}$ over signed permutations equals
$\frac{\operatorname{tr}\mathbf{M}}{m}\mathbf{I}$, every $\mathbf{M}$) in the Matrix layer, serving
§4.3 (ii) and (iv); (b) none: (iv) uses the existing fixed-point form
`eq_smul_one_of_forall_mul_mul_conjTranspose_eq`, and (ii) averages a diagonal block over its
cyclic shifts inside E1's proof. Recommendation (b): (a) needs a signed-permutation-matrix object
(Mathlib has `Equiv.Perm.permMatrix`, no signed version) or an ugly double sum, and it would have no
consumer once (iv) is done by the commutant lemma. Additive later.

**Q5. U1 and U2 in S4 although only S6 consumes them (not hard).** Options: (a) S4, as the brief
places them (Haar infrastructure, done once while `UnitaryInvariance.lean` is open); (b) S6.
Recommendation (a), file 4 scheduled last so that it cannot delay E1.

**Q6. Gaussian twins E3, E4 (not hard).** Options: (a) state them in `RotationInvariant.lean`
(placement flag (1)); (b) none: a Gaussian user applies E1, E2 with
`isLeftUnitarilyInvariant_gaussianMatrix` and `hXr` from `ae_rank_eq_min_of_hasLaw_gaussianMatrix`.
Recommendation (a): EW's bound is the best known Gaussian constant, and the library's Gaussian
statements are found by their `_of_hasLaw_gaussianMatrix` names; the twins also cover $\ell > n$.

**Q7. Nyström first (not hard).** E1 (Theorem 3.6(a)) is primary and E2 (Theorem 3.2) its
consequence by the Gram correspondence at $\mathbf{H} = \mathbf{A}^{\mathsf{H}}\mathbf{A}$, EW's order
and the reverse of S5's. Recommendation: as drafted; the argument lives on Schur complements
(Fact 6.1), so stating it for the randomized SVD would only re-encode $\mathbf{H}$. Proof-internal.

**Q8. The two-level matrix inline (not hard).** Options: (a)
`Matrix.fromBlocks (a • (1 : Matrix s s 𝕜)) 0 0 (b • 1)` in M3, M4, L-a; (b) a definition. Recommendation
(a): three statements, a standard Mathlib spelling with the §5.3 scalar identity; a definition would
need its own API and appears in no consumer's statement (E1 does not mention it).

**Q9. Register `gaussianProjectionFactor` (not hard).** It is a named factor used in five docstrings
and in the statements S4's docstrings compare with, but `docs/constants.toml` has no entry (S3
predates the registry rule). Recommendation: register it in the same commit as
`rotationInvariantFactor` (template `1 + #1/(#2 - #1 - 1)`), with markers added to its five
docstring mentions by a Sonnet pass; otherwise S4's docstrings show one factor's value and not the
other's.

**Q10. M3 public (not hard).** Its only consumers are M4 (same file) and S10's limit. Recommendation:
public, the equational form a user rewrites with (CONTRIBUTING §5.2), at no extra cost since M4's
proof needs it.

**Q11. Frame form of the Haar block lemmas (not hard).** B1 to B4 and U1, U2 take a fixed
$\mathbf{W}$ with orthonormal rows (or frames $\mathbf{V}_1$, $\mathbf{V}_2$) rather than the rows of
a sum type (`toRows₁`). Recommendation: frame form, because S6's consumers split along
$\mathbf{Q}$, $\mathbf{Q}_\perp$ (a basis of $\operatorname{range}\mathbf{A}$), and the sum-type form is
the instance `W := (selectionMatrix Sum.inl)ᴴ` (as L-a uses it).

**Q12. Corrections of record (information).**
- Brief §4.3 (v): (a) is the existing `hasLaw_mul_const_of_hasLaw_haarFrame` (sub-frames) and (c)
  the existing `polarFactor_eq_pinv_sqrt_mul`; only (b) and the corner law are new (B1, B2). "After
  (i) to (iv), the uncertainty of S4 sits here" now sits in B4's reduction and E1's index
  bookkeeping.
- Brief §4.3 (iv): the Matrix-layer lemma exists as `eq_smul_one_of_forall_mul_mul_conjTranspose_eq`
  ("signed permutation matrices suffice", its docstring); (ii) does not need it.
- Brief §4.1 item 4: Loewner antitonicity of the inverse exists (`Matrix.PosDef.inv_le_inv_of_le`).
- Brief §7, S4 entry: four registered files and one new file, about 755 lines, not three files of
  650; no `Matrix/Basic/SignedPermutation.lean`.
- S5 §0, consumer table, row NL1 to NL8: "S4's 3.6(a) composes with NL8 to give the sharp MT 14.1
  for rotation-invariant laws at no cost" is not right: NL8 needs the truncated trace error, which
  3.6(a) does not bound; what composes is E7 with NL8, a decay form incomparable with MT 14.1 (§6).
- EW Theorem 4.2(a)'s $\operatorname{rank}\mathbf{A} \ge k$ is the lower bound's hypothesis; the upper
  bound needs none with the free $r$ (§3.5). EW Lemma 6.2's $a, b > 0$, $a > b$ are not needed for
  the upper half (M4, L-a: $a, b \ge 0$).
- EW §6.3's average of the top block (to $a_0$) is replaced by monotonicity to $\lambda_0$; the bound
  is the same because L-a's does not depend on $a$.

## 8. Amendments from the review (2026-10-15)

Review of this note (eleven amendments: one must-fix, A1; one medium, A5; six minor, A2, A3 and A6
to A9; one process, A4; two for the record, A10, A11; no blocker), all eleven accepted by the
orchestrator; none rejected. Two points are corrected on inspection: A7's first name slip is not
one, `HasOrthonormalCols.exists_fromCols` exists (item 7), and A1's record that CONTRIBUTING §5.2
rule 2 still prints the old marker syntax is out of date (item 1). The review found the mathematics
sound: all 20 statements at every rank and shape under the hypotheses written; the factor is EW's
exactly ($\alpha_{\mathbb{R}} = 1$); the route of E1 (cyclic shifts of the tail block, monotonicity
for the top block, L-a at finite $a$) is a valid replacement for EW's random block permutations and
limit; B1, B2, B4, U1, U2 are true as stated and reduce to lemmas that exist; M3 was rederived
independently; the degenerate cases of §3.0 and the count (3 + 4 + 2 + 11) are right. Q1 is decided
as (a), which the review found dominant (item 12); Q2 as the review's hybrid (item 13); Q9 as
recommended (item 4); the other questions stand as recommended (item 14). Where an item below
contradicts §0 to §7, it supersedes them; §3 stays as drafted.

1. **A1, value markers as the script enforces them** (§1 "Docstrings", the §3 preamble, every
   docstring of §3.4 with a marker). The authority is the docstring of `scripts/check_constants.py`,
   not this note's paraphrase. The marker convention is being changed today by another agent; the
   skeleton follows whatever the final script enforces. As read on 2026-10-15: the value is written
   inline, inside the equation, in place of the constant; the marker
   `<!-- value NAME ARGS -->` sits immediately before the math span, with only whitespace (at most
   one line break) between; there is no closing marker; **a marker never begins a line** (Markdown
   reads a line starting with `<!--` as an HTML block, which ends the paragraph), so it goes at the
   end of the preceding text line; marker lines and span lines are at most 100 characters; the
   filled template is matched modulo whitespace with token boundaries, grouping around it is
   allowed, and a `$$…$$` display may use the optional `display` template. §1's "stands on its own
   line just before that math span" becomes "follows the text before it on that line, immediately
   before the math span". The docstrings that carry a marker (F0, L-a, E1, E2, E7: five in §3.4,
   not the review's seven) are rewritten so; E1, for example:
   ```
   … $\ell \le r$ and $q + 2 \le \ell$, <!-- value rotationInvariantFactor r \ell q -->
   $$\mathbb{E}\|\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{X})\|_* \le
   \frac{r - \ell}{r - q}\Bigl(1 + \frac{q}{\ell - q - 1}\Bigr)
   \|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_q\|_*\,.$$
   ```
   and F0 opens `/-- **Epperly and Webber's factor** <!-- value rotationInvariantFactor r \ell q -->`
   with the inline span `$(r - \ell)/(r - q) \cdot (1 + q/(\ell - q - 1))$` on the next line.
   Additions on inspection: the registry entry of §1 gains
   `display = '\frac{#1 - #2}{#1 - #3}\Bigl(1 + \frac{#3}{#2 - #3 - 1}\Bigr)'`, so that the
   displays read as the library's other displays (S3's I2 writes
   `\Bigl(1 + \frac{k}{\ell - k - 1}\Bigr)`; inline spans keep `latex`); F3's docstring names
   `gaussianProjectionFactor q l` in backticks, so once item 4 registers it F3 carries its marker
   and value, `… at most HMT's, <!-- value gaussianProjectionFactor q \ell -->` then
   `$1 + q/(\ell - q - 1)$`; E3 and E4 repeat the display of E1 and E2 with its marker instead of
   "The same for", since Q6's reason for them is that a Gaussian user finds them by name and reads
   them alone; the module docstrings of files 5a and 5b (item 5), which name
   `rotationInvariantFactor` in backticks, give its value as a span of its own. If the final script
   differs (no `display` field, another placement), the script wins and these docstrings follow
   it. Record: CONTRIBUTING §5.2 rule 2, read on 2026-10-15, already states the new syntax (no
   closing marker; "a marker never begins a line … it follows the text before it"); the review's
   remark that it still prints `<!-- /value -->` predates that update. Nothing for S4 to do there.
2. **A2, E7's comparison at $q = k$** (§3.4, E7's docstring). "at $q = k$ dominated by the
   truncated trace bound with $1 + \frac{k}{\ell-k-1}$, incomparable for $q > k$" is false and
   becomes: "incomparable with
   `Matrix.PosSemidef.integral_nuclearNorm_sub_truncatedSVD_nystrom_le_of_isLeftUnitarilyInvariant`
   at $q = k$ as well: better iff $(r-\ell)(\ell-1) < k(r-k)$, that is for rank close to $\ell$ (at
   $r = \ell$ it gives the best rank-$k$ error with constant one); for $q > k$ better when the tail
   decays". Checked: $1 + \frac{k}{\ell-k-1} = \frac{\ell-1}{\ell-k-1}$, so
   $\rho(r,\ell,k) \le \frac{k}{\ell-k-1}$ iff $(r-\ell)(\ell-1) \le k(r-k)$; as $r \to \infty$
   the comparison is $\ell - 1$ against $k$, and $\ell - 1 > k$. Rule 4's cross-naming stays: the
   docstrings of that statement and of its Gaussian twin
   `Matrix.PosSemidef.integral_nuclearNorm_sub_truncatedSVD_nystrom_le_of_hasLaw_gaussianMatrix`
   name E7 (a docstring edit in registered files). The condition is the one §6 already states for
   the spectral variant.
3. **A3, sharpness wording** (§3.4, E1's docstring; §0, the consumer row of E1). "At
   $r = \operatorname{rank}\mathbf{H}$ it is attained in the worst case" becomes "at
   $r = \operatorname{rank}\mathbf{H}$ the supremum of the ratio over rank-$r$ matrices equals it
   ([EpperlyWebber2026, Theorem 3.6(b)], S10)": Theorem 3.6(b) is a supremum, its proof the hard
   instance with $a \to \infty$, and no single matrix attains the factor. The §0 row's "attained in
   the worst case" is read the same way. F0's "the sharp expected … over matrices of rank $r$"
   stands.
4. **A4 and Q9 decided: `gaussianProjectionFactor` is registered** (§1 last paragraph, Q9). The
   registry's header says it holds "every constant, tail function and sample size that a statement
   uses by name"; `gaussianProjectionFactor` is a `def` used by name in about twenty statements, and
   `rotationInvariantFactor`'s `lean_body` refers to it. Every named constant is registered.
   Entry:
   ```toml
   [[constant]]
   name = "NLAlib.gaussianProjectionFactor"
   kind = "factor"
   file = "NLAlib/RandomMatrix/Gaussian/BlockMoments.lean"
   args = ["k", "l"]
   latex = '1 + #1/(#2 - #1 - 1)'
   display = '1 + \frac{#1}{#2 - #1 - 1}'
   lean_body = 'gaussianProjectionFactor (k l : ℕ) : ℝ := 1 + (k : ℝ) / ((l : ℝ) - k - 1)'
   ```
   with `body_hash` written by `--update`. The `display` template matches the displays S3 and S5
   already print, `\Bigl(1 + \frac{k}{\ell - k - 1}\Bigr)`, so the docstring pass (Sonnet, in the
   registering commit, which may precede S4's proofs) only places markers and rewrites prose. The
   docstrings that name it in backticks, as of 2026-10-15: `LowRank/Gaussian/RangeFinder.lean:187`,
   `LowRank/Gaussian/Nystrom.lean:127`, `LowRank/Gaussian/RotationInvariant.lean:142` and `:336`
   (each "the factor being `gaussianProjectionFactor k ℓ`", the symbol-defined-by-a-sentence form
   the rule forbids: marker before the display, the name kept in prose nearby),
   `RandomMatrix/Gaussian/BlockMoments.lean:34` (module list; its inline `\frac` becomes the
   `latex` form) and `:66` (the `_def` lemma), plus the definition's own docstring, which must show
   its value: seven docstrings. §1's "`gaussianProjectionFactor` is not registered (S3 predates
   the registry rule)" is superseded. S6 is amended to match: its lines 320 to 328 ("unregistered
   source formulas") are superseded, and `haarProjectionFactor` is registered the same way, in the
   commit that defines it.
5. **A5, the split of `RotationInvariant.lean` is named now** (§4 files table and size paragraph,
   the placement bullet, §1 "Home"). The review's estimate of file 5 (450 to 550 lines, E1 alone
   250 to 350 for its index bookkeeping) puts the merged file at 935 to 1035, over the limit at the
   upper end. The review's proposal (the side file `RotationInvariantRank.lean` as the permanent
   home of all eleven, importing `RotationInvariant.lean`) conflicts with Q2's hybrid (item 13): I2
   and NI2 in `RotationInvariant.lean` are reproved from E2 and E1, so E1 and E2 cannot sit in a
   file that imports it. The split is therefore downward:
   - **file 5a, `LowRank/Gaussian/RotationInvariantFactor.lean` (new, permanent): F0 to F4 and
     L-a** (6 declarations, about 180 lines). Topic: Epperly and Webber's factor and the
     two-eigenvalue instance on which it is computed; S10's lower bounds on that instance (Lemma
     6.2's limit) can join it. Imports: file 2 (`NystromOrder`), file 3 (`Haar/Blocks`),
     `RandomMatrix/Gaussian/BlockMoments`, `RandomMatrix/Haar/Transfer`, `LowRank/Random/Nystrom`;
     nothing from `RotationInvariant.lean`. The registry entry's `file` names it from the start; no
     change at a merge.
   - **file 5b, `LowRank/Gaussian/RotationInvariant.lean` (registered): E1 to E4 and E7** (5
     declarations, +300 to +400 lines, side file `LowRank/Gaussian/RotationInvariantRank.lean`
     until proved), new import file 5a. Merged: 785 to 885 lines, under the limit, with I2 and NI2
     (item 13) at its end.
   S6's GN and GH files import file 5b (for E2), which brings 5a. Implementation note from the
   review: `Equiv.addRight k` on `Fin d` needs `[NeZero d]`, available from $d \ge 2$; `finRotate`
   powers are the alternative.
6. **A6, L-a's $\ell \le r$ is derived, not carried** (§3.0 degenerate list and L-a's route (b)).
   L-a has no `hlr`: `hY` with `[IsProbabilityMeasure ν']` makes $\mu$ a probability measure
   (`HasLaw.isProbabilityMeasure`), and `hYr` then gives an injective $(s \oplus t) \times l$
   matrix, so $\ell \le \lvert s\rvert + \lvert t\rvert = r$. Under "$r < \ell$" §3.0 adds: "L-a
   carries no such hypothesis; there it is vacuous, not false". In route (b), B4's
   `hkn : Fintype.card l ≤ Fintype.card (s ⊕ t)` is discharged from it.
7. **A7, names of record, corrected in part on inspection** (§1 "Used directly", §3.2 B4's route,
   the "What is missing" paragraph). The first slip is not one:
   `HasOrthonormalCols.exists_fromCols` exists (`Matrix/Basic/OrthonormalBasis.lean:145`, the case
   of equality, `Fintype.card n + Fintype.card p = Fintype.card m`), and it is what B4 needs to
   complete $\mathbf{V}$ by $\mathbf{V}'$ indexed by a type of size $\lvert n\rvert - \lvert
   k\rvert$; `HasOrthonormalCols.exists_fromCols_of_card_le` (line 80) also serves. Both names
   stand. Accepted: (i) the sorted spectral theorem of R2 is
   `Matrix.IsHermitian.exists_eq_mul_diagonal_mul_conjTranspose`
   (`Matrix/Spectral/Eigenvalues.lean:202`, `U : Matrix n (Fin (Fintype.card n)) 𝕜`, eigenvalues
   `eigenvalue A i` sorted), never the unsorted
   `Matrix.IsHermitian.exists_hasOrthonormalCols_eq_mul_diagonal_mul_conjTranspose` beside it (R2
   needs the first $r$ columns to carry the top eigenvalues); (ii) `Matrix.PosDef.inv_le_inv_of_le`
   is NLAlib's (`Matrix/Inequalities/Order.lean:160`), and the "What is missing" paragraph says
   so; (iii) Mathlib's `Matrix.add_mul_mul_inv_eq_sub` needs `IsUnit A`, `IsUnit C` and
   `IsUnit (C⁻¹ + V * A⁻¹ * U)`; if these prove awkward in M3's push-through step, the alternative
   is the eigenvalue route (the nonzero spectra of $\mathbf{K}^{\mathsf{H}}\mathbf{K}$ and
   $\mathbf{K}\mathbf{K}^{\mathsf{H}}$ agree); (iv) in B1's proof
   `hasLaw_mul_const_of_hasLaw_haarFrame` is applied to the frame $\mathbf{Q}^{\mathsf{H}}$
   ($k \times n$), so its `hk` instantiates to `hnk`, as drafted.
8. **A8, B3 and B4 stay in `Haar/Blocks.lean`, with the reason** (§4 placement bullet). They are
   moments of the block $\mathbf{W}\mathbf{Q}$, proved from the block law B2 and the Gaussian
   inverse moments; `RandomMatrix/Haar/Moments.lean` imports only `Probability/Isotropic` and
   `Haar/Basic`, and holding them would make it import the block laws,
   `Gaussian/InverseMoments/Frobenius` and `Matrix/Factorizations/Polar`. The module docstring of
   `Moments.lean` gets one sentence naming B4 (a docstring edit in a registered file). The other
   placements are confirmed by the review, and the E3, E4 flag stays recorded as a flag.
9. **A9, B2 keeps its `HasLaw` shape** (§3.2, B2's docstring). The conclusion
   `(haarFrame p n).map (· * V)` does not depend on $\mathbf{V}$; the docstring says so: "the law
   does not depend on $\mathbf{V}$: it is the law of the $p \times k$ corner of a Haar orthogonal
   matrix, which any frame $\mathbf{V}$ realises". The `HasLaw` form is kept because it is the
   library's spelling of Haar block laws (B1, `hasLaw_mul_const_of_hasLaw_haarFrame`) and B4's
   proof uses it through `HasLaw.integral_comp`; `hV` is a hypothesis the identity needs, so the
   suffix `_of_hasOrthonormalCols` stays. The measure identity
   `(haarFrame n k).map (W * ·) = (haarFrame p n).map (· * V)` is additive if a consumer rewrites
   with it.
10. **A10, EW's display in the proof of Lemma 6.2** (literature checks, the Lemma 6.2 bullet). The
    bullet adds: "EW's display after 'another explicit calculation using (6.1)' has a slip:
    dividing $a\mathbf{R}_1\mathbf{R}_1^{*} + b\mathbf{R}_2\mathbf{R}_2^{*}$ by $a - b$ gives
    $\mathbf{R}_1\mathbf{R}_1^{*} + \frac{b}{a-b}\mathbf{I}$ (as
    $\mathbf{R}_1\mathbf{R}_1^{*} + \mathbf{R}_2\mathbf{R}_2^{*} = \mathbf{I}$), not
    $\mathbf{R}_1\mathbf{R}_1^{*} + \frac{b}{a-b}\mathbf{R}_2\mathbf{R}_2^{*}$; the limit is
    unaffected. M3 is derived independently and does not match that display; the prover should not
    try to." The review verified M3: with $\mathbf{X} = \mathbf{\Psi}_1\mathbf{\Psi}_1^{\mathsf{H}}$,
    $(a-b)\,b\operatorname{tr}((\mathbf{I}-\mathbf{X})(b\mathbf{I} + (a-b)\mathbf{X})^{-1}) +
    b(r-\ell) = ab\operatorname{tr}(b\mathbf{I} + (a-b)\mathbf{X})^{-1} + b(\lvert t\rvert - \ell)$.
11. **A11, S6 carries the free rank parameter** (§3.5). §3.5 already writes the composition with
    `{r q : ℕ} (hr : A.rank ≤ r) (hlr : Fintype.card l ≤ r) (hq : q + 2 ≤ Fintype.card l)`; it adds
    one line: "S6's GN7 and GH5 take exactly these hypotheses and the factor
    `rotationInvariantFactor r ℓ q`, not shape (b) at `A.rank` under `Fintype.card l ≤ A.rank`,
    which would exclude $\operatorname{rank}\mathbf{A} < \ell$ and the rank-free $r = n$ form". The
    S6 note is amended to match (item 12). S6's (S4-i) is B4 (one
    `frobNorm_pinv_sq_eq_re_trace_inv_of_injective_conjTranspose` rewrite) and (S4-ii) is U2, whose
    hypotheses are weaker than S6's "complementary frames".
12. **Q1 decided: (a), a free rank parameter `r`** (review Part III). (b) is (a) at `r := H.rank`,
    `hr := le_rfl`, so nothing is lost; (a) adds the rank-deficient case and the rank-free instance
    `r := Fintype.card n`, whose factor $\frac{n-\ell}{n-q}$ times HMT's is what a user who knows
    only the dimensions can apply; the proof cost is R0. E1 to E4 and E7 carry `hr` and `hlr` as
    drafted, and **S6 carries the free `r` too**: GN7 and GH5 (EW Theorem 4.2(a)) are stated with
    `hr`, `hlr` and `rotationInvariantFactor r ℓ q` (item 11). S10's lower bounds are statements at
    $\operatorname{rank}\mathbf{H} = r$ and use the same letter. A corollary at `r := H.rank` stays
    cut (§6), a one-liner if wanted later.
13. **Q2 decided: the review's hybrid** (§3.4, §4, Q2). (i) I2,
    `integral_frobNorm_sub_rsvd_sq_le_of_isLeftUnitarilyInvariant`, and NI2,
    `Matrix.PosSemidef.integral_nuclearNorm_sub_nystrom_le_of_isLeftUnitarilyInvariant`, are
    reproved from E2 and E1 in `RotationInvariant.lean` (literal rule 6): E2, E1 at
    $r = \lvert n\rvert$ (`hr` from the rank bound by the width, `hlr` from `hXr` on the probability
    space, as in R0), then F3 and multiplication by the nonnegative tail. Names, statements and
    result ids unchanged; both move to the end of the file, after E1 to E4 (nothing else in the
    file uses them: NI2 is today's only consumer of I2, and NI2 has none), and the module
    docstring's list follows. Their docstrings say they are the instance $r = n$ of E2 and E1 with
    HMT's factor. (ii) G2, `integral_frobNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix`
    (`LowRank/Gaussian/RangeFinder.lean`), and NG2,
    `Matrix.PosSemidef.integral_nuclearNorm_sub_nystrom_le_of_hasLaw_gaussianMatrix`
    (`LowRank/Gaussian/Nystrom.lean`), keep their proofs and places, as the Frobenius and trace
    instances of the Gram-form families G1 and NG1, which EW do not dominate. Their docstrings name
    E4 and E3 as the sharper form, and E4 and E3 name G2 and NG2 (the placement flag (1) of §4
    already plans this edit). (iii) The reading of rule 6 recorded for the maintainer to confirm:
    "an instance of a non-dominated general statement is not re-rooted across layers". Rework if
    the maintainer prefers (b) in full: two proofs moved and one import added, under an hour.
14. **Q3 to Q8 and Q10 to Q12 stand as recommended**: EW 4.2(a) and 2.1 in S6 with §3.5's shape
    checked now (Q3); no signed-permutation lemma (Q4, confirmed by the review's check 3: the $d$
    cyclic shifts and the commutant lemma do the work); U1, U2 in S4, file 4 last (Q5); the Gaussian
    twins E3, E4 in `RotationInvariant.lean` (Q6, with item 1's displays); Nyström first (Q7); the
    two-level matrix inline (Q8); M3 public (Q10); frame form of the Haar block lemmas (Q11); Q12's
    corrections of record.
15. **Files and count after the amendments** (supersedes the §4 table and its size paragraph).

    | # | File | Statements | Lines (est.) | Imports (new) | Depends on |
    |---|---|---|---|---|---|
    | 1 | `Matrix/Factorizations/NystromGram.lean` (registered) | 1 (M1) | +15 | none | none |
    | 2 | `Matrix/Factorizations/NystromOrder.lean` (registered; side file `NystromTwoLevel.lean`) | 2 (M3, M4) | +120 | as §4 | file 1 |
    | 3 | `RandomMatrix/Haar/Blocks.lean` (new) | 4 (B1 to B4) | 220 | as §4 | none |
    | 4 | `RandomMatrix/UnitaryInvariance.lean` (registered; side file `UnitaryInvarianceBlocks.lean`) | 2 (U1, U2) | +70 | none | none |
    | 5a | `LowRank/Gaussian/RotationInvariantFactor.lean` (new) | 6 (F0 to F4, L-a) | 180 | item 5 | files 2, 3 |
    | 5b | `LowRank/Gaussian/RotationInvariant.lean` (registered; side file `RotationInvariantRank.lean`) | 5 (E1 to E4, E7); I2, NI2 reproved | +300 to +400 | file 5a | files 1, 5a |

    20 public declarations (19 theorems, 1 definition), as drafted, now in six files: 1, 2, 4, 2,
    6, 5. About 905 to 1005 lines; `RotationInvariant.lean` reaches 785 to 885. Two registry
    entries (`rotationInvariantFactor` with `file` = file 5a, item 1's `display`;
    `gaussianProjectionFactor`, item 4) and the docstring passes of items 1, 2, 4, 8 and 13 in
    registered files. Order: files 1, 3, 4 and item 4's registration independent; 2 after 1; 5a
    after 2 and 3; 5b after 1 and 5a; file 4 last or deferred (Q5).
