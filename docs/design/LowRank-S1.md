# Design note: LowRank stage S1, the structural bound of the range finder

Status: drafted 2026-10-15 under `docs/PORT_LOWRANK.md` (maintainer decisions of 2026-10-15; D1, D2,
D4, D9, D11 to D13; §4.1 item 6, §4.2, the S1 entry of §7) and `docs/design/LowRank-S0.md` (§3 as
amended by §8; D14 decided, `obliqueProjector X S := X * pinv (S * X) * S`; S0's skeletons are being
written, so S0's names are used as the note fixes them). Deterministic, over `𝕜`, every shape and
rank. Reviewed 2026-10-15, amendments in §8, which overrides §0 to §7 where they disagree (§3
stays as drafted).

Departures from the brief, each argued below:
- the top-$k$ reading of HMT Theorem 9.1 is a one-line rewrite of the general-frame statements by a
  hypothesis `A * Z * Zᴴ = truncatedSVD A k` with an existence lemma, not a second family of
  declarations (§3.3, Q3);
- the tail-flattening lemma moves to the Matrix layer, `Matrix/Spectral/LowRank.lean`, in a
  subtraction-free form; the manuscript's $\lceil\ell/2\rceil$ and $4/t$ arithmetic is S6's (Q7);
- the competitor's rank and range lemmas are not stated: each is one line of Mathlib or library API
  (§6);
- the OSI form is stated in squared Frobenius norm only, CEMT's shape; a Gram-gauge OSI form has no
  consumer (Q6);
- correction of record: TYUC NeurIPS has no structural "Lemma A.1"; brief §9.2 item 2's S1 entry
  points at Proposition A.2 (S0's correspondence) and Theorem A.1 (S5's expectation) (§5).

**Missing infrastructure.** Below the Matrix layer: nothing. In the Matrix layer, four lemmas (§3.4):
the row-space projector of `truncatedSVD` (needs the private SVD lemmas of `LowRank.lean`), the
existence of a frame $\mathbf{Z}$ with $\mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}} =
\llbracket\mathbf{A}\rrbracket_k$, the tail flattening, and the mirror
$\mathbf{A}^{+} = \mathbf{A}^{\mathsf{H}}(\mathbf{A}\mathbf{A}^{\mathsf{H}})^{+}$ of an existing
`Pinv.lean` lemma. From S0 (in progress): `rsvd`, `sub_rsvd`, `nystrom`,
`Matrix.PosSemidef.sub_nystrom_eq`, `singularValues_mul_conjTranspose_self`,
`SymmetricGauge.matrixNorm_mul_conjTranspose_self`, `IsSubspaceInjection.rank_mul_eq`.

## 0. Scope and consumers

$\mathbf{A}$ : `Matrix m n 𝕜`; the test matrix $\mathbf{\Omega}$ : `Matrix n l 𝕜` multiplies on the
right (D2); a frame $\mathbf{Z}$ : `Matrix n r 𝕜` with $\mathbf{Z}^{\mathsf{H}}\mathbf{Z} =
\mathbf{I}$ plays HMT's $\mathbf{V}_1$. Throughout, in docstrings and below,
$$\mathbf{E} = \mathbf{A} - \mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}},\qquad
\mathbf{M} = \mathbf{E}\mathbf{\Omega}(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^{+},\qquad
\mathbf{C} = \mathbf{A}\mathbf{\Omega}(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^{+}\mathbf{Z}^{\mathsf{H}},$$
and the error of the range finder is $\mathbf{A} - \mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A}$,
`A - rsvd A Ω`. With $\mathbf{Z}$ spanning a dominant right singular subspace,
$\mathbf{E} = \mathbf{A} - \llbracket\mathbf{A}\rrbracket_k$ and $\mathbf{M}$ is HMT's
$\mathbf{\Sigma}_2\mathbf{\Omega}_2\mathbf{\Omega}_1^{+}$ up to an isometry.

| Item | Consumers |
|---|---|
| competitor identities (linear, Gram, Frobenius) | the proofs below; S2a (the rank-$k$ competitor form of late truncation, Woodruff Lemma 48); S6 (the truncated-GN baseline $\mathbb{E}(\lVert\mathbf{A}_\perp\rVert_{\mathsf{F}}^2 + \gamma^2)$) |
| Gram form in every gauge (§4.1 item 6, D4) | S3 (one theorem for HMT 10.5, TW (RSVD2) for every Schatten $p \ge 2$, the squared spectral error; TW (RSVD1) tail); S5 (every Nyström bound through S0's correspondence); the Nyström structural bound below |
| unsquared triangle form in every gauge, its spectral corollary | S3 (HMT 10.6, the first spectral moment, from R4's spectral block bound); users wanting nuclear-norm bounds (review A2) |
| spectral and Frobenius squared corollaries | S3 (HMT 10.5 Frobenius; tails); S6 (spectral residual of truncated GN, split at $\lceil\ell/2\rceil$; GN = RSVD term plus completion); S7 (CEMT Theorem 2.2 with the Sketching round's tail) |
| truncation for free (Woodruff Lemma 48's middle term) | S3 (truncated RSVD with HMT's constant); S6 (truncated-GN baseline); S7 (truncated OSI versions) |
| OSI form (CEMT Theorem 2.2, deterministic core) | S7 (CEMT Theorem 2.2, Corollary 2.5 via the correspondence); users holding a fixed sketch with a subspace injection |
| $\mathbf{M}$ through an AMM error, and its bound | S7 (Woodruff Lemma 45 and Theorem 47: injection plus `HasJLMoment` AMM gives $(1+\varepsilon)$) |
| Nyström structural bound in every gauge | S5 (deterministic statements, docstring comparison); users with kernel and Gram matrices (no square root in the statement) |
| frame of $\llbracket\mathbf{A}\rrbracket_k$, row-space projector | S3, S5, S6 (the HMT reading: obtain $\mathbf{Z}$, rewrite) |
| tail flattening $d\,\sigma_{k+d}^2 \le \lVert\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k\rVert_{\mathsf{F}}^2$ | S6 (spectral residual of truncated GN) |

Not in S1: anything probabilistic (S3 to S7); late and early truncation (S2a, S2b), including the
D5 optimality-hypothesis forms and the bridge from $\mathbf{Q}\llbracket\mathbf{Q}^{\mathsf{H}}
\mathbf{A}\rrbracket_k$ to `truncatedSVD (rsvd A Ω) k`; GN (Frobenius only by D4, assembled in S6
and S7 from S0's split and this stage); the power scheme (HMT Theorem 9.2, out of scope, brief §8);
TW's sharper parallel-sum form (8.1) (§6). Noted for S7, not added here: `rsvd A (c • Ω) = rsvd A Ω`
for $c \ne 0$ (the $(\sqrt{k})^{-1}$ scaling of D2's per-family lemmas) belongs in S0's
`SketchedLowRank.lean` and has no S1 consumer.

## 1. Objects

No new definition. No deviation from Mathlib, so no entry in `Mathlib-deviations.md`.

**§5.3 rows** (added by the PR that adds L2; two reviews, CONTRIBUTING §9):

| Concept | Spelling | Bridge |
|---|---|---|
| best rank-$k$ approximation (amended row: the frame clause is new) | as now; a frame of a dominant right singular subspace is a `Z` with `HasOrthonormalCols Z` and `A * Z * Zᴴ = truncatedSVD A k`, never `IsSVD` blocks or `eigenvectorBasis` columns (CONTRIBUTING §5.2) | `exists_hasOrthonormalCols_mul_mul_conjTranspose_eq_truncatedSVD`; `mul_rangeProjector_conjTranspose_truncatedSVD` |
| range-finder error terms (new row) | for a frame `Z`: `A - A * Z * Zᴴ` and `(A - A * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω)`, no definitions; the competitor `A * Ω * pinv (Zᴴ * Ω) * Zᴴ`; the hypothesis `(Ωᴴ * Z).rank = Z.rank` (S0's rank spelling, sketch orientation) | `HasOrthonormalCols.sub_mul_pinv_mul_conjTranspose_eq`; `IsSubspaceInjection.rank_mul_eq` |

**Used directly.** Mathlib: `Matrix.rank_mul_le_right`, `Matrix.rank_le_card_height`,
`Matrix.conjTranspose_mul`, `Finset.card_nsmul_le_sum`, `CFC.sqrt`. Library: `rangeProjector` API
(`isStarProjection_one_sub_rangeProjector`, `rangeProjector_mul_eq_self_iff`,
`rangeProjector_mul_eq_zero_iff`, `rangeProjector_inj`, `HasOrthonormalCols.rangeProjector_eq`,
`range_mulVecLin_le_iff_exists_mul`); `pinv` API (`mul_pinv_self_of_injective_conjTranspose`,
`pinv_eq_pinv_conjTranspose_mul_self_mul`, `pinv_conjTranspose_mul_self`,
`specNorm_pinv_sq_le_inv_of_smul_one_le`); gauges (`SymmetricGauge.matrixNorm_add_le`,
`matrixNorm_le_of_singularValues_le`, `matrixNorm_mul_le_mul_specNorm`,
`matrixNorm_mul_conjTranspose_right_of_hasOrthonormalCols`, `lpGauge_top_matrixNorm`);
`IsStarProjection.singularValues_mul_le`; `specNorm_conjTranspose_mul_self`;
`frobNorm_one_sub_rangeProjector_mul_le_frobNorm_sub_mul`; `frobNorm_mul_conjTranspose_right`;
`HasOrthonormalCols.frobNorm_sub_mul_truncatedSVD_le_of_rank_le` (`ProjectedLowRank.lean`);
`frobNorm_sub_truncatedSVD_sq`, `singularValues_eq_zero_iff`, `truncatedSVD_of_rank_le`,
`rank_truncatedSVD`, `exists_hasOrthonormalCols_range_le`, `mulVec_injective_iff_rank_eq`;
`IsSubspaceInjection.frobNorm_mul_pinv_sq_le` (Sketching, the deterministic half of CEMT Lemma 2.1).

**Mathlib search** ("searched, none" unless named): a range-finder or HMT structural bound; the
row-space projector of a truncated SVD; a frame of a dominant singular subspace; a pseudoinverse
identity $\mathbf{A}^{+} = \mathbf{A}^{\mathsf{H}}(\mathbf{A}\mathbf{A}^{\mathsf{H}})^{+}$ (Mathlib has
no matrix pseudoinverse). The averaging step of the tail flattening is
`Finset.card_nsmul_le_sum`; the prototype's real-sequence lemmas are not restated.

## 2. Interfaces

No new predicate. Hypotheses, each an existing spelling:
- `HasOrthonormalCols Z` for the frame;
- `(Ωᴴ * Z).rank = Z.rank`: $\mathbf{\Omega}^{\mathsf{H}}$ loses no rank on
  $\operatorname{range}\mathbf{Z}$, that is $\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega}$ has full row rank
  (HMT's "$\mathbf{\Omega}_1$ has full row rank"; Woodruff Lemma 48's
  $\operatorname{rank}(\mathbf{Z}^{\mathsf{T}}\mathbf{S}) = \operatorname{rank}\mathbf{Z}$). It is
  S0's rank spelling with the sketch $\mathbf{\Omega}^{\mathsf{H}}$, so a user holding
  `h : IsSubspaceInjection Ωᴴ Z a` writes `h.rank_mul_eq ha`; for a Gaussian $\mathbf{\Omega}$,
  `ae_rank_mul_eq_min_of_hasLaw_gaussianMatrix Zᴴ` and `Matrix.rank_conjTranspose` give it almost
  surely when `card r ≤ card l` (Haar: `ae_rank_mul_eq_min_of_hasLaw_haarFrame`);
- `A * Z * Zᴴ = truncatedSVD A k` for the top-$k$ reading (new §5.3 clause, §1), produced by L2;
- `IsSubspaceInjection Ωᴴ Z a` with `0 < a` for the OSI forms (Sketching's predicate, D2);
- `LinearMap.range (A * Ω).mulVecLin ≤ LinearMap.range Q.mulVecLin` with `HasOrthonormalCols Q` for
  truncation inside a basis of the sketch (§5.3 range containment).

## 3. Statement shapes

`namespace NLAlib`, `open scoped Matrix MatrixOrder`. Variables
`{𝕜 : Type*} [RCLike 𝕜] {m n l r q : Type*} [Fintype m] [Fintype n] [Fintype l] [Fintype r]
[Fintype q] [DecidableEq r] {Ω : Matrix n l 𝕜} {Z : Matrix n r 𝕜}`; `[DecidableEq n]` only where
`1 : Matrix n n 𝕜` appears (N1), `[DecidableEq q]` with `Q`. The statements of §3.1, §3.2 and §3.3
except the Nyström bound contain no `1` (that is why $\mathbf{E}$ is spelled `A - A * Z * Zᴴ`, Q4). Docstrings are shortened; the full
ones carry the citations of §5 and are LaTeX throughout (CONTRIBUTING §6 item 5; S0 §8 item 12).

**Degenerate cases** (checked for every statement; the per-section notes say where a case bites).
- *Necessity of the rank hypothesis.* With $\mathbf{A} = \mathbf{Z} = [1]$ and $\mathbf{\Omega} =
  [0]$: $\mathbf{E} = \mathbf{0}$, $\mathbf{M} = \mathbf{0}$, $\mathbf{C} = \mathbf{0}$ and
  `rsvd A Ω = 0`, so the competitor identity and every bound of §3.1 and §3.2 would claim
  $\mathbf{A} = \mathbf{0}$. The hypothesis is the only one these statements carry besides the frame.
- *`r` empty.* `Z = 0` has orthonormal columns, the rank hypothesis holds ($0 = 0$),
  $\mathbf{E} = \mathbf{A}$, $\mathbf{M}$ and $\mathbf{C}$ are $\mathbf{0}$: every bound reduces to
  the contraction $\lVert(\mathbf{I}-\mathbf{P})\mathbf{A}\rVert \le \lVert\mathbf{A}\rVert$, true.
- *`l` empty, $\mathbf{\Omega} = \mathbf{0}$.* `rsvd A Ω = 0`; the rank hypothesis forces `r` empty
  (previous item). *`n` empty:* a frame forces `r` empty. *`m` empty, $\mathbf{A} = \mathbf{0}$:*
  both sides $0$.
- *More samples than the dimension* ($\lvert l \rvert > \lvert n \rvert$), *rank-deficient*
  $\mathbf{A}\mathbf{\Omega}$, $\mathbf{Z}$ *wider than* $\operatorname{rank}\mathbf{A}$: no statement
  assumes otherwise. $\lvert r \rvert \le \lvert l \rvert$ is implied by the rank hypothesis.
- *Rank of $\mathbf{A}$ at most $k$* (brief §1, "exact a.s."): in the top-$k$ reading
  $\llbracket\mathbf{A}\rrbracket_k = \mathbf{A}$, so $\mathbf{E} = \mathbf{M} = \mathbf{0}$ and the
  bounds say `A - rsvd A Ω = 0`, the deterministic content of exact recovery.
- *Ties* $\sigma_{k-1} = \sigma_k$: L2's $\mathbf{Z}$ matches the chosen `truncatedSVD`; the
  $\mathbf{E}$-terms are choice-free (singular values of $\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k$),
  $\mathbf{M}$ depends on the choice, which S3's expectations integrate away. A user with another
  SVD applies the general-frame statements with that $\mathbf{V}_1$.
- *Hermitian but not PSD inputs to Nyström* (N1): excluded by `hH`, necessarily: $\mathbf{H} =
  \begin{bmatrix} 0 & 1 \\ 1 & 0 \end{bmatrix}$, $\mathbf{\Omega} = \mathbf{Z} = \mathbf{e}_1$ give
  $\mathbf{\Omega}^{\mathsf{H}}\mathbf{H}\mathbf{\Omega} = 0$, `nystrom H Ω = 0`, and a right side
  $\mathbf{0}$ (the compression $(\mathbf{I}-\mathbf{Z}\mathbf{Z}^{\mathsf{H}})\mathbf{H}
  (\mathbf{I}-\mathbf{Z}\mathbf{Z}^{\mathsf{H}})$ vanishes) against $\lVert\mathbf{H}\rVert_\Phi > 0$.
- *$a \le 0$* (OSI forms): excluded by `ha`; the injection is vacuous there.
- *Padded indices* (L3): the statement holds at every `k d : ℕ`, including indices past the
  smaller dimension, where both singular values are $0$ (CONTRIBUTING §5.2).
- Truncation ranks at or above the rank (§3.2 truncation for free, L2): handled, see there.

### 3.1 `LowRank/Structural/RangeFinder.lean`: the competitor (3)

```lean
/-- **The range-finder competitor.** For $\mathbf{Z}$ with orthonormal columns and
$\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega}$ of full row rank, the matrix
$\mathbf{C} = \mathbf{A}\mathbf{\Omega}(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^{+}\mathbf{Z}^{\mathsf{H}}$,
whose columns lie in $\operatorname{range}(\mathbf{A}\mathbf{\Omega})$ and whose rank is at most
$\lvert r \rvert$, satisfies $\mathbf{A} - \mathbf{C} = \mathbf{E} - \mathbf{M}\mathbf{Z}^{\mathsf{H}}$
with $\mathbf{E} = \mathbf{A} - \mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}}$ and
$\mathbf{M} = \mathbf{E}\mathbf{\Omega}(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^{+}$. -/
theorem HasOrthonormalCols.sub_mul_pinv_mul_conjTranspose_eq (hZ : HasOrthonormalCols Z)
    (hΩ : (Ωᴴ * Z).rank = Z.rank) (A : Matrix m n 𝕜) :
    A - A * Ω * pinv (Zᴴ * Ω) * Zᴴ =
      (A - A * Z * Zᴴ) - (A - A * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω) * Zᴴ
/-- **Gram identity of the competitor**: $(\mathbf{A}-\mathbf{C})(\mathbf{A}-\mathbf{C})^{\mathsf{H}} =
\mathbf{E}\mathbf{E}^{\mathsf{H}} + \mathbf{M}\mathbf{M}^{\mathsf{H}}$, because
$\mathbf{E}\mathbf{Z} = \mathbf{0}$. -/
theorem HasOrthonormalCols.sub_mul_pinv_mul_conjTranspose_mul_conjTranspose_eq
    (hZ : HasOrthonormalCols Z) (hΩ : (Ωᴴ * Z).rank = Z.rank) (A : Matrix m n 𝕜) :
    (A - A * Ω * pinv (Zᴴ * Ω) * Zᴴ) * (A - A * Ω * pinv (Zᴴ * Ω) * Zᴴ)ᴴ =
      (A - A * Z * Zᴴ) * (A - A * Z * Zᴴ)ᴴ +
        (A - A * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω) * ((A - A * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω))ᴴ
/-- $$\|\mathbf{A} - \mathbf{C}\|_{\mathsf{F}}^2 = \|\mathbf{E}\|_{\mathsf{F}}^2 +
\|\mathbf{M}\|_{\mathsf{F}}^2\,.$$ -/
theorem HasOrthonormalCols.frobNorm_sub_mul_pinv_mul_conjTranspose_sq
    (hZ : HasOrthonormalCols Z) (hΩ : (Ωᴴ * Z).rank = Z.rank) (A : Matrix m n 𝕜) :
    frobNorm (A - A * Ω * pinv (Zᴴ * Ω) * Zᴴ) ^ 2 =
      frobNorm (A - A * Z * Zᴴ) ^ 2 + frobNorm ((A - A * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω)) ^ 2
```

Proof routes. The rank hypothesis with `hZ.rank_eq` and `mulVec_injective_iff_rank_eq` makes
$(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^{\mathsf{H}} = \mathbf{\Omega}^{\mathsf{H}}\mathbf{Z}$
injective, so $(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^{+} =
\mathbf{I}$ (`mul_pinv_self_of_injective_conjTranspose`). Then $\mathbf{A}\mathbf{\Omega} =
\mathbf{A}\mathbf{Z}(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega}) + \mathbf{E}\mathbf{\Omega}$ gives
$\mathbf{C} = \mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}} + \mathbf{M}\mathbf{Z}^{\mathsf{H}}$
(noncommutative ring algebra). Gram: expand, $\mathbf{E}\mathbf{Z} = \mathbf{A}\mathbf{Z} -
\mathbf{A}\mathbf{Z}(\mathbf{Z}^{\mathsf{H}}\mathbf{Z}) = \mathbf{0}$ kills the cross terms and
$\mathbf{Z}^{\mathsf{H}}\mathbf{Z} = \mathbf{I}$ the last. Frobenius: `frobInner E (M * Zᴴ)` is
$\operatorname{Re}\operatorname{tr}((\mathbf{E}\mathbf{Z})^{\mathsf{H}}\mathbf{M}) = 0$, Pythagoras,
and `frobNorm_mul_conjTranspose_right hZ`. Degenerate: necessity as in §3; nothing else bites. Not
stated: $\operatorname{rank}\mathbf{C} \le \lvert r \rvert$ (`Matrix.rank_mul_le_right` then
`Matrix.rank_le_card_height`) and $\operatorname{range}\mathbf{C} \le
\operatorname{range}(\mathbf{A}\mathbf{\Omega})$ (`range_mulVecLin_le_iff_exists_mul` with
`Matrix.mul_assoc`): one line each, used inside the proof of §3.2's truncation for free (§6).

### 3.2 `LowRank/Structural/RangeFinder.lean`: the structural bound for any frame (6)

```lean
/-- **The structural bound of the range finder, Gram form.** For $\mathbf{Z}$ with orthonormal
columns and $\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega}$ of full row rank, in every unitarily invariant
norm,
$$\bigl\|(\mathbf{A} - \mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A})^{\mathsf{H}}
(\mathbf{A} - \mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A})\bigr\|_{\Phi} \le
\|\mathbf{E}^{\mathsf{H}}\mathbf{E}\|_{\Phi} + \|\mathbf{M}^{\mathsf{H}}\mathbf{M}\|_{\Phi}\,,$$
that is $\Phi(\sigma(\cdot)^2)$ of the error: every quadratic unitarily invariant norm, Schatten
$\|\cdot\|_{S_p}^2$ for $p \ge 2$, never $p < 2$ (review A2). With $\mathbf{A}\mathbf{Z}
\mathbf{Z}^{\mathsf{H}} = \llbracket\mathbf{A}\rrbracket_k$ (rewrite with it) this is
HMT Theorem 9.1 in every quadratic norm. Result: range-finder-structural-bound -/
theorem SymmetricGauge.matrixNorm_conjTranspose_mul_self_sub_rsvd_le (Φ : SymmetricGauge)
    (hZ : HasOrthonormalCols Z) (hΩ : (Ωᴴ * Z).rank = Z.rank) (A : Matrix m n 𝕜) :
    Φ.matrixNorm ((A - rsvd A Ω)ᴴ * (A - rsvd A Ω)) ≤
      Φ.matrixNorm ((A - A * Z * Zᴴ)ᴴ * (A - A * Z * Zᴴ)) +
        Φ.matrixNorm (((A - A * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω))ᴴ *
          ((A - A * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω)))
/-- **The structural bound, unsquared triangle form**, in every unitarily invariant norm:
$\|\mathbf{A} - \mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A}\|_{\Phi} \le \|\mathbf{E}\|_{\Phi} +
\|\mathbf{M}\|_{\Phi}$. Incomparable with the Gram form: this one reaches every norm, the Gram form
is sharper for the squared quadratic norms. Result: range-finder-structural-bound -/
theorem SymmetricGauge.matrixNorm_sub_rsvd_le (Φ : SymmetricGauge) (hZ : HasOrthonormalCols Z)
    (hΩ : (Ωᴴ * Z).rank = Z.rank) (A : Matrix m n 𝕜) :
    Φ.matrixNorm (A - rsvd A Ω) ≤
      Φ.matrixNorm (A - A * Z * Zᴴ) + Φ.matrixNorm ((A - A * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω))
/-- Spectral form: $\|\mathbf{A} - \mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A}\|_2^2 \le
\|\mathbf{E}\|_2^2 + \|\mathbf{M}\|_2^2$ (HMT Theorem 9.1, spectral). Result: range-finder-structural-bound -/
theorem HasOrthonormalCols.specNorm_sub_rsvd_sq_le (hZ : HasOrthonormalCols Z)
    (hΩ : (Ωᴴ * Z).rank = Z.rank) (A : Matrix m n 𝕜) :
    specNorm (A - rsvd A Ω) ^ 2 ≤
      specNorm (A - A * Z * Zᴴ) ^ 2 + specNorm ((A - A * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω)) ^ 2
/-- Unsquared spectral form, MT Theorem 11.4's shape and the step of HMT 10.6:
$\|\mathbf{A} - \mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A}\|_2 \le \|\mathbf{E}\|_2 +
\|\mathbf{M}\|_2$. Result: range-finder-structural-bound -/
theorem HasOrthonormalCols.specNorm_sub_rsvd_le (hZ : HasOrthonormalCols Z)
    (hΩ : (Ωᴴ * Z).rank = Z.rank) (A : Matrix m n 𝕜) :
    specNorm (A - rsvd A Ω) ≤
      specNorm (A - A * Z * Zᴴ) + specNorm ((A - A * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω))
/-- Frobenius form: $\|\mathbf{A} - \mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A}\|_{\mathsf{F}}^2
\le \|\mathbf{E}\|_{\mathsf{F}}^2 + \|\mathbf{M}\|_{\mathsf{F}}^2$ (HMT Theorem 9.1, Frobenius;
Woodruff Lemma 48 for any frame). Result: range-finder-structural-bound -/
theorem HasOrthonormalCols.frobNorm_sub_rsvd_sq_le (hZ : HasOrthonormalCols Z)
    (hΩ : (Ωᴴ * Z).rank = Z.rank) (A : Matrix m n 𝕜) :
    frobNorm (A - rsvd A Ω) ^ 2 ≤
      frobNorm (A - A * Z * Zᴴ) ^ 2 + frobNorm ((A - A * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω)) ^ 2
/-- **Truncation for free.** For any $\mathbf{Q}$ with orthonormal columns whose range contains
$\operatorname{range}(\mathbf{A}\mathbf{\Omega})$ and any $k \ge \lvert r \rvert$,
$$\|\mathbf{A} - \mathbf{Q}\llbracket\mathbf{Q}^{\mathsf{H}}\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2
\le \|\mathbf{E}\|_{\mathsf{F}}^2 + \|\mathbf{M}\|_{\mathsf{F}}^2\,:$$
the rank-$k$ restricted projection keeps the bound of the untruncated range finder, since the
competitor has rank at most $\lvert r \rvert$ and lies in $\operatorname{range}\mathbf{Q}$.
Result: truncated-range-finder-structural-bound -/
theorem HasOrthonormalCols.frobNorm_sub_mul_truncatedSVD_sq_le [DecidableEq q] {A : Matrix m n 𝕜}
    {Q : Matrix m q 𝕜} (hQ : HasOrthonormalCols Q)
    (hQY : LinearMap.range (A * Ω).mulVecLin ≤ LinearMap.range Q.mulVecLin)
    (hZ : HasOrthonormalCols Z) (hΩ : (Ωᴴ * Z).rank = Z.rank) {k : ℕ}
    (hk : Fintype.card r ≤ k) :
    frobNorm (A - Q * truncatedSVD (Qᴴ * A) k) ^ 2 ≤
      frobNorm (A - A * Z * Zᴴ) ^ 2 + frobNorm ((A - A * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω)) ^ 2
```

(In the last statement `A` is implicit, determined by `hQY`.)

Proof routes. All go through $\mathbf{R} := \mathbf{A} - $ `rsvd A Ω` $=
(\mathbf{I}-\mathbf{P}_{\mathbf{Y}})\mathbf{A} = (\mathbf{I}-\mathbf{P}_{\mathbf{Y}})(\mathbf{A} -
\mathbf{C})$ (`sub_rsvd`; $\mathbf{P}_{\mathbf{Y}}\mathbf{C} = \mathbf{C}$ by
`rangeProjector_mul_eq_self_iff` and `range_mulVecLin_le_iff_exists_mul`). *Gram:*
$\lVert\mathbf{R}^{\mathsf{H}}\mathbf{R}\rVert_\Phi = \lVert\mathbf{R}\mathbf{R}^{\mathsf{H}}\rVert_\Phi$
(S0's `SymmetricGauge.matrixNorm_mul_conjTranspose_self`); $\sigma_i(\mathbf{R}) \le
\sigma_i(\mathbf{A}-\mathbf{C})$ (`IsStarProjection.singularValues_mul_le` with
`isStarProjection_one_sub_rangeProjector`), squared through S0's
`singularValues_mul_conjTranspose_self`, so $\lVert\mathbf{R}\mathbf{R}^{\mathsf{H}}\rVert_\Phi \le
\lVert(\mathbf{A}-\mathbf{C})(\mathbf{A}-\mathbf{C})^{\mathsf{H}}\rVert_\Phi$
(`matrixNorm_le_of_singularValues_le`); then the Gram identity, `matrixNorm_add_le`, and the gauge
equality twice more. TW's proof of Proposition 8.5 is this argument for Schatten norms; it needs no
basis, no diagonal $\mathbf{\Sigma}$ and no HMT Propositions 8.2, 8.3. *Triangle:*
`matrixNorm_mul_le_of_isStarProjection`, the linear identity, `matrixNorm_add_le`,
`matrixNorm_neg`, `matrixNorm_mul_conjTranspose_right_of_hasOrthonormalCols`. *Spectral:* the Gram
and triangle forms at `lpGauge ⊤ le_top` (`lpGauge_top_matrixNorm`, `specNorm_conjTranspose_mul_self`).
*Frobenius:* `frobNorm_one_sub_rangeProjector_mul_le_frobNorm_sub_mul` at $\mathbf{B} =
\mathbf{A}\mathbf{\Omega}$, $\mathbf{X} = (\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^{+}
\mathbf{Z}^{\mathsf{H}}$, then the exact identity of §3.1 (not the Gram form: the identity is the
shorter route and is Woodruff's). *Truncation for free:* `HasOrthonormalCols.frobNorm_sub_mul_truncatedSVD_le_of_rank_le`
at $\mathbf{B} = \mathbf{Q}^{\mathsf{H}}\mathbf{C}$ (rank at most $\lvert r \rvert \le k$), where
$\mathbf{Q}\mathbf{Q}^{\mathsf{H}}\mathbf{C} = \mathbf{C}$ (`hQ.rangeProjector_eq`, `hQY`), then the
exact identity. Degenerate: `hk` is necessary ($\mathbf{A} = \mathbf{\Omega} = \mathbf{Z} =
\mathbf{I}_2$, $k = 0$: left side $2$, right side $0$); $k$ at or above
$\operatorname{rank}(\mathbf{Q}^{\mathsf{H}}\mathbf{A})$ gives the untruncated residual, covered;
`q` empty forces $\mathbf{A}\mathbf{\Omega} = \mathbf{0}$, so $\mathbf{C} = \mathbf{0}$ and the left
side $\lVert\mathbf{A}\rVert_{\mathsf{F}}^2 = \lVert\mathbf{A}-\mathbf{C}\rVert_{\mathsf{F}}^2$ equals
the right side by §3.1.

Usage (S3's top-$k$ reading, Q3):
```lean
obtain ⟨Z, hZ, hZA⟩ :=
  exists_hasOrthonormalCols_mul_mul_conjTranspose_eq_truncatedSVD (p := Fin k) A (Fintype.card_fin k) hk
have h := hZ.specNorm_sub_rsvd_sq_le hΩ A
rw [hZA, specNorm_sub_truncatedSVD] at h
-- h : specNorm (A - rsvd A Ω) ^ 2 ≤
--   singularValues A k ^ 2 + specNorm ((A - truncatedSVD A k) * Ω * pinv (Zᴴ * Ω)) ^ 2
```
For R4's block moment S3 then writes $\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k =
(\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k)\mathbf{V}_2\mathbf{V}_2^{\mathsf{H}}$ for a completion
$\mathbf{V}_2$ (`HasOrthonormalCols.exists_fromCols`, `mul_conjTranspose_add_mul_conjTranspose`), which
gives `S * (V₂ᴴ * Ω) * pinv (Zᴴ * Ω)` with `S = (A - truncatedSVD A k) * V₂`, the shape of
`integral_frobNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix`.

### 3.3 `LowRank/Structural/RangeFinder.lean`: subspace injections, AMM, Nyström (4)

```lean
/-- **The structural bound under a subspace injection** (the deterministic core of CEMT
Theorem 2.2): if $\mathbf{\Omega}^{\mathsf{H}}$ is a subspace injection for
$\operatorname{range}\mathbf{Z}$ with constant $a > 0$,
$$\|\mathbf{A} - \mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A}\|_{\mathsf{F}}^2 \le
\|\mathbf{E}\|_{\mathsf{F}}^2 + \frac{\|\mathbf{E}\mathbf{\Omega}\|_{\mathsf{F}}^2}{a}\,.$$
The rank hypothesis follows from the injection. Result: range-finder-structural-bound -/
theorem IsSubspaceInjection.frobNorm_sub_rsvd_sq_le {a : ℝ} (h : IsSubspaceInjection Ωᴴ Z a)
    (hZ : HasOrthonormalCols Z) (ha : 0 < a) (A : Matrix m n 𝕜) :
    frobNorm (A - rsvd A Ω) ^ 2 ≤
      frobNorm (A - A * Z * Zᴴ) ^ 2 + frobNorm ((A - A * Z * Zᴴ) * Ω) ^ 2 / a
/-- **The noise term as an approximate-multiplication error.** For any test matrix,
$$\mathbf{M} = \bigl(\mathbf{E}\mathbf{\Omega}\mathbf{\Omega}^{\mathsf{H}}\mathbf{Z} -
\mathbf{E}\mathbf{Z}\bigr)\bigl((\mathbf{\Omega}^{\mathsf{H}}\mathbf{Z})^{\mathsf{H}}
\mathbf{\Omega}^{\mathsf{H}}\mathbf{Z}\bigr)^{+}\,,$$
where $\mathbf{E}\mathbf{Z} = \mathbf{0}$: the first factor is the error of the sketched product
$(\mathbf{\Omega}^{\mathsf{H}}\mathbf{E}^{\mathsf{H}})^{\mathsf{H}}(\mathbf{\Omega}^{\mathsf{H}}\mathbf{Z})$
for $\mathbf{E}\mathbf{Z}$, the shape `HasJLMoment`'s AMM bounds. -/
theorem HasOrthonormalCols.sub_mul_mul_pinv_eq (hZ : HasOrthonormalCols Z) (A : Matrix m n 𝕜)
    (Ω : Matrix n l 𝕜) :
    (A - A * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω) =
      ((A - A * Z * Zᴴ) * Ω * Ωᴴ * Z - (A - A * Z * Zᴴ) * Z) * pinv ((Ωᴴ * Z)ᴴ * (Ωᴴ * Z))
/-- Under a subspace injection with constant $a > 0$, in every unitarily invariant norm,
$\|\mathbf{M}\|_{\Phi} \le \|\mathbf{E}\mathbf{\Omega}\mathbf{\Omega}^{\mathsf{H}}\mathbf{Z} -
\mathbf{E}\mathbf{Z}\|_{\Phi} / a$ (Woodruff Lemma 45's step). -/
theorem IsSubspaceInjection.matrixNorm_sub_mul_mul_pinv_le {a : ℝ}
    (h : IsSubspaceInjection Ωᴴ Z a) (hZ : HasOrthonormalCols Z) (ha : 0 < a)
    (Φ : SymmetricGauge) (A : Matrix m n 𝕜) :
    Φ.matrixNorm ((A - A * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω)) ≤
      Φ.matrixNorm ((A - A * Z * Zᴴ) * Ω * Ωᴴ * Z - (A - A * Z * Zᴴ) * Z) / a
/-- **The structural bound of Nyström approximation**, in every unitarily invariant norm: for
positive semidefinite $\mathbf{H}$, $\mathbf{Z}$ with orthonormal columns and
$\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega}$ of full row rank, with
$\mathbf{H}_\perp = (\mathbf{I}-\mathbf{Z}\mathbf{Z}^{\mathsf{H}})\mathbf{H}
(\mathbf{I}-\mathbf{Z}\mathbf{Z}^{\mathsf{H}})$,
$$\|\mathbf{H} - \mathbf{H}\langle\mathbf{\Omega}\rangle\|_{\Phi} \le \|\mathbf{H}_\perp\|_{\Phi} +
\bigl\|((\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^{+})^{\mathsf{H}}\,\mathbf{\Omega}^{\mathsf{H}}
\mathbf{H}_\perp\mathbf{\Omega}\,(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^{+}\bigr\|_{\Phi}\,.$$
No square root appears: kernel and Gram matrices apply it directly. With $\mathbf{Z}$ a top-$k$
eigenvector frame, $\mathbf{H}_\perp = \mathbf{H} - \llbracket\mathbf{H}\rrbracket_k$.
Result: nystrom-structural-bound -/
theorem SymmetricGauge.matrixNorm_sub_nystrom_le_of_hasOrthonormalCols [DecidableEq n]
    (Φ : SymmetricGauge) {H : Matrix n n 𝕜} (hH : H.PosSemidef) (hZ : HasOrthonormalCols Z)
    (hΩ : (Ωᴴ * Z).rank = Z.rank) :
    Φ.matrixNorm (H - nystrom H Ω) ≤
      Φ.matrixNorm ((1 - Z * Zᴴ) * H * (1 - Z * Zᴴ)) +
        Φ.matrixNorm ((pinv (Zᴴ * Ω))ᴴ * (Ωᴴ * ((1 - Z * Zᴴ) * H * (1 - Z * Zᴴ)) * Ω) *
          pinv (Zᴴ * Ω))
```

Proof routes. *OSI:* `h.rank_mul_eq ha` (S0) gives the rank hypothesis; the Frobenius form of §3.2;
`IsSubspaceInjection.frobNorm_mul_pinv_sq_le h hZ ha ((A - A * Z * Zᴴ) * Ω)`, whose
`pinv ((Ωᴴ * Z)ᴴ)` is `pinv (Zᴴ * Ω)` by `Matrix.conjTranspose_mul` and
`conjTranspose_conjTranspose`. *AMM identity* (no rank hypothesis): L4 at
$\mathbf{G} = \mathbf{Z}^{\mathsf{H}}\mathbf{\Omega}$ gives $\mathbf{G}^{+} = \mathbf{G}^{\mathsf{H}}
(\mathbf{G}\mathbf{G}^{\mathsf{H}})^{+}$ with $\mathbf{G}^{\mathsf{H}} = \mathbf{\Omega}^{\mathsf{H}}
\mathbf{Z}$ and $\mathbf{G}\mathbf{G}^{\mathsf{H}} = (\mathbf{\Omega}^{\mathsf{H}}\mathbf{Z})^{\mathsf{H}}
\mathbf{\Omega}^{\mathsf{H}}\mathbf{Z}$; $\mathbf{E}\mathbf{Z} = \mathbf{0}$ by `hZ`. *AMM bound:*
`matrixNorm_mul_le_mul_specNorm`; with $\mathbf{X} = \mathbf{\Omega}^{\mathsf{H}}\mathbf{Z}$, the
injection reads $a\mathbf{I} \preceq \mathbf{X}^{\mathsf{H}}\mathbf{X}$ (`hZ.conjTranspose_mul_self`),
so $\lVert\mathbf{X}^{+}\rVert_2^2 \le a^{-1}$ (`specNorm_pinv_sq_le_inv_of_smul_one_le`) and
$\lVert(\mathbf{X}^{\mathsf{H}}\mathbf{X})^{+}\rVert_2 = \lVert\mathbf{X}^{+}(\mathbf{X}^{+})^{\mathsf{H}}
\rVert_2 = \lVert\mathbf{X}^{+}\rVert_2^2$ (`pinv_conjTranspose_mul_self`,
`specNorm_conjTranspose_mul_self` at $(\mathbf{X}^{+})^{\mathsf{H}}$). *Nyström:* S0's
`Matrix.PosSemidef.sub_nystrom_eq` writes $\mathbf{H} - \mathbf{H}\langle\mathbf{\Omega}\rangle$ as
the Gram matrix of `F - rsvd F Ω` at $\mathbf{F} = \mathbf{H}^{1/2}$ (`CFC.sqrt`); the Gram form of
§3.2 at $\mathbf{F}$; then $\mathbf{F} - \mathbf{F}\mathbf{Z}\mathbf{Z}^{\mathsf{H}} =
\mathbf{F}(\mathbf{I}-\mathbf{Z}\mathbf{Z}^{\mathsf{H}})$, $\mathbf{F}^{\mathsf{H}}\mathbf{F} =
\mathbf{H}$ (`CFC.sqrt_mul_sqrt_self`, Hermitian square root), so the two Gram matrices are the
displayed ones. Degenerate: OSI and AMM bound at `r` empty are $0 \le 0$-type; the AMM identity holds
at every rank, including $\mathbf{\Omega} = \mathbf{0}$ (both sides $\mathbf{0}$); Nyström: §3 list.

Why the OSI form is Frobenius only, and the AMM bound is a gauge statement: CEMT Theorem 2.2 and
Woodruff Lemma 45 are Frobenius statements, and the OSI's isotropy computes only
$\mathbb{E}\lVert\mathbf{E}\mathbf{\Omega}\rVert_{\mathsf{F}}^2$, so a Gram-gauge OSI form has no
consumer (Q6). The AMM bound's proof is the same in every gauge, so it is stated once for every gauge
(CONTRIBUTING §5.4) and S7 instantiates `lpGauge 2 one_le_two`.

### 3.4 Matrix layer (4)

```lean
-- Matrix/Spectral/LowRank.lean, after `rangeProjector_truncatedSVD_mul`
/-- The truncated SVD is $\mathbf{A}$ times the projector onto its own row space:
$\mathbf{A}\mathbf{P}_{\llbracket\mathbf{A}\rrbracket_k^{\mathsf{H}}} = \llbracket\mathbf{A}\rrbracket_k$. -/
theorem mul_rangeProjector_conjTranspose_truncatedSVD (A : Matrix m n 𝕜) (k : ℕ) :
    A * rangeProjector (truncatedSVD A k)ᴴ = truncatedSVD A k
/-- **A frame of a dominant right singular subspace.** For $\lvert p \rvert = k \le \lvert n \rvert$
there is $\mathbf{Z}$ with orthonormal columns indexed by $p$ and
$\mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}} = \llbracket\mathbf{A}\rrbracket_k$ (for
$k \ge \operatorname{rank}\mathbf{A}$, any frame containing the row space). -/
theorem exists_hasOrthonormalCols_mul_mul_conjTranspose_eq_truncatedSVD {p : Type*} [Fintype p]
    [DecidableEq p] (A : Matrix m n 𝕜) {k : ℕ} (hp : Fintype.card p = k)
    (hk : k ≤ Fintype.card n) :
    ∃ Z : Matrix n p 𝕜, HasOrthonormalCols Z ∧ A * Z * Zᴴ = truncatedSVD A k
/-- **Tail flattening**: $d\,\sigma_{k+d}(\mathbf{A})^2 \le
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$, since the $d$ singular values
$\sigma_k, \dots, \sigma_{k+d-1}$ are at least $\sigma_{k+d}$. Used to bound the spectral residual
of a range finder split at $k + d$ by the Frobenius tail at $k$. -/
theorem natCast_mul_singularValues_add_sq_le_frobNorm_sub_truncatedSVD_sq (A : Matrix m n 𝕜)
    (k d : ℕ) : (d : ℝ) * singularValues A (k + d) ^ 2 ≤ frobNorm (A - truncatedSVD A k) ^ 2
-- Matrix/Pseudoinverse/Pinv.lean, after `pinv_eq_pinv_conjTranspose_mul_self_mul`
/-- The pseudoinverse through the other Gram matrix:
$\mathbf{A}^{+} = \mathbf{A}^{\mathsf{H}}(\mathbf{A}\mathbf{A}^{\mathsf{H}})^{+}$. -/
theorem pinv_eq_conjTranspose_mul_pinv_mul_conjTranspose_self (A : Matrix m n 𝕜) :
    pinv A = Aᴴ * pinv (A * Aᴴ)
```

Proof routes. *L1:* `LowRank.lean`'s private `exists_isSVD_truncatedSVD_sub` gives SVDs of
$\mathbf{T} = \llbracket\mathbf{A}\rrbracket_k$ and $\mathbf{A}-\mathbf{T}$ with the same factors and
complementary diagonals, so $(\mathbf{A}-\mathbf{T})\mathbf{T}^{\mathsf{H}} = \mathbf{0}$ (the row
twin of the private `conjTranspose_truncatedSVD_mul_sub`); then
`rangeProjector_mul_eq_zero_iff` at $\mathbf{T}^{\mathsf{H}}$ gives $(\mathbf{A}-\mathbf{T})
\mathbf{P}_{\mathbf{T}^{\mathsf{H}}} = \mathbf{0}$, and $\mathbf{T}\mathbf{P}_{\mathbf{T}^{\mathsf{H}}} =
\mathbf{T}$ by `rangeProjector_mul_self` conjugated. It must live in `LowRank.lean` (private API).
*L2:* `exists_hasOrthonormalCols_range_le` at $\mathbf{T}^{\mathsf{H}}$ ($\operatorname{rank}\le k =
\lvert p \rvert \le \lvert n \rvert$) gives $\mathbf{Z}$ with $\operatorname{range}\mathbf{T}^{\mathsf{H}}
\le \operatorname{range}\mathbf{Z}$. If $k \le \operatorname{rank}\mathbf{A}$, `rank_truncatedSVD`
gives rank $k$, the ranges are equal (equal `finrank`), $\mathbf{Z}\mathbf{Z}^{\mathsf{H}} =
\mathbf{P}_{\mathbf{T}^{\mathsf{H}}}$ (`hZ.rangeProjector_eq`, `rangeProjector_inj`), and L1 closes.
Otherwise $\mathbf{T} = \mathbf{A}$ (`truncatedSVD_of_rank_le`) and $\mathbf{A}\mathbf{Z}
\mathbf{Z}^{\mathsf{H}} = \mathbf{A}$ because $\mathbf{Z}\mathbf{Z}^{\mathsf{H}}$ fixes
$\operatorname{range}\mathbf{A}^{\mathsf{H}}$ (`rangeProjector_mul_eq_self_iff`, conjugated). No new
import (`SVD.lean` imports `Basic/OrthonormalBasis`). *L3:* `frobNorm_sub_truncatedSVD_sq`; if
$k + d \le \min(\lvert m\rvert,\lvert n\rvert)$, restrict the sum to `Finset.Ico k (k + d)` and use
`Finset.card_nsmul_le_sum` with `singularValues_antitone`; otherwise $\sigma_{k+d} = 0$
(`singularValues_eq_zero_iff`). *L4:* `pinv_eq_pinv_conjTranspose_mul_self_mul` at
$\mathbf{A}^{\mathsf{H}}$, `pinv_conjTranspose`, conjugate, and Hermitian
$(\mathbf{A}\mathbf{A}^{\mathsf{H}})^{+}$ (`Matrix.IsHermitian.pinv`). Degenerate: L1 at $k = 0$
($\mathbf{T} = \mathbf{0}$, `rangeProjector_zero`) and $k \ge \operatorname{rank}\mathbf{A}$
($\mathbf{T} = \mathbf{A}$); L2 at $k = 0$ (empty frame, `truncatedSVD_zero`), `m` empty
($\mathbf{A} = \mathbf{0}$); L3 at $d = 0$ ($0 \le$), past the smaller dimension (zero padding).
Consumers: L1, L2 the top-$k$ reading (S3, S5 at $\mathbf{F} = \mathbf{H}^{1/2}$, S6 at
$k' = \lceil\ell/2\rceil$); L3 S6; L4 the AMM identity.

## 4. Files

| # | File | Statements | Lines (est.) | Imports (new) | Depends on |
|---|---|---|---|---|---|
| 1 | `Matrix/Spectral/LowRank.lean` (extended, 362 now) | 3 (L1 to L3) | +100 | none | none |
| 2 | `Matrix/Pseudoinverse/Pinv.lean` (extended, 367 now) | 1 (L4) | +10 | none | none |
| 3 | `LowRank/Structural/RangeFinder.lean` (new) | 13 (3 + 6 + 4) | 420 | `Matrix/Factorizations/SketchedLowRank`, `Matrix/Factorizations/Nystrom` (S0), `Matrix/Spectral/ProjectedLowRank`, `Matrix/Pseudoinverse/NormBounds`, `Sketching/Properties/LeastSquares` | 1, 2, S0 |

S1 is about 530 lines and 17 public declarations (brief: 500). Files 1 and 2 are independent of each
other and of S0, and are short: one agent may own both (CONTRIBUTING §11). File 3 needs S0's
`SketchedLowRank.lean`, `Nystrom.lean` and `UnitarilyInvariant.lean`/`SingularValues.lean` additions
and the Sketching addition `IsSubspaceInjection.rank_mul_eq`; it is one agent's file, in the order
§3.1, §3.2, §3.3. `LowRank/` is a new directory: `mk_all` adds the root import.

## 5. Material

**Prototype** (read-only, `~/Documents/prove2me/lean/NLAlib/LowRank/`; ledger dispositions):
- `Structural/RangeFinder.lean` (235 lines, real, `Fin k` blocks, a block SVD hypothesis
  `A = U₁ S₁ V₁ᵀ + U₂ S₂ V₂ᵀ`): `mul_eq_mul_add_mul_of_eq_add` → cut (block algebra; the frame form
  has no blocks); `sub_mul_pinvR_mul_transpose_eq` → `HasOrthonormalCols.sub_mul_pinv_mul_conjTranspose_eq`;
  `frobSq_sub_mul_pinvR_mul_transpose_eq` → `HasOrthonormalCols.frobNorm_sub_mul_pinv_mul_conjTranspose_sq`;
  `mul_transpose_mul_competitor` (private) → cut (one line, §3.1);
  `frobSq_residual_le_of_range_subset` → `HasOrthonormalCols.frobNorm_sub_rsvd_sq_le` (its "any `Q`
  whose range contains $\operatorname{range}(\mathbf{A}\mathbf{\Omega})$" is `rsvd` after
  `hQ.rangeProjector_eq`; the larger-range variant is cut, §6);
  `frobSq_sub_mul_le_of_isBestFrobRankApprox_of_range_subset` →
  `HasOrthonormalCols.frobNorm_sub_mul_truncatedSVD_sq_le` (the optimality-hypothesis form is S2a's,
  D5); `sub_mul_sq_le_sum_Ico_sq`, `sq_le_sum_Ico_sq_div` →
  `natCast_mul_singularValues_add_sq_le_frobNorm_sub_truncatedSVD_sq` (sequence forms cut,
  `Finset.card_nsmul_le_sum`); `sq_le_four_div_mul_sum_Ico_sq`,
  `sq_singularValues_le_four_div_mul_sum_Ico_sq` → S6 (the $\lceil t/2\rceil$, $4k \le t$ arithmetic
  of truncated GN's spectral residual).
- `RangeFinding/SpectralRangeFinder.lean` (433): `specNorm_residual_sq_le_of_range_subset` →
  `HasOrthonormalCols.specNorm_sub_rsvd_sq_le`; `specNorm_residual_le_of_range_subset` →
  `HasOrthonormalCols.specNorm_sub_rsvd_le`; `exists_svd_right_blocks_specNorm` → cut (L2, and
  `exists_isSVD_fromCols` exists); `integrable_and_integral_frobNorm_pinvR_gaussianMatrix_le`,
  `integrable_and_integral_specNorm_mul_block_mul_pinvR_block_le` → exist (R4 block moments);
  `integral_specNorm_residual_le_of_gaussian` and its two variants → S3 (HMT 10.6).
- `projResidual` (the prototype's residual with a hypothesis-level `Q`) → cut (`rsvd`, `sub_rsvd`; D1).

**The maintainer's formalization** (read-only material, never cited, not ledgered; D13):
`~/Documents/Papers/LRA-paper/formal/LRA/Deterministic/RangeFinder.lean`, of which the prototype file is
a port; its `Z_eq`, `frobSq_A_sub_Z`, `hmt_third`, `tail_bound` are the shapes above.
`gamma_le_OPT` ($\lVert\mathbf{Q}^{\mathsf{H}}\mathbf{A} - \llbracket\mathbf{Q}^{\mathsf{H}}\mathbf{A}
\rrbracket_k\rVert_{\mathsf{F}} \le \lVert\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\rVert_{\mathsf{F}}$,
a compression fact) is truncation, S2a or S6. No S1 result first appears in the manuscript; the tail
flattening is the elementary averaging step and is a helper with no citation.

**Literature**, locators confirmed against the PDFs (`~/Documents/prove2me/books/`,
`/tmp/claude-1000/p0/papers/`):
- HMT (arXiv v2, printed pages): §9.1 and (9.1), (9.2) (p. 50); Theorem 9.1 (p. 51: "either the
  spectral norm or the Frobenius norm", $\mathbf{\Omega}_1$ of full row rank, any $k \ge 0$; proof
  written for spectral); proof of Theorem 10.6 (p. 58: $\lVert(\mathbf{I}-\mathbf{P}_{\mathbf{Y}})
  \mathbf{A}\rVert \le \lVert\mathbf{\Sigma}_2\rVert + \lVert\mathbf{\Sigma}_2\mathbf{\Omega}_2
  \mathbf{\Omega}_1^{+}\rVert$ from 9.1).
- MT (printed = PDF + 402): Proposition 11.1 (p. 470); Theorem 11.4 (p. 472): unsquared spectral
  $\lVert(\mathbf{I}-\mathbf{P}_{\mathbf{Y}})\mathbf{B}\rVert \le \sigma_{k+1} +
  \lVert\mathbf{\Sigma}_2\mathbf{X}_2\mathbf{X}_1^{+}\rVert$, "a related inequality holds for every
  quadratic unitarily invariant norm"; credits Boutsidis, Mahoney and Drineas 2009.
- TW (arXiv:2306.12418 v3): Proposition 8.5 (p. 35), (8.2) for every Schatten $p \in [2,\infty]$,
  its proof (8.3) to (8.8) being the Gram route above; (8.1), the sharper parallel-sum form;
  proof of Theorem 8.1 and Corollary 8.2 (p. 37).
- Woodruff 2014: Lemma 45 (p. 63, proof p. 64 to 65, the change of basis $(\mathbf{S}\mathbf{U}_k)^{\mathsf{T}}
  = \mathbf{B}(\mathbf{S}\mathbf{U}_k)^{+}$ that the AMM identity replaces); Lemma 48 (p. 69): for any
  $\mathbf{Z}$ with $\mathbf{Z}^{\mathsf{T}}\mathbf{Z} = \mathbf{I}_k$ and
  $\operatorname{rank}(\mathbf{Z}^{\mathsf{T}}\mathbf{S}) = \operatorname{rank}\mathbf{Z} = k$,
  $\lVert\mathbf{A} - \mathbf{C}\mathbf{C}^{+}\mathbf{A}\rVert_{\mathsf{F}}^2 \le
  \lVert\mathbf{A} - \Pi_{\mathbf{C},k}(\mathbf{A})\rVert_{\mathsf{F}}^2 \le
  \lVert\mathbf{E}\rVert_{\mathsf{F}}^2 + \lVert\mathbf{E}\mathbf{S}(\mathbf{Z}^{\mathsf{T}}
  \mathbf{S})^{+}\rVert_{\mathsf{F}}^2$, credited to Boutsidis, Drineas and Magdon-Ismail.
- CEMT (printed = PDF − 2): Lemma 2.1 (p. 14); Theorem 2.2 and Imported Theorem 2.3 (p. 16;
  Imported 2.3: any orthonormal $\mathbf{Q}$ whose range contains
  $\operatorname{range}(\mathbf{A}\mathbf{\Omega})$, Frobenius); Imported Theorem 2.4 and
  Corollary 2.5 (p. 17).
- TYUC NeurIPS (arXiv:1706.05736): Appendix A has Theorem A.1 (expected Schatten-1 error of
  Nyström, S5), Proposition A.2 ($\hat{\mathbf{A}}_{\mathrm{nys}} = \mathbf{A}^{1/2}\mathbf{P}
  \mathbf{A}^{1/2}$, S0's correspondence) and Proposition A.6 (S2a's constant-2 lemma, with the
  attribution "[36, Prop. 7.1]", that is TYUC SIMAX). There is no deterministic structural Nyström
  lemma; brief §9.2 item 2's "S1: Lemma A.1" is corrected to "provenance for S0 and S5 only".
- Gittens and Mahoney 2016: not in hand; their deterministic Nyström bounds are instances of N1, but
  no locator is cited until the paper is read (brief §9.2, nice to have).

**Citations** (no new `references.bib` key: `HalkoMartinssonTropp2011`, `MartinssonTropp2020`,
`Woodruff2014`, `CamanoEpperlyMeyerTropp2025` exist; `TroppWebber2023` enters with S0's first PR;
D13):

| statement | citation | relation to the printed statement |
|---|---|---|
| competitor identities (§3.1) | [HalkoMartinssonTropp2011, Theorem 9.1 (proof)]; [Woodruff2014, Lemma 48 (proof)]; [TroppWebber2023, Proposition 8.5 (proof), (8.8)] | there with a partitioned SVD, $\mathbf{Z} = \mathbf{V}_1$; here any frame, any field |
| Gram form | [MartinssonTropp2020, Theorem 11.4]; [TroppWebber2023, Proposition 8.5, (8.2)]; [HalkoMartinssonTropp2011, Theorem 9.1] | there top-$k$ frames, spectral (MT, "related inequality" for quadratic norms) or Schatten $p \ge 2$ (TW); here any frame, every gauge of the Gram matrix |
| triangle form, unsquared spectral | [MartinssonTropp2020, Theorem 11.4]; [HalkoMartinssonTropp2011, proof of Theorem 10.6] | there spectral; here every gauge |
| spectral and Frobenius squared | [HalkoMartinssonTropp2011, Theorem 9.1]; [Woodruff2014, Lemma 48]; [CamanoEpperlyMeyerTropp2025, Imported Theorem 2.3] | there top-$k$ (HMT, CEMT) or any frame in Frobenius (Woodruff) |
| truncation for free | [Woodruff2014, Lemma 48] | there over $\mathbb{R}$ with "the best rank-$k$ approximation in the column space"; here $\mathbf{Q}\llbracket\mathbf{Q}^{\mathsf{H}}\mathbf{A}\rrbracket_k$ for any $\mathbf{Q}$ containing $\operatorname{range}(\mathbf{A}\mathbf{\Omega})$ |
| OSI form | [CamanoEpperlyMeyerTropp2025, Theorem 2.2 (proof), Lemma 2.1] | the deterministic core: there with probability 9/10 and an unspecified $C$; here the injection as a hypothesis and $1/a$ explicit |
| AMM identity and bound | [Woodruff2014, Lemma 45 (proof)] | there a change of basis with left singular vectors and the sketch on the left; here test orientation, any gauge, constant $1/a$ |
| Nyström structural bound | [MartinssonTropp2020, Proposition 11.1, Theorem 11.4]; [TroppWebber2023, proof of Theorem 8.1 and Corollary 8.2]; [CamanoEpperlyMeyerTropp2025, proof of Corollary 2.5] | there by the same composition for $\mathbf{F} = \mathbf{A}^{1/2}$ in trace or Schatten norms; here every gauge, stated in $\mathbf{H}$ alone |
| L1 to L4 | none (helpers; each docstring says what it is for) | |

Port provenance lines (CONTRIBUTING §6 item 3) on the six statements with a prototype source above.
**Result ids** (D11; ids are defined by `Result:` lines, S0 §8 item 7; none collides with the existing
`eckart-young-*`, `svd-existence`, `subspace-injection`, `sketch-and-solve-*`):
`range-finder-structural-bound` (D11's description, "the Gram form, every quadratic unitarily
invariant norm", on the Gram form; also on the triangle, spectral, Frobenius and OSI forms, which are
forms of the same result), `truncated-range-finder-structural-bound` (new; Woodruff Lemma 48's middle
inequality, distinct from S2a's `truncation-lemma`), `nystrom-structural-bound` (new). Competitor
identities, AMM forms and L1 to L4 carry none.

## 6. Cut, and why

- *HMT-instance declarations* (`…_of_mul_mul_conjTranspose_eq` twins of each bound, or an `IsSVD`
  block form): the reading is `rw [hZA]` on the general statements plus `specNorm_sub_truncatedSVD`
  (§3.2 usage); twins would double the statement count with one-line proofs (Q3).
- *The competitor's rank and range* (brief S1 list): `Matrix.rank_mul_le_right` with
  `Matrix.rank_le_card_height`, and `range_mulVecLin_le_iff_exists_mul`; one line each.
- *A residual for a larger range* ($\mathbf{P}_{\mathbf{X}}$ with $\operatorname{range}
  (\mathbf{A}\mathbf{\Omega}) \le \operatorname{range}\mathbf{X}$, prototype's "range subset"): the
  range-monotonicity lemmas of `Norms/Projector.lean` and `singularValues_one_sub_rangeProjector_mul_le`
  compose with `rsvd`; block Krylov, its consumer, is out of scope.
- *Unsquared Frobenius*: `Real.sqrt` of the squared form or the triangle form at `lpGauge 2`.
- *A Gram-gauge OSI form* $\lVert\mathbf{R}^{\mathsf{H}}\mathbf{R}\rVert_\Phi \le
  \lVert\mathbf{E}^{\mathsf{H}}\mathbf{E}\rVert_\Phi + \lVert(\mathbf{E}\mathbf{\Omega})^{\mathsf{H}}
  \mathbf{E}\mathbf{\Omega}\rVert_\Phi / a$: no consumer (Q6); the Gram form plus the pinv bound
  give it in two lines.
- *A combined Woodruff Lemma 45 bound* ($\lVert\mathbf{R}\rVert_{\mathsf{F}}^2 \le
  \lVert\mathbf{E}\rVert_{\mathsf{F}}^2 + (\lVert\text{AMM error}\rVert_{\mathsf{F}}/a)^2$): S7 composes
  the Frobenius form with the AMM bound; a third OSI-hypothesis statement on the same left side would
  need a name distinguishing two right sides (rule 4).
- *TW's parallel-sum form (8.1)*: sharper than (8.2), no consumer, and parallel sums are not in the
  library.
- *A Nyström trace (nuclear) corollary of N1*: `lpGauge_one_matrixNorm` and S5's PSD trace forms;
  S5's own note decides whether it wants it named.
- *Real-sequence tail lemmas and the $4/t$ form*: `Finset.card_nsmul_le_sum`; S6.
- *Definitions for $\mathbf{E}$, $\mathbf{M}$, $\mathbf{C}$*: Q4.

## 7. Questions and decisions

Hard-to-reverse items are marked **(hard)**. None needs the maintainer under the round's approval
rule (memory: serious, hard-to-reverse decisions only); Q2 is recorded for the checkpoint after S2b.

**Q1. The rank hypothesis `(Ωᴴ * Z).rank = Z.rank` (moderately hard).** Options: (a) S0's rank
spelling in the sketch orientation; (b) §5.3's full row rank `Function.Injective (Zᴴ * Ω)ᴴ.mulVec`;
(c) `IsUnit ((Zᴴ * Ω) * (Zᴴ * Ω)ᴴ)` (prototype). Recommendation (a): it is S0's spelling for "the
sketch keeps the rank of the basis" (S0 §8 item 2's rule), `IsSubspaceInjection.rank_mul_eq` produces
it literally for the OSI and OSE routes, and it is Woodruff Lemma 48's hypothesis verbatim. (b) is one
rewrite away (`mulVec_injective_iff_rank_eq`, `hZ.rank_eq`). Rework if changed: the hypothesis line of
ten S1 statements and their S3, S5, S6 uses.

**Q2. The error is `A - rsvd A Ω`, its Gram matrix `(A - rsvd A Ω)ᴴ * (A - rsvd A Ω)` (hard).**
Options: (a) the named output; (b) `(1 - rangeProjector (A * Ω)) * A`. Recommendation (a): S0 §8
item 4 allows either; users search for `rsvd`; the statements need no `1` and no `[DecidableEq m]`;
and the Gram matrix is then literally the right side of S0's correspondence
`conjTranspose_mul_self_sub_nystrom`, so S5 transfers every Gram-form result to Nyström by one
`rw`. Rework if reversed: the left side of every RSVD statement of S1, S3, S6, S7 (`sub_rsvd` makes
it mechanical, but the statement shapes are what consumers `exact`).

**Q3. The top-$k$ reading by a hypothesis and an existence lemma (not hard).** Options: (a) general
frame statements only, with `A * Z * Zᴴ = truncatedSVD A k` as the documented hypothesis and L2 for
existence; (b) an `IsSVD (fromCols U₁ U₂) … (fromCols V₁ V₂)` block form, HMT's literal shape;
(c) both general and top-$k$ declarations. Recommendation (a): one rewrite turns every bound into HMT's
($\mathbf{E} = \mathbf{A} - \llbracket\mathbf{A}\rrbracket_k$, choice-free norms); it obeys CONTRIBUTING
§5.2 (a frame with an equation, no basis columns); (b) needs extra bridge lemmas for the singular
values of $\mathbf{A}\mathbf{V}_2$ and repeats a five-part hypothesis in every statement; (c) doubles
the count with one-line corollaries. Additive if a consumer wants (c).

**Q4. No definitions for $\mathbf{E}$, $\mathbf{M}$, $\mathbf{C}$; $\mathbf{E}$ spelled
`A - A * Z * Zᴴ` (moderately hard).** Options: (a) inline, as S0 did for the Schur complement and the
core noise (S0 Q7); (b) `def`s such as `rangeFinderNoise A Ω Z`. Recommendation (a): the formulas are
what HMT, Woodruff and R4's block moments write, `rw [hZA]` reaches them, and a definition would
need its own unfolding at every R4 use. The spelling `A - A * Z * Zᴴ` rather than
`A * (1 - Z * Zᴴ)` makes the top-$k$ rewrite one step and keeps `1` out of the statements. Rework if
reversed: every S1 statement shape and the S3, S6, S7 uses.

**Q5. Gauge-statement namespaces (not hard).** A gauge statement whose only structured hypothesis
is a frame lives in `SymmetricGauge` with `Φ` first (`Φ.matrixNorm_sub_rsvd_le hZ hΩ A`), as
`UnitarilyInvariant.lean` and S0's Nyström helps do; a statement about an `IsSubspaceInjection` lives
in that namespace with `Φ` after it (CONTRIBUTING §5.2, dot notation). Non-gauge frame statements live
in `HasOrthonormalCols`. The Nyström structural bound takes the suffix `_of_hasOrthonormalCols` to
stay distinct from S0's `SymmetricGauge.matrixNorm_sub_nystrom_le` (rule 4, named by its hypothesis).

**Q6. The OSI form only in squared Frobenius norm (not hard).** CEMT Theorem 2.2 and S7 are
Frobenius, and an OSI's isotropy computes only $\mathbb{E}\lVert\mathbf{E}\mathbf{\Omega}
\rVert_{\mathsf{F}}^2$; D4's Gram-form primacy is met by the structural bound itself. Additive if S7
finds a spectral consumer (structured spectral AMM, deferred in Sketching §6.1).

**Q7. Tail flattening in the Matrix layer, subtraction-free (not hard).** The brief puts it in
`RangeFinder.lean`; its subject is singular values and `truncatedSVD`, so CONTRIBUTING §3 places it in
`LowRank.lean`. The form $d\,\sigma_{k+d}^2 \le \lVert\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k
\rVert_{\mathsf{F}}^2$ follows the §5.3 index-shift row (no truncated or real subtraction of indices);
S6 instantiates $k + d = \lceil\ell/2\rceil$.

**Q8. Truncation for free against `truncatedSVD (Qᴴ * A) k` (not hard).** It is Woodruff Lemma 48's
middle term for any basis containing $\operatorname{range}(\mathbf{A}\mathbf{\Omega})$, the form
`ProjectedLowRank.lean` already uses. D5's optimality-hypothesis form and the choice-free bridge to
`truncatedSVD (rsvd A Ω) k` are S2a's (D5 places the hypothesis decision there); S2a restates nothing
of S1.

**Q9. The Nyström structural bound in $\mathbf{H}$ alone (not hard).** Stated with the compression
$(\mathbf{I}-\mathbf{Z}\mathbf{Z}^{\mathsf{H}})\mathbf{H}(\mathbf{I}-\mathbf{Z}\mathbf{Z}^{\mathsf{H}})$
rather than a factor, so no square root or factor appears; a user with $\mathbf{H} =
\mathbf{F}^{\mathsf{H}}\mathbf{F}$ applies it directly, and the general-factor form is the Gram form
of §3.2 after `conjTranspose_mul_self_sub_nystrom`.

**Q10. Corrections of record (information).** Brief §9.2 item 2: TYUC NeurIPS has no structural
Lemma A.1 (§5). Brief §9.3's "structural bound with the rank-$k$ competitor ... CEMT Imported Theorem
2.3 and the remark after Theorem 1.3": CEMT's remark appeals to HMT Theorem 9.3 (spectral) for the
rank-$r$ upgrade and is not a Woodruff-48 statement; only Woodruff Lemma 48 is cited for truncation
for free. Boutsidis, Drineas and Magdon-Ismail 2014 is cited through Woodruff until it is in hand.

## 8. Amendments from the review (2026-10-15)

Review of this note (0 blocker, 2 major, 9 minor), all eleven amendments accepted by the
orchestrator, one corrected on inspection (A1(b)'s Hermitian clause, item 2); none rejected. Q1, Q2
and Q4 decided as recommended, Q2 moreover by the maintainer (item 14); Q3, Q5 to Q10 accepted as
recommended. The review verified, at every rank and shape the brief names (empty `r`, `l`, `m`,
`n`; `A = 0`; `Ω = 0`; rank-deficient `A * Ω`; $k$ at or above the rank; `Z` wider than
$\operatorname{rank}\mathbf{A}$; Hermitian non-PSD `H`; $a \le 0$), every statement of §3.1 to
§3.4, the necessity of each hypothesis where the note says so, every cited library signature, the
literature locators and the prototype ledger. Where an item below contradicts §0 to §7, it
supersedes them; §3 stays as drafted. Skeletons: the files of item 17.

1. **A1(a), the competitor's rank and range are stated** (replaces §6's second bullet and the
   "Not stated" sentence of §3.1; +2 in `RangeFinder.lean`, §3.1). The docstring of
   §3.1 claims both, and a docstring claim with no lemma is a defect (S0 §8 item 5); the brief's S1
   entry asks for them, and truncation for free and S2a's rank-$k$ competitor form use them. No frame
   and no rank hypothesis, so no `[DecidableEq r]`:
   ```lean
   theorem rank_mul_mul_pinv_mul_conjTranspose_le (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜)
       (Z : Matrix n r 𝕜) : (A * Ω * pinv (Zᴴ * Ω) * Zᴴ).rank ≤ Fintype.card r
   theorem range_mul_mul_pinv_mul_conjTranspose_le (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜)
       (Z : Matrix n r 𝕜) :
       LinearMap.range (A * Ω * pinv (Zᴴ * Ω) * Zᴴ).mulVecLin ≤ LinearMap.range (A * Ω).mulVecLin
   ```
   Routes: `Matrix.rank_mul_le_right` then `Matrix.rank_le_card_height`;
   `range_mulVecLin_le_iff_exists_mul` with `Matrix.mul_assoc`. They sit beside S0's
   `rank_rsvd_le` and `range_rsvd_le`. No result id.
2. **A1(b), L5: the truncated SVD of a PSD matrix, and the top-$k$ compression** (+2 in
   `Matrix/Spectral/LowRank.lean`, after L1; amends §3.4). The Nyström docstring's "with
   $\mathbf{Z}$ a top-$k$ eigenvector frame, $\mathbf{H}_\perp = \mathbf{H} -
   \llbracket\mathbf{H}\rrbracket_k$" had no lemma, and Q2's "S5 transfers by one `rw`" depended on
   it. Added:
   ```lean
   /-- The truncated SVD of a positive semidefinite matrix is positive semidefinite:
   $\llbracket\mathbf{A}\rrbracket_k \succeq \mathbf{0}$ for $\mathbf{A} \succeq \mathbf{0}$. -/
   theorem _root_.Matrix.PosSemidef.truncatedSVD {A : Matrix n n 𝕜} (hA : A.PosSemidef) (k : ℕ) :
       (truncatedSVD A k).PosSemidef
   /-- For positive semidefinite $\mathbf{H}$ and a frame with
   $\mathbf{H}\mathbf{Z}\mathbf{Z}^{\mathsf{H}} = \llbracket\mathbf{H}\rrbracket_k$,
   $(\mathbf{I}-\mathbf{Z}\mathbf{Z}^{\mathsf{H}})\mathbf{H}(\mathbf{I}-\mathbf{Z}\mathbf{Z}^{\mathsf{H}})
   = \mathbf{H} - \llbracket\mathbf{H}\rrbracket_k$. -/
   theorem _root_.Matrix.PosSemidef.one_sub_mul_mul_one_sub_eq_sub_truncatedSVD [DecidableEq n]
       {H : Matrix n n 𝕜} (hH : H.PosSemidef) (hZ : HasOrthonormalCols Z) {k : ℕ}
       (hZH : H * Z * Zᴴ = truncatedSVD H k) :
       (1 - Z * Zᴴ) * H * (1 - Z * Zᴴ) = H - truncatedSVD H k
   ```
   Routes. *L5a:* from the private SVD of `truncatedSVD` (L1's API), $\mathbf{A}\mathbf{v}_i =
   \sigma_i\mathbf{u}_i$ and, $\mathbf{A}$ being Hermitian, $\mathbf{A}\mathbf{u}_i = \sigma_i
   \mathbf{v}_i$, so $\mathbf{A}(\mathbf{u}_i - \mathbf{v}_i) = -\sigma_i(\mathbf{u}_i -
   \mathbf{v}_i)$; positive semidefiniteness forces $\mathbf{u}_i = \mathbf{v}_i$ wherever
   $\sigma_i > 0$, so $\llbracket\mathbf{A}\rrbracket_k = \sum_{i<k}\sigma_i\mathbf{v}_i
   \mathbf{v}_i^{\mathsf{H}}$. *L5b:* with $\mathbf{P} = \mathbf{Z}\mathbf{Z}^{\mathsf{H}}$
   idempotent and $\mathbf{T} = \mathbf{H}\mathbf{P}$ Hermitian (L5a), $\mathbf{P}\mathbf{H} =
   \mathbf{T}^{\mathsf{H}} = \mathbf{T}$ and $\mathbf{P}\mathbf{H}\mathbf{P} = \mathbf{T}\mathbf{P} =
   \mathbf{T}$; expand. The frame comes from L2 at $\mathbf{H}$. The Nyström docstring reads "With
   $\mathbf{H}\mathbf{Z}\mathbf{Z}^{\mathsf{H}} = \llbracket\mathbf{H}\rrbracket_k$ (as L2 provides),
   $\mathbf{H}_\perp = \mathbf{H} - \llbracket\mathbf{H}\rrbracket_k$", and S5's top-$k$ reading is
   `rw [hH.one_sub_mul_mul_one_sub_eq_sub_truncatedSVD hZ hZH]`. §3.4's consumer line "S5 at
   $\mathbf{F} = \mathbf{H}^{1/2}$" is replaced by "S5 at $\mathbf{H}$": the route through the
   square root needs the eigenvalues of `CFC.sqrt H` and a choice-dependent identity
   (`truncatedSVD (CFC.sqrt H) k ^ 2 = truncatedSVD H k`, false under ties). **Corrected on
   inspection:** the review proposes L5a for Hermitian $\mathbf{A}$. That is false for some SVD the
   definition may choose: $\mathbf{A} = \operatorname{diag}(1, -1)$ has $\mathbf{\Sigma} =
   \mathbf{I}$, and $\mathbf{V} = [\mathbf{v}_1\ \mathbf{v}_2]$ with $\mathbf{v}_1 = (1,1)/\sqrt2$,
   $\mathbf{U} = \mathbf{A}\mathbf{V}$ is an SVD whose rank-1 truncation $\mathbf{A}\mathbf{v}_1
   \mathbf{v}_1^{\mathsf{H}} = \tfrac12\begin{bmatrix}1&1\\-1&-1\end{bmatrix}$ is not Hermitian;
   since `truncatedSVD` is built from a chosen SVD, the Hermitian claim is not provable. In the PSD
   case $\mathbf{u}_i = \mathbf{v}_i$ for every SVD, ties included, so L5 is stated for PSD only.
   Placement: see item 16.
3. **A2, the S0 file names and the rank dependency** (amends §4 file 3, its last paragraph, and the
   "Missing infrastructure" line). S0's skeleton put `nystrom`, `nystrom_def`, the Gram
   correspondence and `Matrix.PosSemidef.sub_nystrom_eq` in the side file
   `Matrix/Factorizations/NystromGram.lean` (it merges into `Nystrom.lean` at S0's wrap-up), and
   `SymmetricGauge.matrixNorm_sub_nystrom_le` in `NystromOrder.lean`. File 3 imports
   `Matrix/Factorizations/NystromGram` (switched to `Nystrom` at the merge) and
   `Matrix/Factorizations/SketchedLowRank` (which imports `Subspaces/ObliqueProjector`;
   `mulVec_injective_iff_rank_eq` is in `Basic/Gram.lean`, imported through it); `NystromOrder` is
   not imported. `IsSubspaceInjection.rank_mul_eq` is now in the tree, proved
   (`Sketching/Properties/SubspaceEmbedding.lean`, after `IsSubspaceInjection.injective_mulVec`), as
   are `rsvd`, `sub_rsvd`, `singularValues_mul_conjTranspose_self` (`SingularValues.lean`) and
   `SymmetricGauge.matrixNorm_mul_conjTranspose_self` (`UnitarilyInvariant.lean`): nothing from S0 is
   missing. The OSI route keeps `h.rank_mul_eq ha`; should it move, the fallback is
   `h.injective_mulVec ha hZ.mulVec_injective`, then `mulVec_injective_iff_rank_eq` and
   `hZ.rank_eq`, all existing API. `IsSubspaceInjection.frobNorm_mul_pinv_sq_le` is in
   `Sketching/Properties/LeastSquares.lean`, which file 3 already imports.
4. **A3, dominance stated, rule named** (§3.2 docstrings). Triangle form: replace "Incomparable with
   the Gram form ..." by "For every quadratic norm the Gram form is at least as strong
   ($\sqrt{a^2+b^2} \le a + b$); this form's own content is the norms the Gram form does not reach,
   such as the nuclear, Ky Fan and Schatten $p < 2$ norms". `specNorm_sub_rsvd_le`: "dominated by
   `HasOrthonormalCols.specNorm_sub_rsvd_sq_le`, kept because HMT 10.6 (S3) uses this simpler form",
   which is CONTRIBUTING §5.2 rule 6; it is proved from the squared form or the triangle form. The MT
   Theorem 11.4 attribution stands.
5. **A4, both rank bridges in the §5.3 row** (§1, the "range-finder error terms" row; §2; Q1). The
   bridge column reads: `IsSubspaceInjection.rank_mul_eq`; or `IsSubspaceInjection.injective_mulVec`
   with `hZ.mulVec_injective`, then `mulVec_injective_iff_rank_eq` and `hZ.rank_eq` (full column
   rank of `Ωᴴ * Z`, `Function.Injective (Ωᴴ * Z).mulVec`, which the proofs use internally). Q1's
   option (b) is that full-column-rank form, not `Function.Injective (Zᴴ * Ω)ᴴ.mulVec`.
6. **A5, CEMT locator** (Q10). The rank-$r$ upgrade remark ("by a standard truncation technique
   [58, Thm. 9.3]") follows Theorem 2.2 on printed p. 16, not Theorem 1.3 (p. 4); brief §9.3's
   locator is corrected to that. Q10's substance stands.
7. **A6, the AMM identity's instantiation** (§3.3 docstring of `HasOrthonormalCols.sub_mul_mul_pinv_eq`,
   §0 consumer row). The docstring adds: the first factor is
   `HasJLMoment.integral_frobNorm_conjTranspose_mul_sub_rpow_le` (`MatrixMultiplication.lean`) at
   $\mathbf{A} := \mathbf{E}^{\mathsf{H}}$, $\mathbf{S} := \mathbf{\Omega}^{\mathsf{H}}$,
   $\mathbf{B} := \mathbf{Z}$, after two `conjTranspose_conjTranspose`; that moment is over
   $\mathbb{R}$, so S7's route through it is real while S1 is over `𝕜`; and the term
   $-\mathbf{E}\mathbf{Z}$, zero under the frame, is kept only to match that shape.
8. **A7, shorter routes** (§3.4 L4, §3.3 AMM bound). L4: `pinv_mul_conjTranspose_self` gives
   $\mathbf{A}^{\mathsf{H}}((\mathbf{A}^{+})^{\mathsf{H}}\mathbf{A}^{+}) =
   (\mathbf{A}^{+}\mathbf{A})^{\mathsf{H}}\mathbf{A}^{+} = \mathbf{A}^{+}\mathbf{A}\mathbf{A}^{+} =
   \mathbf{A}^{+}$ (`(isPinv_pinv A).isHermitian_right`, `pinv_mul_mul_pinv`); no conjugation of
   `pinv_eq_pinv_conjTranspose_mul_self_mul`. AMM bound: $\lVert(\mathbf{X}^{\mathsf{H}}
   \mathbf{X})^{+}\rVert_2 = \lVert\mathbf{X}^{+}\rVert_2^2$ is `specNorm_pinv_sq`
   (`NormBounds.lean`) directly.
9. **A8, names spell both products before `pinv`** (§3.1, §1's row, §5's ledger). The three
   competitor lemmas become `HasOrthonormalCols.sub_mul_mul_pinv_mul_conjTranspose_eq`,
   `HasOrthonormalCols.sub_mul_mul_pinv_mul_conjTranspose_mul_conjTranspose_eq` and
   `HasOrthonormalCols.frobNorm_sub_mul_mul_pinv_mul_conjTranspose_sq`, matching
   `sub_mul_mul_pinv_eq` and item 1's names. The Nyström suffix `_of_hasOrthonormalCols` stays.
10. **A9, result ids, checked against `explore/build.py`.** An id may carry several declarations:
    the build groups them into one node, titles it from the bold names they share (the part before
    the comma) and lists first the declaration whose bold name matches the title. So
    `range-finder-structural-bound` stays on the six declarations of §5, and their bold names share
    the head: "**The structural bound of the range finder, Gram form**" (first in the file, so
    primary), "**..., unsquared triangle form**", "**..., under a subspace injection**" (replacing
    "The structural bound under a subspace injection"); the spectral and Frobenius forms keep no bold
    name.
11. **A10, `DecidableEq`** (§3 preamble). `[DecidableEq r]` is carried by every statement with a
    frame, because `HasOrthonormalCols Z` is `Zᴴ * Z = 1`; `pinv` needs none. `[DecidableEq m]` is in
    no statement (`sub_rsvd`'s `1` is proof-internal). `[DecidableEq n]` only where
    `1 : Matrix n n 𝕜` is displayed (the Nyström bound, L5b). `[DecidableEq q]` with `Q`.
12. **A11, two precisions.** §0: with $\mathbf{Z} = \mathbf{V}_1$, $\mathbf{M} = \mathbf{U}_2
    (\mathbf{\Sigma}_2\mathbf{\Omega}_2\mathbf{\Omega}_1^{+})$, so "up to an isometry" reads
    "$\mathbf{U}_2$ times HMT's $\mathbf{\Sigma}_2\mathbf{\Omega}_2\mathbf{\Omega}_1^{+}$"; the Gram
    matrices $\mathbf{M}^{\mathsf{H}}\mathbf{M}$ agree. §3.2 usage: the completion
    $\mathbf{V}_2$ of the `Fin k` frame (`HasOrthonormalCols.exists_fromCols`) is indexed by the
    top-$k$ directions and their complement, the case where CONTRIBUTING §5.1 allows `Fin` ("its
    order ... carries content"), so no defect; the snippet needs `hk : k ≤ Fintype.card n` for L2.
13. **Q1 and Q4 decided as (a).** Q1: `(Ωᴴ * Z).rank = Z.rank`, for uniformity with S0 §8 item 2
    across the round; orchestrator-level, "moderately hard" overstated. Q4: no definitions for
    $\mathbf{E}$, $\mathbf{M}$, $\mathbf{C}$, with the §5.3 row governing the spelling; a `def` with a
    `_def` simp lemma is additive later if S6 or S7 state API about $\mathbf{M}$ itself (the trigger
    of S0 §8 item 2).
14. **Q2 decided as (a), and by the maintainer for the round** (2026-10-15, `docs/PORT_LOWRANK.md`,
    "Maintainer decisions"): every error is spelled $\mathbf{A}$ minus the algorithm's named output
    (`A - rsvd A Ω`, `A - nystrom A Ω`, `A - generalizedNystrom A Ω Ψ`, and likewise for the
    truncated outputs), for every algorithm; projector and basis forms (`sub_rsvd` and its siblings)
    are bridge lemmas, never the statement shape. Q2's "(hard)" and the checkpoint note are
    superseded. With item 2, S5's transfer to Nyström is `Matrix.PosSemidef.sub_nystrom_eq` then L5b.
15. **Docstrings are LaTeX** (CONTRIBUTING §6 item 5): every docstring of the skeleton, including
    items 1 and 2, writes its mathematics as `$…$` and `$$…$$` with the notation table; Lean names
    stay in backticks.
16. **Placement in proved files.** `LowRank.lean` and `Pinv.lean` are registered and proved; a
    statement goes into them only once proved. A statement still `sorry` at the skeleton goes into a
    side file beside its home (`Matrix/Spectral/LowRankFrames.lean`,
    `Matrix/Pseudoinverse/PinvGram.lean`), which says it merges into its home at the wrap-up, and
    file 3 imports the side file meanwhile. L1 and L5a need `LowRank.lean`'s private SVD API, so in
    a side file they stay `sorry` until the merge (or the private lemmas they use are made public).
17. **Files and statements for the skeleton** (amends §4):

    | # | File | Statements | Lines (est.) | Imports (new) |
    |---|---|---|---|---|
    | 1 | `Matrix/Spectral/LowRank.lean` (or its side file, item 16) | 5 (L1 to L3, L5a, L5b) | +140 | none |
    | 2 | `Matrix/Pseudoinverse/Pinv.lean` (or its side file) | 1 (L4) | +10 | none |
    | 3 | `LowRank/Structural/RangeFinder.lean` (new) | 15 (5 + 6 + 4) | 440 | `Matrix/Factorizations/SketchedLowRank`, `Matrix/Factorizations/NystromGram`, `Matrix/Spectral/ProjectedLowRank`, `Matrix/Pseudoinverse/NormBounds`, `Sketching/Properties/LeastSquares` |

    S1 is about 590 lines and 21 public declarations. Order within file 3: §3.1 with item 1's two
    lemmas, §3.2, §3.3. Files 1 and 2 remain independent of S0 and of each other.
