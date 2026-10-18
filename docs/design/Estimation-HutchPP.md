# Trace estimation: Hutch++

Design note, draft of 2026-10-18 (revised the same day after review), for the probability round's
trace-estimation work on branch `probability/trace-estimation` (worktree `nlalib-block`, head
`2fdbff8` plus the concurrent agent's uncommitted edits). Not approved. Companion to
`docs/design/Probability-TraceEstimation.md` (Girard–Hutchinson variances, Haar frame variance,
the m-sample estimator), which another agent is writing; every name this note borrows from that
work is marked **(concurrent)** and is a placeholder until that note fixes it.

Maintainer requests (2026-10-18): "we should include hutch++ (gaussian exact computation and
subgaussian) and xtrace"; then "let's just skip xtrace for now". XTrace is therefore out of scope;
§8 keeps what a later round needs to start from.

**Decisions needing the maintainer: TE5 (sub-Gaussian route and constants) and TE10 (form of the
Gaussian headline).** All other decisions in §7 proceed as recommended (probability-round rule).

Sources read for the relevant parts:

* [MeyerMuscoMuscoWoodruff2021] R. A. Meyer, C. Musco, C. Musco, D. P. Woodruff, *Hutch++: Optimal
  stochastic trace estimation*, SOSA 2021; arXiv:2010.09649v5. Cited below as MMMW.
* [EpperlyTroppWebber2024] E. N. Epperly, J. A. Tropp, R. J. Webber, *XTrace: making the most of
  every sample in stochastic trace estimation*, SIMAX 45 (2024); arXiv:2301.07825v2. Cited as ETW.
* E. N. Epperly, *Stochastic trace estimation*, blog post, 26 January 2023. Cited as the blog.

None of the three is in `docs/references.bib`; neither are [AvronToledo2011],
[GilbertStraussTroppVershynin2007] (GSTV07, Lemma 7), [Hutchinson1989], [Girard1989] or
[HsuKakadeZhang2012]. They are added in the first commit that cites them.

## 0. What "Gaussian exact computation" and "sub-Gaussian" mean here

**Gaussian exact computation.** The only exact computation for Hutch++ in the three sources is
the variance identity in the proof of MMMW Theorem 10 (§5, "Variance Analysis", with Algorithm 3
"Gaussian-Hutch++"), which ETW reuse for their Proposition 5.2 (§5.2, proof deferred to MMMW
Theorem 10). Conditioning on the sketch and using the law of total variance, the term
$\operatorname{Var}(\mathbb{E}[\,\cdot \mid \mathbf{Q}])$ vanishes because the estimator is
conditionally unbiased, and Avron–Toledo's Lemma 1 (MMMW Imported Lemma 11) gives the conditional
variance exactly:
$$\operatorname{Var}[\mathsf{hutchpp}] = \frac{2}{\ell}\,
\mathbb{E}\,\|(\mathbf{I} - \mathbf{Q}\mathbf{Q}^{\mathsf{T}})\mathbf{A}
(\mathbf{I} - \mathbf{Q}\mathbf{Q}^{\mathsf{T}})\|_{\mathsf{F}}^2$$
for real symmetric $\mathbf{A}$ and an $n \times \ell$ standard Gaussian residual test matrix
$\mathbf{G}$ independent of $\mathbf{S}$. Everything after this line in MMMW and ETW is a bound:
submultiplicativity, then HMT Theorem 10.5 (MMMW Imported Theorem 12; ETW Lemma 5.4), then GSTV07
Lemma 7 (MMMW Imported Lemma 13; ETW Fact 5.5). Neither paper, nor the blog (whose variance
formulas are for Girard–Hutchinson alone), computes
$\mathbb{E}\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}\mathbf{S}})\mathbf{A}
(\mathbf{I} - \mathbf{P}_{\mathbf{A}\mathbf{S}})\|_{\mathsf{F}}^2$ in closed form, and there is no
closed form in general (HMT's structural bound is itself an inequality, so the exact Gaussian
moment $\mathbb{E}\|\mathbf{\Omega}_1^{+}\|_{\mathsf{F}}^2$ does not yield an identity).

What is exactly computable, and what this note proposes to prove as equalities:

1. **The deterministic error identity.**
   $\mathsf{hutchpp}(\mathbf{A},\mathbf{S},\mathbf{G}) - \operatorname{tr}\mathbf{A} =
   \mathsf{gh}(\mathbf{\Delta},\mathbf{G}) - \operatorname{tr}\mathbf{\Delta}$ with
   $\mathbf{\Delta} = (\mathbf{I} - \mathbf{P}_{\mathbf{A}\mathbf{S}})\mathbf{A}
   (\mathbf{I} - \mathbf{P}_{\mathbf{A}\mathbf{S}})$, for every $\mathbf{S}, \mathbf{G}$ (MMMW proof
   of Theorem 1, the trace split; ETW (1.3)).
2. **The exact mean-square error for any sketch law**, by Fubini over the independence of
   $\mathbf{S}$ and $\mathbf{G}$: the mean-square error of Hutch++ is the average over
   $\mathbf{S}$ of the mean-square error of Girard–Hutchinson on $\mathbf{\Delta}(\mathbf{S})$. With
   the concurrent per-distribution formulas this is exact for Gaussian residual probes
   ($\frac{2}{\ell}\mathbb{E}\|\mathbf{\Delta}_{\mathrm{h}}\|_{\mathsf{F}}^2$, with
   $\mathbf{\Delta}_{\mathrm{h}} = (\mathbf{I} - \mathbf{P})\,\mathrm{herm}(\mathbf{A})\,
   (\mathbf{I} - \mathbf{P})$ the Hermitian part, so no symmetry of $\mathbf{A}$ is needed), and
   equally exact for Rademacher probes
   ($\frac{2}{\ell}\mathbb{E}[\|\mathbf{\Delta}_{\mathrm{h}}\|_{\mathsf{F}}^2 -
   \sum_i (\mathbf{\Delta}_{\mathrm{h}})_{ii}^2]$). The sketch $\mathbf{S}$ can have any law;
   Gaussianity of $\mathbf{S}$ enters only in the bounds. MMMW's Algorithm 3 samples $\mathbf{G}$
   with $\pm 1$ entries but applies the Gaussian Lemma 11; their bound survives because the
   Rademacher variance is at most the Gaussian one, and the Rademacher identity is the exact
   variance of their algorithm as printed. This remark goes into the docstrings.
3. **For symmetric $\mathbf{A}$, a Pythagorean refinement** of the first bound step:
   $\|\mathbf{\Delta}\|_{\mathsf{F}}^2 = \|\mathbf{A} - \mathsf{rsvd}(\mathbf{A},\mathbf{S})\|_{\mathsf{F}}^2
   - \|(\mathbf{I} - \mathbf{P})\mathbf{A}\mathbf{P}\|_{\mathsf{F}}^2$, exact.
4. **Exactness at low rank.** With a Gaussian sketch and
   $\operatorname{rank}\mathbf{A} \le \lvert s\rvert$, $\mathsf{hutchpp} = \operatorname{tr}\mathbf{A}$
   almost surely (from `NLAlib.ae_rsvd_eq_self_of_hasLaw_gaussianMatrix`): the variance is $0$, an
   exact computation the papers mention only informally.
5. **Spectral reduction.** For symmetric $\mathbf{A}$ and Gaussian $\mathbf{S}$ the law of
   $\|\mathbf{\Delta}\|_{\mathsf{F}}$ depends only on the eigenvalues of $\mathbf{A}$ (rotation
   invariance); noted, not proposed as a headline, since it does not produce a formula.

So "Gaussian exact computation" is read as: the exact variance identity (items 1 and 2) for
Gaussian residual probes, with its explicit-constant consequences (MMMW Theorem 10 and Lemma 14,
ETW Theorem 1.1 first line) as corollaries. This mirrors MMMW's own split: §5 Gaussian with
explicit constants, §3 sub-Gaussian with high probability.

**Sub-Gaussian.** MMMW Theorem 1 (stated §1.2, restated and proved §3): if Hutch++ uses
$m = O(\sqrt{\log(1/\delta)}/\varepsilon + \log(1/\delta))$ matrix-vector products, then for PSD
$\mathbf{A}$, with probability at least $1 - \delta$,
$(1 - \varepsilon)\operatorname{tr}\mathbf{A} \le \mathsf{hutchpp} \le
(1 + \varepsilon)\operatorname{tr}\mathbf{A}$; the entries of $\mathbf{S}$ and $\mathbf{G}$ may be
"any sub-Gaussian random variables with mean 0 and variance 1" (§1.2, after Algorithm 1). Theorem 5
is the non-PSD form $|\mathsf{hutchpp} - \operatorname{tr}\mathbf{A}| \le \varepsilon\|\mathbf{A}\|_*$.
**The paper gives no explicit constants for Theorems 1, 4, 5**: Lemma 2 (Hutchinson tail, from
Hanson–Wright, proved in Appendix A) has "fixed constants $c, C$", and the range-finder step cites
[MM20, Corollary 7 and Claim 1] for
$\|\mathbf{A} - \mathbf{A}\mathbf{Q}\mathbf{Q}^{\mathsf{T}}\|_{\mathsf{F}}^2 \le
2\|\mathbf{A} - \mathbf{A}_k\|_{\mathsf{F}}^2$ at $m/3 \ge O(k + \log(1/\delta))$, with no
constant; [MM20] is not among the sources. Explicit constants appear only in §5 (variance). Two
typos to avoid copying: Theorem 4 assumes $\|\mathbf{\Delta}\|_{\mathsf{F}} \le
2\|\mathbf{A} - \mathbf{A}_k\|_{\mathsf{F}}$ while the proof of Theorem 1 derives
$\|\mathbf{\Delta}\|_{\mathsf{F}}^2 \le 2\|\cdot\|_{\mathsf{F}}^2$ and then writes
"$\|\mathbf{\Delta}\|_{\mathsf{F}} \le 2\|\mathbf{A} - \mathbf{A}_k\|_{\mathsf{F}}^2$".

## 1. Definitions

All definitions are over `[RCLike 𝕜]`, basis-free, total, in `namespace NLAlib`.

### 1.1 The residual Girard–Hutchinson estimator (concurrent)

Hutch++ applies the $\ell$-sample Girard–Hutchinson estimator to a compressed residual. This note
assumes the concurrent stage defines it; placeholder:

```lean
/-- (concurrent) The `ℓ`-sample Girard–Hutchinson estimator with the columns of `G` as probes:
(1/ℓ) ∑ⱼ gⱼᴴ B gⱼ = (1/ℓ) tr(Gᴴ B G). -/
noncomputable def girardHutchinson (B : Matrix n n 𝕜) (G : Matrix n t 𝕜) : 𝕜 :=
  (Gᴴ * B * G).trace / Fintype.card t
```

Junk value: `0` for empty `t`. Whatever name and argument order the concurrent note fixes is used
verbatim below (TE3).

### 1.2 Hutch++

```lean
/-- **Hutch++** [MeyerMuscoMuscoWoodruff2021, Algorithm 1]; [EpperlyTroppWebber2024, (1.3)]:
$$\mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G}) :=
\operatorname{tr}\mathsf{rsvd}(\mathbf{A}, \mathbf{S}) +
\mathsf{gh}\bigl((\mathbf{I} - \mathbf{P}_{\mathbf{A}\mathbf{S}})\mathbf{A}
(\mathbf{I} - \mathbf{P}_{\mathbf{A}\mathbf{S}}), \mathbf{G}\bigr),$$
the exact trace of the randomized SVD of `A` with sketch `S` plus the Girard–Hutchinson estimate,
with the columns of `G`, of the trace of the compressed residual. Uses `|s|` products to form
`A * S`, at most `|s|` for `A * Q` and `|t|` for the residual. Junk: for empty `t` the residual
term is `0` and the output is `tr (rsvd A S)`. -/
noncomputable def hutchpp [DecidableEq n] (A : Matrix n n 𝕜) (S : Matrix n s 𝕜)
    (G : Matrix n t 𝕜) : 𝕜 :=
  (rsvd A S).trace +
    girardHutchinson ((1 - rangeProjector (A * S)) * A * (1 - rangeProjector (A * S))) G
```

Relation to the existing API:

* `(rsvd A S).trace = (Qᴴ * A * Q).trace` for any `Q` with `HasOrthonormalCols Q` and
  `Q * Qᴴ = rangeProjector (A * S)` (from `NLAlib.HasOrthonormalCols.rangeProjector_eq`,
  `NLAlib/Matrix/Basic/Projector.lean:438`); the bridge `HasOrthonormalCols.hutchpp_eq` restates the
  definition in the papers' basis form, so no basis enters any statement. Over ℝ the concurrent
  lemma `NLAlib.trace_conjTranspose_mul_hermitianPart_mul`
  (`NLAlib/Matrix/Spectral/HermitianPart.lean:92`, uncommitted) gives
  $\operatorname{tr}(\mathbf{Q}^{\mathsf{T}}\,\mathrm{herm}(\mathbf{A})\,\mathbf{Q}) =
  \operatorname{tr}(\mathbf{Q}^{\mathsf{T}}\mathbf{A}\mathbf{Q})$, so the bridge and the reduction
  of Hutch++ to the Hermitian part are one rewrite each.
* `A - rsvd A S = (1 - rangeProjector (A * S)) * A` is `NLAlib.sub_rsvd`
  (`NLAlib/Matrix/Factorizations/SketchedLowRank.lean:106`), so the residual is
  `(A - rsvd A S) * (1 - rangeProjector (A * S))` and every bound on it goes through the
  randomized-SVD error.
* Measurability in `(S, G)` from `NLAlib.measurable_rsvd` and `NLAlib.measurable_rangeProjector`
  (`NLAlib/Probability/Measurability/Matrix.lean:183`, `:162`).
* Two arguments `S`, `G` with an `IndepFun S G μ` hypothesis, not one test matrix split in blocks
  (TE2); MMMW's Algorithm 3 already uses different widths $(m+2)/4$ and $(m-2)/2$.

## 2. Inventory

Status: **E** existing NLAlib (file:line at `2fdbff8`, or on the worktree where noted), **M**
Mathlib, **C** concurrent stage, **N** new. Difficulty: easy (under a day, under 60 lines), medium,
hard.

### 2.1 Matrix layer (layer 0)

| # | Statement sketch | Status, name | Source | Home | Diff. |
|---|---|---|---|---|---|
| A1 | `IsStarProjection P → (P * A).trace + ((1 - P) * A * (1 - P)).trace = A.trace` | N, `IsStarProjection.trace_mul_add_trace_one_sub_mul_mul_one_sub` | MMMW §3 proof of Thm 1; ETW §1.1.2 | `Matrix/Basic/ComplementaryProjector.lean` (projector algebra) | easy |
| A2 | `hermitianPart ((1-P) * A * (1-P)) = (1-P) * hermitianPart A * (1-P)` for Hermitian `P` | E, `hermitianPart_mul_mul_conjTranspose` | blog, "Real-valued test vectors" | `Matrix/Spectral/HermitianPart.lean:106` (worktree; was `:81` at `2fdbff8`) | done |
| A3 | real part of `quadForm A x` equals that of `hermitianPart A`; over ℝ the quadratic form itself; trace of a real compression sees only the Hermitian part | E, `re_quadForm_hermitianPart`; C, `quadForm_hermitianPart`, `trace_conjTranspose_mul_hermitianPart_mul` | blog | `HermitianPart.lean:72`, `:84`, `:92` (worktree) | done |
| A4 | `frobNorm (B * P) ≤ frobNorm B` for a star projection | E, `IsStarProjection.frobNorm_mul_right_le` | MMMW "submultiplicativity" | `Matrix/Norms/Projector.lean:97` | done |
| A5 | Pythagoras `frobNorm ((1-P) * A) ^ 2 = frobNorm ((1-P)*A*P) ^ 2 + frobNorm ((1-P)*A*(1-P)) ^ 2` | E (via `IsStarProjection.frobNorm_sq_eq_add`, `Projector.lean:116`), restated N as `frobNorm_one_sub_rangeProjector_mul_mul_sq` | derived | `Matrix/Norms/Projector.lean` | easy |
| A6 | `0 < r → frobNorm (A - truncatedSVD A r) ≤ nuclearNorm A / (2 * √r)` | N, `frobNorm_sub_truncatedSVD_le_nuclearNorm_div` | GSTV07 Lemma 7; MMMW Imported Lemma 13; ETW Fact 5.5 | `Matrix/Spectral/LowRank.lean` (planned there by `docs/PORT_KRYLOV.md` D12 as the weaker MMMW Lemma 3, `tr A / √k`, PSD; A6 dominates it, and the PSD form is a one-line corollary through `Matrix.PosSemidef.nuclearNorm_eq_re_trace`, `Matrix/Norms/Nuclear.lean:296`) | medium |

### 2.2 Probability layer (layer 1)

| # | Statement sketch | Status, name | Source | Home | Diff. |
|---|---|---|---|---|---|
| P1 | Fubini for an independent pair: `IndepFun X Y μ`, integrable on the product of laws, `∀ x, ∫ g x (Y ω) = c x` ⟹ `∫ g (X ω) (Y ω) = ∫ c (X ω)`; and the `μ.real` form for a measurable set | N, `IndepFun.integral_comp_eq_integral_integral`, `IndepFun.measureReal_eq_integral` (Mathlib: `indepFun_iff_map_prod_eq_prod_map_map`, `Probability/Independence/Basic.lean:703`, then `integral_prod`; searched `Independence/Integration.lean`, no such lemma) | MMMW proof of Thm 10; prototype `integral_comp_of_indepFun_of_forall_integral_eq` | `ForMathlib/Probability/Independence/Integration.lean` (upstream candidate) | medium |
| P2 | Isotropy interface `IsIsotropic x μ`; Hutchinson's identity `IsIsotropic.integral_quadForm` | E | Hutchinson; ETW (1.1) | `Probability/Isotropic.lean:65`, `:98` | done |
| P3 | Mean-square error of a quadratic form, general moments | E, `integral_norm_quadForm_sub_trace_sq` | AT11 Lemma 1 | `Probability/QuadraticForm/Moments.lean:269` | done |
| P4 | Gaussian, Rademacher single-probe variances (real symmetric) | E, `variance_quadForm_of_hasLaw_gaussianVector`, `..._rademacherVector` | AT11; blog | `Moments.lean:350`, `:369` | done |
| P5 | m-sample estimator: mean `tr B`; mean-square error `(1/ℓ)·(single-probe)` for iid columns; Gaussian `2/ℓ‖herm B‖²_F`, Rademacher; complex and sphere forms | C | blog; AT11 | concurrent file | C |
| P6 | Hanson–Wright, real, independent sub-Gaussian coordinates, constant `hansonWrightConstant` | E, `measureReal_abs_quadForm_sub_integral_ge_le` | RV13; MMMW Imported Thm 15 | `Probability/QuadraticForm/HansonWright.lean:219` (constant `:76`) | done |
| P7 | m-sample Girard–Hutchinson tail: entries independent, `HasSubgaussianMGF c`, unit variance ⟹ `μ.real {t ≤ |gh B G - tr B|} ≤ 2 exp(-C_HW min(ℓt²/(c²‖B‖_F²), ℓt/(c‖B‖₂)))` | N (or C if the concurrent note includes it), `measureReal_abs_girardHutchinson_sub_trace_ge_le` | MMMW Lemma 2, App. A; prototype `measureReal_le_abs_hutchinsonEstimate_sub_integral_le` | file of `girardHutchinson` | medium (vectorization through Mathlib `Matrix.blockDiagonal`; Frobenius and spectral norm of a constant block diagonal: N, small, proof-local or `Matrix/Norms`) |
| P8 | Vectorization: independent columns, each `IsSubgaussianVector c` ⟹ the flattened `n × t` vector is `IsSubgaussianVector c` | N, `IsSubgaussianVector.uncurry_of_iIndepFun` | standard | `Probability/SubGaussianVector/Basic.lean` | easy |
| P9 | Hsu–Kakade–Zhang upper tail of `‖M x‖²` for a sub-Gaussian vector | E, `IsSubgaussianVector.measure_norm_mulVec_sq_ge_le` | HKZ12 Thm 2.1 | `Probability/SubGaussianVector/Norm.lean:448` | done |
| P10 | Law of total variance | M, `integral_condVar_add_variance_condExp` (`Probability/CondVar.lean:135`); not used, P1 is simpler here because the conditional mean is constant | MMMW (2) | | |

### 2.3 Random matrices and low-rank layers (2, 4)

| # | Statement sketch | Status, name | Home | Diff. |
|---|---|---|---|---|
| L1 | Gaussian law `gaussianMatrix n l` (real), column independence | E | `RandomMatrix/Gaussian/Basic.lean:51`, `:98` | done |
| L2 | `ae_rsvd_eq_self_of_hasLaw_gaussianMatrix` (exact recovery at `rank A ≤ |l|`) | E | `LowRank/Gaussian/RangeFinder.lean:104` | done |
| L3 | HMT 10.5, squared: `∫ ‖A - rsvd A X‖_F² ≤ gaussianProjectionFactor r ℓ · ‖A - [A]_r‖_F²`, `r + 2 ≤ ℓ` | E, `integral_frobNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix` (`gaussianProjectionFactor` $= 1 + r/(\ell - r - 1)$, `RandomMatrix/Gaussian/BlockMoments.lean:76`) | `RangeFinder.lean:208` | done |
| L4 | EW sharp factor with rank parameter | E, `integral_frobNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix_of_rank_le` | `LowRank/Gaussian/RotationInvariant.lean:846` | done |
| L5 | Gaussian range-finder tails (TW RSVD1; HMT 10.7) | E, `measureReal_not_frobNorm_sub_rsvd_sq_le_le_of_hasLaw_gaussianMatrix`, `measureReal_not_frobNorm_sub_rsvd_le_le_of_hasLaw_gaussianMatrix` | `LowRank/Gaussian/RangeFinderTail.lean:250`, `:396` | done |
| L6 | Sub-Gaussian range finder, relative error, failure $\delta$ at $\ell \gtrsim c^2(k/(\varepsilon\delta) + \log(1/\delta))$ | E, `measureReal_frobNorm_sub_rsvd_sq_gt_le_of_isSubgaussianVector` | `LowRank/Oblivious/SubGaussian.lean:121` | done, but **polynomial in $1/\delta$** (`hl' : 8(16c²−1)k ≤ εδℓ`): unusable for MMMW's count |
| L7 | **Sub-Gaussian range finder, constant factor, failure $\delta$ at $\ell \gtrsim c^2(k + \log(1/\delta))$**: `μ.real {ω | subgaussianRangeFinderFactor c * ‖A - [A]_k‖_F² < ‖A - rsvd A (X ω)‖_F²} ≤ δ` when `subgaussianEmbeddingDim c k (1/2) (δ/2) ≤ |l|`; factor proved $1 + 10c$ | N, `measureReal_frobNorm_sub_rsvd_sq_gt_le_mul_of_isSubgaussianVector` | `LowRank/Oblivious/SubGaussian.lean` | medium |
| L8 | Structural bound under a subspace injection: `‖A - rsvd A Ω‖_F² ≤ ‖E‖_F² + ‖E Ω‖_F²/a` | E, `IsSubspaceInjection.frobNorm_sub_rsvd_sq_le` | `LowRank/Structural/RangeFinder.lean:359` | done |
| L9 | Sub-Gaussian OSI at log failure | E, `isObliviousSubspaceInjection_of_isSubgaussianVector_of_subgaussianEmbeddingDim_le` | `Sketching/Gaussian/SubGaussian.lean:693` (`subgaussianEmbeddingDim`, `:139`) | done |
| L10 | Haar frame law, sphere law, frame moments | E (`haarFrame`, `uniformSphereVector`) and C (frame variance of `tr(QᵀAQ)`) | `RandomMatrix/Haar/Basic.lean:63`, `:168`; `Haar/Moments.lean` | C, not needed by §3 |

Proof of L7: the OSI (L9) at $\varepsilon = 1/2$ and failure $\delta/2$ for the top-$k$ right
singular frame $\mathbf{Z}$, for the sketch scaled by $\ell^{-1/2}$, that is
`IsSubspaceInjection Ωᴴ Z (ℓ/2)`; the structural bound L8 with
$\mathbf{E} = \mathbf{A} - \llbracket\mathbf{A}\rrbracket_k$, giving
$\|\mathbf{E}\|_{\mathsf{F}}^2 + 2\|\mathbf{E}\mathbf{\Omega}\|_{\mathsf{F}}^2/\ell$; and the
Hsu–Kakade–Zhang tail P9 for $\|\mathbf{E}\mathbf{\Omega}\|_{\mathsf{F}}^2 =
\|(\mathbf{I}_\ell \otimes \mathbf{E})\operatorname{vec}\mathbf{\Omega}\|^2$ (vectorization P8),
which with $t = \log(2/\delta) \le \ell$ gives
$\|\mathbf{E}\mathbf{\Omega}\|_{\mathsf{F}}^2 \le c\|\mathbf{E}\|_{\mathsf{F}}^2(\ell + 2\sqrt{\ell t} + 2t)
\le 5c\,\ell\,\|\mathbf{E}\|_{\mathsf{F}}^2$ except with probability $\delta/2$. Hence
$\|\mathbf{A} - \mathsf{rsvd}\|_{\mathsf{F}}^2 \le (1 + 10c)\|\mathbf{E}\|_{\mathsf{F}}^2$ with
probability $1 - \delta$ at $\ell = O(c^2(k + \log(1/\delta)))$. Side conditions: the cases
$\mathbf{E} = \mathbf{0}$ and $c = 0$ are split off (HKZ needs $\mathbf{A} \ne \mathbf{0}$,
$c \ne 0$); $\log(2/\delta) \le \ell$ is implied by the embedding-dimension hypothesis because
$c \ge 1$ (`IsSubgaussianVector.one_le_of_isIsotropic`), and the docstring says so. This replaces
MMMW's citation of [MM20] by a different route of the same shape. Gaussian and Rademacher
sketches are its instances $c = 1$.

### 2.4 Estimation layer (layer 4, new): the headlines, §3

| # | Name | Home | Diff. |
|---|---|---|---|
| H1 | `hutchpp`, `HasOrthonormalCols.hutchpp_eq`, `hutchpp_sub_trace`, `hutchpp_eq_trace_of_rank_eq`, `measurable_hutchpp` | `Estimation/Trace/HutchPlusPlus.lean` | easy |
| H2 | `integral_hutchpp` (unbiased) | same | easy given P1 |
| H3 | `integral_norm_hutchpp_sub_trace_sq` (exact, any probe law) and Gaussian, Rademacher instances; `ae_hutchpp_eq_trace_of_hasLaw_gaussianMatrix` | same | medium |
| H4 | Gaussian variance bounds, nuclear form, asymptotic | same | easy-medium |
| H5 | High-probability theorem over a range-finder hypothesis; Gaussian and sub-Gaussian instances; PSD $(1\pm\varepsilon)$ form; asymptotic | `Estimation/Trace/HutchPlusPlusTail.lean` (TE9) | medium-hard |

## 3. Headline statements

Conventions: `{Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]`, index
types `{n s t : Type*} [Fintype _] [DecidableEq n]`, random test matrices
`{S : Ω → Matrix n s _} {G : Ω → Matrix n t _}`. Probabilistic statements are over ℝ where they
need `gaussianMatrix` or Hanson–Wright (TE6); unbiasedness is over `𝕜`.

### 3.1 Deterministic core and unbiasedness

```lean
/-- The error of Hutch++ is the error of Girard–Hutchinson on the compressed residual:
hutchpp A S G − tr A = gh(Δ, G) − tr Δ, Δ = (I − P_{AS}) A (I − P_{AS}). -/
theorem hutchpp_sub_trace (A : Matrix n n 𝕜) (S : Matrix n s 𝕜) (G : Matrix n t 𝕜) :
    hutchpp A S G - A.trace =
      girardHutchinson ((1 - rangeProjector (A * S)) * A * (1 - rangeProjector (A * S))) G -
        ((1 - rangeProjector (A * S)) * A * (1 - rangeProjector (A * S))).trace

/-- **Hutch++ is unbiased** for any sketch law and any residual probes independent of the sketch
with isotropic columns. [MMMW, proof of Theorem 10]; [ETW, Proposition 5.2]; there with Gaussian
test matrices. Result: hutchpp-unbiased -/
theorem integral_hutchpp [Nonempty t] (A : Matrix n n 𝕜) {S : Ω → Matrix n s 𝕜}
    {G : Ω → Matrix n t 𝕜} (hS : AEMeasurable S μ) (hSG : IndepFun S G μ)
    (hG : ∀ j, IsIsotropic (fun ω i => G ω i j) μ) :
    ∫ ω, hutchpp A (S ω) (G ω) ∂μ = A.trace
```

`hutchpp_sub_trace` needs only A1 and idempotence of `1 - P`. The column hypothesis on `G` is
whatever the concurrent m-sample estimator's unbiasedness takes; isotropy of each column is the
minimum. To check during TE-2: the Fubini step P1 needs `G` a.e.-measurable; `IsIsotropic.memLp`
gives a.e.-strong measurability of each coordinate, hence of `G`.

### 3.2 The exact Gaussian computation

```lean
/-- **The mean-square error of Hutch++, exactly**: for any sketch law and residual probes
independent of the sketch, it is the average over the sketch of the mean-square error of
Girard–Hutchinson on the compressed residual. [MMMW, (2) and proof of Theorem 10]. -/
theorem integral_norm_hutchpp_sub_trace_sq (A : Matrix n n 𝕜) {S : Ω → Matrix n s 𝕜}
    {G : Ω → Matrix n t 𝕜} (hS : AEMeasurable S μ) (hSG : IndepFun S G μ)
    (hG : <the concurrent L⁴ / isotropy hypotheses on the columns of G>) :
    ∫ ω, ‖hutchpp A (S ω) (G ω) - A.trace‖ ^ 2 ∂μ =
      ∫ ω, (∫ ω', ‖girardHutchinson (Δ (S ω)) (G ω') - (Δ (S ω)).trace‖ ^ 2 ∂μ) ∂μ
      -- Δ S := (1 - rangeProjector (A * S)) * A * (1 - rangeProjector (A * S)), written out

/-- **The exact variance of Hutch++ with a Gaussian residual test matrix**: for every real square
`A`, every sketch law independent of `G` and at least one residual probe,
$$\operatorname{Var}[\mathsf{hutchpp}(\mathbf{A},\mathbf{S},\mathbf{G})] = \frac{2}{\ell}\,
\mathbb{E}\,\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}\mathbf{S}})\,\mathrm{herm}(\mathbf{A})\,
(\mathbf{I} - \mathbf{P}_{\mathbf{A}\mathbf{S}})\|_{\mathsf{F}}^2.$$
[MMMW, Theorem 10 (proof), Imported Lemma 11]; there for PSD A and as the first line of a bound.
Result: hutchpp-variance -/
theorem variance_hutchpp_of_hasLaw_gaussianMatrix [Nonempty t] (A : Matrix n n ℝ)
    {S : Ω → Matrix n s ℝ} {G : Ω → Matrix n t ℝ} (hS : AEMeasurable S μ)
    (hG : HasLaw G (gaussianMatrix n t) μ) (hSG : IndepFun S G μ) :
    variance (fun ω => hutchpp A (S ω) (G ω)) μ =
      2 / Fintype.card t * ∫ ω, frobNorm ((1 - rangeProjector (A * S ω)) * hermitianPart A *
        (1 - rangeProjector (A * S ω))) ^ 2 ∂μ
```

`[Nonempty t]` is needed: for empty `t`, `hutchpp = tr (rsvd A S)`, whose variance is nonzero in
general, while the right side is `2/0 * … = 0`. The Fubini identity
`integral_norm_hutchpp_sub_trace_sq` holds without it (both sides reduce through A1).

Corollaries in the same file: the Rademacher identity (diagonal correction, P5; `[Nonempty t]`);
for `A.IsHermitian` the Pythagorean form through A5,
`2/ℓ * (∫ ‖A - rsvd A (S ω)‖_F² - ∫ ‖(1-P) * A * P‖_F²)`; `ae_hutchpp_eq_trace_of_hasLaw_gaussianMatrix`
(`A.rank ≤ card s` ⟹ `hutchpp A (S ω) (G ω) = A.trace` a.s., for any `G`).

### 3.3 Gaussian variance bounds

```lean
/-- Gaussian sketch and residual probes, HMT's factor, any `r` with `r + 2 ≤ |s|`:
Var ≤ (2/ℓ)(1 + r/(|s| − r − 1)) ‖A − ⟦A⟧_r‖_F². [ETW, Theorem 1.1 (Hutch++ line), Proposition 5.2];
[MMMW, Theorem 10 (proof)]. Result: hutchpp-variance -/
theorem variance_hutchpp_le_of_hasLaw_gaussianMatrix [Nonempty t] (A : Matrix n n ℝ)
    {S : Ω → Matrix n s ℝ} {G : Ω → Matrix n t ℝ} (hS : HasLaw S (gaussianMatrix n s) μ)
    (hG : HasLaw G (gaussianMatrix n t) μ) (hSG : IndepFun S G μ) {r : ℕ}
    (hr : r + 2 ≤ Fintype.card s) :
    variance (fun ω => hutchpp A (S ω) (G ω)) μ ≤
      2 / Fintype.card t * gaussianProjectionFactor r (Fintype.card s) *
        frobNorm (A - truncatedSVD A r) ^ 2
```

* `..._of_rank_le`: the same with `rotationInvariantFactor r' (card s) r` (L4), the sharper EW
  factor.
* **Nuclear form** `variance_hutchpp_le_nuclearNorm_of_hasLaw_gaussianMatrix` (MMMW Theorem 10 and
  Lemma 14, through A6): for `0 < r` and `2 * r + 1 ≤ card s`,
  `variance ≤ nuclearNorm A ^ 2 / (card t * r)`. Derivation:
  `gaussianProjectionFactor r q ≤ 2` iff `q - r - 1 ≥ r`, and A6 gives
  $\|\mathbf{E}_r\|_{\mathsf{F}}^2 \le \|\mathbf{A}\|_*^2/(4r)$, so the bound is
  $\frac{2}{\ell}\cdot 2 \cdot \frac{\|\mathbf{A}\|_*^2}{4r}$. Relation to MMMW, for the docstring:
  their $q = |s| = (m+2)/4 = 2k + 1$ with $k = (m-2)/8$ (their $k$ is our $r$; the extracted text
  "k = 8" is a garbled $k = (m-2)/8$), $\ell = |t| = (m-2)/2$, total $m = 2q + \ell$, so
  $\ell k = (m-2)^2/16$ and the bound is their $16\,\|\mathbf{A}\|_*^2/(m-2)^2$ (Lemma 14;
  Theorem 10 with $\operatorname{tr}^2\mathbf{A}$ for PSD $\mathbf{A}$). PSD corollary with
  `A.trace ^ 2`.
* **Asymptotic** (ETW (1.10)), `exists_forall_variance_hutchpp_le_of_hasLaw_gaussianMatrix`:
  ```lean
  ∃ C : ℝ, 0 < C ∧ ∀ {Ω n s t : Type} [MeasurableSpace Ω] [Fintype n] [Fintype s] [Fintype t]
      [DecidableEq n] (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Matrix n n ℝ)
      (S : Ω → Matrix n s ℝ) (G : Ω → Matrix n t ℝ) (η : ℝ),
      HasLaw S (gaussianMatrix n s) μ → HasLaw G (gaussianMatrix n t) μ → IndepFun S G μ →
      0 < η → η ≤ 1 → C / √η ≤ Fintype.card s → C / √η ≤ Fintype.card t →
      variance (fun ω => hutchpp A (S ω) (G ω)) μ ≤ η * nuclearNorm A ^ 2
  ```
  "$O(\eta^{-1/2})$ products suffice". The proof takes $C = 4$ and $r = \lfloor (q-1)/2 \rfloor$
  with $q = |s|$. Check: $q \ge 4/\sqrt\eta \ge 4$ (because $\eta \le 1$), so $r \ge 1$ and
  $2r + 1 \le q$; $r \ge (q-2)/2 \ge (4/\sqrt\eta - 2/\sqrt\eta)/2 = 1/\sqrt\eta$ (using
  $2 \le 2/\sqrt\eta$); $\ell \ge 4/\sqrt\eta \ge 1$, so `t` is nonempty; hence
  $\ell r \ge 4/\eta \ge 1/\eta$ and the nuclear form gives $\le \eta\|\mathbf{A}\|_*^2$. Any
  $C \ge 1 + \sqrt 3$ works with the same argument ($C(C-2)/2 \ge 1$); the cap $\eta \le 1$ is in
  the statement, and without it $r \ge 1$ can fail. Docstring ends with
  `Asymptotic: NLAlib.variance_hutchpp_le_nuclearNorm_of_hasLaw_gaussianMatrix`.

### 3.4 Sub-Gaussian high-probability bound

Primary form, generic in the sketch's law (CONTRIBUTING §5.4, "parametrise over the interface"):
the range-finder guarantee is a hypothesis.

```lean
/-- **Hutch++ deviation given a range-finder guarantee.** If the event
‖A − rsvd A S‖_F² ≤ K ‖A − ⟦A⟧_r‖_F² fails with probability at most δ₁ and the residual probes have
independent sub-Gaussian entries (proxy c, unit variance) independent of S, then for τ ≥ 0
P(|hutchpp − tr A| ≥ τ) ≤ δ₁ + 2 exp(−C_HW min(ℓτ²/(c² K ‖E_r‖_F²), ℓτ/(c √K ‖E_r‖_F))).
[MMMW, Theorem 4 and Lemma 2]. -/
theorem measureReal_abs_hutchpp_sub_trace_ge_le (A : Matrix n n ℝ) {S : Ω → Matrix n s ℝ}
    {G : Ω → Matrix n t ℝ} {c : ℝ≥0} (hS : AEMeasurable S μ) (hSG : IndepFun S G μ)
    (hGind : iIndepFun (fun p : n × t => fun ω => G ω p.1 p.2) μ)
    (hGsub : ∀ i j, HasSubgaussianMGF (fun ω => G ω i j) c μ)
    (hGvar : ∀ i j, ∫ ω, G ω i j ^ 2 ∂μ = 1) {r : ℕ} {K δ₁ : ℝ} (hK : 0 ≤ K)
    (hRF : μ.real {ω | K * frobNorm (A - truncatedSVD A r) ^ 2 <
      frobNorm (A - rsvd A (S ω)) ^ 2} ≤ δ₁) {τ : ℝ} (hτ : 0 ≤ τ) :
    μ.real {ω | τ ≤ |hutchpp A (S ω) (G ω) - A.trace|} ≤
      δ₁ + 2 * Real.exp (-(hansonWrightConstant *
        min (Fintype.card t * τ ^ 2 / (c ^ 2 * K * frobNorm (A - truncatedSVD A r) ^ 2))
          (Fintype.card t * τ / (c * √K * frobNorm (A - truncatedSVD A r)))))
```

The `G` hypotheses are the triple of `NLAlib.hasJLProperty_of_iIndepFun_entry`
(`Sketching/Gaussian/SubGaussian.lean:857`), reused rather than re-bundled. Zero-denominator junk:
`‖E_r‖_F = 0` makes the residual zero on the good event; the proof splits that case. Empty `t`
is harmless here: the exponent is `0` and the bound is at least `1`.

Instances, same file:

* `measureReal_abs_hutchpp_sub_trace_ge_le_of_isSubgaussianVector`: `S` with independent,
  isotropic, sub-Gaussian columns (the `LowRank/Oblivious/SubGaussian.lean` triple), `hRF` from L7
  with `K = subgaussianRangeFinderFactor c`, `δ₁ = δ/2`.
* `..._of_hasLaw_gaussianMatrix`: `hRF` from L5 (HMT 10.7 form) or from L7 at `c = 1`.
* Relative form (MMMW Theorem 5, nuclear norm): `μ.real {ω | ε * nuclearNorm A ≤ |hutchpp − tr A|} ≤ δ`
  under explicit size conditions on `card s` and `card t`, through A6. PSD form (MMMW Theorem 1
  literally) as two one-sided tails, `(1 - ε) * A.trace ≤ hutchpp` and `hutchpp ≤ (1 + ε) * A.trace`
  (CONTRIBUTING §5.2, "two-sided bounds are two theorems").
* **Asymptotic** (TE8): `exists_forall_measureReal_abs_hutchpp_sub_trace_ge_le_of_isSubgaussianVector`:
  `∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω n s t : Type} … (A) (S G) (c) (ε δ), hyps → 0 < ε → ε ≤ ε₀ →
  0 < δ → δ ≤ 1/2 → C * (c ^ 4 * (√(Real.log (1/δ)) / ε + Real.log (1/δ))) ≤ card s →
  C * (c ^ 4 * (√(Real.log (1/δ)) / ε + Real.log (1/δ))) ≤ card t →
  μ.real {ω | ε * nuclearNorm A < |hutchpp A (S ω) (G ω) - A.trace|} ≤ δ`.
  "$O(c^4(\sqrt{\log(1/\delta)}/\varepsilon + \log(1/\delta)))$ products suffice", total
  $m = 2|s| + |t|$. The proxy power is what the inversion reaches ($c^{7/2}$ by the count below,
  rounded up using $c \ge 1$ from isotropy); the proof fixes it. Exponent check: with
  $r \asymp |s|/c^2$ and $\|\mathbf{E}_r\|_{\mathsf{F}} \le \|\mathbf{A}\|_*/(2\sqrt r)$, the
  Hanson–Wright exponent is at least
  $C\min(|t| r\varepsilon^2/c^3, |t|\sqrt r\,\varepsilon/c^{3/2})$, which is
  $\ge \log(4/\delta)$ once $|s|, |t| \gtrsim c^4(\sqrt{\log(1/\delta)}/\varepsilon + \log(1/\delta))$,
  because $(\log/\varepsilon)^{2/3} \le \max(\sqrt{\log}/\varepsilon, \log)$.

## 4. Dependencies on the concurrent work and on Hanson–Wright

1. **m-sample Girard–Hutchinson (C, P5).** Hutch++ is defined through it (TE3); H2 needs its
   unbiasedness under column isotropy; H3's Gaussian and Rademacher identities are its mean-square
   formulas composed with P1. If the concurrent estimator takes probes as `t → n → 𝕜` rather than a
   matrix, `hutchpp`'s third argument follows that shape. **No Lean for TE-2 before the concurrent
   m-sample file is merged.**
2. **Hermitian-part lemmas (C, A3).** `quadForm_hermitianPart` and
   `trace_conjTranspose_mul_hermitianPart_mul` (uncommitted on the worktree) are used by H1's bridge
   and by the reduction of the Gaussian identity to `hermitianPart A`.
3. **Haar frame variance (C, L10).** Not needed for §3: MMMW and ETW analyse Gaussian probes. It is
   the dependency of a later normalized variant (ETW §2.3 applied to Hutch++'s residual probes):
   $\boldsymbol{\nu} = \sqrt{N - r}\,(\mathbf{I} - \mathbf{P})\boldsymbol{\omega}/
   \|(\mathbf{I} - \mathbf{P})\boldsymbol{\omega}\|$ is uniform on the sphere of radius
   $\sqrt{N - r}$ in $\operatorname{range}(\mathbf{I} - \mathbf{P})$ given $\mathbf{P}$, so its
   conditional variance is the concurrent sphere formula ($k = 1$ frame) in dimension $N - r$.
   Not proposed this round.
4. **Complex Haar frame (C, possible).** Would enable complex Hutch++ variance statements; until a
   complex Gaussian matrix law exists the probabilistic theorems stay over ℝ (TE6).
5. **Hanson–Wright (E, P6).** Used once, in P7, by vectorizing the residual probes:
   `quadForm (blockDiagonal (fun _ => B)) (vec G) = ℓ • girardHutchinson B G`, Frobenius norm
   $\sqrt\ell\,\|\mathbf{B}\|_{\mathsf{F}}$, spectral norm $\|\mathbf{B}\|_2$. Its hypotheses are real
   with independent coordinates; a test matrix with independent sub-Gaussian columns but dependent
   coordinates (the `IsSubgaussianVector` interface) does not fit, which is why the residual probes
   carry entry hypotheses while the sketch carries column hypotheses. Hsu–Kakade–Zhang (P9) is the
   column-interface tool for the sketch side (L7).

## 5. Stage plan

Sizes are Lean lines including docstrings.

| Stage | Content | Files | Size | Risk |
|---|---|---|---|---|
| TE-0 | A1, A5, A6 (with PSD corollary) | `ComplementaryProjector.lean`, `Norms/Projector.lean`, `Spectral/LowRank.lean` | 120 | low; A6's proof through singular-value sums is the longest |
| TE-1 | P1 (ForMathlib), P8; P7 if the concurrent note leaves it out | `ForMathlib/Probability/Independence/Integration.lean`, `Probability/SubGaussianVector/Basic.lean`, GH file | 250 | medium: integrability side conditions in P1; ship the `μ.real` set form with it |
| TE-2 | H1, H2, H3 | `Estimation/Trace/HutchPlusPlus.lean` | 350 | medium; waits for the concurrent m-sample file; size depends on how much Fubini bookkeeping P1 absorbs |
| TE-3 | H4 (Gaussian bounds, nuclear form, asymptotic) | same file | 200 | low |
| TE-4 | L7 (sub-Gaussian constant-factor range finder), named factor and registry entry | `LowRank/Oblivious/SubGaussian.lean` | 150 | medium |
| TE-5 | H5 (generic tail, two instances, relative and PSD forms, asymptotic inversion) | `Estimation/Trace/HutchPlusPlusTail.lean` | 500 to 600 | medium-high: constant inversion with powers of `c` |

Order: TE-0 then TE-2 then TE-3; TE-1 in parallel with TE-4; TE-5 after TE-1, TE-2 and TE-4.
Total about 1,600 lines.

**Risks.**

1. The sub-Gaussian theorem's route differs from MMMW's (L7 instead of [MM20]); constants and the
   proxy power are ours, and the explicit theorem's hypotheses will be long. Mitigation: the
   generic `hRF` form keeps the range finder out of the Hutch++ proof. This is TE5.
2. Concurrency: the names, argument shapes and column hypotheses of the m-sample estimator, and who
   owns P7, are set by the concurrent note. This note's signatures are rewritten when it lands.
3. Real-only Gaussian matrix law: the complex half of the variance story is not reachable this
   round.
4. P1's integrability conditions on the product of laws: needed for every Fubini step; if they
   prove awkward, state P1 for nonnegative integrands through `lintegral` first.

## 6. Placement summary (additions outside the new `Estimation/Trace/` files)

| Addition | Home | Reason |
|---|---|---|
| A1 trace split | `Matrix/Basic/ComplementaryProjector.lean` | complementary-projector algebra |
| A5 Pythagoras of the compressed residual | `Matrix/Norms/Projector.lean` | Frobenius norms of projections |
| A6 GSTV tail bound | `Matrix/Spectral/LowRank.lean` | best rank-r approximation (as planned in `PORT_KRYLOV.md` D12) |
| P1 Fubini for independence | `ForMathlib/Probability/Independence/Integration.lean` | general, no NLAlib vocabulary |
| P7 GH tail | file of `girardHutchinson` | the estimator's topic |
| P8 vectorization | `Probability/SubGaussianVector/Basic.lean` | sub-Gaussian vector API |
| L7 constant-factor range finder | `LowRank/Oblivious/SubGaussian.lean` | sub-Gaussian randomized SVD |

No flags: every addition is at its topic's home. No Mathlib deviation is introduced (no parallel
notion; `girardHutchinson` and `hutchpp` are new objects).

§5.3 rows to add: `hutchpp A S G` (Hutch++ output, `\mathsf{hutchpp}`), and the independence of two
random test matrices as `IndepFun S G μ`.

**Prototype material** (read through `~/Documents/prove2me/lean/atlas/declarations.json`, modules
`NLAlib.Estimation.Trace.Unbiased` and `NLAlib.Estimation.Trace.HutchinsonTail`): reused as
mathematics, the trace split (`trace_eq_trace_transpose_mul_mul_add`, now A1 for any star
projection), the independence Fubini step (`integral_comp_of_indepFun_of_forall_integral_eq`, now
P1) and the block-diagonal Hutchinson tail (`hutchinsonBlock`, `quadForm_hutchinsonBlock`). Not
reproduced: `hutchPlusPlusBasis` (a `Fin (finrank …)` basis; replaced by `rangeProjector`),
`deflatedTraceEstimate` with a supplied `Q` (replaced by the bridge `HasOrthonormalCols.hutchpp_eq`),
the raw `hsecond` second-moment hypotheses (replaced by `IsIsotropic`), the `1/m`-scaled public
`hutchinsonBlock` (the block matrix is proof-internal), and the prototype's Hanson–Wright constant
$1/(256e^2)$ (the library has $1/196$). The prototype had no variance or high-probability theorem
for Hutch++.

## 7. Decisions

Numbering after the XTrace drop: TE1 to TE5 keep their numbers; old TE6, TE10, TE11, TE12, TE13,
TE14 are now TE6 to TE11; old TE7 to TE9 (XTrace) are removed.

**For the maintainer**

**TE5. Route to the sub-Gaussian theorem, and its constants.** (a) A generic theorem over a
range-finder hypothesis (§3.4) plus the new log-failure sub-Gaussian range finder L7 (our route,
OSI + Hsu–Kakade–Zhang, in place of MMMW's uncited-here [MM20]; factor $1 + 10c$ in place of
MMMW's $2$; proxy power $c^4$ in the asymptotic threshold), reaching MMMW's
$O(\sqrt{\log(1/\delta)}/\varepsilon + \log(1/\delta))$; (b) the existing L6, which gives only
$O(\sqrt{\log(1/\delta)}/(\varepsilon\delta))$; (c) Gaussian sketch only, through L5.
Recommendation: (a), whose Gaussian instance is (c) for free.

**TE10. Form of the Gaussian headline** (old TE13). (a) The exact identity (§3.2) as the primary
theorem carrying `Result: hutchpp-variance`, with the bounds of §3.3 as corollaries; (b) only the
bound, as printed in MMMW Theorem 10. Recommendation: (a), which is the maintainer's "exact
computation".

**Proceeding as recommended**

* **TE1. Definition.** Basis-free `tr (rsvd A S) + gh ((1-P) A (1-P), G)`; the basis form as the
  bridge `HasOrthonormalCols.hutchpp_eq`.
* **TE2. Inputs.** Two test matrices `S`, `G` with `IndepFun S G μ`; covers MMMW Algorithm 3's
  unequal widths and deterministic `S`.
* **TE3. Residual estimator.** Reuse the concurrent `girardHutchinson`, name and shape as it fixes
  them.
* **TE4. Probe-variance interface.** Deferred (option (b)): Hutch++'s Gaussian and Rademacher
  identities are exact and need no `κ` interface. Revisit with XTrace (§8).
* **TE6. Scalars.** Definitions and unbiasedness over `𝕜`; variance and tail theorems over ℝ.
* **TE7. Named constants** (old TE10). `subgaussianRangeFinderFactor c` (proved $1 + 10c$) with a
  registry entry and API `1 ≤ ·`, monotone in `c`, `≤ 1 + 10c`; Hanson–Wright through the existing
  `hansonWrightConstant`.
* **TE8. Asymptotic forms** (old TE11). Thresholds on `card s` and `card t` separately; the
  docstring states the total $m = 2|s| + |t|$; the Gaussian variance form carries the cap
  `η ≤ 1`.
* **TE9. Placement** (old TE12). New `NLAlib/Estimation/Trace/` (layer 4, as `PORT_KRYLOV.md` D12
  lists), files `HutchPlusPlus.lean` and `HutchPlusPlusTail.lean`.
* **TE11. NA-Hutch++** (old TE14, MMMW Algorithm 2, Theorem 6). Deferred: for symmetric
  $\mathbf{A}$ the low-rank part is `generalizedNystrom A R S` (`SketchedLowRank.lean:198`), but
  Theorem 6 needs [CW09, Theorem 4.7], not in the library.

### Maintainer decisions (2026-10-18)

Maintainer: "okay go with (a) for both". TE5 (a): the generic Hutch++ tail theorem with a
range-finder hypothesis, plus the new constant-factor sub-Gaussian range finder L7 with
log(1/δ) failure (a variant of the existing
`measureReal_frobNorm_sub_rsvd_sq_gt_le_of_isSubgaussianVector`, whose JL-moment step costs
1/δ). TE10 (a): the exact variance identity is the primary Gaussian headline, with MMMW's
explicit-constant bound as its corollary. The other decisions proceed as recommended. XTrace is
deferred (§8).

## 8. Deferred: XTrace (maintainer, 2026-10-18: "let's just skip xtrace for now")

Key facts for a later round, checked against ETW:

* **Definition** (ETW (1.4) to (1.6), Algorithm 1.2): $k = m/2$ test vectors; basic estimator
  $\hat t_i = \operatorname{tr}\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega}_{-i}) +
  \boldsymbol{\omega}_i^{\mathsf{H}}(\mathbf{I} - \mathbf{P}_i)\mathbf{A}(\mathbf{I} - \mathbf{P}_i)
  \boldsymbol{\omega}_i$ with $\mathbf{P}_i = \mathbf{P}_{\mathbf{A}\mathbf{\Omega}_{-i}}$; XTrace is
  their average $\frac1k\sum_i \hat t_i$, $m$ products in all (ETW §2.1). Suggested spelling of the
  leave-one-out sketch: `X.submatrix id (Subtype.val : {j // j ≠ i} → κ)` (Gaussian by
  `hasLaw_submatrix_of_hasLaw_gaussianMatrix`, `Invariance.lean:177`; `card` one less), leave-two-out
  `{j // j ≠ i ∧ j ≠ i'}`.
* **Guarantees**: unbiased for independent isotropic vectors of any law ((5.1)); ETW Theorem 1.1
  gives mean-square bounds only, for standard normal vectors only; no high-probability bound.
  Normalized and sphere vectors (§2.3, §4.2) are numerical only.
* **Proposition 5.1**: $\mathbb{E}|\mathsf{xtrace} - \operatorname{tr}\mathbf{A}|^2 \le
  \frac2k\mathbb{E}\|(\mathbf{I} - \mathbf{\Pi}_1)\mathbf{A}\|_{\mathsf{F}}^2 +
  4\mathbb{E}\|(\mathbf{I} - \mathbf{\Pi}_{12})\mathbf{A}\|_2^2$. Proof: variance of the average as
  diagonal terms plus covariances (no exchangeability needed if every term gets the same Gaussian
  bound); covariance via the centring identity (5.2) to (5.4) with
  $\mathbf{X} = (\mathbf{I} - \mathbf{\Pi}_{12})\mathbf{A}(\mathbf{I} - \mathbf{\Pi}_{12})$,
  Cauchy–Schwarz, and the deterministic inequality
  $\|(\mathbf{I} - \mathbf{\Pi}_1)\mathbf{X}(\mathbf{I} - \mathbf{\Pi}_1) - \mathbf{X}\|_{\mathsf{F}}^2
  \le 2\|\mathbf{X}\|_2^2$ for nested projectors differing by rank at most one.
* **Library inputs** for the explicit bound: L3 at width $k - 1$; for the spectral term
  `integral_specNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix_pinvSpecNormBound`
  (`RangeFinder.lean:392`, Frobenius weight $O(1/\ell)$, which yields ETW's
  $O(1/m^2)\|\mathbf{A}\|_*^2$) and the incomparable TW RSVD2 form
  `integral_specNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix` (`:305`); Fact 5.5's spectral half
  $\sigma_r \le \|\mathbf{A}\|_*/(r+1)$ (new, `Matrix/Norms/Nuclear.lean`) and A6.
* **New lemmas it would need**: rank of a projector increment ($\le 1$ on deleting a column), the
  nested-projector inequality above (`Matrix/Subspaces/ProjectorPair.lean`), Frobenius equals
  spectral norm at rank $\le 1$, column-versus-rest independence from `iIndepFun.indepFun_finset`
  (Mathlib `Probability/Independence/Basic.lean:796`), and the probe-variance interface of TE4
  ($\mathbb{E}|\boldsymbol\omega^{\mathsf{H}}\mathbf{Y}\boldsymbol\omega - \operatorname{tr}\mathbf{Y}|^2
  \le \kappa\|\mathbf{Y}\|_{\mathsf{F}}^2$ for non-symmetric $\mathbf{Y}$; $\kappa = 2$ real,
  $1$ complex).
* **XNysTrace** (ETW (1.7) to (1.9), Proposition 5.3): uses `NLAlib.nystrom`; its variance needs
  second moments of the Nyström error ($\mathbb{E}\|\cdot\|_{\mathsf{F}}^2$, $\mathbb{E}\|\cdot\|_2^2$),
  which the library lacks (first moments only, `LowRank/Gaussian/Nystrom.lean:224`, `:110`).
* Estimated size when resumed: about 900 lines; the variance proof (three conditionings over
  subtype sketches) is the hard part.
