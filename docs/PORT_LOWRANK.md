# Port brief: the LowRank round

For the orchestrating agent building `NLAlib/LowRank/`. Read `CONTRIBUTING.md` in full first
(above all §5.2 "Numerical bounds", §5.3, §5.4 and §8), then `docs/design/Sketching-REPORT.md`
(the predicates this round consumes, §2 and §6.3), `docs/design/Probability-REPORT.md` (the
Gaussian and Haar matrix layer, §2 "Gaussian matrices" and "Haar frames"),
`docs/design/RandomMatrix-R2.md` and `docs/design/Mathlib-deviations.md`.
Status: **draft, 2026-10-15, revised the same day** (below). Written from the maintainer's request
and guidance (§0.1), then revised after a mathematics review and a design assessment of the
maintainer's own notes. Nothing in §3(a) is decided; §3(b) is decided by the orchestrator and open
to correction.

## Revision 2026-10-15

Inputs: the mathematics review of the first draft (13 amendments, cited "review A1" to "A13"),
and a design assessment of how the Chen–Persson manuscript in `~/Documents/Papers/LRA-paper/`
combines projection-cost-preserving sketches (PCPs) and truncation (cited "assessment"). Every
amendment of both is accepted. What changed:

1. **D1** restated with the assessment's verdict: one `obliqueProjector` core; `rsvd`,
   `generalizedNystrom`, `nystrom` and `sketchAndSolve` as definitions with bridge lemmas (the
   draft had no `rsvd` name); one exact split, also in core-noise form. D1 now says what is shared
   and where the analyses diverge, and limits the unification to that. "Hard to reverse" is
   narrowed to the argument orientation, the names and the §5.3 row (review, answer 2).
2. **Truncation and PCPs restructured** (§5). S2 is split. S2a holds the late-truncation lemmas,
   now including the perturbed-truncation lemma. S2b holds the early-truncation deterministic core
   together with the deterministic PCP predicate: that is where PCPs and truncation combine.
   Truncated GN in expectation and early-truncated GN join S6. The OSE-plus-AMM early-truncation
   tail joins S7. S9 keeps only the probabilistic PCP material. Early-truncated RSVD in
   expectation is deferred (§8). The retracted rank-constrained GN draft is not ported (D15).
3. **Norm claims corrected.** The Gram form covers the quadratic unitarily invariant norms (Schatten
   $p \ge 2$ of the error, squared), not every unitarily invariant norm. An unsquared triangle form
   in every gauge is added beside it (review A2, A13a).
4. **MT Theorem 14.1** is a spectral-norm statement, and its constant is not reached by this
   brief's route. S5 promises only what S2a proves, and nothing about that constant until TYUC
   NeurIPS has been read (review A1).
5. **The GN identity** gets a rank condition that makes it a statement, in two shapes, and is an
   identity for Haar $\mathbf{\Psi}$ too (review A3).
6. **Epperly–Webber simplified** (review A4): no limit, a finite group average in place of random
   permutations, and only the trace of the Beta inverse. Added: the coupled conjugation-average
   lemma and the Haar block-law lemmas. S4's estimate falls.
7. **Smaller changes.** EW Lemma 5.8 leaves S0 for S10 (A5). HMT 9.3 and the Nyström spectral
   truncation become one gauge lemma (A6). TW (RSVD1) is the primary tail (A7). The orientation of
   the projector's second argument is an orchestrator decision, D14 (A8). The isometry $\mathbf{Q}$
   is restored in item 2 (A9). Stage order is now S5 before S4 (A10). Downloads are re-tiered
   (A11). §10 is trimmed (A12). Corrections of record (A13).
8. **Citations.** The manuscript is unpublished and is never cited. §9.3 gives the published
   inputs for each ported result, and marks the manuscript's new results "proved without a
   literature source". Woodruff Theorem 47's rank-$k$ clause is cited only after a dimension check
   (D15). The policy is a confirmation question (§10).
9. **D3, D5 and D8** are now orchestrator decisions. D5 gains the optimality-hypothesis form of
   the truncation lemmas (assessment R3).
10. **Sizes:** the total rises from about 5600 to about 6750 lines (§7).

Two readings, not rejections:
- The assessment calls the uniform-PCP early-truncation corollary a consumer of the
  early-truncation core. Its proof uses only the PCP predicate and Eckart–Young, so the brief puts
  it *beside* the core in S2b, as a second route.
- The assessment's `Matrix/Inequalities/VonNeumann.lean` does not exist. Von Neumann's trace
  inequality is `norm_trace_conjTranspose_mul_le_sum_singularValues_mul` in
  `Matrix/Majorization/TraceInequalities.lean`.

Review A11 lists copying the EW PDF as an "essential download". It is a copy, so it is listed
under housekeeping in §9.2.

## 0. What this is and is not

### 0.1 The request and how this brief reads it

The maintainer's request, verbatim: "Next I would like to turn to one pass algorithms for low-rank
approximation (RSVD, GN, Nystrom). In general nystrom should be proved by the gram correspondence
when possible. https://arxiv.org/abs/2605.19096 this may be useful/important. We will also want
some results for truncated variants. Prepare for this".

Guidance the same day, verbatim: "Do not work on power, rbki, rp cholesky,etc yet. For truncation
also consider pcps. You can look at the structuring from the prototype and think about
reusability since these algorithms all kind of fall into the same general structure. You maybe
also work on sketched regression at this point since there is some overlap. It is okay to focus
on gaussian or haar only first if this makes sense, although eventually we would want
everything."

Guidance after the first draft, verbatim: "pcps and truncation can be combined together too.
There some notes on this chen persson somewhere on my computer. im not sure if unifying the
analyses of all these algorithms will simplify things or make it more complicated".

The brief's answer to the last point is D1: unify the *structure* (one projector, one exact
split, one structural bound), not the *analyses*. The truncated analyses diverge in ways that a
common abstraction would hide rather than simplify (§5).

The brief reads the request as follows. Each reading the maintainer should check is marked
**(check)**.

- **The algorithms.** Randomized low-rank approximation from sketches:
  - the randomized range finder and the randomized SVD (RSVD), whose output is
    $\mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A}$;
  - generalized Nyström (GN; Clarkson and Woodruff 2009, Tropp, Yurtsever, Udell and Cevher 2017,
    Nakatsukasa 2020), with output $\mathbf{A}\mathbf{\Omega}(\mathbf{\Psi}^{\mathsf{H}}\mathbf{A}
    \mathbf{\Omega})^{+}\mathbf{\Psi}^{\mathsf{H}}\mathbf{A}$;
  - Nyström for a positive semidefinite $\mathbf{A}$, with output $\mathbf{A}\langle\mathbf{\Omega}
    \rangle = \mathbf{A}\mathbf{\Omega}(\mathbf{\Omega}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega})^{+}
    \mathbf{\Omega}^{\mathsf{H}}\mathbf{A}$;
  - sketch-and-solve least squares, $\hat{\mathbf{X}} = (\mathbf{\Psi}^{\mathsf{H}}\mathbf{A})^{+}
    \mathbf{\Psi}^{\mathsf{H}}\mathbf{B}$, because GN is a range finder followed by
    sketch-and-solve (§4.1).
- **One pass and two passes (check).** The RSVD reads $\mathbf{A}$ twice: once for
  $\mathbf{Y} = \mathbf{A}\mathbf{\Omega}$, then again for $\mathbf{Q}^{\mathsf{H}}\mathbf{A}$.
  GN reads it once: both sketches $\mathbf{A}\mathbf{\Omega}$ and $\mathbf{\Psi}^{\mathsf{H}}
  \mathbf{A}$ are linear in $\mathbf{A}$ and can be accumulated in one pass or a stream. Nyström
  of a Hermitian matrix needs only $\mathbf{A}\mathbf{\Omega}$, since
  $\mathbf{\Omega}^{\mathsf{H}}\mathbf{A} = (\mathbf{A}\mathbf{\Omega})^{\mathsf{H}}$. What is
  formalised is the **output as a function of $\mathbf{A}$ and the sketches**. The pass count is a
  property of the formula, recorded in the docstrings. There is no streaming model, no cost model
  and no finite-precision analysis. Recommendation: keep it so. A streaming model adds a definition
  no theorem uses.
- **Nyström by the Gram correspondence.** For any factor $\mathbf{F}$ with $\mathbf{H} =
  \mathbf{F}^{\mathsf{H}}\mathbf{F}$, the Nyström approximation of $\mathbf{H}$ is
  $\mathbf{F}^{\mathsf{H}}\mathbf{P}_{\mathbf{F}\mathbf{\Omega}}\mathbf{F}$, and its error is the
  Gram matrix of the range finder's error on $\mathbf{F}$. The case
  $\mathbf{F} = \mathbf{H}^{1/2}$ is the maintainer's
  $\mathbf{A}^{1/2}\mathbf{P}_{\mathbf{A}^{1/2}\mathbf{\Omega}}\mathbf{A}^{1/2}$. Nyström theorems
  are corollaries of range-finder theorems wherever the transfer keeps the constant. §4.2 says
  exactly where it does.
- **Truncated variants (check).** The rank-$k$ outputs, with bounds against the best rank-$k$
  error, in the three forms of the maintainer's notes (§5.1):
  - **late** truncation $\llbracket\hat{\mathbf{A}}\rrbracket_k$ of the RSVD, GN and Nyström
    outputs (HMT §9.4, Gu 2015, TYUC 2017, Woodruff 2014 Lemma 44 and Theorem 47);
  - the **rank-$k$-restricted projection** $\mathbf{Q}\llbracket\mathbf{Q}^{\mathsf{H}}\mathbf{A}
    \rrbracket_k$ (Woodruff Lemma 48), which is the late truncation of the RSVD;
  - **early** truncation, which truncates the sketch before projecting:
    $\mathbf{P}_{\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k}\mathbf{A}$ and its GN twin.
    This is where PCPs enter (§5.3).
- **PCPs (check).** "pcps" is read as *projection-cost-preserving sketches* (Cohen, Elder, Musco,
  Musco and Persu 2015, cited "CEMMP"; Musco and Musco 2020). The maintainer's notes use exactly
  this notion (assessment §1.1).
- **Epperly and Webber 2026** (arXiv:2605.19096 v2, cited "EW" below). It is read in full, and §6
  says what of it is in scope.

### 0.2 Scope

- **In scope:**
  - **Deterministic layer:**
    - the shared definitions;
    - the Gram correspondence;
    - the exact error split of sketched projections, in projector and core form;
    - the structural bound of the range finder, in the Gram form and the unsquared triangle form;
    - the late-truncation lemmas, including the perturbed-truncation lemma;
    - the early-truncation deterministic core and the deterministic PCP predicate;
    - the Schur-complement facts EW needs.
  - **Probabilistic layer:**
    - Gaussian and Haar test matrices first: expectation, tail and exact formulas, including
      truncated GN in expectation and early-truncated GN;
    - EW's sharp upper bounds for rotation-invariant test matrices;
    - then the oblivious subspace injection (OSI) and embedding routes, which cover every family
      of the Sketching round, including the early-truncation tail;
    - the probabilistic PCP predicate;
    - optionally, EW's lower bounds (D6; recommended for a later round).
- **Not in scope** (later rounds, no stage; §8):
  - iterative and adaptive methods: power and subspace iteration (HMT §9.3, §10.4; MT §11.6),
    RBKI and block Krylov, polynomial filters, randomly pivoted Cholesky, adaptive rank
    determination;
  - column, volume and leverage-score selection, CUR and interpolative decompositions;
  - Nyström-preconditioned solvers (Frangella, Tropp and Udell 2023), and Nyström for matrix
    functions (Persson and Kressner 2023);
  - the three-sketch single-view core of Tropp et al. 2019 (MT §15.1, (15.10)–(15.12)), unless the
    maintainer adds it;
  - early-truncated RSVD *in expectation*. It needs smallest-singular-value tails (Gordon's
    inequality, a small-ball bound, inverse moments of order four) that RandomMatrix lacks (D15);
  - rank-constrained GN and the two-sided two-pass estimator from the maintainer's notes: there
    is no rigorous source for either (D15);
  - complex Gaussian and Haar laws, which belong to the RandomMatrix layer (D3);
  - streaming, cost and precision models;
  - SparseStack and OSNAP families (Sketching D6; they plug in through the OSI when they arrive).

## 1. Process

As in the Sketching round (`docs/PORT_SKETCHING.md` §1), with these amendments:

- **Consumers first.** Each stage note opens with its consumers. For the deterministic stages they
  are the later probabilistic stages and the Solvers round (sketch-and-solve). For the
  probabilistic stages they are users holding a sketch with a Sketching-round predicate. The
  atlas lists the downstream candidates: `nystrom-pcg`, `sketch-and-solve-ls`,
  `sketch-and-precondition`, `tgn-expected-error`, `etrsvd`, `etgn`, `truncation-lemma`,
  `rsvd-tail`, `nystrom-randomized`.
- **Degenerate-case checklist** for every statement, beyond PORT_PROBABILITY §3.2:
  - $\operatorname{rank}\mathbf{A} < k$ or $\le \ell$, where the range finder is exact almost
    surely (the prototype's `ae_gaussian_projection_reproduces_of_rank_le`);
  - $\operatorname{rank}\mathbf{A} < \ell$ for GN and truncated GN, where the output is exact
    almost surely (assessment A10);
  - $\operatorname{rank}\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k < k$ for early-truncated
    GN, where the completion factor is taken at the actual rank (assessment A10);
  - $\mathbf{V}_1^{\mathsf{H}}\mathbf{\Omega}$ without full row rank;
  - $\operatorname{rank}(\mathbf{\Psi}^{\mathsf{H}}\mathbf{X}) < \operatorname{rank}\mathbf{X}$,
    where the sketched projector is not onto $\operatorname{range}\mathbf{X}$ and is not invariant
    under $\mathbf{X}\mapsto\mathbf{X}\mathbf{M}$ (review A13f);
  - more samples than the dimension ($\ell > n$);
  - a truncation rank at or above the rank;
  - ties $\sigma_{k-1} = \sigma_k$, where `truncatedSVD` is a choice (D5);
  - Hermitian but not PSD inputs to Nyström;
  - an empty sketch index type;
  - $\ell = k + 1$ or $\ell = k$, where HMT's Gaussian expectations diverge. TW Theorem 8.7 and
    Corollary 8.8 give finite ones there (review A13d).
- **File budget.** About 1000 lines and twenty-five statements per file, or the note names its
  split.
- **Duplicate search** against Mathlib and `NLAlib/`, and against `Sketching/Properties/`, which
  already has CEMT Lemmas 2.1 and 2.6 (§2). Known starting points:
  - `isLeast_re_quadForm_fromBlocks` for the Schur-complement variational form;
  - `Factorizations/PolarFrames.lean` for polar factors and
    `eq_smul_one_of_forall_mul_mul_conjTranspose_eq`;
  - `norm_trace_conjTranspose_mul_le_sum_singularValues_mul` (von Neumann).
- **Skeleton rule, delegation and ledger** as in `docs/port/status.md`. The ledger accounts for
  the prototype's 324 `LowRank` declarations: in scope, ported or cut, and out of scope as deferred
  with §8 as the reason. The manuscript's formalization (§4.4) is proof material and is not
  ledgered.
- **Approval.** The maintainer confirms or decides §3(a) before any skeleton depends on it. §3(b)
  proceeds.
- **Design checkpoints** for the maintainer:
  - after S2b, when the deterministic layer has met its first consumers in S3's statement shapes.
    That layer is the shared definitions, the Gram correspondence, the structural bound, and late
    and early truncation with the PCP predicate;
  - after S6, before the OSI route generalises the Gaussian and Haar results.
- **Deviations from Mathlib.** None expected. The one new matrix definition (D1) has no Mathlib
  counterpart. Its §5.3 row amends the "oblique projector" row and needs two reviews
  (CONTRIBUTING §9).

## 2. What the library has, and what is missing

**Matrix layer**
- `truncatedSVD A k` (written $\llbracket\mathbf{A}\rrbracket_k$), chosen from an SVD:
  - rank, error singular values `singularValues_sub_truncatedSVD`, `specNorm_sub_truncatedSVD`,
    `frobNorm_sub_truncatedSVD_sq`;
  - Eckart–Young in spectral and Frobenius form, and in every unitarily invariant norm
    (`matrixNorm_sub_truncatedSVD_le_of_rank_le`, `isLeast_matrixNorm_sub_of_rank_le`, from
    Mirsky's theorem);
  - `rangeProjector_truncatedSVD_mul`.
- `Spectral/ProjectedLowRank.lean`:
  - the frame split $\|\mathbf{A}-\mathbf{Q}\mathbf{B}\|_{\mathsf{F}}^2 =
    \|(\mathbf{I}-\mathbf{Q}\mathbf{Q}^{\mathsf{H}})\mathbf{A}\|_{\mathsf{F}}^2 +
    \|\mathbf{Q}^{\mathsf{H}}\mathbf{A}-\mathbf{B}\|_{\mathsf{F}}^2$. This is the core-form
    split of D1 already;
  - the optimality of $\mathbf{Q}\llbracket\mathbf{Q}^{\mathsf{H}}\mathbf{A}\rrbracket_k$ among
    $\mathbf{Q}\mathbf{B}$ with $\operatorname{rank}\mathbf{B}\le k$ (Woodruff Lemma 44).
- `rangeProjector` and its residual:
  - monotonicity in the range, in spectral and Frobenius norm and in every gauge
    (`…_of_range_le`, `SymmetricGauge.matrixNorm_one_sub_rangeProjector_mul_rangeProjector_le`);
  - best approximation (`frobNorm_one_sub_rangeProjector_mul_le_frobNorm_sub_mul`, spectral twin);
  - `singularValues_one_sub_rangeProjector_mul_le`, `IsStarProjection.singularValues_mul_le`.
- `pinv` in every shape and rank, with `mul_pinv`, `pinv_eq_pinv_conjTranspose_mul_self_mul` and
  the generalized Schur complement (`Pseudoinverse/GeneralizedSchur.lean`, including the
  variational form `isLeast_re_quadForm_fromBlocks`).
- `Subspaces/Oblique.lean`: idempotents and the oblique projector
  $\mathbf{X}(\mathbf{Y}^{\mathsf{H}}\mathbf{X})^{-1}\mathbf{Y}^{\mathsf{H}}$ in the invertible
  case.
- `Factorizations/Nystrom.lean`: the Nyström residual along a *selection*
  $\mathbf{A}-\mathbf{A}_{:,e}(\mathbf{A}_{e,e})^{+}\mathbf{A}_{e,:}$. It is PSD, below
  $\mathbf{A}$, and the largest such matrix vanishing on the selected columns. Its link to
  elimination is there too.
- `Factorizations/PolarFrames.lean`: polar factors of products, and
  `eq_smul_one_of_forall_mul_mul_conjTranspose_eq` (a matrix commuting with every unitary is
  scalar).
- `CFC.sqrt` with `Matrix.PosSemidef.sqrt_le_sqrt`, `singularValues_sqrt_conjTranspose_mul_self`
  and `Matrix.PosSemidef.singularValues_eq_eigenvalue`.
- Weyl monotonicity `eigenvalue_le_eigenvalue_of_le`; `SymmetricGauge.matrixNorm` with
  `matrixNorm_mul_le_of_isStarProjection`, `matrixNorm_le_apply_single_mul_nuclearNorm`,
  `matrixNorm_le_of_singularValues_le`.
- Von Neumann's trace inequality `norm_trace_conjTranspose_mul_le_sum_singularValues_mul`
  (`Majorization/TraceInequalities.lean`).
- Schatten norms with `schattenNorm_two_mul_natCast_pow` (`SchattenPowers.lean`).

**RandomMatrix layer** (real laws only)
- `gaussianMatrix` with `hasLaw_conjTranspose_of_hasLaw_gaussianMatrix`, orthogonal invariance,
  independence of orthogonal blocks, and a.s. rank $\min(\operatorname{rank}\mathbf{A}, k)$.
- R2: $\mathbb{E}\|\mathbf{S}\mathbf{G}\mathbf{T}\|_{\mathsf{F}}^2 = \|\mathbf{S}\|_{\mathsf{F}}^2
  \|\mathbf{T}\|_{\mathsf{F}}^2$, also with $(\mathbf{S},\mathbf{T})$ independent of
  $\mathbf{G}$.
- Chevet's inequality for $\mathbb{E}\|\mathbf{S}\mathbf{G}\mathbf{T}\|_2$ and its tail
  (`Gaussian/SpectralNorm.lean`). The *second* spectral moment, which truncated GN needs (TW
  Lemma B.1), follows by integrating the tail; S6 checks whether it exists.
- R4 inverse moments:
  - $\mathbb{E}(\mathbf{G}\mathbf{G}^{\mathsf{H}})^{-1}$ and $\mathbb{E}\|\mathbf{G}^{+}\|_{\mathsf{F}}^2$;
  - $\mathbb{E}\|\mathbf{G}^{+}\|_{\mathsf{F}}^4$;
  - the spectral moments $\mathbb{E}\|\mathbf{G}^{+}\|_2^q$, with the constant
    $\frac{e}{k-r}\sqrt{(k+r-1)/2}$, which is sharper than TW Lemma B.3.
- R4 block moments `RandomMatrix/Gaussian/BlockMoments.lean`:
  - $\mathbb{E}\|\mathbf{S}\mathbf{G}_2\mathbf{G}_1^{+}\|_{\mathsf{F}}^2 =
    \|\mathbf{S}\|_{\mathsf{F}}^2\, r/(k-r-1)$ (HMT's step in Theorem 10.5);
  - the transposed form `integral_frobNorm_pinv_mul_mul_sq_of_hasLaw_gaussianMatrix`, for Nyström
    and GN;
  - the spectral block bound (HMT Theorem 10.6).
- R1 Lipschitz concentration in Frobenius (HMT Proposition 10.3).
- `haarFrame` as the polar factor of a Gaussian, with:
  - the classes `IsLeftUnitarilyInvariant` and `IsRightUnitarilyInvariant`;
  - the characterization `hasLaw_haarFrame_of_isLeftUnitarilyInvariant`;
  - the Gaussian–Haar transfer of every function of $\operatorname{range}(\mathbf{A}\mathbf{\Omega})$
    (`integral_comp_rangeProjector_mul_of_hasLaw_haarFrame`);
  - `hasLaw_conjTranspose_of_hasLaw_haarFrame`;
  - `hasLaw_const_mul_of_isLeftUnitarilyInvariant` and
    `integral_mul_mul_conjTranspose_of_isLeftUnitarilyInvariant` (for a *fixed* middle factor).

**Sketching layer** (over `𝕜`)
- `IsSubspaceInjection`, `IsSubspaceEmbedding`, `IsIsotropicSketch`, the oblivious predicates,
  `HasJLMoment` and AMM, with the transfer to an independent random subspace.
- In `Properties/LeastSquares.lean`, the GN step in OSI form, all in the sketch orientation
  ($\mathbf{S}$ on the left, raw `pinv` formulas):
  - CEMT Lemma 2.6;
  - its matrix right-hand side `IsSubspaceInjection.frobNorm_sub_mul_pinv_mul_sq_le`
    ($\|\mathbf{Y}-\mathbf{A}(\mathbf{S}\mathbf{A})^{+}\mathbf{S}\mathbf{Y}\|_{\mathsf{F}}^2 \le
    \|(\mathbf{I}-\mathbf{P}_{\mathbf{A}})\mathbf{Y}\|_{\mathsf{F}}^2 +
    \|\mathbf{S}(\mathbf{I}-\mathbf{P}_{\mathbf{A}})\mathbf{Y}\|_{\mathsf{F}}^2/a$);
  - the deterministic half of CEMT Lemma 2.1.
- In `Properties/Injection.lean`, both as tails $\delta + 1/t$.

**Missing**
- A name for the sketched projection and the algorithms; the Gram correspondence; the exact (not
  only upper) error split and the core-noise identity.
- The structural bound of the range finder in any form. The prototype's is real, Frobenius or
  spectral, and tied to SVD blocks.
- Truncation lemmas beyond Woodruff Lemma 44: the constant-1 gauge lemma, the perturbed-truncation
  lemma, the early-truncation core.
- A projection-cost-preserving predicate.
- Schur-complement concavity and monotonicity for a general test matrix.
- For EW: the block laws of a Haar unitary (column block, row block) and the coupled
  conjugation-average lemma (§4.3). No Beta-matrix law and no limit theorem are needed for the
  upper bounds (review A4).
- Everything probabilistic about low-rank outputs.

## 3. Decisions

### 3(a) For the maintainer

Each decision gives options, a recommendation, the reason, and what reversing it would cost.
D1, D2 and D4 are confirmations: the review found each consistent with the library and with the
sources. D6 and D7 are scope questions.

**D1. The shared structure (confirmation).** Every algorithm of the round has the same shape:
1. sketch the range, $\mathbf{Y} = \mathbf{A}\mathbf{\Omega}$;
2. fit coefficients by a least-squares problem, solved exactly or sketched with
   $\mathbf{\Psi}^{\mathsf{H}}$;
3. optionally truncate, after fitting (late) or before (early).

The prototype wrote it four times: `projResidual` with a hypothesis-level `Q`, `nystrom`,
`sketchedCore`/`sketchedOutput` and `rawGeneralizedNystrom`, with bridge files between them
(`RawNystromBridge` and friends). The maintainer's notes, by contrast, already write every proof in
one shape (orthonormal $\mathbf{Q}$, a core, a residual), and their Lean formalization reuses one
sketched-core file and one assembly lemma across GN, truncated GN and early-truncated GN
(assessment §2.1).

*Verdict and recommendation: option (a), deliberately limited.* Unify the structure, not the
analyses:
- one core definition;
- the algorithms as named definitions with bridge lemmas;
- one exact error split, stated in two forms.

Beyond that the analyses diverge, and the brief does not abstract over the divergence.

- **The core** (Matrix layer): the sketched (oblique) projector
  `obliqueProjector X Ψ := X * pinv (Ψᴴ * X) * Ψᴴ`, written $\mathbf{\Pi}_{\mathbf{X},\mathbf{\Psi}}$.
  - It extends the existing §5.3 row "oblique projector, from two bases
    $\mathbf{X}(\mathbf{Y}^{\mathsf{H}}\mathbf{X})^{-1}\mathbf{Y}^{\mathsf{H}}$" to every shape and
    rank, as `pinv` did for inverses.
  - It is total and always idempotent. Its range is $\operatorname{range}\mathbf{X}$ exactly when
    `(Ψᴴ * X).rank = X.rank`, which is the one hypothesis the identities need.
  - It equals `rangeProjector X` at `Ψ = 1` and at `Ψ = X`, and the old formula when
    `IsUnit (Ψᴴ * X)`. The invertible-case lemmas of `Oblique.lean` become
    `obliqueProjector_of_isUnit` corollaries.
  - The orientation of the second argument (test matrix $\mathbf{\Psi}$, applied as
    $\mathbf{\Psi}^{\mathsf{H}}$, or sketch $\mathbf{S}$ applied as is) is D14. The spellings in
    this brief are provisional until the S0 note.
- **The named instances**, as `def`s (not `abbrev`s: users search for them, and an abbrev
  unfolds in goals), each with a bridge to the core:

  | output | definition | bridge |
  |---|---|---|
  | RSVD | `rsvd A Ω := rangeProjector (A * Ω) * A` | `rsvd_eq_obliqueProjector`: `= obliqueProjector (A * Ω) 1 * A` |
  | GN | `generalizedNystrom A Ω Ψ := obliqueProjector (A * Ω) Ψ * A` | by `rfl` |
  | Nyström | `nystrom A Ω := generalizedNystrom A Ω Ω`, for every square `A`; theorems take `A.PosSemidef` | the Gram correspondence (§4.1 item 3); the selection case of `Factorizations/Nystrom.lean` at `Ω := selectionMatrix e` |
  | sketch-and-solve | `sketchAndSolve A Ψ B := pinv (Ψᴴ * A) * (Ψᴴ * B)` | `mul_sketchAndSolve`: `A * sketchAndSolve A Ψ B = obliqueProjector A Ψ * B` |
  | late truncations | `truncatedSVD (rsvd A Ω) k` and so on; no new names | D5 |
  | early truncations | `rangeProjector (truncatedSVD (A * Ω) k) * A` and `obliqueProjector (truncatedSVD (A * Ω) k) Ψ * A`; no new names | §5.3 |

  The docstring notation is $\mathbf{A}\langle\mathbf{\Omega}\rangle$ and
  $\mathbf{A}\langle\mathbf{\Omega},\mathbf{\Psi}\rangle$ (MT §2.7, EW Definitions 3.4 and 4.1).
  The existing Sketching statements keep their raw spelling, which `sketchAndSolve` unfolds to.
- **What is shared** (each proved once, §4.1):
  - the projector API, including invariance under $\mathbf{X}\mapsto\mathbf{X}\mathbf{M}$ for
    invertible $\mathbf{M}$ (under the rank hypothesis, which is not decorative: review A13f);
  - the exact error split in **projector form**
    $(\mathbf{I}-\mathbf{\Pi})\mathbf{B} = (\mathbf{I}-\mathbf{P}_{\mathbf{X}})\mathbf{B} -
    \mathbf{\Pi}(\mathbf{I}-\mathbf{P}_{\mathbf{X}})\mathbf{B}$ with orthogonal terms. The RSVD,
    GN, sketch-and-solve, gauge norms and EW consume this form;
  - the same split in **core form**. For orthonormal $\mathbf{Q}$ and any core $\mathbf{C}$,
    $\|\mathbf{A}-\mathbf{Q}\mathbf{C}\|_{\mathsf{F}}^2 =
    \|(\mathbf{I}-\mathbf{Q}\mathbf{Q}^{\mathsf{H}})\mathbf{A}\|_{\mathsf{F}}^2 +
    \|\mathbf{Q}^{\mathsf{H}}\mathbf{A}-\mathbf{C}\|_{\mathsf{F}}^2$. The **core noise** is
    $(\mathbf{\Psi}^{\mathsf{H}}\mathbf{Q})^{+}\mathbf{\Psi}^{\mathsf{H}}\mathbf{A} =
    \mathbf{Q}^{\mathsf{H}}\mathbf{A} + (\mathbf{\Psi}^{\mathsf{H}}\mathbf{Q})^{+}
    \mathbf{\Psi}^{\mathsf{H}}(\mathbf{I}-\mathbf{Q}\mathbf{Q}^{\mathsf{H}})\mathbf{A}$ when
    $\mathbf{\Psi}^{\mathsf{H}}\mathbf{Q}$ has full column rank. Truncation consumes this form
    (assessment R1);
  - the Gram correspondence, which carries Nyström;
  - the structural bound of the range finder (S1). It is consumed by the RSVD, its truncation,
    GN, Nyström and truncated GN;
  - the Gaussian completion identity in projector form: for fixed $\mathbf{X}$ of rank $q$ and an
    independent Gaussian $\mathbf{\Psi}$,
    $\mathbb{E}\|\mathbf{B}-\mathbf{\Pi}_{\mathbf{X},\mathbf{\Psi}}\mathbf{B}\|_{\mathsf{F}}^2 =
    (1+\frac{q}{p-q-1})\|(\mathbf{I}-\mathbf{P}_{\mathbf{X}})\mathbf{B}\|_{\mathsf{F}}^2$.
    GN, sketch-and-solve and early-truncated GN consume it.
- **Where the analyses diverge** (not unified, deliberately; §5):
  - *GN untruncated*: the completion identity is exact; there are no cross terms.
  - *Late truncation of GN*: truncation is nonlinear, so the completion identity is useless
    after it. The analysis needs the perturbed-truncation lemma, the *spectral* norm of the core
    noise, and the spectral second moment of the range residual. These three are used by
    truncated GN only.
  - *Early truncation*: a different deterministic core (the competitor lives on the sketch, with
    parameters $\lambda, w, \chi$) and a different probabilistic toolkit. It uses nothing of the
    structural bound.
  - *Nyström*: through the correspondence, not through the split.
  - *Norms*: truncated results are squared-Frobenius (trace for Nyström) statements. Neither the
    perturbed-truncation lemma nor the early-truncation core has a gauge version, and none is
    attempted (assessment R2).

Why the projector is the carrier and not an orthonormal basis: the sketches are measurable
functions (D2), and a basis of $\operatorname{range}(\mathbf{A}\mathbf{\Omega}(\omega))$ has random
width. `obliqueProjector (A * Ω ω) (Ψ ω)` has fixed index types. "Condition on $\mathbf{\Omega}$,
then $\mathbf{Q}$ is fixed" becomes "condition on $\mathbf{\Omega}$, then $\mathbf{X}$ is fixed
with `X.rank = q`". The proofs pass through a basis internally, by the single-view bridge of §4.1
item 1.

Other options:
- **(b)** A structure bundling a sketching scheme (test matrix, co-range sketch, recovery map),
  with algorithms as instances. It adds an object no theorem takes, since every bound is a
  function of $\mathbf{A}$ and the sketches.
- **(c)** The prototype's separate definitions per algorithm, joined by bridges. CONTRIBUTING
  §5.4 forbids it, and the prototype's bridge files show its cost.
- **(d)** No definitions: raw `pinv` formulas in every statement. §5.4 forbids it too.

*Home:* `def`s in the Matrix layer, beside `Factorizations/Nystrom.lean` (D12).

*How hard to reverse:* less than the draft said (review, answer 2). A `def` with a `_def` simp
lemma reverts to raw `pinv` formulas mechanically. What is sticky is the argument orientation
(D14), the names and the §5.3 row.

**D2. Test-matrix orientation and the probabilistic carrier (confirmation; hard to reverse).**
- The test matrix is $\mathbf{\Omega}$ : `Matrix n ℓ 𝕜`, multiplied on the right
  ($\mathbf{Y} = \mathbf{A}\mathbf{\Omega}$). The co-range sketch is $\mathbf{\Psi}$ :
  `Matrix m p 𝕜`, applied as $\mathbf{\Psi}^{\mathsf{H}}\mathbf{A}$. This is the orientation of
  HMT, MT, CEMT, EW and the maintainer's notes, and of the existing block moments.
- Probabilistic hypotheses go on the sketch $\mathbf{\Omega}^{\mathsf{H}}$ in the Sketching
  round's orientation: `IsObliviousSubspaceInjection (fun ω => (Ω ω)ᴴ) d a δ μ`, which is CEMT's
  Definition 1.2 literally (their sketch is $\mathbf{\Omega}^{*}$, checked on p. 3).
- Laws: `HasLaw Ω (gaussianMatrix n ℓ) μ` and `HasLaw Ω (haarFrame n ℓ) μ`. The bridges to the
  sketch orientation exist (`hasLaw_conjTranspose_of_…`).
- Two sketches: `IndepFun Ω Ψ μ`.
- The per-family orientation lemmas of S7 also need the real scaling of the predicates. For
  example, the Gaussian OSI is stated for $(\sqrt{k})^{-1}\mathbf{G}$.

*Alternative:* sketches throughout, with $\mathbf{Y} = \mathbf{A}\mathbf{S}^{\mathsf{H}}$. That
makes every formula in every source read transposed.

*Recommendation:* the test-matrix orientation above. It is forced by consistency with the
Sketching round. *Rework if reversed:* every probabilistic statement.

**D4. Error measures and the shape of probabilistic statements (confirmation; hard to
reverse).**
- **Deterministic: the Gram form, which covers the quadratic unitarily invariant norms.** The
  primary structural statements bound `Φ.matrixNorm (Eᴴ * E)` for the error `E`, for every
  `Φ : SymmetricGauge`. This is $\Phi(\sigma(\mathbf{E})^2)$, MT's "quadratic unitarily invariant
  norm" of $\mathbf{E}$ (Theorem 11.4 remark).
  - It reaches $\|\mathbf{E}\|_{S_p}^2$ for every $p \ge 2$ (spectral squared at $p = \infty$,
    Frobenius squared at $p = 2$) and every gauge of the squared singular values (Ky Fan norms of
    $\sigma^2$).
  - It does **not** reach $\|\mathbf{E}\|_{S_p}$ for $p < 2$ (the nuclear norm of $\mathbf{E}$,
    for instance), nor an arbitrary unitarily invariant norm squared (review A2).
  - Nyström needs exactly this family. Its error *is* `Eᴴ * E`, so every unitarily invariant
    norm of the Nyström error is a quadratic norm of the range finder's error (§4.2).
- **Deterministic companion: the unsquared triangle form in every gauge.**
  $\|(\mathbf{I}-\mathbf{P}_{\mathbf{Y}})\mathbf{A}\|_\Phi \le \|\mathbf{E}\|_\Phi +
  \|\mathbf{M}\|_\Phi$ for every `Φ` (§4.1 item 6).
  - It is what HMT 10.6 (the first spectral moment) consumes, and what a user wanting a
    nuclear-norm bound needs.
  - The unsquared spectral and Frobenius forms are corollaries of either form.
- **Truncated results:** squared Frobenius, and trace for Nyström (D1, "Norms").
- **Gaussian and Haar: expectation first, tails second.**
  - Expectations are where the sharp results are: HMT 10.5 and 10.6, Tropp and Webber 2023 (TW)
    Theorem 8.1 (RSVD2) and 8.7, EW.
  - Each expectation upper bound comes with its `integrable_…` companion.
  - Exact identities are stated as equalities: EW Theorem 2.1, the GN identity in both shapes
    (§4.3).
  - The primary tail is TW Theorem 8.1 (RSVD1): one tail for every Schatten $p\in[2,\infty]$,
    in the Gram form, transferring to Nyström unchanged. HMT 10.7 and 10.8 sit beside it or follow
    as corollaries (review A7).
  - CONTRIBUTING's "tails, not sample sizes" rule is respected: no theorem is stated as a sample
    size; sample-size forms are corollaries.
- **OSI and OSE: tails in the Sketching round's form.**
  - The failure probability is $\delta + 1/t$ and the factor $(1 + t/a)$ is explicit, where CEMT
    write "$C/\alpha$ with probability 9/10".
  - This is Sketching S1's `HasSubspaceInjection.measure_frobNorm_mul_pinv_sq_gt_le` composed
    with the structural bound.
  - There is no universal constant. CEMT's $C$ becomes $t$, chosen by the user.
- **Which norms per algorithm.**

  | algorithm | spectral | Frobenius | other |
  |---|---|---|---|
  | RSVD | yes | yes | Schatten $p \ge 2$ and every quadratic norm through the Gram form; every gauge, unsquared, through the triangle form |
  | Nyström | yes | yes | nuclear (trace) first: the norm whose range-finder twin (Frobenius squared) carries the sharp results; every gauge through the Gram form (review A13a) |
  | GN | no | yes | the literature's bounds are Frobenius only (EW Theorem 4.2, CEMT Corollary 2.8, Woodruff Theorem 47), and MT Remark 15.4 notes that relative spectral bounds are impossible for one-pass methods |
  | truncated outputs | deterministic only (§4.1 items 7.1, 7.2) | yes | trace for Nyström |

*Rework if reversed:* the statement shape of every theorem.

**D6. EW's lower bounds.** These are the minimax optimality results, EW Theorems 2.2, 3.3, 3.6(b)
and 4.2(b). Do they belong to this round?
- *Recommendation:* a later round, unless the maintainer wants minimax statements now
  (review, answer 5).
  - No downstream proof applies a lower bound.
  - They need the heaviest new infrastructure: a Haar unitary on $\mathbb{K}^{n\times n}$
    independent of the sketch, a probabilistic-method argument, and a limit under monotone
    convergence.
  - S10 is kept as a placeholder. EW Lemma 5.8 ("weighting hurts") goes with it, since its only
    consumer is the sketch-and-solve lower bound (review A5).
- The sharp *upper* bounds and the exact formulas are in the main line (S4, S6).

*Rework:* none.

**D7. Projection-cost-preserving sketches: in this round, and where.** §5 assesses them.
- *Recommendation:* yes, split by layer.
  - **S2b**, the deterministic part, beside the early-truncation core:
    - the predicate `IsProjectionCostPreserving`;
    - its consequence (a $\gamma$-optimal projector for the sketch is
      $\gamma\frac{1+\varepsilon}{1-\varepsilon}$-optimal for $\mathbf{A}$);
    - the constructor from a subspace embedding of the row space;
    - the uniform-PCP early-truncation corollary.

    This is where "pcps and truncation can be combined": S2b holds both routes to early
    truncation side by side.
  - **S9**, the probabilistic part: the tail form, its family corollaries, and the early-truncation
    corollaries through it.
  - The $O(k/\varepsilon^2)$ head–tail constructor waits for CEMMP to be in hand and for
    spectral-norm AMM (Sketching §6.1 item 3, deferred).
- The PCP is *not* the interface of late truncation, and for early truncation it is one of two
  routes. The other is the sharper non-uniform core (§5.3).

*Rework:* none. If declined, S2b keeps only the core, and S9 is empty.

### 3(b) Decisions the orchestrator takes

**D3. Field (decided).**
- Deterministic results are over `𝕜`, including the perturbed-truncation lemma and the
  early-truncation core. The manuscript states them over ℝ, but their proofs are algebraic plus
  von Neumann; the S2a and S2b notes confirm.
- OSI and OSE results are over `𝕜`, since the Sketching predicates and the SRHT and CountSketch
  laws are.
- Gaussian and Haar results are real, because the laws are (`Probability-REPORT.md` §4 item 11;
  CONTRIBUTING §5.1).
- EW's complex constants ($\alpha_{\mathbb{C}} = 0$) are new theorems later, beside the real ones:
  `…_of_hasLaw_gaussianMatrix` now, `…_of_hasLaw_complexGaussianMatrix` later.

*Rework:* none; complex results are added beside.

**D5. Truncation: the operator and the hypothesis form (decided).**
- The truncation is `truncatedSVD Â k`, written $\llbracket\hat{\mathbf{A}}\rrbracket_k$, for
  every output. No new truncation operator.
- `truncatedSVD` is a choice. `truncatedSVD (Q * X) k = Q * Y` holds only for *some* best
  approximation $\mathbf{Y}$ of $\mathbf{X}$. So the truncation lemmas are written against a
  one-line optimality hypothesis, not against `truncatedSVD` itself:
  `Y.rank ≤ k ∧ frobNorm (C - Y) ≤ frobNorm (C - truncatedSVD C k)`
  (the formalization's `IsBestRankApprox`; assessment R3). With them:
  - a lemma that $\mathbf{Q}^{\mathsf{H}}\,$`truncatedSVD (Q * X) k` satisfies the hypothesis for
    $\mathbf{X}$, and that `truncatedSVD (Q * X) k` equals $\mathbf{Q}$ times it;
  - the `truncatedSVD` forms as corollaries;
  - choice-free identities where they hold: in Frobenius norm,
    $\|\mathbf{A}-\llbracket\mathbf{P}_{\mathbf{Y}}\mathbf{A}\rrbracket_k\|_{\mathsf{F}} =
    \|\mathbf{A}-\mathbf{Q}\llbracket\mathbf{Q}^{\mathsf{H}}\mathbf{A}\rrbracket_k\|_{\mathsf{F}}$
    for every orthonormal basis $\mathbf{Q}$ of $\operatorname{range}\mathbf{Y}$. Both equal the
    residual plus a tail of the same singular values.
- A predicate is added under its own §5.4 review only if the S2a note finds the hypothesis
  repeated in more than three statements.

*Rework:* low.

**D8. Where sketched regression lives (decided).**
- The deterministic sketch-and-solve facts already live in
  `Sketching/Properties/LeastSquares.lean`. `sketchAndSolve` and the exact split go in the Matrix
  layer with `obliqueProjector` (S0).
- GN (layer 4) needs the exact Gaussian and Haar sketch-and-solve formulas (EW Theorem 2.1), so
  they cannot wait for the Solvers layer (layer 5). They go in a new
  `Sketching/Gaussian/LeastSquares.lean` (S6), and Solvers imports them later.

*Rework:* file moves only.

**D9. Constants.**
- Source constants are written in the statements:
  - HMT's $1 + k/(\ell-k-1)$;
  - EW's $\frac{r-\ell}{r-q}\bigl(1+\frac{q}{\ell-q-1}\bigr)$;
  - the GN and completion factor $1 + q/(p-q-1)$;
  - the Haar completion factor $1 + \frac{d-p}{d-q}\cdot\frac{q}{p-q-1}$ ($d$ the ambient
    dimension, $p$ the sketch size, $q$ the rank).
- Because they repeat across RSVD, Nyström, GN and their truncations, each is a named real
  function with its source formula as body. It is a plain `def` with a `_def` simp lemma, not an
  `irreducible_def`, since the body is the source's. CONTRIBUTING §4 requires named quantities,
  not repeated inline formulas.
- Names say what the quantity is, never how good it is (§5.2 rule 1). Candidates, fixed in the S3
  note:
  - `gaussianProjectionFactor k ℓ` $= 1 + k/(\ell-k-1)$. It is $1 + \mathbb{E}
    \|\mathbf{G}_1^{+}\|_{\mathsf{F}}^2$ for a real $k \times \ell$ Gaussian, and it is also the
    completion factor (one `def` with two docstring roles; assessment A9);
  - `rotationInvariantFactor r ℓ q`;
  - `haarProjectionFactor d p q`;
  - `truncatedGNFactor k ℓ p` for truncated GN (§4.3). Its constants are the proof's, not a
    source's, so it falls under §5.2 rule 2: a definition with positivity, monotonicity and an
    explicit upper comparison as its API.
- Sizes are index types; the target rank is `q k r : ℕ` with `q + 2 ≤ Fintype.card ℓ`. No
  oversampling variable in statements: it is `card ℓ - k` in words only.
- HMT's simpler bound coexists with EW's as a corollary that keeps its own name (rule 6: it needs
  no rank hypothesis).

**D10. Incomparable bounds coexist (rule 4).**
- HMT 10.6 (first moment of the spectral error, constant $e\sqrt{k+p}/p$) and the second-moment
  bound from the Gram form (TW (RSVD2) at $p=\infty$). The first is better for large $k$.
- The OSI bound $(1+t/a)$ and the OSE plus AMM bound $(1+\varepsilon)$ (Woodruff Lemma 45),
  named by hypothesis (`_of_isObliviousSubspaceInjection`, `_of_hasJLMoment`).
- Late truncation: the generic $+2\|\mathbf{A}-\hat{\mathbf{A}}\|_{\mathsf{F}}$ lemma and the
  perturbed-truncation lemma's $+2\sqrt{2k}\,\|\mathbf{E}\|_2$. The second wins when $\mathbf{E}$
  has stable rank above $2k$, which is the sketch-and-solve case. They are named by the parameter
  of the bound.
- Early truncation: the core route and the uniform-PCP route, named by hypothesis.
- TW (RSVD1) and HMT 10.7 and 10.8 tails, where neither dominates.

**D11. Names.**
- Following §4 of CONTRIBUTING: `frobNorm_sub_generalizedNystrom_sq_le_…`,
  `integral_frobNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix`, `matrixNorm_sub_nystrom_le_…`,
  `matrixNorm_sub_truncatedSVD_le_add_of_singularValues_le`.
- Definitions `rsvd`, `generalizedNystrom`, `nystrom`, `sketchAndSolve` (D1). `rsvd` reverses the
  draft's "no `rsvd` name": a named instance is what users search for, and its bridge to
  `rangeProjector` is one line.
- Result ids (CONTRIBUTING §6.4): `randomized-svd-expected-error`, `gram-correspondence`,
  `generalized-nystrom-expected-error`, `nystrom-expected-error`,
  `range-finder-structural-bound` (described as "the Gram form, every quadratic unitarily
  invariant norm"), `truncation-lemma`, `perturbed-truncation`, `tgn-expected-error`,
  `early-truncation-structural-bound`, `etrsvd`, `etgn`, `projection-cost-preserving-sketch`.
  The S notes check them against the explore repository's map.

**D12. Layout.**
- Matrix layer:
  - `Matrix/Subspaces/ObliqueProjector.lean` (new; `Oblique.lean` keeps the invertible case);
  - `Matrix/Factorizations/Nystrom.lean` (extended);
  - `Matrix/Factorizations/NystromOrder.lean` (Schur-complement order facts).
- `LowRank/` subdirectories:
  - `Structural/`: deterministic bounds (`RangeFinder.lean`, `Truncation.lean`,
    `EarlyTruncation.lean`);
  - `Gaussian/`: Gaussian and Haar;
  - `Oblivious/`: the OSI and OSE routes;
  - `Optimality/`: EW lower bounds, if kept.
- The PCP predicate goes in `Sketching/Properties/ProjectionCost.lean`.

**D13. Bibliography and citation policy.**
- New keys before citing (CONTRIBUTING §6): `TroppWebber2023`, `EpperlyWebber2026`,
  `TroppYurtseverUdellCevher2017` (SIMAX), `TroppYurtseverUdellCevher2017a` (NeurIPS),
  `CohenElderMuscoMuscoPersu2015`. Later, as the nice-to-have papers arrive: `GittensMahoney2016`,
  `Nakatsukasa2020`, `Gu2015`, `MuscoMusco2020`, `ClarksonWoodruff2009`.
- **The Chen–Persson manuscript** (`~/Documents/Papers/LRA-paper/main.tex`, August 2026, no venue;
  the prototype's `cp25`) is unpublished. The maintainer has asked before that it not be cited as a
  source; for this library that is Sketching D16. It is material only. Each ported result cites
  the published source that states it. A result that first appears in the manuscript says "proved
  without a literature source" and cites only its published inputs. §9.3 lists both, result by
  result. The maintainer confirms the policy for this round (§10, question 7).

**D14. Orientation of `obliqueProjector`'s second argument (decided in the S0 note; review A8).**
- *Test-matrix orientation*, `obliqueProjector X Ψ := X * pinv (Ψᴴ * X) * Ψᴴ`. It matches the
  sources' $\mathbf{\Psi}^{*}$.
- *Sketch orientation*, `obliqueProjector X S := X * pinv (S * X) * S`. It matches the library:
  `IsSubspaceInjection S U a` and `frobNorm_sub_mul_pinv_mul_sq_le` have $\mathbf{S}$ on the left.
  GN is then `obliqueProjector (A * Ω) Ψᴴ * A`, Nyström `obliqueProjector (A * Ω) Ωᴴ * A`,
  regression `obliqueProjector A Ψᴴ * B`, and RSVD `obliqueProjector X 1`.
- *Leaning:* the sketch orientation. D2 already puts the Sketching predicates on
  $\mathbf{\Omega}^{\mathsf{H}}$ and $\mathbf{\Psi}^{\mathsf{H}}$, so the predicate's matrix and the
  projector's argument become literally the same term, with no `conjTranspose_conjTranspose` at
  each use. The S0 note records the decision and the reason.

**D15. What of the maintainer's notes is ported, and what is not.**
- **Ported** (§5, §9.3):
  - the perturbed-truncation lemma (S2a);
  - the early-truncation deterministic core and its almost-sure corollary (S2b);
  - the uniform-PCP early-truncation corollary (S2b);
  - truncated GN in expectation (S6);
  - early-truncated GN as a composition (S6, S7, S9);
  - the OSE-plus-AMM early-truncation tail (S7);
  - the spectral tail-flattening lemma (S1).
- **Deferred** (§8): early-truncated RSVD in expectation. It needs Gordon's inequality with
  Gaussian concentration for $\sigma_{\min}$, a chi-square small-ball bound, and a layer-cake
  integral with inverse moments of $\min\{1,\lambda\}$ up to order four. None of this is in
  RandomMatrix, and the "defer very complex material" rule applies. The deterministic core and the
  tail-form consumers give the library an early-truncation result without it.
- **Not ported:**
  - **rank-constrained GN** (`~/Documents/Papers/Generalized Nystrom/rank_constrained_gn.tex`). Its
    proof is retracted in `research/STATUS.md`, whose "Lemma B" (a uniform affine embedding over
    all rank-$k$ cores at $O(s/\varepsilon)$ rows) is false as stated;
  - the two-sided two-pass estimator $\mathbf{Q}\llbracket\mathbf{Q}^{\mathsf{H}}\mathbf{A}
    \mathbf{P}\rrbracket_k\mathbf{P}^{\mathsf{H}}$ (draft only);
  - the $2\times 2$ lower bound for early truncation (draft only).

  These are recorded in §8 with "no rigorous source" as the reason.
- **Woodruff Theorem 47 caution.** Its rank-$k$ clause
  $\llbracket\mathbf{A}\mathbf{R}\mathbf{U}\rrbracket_k\mathbf{U}^{\mathsf{T}}
  (\mathbf{S}\mathbf{A}\mathbf{R})^{+}\mathbf{S}\mathbf{A}$ goes through an affine-embedding
  step. The notes found that a uniform affine embedding over all rank-$k$ cores fails at the
  dimension one might expect. Before S2a or S7 states or cites that clause, its note checks which
  dimension Woodruff's step actually needs and says how the published route avoids the false
  lemma. If it cannot, the clause is not ported.

## 4. The mathematics

### 4.1 The deterministic layer

Notation, for this section only: $\mathbf{A}\in\mathbb{K}^{m\times n}$; test matrix
$\mathbf{\Omega}\in\mathbb{K}^{n\times\ell}$ with $\mathbf{Y} = \mathbf{A}\mathbf{\Omega}$; co-range
sketch $\mathbf{\Psi}\in\mathbb{K}^{m\times p}$; $\mathbf{\Pi}_{\mathbf{X},\mathbf{\Psi}}$ is
`obliqueProjector X Ψ` (in the sources' orientation; D14); $\mathbf{P}_{\mathbf{X}}$ is
`rangeProjector X`. Singular values and eigenvalues are indexed from $1$ in this prose. The
library indexes from $0$, so $\sigma_{k+1}$ is `singularValues A k`.

1. **Oblique projector API (S0).**
   - $\mathbf{\Pi}$ is idempotent, for every rank ($\mathbf{M}^{+}\mathbf{M}\mathbf{M}^{+} =
     \mathbf{M}^{+}$).
   - $(\mathbf{I}-\mathbf{P}_{\mathbf{X}})\mathbf{\Pi} = \mathbf{0}$, always.
   - $\mathbf{\Pi}_{\mathbf{X},\mathbf{\Psi}}\mathbf{P}_{\mathbf{X}} = \mathbf{P}_{\mathbf{X}}$,
     and $\operatorname{range}\mathbf{\Pi} = \operatorname{range}\mathbf{X}$, exactly when
     $\operatorname{rank}(\mathbf{\Psi}^{\mathsf{H}}\mathbf{X}) = \operatorname{rank}\mathbf{X}$.
     The hypothesis is spelled `(Ψᴴ * X).rank = X.rank`. It follows from
     `IsSubspaceInjection Ψᴴ X a` with `0 < a`.
   - $\mathbf{\Pi}_{\mathbf{X}\mathbf{M},\mathbf{\Psi}} = \mathbf{\Pi}_{\mathbf{X},\mathbf{\Psi}}$
     for invertible $\mathbf{M}$, under the rank hypothesis. It fails without it: take
     $\mathbf{X} = \mathbf{I}$, $\mathbf{\Psi} = \mathbf{e}_1$ and $\mathbf{M}$ unit upper
     triangular (review A13f).
   - $\mathbf{\Pi}_{\mathbf{X},\mathbf{1}} = \mathbf{\Pi}_{\mathbf{X},\mathbf{X}} =
     \mathbf{P}_{\mathbf{X}}$ (`mul_pinv`, `pinv_eq_pinv_conjTranspose_mul_self_mul`).
   - **Exactness at low rank** (assessment A1): if $\operatorname{range}\mathbf{B}\subseteq
     \operatorname{range}\mathbf{X}$ and the rank hypothesis holds, then
     $\mathbf{\Pi}_{\mathbf{X},\mathbf{\Psi}}\mathbf{B} = \mathbf{B}$. In core form: the sketched
     core is $\mathbf{Q}^{\mathsf{H}}\mathbf{B}$ and the output is $\mathbf{B}$.
   - **The single-view form** $\mathbf{Y}(\mathbf{\Psi}^{\mathsf{H}}\mathbf{Y})^{+} =
     \mathbf{Q}(\mathbf{\Psi}^{\mathsf{H}}\mathbf{Q})^{+}$, when $\mathbf{Y} = \mathbf{Q}\mathbf{R}$
     with $\mathbf{R}$ of full row rank and $\mathbf{\Psi}^{\mathsf{H}}\mathbf{Q}$ of full column
     rank. This is what TYUC and CEMT's Algorithm 4 compute (MT §15.1, (15.8)). It is the bridge
     the probabilistic proofs use to pass from the projector to a fixed basis.
2. **The exact error split (S0).** Under the rank hypothesis, for every $\mathbf{B}$:
   $$\bigl((\mathbf{I}-\mathbf{\Pi})\mathbf{B}\bigr)^{\mathsf{H}}(\mathbf{I}-\mathbf{\Pi})\mathbf{B}
   = \bigl((\mathbf{I}-\mathbf{P}_{\mathbf{X}})\mathbf{B}\bigr)^{\mathsf{H}}
   (\mathbf{I}-\mathbf{P}_{\mathbf{X}})\mathbf{B} +
   \bigl(\mathbf{\Pi}(\mathbf{I}-\mathbf{P}_{\mathbf{X}})\mathbf{B}\bigr)^{\mathsf{H}}
   \mathbf{\Pi}(\mathbf{I}-\mathbf{P}_{\mathbf{X}})\mathbf{B}.$$
   - The cross terms vanish because $(\mathbf{I}-\mathbf{P}_{\mathbf{X}})\mathbf{\Pi} = \mathbf{0}$.
   - So in every gauge, $\|\cdot\|_\Phi$ of the left side is at most the sum. In trace it is an
     identity: EW Lemma 5.1, CEMT Lemma 2.6, TYUC Lemma A.4.
   - With an orthonormal $\mathbf{Q}$ for $\operatorname{range}\mathbf{X}$ and its complement
     $\mathbf{Q}_\perp$, the second term is
     $\mathbf{Q}(\mathbf{\Psi}^{\mathsf{H}}\mathbf{Q})^{+}(\mathbf{\Psi}^{\mathsf{H}}\mathbf{Q}_\perp)
     \mathbf{Q}_\perp^{\mathsf{H}}\mathbf{B}$, with the leading isometry $\mathbf{Q}$ (review A9).
     The Gram matrices agree with and without it, but the Lean statement needs it.
   - **Core form** (assessment R1). With $\mathbf{Q}$ as above and any core $\mathbf{C}$,
     $\|\mathbf{B}-\mathbf{Q}\mathbf{C}\|_{\mathsf{F}}^2 =
     \|(\mathbf{I}-\mathbf{Q}\mathbf{Q}^{\mathsf{H}})\mathbf{B}\|_{\mathsf{F}}^2 +
     \|\mathbf{Q}^{\mathsf{H}}\mathbf{B}-\mathbf{C}\|_{\mathsf{F}}^2$. This is in
     `ProjectedLowRank` already; S0 restates it as the core-form split. Its instances:
     - $\mathbf{C} = \mathbf{Q}^{\mathsf{H}}\mathbf{B}$: the RSVD;
     - $\mathbf{C} = \llbracket\mathbf{Q}^{\mathsf{H}}\mathbf{B}\rrbracket_k$: the truncated RSVD;
     - $\mathbf{C} = \hat{\mathbf{X}}$: GN;
     - $\mathbf{C} = \llbracket\hat{\mathbf{X}}\rrbracket_k$: truncated GN.
   - **Core noise.** The sketched core is $\hat{\mathbf{X}} :=
     (\mathbf{\Psi}^{\mathsf{H}}\mathbf{Q})^{+}\mathbf{\Psi}^{\mathsf{H}}\mathbf{B} =
     \mathbf{Q}^{\mathsf{H}}\mathbf{B} + \mathbf{N}$, where
     $\mathbf{N} = (\mathbf{\Psi}^{\mathsf{H}}\mathbf{Q})^{+}\mathbf{\Psi}^{\mathsf{H}}
     (\mathbf{I}-\mathbf{Q}\mathbf{Q}^{\mathsf{H}})\mathbf{B}$, when
     $\mathbf{\Psi}^{\mathsf{H}}\mathbf{Q}$ has full column rank. $\mathbf{N}$ is the second term
     of the projector form in $\mathbf{Q}$-coordinates.
   - The existing `IsSubspaceInjection.frobNorm_sub_mul_pinv_mul_sq_le` is then a corollary
     (reproved, name kept; rule 6).
   - EW's solution error (5.1), $\hat{\mathbf{X}} - \mathbf{A}^{+}\mathbf{B} = \mathbf{R}^{+}
     (\mathbf{\Psi}^{\mathsf{H}}\mathbf{Q})^{+}(\mathbf{\Psi}^{\mathsf{H}}\mathbf{Q}_\perp)
     \mathbf{Q}_\perp^{\mathsf{H}}\mathbf{B}$, sits beside it for unbiasedness.

   This one identity serves:
   - sketched regression ($\mathbf{X} = \mathbf{A}$);
   - GN ($\mathbf{X} = \mathbf{A}\mathbf{\Omega}$, $\mathbf{B} = \mathbf{A}$): the error is the
     RSVD error plus a sketch-and-solve excess;
   - early-truncated GN ($\mathbf{X} = \llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k$);
   - the RSVD itself ($\mathbf{\Psi} = \mathbf{1}$, second term zero).
3. **The Gram correspondence (S0).** For any $\mathbf{F}$ and $\mathbf{H} =
   \mathbf{F}^{\mathsf{H}}\mathbf{F}$, and every rank:
   $$\mathbf{H}\langle\mathbf{\Omega}\rangle =
   (\mathbf{P}_{\mathbf{F}\mathbf{\Omega}}\mathbf{F})^{\mathsf{H}}\mathbf{P}_{\mathbf{F}\mathbf{\Omega}}
   \mathbf{F},\qquad \mathbf{H} - \mathbf{H}\langle\mathbf{\Omega}\rangle =
   \bigl((\mathbf{I}-\mathbf{P}_{\mathbf{F}\mathbf{\Omega}})\mathbf{F}\bigr)^{\mathsf{H}}
   (\mathbf{I}-\mathbf{P}_{\mathbf{F}\mathbf{\Omega}})\mathbf{F}.$$
   - The proof is one line from `pinv_eq_pinv_conjTranspose_mul_self_mul`, since
     $(\mathbf{F}\mathbf{\Omega})^{\mathsf{H}}\mathbf{F}\mathbf{\Omega} =
     \mathbf{\Omega}^{\mathsf{H}}\mathbf{H}\mathbf{\Omega}$.
   - Sources: MT Proposition 11.1 ($|\mathbf{E}|^2 = (\mathbf{B}^{*}\mathbf{B})/\mathbf{X}$) and
     §14.2; EW Fact 3.5; CEMT Imported Theorem 2.4, after Gittens and Mahoney 2016 Lemma 1; TW §5.4
     and the proof of Corollary 8.2.
   - It is stated for a general factor, so it covers kernel and Gram matrices with no square root.
     `CFC.sqrt` enters once, in the corollary $\mathbf{F} = \mathbf{H}^{1/2}$.
   - Companions:
     - $\mathbf{H}\langle\mathbf{\Omega}\rangle$ and $\mathbf{H}/\mathbf{\Omega}$ are PSD;
     - $\mathbf{H}\langle\mathbf{\Omega}\mathbf{M}\rangle = \mathbf{H}\langle\mathbf{\Omega}
       \rangle$ for invertible $\mathbf{M}$. More generally it depends only on
       $\operatorname{range}\mathbf{\Omega}$;
     - TW Lemma 5.2, "Nyström helps": $\|\mathbf{H}-\mathbf{H}\langle\mathbf{\Omega}\rangle\|_\Phi
       \le\|\mathbf{H}-\mathbf{P}_{\mathbf{\Omega}}\mathbf{H}\|_\Phi$;
     - the selection case of `Factorizations/Nystrom.lean` as the instance
       $\mathbf{\Omega} = $ `selectionMatrix e`.
4. **Schur-complement order facts (S0; EW Fact 6.1).**
   - $\mathbf{H}\mapsto\mathbf{H}/\mathbf{\Omega}$ is monotone and concave in the Loewner order,
     including for finite convex combinations (Fact 6.1(c)), which S4's group average uses.
   - The route is the variational form
     $\langle\mathbf{x},(\mathbf{H}/\mathbf{\Omega})\mathbf{x}\rangle =
     \min_{\mathbf{y}}\langle\mathbf{x}-\mathbf{\Omega}\mathbf{y},
     \mathbf{H}(\mathbf{x}-\mathbf{\Omega}\mathbf{y})\rangle$, a minimum of affine functions of
     $\mathbf{H}$. `isLeast_re_quadForm_fromBlocks` looks like this form already; the S0 note's
     duplicate search starts there (review A13e).
   - MT Corollary 11.2 is the monotonicity, and EW §6.3 uses both.
   - Loewner antitonicity of the inverse, $(\mathbf{X}+c\mathbf{Y})^{-1}\preceq\mathbf{X}^{-1}$ for
     $\mathbf{X}\succ\mathbf{0}$, $\mathbf{Y}\succeq\mathbf{0}$, $c\ge 0$, if the library lacks it
     (S4's pointwise step).
5. **Gauge equality (S0).** $\|\mathbf{X}\mathbf{X}^{\mathsf{H}}\|_\Phi =
   \|\mathbf{X}^{\mathsf{H}}\mathbf{X}\|_\Phi$, for item 6.

   (EW Lemma 5.8, "weighting hurts", was item 5 of the draft. Its only consumer is the
   sketch-and-solve lower bound, so it moves to S10; review A5.)
6. **The structural bound of the range finder (S1).** One general statement: for any frame
   $\mathbf{Z}\in\mathbb{K}^{n\times k}$ with $\mathbf{Z}^{\mathsf{H}}\mathbf{Z} = \mathbf{I}$ and
   $\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega}$ of full row rank, put
   $$\mathbf{E} = \mathbf{A}(\mathbf{I}-\mathbf{Z}\mathbf{Z}^{\mathsf{H}}),\qquad
   \mathbf{M} = \mathbf{E}\mathbf{\Omega}(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^{+},\qquad
   \mathbf{C} = \mathbf{A}\mathbf{\Omega}(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^{+}
   \mathbf{Z}^{\mathsf{H}}.$$
   Then:
   - $\mathbf{C}$ has rank at most $k$ and range inside $\operatorname{range}\mathbf{Y}$;
   - $\mathbf{A}-\mathbf{C} = \mathbf{E} - \mathbf{M}\mathbf{Z}^{\mathsf{H}}$;
   - $(\mathbf{A}-\mathbf{C})(\mathbf{A}-\mathbf{C})^{\mathsf{H}} = \mathbf{E}\mathbf{E}^{\mathsf{H}}
     + \mathbf{M}\mathbf{M}^{\mathsf{H}}$, because $\mathbf{E}\mathbf{Z} = \mathbf{0}$.

   Two conclusions, for every gauge $\Phi$:
   - **Gram form** (every quadratic unitarily invariant norm), with the contraction
     $\mathbf{I}-\mathbf{P}_{\mathbf{Y}}$ and item 5:
     $$\bigl\|\bigl((\mathbf{I}-\mathbf{P}_{\mathbf{Y}})\mathbf{A}\bigr)^{\mathsf{H}}
     (\mathbf{I}-\mathbf{P}_{\mathbf{Y}})\mathbf{A}\bigr\|_\Phi \le
     \|\mathbf{E}^{\mathsf{H}}\mathbf{E}\|_\Phi + \|\mathbf{M}^{\mathsf{H}}\mathbf{M}\|_\Phi.$$
   - **Unsquared triangle form** (every unitarily invariant norm; review A2). Since
     $(\mathbf{I}-\mathbf{P}_{\mathbf{Y}})\mathbf{C} = \mathbf{0}$,
     $(\mathbf{I}-\mathbf{P}_{\mathbf{Y}})\mathbf{A} = (\mathbf{I}-\mathbf{P}_{\mathbf{Y}})
     (\mathbf{E}-\mathbf{M}\mathbf{Z}^{\mathsf{H}})$. Hence
     $\|(\mathbf{I}-\mathbf{P}_{\mathbf{Y}})\mathbf{A}\|_\Phi \le \|\mathbf{E}\|_\Phi +
     \|\mathbf{M}\|_\Phi$, by `matrixNorm_mul_le_of_isStarProjection` and
     `matrixNorm_mul_conjTranspose_right_of_hasOrthonormalCols`.

   About the statement:
   - HMT Theorem 9.1 is the instance where $\mathbf{Z}$ spans the top $k$ right singular
     vectors, so that $\mathbf{E} = \mathbf{A}-\llbracket\mathbf{A}\rrbracket_k$, in spectral and
     Frobenius norm. So are MT Theorem 11.4 (and its remark on quadratic norms), TW Proposition
     8.5 (8.2), Woodruff Lemma 48 (literally the general-$\mathbf{Z}$ form in Frobenius, p. 69) and
     CEMT Imported Theorem 2.3.
   - The general-$\mathbf{Z}$ form is the competitor argument of Woodruff Lemmas 45 and 48. It
     needs no invertible $\mathbf{\Sigma}_1$, no diagonal blocks, and no HMT Propositions 8.2
     and 8.3.
   - Full row rank of $\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega}$ is
     `IsSubspaceInjection (Ωᴴ) Z a` with `0 < a`, or the raw `Function.Injective (Ωᴴ * Z).mulVec`.
   - **Truncation for free:** the competitor $\mathbf{C}$ has rank at most $k$ and range inside
     $\operatorname{range}\mathbf{Y}$, so by `ProjectedLowRank` the Frobenius bound holds for
     $\mathbf{Q}\llbracket\mathbf{Q}^{\mathsf{H}}\mathbf{A}\rrbracket_k$ too. This is Woodruff
     Lemma 48's middle term, and the reason the fixed-rank RSVD inherits HMT's constant exactly.
   - **Tail flattening** (assessment A3; prototype `sq_le_four_div_mul_sum_Ico_sq`):
     $\sigma_{j+1}^2\le(j-k)^{-1}\sum_{k<i\le j}\sigma_i^2$. With the structural bound split at
     $j = \lceil\ell/2\rceil$ instead of $k$, it gives the spectral second moment of the range
     residual against the Frobenius tail that truncated GN needs (§4.3).
7. **Late-truncation lemmas (S2a).** Below, "a best rank-$k$ approximation" means the D5
   hypothesis, so that every lemma holds for `truncatedSVD` and for any other choice.
   1. **Constant 1 under singular-value domination** (review A6). If
      $\sigma_i(\hat{\mathbf{A}})\le\sigma_i(\mathbf{A})$ for all $i$, then for every gauge
      $$\|\mathbf{A}-\llbracket\hat{\mathbf{A}}\rrbracket_k\|_\Phi \le
      \|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k\|_\Phi + \|\mathbf{A}-\hat{\mathbf{A}}\|_\Phi.$$
      The proof is the triangle inequality, then the tails by `matrixNorm_le_of_singularValues_le`.
      The hypothesis holds in two cases:
      - for $\hat{\mathbf{A}} = \mathbf{P}\mathbf{A}$ (`IsStarProjection.singularValues_mul_le`).
        In spectral norm this is HMT Theorem 9.3 (p. 54);
      - for Nyström, $\mathbf{0}\preceq\hat{\mathbf{H}}\preceq\mathbf{H}$, by Weyl monotonicity
        (`eigenvalue_le_eigenvalue_of_le`).

      One lemma, `matrixNorm_sub_truncatedSVD_le_add_of_singularValues_le`, with the two
      instances.
   2. **Generic, constant 2.** For any $\hat{\mathbf{A}}$ and every gauge,
      $\|\mathbf{A}-\llbracket\hat{\mathbf{A}}\rrbracket_k\|_\Phi \le
      \|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k\|_\Phi + 2\|\mathbf{A}-\hat{\mathbf{A}}\|_\Phi$.
      This is the triangle inequality and Eckart–Young for $\hat{\mathbf{A}}$
      (`matrixNorm_sub_truncatedSVD_le_of_rank_le`). It is needed for GN, since an oblique
      projection does not dominate singular values. Attributed to TYUC SIMAX; the number is to be
      confirmed (§9.2).
   3. **Frobenius-squared forms**, sharper than the squared triangle:
      - projections: $\|\mathbf{A}-\llbracket\mathbf{P}\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2 \le
        \|(\mathbf{I}-\mathbf{P})\mathbf{A}\|_{\mathsf{F}}^2 + \|\mathbf{A}-\llbracket\mathbf{A}
        \rrbracket_k\|_{\mathsf{F}}^2$, by Pythagoras (Woodruff Lemma 44);
      - item 6's rank-$k$ competitor (Woodruff Lemma 48);
      - the choice-free identities of D5.
   4. **Perturbed truncation** (assessment A3(i); new, §9.3). For any $\mathbf{C}$,
      $\mathbf{E}$, any best rank-$k$ approximation $\mathbf{Y}'$ of $\mathbf{C}+\mathbf{E}$, and any
      $e$ such that $\operatorname{Re}\langle\mathbf{Z},\mathbf{E}\rangle\le\sqrt{2k}\,
      \|\mathbf{Z}\|_{\mathsf{F}}\,e$ for every $\mathbf{Z}$ of rank at most $2k$:
      $$\|\mathbf{C}-\mathbf{Y}'\|_{\mathsf{F}} \le \|\mathbf{C}-\llbracket\mathbf{C}\rrbracket_k
      \|_{\mathsf{F}} + 2\sqrt{2k}\,e.$$
      - The corollary at $e = \|\mathbf{E}\|_2$ uses von Neumann's trace inequality and
        Cauchy–Schwarz.
      - The proof uses the optimality of $\mathbf{Y}'$, then pairs the rank-$\le 2k$ matrix
        $\mathbf{Y}'-\llbracket\mathbf{C}\rrbracket_k$ with $\mathbf{E}$, then takes the right root
        of a quadratic. Only $\|\mathbf{E}\|_2$ enters.
      - It is incomparable with item 7.2 (D10). It is the step that turns truncated GN's
        $\varepsilon^{-3}$ into $\varepsilon^{-2}$.
      - The hypothesis form is the formalization's `RankTraceBound`. The S2a note decides whether
        that is a named interface (§5.4) or only the corollary's internal step.
   5. **Truncation under the correspondence** (trace). With $\mathbf{C}$ a best rank-$k$
      approximation of $\mathbf{P}\mathbf{F}$, $\mathbf{H} - \mathbf{C}^{\mathsf{H}}\mathbf{C} =
      (\mathbf{F}-\mathbf{C})^{\mathsf{H}}(\mathbf{F}-\mathbf{C})$ (since
      $\mathbf{C} = \mathbf{P}\mathbf{C}$), and $\mathbf{C}^{\mathsf{H}}\mathbf{C}$ is a best
      rank-$k$ approximation of $\hat{\mathbf{H}}$. Hence
      $\operatorname{tr}(\mathbf{H}-\llbracket\hat{\mathbf{H}}\rrbracket_k) =
      \|\mathbf{F}-\llbracket\mathbf{P}\mathbf{F}\rrbracket_k\|_{\mathsf{F}}^2$. This is
      choice-free, because both sides are tail sums. Truncated Nyström in trace norm is truncated
      RSVD of $\mathbf{F}$ in Frobenius norm squared.
   6. **The factored form** (D5): $\mathbf{Q}^{\mathsf{H}}\,$`truncatedSVD (Q * X) k` is a best
      rank-$k$ approximation of $\mathbf{X}$, and `truncatedSVD (Q * X) k` is $\mathbf{Q}$ times
      it.
   7. **GN core truncation** (Woodruff Theorem 47's rank-$k$ clause), only after the dimension
      check of D15.
   8. **Gu 2015's gapped "reverse Eckart–Young"** (Theorem 3.4, cited by TW p. 42) waits for the
      paper. Its form may be the spectral twin of "truncation for free",
      $\|\mathbf{A}-\mathbf{Q}\llbracket\mathbf{Q}^{\mathsf{H}}\mathbf{A}\rrbracket_k\|_2^2\le
      \sigma_{k+1}^2+\|\mathbf{\Sigma}_2\mathbf{\Omega}_2\mathbf{\Omega}_1^{+}\|_2^2$.
8. **The early-truncation core (S2b; assessment A3(ii); new, §9.3).** Notation:
   - $\mathbf{A} = \mathbf{A}_1+\mathbf{A}_2$ with $\mathbf{A}_1 = \mathbf{A}\mathbf{V}_1
     \mathbf{V}_1^{\mathsf{H}}$, where $\mathbf{V}_1$ spans the top $k$ right singular vectors,
     and $\mathrm{OPT} = \|\mathbf{A}_2\|_{\mathsf{F}}$;
   - $\mathbf{S}$ is the (scaled) test matrix;
   - $\hat{\mathbf{P}}$ is a rank-$\le k$ orthogonal projector at least as good on the sketch as
     the competitor $\mathbf{P}_1 = \mathbf{P}_{\mathbf{A}_1}$:
     $\|(\mathbf{I}-\hat{\mathbf{P}})\mathbf{A}\mathbf{S}\|_{\mathsf{F}}\le
     \|(\mathbf{I}-\mathbf{P}_1)\mathbf{A}\mathbf{S}\|_{\mathsf{F}}$. The projector onto
     $\operatorname{range}\llbracket\mathbf{A}\mathbf{S}\rrbracket_k$ qualifies by Eckart–Young;
   - $\lambda$ is any real with $\lambda\|\mathbf{z}\|^2\le\langle\mathbf{z},
     \mathbf{V}_1^{\mathsf{H}}\mathbf{S}\mathbf{S}^{\mathsf{H}}\mathbf{V}_1\mathbf{z}\rangle$
     (a head subspace-embedding lower bound);
   - $w = \|\mathbf{A}_2\mathbf{S}\mathbf{S}^{\mathsf{H}}\mathbf{A}_2^{\mathsf{H}}-\mathbf{A}_2
     \mathbf{A}_2^{\mathsf{H}}\|_{\mathsf{F}}$ (tail–tail AMM error) and
     $\chi = \|\mathbf{A}_2\mathbf{S}\mathbf{S}^{\mathsf{H}}\mathbf{V}_1\|_{\mathsf{F}}$
     (tail–head AMM error);
   - $r_i = \|(\mathbf{I}-\hat{\mathbf{P}})\mathbf{A}_i\|_{\mathsf{F}}$.

   Then:
   $$\lambda r_1^2 + r_2^2 \le \mathrm{OPT}^2 + \sqrt{k}\,w + 2\chi r_1,\qquad
   \|\mathbf{A}-\hat{\mathbf{P}}\mathbf{A}\|_{\mathsf{F}}^2 = r_1^2 + r_2^2.$$
   The almost-sure corollary, with $\bar\lambda = \min\{1,\lambda\} > 0$ and $\theta\in(0,1)$:
   $\|\mathbf{A}-\hat{\mathbf{P}}\mathbf{A}\|_{\mathsf{F}}^2 \le
   (\mathrm{OPT}^2+\sqrt{k}\,w)/((1-\theta)\bar\lambda) + \chi^2/(\theta(1-\theta)\bar\lambda^2)$.
   - The proof expands the sketch-optimality inequality into head, tail and cross terms. The tail
     term's $\|\mathbf{A}_2\mathbf{S}\|_{\mathsf{F}}^2 - \mathrm{OPT}^2$ appears on both sides and
     cancels.
   - That cancellation deletes the Frobenius-preservation condition of the PCP sufficient
     conditions. The inequality needs the sketch conditions at *two* projectors, not uniformly,
     and only the lower side of the head embedding. It is therefore strictly sharper than the
     uniform PCP route.
   - It is the largest deterministic item of the round: about 450 lines in the formalization.
9. **The PCP predicate and its consequence (S2b; §5.4).**

### 4.2 What transfers through the Gram correspondence, and with which constant

Let $\mathbf{H} = \mathbf{F}^{\mathsf{H}}\mathbf{F}$ and $\mathbf{E}_{\mathrm{RF}} =
(\mathbf{I}-\mathbf{P}_{\mathbf{F}\mathbf{\Omega}})\mathbf{F}$. Then
$\mathbf{H}-\mathbf{H}\langle\mathbf{\Omega}\rangle = \mathbf{E}_{\mathrm{RF}}^{\mathsf{H}}
\mathbf{E}_{\mathrm{RF}}$, so $\sigma_i(\mathbf{H}-\mathbf{H}\langle\mathbf{\Omega}\rangle) =
\sigma_i(\mathbf{E}_{\mathrm{RF}})^2$. Likewise
$\sigma_i(\mathbf{H}-\llbracket\mathbf{H}\rrbracket_k) = \sigma_i(\mathbf{F}-\llbracket\mathbf{F}
\rrbracket_k)^2$. Checked against TW pp. 37–38: $\|\mathbf{H}-\mathbf{H}\langle\mathbf{\Omega}
\rangle\|_{S_p} = \|\mathbf{E}_{\mathrm{RF}}\|_{S_{2p}}^2$. Every norm of the Nyström error is
thus a quadratic norm of $\mathbf{E}_{\mathrm{RF}}$; the transfer is an equality of matrices.

| Nyström error in | equals, for the range finder on $\mathbf{F}$ | transfers with the same constant? |
|---|---|---|
| trace (nuclear) | $\|\mathbf{E}_{\mathrm{RF}}\|_{\mathsf{F}}^2$; best error $\operatorname{tr}(\mathbf{H}-\llbracket\mathbf{H}\rrbracket_k) = \|\mathbf{F}-\llbracket\mathbf{F}\rrbracket_k\|_{\mathsf{F}}^2$ | **Yes, everything:** deterministic; expectation (HMT 10.5 gives $\mathbb{E}\operatorname{tr} \le (1+\frac{k}{\ell-k-1})\operatorname{tr}(\mathbf{H}-\llbracket\mathbf{H}\rrbracket_k)$, TW Corollary 8.8); tails; OSI (CEMT Corollary 2.5 from Theorem 2.2); EW Theorem 3.6(a) from 3.2; truncation (§4.1 item 7.5) |
| spectral | $\|\mathbf{E}_{\mathrm{RF}}\|_2^2$; best error $\lambda_{k+1}(\mathbf{H}) = \sigma_{k+1}(\mathbf{F})^2$ | **Deterministic and tail bounds: yes**, by squaring the event. **Expectations: only from second-moment statements.** $\mathbb{E}\|\mathbf{E}_{\mathrm{RF}}\|_2^2$ is needed, and HMT 10.6 bounds the first moment, which does not give it. The Gram-form route (§4.3) gives the second moment directly, and from it TW Corollary 8.2 (NysSVD2) |
| Frobenius | $\|\mathbf{E}_{\mathrm{RF}}\|_{S_4}^2$ (not $\|\mathbf{E}_{\mathrm{RF}}\|_{\mathsf{F}}^2$) | **Only through the Gram form.** No source bounds the range finder in $S_4$ except TW Theorem 8.7's Schatten-4 and fourth-moment bounds. The structural bound (§4.1 item 6) transfers with equal constant; the expectation goes through the §4.3 route |
| any unitarily invariant $\Phi$ | $\Phi(\sigma(\mathbf{E}_{\mathrm{RF}})^2) = \|\mathbf{E}_{\mathrm{RF}}^{\mathsf{H}}\mathbf{E}_{\mathrm{RF}}\|_\Phi$ | **Yes**, for every statement made in the Gram form (D4). That is the reason for D4 |

So the policy is: state range-finder results in the Gram form, and Nyström follows with equal
constants in every norm: deterministic, expectation and tail. The unsquared statements (HMT
10.6's first moment and the triangle form of item 6) are the ones with no Nyström twin.

### 4.3 The probabilistic layer, by family

**Gaussian test matrices (real; S3, S5, S6).**
- **The range finder.** With $\mathbf{Z}$ the top $k$ right singular vectors,
  $\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega}$ and $\mathbf{E}\mathbf{\Omega}$ are independent
  Gaussians (R1). R4 then gives $\mathbb{E}\|\mathbf{M}\|_{\mathsf{F}}^2 =
  \frac{k}{\ell-k-1}\|\mathbf{E}\|_{\mathsf{F}}^2$. Its lemma needs $\mathbf{Z}_\perp$ to span the
  whole complement ($\operatorname{card} s + k = n$), so that $\mathbf{E} =
  \mathbf{A}\mathbf{Z}_\perp\mathbf{Z}_\perp^{\mathsf{H}}$. With §4.1 item 6 and
  $\|\mathbf{M}^{\mathsf{H}}\mathbf{M}\|_\Phi \le
  \Phi(\mathbf{e}_1)\|\mathbf{M}\|_{\mathsf{F}}^2$ (`matrixNorm_le_apply_single_mul_nuclearNorm`):
  $$\mathbb{E}\bigl\|\mathbf{E}_{\mathrm{RF}}^{\mathsf{H}}\mathbf{E}_{\mathrm{RF}}\bigr\|_\Phi \le
  \bigl\|(\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k)^{\mathsf{H}}
  (\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k)\bigr\|_\Phi + \Phi(\mathbf{e}_1)\,\frac{k}{\ell-k-1}\,
  \|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2.$$
  - One theorem gives HMT 10.5 (nuclear gauge), TW Theorem 8.1 (RSVD2) for all
    $2\le p\le\infty$ (checked against TW p. 33), the squared spectral error, and, through §4.2,
    every Nyström bound of TW Corollaries 8.2 and 8.8.
  - Beside it:
    - HMT 10.6, the first moment, from the existing block bound and the triangle form;
    - **the tails.** TW Theorem 8.1 (RSVD1), p. 33, is primary. In this brief's letters, for every
      $\ell\ge k$, every $p\in[2,\infty]$ and $u, t$:
      $$\|\mathbf{A}-\mathbf{P}_{\mathbf{Y}}\mathbf{A}\|_{S_p}^2\le
      \|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k\|_{S_p}^2 + \frac{u\,t\,k}{\ell-k+1}
      \|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2,$$
      with failure probability $e^{-(u-2)/4} + \sqrt{\pi k}\,(t/e)^{-(\ell-k+1)/2}$. Its proof is
      the Gram form plus a chi-square-type tail on $\|\mathbf{E}\mathbf{\Omega}\|_{\mathsf{F}}$
      conditional on $\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega}$, and an HMT 10.4-type tail on
      $\|(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^{+}\|$. It transfers to Nyström (NysSVD1) with
      no extra work. HMT 10.7 and 10.8 (R1's Lipschitz concentration plus R4's moments) sit beside
      it as rule-4 neighbours or follow as corollaries; the S3 note decides which. Constants not
      reached are named per §5.2;
    - optionally, TW Theorem 8.7 and Corollary 8.8's finite bounds at $\ell = k+1$ and
      $\ell = k$, where HMT's diverge (one line in the S3 note);
    - the truncated RSVD in Frobenius with HMT's constant (item 6);
    - the a.s. exact recovery when $\operatorname{rank}\mathbf{A}\le\ell$.
- **Nyström (S5).** Everything above transfers by §4.2. For truncated Nyström, S5 promises only
  what S2a proves (review A1):
  - trace: $\mathbb{E}\operatorname{tr}(\mathbf{H}-\llbracket\hat{\mathbf{H}}\rrbracket_k)\le
    (1+\frac{k}{\ell-k-1})\operatorname{tr}(\mathbf{H}-\llbracket\mathbf{H}\rrbracket_k)$, by item
    7.5 and the rank-$k$ competitor;
  - spectral: $\mathbb{E}\|\mathbf{H}-\llbracket\hat{\mathbf{H}}\rrbracket_k\|_2\le
    2\lambda_{k+1} + \frac{k}{\ell-k-1}\sum_{j>k}\lambda_j$, by item 7.1 and the Gram-form second
    moment;
  - MT Theorem 14.1 (p. 496) is a *spectral* statement with one $\lambda_{k+1}$:
    $\mathbb{E}\|\mathbf{H}-\llbracket\hat{\mathbf{H}}\rrbracket_k\|_2\le\lambda_{k+1} +
    \frac{k}{\ell-k-1}\sum_{j>k}\lambda_j$, credited to TYUC NeurIPS Theorem 4.1. This brief's
    route does not reach it. No promise is made until TYUC NeurIPS is read. If its argument is
    found, it is a sharper S2a lemma, not an S5 change.
- **GN with $\mathbf{\Psi}$ Gaussian, independent of $\mathbf{\Omega}$ (S6).** The GN
  "identity" with $\ell' = \operatorname{rank}\mathbf{Y}$ outside the expectation is not a
  statement, since $\ell'$ depends on $\omega$ (review A3). Two honest shapes:
  - **(a) Fixed $\mathbf{X}$.** For fixed $\mathbf{X}$ with $q = \operatorname{rank}\mathbf{X}$
    and $q+2\le p$:
    $\mathbb{E}\|\mathbf{B}-\mathbf{\Pi}_{\mathbf{X},\mathbf{\Psi}}\mathbf{B}\|_{\mathsf{F}}^2 =
    (1+\frac{q}{p-q-1})\|(\mathbf{I}-\mathbf{P}_{\mathbf{X}})\mathbf{B}\|_{\mathsf{F}}^2$.
    - The proof: item 2, then `integral_frobNorm_pinv_mul_mul_sq_of_hasLaw_gaussianMatrix` with
      $\mathbf{V}_1 = \mathbf{Q}$, $\mathbf{V}_2 = \mathbf{Q}_\perp$ and
      $\mathbf{S} = \mathbf{Q}_\perp^{\mathsf{H}}\mathbf{B}$, through the single-view bridge
      (the basis has a `Fin q` index, which §5.1 permits where the index carries content).
    - It covers GN conditionally on $\mathbf{\Omega}$, sketch-and-solve
      ($\mathbf{X} = \mathbf{A}$), and early-truncated GN
      ($\mathbf{X} = \llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k$, $q\le k$).
    - Integrated over $\mathbf{\Omega}$, the rank stays inside the expectation.
  - **(b) Unconditional.** With $\ell' := \min(\operatorname{rank}\mathbf{A},\ell)$, which is
    deterministic and equals $\operatorname{rank}(\mathbf{A}\mathbf{\Omega})$ a.s. (R1):
    $\mathbb{E}\|\mathbf{A}-\mathbf{A}\langle\mathbf{\Omega},\mathbf{\Psi}\rangle\|_{\mathsf{F}}^2 =
    (1+\frac{\ell'}{p-\ell'-1})\,\mathbb{E}\|(\mathbf{I}-\mathbf{P}_{\mathbf{Y}})\mathbf{A}
    \|_{\mathsf{F}}^2$. The common case $\ell\le\operatorname{rank}\mathbf{A}$ is the first line of
    EW Theorem 4.2(a), with $\gamma = 1$. TYUC Theorem 4.3 is the bound form.
- **Truncated GN in expectation (S6; assessment A5; new, §9.3).** Here $\hat{\mathbf{X}} =
  \mathbf{Q}^{\mathsf{H}}\mathbf{A}+\mathbf{N}$ (item 2's core noise), and $\mathbf{A}_\perp =
  (\mathbf{I}-\mathbf{Q}\mathbf{Q}^{\mathsf{H}})\mathbf{A}$.
  - The core-form split gives $\|\mathbf{A}-\mathbf{Q}\llbracket\hat{\mathbf{X}}\rrbracket_k\|
    _{\mathsf{F}}^2 = \|\mathbf{A}_\perp\|_{\mathsf{F}}^2 + \|\mathbf{Q}^{\mathsf{H}}\mathbf{A} -
    \llbracket\hat{\mathbf{X}}\rrbracket_k\|_{\mathsf{F}}^2$. Item 7.4 bounds the second term.
  - Three Gaussian inputs:
    - **spectral core noise:** for fixed orthonormal $\mathbf{Q}$ with $\ell$ columns and
      $p\ge 4\ell$, $\mathbb{E}_{\mathbf{\Psi}}\|\mathbf{N}\|_2^2\le\frac{18}{p}\|\mathbf{A}_\perp
      \|_{\mathsf{F}}^2+\frac{4\ell}{p}\|\mathbf{A}_\perp\|_2^2$. It follows from TW Lemma B.1
      (spectral half) and R4's spectral $\mathbb{E}\|\mathbf{G}^{+}\|_2^2$;
    - **spectral residual:** for $\operatorname{rank}\mathbf{A}\ge\ell\ge 4k$,
      $\mathbb{E}\|\mathbf{A}_\perp\|_2^2\le\frac{102}{\ell}\mathrm{OPT}^2$. It follows from the
      spectral structural bound split at $\lceil\ell/2\rceil$, the tail flattening, and R4;
    - **the baseline:** $\|\mathbf{Q}^{\mathsf{H}}\mathbf{A}-\llbracket\mathbf{Q}^{\mathsf{H}}
      \mathbf{A}\rrbracket_k\|_{\mathsf{F}}\le\mathrm{OPT}$ pointwise, and
      $\mathbb{E}(\|\mathbf{A}_\perp\|_{\mathsf{F}}^2+\gamma^2)\le(1+\frac{k}{\ell-k-1})
      \mathrm{OPT}^2$ (item 6, truncation for free).
  - Closed form (§5.2 rule 2), with $\ell\ge 4k+2$, $p\ge 4\ell$ and
    $\operatorname{rank}\mathbf{A}\ge\ell$, where $c = (18(1+\frac{k}{\ell-k-1})+408)/p$:
    $$\mathbb{E}\|\mathbf{A}-\llbracket\mathbf{A}\langle\mathbf{\Omega},\mathbf{\Psi}\rangle
    \rrbracket_k\|_{\mathsf{F}}^2\le\Bigl(1+\frac{k}{\ell-k-1}+4\sqrt{2kc}+8kc\Bigr)\mathrm{OPT}^2
    =: \texttt{truncatedGNFactor}\;k\;\ell\;p\cdot\mathrm{OPT}^2.$$
    The $(1+\varepsilon)$ sample-size form ($\ell = O(k/\varepsilon)$,
    $p = O(k/\varepsilon^2)$) is a corollary, with whatever constant the arithmetic gives. The
    manuscript's 12500 is a by-product of its rounding.
  - The branch $\operatorname{rank}\mathbf{A} < \ell$ is exact a.s.
  - The atlas candidate `tgn-expected-error` gets a proof.
- **Sketch-and-solve (S6).** EW Theorem 2.1 (Gaussian):
  $\mathbb{E}\|\mathbf{B}-\mathbf{A}\hat{\mathbf{X}}\|_{\mathsf{F}}^2 = (1+\frac{r}{p-r-1})\min$,
  with $r = \operatorname{rank}\mathbf{A}$ and $r+2\le p$. It is shape (a) at
  $\mathbf{X} = \mathbf{A}$, with unbiasedness $\mathbb{E}\hat{\mathbf{X}} =
  \mathbf{A}^{+}\mathbf{B}$.

**Haar and rotation-invariant test matrices (real; S3, S4, S6).**
- Every range-finder and Nyström statement depends on $\mathbf{\Omega}$ only through
  $\operatorname{range}\mathbf{\Omega}$ (item 3) or $\operatorname{range}(\mathbf{A}\mathbf{\Omega})$.
  R5's transfer therefore gives the Haar case for free, and the characterization gives it for any
  full-rank left-invariant law, whose polar factor is Haar.
- **EW Theorems 3.2 and 3.6(a) (S4)**, for rank $r\ge\ell$:
  $$\mathbb{E}\|\mathbf{A}-\mathbf{P}_{\mathbf{Y}}\mathbf{A}\|_{\mathsf{F}}^2 \le
  \min_{q\le\ell-2}\frac{r-\ell}{r-q}\Bigl(1+\frac{q}{\ell-q-1}\Bigr)
  \|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_q\|_{\mathsf{F}}^2.$$
  It is proved for Nyström (trace) and transferred by §4.2. EW's proof simplifies for the upper
  bounds (review A4):
  - **(i) No limit.** For every $a>b$, Lemma 6.2's computation and Loewner antitonicity of the
    inverse give the pointwise inequality
    $\operatorname{tr}(\mathbf{H}_{a,b}-\mathbf{H}_{a,b}\langle\mathbf{\Omega}\rangle)\le
    b\operatorname{tr}((\mathbf{R}_1\mathbf{R}_1^{*})^{-1})+b(r-\ell-q)$ at finite $a$. Monotone
    convergence is needed only for the lower bound (S10).
  - **(ii) A finite group average, not random permutations.** The symmetrisation
    $\mathbb{E}\operatorname{tr}(\mathbf{\Lambda}/\mathbf{\Omega}) =
    \mathbb{E}\operatorname{tr}((\mathbf{P}^{\mathsf{T}}\mathbf{\Lambda}\mathbf{P})/\mathbf{\Omega})$
    holds for each *fixed* block permutation $\mathbf{P}$
    (`hasLaw_const_mul_of_isLeftUnitarilyInvariant`). Averaging over the finite group is a convex
    combination, and Fact 6.1(c) applies directly. There is no product space and no conditional
    expectation.
  - **(iii) Trace only.** Proposition 5.7 (at $\mathbf{R} = \mathbf{I}$) and Lemma 6.2 use only
    $\mathbb{E}\operatorname{tr}((\mathbf{\Omega}_1\mathbf{\Omega}_1^{*})^{-1}) =
    r(1+\frac{n-\ell}{\ell-r-1})$, never the matrix $\mathbb{E}\mathbf{X}^{-1}$. The proof:
    $\operatorname{tr}\mathbf{X}^{-1} = r+\operatorname{tr}(\mathbf{W}_1^{-1}\mathbf{W}_2)$, with
    $\mathbf{W}_1 = \mathbf{G}_1\mathbf{G}_1^{\mathsf{H}}$ and $\mathbf{W}_2 =
    \mathbf{G}_3\mathbf{G}_3^{\mathsf{H}}$ independent (R1), $\mathbb{E}\mathbf{W}_1^{-1} =
    (\ell-r-1)^{-1}\mathbf{I}$ (R4), and $\mathbb{E}\mathbf{W}_2 = (n-\ell)\mathbf{I}$ (R2). No
    Beta-matrix law is needed.
  - **(iv) Needed: the coupled conjugation-average lemma.** Proposition 5.7 needs
    $\mathbb{E}[\mathbf{\Omega}_2\mathbf{Y}\mathbf{\Omega}_2^{\mathsf{H}}] =
    \frac{\mathbb{E}\operatorname{tr}(\mathbf{\Omega}_2\mathbf{Y}\mathbf{\Omega}_2^{\mathsf{H}})}
    {n-r}\mathbf{I}$, with $\mathbf{Y}$ a function of $\mathbf{\Omega}_1$, so the two are dependent.
    The existing `integral_mul_mul_conjTranspose_of_isLeftUnitarilyInvariant` is for a fixed
    middle factor. The route has two parts:
    - a Matrix-layer lemma: the average of $\mathbf{S}\mathbf{M}\mathbf{S}^{\mathsf{H}}$ over the
      finite group of signed permutations is $(\operatorname{tr}\mathbf{M}/m)\,\mathbf{I}$. Sign
      flips kill the off-diagonal entries and permutations equalise the diagonal. Check
      `eq_smul_one_of_forall_mul_mul_conjTranspose_eq` first;
    - the law invariance $(\mathbf{\Omega}_1,\mathbf{S}\mathbf{\Omega}_2)\sim
      (\mathbf{\Omega}_1,\mathbf{\Omega}_2)$ for the block-diagonal unitary
      $\operatorname{diag}(\mathbf{1},\mathbf{S})$.

    The same Matrix-layer lemma serves (ii).
  - **(v) Needed: the Haar block laws.** These are in RandomMatrix:
    - (a) the $n\times\ell$ Haar frame is the law of a column block of the $n\times n$ Haar
      unitary, by the characterization (left-invariant with orthonormal columns);
    - (b) the $r\times n$ row block of the Haar unitary is `haarFrame r n` after `conjTranspose`,
      since right invariance of $\mathbf{U}$ gives left invariance of the block's adjoint, then the
      characterization and `hasLaw_conjTranspose_of_hasLaw_haarFrame` apply;
    - (c) the polar factor of a wide full-row-rank $\mathbf{G}$ is
      $(\mathbf{G}\mathbf{G}^{\mathsf{H}})^{-1/2}\mathbf{G}$, in the Matrix layer (check
      `PolarFrames.lean` first).

    Then $\mathbf{\Omega}_1\mathbf{\Omega}_1^{\mathsf{H}} = \mathbf{W}^{-1/2}\mathbf{W}_1
    \mathbf{W}^{-1/2}$ is algebra. After (i) to (iv), the uncertainty of S4 sits here.
- **Haar $\mathbf{\Psi}$ in GN and in sketch-and-solve (S6).** EW Proposition 5.7 at
  $\mathbf{R} = \mathbf{I}$ (an equality, needing no Lemma 5.8) makes both shapes of the GN step
  *identities* for Haar $\mathbf{\Psi}$ too (review A3). For fixed $\mathbf{X}$ of rank $q$ in
  ambient dimension $m$, with sketch size $p$, the factor is
  $1+\frac{m-p}{m-q}\cdot\frac{q}{p-q-1}$. Hence EW Theorem 4.2(a) with
  $\gamma = \frac{m-p}{m-\ell}$, and EW Theorem 2.1's random orthonormal case
  ($1+\frac{m-p}{m-r}\cdot\frac{r}{p-r-1}$). The "$\le$" of Theorem 4.2(a) enters only through
  Theorem 3.2's minimum over $q$. This half of S6 depends on S4's row-block law.

**Oblivious subspace injections and embeddings (over `𝕜`; S7).** Every family of the Sketching
round enters here: Gaussian, Haar, sub-Gaussian, Rademacher, SRHT in both models, CountSketch,
and row sampling for fixed $\mathbf{U}$. The per-family orientation lemmas carry the scaling of
D2.
- **RSVD (CEMT Theorem 2.2).** Item 6 plus Sketching S1's tail for the injection on
  $\operatorname{range}\mathbf{Z}$ gives
  $$\|(\mathbf{I}-\mathbf{P}_{\mathbf{Y}})\mathbf{A}\|_{\mathsf{F}}^2 \le (1+t/a)
  \|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
  outside $\delta + 1/t$, and with it the truncated RSVD. By §4.2 the Nyström trace form follows
  (CEMT Corollary 2.5).
- **GN (CEMT Corollary 2.8).** $\mathbf{\Psi}^{\mathsf{H}}$ is an OSI of dimension $\ell$,
  independent of $\mathbf{\Omega}$. The Sketching transfer applies to the random
  $\operatorname{range}\mathbf{Y}$, and item 2 combines the two failure events. Truncated versions
  follow by S2a (items 7.2 and 7.4).
- **Relative error (Woodruff Lemma 45, Theorem 47).** An injection on
  $\operatorname{range}\mathbf{Z}$ plus AMM for the pair $(\mathbf{Z},\mathbf{E}^{\mathsf{H}})$
  bounds $\|\mathbf{M}\|_{\mathsf{F}}$:
  $\mathbf{M} = \mathbf{E}(\mathbf{\Omega}\mathbf{\Omega}^{\mathsf{H}}-\mathbf{I})\mathbf{Z}
  (\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega}\mathbf{\Omega}^{\mathsf{H}}\mathbf{Z})^{-1}$ because
  $\mathbf{E}\mathbf{Z} = \mathbf{0}$. That gives $(1+\varepsilon)$ for every family with
  `HasJLMoment`, coexisting with the OSI bound (D10). Theorem 47's rank-$k$ clause comes only after
  the D15 check.
- **Early truncation by OSE plus AMM** (Woodruff Theorem 61 shape; assessment A4). This is S2b's
  core with $\lambda\ge 1-\varepsilon$ from `IsObliviousSubspaceEmbedding` for
  $\mathbf{V}_1$, and $w$, $\chi$ from the `HasJLMoment` AMM tails. Composed with shape (a) of
  GN, it gives early-truncated GN.
- **HMT §11 (SRFT Theorem 11.2).** Not ported as stated: its $\sqrt{1+7n/\ell}$ is dominated by
  the OSI route with the SRHT's injection from Sketching S6. To confirm in S7's note.

### 4.4 Material: the prototype and the maintainer's notes

The prototype is `~/Documents/prove2me/lean/NLAlib/LowRank/`: 42 files, 7413 lines, about 262
theorems and 47 definitions, one `sorry` (in the Cholesky block). It is mostly real, with
`Fin`-indexed Gaussian test matrices.

| Prototype | Lines | Disposition |
|---|---|---|
| `Structural/RangeFinder.lean` (HMT 9.1 Frobenius, any blocks; the $\sigma$-tail lemma `sq_le_four_div_mul_sum_Ico_sq`) | 235 | S1 material; replaced by the general-$\mathbf{Z}$ forms; the tail lemma kept |
| `RangeFinding/SpectralRangeFinder.lean` (HMT 9.1 spectral, 10.6) | 433 | S1, S3; the 10.6 step is already R4's block bound |
| `RandomizedSVD/{RSVD,Assembly,GaussianSketch,OptimalError}.lean` (HMT 10.5, truncated RSVD, `truncatedRsvdOutput`, `bestRankFrobSq`) | 934 | S2a, S3. `Assembly` (pure real arithmetic with expectations as hypotheses) and `bestRankFrobSq` (the library has `truncatedSVD` and Eckart–Young) are cut |
| `Nystrom/Structural.lean` (`nystrom`, the Gram correspondence for a factor, trace transfer) | 211 | S0, S5; the right shape already |
| `Nystrom/{SketchedRegression,GeneralizedNystrom,GaussianNystrom,RawNystromBridge,RawGaussianNystrom}.lean` | 1008 | S0, S6; four representations collapse into `obliqueProjector` (D1) |
| `Cholesky/` (RPCholesky, partial Cholesky, histories, complex twins) | 1501 | out of scope (§8); `eliminationStep_eq_sub_nystrom` is already in the Matrix layer |
| `Sampling/` (volume sampling, real and complex) | 1162 | out of scope (§8) |
| `PolynomialMethods/`, `RangeFinding/{ExpectedPower,SubspaceConvergence,ComplexSubspace*}.lean`, `Structural/PowerIteration.lean` | about 1700 | out of scope (§8) |

**The maintainer's notes** are read-only material and are never cited (D13):
- the Chen–Persson manuscript `~/Documents/Papers/LRA-paper/main.tex` (with
  `tGN_replacement.tex`, `pcps-et-audited.tex` and the audit `pcps-audit.md`);
- its Lean 4 formalization `~/Documents/Papers/LRA-paper/formal/` (253 theorems, no `sorry`, real
  field, Gaussian facts taken as hypotheses), organised by mechanism. From it:

  | file | used for |
  |---|---|
  | `Deterministic/RangeFinder.lean` | S1 |
  | `Deterministic/SketchedRegression.lean` | S0 core form, core noise |
  | `Deterministic/PerturbedTruncation.lean` | S2a item 7.4 |
  | `Deterministic/EarlyTruncation.lean` | S2b |
  | `Probability/Assembly.lean` (`gn_assembly`) | S6 |
  | `Theorems/*.lean` | S6, S7 statement shapes |

  Its `frobSq_sub_mul_eq`, `IsBestRankApprox` and `RankTraceBound` are the shapes of D1's core
  form, D5's hypothesis and item 7.4's hypothesis;
- `~/Documents/Papers/Generalized Nystrom/` and `~/Documents/Papers/PCPS*/`: earlier research
  notes, in places retracted (D15). They are not material for any stage.

## 5. Truncation and projection-cost-preserving sketches

### 5.1 Two places to truncate

The maintainer's notes describe two transformations of the RSVD: "sketch the projection" (RSVD
to GN) and "truncate", in two places. In this brief's spelling, with
$\mathrm{OPT} = \|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}$, $\ell$ the range
sketch size and $p$ the co-range sketch size:

| algorithm | output | Gaussian expectation, Frobenius squared | where |
|---|---|---|---|
| RSVD | `rsvd A Ω` | $(1+\frac{k}{\ell-k-1})\mathrm{OPT}^2$ (HMT 10.5) | S3 |
| late-truncated RSVD | `truncatedSVD (rsvd A Ω) k` | the same constant (item 6, truncation for free) | S3 |
| GN | `generalizedNystrom A Ω Ψ` | $(1+\frac{\ell}{p-\ell-1})(1+\frac{k}{\ell-k-1})\mathrm{OPT}^2$ (TYUC 4.3; EW 4.2(a)) | S6 |
| late-truncated GN | `truncatedSVD (generalizedNystrom A Ω Ψ) k` | `truncatedGNFactor k ℓ p`$\cdot\mathrm{OPT}^2$; $(1+\varepsilon)$ at $\ell = O(k/\varepsilon)$, $p = O(k/\varepsilon^2)$ | S6 (new) |
| early-truncated RSVD | `rangeProjector (truncatedSVD (A * Ω) k) * A` | deferred (§8); tail forms in S7 and S9 | S2b, S7, S9 |
| early-truncated GN | `obliqueProjector (truncatedSVD (A * Ω) k) Ψ * A` | $(1+\frac{k}{p-k-1})$ times the early-truncated RSVD bound | S6, S7, S9 |

Late truncation never uses PCPs. Early truncation is where they belong (assessment §1.2).

### 5.2 Late truncation (S2a)

The truncation of an output $\hat{\mathbf{A}}$ needs only Eckart–Young and §4.1 item 7, with four
tools:
- the constant-1 lemma (projections, Nyström);
- the generic constant-2 lemma (GN);
- the Frobenius-squared forms (the RSVD's competitor);
- the perturbed-truncation lemma, which bounds the truncated core by the *spectral* norm of the
  core noise.

A PCP hypothesis would be strictly stronger than what these proofs use. The probabilistic work
of truncated GN (spectral core noise, spectral residual) is bespoke to it and is stated in S6, not
abstracted (D1).

### 5.3 Early truncation (S2b), where PCPs and truncation combine

Early truncation optimises a projector *on the sketch*:
$\hat{\mathbf{P}} = \mathbf{P}_{\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k}$ is the best
rank-$k$ projector for $\mathbf{A}\mathbf{\Omega}$. Any statement transferring that optimality to
$\mathbf{A}$ has the shape of a projection-cost estimate. There are two deterministic routes,
and S2b holds both:
1. **The core (§4.1 item 8).** It is non-uniform: two projectors, three scalar sketch parameters
   $\lambda, w, \chi$, and no Frobenius-preservation condition. Its almost-sure corollary has all
   unboundedness in the scalar $\bar\lambda$, so it is the route that yields expectations as well
   as tails. Consumers:
   - the OSE-plus-AMM tail (S7, Woodruff Theorem 61 shape);
   - early-truncated GN through shape (a) of §4.3 (S6, S7);
   - later, the Gaussian expectation (§8).
2. **The uniform PCP.** If $\mathbf{A}\mathbf{\Omega}$ is a rank-$k$ PCP of $\mathbf{A}$ with
   error $\varepsilon$, then
   $\|\mathbf{A}-\hat{\mathbf{P}}\mathbf{A}\|_{\mathsf{F}}^2\le
   \frac{1+\varepsilon}{1-\varepsilon}\mathrm{OPT}^2$. The proof takes the lower bound at
   $\hat{\mathbf{P}}$, the optimality of $\hat{\mathbf{P}}$ on the sketch, and the upper bound at
   every $\mathbf{P}$. It is weaker by the $(1+\varepsilon)/(1-\varepsilon)$ loss, and gives no
   expectation: on the failure event the only fallback is $\|\mathbf{A}\|_{\mathsf{F}}^2$. But it
   is a black box, reused by every algorithm that optimises over projectors on a sketch
   (constrained low-rank approximation, $k$-means).

The two coexist (rule 4, named by hypothesis). Neither is the other's interface.

### 5.4 The PCP predicate

**Definition** (CEMMP 2015; Musco and Musco 2020, Definition 1; to confirm against CEMMP). For
$\mathbf{A}\in\mathbb{K}^{m\times n}$ and a sketch $\tilde{\mathbf{A}}\in\mathbb{K}^{m\times t}$,
$\tilde{\mathbf{A}}$ is a rank-$k$ projection-cost-preserving sketch of $\mathbf{A}$ with error
$\varepsilon$ and offset $c$ if, for every orthogonal projector $\mathbf{P}$ of rank at most $k$,
$$(1-\varepsilon)\|\mathbf{A}-\mathbf{P}\mathbf{A}\|_{\mathsf{F}}^2 \le
\|\tilde{\mathbf{A}}-\mathbf{P}\tilde{\mathbf{A}}\|_{\mathsf{F}}^2 + c \le
(1+\varepsilon)\|\mathbf{A}-\mathbf{P}\mathbf{A}\|_{\mathsf{F}}^2.$$
- Costs are squared Frobenius.
- The sketch is on the right, $\tilde{\mathbf{A}} = \mathbf{A}\mathbf{\Omega}$, and the projectors
  act on the left. This is D2's test-matrix orientation, as in CEMMP and the maintainer's notes.
- The predicate takes the pair $(\mathbf{A},\tilde{\mathbf{A}})$, so it applies to any sketch.
  `IsProjectionCostPreserving A Ã k ε c` is the candidate; the S2b note fixes the signature.

Its consequence: a $\gamma$-optimal rank-$k$ projector for $\tilde{\mathbf{A}}$ is
$\gamma\frac{1+\varepsilon}{1-\varepsilon}$-optimal for $\mathbf{A}$.

**Relation to the existing predicates.**
- A subspace embedding with parameters $(1\mp\varepsilon)$ for the whole row space of
  $\mathbf{A}$ makes $\mathbf{A}\mathbf{\Omega}$ a PCP for every $k$ at once, with $c = 0$, since
  every row of $(\mathbf{I}-\mathbf{P})\mathbf{A}$ lies in that row space. This is one line from
  `IsSubspaceEmbedding` (S2b). It costs dimension $\operatorname{rank}\mathbf{A}/\varepsilon^2$.
- The point of PCPs is dimension $O(k/\varepsilon^2)$, independent of the rank. That needs an OSE
  for the head $\mathbf{V}_k$ together with AMM-type control of the tail (CEMMP's sufficient
  conditions; Musco and Musco 2020 Theorem 2, conditions (i) to (iv)). `HasJLMoment` and
  `IsObliviousSubspaceEmbedding` supply the Frobenius parts for Gaussian, sub-Gaussian, Rademacher
  and CountSketch. The spectral part waits for spectral AMM (D7).
- An OSI is not enough: a PCP is two-sided and uniform over all rank-$k$ projectors, while the
  OSI route bounds one competitor from one side.

**Where it lives.** The deterministic predicate, its consequence, the row-space constructor and
route 2 of §5.3 are in S2b. `HasProjectionCostPreserving … δ μ`, in the tail form of the Sketching
round, with its family corollaries, is in S9. The head–tail constructor comes when CEMMP is in
hand.

### 5.5 Not ported from the notes

Rank-constrained GN (retracted proof), the two-sided two-pass estimator, and the $2\times 2$
early-truncation lower bound. All three are draft-only or retracted; D15 gives the reasons, and
§8 records them.

## 6. Epperly and Webber 2026: what is in scope

EW work over $\mathbb{K}\in\{\mathbb{R},\mathbb{C}\}$ with $\alpha_{\mathbb{K}}$, for Gaussian,
random orthonormal and rotation-invariant embeddings, in squared Frobenius and trace norm. Their
results, and where each goes:

| EW | Content | This round |
|---|---|---|
| Lemma 5.1 | sketch-and-solve error decomposition, rank-deficient case | S0 (§4.1 item 2), on `obliqueProjector` |
| Lemma 5.8 | "weighting hurts" | S10 (its only consumer is the Theorem 2.2 lower bound; review A5) |
| Fact 6.1 | Nyström and Schur complement: PSD, representation invariance, concavity, monotonicity | S0 |
| Fact 3.5 | Gram correspondence | S0, for a general factor |
| Proposition 5.4 | Gaussian sketching identity | exists (R4); S6 restates it as shape (a) |
| Proposition 5.6 | Beta inverse mean | S4, trace form only ($\mathbb{E}\operatorname{tr}\mathbf{X}^{-1}$; review A4(iii)) |
| Proposition 5.7 | random orthonormal sketching identity | S6 at $\mathbf{R} = \mathbf{I}$ (an equality); the general-$\mathbf{R}$ inequality is S10 |
| Theorem 2.1 | exact sketch-and-solve MSE and unbiasedness, Gaussian and orthonormal | S6 (real; $\alpha = 1$) |
| Theorem 3.1 | HMT 10.5 for rotation-invariant $\mathbf{\Omega}$ | S3, through the transfer |
| Theorems 3.2, 3.6(a) | sharp RSVD and Nyström upper bounds | S4 |
| Theorem 4.2(a) | sharp GN upper bound, $\gamma\in\{1,\frac{m-p}{m-\ell}\}$ in this brief's letters | S6 |
| Lemma 6.2 | two-eigenvalue instance | S4: the pointwise inequality at finite $a$; the limit $a\to\infty$ is S10 (review A13c) |
| Theorems 2.2, 3.3, 3.6(b), 4.2(b) | minimax lower bounds | S10, recommended for a later round (D6) |
| §4.2 | optimal ratio $k/\ell$ for GN, $q/\varepsilon$ versus $q/\varepsilon^2$ matvecs | docstring remarks only |
| Conjecture 7.1 | optimality of the algorithms | not formalised |

**Why these.** The upper bounds and exact formulas are what a user applies: they are the best
constants available for Gaussian and Haar test matrices. EW reduce every rotation-invariant law to
Haar by the polar factor, which the library already has (R5's characterization). Theorem 2.1 is
the sketch-and-solve result the maintainer brought into scope. Its Gaussian half is R4's block
moment almost verbatim, and GN is the composition (item 2). The lower bounds need a Haar unitary
on $\mathbb{K}^{n\times n}$ independent of the sketch and a probabilistic-method argument with a
limit. They are statements of optimality, not tools.

**Not in the library yet, for EW's upper bounds:**
- the Haar block laws (§4.3 (v): column block, row block, polar factor of a wide matrix);
- the signed-permutation conjugation average and the coupled law invariance (§4.3 (iv));
- complex laws ($\alpha_{\mathbb{K}} = 0$; D3).

No Beta-matrix law, no random permutations and no limit theorem are needed (review A4).

## 7. Stages

**Order:** S0, S1, S2a, S2b (maintainer checkpoint), S3, S5, S4, S6 (maintainer checkpoint), S7,
S9. S10 comes only if D6 keeps it in the round.
- The labels are kept from the draft so that the reviews' references stay valid. Only S2 is
  split.
- S5 comes before S4 (review A10). S5 needs only S0 to S3, and S4 is the most uncertain stage; its
  output (EW 3.6(a), 3.2) is a sharpening that lands on S3 and S5 afterwards. S6's Gaussian half
  does not need S4; its Haar half needs S4's row-block law.
- PCPs and truncation meet in S2b, before the first checkpoint, so the maintainer sees the
  combination early.

Gaussian and Haar first (S3 to S6), then the general routes (S7, S9), as the maintainer allowed.
Each stage gets `docs/design/LowRank-<Stage>.md`. Sizes are estimates from the prototype's and the
manuscript formalization's line counts, after removing twins and parallel representations.

- **S0 Shared definitions and exact identities.**
  - Content:
    - `obliqueProjector` and its API (§4.1 item 1), with the §5.3 row amendment and D14 decided;
    - the `obliqueProjector_of_isUnit` corollaries replacing `Oblique.lean`'s invertible-case
      lemmas;
    - `rsvd`, `generalizedNystrom`, `nystrom`, `sketchAndSolve` with their bridges (D1);
    - the exact error split in projector form, core form and core-noise form, and EW's solution
      error (item 2);
    - exactness at low rank;
    - the Gram correspondence and its companions (item 3), including the selection instance;
    - Schur-complement monotonicity and concavity (item 4);
    - gauge equality for $\mathbf{X}\mathbf{X}^{\mathsf{H}}$ and $\mathbf{X}^{\mathsf{H}}\mathbf{X}$
      (item 5);
    - reproving the Sketching round's `frobNorm_sub_mul_pinv_mul_sq_le` from the split, name kept.
  - Files:
    - `Matrix/Subspaces/ObliqueProjector.lean` (about 400);
    - `Matrix/Factorizations/Nystrom.lean` (extended, about 250);
    - `Matrix/Factorizations/NystromOrder.lean` (about 250).
  - Consumers: every later stage; Solvers.
  - Material: prototype `Nystrom/Structural.lean`, `Nystrom/SketchedRegression.lean`,
    `Nystrom/RawNystromBridge.lean`; formalization `Deterministic/SketchedRegression.lean`; EW
    §5.1, §6.1; MT §2.7, Proposition 11.1, §14.2; TW §5.4, Lemma 5.2.
  - Size: about 900 lines (draft: 700; review answer 5).
- **S1 The structural bound of the range finder.**
  - Content:
    - §4.1 item 6 for any frame $\mathbf{Z}$, in the Gram form and the unsquared triangle form;
    - the instance at the top singular vectors (HMT Theorem 9.1, spectral and Frobenius,
      unsquared corollaries);
    - the competitor $\mathbf{C}$ as a public lemma (rank, range);
    - the Nyström structural bound in every gauge by S0 (Gittens and Mahoney's form);
    - the $\mathbf{M}$ formula through an AMM error (for S7);
    - the tail-flattening lemma.
  - File: `LowRank/Structural/RangeFinder.lean`.
  - Consumers: S2a to S7.
  - Material: prototype `Structural/RangeFinder.lean`, `RangeFinding/SpectralRangeFinder.lean`;
    formalization `Deterministic/RangeFinder.lean`; HMT §9.1–9.2; MT Theorem 11.4; TW Proposition
    8.5; Woodruff Lemmas 45, 48; CEMT Imported Theorem 2.3.
  - Size: about 500 lines.
- **S2a Late truncation.**
  - Content: §4.1 item 7. That is:
    - the constant-1 gauge lemma with its projection (HMT 9.3) and Nyström instances;
    - the generic constant-2 lemma;
    - the Frobenius-squared forms and the rank-$k$ competitor form;
    - the D5 hypothesis form and the factored-form lemma, with the choice-free identities;
    - the truncated Gram correspondence (trace);
    - the perturbed-truncation lemma and its spectral corollary;
    - GN core truncation (Woodruff Theorem 47 shape) only after the D15 check.
  - File: `LowRank/Structural/Truncation.lean`.
  - Consumers: every late-truncated statement of S3 to S7.
  - Material: prototype `RandomizedSVD/OptimalError.lean` (truncation half); formalization
    `Deterministic/PerturbedTruncation.lean`; HMT §9.4; Woodruff Lemmas 44 and 48, Theorem 47.
  - Size: about 550 lines.
- **S2b Early truncation and projection-cost-preserving sketches (deterministic).**
  - Content:
    - the early-truncation core and its almost-sure corollary (§4.1 item 8);
    - if D7 is approved: the PCP predicate, its consequence, the constructor from a row-space
      subspace embedding, and the uniform-PCP early-truncation corollary (§5.3 route 2, §5.4).
  - Files: `LowRank/Structural/EarlyTruncation.lean` (about 450),
    `Sketching/Properties/ProjectionCost.lean` (about 250).
  - Consumers: S6 (early-truncated GN), S7 (OSE-plus-AMM tail), S9; later, early-truncated RSVD in
    expectation.
  - Material: formalization `Deterministic/EarlyTruncation.lean`; CEMMP; Musco and Musco 2020;
    Woodruff Theorem 61.
  - Size: about 700 lines.
  - **Maintainer checkpoint after S2b.**
- **S3 Gaussian and Haar range finder and RSVD.**
  - Content:
    - the Gram-form expectation of §4.3, giving HMT 10.5, TW (RSVD2) for every Schatten
      $p \ge 2$, and the squared spectral error;
    - HMT 10.6 from the existing block bound;
    - TW (RSVD1) as the primary tail, with HMT 10.7 and 10.8 beside it or as corollaries;
    - optionally, TW 8.7 and 8.8 at $\ell\in\{k, k+1\}$;
    - truncated RSVD in Frobenius with HMT's constant;
    - exact recovery at low rank;
    - Haar and rotation-invariant versions through R5;
    - named factors (D9).
  - Files: `LowRank/Gaussian/RangeFinder.lean`, `LowRank/Gaussian/RangeFinderTail.lean`.
  - Consumers: S5, S6; users.
  - Material: prototype `RandomizedSVD/*`, `RangeFinding/SpectralRangeFinder.lean`; HMT §10; TW
    Theorems 8.1, 8.7; MT Theorem 11.5.
  - Size: about 800 lines.
- **S5 Nyström from the range finder.**
  - Content:
    - trace, spectral and every-gauge expectation bounds (TW Corollaries 8.2 and 8.8) and tails
      (NysSVD1), all by S0's correspondence from S3;
    - $\mathbf{F} = \mathbf{H}^{1/2}$ corollaries stated for PSD $\mathbf{H}$, with best errors
      in eigenvalues;
    - truncated Nyström: the trace bound with $(1+\frac{k}{\ell-k-1})$ and the spectral bound with
      $2\lambda_{k+1}$ (§4.3). MT Theorem 14.1's constant only after TYUC NeurIPS is read, and
      then as an S2a lemma.
  - File: `LowRank/Gaussian/Nystrom.lean`.
  - Consumers: Solvers (Nyström PCG), Estimation.
  - Material: prototype `Nystrom/Structural.lean`; MT §14; TW §8; CEMT §2.3.
  - Size: about 400 lines.
- **S4 Sharp bounds for rotation-invariant test matrices.**
  - Content:
    - the Haar block laws (§4.3 (v) a, b) and the polar factor of a wide matrix (c);
    - the signed-permutation conjugation average and the coupled law invariance (§4.3 (iv));
    - $\mathbb{E}\operatorname{tr}((\mathbf{\Omega}_1\mathbf{\Omega}_1^{\mathsf{H}})^{-1})$ by
      the trace route (§4.3 (iii));
    - the finite block-permutation average with Fact 6.1(c) (§4.3 (ii));
    - Lemma 6.2's pointwise inequality at finite $a$ (§4.3 (i));
    - EW Theorem 3.6(a) and, by the correspondence, 3.2. Their sharpenings of S3 and S5 are
      added as corollaries.
  - Files:
    - `RandomMatrix/Haar/Blocks.lean` (block laws);
    - the conjugation average in the Matrix layer (`NystromOrder.lean` or a small
      `Matrix/Basic/SignedPermutation.lean`; the S4 note decides);
    - `LowRank/Gaussian/RotationInvariant.lean`.
  - Consumers: S6 (Haar $\mathbf{\Psi}$, GN's sharp bound); S10 if kept.
  - Material: EW §5.3, §6.2, §6.3; no prototype material.
  - Size: about 650 lines (draft: 900). The uncertainty now sits in the block laws.
- **S6 Sketched regression, generalized Nyström and their truncations, Gaussian and Haar.**
  - Content:
    - EW Theorem 2.1 (both laws) and unbiasedness;
    - Proposition 5.7 at $\mathbf{R} = \mathbf{I}$;
    - the GN identity in shapes (a) and (b), for Gaussian and for Haar $\mathbf{\Psi}$ (EW Theorem
      4.2(a); TYUC Theorem 4.3 as the bound form);
    - early-truncated GN as shape (a) at $\mathbf{X} = \llbracket\mathbf{A}\mathbf{\Omega}
      \rrbracket_k$, stated with the range-finder bound as a hypothesis so that every
      early-truncation route instantiates it;
    - truncated GN in expectation: spectral core noise, spectral residual, assembly,
      `truncatedGNFactor`, the $(1+\varepsilon)$ corollary, and the exact-recovery branch;
    - GN truncation by S2a's lemmas in the deterministic forms.
  - Files:
    - `Sketching/Gaussian/LeastSquares.lean` (D8);
    - `LowRank/Gaussian/GeneralizedNystrom.lean`;
    - `LowRank/Gaussian/TruncatedGeneralizedNystrom.lean`.
  - Consumers: Solvers; users of single-pass methods.
  - Material: prototype `Nystrom/{GeneralizedNystrom,GaussianNystrom,RawGaussianNystrom}.lean`;
    formalization `Probability/Assembly.lean`, `Theorems/*.lean`; EW §2, §4, §5; R2, R4, and the
    spectral moments of `Gaussian/SpectralNorm.lean` and `InverseMoments/Spectral.lean`.
  - Size: about 1150 lines (draft: 800, before truncated and early-truncated GN).
  - **Maintainer checkpoint after S6.**
- **S7 The OSI and OSE routes, every family.**
  - Content:
    - CEMT Theorem 2.2, Corollaries 2.5 and 2.8 with explicit $(1+t/a)$ and $\delta + 1/t$;
    - Woodruff Lemma 45, and Theorem 47 subject to D15, through injection plus AMM;
    - truncated versions by S2a;
    - early truncation by OSE plus AMM (S2b's core), and early-truncated GN through it;
    - one corollary per family: SRHT (both models), CountSketch, sub-Gaussian, Rademacher, Haar,
      Gaussian; sampling where the fixed-$\mathbf{U}$ form suffices;
    - the orientation lemmas of D2, with the scaling.
  - Files: `LowRank/Oblivious/RangeFinder.lean`, `LowRank/Oblivious/GeneralizedNystrom.lean`,
    `LowRank/Oblivious/EarlyTruncation.lean`.
  - Consumers: users holding a structured sketch.
  - Material: CEMT §2; Woodruff §4.1, Theorem 61; Sketching S0, S1 and the family theorems.
  - Size: about 850 lines.
- **S8 Reserved.** Complex Gaussian and Haar versions of S3 to S6, if D3 changes. Otherwise
  empty.
- **S9 Projection-cost-preserving sketches (probabilistic).** Only if D7 is approved.
  - Content:
    - `HasProjectionCostPreserving` in the tail form;
    - its constructor from an OSE of the row space;
    - the uniform-PCP corollaries for early-truncated RSVD and GN;
    - the head–tail constructor at $O(k/\varepsilon^2)$ and its family corollaries, when CEMMP is
      in hand and spectral AMM exists.
  - Files: `Sketching/Properties/ProjectionCost.lean` (extended),
    `LowRank/Oblivious/EarlyTruncation.lean` (extended).
  - Size: about 250 lines, plus about 400 for the head–tail constructor.
- **S10 EW lower bounds, if D6 keeps them in the round.**
  - Content: Theorems 2.2, 3.3, 3.6(b), 4.2(b); Lemma 5.8; Proposition 5.7 for general
    $\mathbf{R}$; Lemma 6.2's limit.
  - File: `LowRank/Optimality/RotationInvariant.lean`.
  - Size: about 750 lines.

| stage | lines |
|---|---|
| S0 | 900 |
| S1 | 500 |
| S2a | 550 |
| S2b | 700 |
| S3 | 800 |
| S5 | 400 |
| S4 | 650 |
| S6 | 1150 |
| S7 | 850 |
| S9 | 250 |
| **total** | **about 6750** |

The total excludes S8, S10 (750) and S9's head–tail constructor (400). The draft's comparable
total was about 5600. The growth is truncated GN (about 350), the early-truncation core (about
450) and the larger S0. S4 and S9 shrink. The prototype had about 3000 in-scope lines, and no
gauge forms, no EW, no OSI route, no PCPs and no truncated GN.

## 8. Later rounds (no stage here)

Recorded so that a later brief starts from it.

- **Iterative and adaptive methods** (maintainer, 2026-10-15): power and subspace iteration (HMT
  §9.3, §10.4, Corollary 10.10; MT §11.6), RBKI and block Krylov (MT §11.7; Musco and Musco 2015;
  TW §7), polynomial filters, randomly pivoted Cholesky (Chen, Epperly, Tropp and Webber), adaptive
  rank. Prototype material:
  - `PolynomialMethods/`, `Structural/PowerIteration.lean` (HMT Proposition 8.6),
    `RangeFinding/{ExpectedPower,SubspaceConvergence,ComplexSubspace*}.lean`, `Cholesky/`.
  - These are ledgered as deferred with this section as the reason. Their deterministic
    prerequisites (Proposition 8.6, the Gram-power bound) would join S1's file when taken up.
- **Early-truncated RSVD in expectation** (D15). The maintainer's notes prove
  $(1+\varepsilon)\mathrm{OPT}^2$ at $\ell\ge 900k/\varepsilon^2$ from S2b's core. It needs,
  first, a RandomMatrix item "smallest singular value tails":
  - Gordon's inequality with Gaussian concentration (Vershynin 2012, Theorem 5.32, Corollary
    5.35);
  - a chi-square small-ball bound (Laurent and Massart 2000);
  - inverse moments of $\min\{1,\lambda\}$ up to order four by a layer-cake integral;
  - the decoupling of $\mathbf{V}_1^{\mathsf{H}}\mathbf{\Omega}$ from the tail sketch.

  Early-truncated GN in expectation then follows from S6's shape (a).
- **Not ported, no rigorous source** (D15): rank-constrained GN (retracted), the two-sided
  two-pass estimator, the $2\times 2$ early-truncation lower bound. They are later-round
  candidates only if a proof appears.
- **EW lower bounds** (S10), if D6 defers them, with Lemma 5.8 and Lemma 6.2's limit.
- **Column selection**: volume sampling (prototype `Sampling/`), leverage-score column sampling,
  CUR and interpolative decompositions. The Matrix layer's `IsLocalMaxVolume` is their
  deterministic half.
- **Solvers**: Nyström PCG (Frangella, Tropp and Udell 2023; MT §17), sketch-and-precondition,
  and EW Theorem 2.2's sketch-and-solve lower bound if S10 is skipped.
- **Three-sketch single-view SVD** (Tropp et al. 2019; MT §15.1, Theorem 15.3).
- **Complex laws** (D3), then complex versions of S3 to S6 with EW's $\alpha_{\mathbb{C}} = 0$.

## 9. Literature

### 9.1 In hand, locators confirmed against the PDFs

- **HMT** (`HalkoMartinssonTropp2011`; arXiv v2, printed pages):
  - Propositions 8.1–8.6 (p. 47–49);
  - Theorem 9.1 (p. 51, both norms, proof written for spectral);
  - Theorem 9.2 (p. 54; the printed $B = (A^*A)^qA$ is a typo for $(AA^*)^qA$);
  - §9.4 Theorem 9.3 (p. 54, spectral only, projections only; credited to Gu). Its proof is
    triangle inequality, Eckart–Young and $\sigma_{k+1}(\mathbf{P}\mathbf{A})\le
    \sigma_{k+1}(\mathbf{A})$, which is §4.1 item 7.1;
  - Propositions 10.1–10.4 (p. 55–56);
  - Theorems 10.5–10.8 and Corollary 10.9 (p. 56–59);
  - Corollary 10.10 (p. 60);
  - Theorems 11.1, 11.2 (p. 62–63);
  - Nyström only in §5.4 (Algorithm 5.5, p. 33), with no proved error bound.
- **Martinsson and Tropp 2020** (`MartinssonTropp2020`; printed = PDF + 402):
  - §2.7 Schur complements (p. 415);
  - Algorithm 8 (p. 469–470);
  - Proposition 11.1 and Corollary 11.2 (p. 470–471);
  - Theorem 11.4 (p. 472, remark on quadratic unitarily invariant norms);
  - Theorem 11.5 (p. 473, spectral only);
  - §14.2 (p. 495, $\mathbf{A}\langle\mathbf{X}\rangle = \mathbf{A}^{1/2}\mathbf{P}\mathbf{A}^{1/2}$
    stated without proof);
  - Theorem 14.1 (p. 496, PDF 94): truncated Nyström in the **spectral** norm (confirmed),
    $\mathbb{E}\|\mathbf{A}-\hat{\mathbf{A}}_k\|\le\lambda_{k+1}+\frac{k}{\ell-k-1}\sum_{j>k}
    \lambda_j$, credited to TYUC NeurIPS Theorem 4.1. This brief's route reaches only
    $2\lambda_{k+1}$ (§4.3);
  - §15 single view, Theorem 15.3 (p. 501–502), Remark 15.4.
- **Tropp and Webber 2023** (arXiv:2306.12418 v3; real field):
  - Lemma 5.1 (p. 15);
  - §5.4 and Lemma 5.2 (p. 18–20);
  - Theorem 8.1 (RSVD1 and RSVD2) and Corollary 8.2 (p. 33);
  - Proposition 8.5 (p. 35);
  - Proposition 8.6 (p. 36);
  - Theorem 8.7 and Corollary 8.8 (p. 37–38);
  - the $\mathbf{A}^{1/2}$ identity in the proofs (p. 37–38);
  - truncation remark (p. 42);
  - Lemmas B.1–B.3 (Gaussian moments, used by truncated GN).

  It does not use the phrase "Gram correspondence" and does not analyse GN. Not yet in
  `references.bib`.
- **Camaño, Epperly, Meyer and Tropp 2025** (`CamanoEpperlyMeyerTropp2025`; printed = PDF − 2):
  - Definition 1.2 (p. 3: the sketch is $\mathbf{\Omega}^{*}$, $\mathbf{\Omega}\in
    \mathbb{F}^{d\times k}$);
  - Theorem 1.3 and its truncation remark (p. 6–7). The remark appeals to HMT Theorem 9.3, which
    is spectral-only, for Frobenius bounds; S2a's Frobenius lemmas close that gap;
  - Lemma 2.1 (p. 14), Theorem 2.2 and Imported Theorem 2.3 (p. 16);
  - Imported Theorem 2.4 (the Gram correspondence, after Gittens and Mahoney Lemma 1; nuclear form
    only) and Corollary 2.5 (p. 17);
  - Lemma 2.6 (after TYUC Lemma A.4) and Theorem 2.7 (p. 18–19);
  - Corollary 2.8, in which $\mathbf{\Psi}$ is an OSI of dimension $k$ = the columns of
    $\mathbf{\Omega}$, and Remark 2.9 on truncated GN (p. 19–21). Remark 2.9 is the published
    comparison point for truncated GN; its exact claim is checked in the S6 note.
- **Woodruff 2014** (`Woodruff2014`):
  - Lemma 44 (p. 63), Lemma 45 (p. 63–65), Theorem 47 (p. 66–67; rank-$k$ clause under the D15
    caution), Lemma 48 (p. 69);
  - Theorem 60 (p. 92, power method, out of scope);
  - Theorem 61 (p. 95, early truncation under an OSE).

  It has no projection-cost-preserving sketches by that name.
- **Epperly and Webber 2026** (arXiv:2605.19096 v2, 24 pp.), read in full. Locators as in §6.
  Currently in a session scratch directory, not in `~/Documents/prove2me/books/` (§9.2).
- **Horn and Johnson** (`HornJohnson2013`): Theorem 7.4.9.1 (Mirsky), behind
  `matrixNorm_sub_truncatedSVD_le_of_rank_le`; Theorem 7.4.1.1 (von Neumann), behind
  `norm_trace_conjTranspose_mul_le_sum_singularValues_mul`.
- **Not citable, material only:** the Chen–Persson manuscript and its formalization (§4.4, D13).
- In `references.bib`: `HalkoMartinssonTropp2011`, `MartinssonTropp2020`, `Woodruff2014`,
  `CamanoEpperlyMeyerTropp2025`, `HornJohnson2013`, `Bhatia1997`, `GolubVanLoan2013`,
  `Tropp2015`, `Vershynin2018`. Missing and needed: `TroppWebber2023`, `EpperlyWebber2026`, and
  the essential downloads below.

### 9.2 To download

**Essential** (a stage statement or its citation depends on the locator):
1. **Tropp, Yurtsever, Udell and Cevher**, "Practical sketching algorithms for low-rank matrix
   approximation", SIAM J. Matrix Anal. Appl. 38(4):1454–1485, 2017 (arXiv:1609.00048).
   - S6: Theorem 4.3, GN with Gaussian sketches (the bound form of the GN identity, and the
     published source for GN and the completion bound).
   - S0: Lemma A.4, the error formula and the core-noise algebra.
   - S2a: the fixed-rank bounds of §5–6, to confirm that item 7.2 is theirs, and its number.
2. **Tropp, Yurtsever, Udell and Cevher**, "Fixed-rank approximation of a positive-semidefinite
   matrix from streaming data", NeurIPS 30, 2017 (arXiv:1706.05736).
   - S5 and S2a: Theorem 4.1, truncated Nyström. Its argument is the only known route to MT
     Theorem 14.1's single-$\lambda_{k+1}$ constant. S5's note is not written before this is read
     (review A1).
   - S1: Lemma A.1, the structural Nyström bound (provenance).
3. **Cohen, Elder, Musco, Musco and Persu**, "Dimensionality reduction for k-means clustering and
   low rank approximation", STOC 2015 (arXiv:1410.6801).
   - S2b: the PCP definition (cited "to confirm" until read), its consequence for constrained
     low-rank approximation, and the sufficient conditions the early-truncation core's docstring
     names.
   - S9: the $O(k/\varepsilon^2)$ families.

**Housekeeping** (a copy, not a download): copy the Epperly and Webber PDF from the session scratch
directory into `~/Documents/prove2me/books/`, so that later agents find it.

**Nice to have** (provenance, alternative proofs, optional sharpenings):
- **Gittens and Mahoney**, "Revisiting the Nyström method for improved large-scale machine
  learning", JMLR 17(117):1–65, 2016 (arXiv:1303.1849).
  - S0: Lemma 1, the Gram correspondence as CEMT cite it. It is proved here from
    `pinv_eq_pinv_conjTranspose_mul_self_mul`, so the paper is provenance only.
  - S1, S5: their norm-specific deterministic Nyström bounds are instances of the Gram form.
- **Nakatsukasa**, "Fast and stable randomized low-rank matrix approximation", arXiv:2009.11392,
  2020. S0, S6: GN's formulation, the $\ell$-to-$p$ ratio, stability remarks (docstrings only).
- **Gu**, "Subspace iteration randomization and singular value problems", SIAM J. Sci. Comput.
  37(3):A1139–A1173, 2015 (arXiv:1408.2208). S2a: Theorem 3.4 (gapped reverse Eckart–Young) and
  the fixed-rank RSVD bounds HMT Theorem 9.3 credits to him. It is worth one read: its spectral
  form may be the twin of "truncation for free" (§4.1 item 7.8).
- **Musco and Musco**, "Projection-cost-preserving sketches: proof strategies and constructions",
  arXiv:2004.08434, 2020. S2b, S9: Definition 1, Theorem 2 (the sufficient conditions),
  Corollary 7.
- **Boutsidis, Drineas and Magdon-Ismail**, "Near-optimal column-based matrix reconstruction",
  SIAM J. Comput. 43(2), 2014. S1: the structural form beside Woodruff Lemma 48 (locator to
  confirm).
- Clarkson and Woodruff, "Numerical linear algebra in the streaming model", STOC 2009
  (Theorem 4.7, GN; Woodruff Theorem 47 restates it).
- Tropp, Yurtsever, Udell and Cevher, "Streaming low-rank matrix approximation with an
  application to scientific simulation", SIAM J. Sci. Comput. 41(4), 2019 (Theorem 5.1,
  Corollary 5.5; MT Theorem 15.3).
- Epperly, PhD thesis, Caltech 2025 (§2.6, history of the Gram correspondence), and his blog post
  "Low-rank approximation toolbox: The Gram correspondence" (December 2024), the source of the
  name.
- Gittens, "The spectral norm error of the naïve Nyström extension", arXiv:1110.5305 (2011).
- Drineas and Mahoney, "On the Nyström method for approximating a Gram matrix…", JMLR 6, 2005
  (Lemma 4, cited by HMT §5.4).
- Boutsidis, Mahoney and Drineas, SODA 2009 (credited by MT Theorem 11.4).
- Witten and Candès, Algorithmica 72, 2015 (sharp spectral analysis, EW §3.3).
- Bartan and Pilanci, arXiv:2002.06538 (2020) (Lemma 2.1, the real Gaussian case of EW Theorem
  2.1).
- Feldman, Schmidt and Sohler, SODA 2013 / SIAM J. Comput. 2020 (PCP-type coresets).
- Musco and Musco, NeurIPS 2015 (gapless truncation bounds, TW p. 42; block Krylov, later).
- Woolfe, Liberty, Rokhlin and Tygert, ACHA 25, 2008 (provenance of GN and the SRFT).
- Later rounds:
  - Vershynin 2012 (Theorem 5.32, Corollary 5.35) and Laurent and Massart 2000 (Lemma 1), for
    early-truncated RSVD in expectation;
  - Frangella, Tropp and Udell, SIAM J. Matrix Anal. Appl. 44(2), 2023 (Nyström PCG);
  - Persson and Kressner, SIAM J. Matrix Anal. Appl. 44(2), 2023 (Nyström for monotone matrix
    functions);
  - Chen, Epperly, Tropp and Webber (RPCholesky, Comm. Pure Appl. Math., 2025).

### 9.3 Citations for each ported result

The Chen–Persson manuscript is never cited (D13). Each docstring cites the published source that
states the result. If there is none, the docstring says "proved without a literature source" and
cites only the published inputs. Locators marked "to confirm" are checked when the paper is in
hand.

| result | stage | citation |
|---|---|---|
| structural bound, untruncated (spectral, Frobenius, Gram form) | S1 | HMT Theorem 9.1; MT Theorem 11.4; TW Proposition 8.5 |
| structural bound with the rank-$k$ competitor (truncation for free) | S1, S2a | Woodruff Lemma 48; CEMT Imported Theorem 2.3 and the remark after Theorem 1.3; Boutsidis, Drineas and Magdon-Ismail 2014 (to confirm) |
| RSVD and late-truncated RSVD in expectation | S3 | HMT Theorem 10.5, plus the row above |
| Gaussian completion identity (GN step, sketch-and-solve) | S6 | EW Theorem 2.1 and Lemma 5.1; TW 2023, proof of Theorem 5.1; bound form TYUC 2017 Theorem 4.3 |
| GN in expectation | S6 | TYUC 2017 Theorem 4.3 (bound); EW Theorem 4.2(a) with $\gamma = 1$ (identity) |
| Gaussian moment inputs | S6 | TW Lemmas B.1–B.3; HMT Propositions 10.1, 10.2 |
| exact Gaussian AMM second moment $(\|\mathbf{M}\|_{\mathsf{F}}^2\|\mathbf{N}\|_{\mathsf{F}}^2+\|\mathbf{M}\mathbf{N}^{\mathsf{T}}\|_{\mathsf{F}}^2)/t$, if needed | S7 | proved without a literature source; input: Isserlis (as for CountSketch's twin) |
| perturbed-truncation lemma (§4.1 item 7.4) | S2a | proved without a literature source; input: von Neumann (Horn and Johnson Theorem 7.4.1.1). Related but different: Gu 2015 Theorem 3.4, TYUC SIMAX, Musco and Musco 2015 |
| spectral core noise of truncated GN | S6 | proved without a literature source; inputs: TW Lemmas B.1, B.3; the algebra is EW Lemma 5.1 and TYUC Lemma A.4 |
| spectral residual of truncated GN | S6 | proved without a literature source; inputs: HMT Theorem 9.1, TW Lemmas B.1, B.3 |
| truncated GN in expectation | S6 | proved without a literature source; comparison points named in the docstring: CEMT Remark 2.9, and the $k/\varepsilon^3$ triangle-inequality baseline |
| early-truncation core and almost-sure corollary | S2b | proved without a literature source; the sketch conditions are those of CEMMP 2015 and Musco and Musco 2020 Theorem 2, conditions (i)–(iii) |
| early truncation by OSE plus AMM | S7 | Woodruff Theorem 61; CEMMP 2015 |
| PCP predicate, consequence, uniform-PCP early truncation | S2b, S9 | CEMMP 2015 (definition and constrained-LRA lemma); Musco and Musco 2020 Definition 1, Theorem 2, Corollary 7 (constants there unspecified; explicit ones are the library's) |
| early-truncated GN | S6, S7, S9 | proved without a literature source, as a composition; cite EW Theorem 2.1 for the completion step and the early-truncation source used |
| Gram correspondence | S0 | MT Proposition 11.1, §14.2; EW Fact 3.5; CEMT Imported Theorem 2.4; Gittens and Mahoney Lemma 1 |

## 10. Questions for the maintainer

1. **Readings (§0.1).** Recommended: yes to each.
   - Is "one pass" a property of the output formula, with no streaming model?
   - Are "truncated variants" all three of: late truncation
     $\llbracket\hat{\mathbf{A}}\rrbracket_k$, the rank-$k$-restricted projection
     $\mathbf{Q}\llbracket\mathbf{Q}^{\mathsf{H}}\mathbf{A}\rrbracket_k$, and early truncation
     $\mathbf{P}_{\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k}\mathbf{A}$ with its GN twin, as
     in your notes?
   - Does "pcps" mean projection-cost-preserving sketches (CEMMP; Musco and Musco 2020)?
2. **D1 (confirm).** One core `obliqueProjector`; `rsvd`, `generalizedNystrom`, `nystrom` and
   `sketchAndSolve` as definitions with bridge lemmas; one exact split, also in core-noise form; in
   the Matrix layer. The unification stops there: the truncated analyses stay separate (D1, "Where
   the analyses diverge"). Recommended: confirm.
3. **D2 (confirm).** HMT and CEMT orientation, with the Sketching predicates applied to
   $\mathbf{\Omega}^{\mathsf{H}}$ and $\mathbf{\Psi}^{\mathsf{H}}$. Recommended: confirm; it is
   forced by consistency with the Sketching round.
4. **D4 (confirm).** Two deterministic forms:
   - the Gram form as primary, covering the quadratic unitarily invariant norms (Schatten
     $p\ge 2$ of the error, squared);
   - the unsquared triangle form in every gauge as companion.

   Truncated results in squared Frobenius (trace for Nyström). For Gaussian and Haar, expectation
   before tails, with TW (RSVD1) as the primary tail. Recommended: confirm.
5. **D6.** EW's minimax lower bounds: this round (S10) or a later one? Recommended: a later round.
6. **D7.** PCPs in this round? Recommended: yes. The deterministic predicate sits beside the
   early-truncation core in S2b (where PCPs and truncation combine), and the probabilistic form in
   S9. The $O(k/\varepsilon^2)$ constructor waits for CEMMP and spectral AMM.
7. **Citation policy for your manuscript with Persson (`cp25`; LRA-paper, August 2026, no venue).**
   It is not cited anywhere, following your earlier instruction (Sketching D16). Its new results
   are ported with docstrings that say "proved without a literature source" and cite only
   published inputs (§9.3):
   - the perturbed-truncation lemma;
   - truncated GN in expectation;
   - the early-truncation core and its almost-sure corollary;
   - the early-truncated GN composition.

   Please confirm:
   - that you want these results in the public library before the manuscript appears (the
     alternative is to hold them until it does);
   - whether docstrings should be updated to cite it once it is published.

   Recommended: port now, cite on publication.

## 11. Done

The round is done when:
- S0, S1, S2a, S2b, S3 to S7, and those of S9 and S10 the maintainer keeps, are implemented;
- `NLAlib` and `NLAlibScaffold` build with no warnings;
- `scripts/Audit.lean`, `scripts/Lint.lean` and `check_refs.py` pass;
- the ledger accounts for the prototype's 324 `LowRank` declarations, with §8 the reason for the
  deferred ones;
- `docs/design/LowRank-REPORT.md` reports as `Sketching-REPORT.md` did.
