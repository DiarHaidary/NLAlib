# Port status

Updated at every stopping point. Newest entry first within each section.

## Sketching moments round: skeleton (2026-10-22)

Branch `sketching/moments` (worktree `nlalib-block`), from `46f78ab` (rebased from `1e5334f`
after the Krylov-spectral review follow-ups). Statement skeleton of
`docs/design/Sketching-Moments.md` (approved 2026-10-22, MD2–MD4 as recommended, full scope; the
note's last section lists the changes during the skeleton). Statements with `sorry` (48 in all):
`Sketching/Structured/SRHTMultiplication.lean` (new, 12), `Sketching/Gaussian/ProjectionCost.lean`
(new, 7: the twins, the Haar PCPs and the three asymptotic forms),
`Probability/MatrixConcentration/BernsteinWithoutReplacement.lean` (new, 6),
`LowRank/Oblivious/{SubGaussian, SRHT, Gaussian, Haar}.lean` (4, 4, 2, 2; `Haar` new),
`Regression/{Haar, Gaussian, SubGaussian, SRHT}.lean` (3, 2, 2, 2; `Haar` new),
`Sketching/Sampling/MatrixMultiplication.lean` (2). Proved and sorry-free: the ForMathlib Gamma
and log bounds, everything added to `Probability/Tail.lean`, `SubExponential/Tail.lean`,
`MatrixConcentration/{Bernstein, ChernoffWithoutReplacement}.lean`, `JohnsonLindenstrauss.lean`,
`Sketching/Gaussian/{Gaussian, Haar, HaarEmbedding, SubGaussian, Rademacher}.lean` (the JL moments
at every order with sizes and asymptotic forms, the Haar $1 \mp \varepsilon$ OSE/OSI) and
`Flattening.lean`. Six asymptotic forms change statement (MD4), listed in
`docs/renames/2026-10-sketching-moments.json`. Next: proofs, two agents on disjoint files (the
report of the skeleton gives the order).

## Krylov spectral round: proofs (2026-10-22)

Every statement of the skeleton is proved; no `sorry` remains in the round's files, and all of
them count as proved modules (`scripts/proved_modules.py`): `Matrix/Spectral/SpectralMeasure.lean`,
`Polynomial/Orthogonal/{Moments, Basic, Gauss}.lean`, `Polynomial/Chebyshev/EvenFilter.lean`,
`Krylov/Functions/Quadrature.lean`, `Krylov/Eigenvalues/{Ritz, PowerIteration}.lean`,
`Estimation/Spectral/RandomStart.lean`, and the new
`ForMathlib/Analysis/SpecialFunctions/Trigonometric/Chebyshev/ChebyshevGauss.lean`. No statement
changed. The public helpers the proofs added (`integrable_eval_of_ae_mem_Icc`,
`Polynomial.Chebyshev.sumZeroes_def`, `rayleighQuotient_cfc_mulVec_eq_integral_div`) and the
`Bochner.Set` imports are recorded with dates in the note's "Changes during the proofs". KS3c
(the Ritz values as Gauss nodes, positive weights) is proved from the compression alone, without
tridiagonal theory. `scripts/leansrc.py` now reads `import all X` as an import of `X` (it took
`all` for a module, a false P11 error); test added.

Checks: `lake build --wfail NLAlib` 3990 jobs, 0 warnings; `scripts/stage_check.sh`: 391 proved
modules, 0 not yet; build 3988 jobs, 0 warnings; audit 9615 declarations, 0 violations; lint 6245 declarations, 0
errors; references 87 keys, 70 asymptotic forms, 0 problems; constants 30, 336 value markers, 0
problems; rules 0 errors, 73 in the baseline; duplicates 5706 theorems, 0 classes.

Open items:
* The printed constants of Kuczyński and Woźniakowski (`KuczynskiWozniakowski1992`) are not yet
  checked. The power constant $\lambda_0\log(1 + \tan^2)/(2q + 1)$ is proved
  (`Matrix.PosSemidef.eigenvalue_sub_rayleighQuotient_pow_mulVec_le`). Only the docstrings of the
  named bounds `randomStartPowerBound` and `randomStartLanczosBound`
  (`Estimation/Spectral/RandomStart.lean`) say that the printed constant is to be compared. The
  theorem docstrings in `Krylov/Eigenvalues/PowerIteration.lean`
  (`Matrix.PosSemidef.eigenvalue_sub_rayleighQuotient_pow_mulVec_le`) and
  `Krylov/Eigenvalues/Ritz.lean`
  (`Matrix.PosSemidef.eigenvalue_sub_eigenvalue_conjTranspose_mul_mul_le_div_sq`) never mention
  the paper's constant: they cite it with a locator from the quarry, "to check", and the
  skeleton entry below overstates them. Each of the four must be checked against the paper, and
  its docstring must state the source's value, the value proved and the gap (CONTRIBUTING §5.2,
  rule 2).
* KS7 (orthogonal-polynomial structure theory: existence and real-rootedness, three-term
  recurrence, Christoffel–Darboux, `jacobiMatrix`, interlacing of zeros) stays deferred, note §8;
  no consumer this round.

## Krylov spectral round: skeleton (2026-10-22)

Branch `krylov/spectral` (worktree `nlalib-block`), from `375e005`. Statement skeleton of
`docs/design/Krylov-Spectral.md` (approved 2026-10-22, SD1–SD7 as recommended, SD4's rule named
`interpolatoryQuadrature`; the note's last section lists the changes during the skeleton). New
files with `sorry` statements: `Matrix/Spectral/SpectralMeasure.lean`,
`Polynomial/Orthogonal/{Moments, Basic, Gauss}.lean`, `Polynomial/Chebyshev/EvenFilter.lean`,
`Krylov/Functions/Quadrature.lean`, `Krylov/Eigenvalues/{Ritz, PowerIteration}.lean`,
`Estimation/Spectral/RandomStart.lean` (50 `sorry` in all). Proved and sorry-free: the additions to
`Polynomial/Approximation/Jackson.lean` (Jackson on $[a, b]$), `Krylov/Functions/LanczosFA.lean`
(the two KS4 rates), `Matrix/Spectral/SingularValues.lean` (the frame-conjugation eigenvalue
lemma, flagged: intended home `Eigenvalues.lean`), `Probability/Distributions/Gaussian.lean`,
`Probability/Measurability/{Matrix, Krylov}.lean`. Next: proofs, one file at a time, in the
order of the note's §6 adjusted by the skeleton report.

Open item, before the round closes: the printed constants of Kuczyński and Woźniakowski
(`KuczynskiWozniakowski1992`) are not yet checked. The docstrings of `randomStartPowerBound` and
`randomStartLanczosBound` (`Estimation/Spectral/RandomStart.lean`),
`Matrix.PosSemidef.eigenvalue_sub_rayleighQuotient_pow_mulVec_le`
(`Krylov/Eigenvalues/PowerIteration.lean`) and
`Matrix.PosSemidef.eigenvalue_sub_eigenvalue_conjTranspose_mul_mul_le_div_sq`
(`Krylov/Eigenvalues/Ritz.lean`) cite the paper with locators from the quarry and say only that
the printed constant is to be compared. Each must be checked against the paper, and the
docstring must state the source's value, the value proved and the gap (CONTRIBUTING §5.2, rule
2).

## Consolidation round complete (2026-10-22)

Branch `cleanup/consolidation` (worktree `nlalib-block`), from `dd2eaf7`. Design note
`docs/design/Consolidation.md` (approved 2026-10-22, D1 option (a); its dated amendments record the
few unforeseen imports and statement spellings). No new mathematics: re-proved private helpers became
the 49 public lemmas of §3 in the file of their topic (Phase A, 27 commits), and every consumer
dropped its copies (Phase B, one file per commit). Private declarations 1731 → 1646. One public
declaration removed (`NLAlib.integral_comp_eq_integral_integral_of_indepFun`, in favour of
`ProbabilityTheory.IndepFun.integral_comp_eq_integral_integral`) and one statement change
(`conjTranspose_mul_mul_le_conjTranspose_mul_mul` drops `[Finite n]`), both in the rename map
`docs/renames/2026-10-consolidation.json`; `rademacherMatrix` moved to
`RandomMatrix/Rademacher/Basic.lean` under the same name. The CONTRIBUTING §5.3 row "independent
test matrices" names the F1 conditioning lemmas as the preferred route (bridge column only, D1).

Checks: `lake build --wfail NLAlib` 3979 jobs, 0 warnings; `check_rules.py --only S5 --warnings`
0 (was 17 same-name pairs); `scripts/stage_check.sh`: 381 proved modules, build 3977 jobs, 0
warnings; audit 9363 declarations, 0 violations; lint 6106 declarations, 0 errors; references 86
keys, 68 asymptotic forms, 0 problems; constants 28, 324 value markers, 0 problems; rules 0 errors,
73 in the baseline; duplicates 5582 theorems, 0 classes (was 4). `scripts/Reuse.lean` on the 181
public theorems whose proofs changed: each consumer calls the new public lemma. Copies kept as
recorded in the note: the single-use privates of §6 and the Hanson–Wright MGF.

## Sketch-and-precondition and randomized Kaczmarz: proofs (2026-10-20)

Every statement of the skeleton is proved; no `sorry` remains in the round's files, and all of
them count as proved modules. No statement changed. Maintainer decisions of 2026-10-20 applied:
the i.i.d. law is `NLAlib.iidSequence` with `_of_hasLaw_iidSequence` names (N9), and
`IsSubspaceEmbedding.pos_right_of_injective` moved to `Sketching/Properties/SubspaceEmbedding.lean`
(P10). Helpers added: `EuclideanSpace.norm_le_norm_toLp` (ForMathlib PiL2),
`Matrix.integral_mulVec` (ForMathlib SpecificCodomains.Matrix), `Real.mul_pow_le_of_mul_log_le`
(ForMathlib Log.Basic), and the tail
`HasSubspaceEmbedding.measureReal_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le_of_one_sub_one_add`
in `Regression/SketchAndPrecondition.lean`, which the four family files apply.

## Sketch-and-precondition and randomized Kaczmarz: skeleton (2026-10-20)

Branch `regression/sketch-precondition` (worktree `nlalib-block`), rebased onto `rules/stage3`.
Statement skeleton of `docs/design/Regression-SketchPrecondition.md` and
`docs/design/Regression-Kaczmarz.md` (both approved 2026-10-19; each note's last section lists the
changes during the skeleton). New files with `sorry` statements:
`Krylov/LinearSystems/Richardson.lean`, `Regression/{SketchAndPrecondition, IterativeSketching,
SubGaussian, SRHT}.lean`, `Solvers/{SketchAndProject, Kaczmarz}.lean`; the family forms added to
`Regression/{Gaussian, CountSketch}.lean` are `sorry` too. Proved and sorry-free: the additions to
`ForMathlib/Probability/Independence/{Basic, InfinitePi}.lean`, `Probability/Law.lean`,
`Matrix/Pseudoinverse/{Pinv, ConditionNumber}.lean`, `Matrix/Norms/Frobenius.lean` and
`Regression/Embedding.lean`. Next: proofs, one file at a time, Richardson first.

## Naming grammar and renames (2026-10-19)

Branch `naming/grammar` (worktree `nlalib-block`), from `origin/main` at bc72b8d. Design note
`docs/design/Naming.md` (the audit, the maintainer's decisions of 2026-10-19, the dot-notation
scope addition); grammar CONTRIBUTING §4, rules N1–N18. 311 public declarations renamed (194 by
the grammar rules, 117 more by N18 dot notation) and 37 statements changed (28 scalar tails stated
positively, 9 trace-estimation errors flipped to `tr A − estimate`), no aliases (before `v0.1`);
rename map `docs/renames/2026-10-naming.json` for the explorer's `#d/` redirects. No exception
kept; 5 checker false positives on `scripts/names_allow.toml`. `scripts/check_names.py` runs on the
extraction in CI (error mode) and in `scripts/stage_check.sh`. Private helpers keep their names.

Checks: `lake build NLAlib NLAlibScaffold` 3954 jobs, 0 warnings; `lake exe mk_all --check` clean;
`scripts/stage_check.sh`: 354 proved modules, build 3950 jobs, 0 warnings; audit 9164
declarations, 0 violations; lint 5983 declarations, 0 errors; references 77 keys, 61 asymptotic
forms, 0 problems; constants 28, 306 value markers, 0 problems; names 4105 declarations, 0
violations, 5 allowlisted; duplicates 5464 theorems, 0 classes; LaTeX 22889 spans, 0 problems;
no `sorry`. Open: `docs/design/Naming.md` §4 (`norm_toLp`, `truncatedGNFactor`, explorer
redirects and its two TOML citations; the rules-enforcement stage absorbs `check_names.py`).

## Hutch++ round complete (2026-10-18)

Branch `probability/trace-estimation` (worktree `nlalib-block`), uncommitted on top of `e2b2d91`.
Stages TE-0 to TE-5 of `docs/design/Estimation-HutchPP.md` are proved; `import NLAlib` has no
`sorry`. The last one, P1 `ProbabilityTheory.IndepFun.integral_comp_eq_integral_integral`
(`ForMathlib/Probability/Independence/Basic.lean`), is three rewrites: the joint law is the
product of the laws (`indepFun_iff_map_prod_eq_prod_map_map`), then `integral_map`,
`integral_prod`; Mathlib has only the product forms (`IndepFun.integral_fun_comp_mul_comp`,
searched). `HutchPlusPlusTail.lean` now builds in the full library (it had been checked only
against a scratch olean). Fixes from the checks: a 100-character line in the module docstring of
`Probability/QuadraticForm/Moments.lean`; value markers for `subgaussianRangeFinderFactor c` and
`hansonWrightConstant` in the `HutchPlusPlusTail.lean` module docstring. In
`Probability-TraceEstimation.md` two `\rvert` that had become carriage returns are restored. The asymptotic `C = 20000`
stays existential (CONTRIBUTING §5.2 rule 3; the docstring says "the proof takes $C = 20000$", as
the other asymptotic forms do). The note's Implementation has "What was proved", "Deviations"
(Skeleton changes 1 to 12) and "Later targets" (XTrace, NA-Hutch++, complex probes, the TE4 probe
interface). CONTRIBUTING §5.3: rows for independent test matrices (`IndepFun S G μ`),
`girardHutchinson` and `hutchpp`; `subgaussianRangeFinderFactor` gets none (a named factor with a
registry entry, like the others). Ledger: twenty prototype entries from
`Estimation.Trace.Unbiased` and `Estimation.Trace.HutchinsonTail` (stages TE-0, TE-1, TE-2); the
prototype's XTrace declarations and Gaussian/Rademacher corollaries of the Hutchinson tail remain
unported.

Checks: `lake build NLAlib` 3952 jobs, 0 warnings; `lake exe mk_all --check` clean;
`scripts/stage_check.sh`: 354 proved modules, build 3950 jobs, 0 warnings; audit 9153
declarations, 0 violations; lint 5983 declarations, 0 errors; references 77 keys, 61 asymptotic
forms, 0 problems; constants 28, 306 value markers, 0 problems; duplicates 5464 theorems, 0
classes; LaTeX 22889 spans, 0 problems; `ledger_check.py` only the documented `IsSVD.eq` false
positive. NLAlibScaffold not rebuilt.

## Trace estimation variances (2026-10-18)

Branch `probability/trace-estimation` (worktree `nlalib-block`), uncommitted on top of `b1d21fa`
(the Hutch++ design note). Design and implementation: `docs/design/Probability-TraceEstimation.md`
(decisions D1 to D8; D2, D3, D8 moot; **[maintainer]** flags on D5 suffix `_hermitianPart`, D6 name
`girardHutchinson`). Proved, no `sorry`:

- `RandomMatrix/Haar/Moments.lean`: exact variance of `tr (Qᴴ A Q)` for Haar frames (multiplied
  form for every `n`, divided for `n ≥ 2`, any real `A`), real sphere `2n/(n+2)(‖A‖² − tr²/n)`.
- `Probability/QuadraticForm/Moments.lean`: real Gaussian/Rademacher for any real `A`, Rademacher optimality.
- New `Estimation/Trace/GirardHutchinson.lean`: `girardHutchinson`, unbiasedness, `v / m` for
  independent probes (𝕜 and real `variance` forms), orthonormal Haar probes.
- `Matrix/Spectral/HermitianPart.lean`: `quadForm_hermitianPart`,
  `trace_conjTranspose_mul_hermitianPart_mul` (the Hutch++ note's A3).

Deferred, maintainer request: the complex probe laws (Gaussian, Steinhaus, sphere) were removed
(recoverable from `f1d3e75`; see "Deferred: complex probes" in the design note). Later target: the
sphere's worst-case optimality.
Ledger: `hutchinsonEstimate`, `integral_hutchinsonEstimate_eq_trace`. Not mine and not touched:
the concurrent edit of `Probability/SubGaussianVector/Basic.lean` (Hutch++ P8).

Checks: `lake build NLAlib` 3952 jobs, 0 warnings; `scripts/stage_check.sh`: 354 proved modules,
build 3950 jobs, 0 warnings; audit 9133 declarations, 0 violations; lint 5969 declarations, 0
errors; references 74 keys, 0 problems; constants 28, 0 problems; duplicates 5439 theorems, 0
classes; LaTeX 22523 spans, 0 problems; `mk_all --check` clean (NLAlib); `ledger_check.py` only
the documented `IsSVD.eq` false positive. NLAlibScaffold not rebuilt. (Counts include the
concurrent Hutch++ work in the same worktree.)

## Krylov block round complete (2026-10-18)

Branch `krylov/block` (worktree `nlalib-block`), uncommitted on top of `657cd18` (B7). Stages B0 to
B7 of `docs/design/Krylov-Block.md` are proved: block Krylov spaces, `rbki` and `nystromBKI`, TW
Lemma 9.5, TW Theorem 9.2 (gapped) and Theorem 9.1 (gapless) for RBKI and RSI, the Musco–Musco
$(1 + \varepsilon)$ gapless form with its truncated lines and asymptotic depth, the Nyström variants.
The note's Implementation now has "What was proved", "Wrap-up amendments", "Deviations" and
"Later targets" (next: BCW arXiv:2202.05120 Theorem 5.1, upper bound only); `PORT_KRYLOV.md` has the
2026-10-18 directions and progress. CONTRIBUTING §5.3: rows for `singularGapRatio` and
`HasSupportingLineOn` (BD9; `rangeFinderTailRatio` needs none).

Wrap-up placement pass (no statement changed): the private attainment helper of `TraceFunctions.lean`
is public as `IsStarProjection.exists_mulVec_eq_self_and_re_quadForm_eq_specNorm_mul_sq` in
`Matrix/Spectral/CourantFischer.lean`; the private "$\sigma_t = 0$" helper of
`Gaussian/BlockKrylov.lean` is replaced by the public `truncatedSVD_of_singularValues_eq_zero`
in `Matrix/Spectral/LowRank.lean`; `Polynomial/Chebyshev/Filter.lean` is deleted, its one fact now
`Polynomial.Chebyshev.hasSupportingLineOn_mul_eval_T_sq` in ForMathlib's Chebyshev growth file;
`Real.exp_two_mul_le_one_add_div_one_sub` moved to `ForMathlib/Analysis/SpecialFunctions/Log/Deriv.lean`;
three private copies of $0 \le t/(\ell - t - 1)$ (Duplicates) replaced by the public
`natCast_div_sub_sub_one_nonneg` in `Gaussian/RangeFinder.lean`. No placement flag open. Ledger:
eleven prototype entries (B0, B1b, B3).

Checks (`scripts/stage_check.sh`): 351 proved modules, build 3947 jobs, 0 warnings; audit 8924
declarations, 0 violations; lint 5848 declarations, 0 errors; references 73 keys, 41 asymptotic
forms, 0 problems; constants 27, 0 problems; duplicates 5332 theorems, 0 classes; LaTeX 21703 spans,
0 problems; `lake build NLAlib` 3949 jobs; `mk_all --check` clean (NLAlib). `ledger_check.py`
reports only its documented `IsSVD.eq` false positive. NLAlibScaffold not rebuilt.

## Krylov K1, K2, K2b complete (2026-10-17)

Branch `krylov/brief`, uncommitted on top of `1908a3f` (K1 checkpoint 5): `WorstCase.lean`
(Greenbaum for CG and MINRES), the new `Krylov/Functions/Optimality.lean` (Chen–Persson Theorem 2,
its fixed-shift form and CG case), `NLAlib.lean`. K1 (`Krylov-LinearSystems.md`) checkpoints 1 to
5, K2 (`Krylov-Functions.md`) C1 to C5 and K2b (`Krylov-Sharpness.md`) KB1 to KB3 are proved; K2
C6 (quadrature) is open. Docstring follow-ups of `Krylov-Sharpness.md` §10 done (no "stage K2b"
forward references remain). Placement flags closed: `exists_hasOrthonormalCols_range_eq_krylovSpace`
public in `Krylov/Basic/Grade.lean`; `Matrix.IsHermitian.preconditionedLanczosState_z_eq_zero_of_le`
and `…_beta_eq_zero_of_le` public in `Processes/PreconditionedLanczos.lean` (the private conjunction
split); the private grade identity in `MINRESRecurrence.lean` replaced by `krylovGrade_mul_mulVec`;
`mgsArnoldiHessenberg_apply_eq_zero_of_le`, `injective_mulVec_mgsArnoldiHessenberg_iff` public in
`Processes/ArnoldiRecurrence.lean`; `Matrix.mulVec_eq_submatrix_castLE_mulVec` in
`ForMathlib/Data/Matrix/Mul.lean`. No statement changed. `Greenbaum1979`, `GreenbaumGurvits1994`
checked against Crossref (DOIs added); theorem locators still to verify. Notes amended (all three
design notes, `PORT_KRYLOV.md` "Progress"). Ledger: one missing K1 entry added
(`krylovSpace_mul_mulVec_eq_map`); the K2b files port nothing.

Checks (`scripts/stage_check.sh`): 342 proved modules, build 3938 jobs, 0 warnings; audit 8696
declarations, 0 violations; lint 5706 declarations, 0 errors; references 72 keys, 0 problems;
constants 26, 0 problems; duplicates 5195 theorems, 0 classes; LaTeX 20845 spans, 0 problems;
`mk_all --check` clean (NLAlib, NLAlibScaffold). `ledger_check.py` reports only its documented
`IsSVD.eq` false positive. NLAlibScaffold not rebuilt.

## Krylov K0 (CG slice) complete (2026-10-17)

Branch `krylov/brief`, uncommitted on top of checkpoint `71fb07c`. All eight Krylov files of
`docs/design/Krylov-CG.md` §6 are proved and registered in `NLAlib.lean` (`lake exe mk_all`).
Placement pass (CONTRIBUTING §8 item 5): `conjTranspose_mul_apply` and
`conjTranspose_mul_mul_apply` now public in `Matrix/Basic/Gram.lean` (two private copies deleted);
`HasOrthonormalCols.star_col_dotProduct_eq_zero_of_mem_span` public in
`Matrix/Basic/Orthonormal.lean`; `krylovGrade_le_of_mem_of_mulVec_eq` public in
`Krylov/Basic/Grade.lean`. A private `conjTranspose_mul_mul_apply` in
`Sketching/Properties/Isotropic.lean` clashed and is renamed `conjTranspose_mul_mul_apply_eq_sum`.
Note amended ("Implementation (2026-10-17)": added lemmas, the direct Lanczos and
Hestenes–Stiefel routes, the moves, counts); no statement changed. Ledger: 9 K0 entries.

Checks (`scripts/stage_check.sh`): 322 proved modules, build 3913 jobs, 0 warnings; audit 7784
declarations, 0 violations; lint 5282 declarations, 0 errors; references 61 keys, 0 problems;
constants 26, 0 problems; duplicates 4848 theorems, 0 classes; LaTeX 18643 spans, 0 problems;
`mk_all --check` clean. Open: the note's Saad2003/Saad2011/TrefethenBau1997 locators still to be
checked against the books before the PR; NLAlibScaffold not rebuilt in this pass.

## Stronger Jackson bound complete (2026-10-16)

The public `isUniformApproxOn_jacksonApprox_of_lipschitz` now exposes the proved error
πL/(N+2) for the same polynomial, interval Lipschitz hypotheses and RCLike values. It uses
`jacksonApproximationConstant`, currently π, with positivity and ≤π API, following the HMT
Gaussian pseudoinverse precedent and CONTRIBUTING §5.2. The earlier final weakening is removed.
The design amendment and actual source/registry/instruction changes passed independent review.
CONTRIBUTING explicitly says not to discard an already-proved stronger bound merely to match a
source constant or an earlier draft. Same theorem/result names; no unused weaker companion.
Twenty-three explicit public additions in the combined Jackson work; the irreducible definition
also generates its body equation. Kernel, coefficients and hypothesis interfaces are unchanged.

Added `Rivlin1981` and `ShahUrschelWest2026` (arXiv:2607.23375v2) as requested, with module
background citations. Documentation distinguishes improvement over the cited CTU v1 bound from
optimality: the newer paper's sharper asymptotic constants/remainder are not formalized here.

Final stronger-source checks: target build and capped file check clean; full build 3909 jobs/0
warnings; audit 7501 declarations/0 violations; 14 linters on 5116+2385 declarations/0 errors;
duplicates 4709 theorems/0 classes; root import and proof-reuse checks pass. References (59 keys),
constants (26), and LaTeX (18199 spans) pass. Explorer extraction has 315 modules/3534 declarations,
all source fingerprints match, headline displays πL/(N+2), and the named factor has support role.
Logs/artifact: `/tmp/nlalib-jackson-stronger-{target,lean,build,audit,lint,duplicates,reuse,explore}.log`
and `/tmp/nlalib-jackson-stronger-explore.json`. No active build or proof gap at handoff.
The prototype ledger remains unchanged for the previously reviewed source-coverage reasons.

The report below records the prior `c769e96` source-bound commit; this section and the latest
design amendment supersede its numerical guarantee. J1, moments and OP remain later stages.

## Jackson kernel and constructive approximation complete (2026-10-16)

The user-approved stages 1 and 2 are complete and independently reviewed. Design, exact APIs,
source relation and mathematical read-back: `docs/design/Polynomial-Jackson-Moments.md`.
`Polynomial/Approximation/JacksonKernel.lean` has 2 definitions and 11 theorems;
`Polynomial/Approximation/Jackson.lean` has 1 definition and 5 theorems. One shared finite
Chebyshev-expansion coefficient theorem in the existing coefficient owner replaces both private
consumer inductions. Twenty public additions total; prior truncation API unchanged. All three
CONTRIBUTING vocabulary rows and the shared-owner placement passed independent review.

The canonical approximant has degree at most N, its full coefficients are exactly the damped input
coefficients and each contracts. For an interval-Lipschitz real- or complex-valued function the
uniform error on [-1,1] is at most π²L/(2(N+2)), including N=0/L=0 and endpoints. Kernel positivity,
normalization and first cosine moment are proved. Source is Chen–Trogdon–Ubaru arXiv:2204.01941v1
Appendix C; no new coefficient spelling, global Lipschitz or analytic assumption is introduced.

Combined checks: full build 3909 jobs/0 warnings; axiom audit 7502 reachable declarations/0
violations; 14 linters on 5112+2390 declarations/0 errors; duplicates 4707 theorems/0 classes;
root import checks, references, constants, LaTeX and proof reuse pass. Affected-target builds and
capped file checks are clean. Logs: `/tmp/nlalib-jackson-{build,audit,lint,duplicates,reuse}.log`,
`/tmp/nlalib-j0-checks/`, `/tmp/nlalib-j2-checks/`. Explorer extraction contains 315 modules,
3530 declarations and the documented `jackson-lipschitz` result, with all source hashes checked.
Artifact: `/tmp/nlalib-jackson-explore.json`; this is extraction validation, not site deployment.

The unchanged textual ledger checker reports its documented false positive for the generated
`IsSVD.eq` field; a direct Lean check confirms the field exists. No genuine prototype dispositions
apply: the prototype's sharper existential/sawtooth Jackson results remain outstanding, so the
ledger is unchanged. No new scaffolds or remaining proof gaps; no active builds at handoff.
Available-agent fallback continues. J1 coefficient decay, noisy moment comparison and finite OP
results remain later exact-design checkpoints. No Wasserstein/duality identity is claimed.

## Polynomial Poly3 (2026-10-16)

Complete and independently reviewed: `docs/design/Polynomial-Analytic.md`. All five proof steps
and eleven public declarations are approved: focal ellipse definition, ten theorems for canonical
coefficient bridges/decay, generic reconstruction, inclusive truncation error and affine existence.
Four new modules plus the coefficient-owner extension preserve the approved generic f/compatible
complex-extension interface, open-domain hypotheses, endpoints, N=0 and M=0. Four root imports,
one vocabulary row/addition note and two genuine headline successor mappings are recorded;
previous mappings unchanged, no object aliases or unproved ellipse equivalence claimed.

Final-source full two-thread build passed (3907 jobs, zero warnings), both root checks passed,
audit 7398/zero violations, 14 linters 5069 plus 2329 generated/zero errors, duplicates 4667
and zero classes. Refs (56 keys/40 forms), constants (25), KaTeX (5516 docstrings/18168 spans),
11 metadata tests and eleven reuse targets passed. Prior target/capped checks passed. The reviewed
period amendment reuses Mathlib `Polynomial.instTwoPiPos` locally, with no new public Fact witnesses;
final gates were rerun against those sources. Logs: `/tmp/nlalib-poly3-checks`.
Fresh extraction `/tmp/nlalib-poly3-explore.json`: 313 modules/3510 public declarations, all source
hashes matching and eleven additions proved. Strict unchanged Explorer build: 312 visible modules,
254 results/172 enriched definitions; Rates unchanged at 32 rows/nine guarantees/three families.
No UI/Rate edits, redundant browser/stage build, active validation process, commit or push.
Root handles commit and extraction restamp; later stages retain exact design checkpoints.

## Polynomial Poly2 (2026-10-16)

Complete and independently reviewed: `docs/design/Polynomial-Series.md`. Both files/all nine
public declarations are approved: one canonical full RCLike coefficient, four coefficient facts,
inclusive degree-N truncation, evaluation/degree and exact arbitrary-polynomial reproduction.
Two root imports, two approved vocabulary rows and one genuine real-coefficient prototype mapping
are recorded; prior ledger entries are unchanged. Analytic contour/real-part objects remain
unmapped pending true representation bridges. No numbered Mathlib deviation or proof changes.

Full two-thread build passed (3900 jobs, zero warnings), both root checks passed, audit 7300/zero
violations, 14 linters 5033 plus 2267 generated/zero errors, duplicates 4632 theorems/zero classes.
References (56 keys/40 asymptotic forms), constants (25), KaTeX (5501 docstrings/18134 spans),
11 metadata tests and nine reuse targets passed. Prior target/capped checks passed; no redundant
stage build or browser run. Logs: `/tmp/nlalib-poly2-checks`.
Fresh extraction `/tmp/nlalib-poly2-explore.json`: 309 modules/3499 public declarations, all source
hashes matching and nine additions proved. Strict unchanged Explorer build: 308 visible modules,
252 results/171 enriched definitions; Rates remains 32 rows/nine guarantees/three families.
No active validation process, commit or push; root handles commit and extraction restamp.
The subsequently approved Poly3 interface is implemented in the completed stage above.

## Polynomial Poly1 (2026-10-16)

Complete and independently reviewed: `docs/design/Polynomial-Minimax.md`. Both files/all six
new statements are approved: external modulus comparison, monic minimax and exact normalized
residual minimax, preserving Poly0 API and including q=0. One new root import and six genuine
prototype mappings were recorded; previous ledger entries are unchanged. No new vocabulary,
Mathlib deviation or proof edits during mechanical validation.

Full two-thread build passed (3895 jobs, zero warnings), both root checks passed, audit 7278/zero
violations, 14 linters 5020 plus 2258 generated/zero errors, duplicates 4621 theorems/zero classes.
References (56 keys/40 asymptotic forms), constants (25), KaTeX (5490 docstrings/18117 spans),
11 metadata tests and six reuse targets passed. Prior target/capped checks passed; no redundant
stage build. Logs: `/tmp/nlalib-poly1-checks`.
Fresh extraction `/tmp/nlalib-poly1-explore.json`: 307 modules/3490 public declarations, all source
hashes matching and all six additions proved. Strict unchanged Explorer build passed: 306 visible
modules/251 results/169 enriched definitions; Rates remains 32 rows/nine guarantees/three families.
No active validation process, commit or push; root handles the commit and extraction restamp.

Poly2 full coefficient normalization, one generic RCLike API and inclusive degree-N truncation
(0 through N) are explicitly user-approved. These choices are implemented in the completed Poly2 stage above. Available-agent fallback continues.

## Polynomial Poly0 (2026-10-16)

Complete and independently reviewed; user-approved roadmap and stage design:
`docs/PORT_POLYNOMIAL.md`, `docs/design/Polynomial-Chebyshev.md`. Five new modules provide
18 public declarations for the shared metric approximation interface, Chebyshev growth,
normalized residual, generic degree-controlled factorization and inverse approximation,
including q=0. The existing Matrix approximation theorem now consumes the named interface
in place. All six topic reviews approved; no proof edits during mechanical validation.

Five root imports, two approved CONTRIBUTING vocabulary rows and eleven genuine prototype
ledger mappings are recorded. The Mathlib comparison records additions with existing `dist`,
`Chebyshev.T` and `ContinuousMap.dist_le`, without a competing spelling or numbered deviation.
No future-stage prototype dispositions were added. Full two-thread build passed (3893 jobs,
zero warnings), both root checks passed, audit 7267 declarations/zero violations, 14 linters
5012 plus 2255 generated/zero errors, duplicate report 4613 theorems/zero classes. References
(55 keys, 40 asymptotic forms), constants (25 bounds), KaTeX (5483 docstrings/18083 spans),
11 metadata tests and all nineteen reuse targets passed. Target/capped file checks had already
passed. Logs: `/tmp/nlalib-poly0-checks`; no redundant overlapping stage build was run.

Fresh extraction `/tmp/nlalib-poly0-explore.json`: 306 modules, 3484 public declarations,
all source hashes matching and all nineteen changed/new targets proved. The unchanged actual
Explorer metadata passes a strict build (305 visible modules, 248 results, 169 enriched
definitions); its 32 Rates rows/nine guarantees/three families remain unchanged. No Explorer
edit or new Rates family. Final source/read-back and verified Saad2003 locators are in the design
report. No active build/process and no validation-agent commit or push; root handles the commit.
The already-approved roadmap's next exact stage receives bounded design review before proofs;
important lasting changes retain user assessment. Available-agent fallback continues.

## Regression rates (2026-10-16)

Complete and independently reviewed on `feat/regression-rates`; design, source read-back and
validation report: `docs/design/Regression-Rates.md`. Eleven new public declarations provide
Gaussian/Haar expected relative squared-residual pairs, a generic RCLike AMM-tail consumer,
and Gaussian/CountSketch high-probability relative-residual pairs. The existing factor helper
was moved unchanged to its RandomMatrix owner; no new object, interface, constant or prototype
mapping. Both new Regression modules are registered. Available-model fallback continues.

Full two-thread build passed (3873 jobs, zero warnings), as did both root checks, axiom audit
(7235 declarations, zero violations), 14 linters (4994 plus 2241 generated, zero errors), duplicate
report (4597 theorems, zero classes), references (55 keys, 40 asymptotic forms), constants,
KaTeX and all-eleven-target reuse. Prior capped module/single-file checks passed. The import
DAG is acyclic with no Regression→LowRank import; ledger dispositions are unchanged. A second
overlapping stage build was omitted after the equivalent root gates passed.
Fresh extraction: `/tmp/nlalib-regression-rates-explore.json`, 301 modules, 3466 declarations;
all source hashes match and all eleven additions are proved. Logs:
`/tmp/nlalib-regression-rates-checks`. Explorer integration uses this extraction separately.
No validation-agent commit or push; root handles the requested local commit.

## Regression organization (2026-10-16)

Completed user-approved whole-file relocation on `feat/regression-organization`:
`Regression/{Embedding,Oblique,Oblivious,SketchAndSolve}.lean`, with consumers and root imports
updated. Names, statements and proof bodies are unchanged; the import DAG is acyclic and
Sketching core does not import Regression. No aliases or ledger edits are needed. Public direct
module imports migrate according to `docs/design/Regression-Organization.md` (design/read-back/report).
Validation passed: full two-thread build (3871 jobs, no warnings), four moved-file Lean checks,
root generation/audit/lint/duplicate checks, references/constants/LaTeX. The redundant stage
script was omitted because the root checks cover its gates. Fresh extraction has 299 modules,
3455 declarations and validated Regression source hashes; old paths are absent.
Logs: `/tmp/nlalib-regression-checks`; extraction: `/tmp/nlalib-regression-explore.json`.
Validated for the requested local commit; no push requested.

## Standing instructions

- 2026-10-14, maintainer: no approval stop for the Matrix layer. Each stage's design note is
  written, sent to a Fable review, amended, and implemented without waiting. Decisions that would
  have been approval questions are recorded in the note under "Open questions" with the choice
  taken, for review after the fact. When very unsure: commit a checkpoint, then continue.

- 2026-10-14, maintainer: **the orchestrator does less itself** (its context runs out). It keeps
  the decisions, the agent briefs, the reading of agent reports, and commits. It delegates: design
  notes are drafted by an Opus agent from a short brief (scope, consumers, decisions already made)
  and reviewed by Fable; skeletons are written by the proof agent's predecessor or by an Opus
  "skeleton" agent from the reviewed note; file splits, ledger entries (prototype-key lookup and
  `ledger_add.py`), `NLAlib.lean` registration, status-table updates and `stage_check.sh` runs go
  to Sonnet agents; proofs to Opus as before. The orchestrator reads reports, not files, and checks
  builds only through `stage_check.sh` output.
- 2026-10-14, orchestrator rule for skeleton agents: never add a `sorry` statement to a proved
  file (above all a registered one); new statements go in a new skeleton file, merged at wrap-up.
  (A P6/R3 skeleton agent added two to `Isotropic.lean` and one to `ChiSquareMoments.lean`; a proof
  agent was sent to prove them.)
- 2026-10-14, maintainer: files up to about 1000 lines (Mathlib's 1500-line linter is the hard
  ceiling); proofs under about 80 lines (`CONTRIBUTING.md` §1, §8, §10).

- 2026-10-14, maintainer, approval for the Probability round: the maintainer weighs in on
  serious design decisions, meaning those that would need substantial rework to change once the
  round is finished (an interface every later theorem takes, a definition's carrier or indexing,
  a naming scheme, a global instance). The orchestrator collects these, with the alternatives
  and a recommendation, and stops for them before building on them. Everything else proceeds
  without a stop and is recorded in the design note, as in the Matrix layer.

- 2026-10-14, maintainer, for the Probability layer and above (inputs to its brief, not yet
  designed):
  1. Measurability belongs to Probability, not Matrix (done: `Probability/Measurability/`).
  2. Numerical bounds start here. Before statements are written, fix how a later improvement of
     a bound, and a new proof whose bound is incomparable with the old one (mostly better, worse
     in edge cases), are handled, above all in naming.
  3. Results that repeat across distributions go through shared interfaces; nothing is derived as
     a one-off for a single distribution.
  4. Random matrices with orthonormal columns (normalised Gaussians) are a first-class
     distribution alongside Gaussian, sub-Gaussian, sparse and structured ones.

## Explorer documentation follow-up (2026-10-16)

- Complete on `feat/explorer-docs` in the existing library and explorer checkouts; the user
  requested separate local commits after validation.
  All 28 asymptotic forms have paired explorer views, 24 named bounds are supporting API,
  and 21 Lean files received comment-only corrections. No theorem statements or proofs changed.
- Design, read-back, independent reviews, residual citation follow-up and validation:
  `docs/design/Explorer-Documentation.md`. Full build and per-file checks, root checks,
  audit/lint/duplicate report, documentation checks, 19 regression tests and browser checks pass.
  Logs: `/tmp/nlalib-explorer-checks/`. Merge library changes before deploying the stricter
  explorer parser. No prototype work was added, so ledger dispositions are unchanged.
- Unrelated untracked files are untouched and excluded: the preexisting
  `docs/design/LowRank-S7.md` and the concurrently added
  `NLAlib/Sketching/Sparse/CountSketchEmbedding.lean`. Concurrent CountSketch source and
  constant-registry refactoring is also preserved in the working tree, outside this commit.

## Gaussian fourth-moment follow-up (2026-10-16)

- **Complete and independently reviewed**, branch `feat/gaussian-fourth-moments`, base
  `0daf947`; execution worktree `/tmp/nlalib-gaussian-fourth-moments`. User authorized exact
  Gaussian fourth moments and useful fourth-order Wick, then requested a local commit.
  No push was requested.
- Delivery worktree: `/home/tyler/Documents/NLA-lib/nlalib-gaussian-fourth-moments`, relocated
  after validation; the main checkout's ongoing work was preserved.
- `Probability/Distributions/GaussianMoments.lean` (182 lines, four public theorems) and
  `RandomMatrix/Gaussian/FourthMoment.lean` (300 lines, eight public theorems) are proved and
  registered. Headline results: fourth-order Wick, Gaussian vector linear-image fourth moment,
  sandwich fourth moment with factor-three bound, centered Gram error, exact normalized AMM
  error with factor-two bound. Normalized expectation formulas require nonempty sketch type;
  integrability includes empty sketch types. Full arbitrary-order Wick remains outside scope.
- Design and full statement read-backs: `docs/design/Gaussian-FourthMoments.md`, including the
  final stage report and honest available-model fallback for unavailable requested aliases.
  Independent bounded design/file/stage reviews approved; no new enduring interface, global
  instance, object, or placement deviation. R2's old scope cut has a dated follow-up amendment.
- Added verified `Isserlis1918`; reconsidered exactly twelve existing R2-cut ledger entries,
  preserving every other entry. Prototype coverage is zero missing of twelve declarations;
  generic Fubini and second-moment wrappers remain explicitly not reproduced via existing APIs.
- Checks: full `NLAlib NLAlibScaffold` build 3860 jobs, zero warnings; required stage check
  287 proved modules, zero unproved, build 3856 jobs, zero warnings; audit 6950 declarations,
  zero violations; 14 linters, 4856 plus 2094 generated declarations, zero errors; 55 reference
  keys, zero problems; constants and KaTeX clean; duplicate report 4461 theorems, zero classes.
  Both root checks passed; targeted reuse covers all twelve public theorems. Individual module
  and `lake lean` checks passed. Logs: `/tmp/nlalib-gaussian-fourth-checks`; see the stage report
  for exact checks and read-backs. Final `git diff --check` and ledger structural checks clean.

## Current

**Probability round started, 2026-10-14.** The maintainer decided §2 of `docs/PORT_PROBABILITY.md`
(all ten as recommended; D4 revised: `RCLike` wherever the proof allows, Gaussian and Haar matrix
laws real for now with complex analogues in view). `CONTRIBUTING.md` §5.1 and §5.2 ("Numerical
bounds") and `Mathlib-deviations.md` entries 12 and 13 are updated to match. Design checkpoint
for the maintainer after P3. Now: P0.

**P3 checkpoint passed (maintainer, 2026-10-14).** P0 §7 Q1 decided: `Matrix.Norms.L2Operator`
for matrix integrals (D10 amended; `Mathlib-deviations.md` entry 13; `CONTRIBUTING.md` §5.1 rule).
P4 proceeded on the orchestrator's recommendations (Lipschitz as `LipschitzWith` on
`EuclideanSpace`; the log-Sobolev route with constant `L²`), open to the maintainer's correction.

**Queue (orchestrator, 2026-10-14, latest):**
- **Probability round complete, 2026-10-14.** Every Probability and RandomMatrix stage proved and registered; round report `docs/design/Probability-REPORT.md`; final stage check in its §7.
- P5b, P5c, P5d proved (P5b mean constant 8; P5d bridge for deviation 17 proved); P7 in progress.
- P5b/P5c/P5d/P7 notes Fable-reviewed; findings and decisions in `/tmp/claude-1000/p0/review_p5bcd7.txt` (to be copied into each note's §8). P5d Q1 decided: conditional matrix MGF bound spelled with `μ[·|m]` (a.e. per θ), not `condExpKernel`; deviation entry 17; bridge from Mathlib's `HasCondSubgaussianMGF` needs `StandardBorelSpace` only there. P5b+P5c skeletons in progress; P5d+P7 skeletons next.
- R3 complete: `RandomMatrix/Gaussian/SpectralNorm.lean` and `RandomMatrix/Gaussian/ExtremeSingularValues.lean` proved and registered in `NLAlib.lean`; ledger R3 entries added.
- R3 `RandomMatrix/SubGaussian/ExtremeSingularValues.lean` proved (constant 24 reached) and registered. Stage check 2026-10-14: 200 proved modules (1 not yet), 0 warnings, audit 4681 declarations 0 violations, lint 0 errors (14 linters), 38 bib keys 0 problems.
- Proved and registered: P0–P5a, R1, R2 (stage checks green at 185 modules, before R4–R5).
- R4 `ChiSquareMoments.lean`, `InverseMoments.lean`, `InverseMoments/Spectral.lean` proved (split at 1490 lines); P6 `GaussianIntegrationByParts.lean`,
  `GaussianComparison.lean` (Opus).
- R5 complete: all six files proved (`PolarFrames`, `UnitaryInvariance`, `Haar/{Basic,Uniqueness,Moments,Transfer}`); deviation bridges 15 and 16 proved.
- P6 proved: `GaussianIntegrationByParts.lean`, `GaussianComparison.lean` (1035 lines, slightly over the soft limit); R5 `PolarFrames.lean`, `UnitaryInvariance.lean` proved.
- R4 complete: `RandomMatrix/Gaussian/BlockMoments.lean` proved and registered (with a transposed form for Nystrom that needs the rank hypothesis and gives the closed value); ledger R4 block entries added.
- Ledger keys are full prototype names with `NLAlib.` (fixed 2026-10-14; `ledger_missing.py NLAlib.Probability. NLAlib.RandomMatrix.` reports coverage: 302 of 921). Pending bookkeeping (Sonnet): ledger lines in `/tmp/claude-1000/p0/ledger_pending.txt` (may be
  lost on reboot: re-derive from agent reports in the design notes' stage reports if so) and the
  R4/P6/R3/R5 entries as they finish; register modules in `NLAlib.lean` once sorry-free;
  `stage_check.sh` after each stage.
- Wrap-up items (2026-10-14): done (R3 helpers public, Procrustes, unitary-group compactness in ForMathlib, P5a and P4 moves; the skeleton-era merges LaplaceGeneral into Laplace, RademacherSymmetry into Rademacher, GaussianIntegrationByPartsGrowth into GaussianIntegrationByParts (the bounded Stein identity now its `k = 0` corollary), EntropyExpBounded into Entropy; the P5b copies deleted for public originals `exp_div_rpow_rpow_eq_exp` (Chernoff, was `chernoff_base_rpow_eq`), `exp_integral_le_integral` (Laplace), `dilationCLM`, `memLp_dilation`, `iIndepFun_dilation`, `integral_dilation_eq_zero` (Bernstein, replacing `dilation_hypotheses`) and `Matrix.sum_fromBlocks` (new `ForMathlib/Data/Matrix/Block.lean`, replacing `sum_fromBlocks_diagonal` and its copy in Freedman); `bernsteinCoeff_nonneg` split into `mul_lt_three_of_mem_Ioo` and `sq_div_two_div_nonneg_of_mem_Ioo`; `condExp_cfc` public as `Matrix.IsHermitian.condExp_cfc` in `MatrixConditionalExpectation.lean`; Orlicz and BoundedDifferences registered in `NLAlib.lean`; P5b §8 records the mean constant 8, P7 §8 the reached constants and the entropy-lemma route); the P5a row is in the table.
  ForMathlib; `|s log s| ≤ s² + 1` duplicated (P4).
- Then to design (drafted by Opus agents from a brief): P5b (intrinsic dimension), P5c
  (Khintchine), P5d (Freedman, with matrix conditional expectations), P7 (bounded differences,
  Orlicz bridges, entropy extras); then the round report `docs/design/Probability-REPORT.md` and
  the ledger accounting for all prototype `Probability/`, `RandomMatrix/` declarations.

| Stage | File | Owner | State | Notes |
|---|---|---|---|---|
| P0 | design note `docs/design/Probability-P0.md` | orchestrator | written, Fable-reviewed | Q1 to the maintainer |
| P0 | `Probability/Law.lean`, `Tail.lean` | Opus agent | proved | `measureReal_abs_ge_le` needs no finiteness. Note for R1: `HasLaw.isProbabilityMeasure` does not find the `Measure.pi` instance at type `Measure (Matrix m n α)`; consider an instance for the nested product on matrices |
| P0 | `Probability/Isotropic.lean` | Opus agent | proved | `of_iIndepFun` needs no probability hypothesis (`iIndepFun` implies it) |
| P0 | checks on the proved part | orchestrator | done | `stage_check.sh`: 147 modules, 0 warnings, audit 3537 declarations 0 violations, lint 2714 clean, 34 keys; ledger +9 |
| P1 | design note `docs/design/Probability-P1.md` | orchestrator | written, Fable-reviewed | |
| P1 | `SubGaussian/Basic.lean`, `Moments.lean` | Opus agent | proved | `HasSubgaussianMGF.isFiniteMeasure` made public |
| P1 | `SubExponential/Basic.lean`, `Tail.lean` | Opus agent | proved | split at the skeleton (file budget); `measureReal_ge_le_of_le_mul` lost a redundant `0 ≤ t` |
| P1 | `SubGaussian/Square.lean` | Opus agent | proved | reached the literature's constants `32 c²`, `4 c`, now literals in the statement; stage report in the note |
| P2 | design note `docs/design/Probability-P2.md` | orchestrator | written, Fable-reviewed (§8 amendments) | |
| P2 | `Distributions/Rademacher.lean`, `Sampling.lean` | Opus agent | proved | `samplingMeasure_singleton` public |
| P2 | `Distributions/Gaussian.lean` | Opus agent | proved | |
| P0–P2 | checks | orchestrator | done | `stage_check.sh`: 155 modules, 0 warnings; audit 3697, 0 violations; lint 2818 clean; ledger +69 |
| P3 | design note `docs/design/Probability-P3.md` | orchestrator | written, Fable-reviewed (§8) | maintainer checkpoint after P3 |
| P3 | `SubGaussianVector/Basic.lean`, `Norm.lean` | Opus agent | proved | `IsSubgaussianVector.aemeasurable` public over `𝕜` |
| P3 | `Distributions/ChiSquare.lean`, `QuadraticForm/Moments.lean` | Opus agent | proved | Hutchinson's variance over `𝕜` with moment parameters |
| P3 | `QuadraticForm/HansonWright.lean` (+ `HansonWright/{LinearImage,OffDiagonal}.lean`) | Opus agent | proved | constant `1/196` (prototype `1/(256e²)`); 884 lines against 3,400 |
| P0–P3 | checks | orchestrator | done | `stage_check.sh`: 162 modules, 0 warnings; audit 3809, 0 violations; lint 2900 clean; `Result:` ids on the headline theorems; ledger +35 |
| P0–P3 | wrap-up (one public Gaussian linear-form MGF, `HasSubexponentialMGF.add`, tail-prefix rename) | Opus agent, orchestrator | done | stage review by Fable; ledger targets qualified (0 missing) |
| P0 | `Probability/MatrixIntegral.lean`, `ForMathlib/Analysis/CStarAlgebra/Matrix.lean` | Opus agent | proved | the Loewner closedness instance already existed (`ForMathlib/LinearAlgebra/Matrix/PosDef.lean`); the planned `Order.lean` dropped |
| P4 | design note `docs/design/Probability-P4.md`, skeletons | orchestrator | written, Fable-reviewed (§8); skeletons compile | |
| P4 | `Probability/Entropy.lean`, `EntropyTensorization.lean`, `ForMathlib/MeasureTheory/Constructions/PiUpdate.lean` | Opus agent, orchestrator | proved | split from one 722-line file |
| P4 | `Distributions/GaussianLogSobolev.lean`, `GaussianLogSobolevOneDim.lean` | Opus agent | proved | Gross's two-point route through Mathlib's CLT (the prototype's Ornstein–Uhlenbeck files not needed); wrap-up: one `ForMathlib` copy of `|s log s| ≤ s² + 1` |
| P4 | `LogSobolev.lean` (+ `ForMathlib/Analysis/Calculus/BumpFunction/Convolution.lean`) | Opus agent | proved | Lipschitz approximation by convolution |
| P4 | `Distributions/GaussianConcentration.lean` | Opus agent | proved | P4 complete; stage report and checks at the next quiet point |
| P5a | design note `docs/design/Probability-P5a.md`, skeletons `MatrixConcentration/*` | orchestrator | written, Fable-reviewed (§8); skeletons compile | |
| P5a | `MatrixConcentration/{Laplace,Subadditivity,MGFBound}.lean` (+ `ForMathlib/Analysis/Convex/Integral.lean`) | Opus agent | proved | Jensen on a non-closed convex set; wrap-up: move `continuousOn_cfc_log` to the Matrix layer, `measurableSet_posDef` to Measurability |
| P5a | `MatrixConcentration/{Chernoff,ChernoffSum}.lean` | Opus agent | proved | skeleton bug fixed: `∀ θ` had elaborated as `θ : ℕ` (rule added to CONTRIBUTING §5.2) |
| R1 | design note `docs/design/RandomMatrix-R1.md`, skeletons `RandomMatrix/Gaussian/*` | orchestrator | written, Fable-reviewed (§8); skeletons compile | `frobNorm_eq_norm_toLp_uncurry` proved in the Matrix layer |
| R1 | `RandomMatrix/Gaussian/{Basic,Invariance}.lean` | Opus agent | proved | |
| R1 | `RandomMatrix/Gaussian/{Rank,Concentration}.lean` | Opus agent | proved | |
| R2 | design note `docs/design/RandomMatrix-R2.md`, skeleton `RandomMatrix/Gaussian/Moments.lean` | Opus agent | proved | |
| R4 | design note `docs/design/RandomMatrix-R4.md`, skeletons | orchestrator | written, Fable-reviewed (§8); skeleton check pending a slot | |
| P5a | `MatrixConcentration/{Bernstein,Series}.lean` | Opus agent | proved | |
| P5a | wrap-up | orchestrator, Opus agent | done | moved the duplicated private `le_sqrt_of_forall_le_div_add_mul` (Bernstein, Series) to ForMathlib; `integrable_and_integral_cfc` (Series) to `MatrixIntegral.lean`; `continuousOn_cfc_log` to the Matrix layer; `measurableSet_posDef` to Measurability; note: under `Matrix.Norms.L2Operator`, `Continuous.measurable` finds no `BorelSpace (Matrix …)` |
| P5a | `MatrixConcentration/{Laplace,Subadditivity,MGFBound,Chernoff,ChernoffSum,Bernstein,Series}.lean` | Opus agents | proved | P5a complete: all seven files proved and registered, nothing in the scaffold library |

**Matrix layer complete, 2026-10-14** (branch `scaffold`, local commits, not pushed): stages M0 to
M10 proved, 144 files, nothing scaffolded, all checks green. Read `docs/design/Matrix-REPORT.md`
first. No design note was approved by the maintainer; the decisions to confirm are in §3 of the
report.

| Stage | File | Owner | State | Notes |
|---|---|---|---|---|
| M0 | bootstrap | orchestrator | done | see "M0 findings" |
| M1 | all 15 files | Opus agents | **done** | `docs/design/Matrix-Foundations.md` with stage report; not maintainer-approved |
| M2 | all 8 files | Opus agents | **done** | `docs/design/Matrix-Norms.md` with stage report; not maintainer-approved |
| M3 | all 10 files | Opus agents | **done** | `docs/design/Matrix-Spectral.md` with stage report; not maintainer-approved |
| M3a | all 7 files | Opus agents | **done** | `docs/design/Matrix-Majorization.md` with stage report; not maintainer-approved |
| M3b | all 8 files | Opus agents | **done** | `docs/design/Matrix-InvariantNorms.md` with stage report; not maintainer-approved |
| M5 | design note `docs/design/Matrix-Subspaces.md`, skeleton of 5 files under `Matrix/Subspaces/` | orchestrator | done, Fable-reviewed, not maintainer-approved | distance is `(1 - Q) * P` in a norm; `principalAngle`; `tangentMatrix` |
| M5 | `Subspaces/ProjectorPair.lean`, `Frames.lean` | Opus agent | proved | |
| M5 | `Subspaces/PrincipalAngles.lean`, `Oblique.lean` | Opus agent | proved | `PrincipalAngles.lean` is 530 lines: split tangents and frame alignment off at wrap-up; publish four helpers |
| M5 | `Subspaces/CSDecomposition.lean` | Opus agent | proved | wrap-up: drop `card p ≤ card q` where unused, add `singularValues U.toBlocks₁₂ = singularValues U.toBlocks₂₁` |
| M6 | `Perturbation/Sylvester.lean`, `Inverse.lean`, `Relative.lean` | Opus agents | proved | `specNorm_sub_smul_one_le_of_le` was false for size zero with `b < a`; `(hab : a ≤ b)` added |
| M6 | `Perturbation/Residual.lean`, `Pseudoinverse.lean` | Opus agent | proved | golden-ratio block lemma moved to `Norms/Projector.lean` |
| M6 | `Perturbation/DavisKahan.lean` | Opus agent | proved | 752 lines: split the gap forms off at wrap-up |
| M6 | `Perturbation/LeastSquares.lean`, `Continuity.lean` | Opus agent | proved | `isLeast_matrixNorm_sub_of_rank_le` moved to `Norms/UnitarilyInvariant.lean` |
| M6 | `Perturbation/Wedin.lean`, `SimpleEigenvalue.lean` | Opus agent | proved | simple eigenvalue branch by the implicit function theorem on the characteristic polynomial |
| M5, M6 | wrap-up (file splits `Subspaces/Tangent.lean`, `Perturbation/DavisKahanGap.lean`; published helpers; review follow-ups) | Opus agent | done | build, audit (1827 declarations), lint (1461) and references clean; stage reports in the two notes; the ledger accounts for every prototype `Subspaces/` and `Perturbation/` declaration (368 lines added by a bookkeeping agent: 185 mapped, 183 null with reasons) |
| M7 | `Inequalities/Order.lean`, `Block.lean` | Opus agent | proved | two condition-number bounds were false for size zero with `b < 0`; `(hb : 0 ≤ b)` added |
| M7 | `Inequalities/Determinant.lean`, `Kantorovich.lean` | Opus agent | proved | `Determinant.lean` is 582 lines: split the Minkowski section off at wrap-up |
| M7 | `Inequalities/SchurHorn.lean` | Opus agent | proved | Horn's converse by induction with plane rotations, not the prototype's descent |
| M7 | `Inequalities/PrincipalMinors.lean`, `HadamardProduct.lean`, `ForMathlib/LinearAlgebra/Matrix/Hadamard.lean` | Opus agent | proved | Oppenheim by a new induction through Schur complements |
| M7 | `Inequalities/EntrywiseFunctions.lean` and stage wrap-up | Opus agent | done | `Inequalities/Minkowski.lean` split off `Determinant.lean`; majorization companions published; build, audit (1979 declarations), lint (1583) and references clean; stage report in the note; ledger completion for the prototype `Inequalities/` leftovers in progress |
| M9 | `Factorizations/Triangular.lean`, `Elimination.lean` | Opus agent | proved | `Elimination.lean` is 743 lines: the `gaussState` part moves to `GaussState.lean` |
| M9 | `Factorizations/LU.lean`, `Cholesky.lean`, `GaussState.lean` (split off `Elimination.lean`) | Opus agent | proved | the rank pattern of pivoted Cholesky, unproved in the prototype, is proved |
| M9 | `Factorizations/QR.lean`, `GramSchmidt.lean` | Opus agent | proved | existence from Mathlib's `gramSchmidtOrthonormalBasis` on zero-padded columns |
| M9 | `Factorizations/Householder.lean`, `Givens.lean` | Opus agent | proved | |
| M9 | `Factorizations/Hessenberg.lean`, `RankRevealing.lean`, `ColumnVolume.lean` (split off) | Opus agent | proved | Hessenberg reduction, the Hessenberg QR and the implicit Q theorem, unproved in the prototype, are proved |
| M10 | `Spectral/Schur.lean`, `EigenvalueListing.lean` (split off), `Structured/Walsh.lean`, `Structured/Cauchy.lean` | Opus agent | proved | unitary Schur from the field similarity plus a QR factorization; Hilbert matrix positive definite through `posDef_iff_eliminationStep` |
| M10 | `Spectral/Normal.lean`, `Simultaneous.lean`, `Diagonalizable.lean`, `EigenvectorPairing.lean`, `SylvesterEquation.lean` (split off) | Opus agent | proved | commuting families over `𝕜` with split characteristic polynomials; simple-eigenvalue pairing over any field |
| M10 | `Spectral/Inertia.lean`, `InertiaElimination.lean`, `SylvesterCriterion.lean`, `RankOneUpdate.lean`, `InterlacingConverse.lean` (two split off) | Opus agent | proved | Sylvester's criterion by interlacing, no pivots; both interlacing converses proved |
| M10 | `Spectral/Congruence.lean`, `ForMathlib/MeasureTheory/Matrix.lean`, `Measurability/Basic.lean` | Opus agent | proved | all M10 files proved, nothing in the scaffold library; QZ by Schur of `B⁻¹ A` and a compactness limit |
| M10 | stage wrap-up | Opus agent | done | |
| all | gap-closing additions from the downstream audit | Opus agent | done | `docs/port/matrix-downstream-audit.md`; new files `Spectral/LeastSingularValue.lean`, `Basic/ComplementaryProjector.lean` |
| all | final checks and report | orchestrator | **done** | full build of `NLAlib` and `NLAlibScaffold` with no warnings; audit 3493 declarations, 0 violations; lint 2680 clean; 32 bibliography keys, 0 problems; ledger 2734 of 2734 accounted; `docs/design/Matrix-REPORT.md` |
| M5 to M9 | follow-up additions from the ledger passes | Opus agent | done | idempotents in oblique form, invariance of principal angles, `Spectral/ProjectedLowRank.lean` (truncation step of the randomized SVD), compression determinant bound, `frobInner_polarFactor`, `givens_apply` |
| M10 | `Spectral/Gershgorin.lean`, `HermitianPart.lean`, `Structured/Kronecker.lean`, `Circulant.lean` | Opus agent | proved | |
| M10 | `Spectral/SpectralRadius.lean`, `PowerBounds.lean`, `QuasiTriangular.lean`, `RealSchur.lean`, `RealSimilarity.lean` (three split off) | Opus agent | proved | real Schur, the real normal form and real QZ by one deflation through a one- or two-dimensional invariant subspace |
| M8 | `Functions/HermitianCalculus.lean`, `ForMathlib/Analysis/RCLike/ToComplex.lean`, `ForMathlib/Analysis/Calculus/Deriv/Matrix.lean` | Opus agent | proved | diagonalisation lemmas to be restated for a frame `U : Matrix n r 𝕜` with `card r = card n`, the shape the spectral theorem of M3 produces |
| M8 | `Functions/Polynomial.lean`, `Exponential.lean` | Opus agent | proved | |
| M8 | `Functions/Complexification.lean`, `TraceFunctions.lean` | Opus agent | proved | convexity of trace functions through Jensen for quadratic forms (Peierls), Klein from the generalized Klein inequality |
| M8 | `Functions/OperatorMonotone.lean`, `GoldenThompson.lean` | Opus agent | proved | Golden–Thompson by the Lie product formula over `𝕜` (the prototype derived it from Lieb's theorem); `OperatorMonotone.lean` is 596 lines, split at wrap-up |
| M8 | `Functions/Perspective.lean`, `Lieb.lean`, `OperatorConvex.lean` (split off `OperatorMonotone.lean`) | Opus agent | proved | Lieb's concavity theorem over `𝕜` on any index type; joint convexity of the relative entropy through Kronecker products |
| M8 | `Functions/TracePowers.lean`, `LogDet.lean`, `AbsoluteValue.lean` | Opus agent | proved | all thirteen M8 files proved; wrap-up pending |
| M9 | `Factorizations/Polar.lean`, `Procrustes.lean` and stage wrap-up (`Nystrom.lean`, `LUGeneral.lean`) | Opus agent | done | all sixteen M9 files proved, nothing in the scaffold library; stage checks and ledger completion pending |
| M8 | stage wrap-up | Opus agent | done | stage report in `Matrix-Functions.md` §9 |
| M8, M9 | stage checks | orchestrator | done | build no warnings; audit 2963 declarations, 0 violations; lint 2280 clean; refs clean; ledger complete for prototype `Functions`, `Calculus`, `Factorizations`, `Basic` |
| M6 | design note `docs/design/Matrix-Perturbation.md`, skeleton of 10 files under `Matrix/Perturbation/` | orchestrator | done, Fable-reviewed, not maintainer-approved | Davis–Kahan in residual form at three levels; one review proposal rejected (false under repeated eigenvalues) |
| M7 | design note `docs/design/Matrix-Inequalities.md`, skeleton of 8 files under `Matrix/Inequalities/` | orchestrator | done, Fable-reviewed, not maintainer-approved | spectral equivalence as a Loewner sandwich; `principalMinor`; determinants through `RCLike.re` |
| M8 | design note `docs/design/Matrix-Functions.md`, skeleton of 12 files under `Matrix/Functions/`, `ForMathlib/Analysis/Calculus/Deriv/Matrix.lean`, `ForMathlib/Analysis/RCLike/ToComplex.lean` | orchestrator | done, Fable-reviewed, not maintainer-approved | `cfc f A` is the spelling of `f(A)`; no `matrixExp`/`traceExp`/`lambdaMax` names; results over `𝕜` through `complexify`; entrywise derivatives |
| M9 | design note `docs/design/Matrix-Factorizations.md`, skeleton of 11 files under `Matrix/Factorizations/` | orchestrator | done, Fable-reviewed, not maintainer-approved | step-indexed recursions with breakdown as a value; `eliminationStep`/`gaussState` shared by LU and Cholesky; leading minors as `principalMinor A (Finset.Iic i)`; `polarFactor`; `IsLocalMaxVolume` certificate for rank-revealing column selection |
| M10 | design note `docs/design/Matrix-Structured.md`, skeleton of 18 files under `Matrix/Structured/`, `Matrix/Spectral/`, `Matrix/Measurability/`, `ForMathlib/MeasureTheory/` | orchestrator | done, Fable-reviewed, not maintainer-approved | eigenvalue listings `IsEigenvalueListing A d`; `inertiaPos`/`inertiaNeg` through `eigenvalue`; real-valued `specRadius`; `IsDiagonalizable`; `fourierMatrix`, `walshHadamard`; `Matrix.instMeasurableSpace` |
| M4 | all 6 files | Opus agents | **done** | `docs/design/Matrix-Pseudoinverse.md` with stage report; not maintainer-approved. One designed statement was false (empty column type) and gained `0 ≤ b` |

Stage order after M3, changed by the M3 and M4 notes: **M4** (pseudoinverse, least squares) →
**M3a** (majorization, Ky Fan sums, von Neumann trace inequality, Hoffman–Wielandt, Mirsky,
Lidskii) → **M3b** (Schatten, nuclear, Ky Fan and unitarily invariant norms) → M5 → M6 → M7 (the
rest of the inequalities) → M8 → M9 → M10.

While a stage is being proved, `import NLAlib` contains `sorry` and `scripts/Audit.lean` fails.
That is the expected state between a stage's skeleton and its last proof.

## M2 result (2026-10-14)

- 8 files, 2022 lines under `Matrix/Norms/` plus
  `ForMathlib/Topology/MetricSpace/CoveringNumbers.lean`: `Frobenius`, `Spectral`, `Compare`,
  `Loewner`, `Block`, `Projector`, `Net`.
- Checks on M1 + M2 + the two proved M3 eigenvalue files (25 modules): build with no warnings;
  axiom audit, 563 constants, 0 violations; `#lint` clean on 468 declarations; `check_refs.py`
  clean.
- Nothing in `NLAlibScaffold`. The volumetric net bound, expected to be scaffolded, was proved.
- `frobSq` is gone from the vocabulary; CONTRIBUTING §5.3 was amended (Frobenius row, scalar
  multiples of the identity, Loewner form of spectral bounds, nets).
- Ledger: every declaration of the prototype's `Norms/{Core, Frobenius, SpectralNormBounds,
  BlockNormBounds, EntryBounds, EuclideanOperatorBounds, RayleighNorm, Net, ColumnNorms, Reindex}`
  is accounted for. The Schatten, nuclear, Ky Fan, invariant-norm and rectangular-diagonal files
  wait for M3b.

## M1 result (2026-10-14)

- 15 files, 2707 lines, 229 declarations: `ForMathlib/LinearAlgebra/Matrix/{Rank, PosDef,
  Adjugate, SchurComplement, CauchyBinet}`, `ForMathlib/Analysis/InnerProductSpace/PiL2`,
  `Matrix/Basic/{Orthonormal, QuadForm, Gram, Projector, OrthonormalBasis, SchurComplement,
  Selection, Dilation, PlaneRotation}`.
- Checks on the M1 modules alone: build with no warnings; axiom audit, 282 constants, 0
  violations; `#lint`, 14 linters, clean; `check_refs.py` clean.
- Nothing in `NLAlibScaffold`.
- `Projector.lean` is 510 lines after the split.
- Ledger: 165 prototype declarations accounted for. Left for later stages: Moore–Penrose,
  pseudoinverse, least squares, generalized Schur complement (M4); leading minors and the pivot
  Schur step (M9); projector norm lemmas (M2).
- `scripts/check_refs.py` rejected the docstring ending `Result: id -/` that CONTRIBUTING §6 shows
  as the example. The script was fixed to accept it.
- New scripts: `scripts/ledger_add.py` (add entries from `old -> new` lines) and
  `scripts/ledger_missing.py` (list prototype declarations the ledger does not account for).
- `docs/port/proof-agent-brief.md` is the standing brief given to every proof agent.

## M0 findings (2026-10-14)

- `lake update` resolves Mathlib tag `v4.33.1` to commit `0df444a3`, the prototype's pin. The
  Mathlib cache was already on the machine; `lake exe cache get` decompresses it in half a minute.
- **Lake 5.0.0 has no `-j` flag.** `lake build -j 4` fails with `unknown short option '-j'`. The
  cap that works is the environment variable: `LEAN_NUM_THREADS=4 lake build <targets>` runs at
  most 4 Lean processes (measured 1, 2, 4 for values 1, 2, 4 on a ten-file test project; 10
  without it). CONTRIBUTING §9 and §10, AGENTS.md, README, the PR template and the port brief were
  changed from `lake build -j N` to `LEAN_NUM_THREADS=N lake build`.
- **`mk_all` needs `--module` the first time.** Without it the root file is generated with plain
  `import`. With `lake exe mk_all --module --lib NLAlib` it is `module` plus `public import`.
  Later runs infer the style from the existing file, so `--check` in CI needs no flag. `mk_all`
  exits 1 when it rewrites a file; that is not a failure.
- **`lake env lean <file>` ignores `lakefile.toml` options.** `autoImplicit` is then on and the
  Mathlib linter set is off, so a skeleton can look clean and be wrong. The single-file check is
  `LEAN_NUM_THREADS=2 lake lean <file> -- -M 8000`. The docs were changed to this form. The
  scripts `Audit.lean` and `Lint.lean` are still run with `lake env lean`.
- The file template of CONTRIBUTING §3 compiles as written: `module`, `public import`,
  `@[expose] public section`. Header linter, `scripts/Audit.lean`, `scripts/Lint.lean` and
  `scripts/check_refs.py` all pass on the first file (`NLAlib/Matrix/Basic/Orthonormal.lean`).
- `lake-manifest.json` is generated and should be committed with the first commit.

## In NLAlibScaffold

Nothing. Every statement of the Matrix layer is proved (2026-10-14).
