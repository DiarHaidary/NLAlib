# Stage 2 worklist: the rules debt left in the ratchet

Regenerated on 2026-10-20 at the end of stage 2 of the rules enforcement (branch `rules/stage2`)
from `scripts/rules_baseline.json`: 88 baselined errors, down from 399 at the end of stage 1
(73 after stage 3, which cleared P9 and T9).
Every item below is a baselined error of `scripts/check_rules.py`; fixing one lowers the baseline
(`python3 scripts/check_rules.py DATA.json --update-baseline`, CONTRIBUTING §9.1). Stage 2 cleared
D1, D2, G1, M2, P8, S4, T2 and T13; its renames and statement changes are in
`docs/renames/2026-10-rules.json`. Run `python3 scripts/check_rules.py --files <file>` for the
current list of a file.

What is left, and what each needs:

- **C1** (31) and **C2** (42): a printed label that someone has checked in the source. None of
  these sources could be read openly: DavisKahan1970, Wedin1972, Wedin1973 (SIAM, BIT);
  Szyld2006 (only the author's report 05-12-30 was readable, whose numbering may differ from the
  Numerical Algorithms version: Theorem 2.1, the second proof of Theorem 2.1 and Theorem 6.1
  there are the candidate labels); Greenbaum1979, GreenbaumGurvits1994, Greenbaum1997,
  ElmanSilvesterWathen2014; McDiarmid1989 (the P7 reviewer reads Lemma (1.2)), Kahane1986,
  Gordon1985, KuczynskiWozniakowski1992, BoucheronLugosiMassart2013,
  KuratowskiRyllNardzewski1965. The C1 items in Matrix are textbook facts (Eckart–Young, SVD
  uniqueness, Sylvester inertia, Haynsworth, Ky Fan equality, Cholesky existence) awaiting a
  readable textbook locator. Two C1 items need a bibliography entry first (Hsu–Kakade–Zhang 2012,
  Theorem 2.1, for the sub-Gaussian norm tail; Ville 1939 or a textbook for Ville's inequality).
  The six Haar subspace-embedding results have no printed source found: either "No printed
  source." (if these Gaussian-transfer bounds count as the library's own) or a source.
- **P9** and **T9** were settled by the maintainer's decisions of 2026-10-20 and cleared in stage 3
  (branch `rules/stage3`): `lpGauge` takes `[Fact (1 ≤ q)]`, `HasCondMatrixMGFBound` drops `hm`,
  the Polynomial layer is exempt from P9 while P11 holds, and Weyl's majorant lemma is
  allowlisted. The baseline is 73 errors after stage 3.

## Matrix (42)

**C1** (15)

- `NLAlib/Matrix/Basic/SchurComplement.lean:177` `Matrix.PosSemidef.quadForm_sub_conjTranspose_mul_mul_le`
- `NLAlib/Matrix/Factorizations/Cholesky.lean:394` `NLAlib.exists_isCholesky_iff_posDef`
- `NLAlib/Matrix/Functions/LogDet.lean:307` `NLAlib.strictConvexOn_re_trace_inv`
- `NLAlib/Matrix/Inequalities/Order.lean:347` `NLAlib.pseudoConditionNumber_conjTranspose_mul_mul_le_div`
- `NLAlib/Matrix/Majorization/KyFan.lean:79` `Matrix.IsHermitian.exists_re_trace_conjTranspose_mul_mul_eq_sum_eigenvalue`
- `NLAlib/Matrix/Majorization/KyFan.lean:354` `NLAlib.exists_trace_conjTranspose_mul_mul_eq_kyFanNorm`
- `NLAlib/Matrix/Norms/Nuclear.lean:277` `NLAlib.isGreatest_frobInner_specNorm`
- `NLAlib/Matrix/Perturbation/DavisKahan.lean:123` `NLAlib.SymmetricGauge.mul_matrixNorm_conjTranspose_mul_le_of_le`
- `NLAlib/Matrix/Perturbation/Wedin.lean:476` `NLAlib.HasOrthonormalCols.max_specNorm_one_sub_mul_le_two_mul_specNorm_div_singularGap`
- `NLAlib/Matrix/Spectral/Inertia.lean:328` `Matrix.IsHermitian.inertiaNeg_conjTranspose_mul_mul`
- `NLAlib/Matrix/Spectral/InertiaElimination.lean:167` `Matrix.IsHermitian.inertiaNeg_fromBlocks`
- `NLAlib/Matrix/Spectral/LowRank.lean:640` `NLAlib.isLeast_specNorm_sub_of_rank_le`
- `NLAlib/Matrix/Spectral/LowRank.lean:652` `NLAlib.isLeast_frobNorm_sub_of_rank_le`
- `NLAlib/Matrix/Spectral/SVD.lean:249` `NLAlib.IsSVD.singularValues_eq`
- `NLAlib/Matrix/Subspaces/ProjectorPair.lean:486` `IsStarProjection.specNorm_sub_eq_of_rank_eq`

**C2** (27)

- `NLAlib/Matrix/Perturbation/Continuity.lean:270` `NLAlib.continuousOn_pinv_setOf_rank_eq` — [Wedin1973]
- `NLAlib/Matrix/Perturbation/DavisKahan.lean:94` `NLAlib.SymmetricGauge.mul_matrixNorm_conjTranspose_mul_le_of_eigenvalue` — [DavisKahan1970]
- `NLAlib/Matrix/Perturbation/DavisKahan.lean:132` `Matrix.IsHermitian.mul_frobNorm_conjTranspose_mul_le` — [DavisKahan1970]
- `NLAlib/Matrix/Perturbation/DavisKahan.lean:196` `NLAlib.SymmetricGauge.mul_matrixNorm_mul_le_of_mul_mul_le` — [DavisKahan1970]
- `NLAlib/Matrix/Perturbation/DavisKahan.lean:441` `NLAlib.SymmetricGauge.mul_matrixNorm_one_sub_mul_le_of_add_smul_one_le` — [DavisKahan1970]
- `NLAlib/Matrix/Perturbation/DavisKahan.lean:467` `NLAlib.SymmetricGauge.mul_matrixNorm_conjTranspose_mul_le_of_mul_eq_mul` — [DavisKahan1970]
- `NLAlib/Matrix/Perturbation/DavisKahan.lean:487` `NLAlib.SymmetricGauge.mul_matrixNorm_one_sub_mul_le_of_eigenvalue_sub` — [DavisKahan1970]
- `NLAlib/Matrix/Perturbation/LeastSquares.lean:73` `NLAlib.IsLeastSquaresSolution.norm_sub_le` — [Wedin1973]
- `NLAlib/Matrix/Perturbation/Pseudoinverse.lean:199` `NLAlib.SymmetricGauge.matrixNorm_pinv_sub_pinv_le` — [Wedin1973]
- `NLAlib/Matrix/Perturbation/Pseudoinverse.lean:284` `NLAlib.specNorm_rangeProjector_sub_rangeProjector_le` — [Wedin1973]
- `NLAlib/Matrix/Perturbation/Pseudoinverse.lean:358` `NLAlib.SymmetricGauge.matrixNorm_pinv_sub_pinv_le_three_mul_of_rank_eq` — [Wedin1973]
- `NLAlib/Matrix/Perturbation/Pseudoinverse.lean:385` `NLAlib.specNorm_pinv_sub_pinv_le_goldenRatio_mul_of_rank_eq` — [Wedin1973]
- `NLAlib/Matrix/Perturbation/Pseudoinverse.lean:436` `NLAlib.frobNorm_pinv_sub_pinv_le_sqrt_two_mul_of_rank_eq` — [Wedin1973]
- `NLAlib/Matrix/Perturbation/Pseudoinverse.lean:482` `NLAlib.specNorm_pinv_le_div_of_rank_eq` — [Wedin1973]
- `NLAlib/Matrix/Perturbation/Sylvester.lean:125` `NLAlib.SymmetricGauge.mul_matrixNorm_le_matrixNorm_mul_sub_mul_of_eigenvalue` — [DavisKahan1970]
- `NLAlib/Matrix/Perturbation/Wedin.lean:112` `NLAlib.SymmetricGauge.sub_mul_max_matrixNorm_le_max` — [Wedin1972]
- `NLAlib/Matrix/Perturbation/Wedin.lean:142` `NLAlib.sub_sq_mul_frobNorm_sq_add_frobNorm_sq_le` — [Wedin1972]
- `NLAlib/Matrix/Perturbation/Wedin.lean:323` `NLAlib.SymmetricGauge.sub_mul_max_matrixNorm_one_sub_mul_le_max` — [Wedin1972]
- `NLAlib/Matrix/Perturbation/Wedin.lean:359` `NLAlib.HasOrthonormalCols.sub_sq_mul_frobNorm_one_sub_mul_sq_add_le` — [Wedin1972]
- `NLAlib/Matrix/Perturbation/Wedin.lean:393` `NLAlib.SymmetricGauge.mul_max_matrixNorm_one_sub_mul_le_of_singularValues_sub` — [Wedin1972]
- `NLAlib/Matrix/Perturbation/Wedin.lean:429` `NLAlib.HasOrthonormalCols.sq_mul_frobNorm_one_sub_mul_sq_add_le_of_singularValues_sub` — [Wedin1972]
- `NLAlib/Matrix/Subspaces/Oblique.lean:169` `IsIdempotentElem.specNorm_sq` — [Szyld2006]
- `NLAlib/Matrix/Subspaces/Oblique.lean:208` `IsIdempotentElem.specNorm_one_sub` — [Szyld2006]
- `NLAlib/Matrix/Subspaces/Oblique.lean:228` `IsIdempotentElem.specNorm_mul_cos_principalAngle` — [Szyld2006]
- `NLAlib/Matrix/Subspaces/Oblique.lean:355` `NLAlib.HasOrthonormalCols.specNorm_mul_inv_mul_conjTranspose` — [Szyld2006]
- `NLAlib/Matrix/Subspaces/ObliqueBases.lean:79` `NLAlib.HasOrthonormalCols.specNorm_obliqueProjector` — [Szyld2006]
- `NLAlib/Matrix/Subspaces/ObliqueBases.lean:94` `NLAlib.HasOrthonormalCols.specNorm_obliqueProjector_mul_cos` — [Szyld2006]

## Polynomial (1)

**C2** (1)

- `NLAlib/Polynomial/Chebyshev/ResidualMinimax.lean:247` `NLAlib.exists_residualMinimax_sq_le_sum_mul_norm_sq` — [Greenbaum1979]

## Probability (8)

**C1** (1)

- `NLAlib/Probability/SubGaussianVector/Norm.lean:448` `NLAlib.IsSubgaussianVector.measureReal_norm_mulVec_sq_ge_le`

**C2** (7)

- `NLAlib/Probability/BoundedDifferences.lean:135` `NLAlib.hasSubgaussianMGF_sub_integral_of_abs_update_sub_le` — [McDiarmid1989]
- `NLAlib/Probability/BoundedDifferences.lean:158` `NLAlib.measureReal_sub_integral_ge_le_mcdiarmid` — [McDiarmid1989]
- `NLAlib/Probability/Distributions/GaussianComparison.lean:419` `NLAlib.integral_comp_le_integral_comp_of_hasGaussianLaw` — [Kahane1986]
- `NLAlib/Probability/Distributions/GaussianComparison.lean:1031` `NLAlib.integral_iInf_iSup_le_integral_iInf_iSup_of_hasGaussianLaw` — [Gordon1985]
- `NLAlib/Probability/Distributions/GaussianLogOverlap.lean:457` `NLAlib.measureReal_log_norm_sq_div_sq_ge_le_of_hasLaw_gaussianVector` — [KuczynskiWozniakowski1992]
- `NLAlib/Probability/Distributions/GaussianLogOverlap.lean:491` `NLAlib.integral_log_norm_sq_div_sq_le_of_hasLaw_gaussianVector` — [KuczynskiWozniakowski1992]
- `NLAlib/Probability/Tail.lean:210` `NLAlib.measureReal_ge_le_exp_neg_of_mgf_le` — [BoucheronLugosiMassart2013]

## Krylov (13)

**C1** (8)

- `NLAlib/Krylov/LinearSystems/MINRES.lean:181` `Matrix.IsHermitian.norm_sub_mulVec_gmresIterate_le_two_mul_pow_of_forall_le`
- `NLAlib/Krylov/LinearSystems/MINRES.lean:329` `NLAlib.pminresIterate_eq_mulVec_gmresIterate`
- `NLAlib/Krylov/LinearSystems/MINRES.lean:380` `Matrix.IsHermitian.re_quadForm_sub_mulVec_pminresIterate_le`
- `NLAlib/Krylov/LinearSystems/MINRES.lean:455` `NLAlib.pminresIterate_eq_of_krylovGrade_le`
- `NLAlib/Krylov/LinearSystems/PCG.lean:263` `Matrix.PosDef.re_quadForm_sub_pcgIterate_le_four_mul_sq_mul_pow`
- `NLAlib/Krylov/LinearSystems/WorstCase.lean:223` `NLAlib.re_quadForm_sub_cgIterate_chebyshevExtremaMatrix_eq_four_mul_pow_div`
- `NLAlib/Krylov/Processes/Lanczos.lean:191` `NLAlib.IsGradedKrylovBasis.eq_arnoldiMatrix`
- `NLAlib/Krylov/Processes/PreconditionedLanczos.lean:269` `Matrix.IsHermitian.preconditionedLanczosTridiagonal_eq`

**C2** (5)

- `NLAlib/Krylov/Functions/Optimality.lean:396` `Matrix.PosDef.exists_inv_add_le_re_quadForm_cfc_cfc_mulVec_sub_lanczosFA` — [Greenbaum1979]
- `NLAlib/Krylov/LinearSystems/WorstCase.lean:503` `Matrix.PosDef.exists_re_quadForm_sub_cgIterate_eq_residualMinimax_sq_mul` — [Greenbaum1979]
- `NLAlib/Krylov/LinearSystems/WorstCase.lean:553` `Matrix.PosDef.isGreatest_re_quadForm_sub_cgIterate_div` — [Greenbaum1979]
- `NLAlib/Krylov/LinearSystems/WorstCase.lean:577` `Matrix.IsHermitian.exists_norm_sub_mulVec_gmresIterate_eq_residualMinimax_mul` — [GreenbaumGurvits1994]
- `NLAlib/Krylov/LinearSystems/WorstCase.lean:621` `Matrix.IsHermitian.isGreatest_norm_sub_mulVec_gmresIterate_div` — [GreenbaumGurvits1994]

## Sketching (6)

**C1** (6)

- `NLAlib/Sketching/Gaussian/HaarEmbedding.lean:323` `NLAlib.HasOrthonormalCols.hasSubspaceEmbedding_of_hasLaw_haarFrame`
- `NLAlib/Sketching/Gaussian/HaarEmbedding.lean:350` `NLAlib.HasOrthonormalCols.hasSubspaceEmbedding_of_hasLaw_haarFrame_of_lt_sqrt_sub_sqrt`
- `NLAlib/Sketching/Gaussian/HaarEmbedding.lean:546` `NLAlib.HasOrthonormalCols.hasSubspaceEmbedding_of_hasLaw_haarFrame_of_card_add_eq`
- `NLAlib/Sketching/Gaussian/HaarEmbedding.lean:596` `NLAlib.isObliviousSubspaceInjection_of_hasLaw_haarFrame`
- `NLAlib/Sketching/Gaussian/HaarEmbedding.lean:626` `NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_haarFrame`
- `NLAlib/Sketching/Gaussian/HaarEmbedding.lean:660` `NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_haarFrame_of_lt_sqrt_sub_sqrt`

## ForMathlib (3)

**C1** (1)

- `NLAlib/ForMathlib/Probability/Martingale/OptionalStopping.lean:40` `MeasureTheory.Supermartingale.measureReal_exists_ge_le`

**C2** (2)

- `NLAlib/ForMathlib/MeasureTheory/Constructions/BorelSpace/MeasurableSelection.lean:162` `IsClosed.measurable_of_forall_toLex_equivFun_le` — [KuratowskiRyllNardzewski1965]
- `NLAlib/ForMathlib/MeasureTheory/Constructions/BorelSpace/MeasurableSelection.lean:189` `IsClosed.exists_measurable_forall_prodMk_mem` — [KuratowskiRyllNardzewski1965]

## Explorer follow-ups (the explore repository is not edited from here)

- **Result ids removed from definitions** (R1, decision 9). `collections.toml` line 85 lists the
  results `ose-def`, `osi-def` and `subspace-injection`, which no declaration carries any more;
  drop them (the definitions are already in that collection's `definitions` list, line 84). The
  id `leverage-scores` (on `NLAlib.leverageScore`) is in no explorer file; if the definition should
  be listed, add `NLAlib.leverageScore` to a collection's `definitions`. `HasProjectionCostPreserving`
  lost `projection-cost-preserving-sketch`, which its theorems still carry; it is in no
  `definitions` list today. `python3 scripts/check_rules.py --only R3 --explore-repo
  ~/Documents/NLA-lib/explore` lists every explorer id or name the library no longer has.
- **Jensen corollaries removed** (T15). `NLAlib.integral_frobNorm_sub_rsvd_le_of_hasLaw_gaussianMatrix`
  and `NLAlib.integral_frobNorm_sub_rsvd_le_of_isLeftUnitarilyInvariant` are gone; neither is named
  in `results.toml`, `rates.toml` or `collections.toml`. `docs/renames/2026-10-naming.json` lists
  them with `"removed": true` and their squared theorems as `new`; the explorer's redirect of old
  `#d/` links should read the new field.
- **Renames of P5.** The seven Hessian lemmas of `ForMathlib/Analysis/Calculus/ContDiff/Hessian.lean`
  lost their `NLAlib.` prefix (rename map, rule P5); none is named in the explorer's TOML.
- **Renames of stage 2.** `docs/renames/2026-10-rules.json` lists the 32 renames and removals
  of stage 2 (rules P8, P9, T13) and its 8 statement changes; none of the old names is in the
  explorer's TOML (checked 2026-10-20), so only the `#d/` redirects need the map.
- **Renames of stage 3.** `docs/renames/2026-10-rules.json` adds the six Polynomial renames of the
  upstreaming audit (rule P11) and the statement changes of `lpGauge` and
  `HasCondMatrixMGFBound`; none of the old names is in the explorer's TOML (checked 2026-10-20).
