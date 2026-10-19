# Stage 2 worklist: the rules debt left in the ratchet

Generated on 2026-10-20 from `scripts/rules_baseline.json` at the end of stage 1 of the rules
enforcement (branch `rules/enforcement`). Every item below is a baselined error of
`scripts/check_rules.py`; fixing one lowers the baseline (`python3 scripts/check_rules.py
DATA.json --update-baseline`, CONTRIBUTING §9.1). The items are grouped by topic directory so
that parallel agents can take one topic each; within a topic, by rule. Run
`python3 scripts/check_rules.py --files <file>` for the current list of a file.

What each rule needs:

- **C1** (65): a `Result:` declaration with no `[Key, label]` citation and no "No printed source.". Cite where the result is printed, `[Key, label]`, or write "No printed source." Needs the sources (Saad2003, Greenbaum1997, TrefethenBau1997 for Krylov).
- **C2** (86): a bare `[Key]` citation in a declaration docstring. Add the printed label to each bare `[Key]` in a declaration docstring. Needs the paper: the design notes withdrew several drafted locators as unverified (Probability-P7 §8 item 4 for McDiarmid1989; Sketching-S5 review A2 for Tropp2011a, Hoeffding1963, GrossNesme2010).
- **D1** (37): a `Result:` declaration whose docstring has no bold name. Give the `Result:` declaration a bold name in its first sentence.
- **D2** (47): the docstring defers its hypotheses or notation to another declaration. Restate the hypotheses and notation instead of "under the hypotheses of `X`" or "as there".
- **G1** (13): a Mathlib-deviations entry without all of Mathlib, NLAlib, Bridge, Why, Cost, Status. Fill the missing fields of the entry (Mathlib, NLAlib, Bridge, Why, Cost, Status).
- **M2** (34): a `Result:` theorem about an algorithm whose docstring never writes its output as `\mathsf{name}(…)`. Write the algorithm output as `\mathsf{name}(…)` (the Lean name, or a short name registered in CONTRIBUTING §5.3), e.g. $\mathbf{x}_k = \mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, k)$.
- **P8** (28): a declaration outside ForMathlib and outside `NLAlib`, not on a Mathlib hypothesis structure. Root-namespace declaration outside ForMathlib, not API of a Mathlib hypothesis structure: move it to ForMathlib, or into `NLAlib` (decision 5; a rename, listed in a rename map).
- **P9** (60): a general fact outside ForMathlib: a statement with no NLAlib, matrix or measure vocabulary (heuristic). General fact with no NLAlib, matrix or measure vocabulary: move it to the ForMathlib file of its Mathlib subject, in Mathlib's namespace (decision 5; a rename, listed in a rename map). Heuristic: a false positive goes on `scripts/rules_allow.toml` with a reason.
- **S4** (13): a proof over 80 lines. Split the proof (over 80 lines) into named lemmas.
- **T2** (1): `Real.toNNReal` in a statement. State the `ℝ≥0` quantity with `‖·‖₊`, not `Real.toNNReal` (a statement change).
- **T9** (12): a proof term inside a statement (`⋯` in the signature). Remove the proof term from the statement: take the hypothesis, or state through a definition (several come from `lpGauge p hp` and `⟨k, ⋯⟩ : Fin`).
- **T13** (3): a hypothesis named `_h…` in a public statement (unused, so the statement is not minimal). Drop the unused `_h` hypothesis, or allowlist it with the reason it is kept (a statement change).

## Matrix (118)

**C1** (16)

- `NLAlib/Matrix/Basic/SchurComplement.lean:177` `Matrix.PosSemidef.quadForm_sub_conjTranspose_mul_mul_le`
- `NLAlib/Matrix/Factorizations/Cholesky.lean:393` `NLAlib.exists_isCholesky_iff_posDef`
- `NLAlib/Matrix/Functions/HermitianCalculus.lean:452` `Matrix.IsHermitian.re_trace_cfc`
- `NLAlib/Matrix/Functions/LogDet.lean:307` `NLAlib.strictConvexOn_re_trace_inv`
- `NLAlib/Matrix/Inequalities/Order.lean:347` `NLAlib.pseudoConditionNumber_conjTranspose_mul_mul_le_div`
- `NLAlib/Matrix/Majorization/KyFan.lean:78` `Matrix.IsHermitian.exists_re_trace_conjTranspose_mul_mul_eq_sum_eigenvalue`
- `NLAlib/Matrix/Majorization/KyFan.lean:352` `NLAlib.exists_trace_conjTranspose_mul_mul_eq_kyFanNorm`
- `NLAlib/Matrix/Norms/Nuclear.lean:277` `NLAlib.isGreatest_frobInner_specNorm`
- `NLAlib/Matrix/Perturbation/DavisKahan.lean:123` `NLAlib.SymmetricGauge.mul_matrixNorm_conjTranspose_mul_le_of_le`
- `NLAlib/Matrix/Perturbation/Wedin.lean:476` `NLAlib.HasOrthonormalCols.max_specNorm_one_sub_mul_le_two_mul_specNorm_div_singularGap`
- `NLAlib/Matrix/Spectral/Inertia.lean:328` `Matrix.IsHermitian.inertiaNeg_conjTranspose_mul_mul`
- `NLAlib/Matrix/Spectral/InertiaElimination.lean:167` `Matrix.IsHermitian.inertiaNeg_fromBlocks`
- `NLAlib/Matrix/Spectral/LowRank.lean:640` `NLAlib.isLeast_specNorm_sub_of_rank_le`
- `NLAlib/Matrix/Spectral/LowRank.lean:652` `NLAlib.isLeast_frobNorm_sub_of_rank_le`
- `NLAlib/Matrix/Spectral/SVD.lean:248` `NLAlib.IsSVD.singularValues_eq`
- `NLAlib/Matrix/Subspaces/ProjectorPair.lean:486` `IsStarProjection.specNorm_sub_eq_of_rank_eq`

**C2** (31)

- `NLAlib/Matrix/Factorizations/GivensHessenberg.lean:122` `NLAlib.givensHessenbergR_apply_eq_zero_of_add_two_lt` — [PaigeSaunders1975]
- `NLAlib/Matrix/Functions/Lieb.lean:264` `NLAlib.convexOn_relativeEntropy` — [Lindblad1974]
- `NLAlib/Matrix/Functions/Lieb.lean:351` `Matrix.IsHermitian.concaveOn_re_trace_exp_add_cfc_log` — [Lieb1973]
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
- `NLAlib/Matrix/Subspaces/CSDecomposition.lean:186` `NLAlib.HasOrthonormalCols.exists_cs_decomposition` — [PaigeWei1994]
- `NLAlib/Matrix/Subspaces/Oblique.lean:169` `IsIdempotentElem.specNorm_sq` — [Szyld2006]
- `NLAlib/Matrix/Subspaces/Oblique.lean:208` `IsIdempotentElem.specNorm_one_sub` — [Szyld2006]
- `NLAlib/Matrix/Subspaces/Oblique.lean:228` `IsIdempotentElem.specNorm_mul_cos_principalAngle` — [Szyld2006]
- `NLAlib/Matrix/Subspaces/Oblique.lean:355` `NLAlib.HasOrthonormalCols.specNorm_mul_inv_mul_conjTranspose` — [Szyld2006]
- `NLAlib/Matrix/Subspaces/ObliqueBases.lean:79` `NLAlib.HasOrthonormalCols.specNorm_obliqueProjector` — [Szyld2006]
- `NLAlib/Matrix/Subspaces/ObliqueBases.lean:94` `NLAlib.HasOrthonormalCols.specNorm_obliqueProjector_mul_cos` — [Szyld2006]

**D1** (13)

- `NLAlib/Matrix/Majorization/KyFan.lean:78` `Matrix.IsHermitian.exists_re_trace_conjTranspose_mul_mul_eq_sum_eigenvalue`
- `NLAlib/Matrix/Majorization/KyFan.lean:147` `Matrix.IsHermitian.majorized_eigenvalue_add`
- `NLAlib/Matrix/Majorization/KyFan.lean:352` `NLAlib.exists_trace_conjTranspose_mul_mul_eq_kyFanNorm`
- `NLAlib/Matrix/Majorization/Lidskii.lean:243` `NLAlib.weaklyMajorized_abs_singularValues_add_sub`
- `NLAlib/Matrix/Majorization/Schur.lean:109` `Matrix.IsHermitian.sumLargest_re_diag_le_sum_eigenvalue`
- `NLAlib/Matrix/Majorization/TraceInequalities.lean:190` `NLAlib.abs_frobInner_le_sum_singularValues_mul`
- `NLAlib/Matrix/Perturbation/DavisKahan.lean:123` `NLAlib.SymmetricGauge.mul_matrixNorm_conjTranspose_mul_le_of_le`
- `NLAlib/Matrix/Spectral/CourantFischer.lean:437` `Matrix.IsHermitian.eigenvalue_zero_eq_iSup`
- `NLAlib/Matrix/Spectral/CourantFischer.lean:457` `Matrix.IsHermitian.eigenvalue_last_eq_iInf`
- `NLAlib/Matrix/Spectral/LowRank.lean:640` `NLAlib.isLeast_specNorm_sub_of_rank_le`
- `NLAlib/Matrix/Spectral/SVD.lean:248` `NLAlib.IsSVD.singularValues_eq`
- `NLAlib/Matrix/Subspaces/ObliqueBases.lean:101` `NLAlib.HasOrthonormalCols.specNorm_obliqueProjector_mul_cos`
- `NLAlib/Matrix/Subspaces/ProjectorPair.lean:486` `IsStarProjection.specNorm_sub_eq_of_rank_eq`

**D2** (2)

- `NLAlib/Matrix/Factorizations/NystromOrder.lean:549` `NLAlib.HasOrthonormalCols.nuclearNorm_fromBlocks_sub_nystrom_le`
- `NLAlib/Matrix/Inequalities/HadamardProduct.lean:137` `NLAlib.neg_hadamard_le_hadamard_of_neg_le_of_le`

**M2** (1)

- `NLAlib/Matrix/Factorizations/NystromOrder.lean:142` `NLAlib.sum_smul_sub_nystrom_le` — nystrom

**P8** (4)

- `NLAlib/Matrix/Basic/Projector.lean:61` `Matrix.isStarProjection_iff` — Matrix
- `NLAlib/Matrix/Functions/Complexification.lean:151` `Commute.complexify` — Commute
- `NLAlib/Matrix/Functions/Polynomial.lean:289` `Matrix.mul_pow_mul` — Matrix
- `NLAlib/Matrix/Norms/Net.lean:57` `Metric.IsCover.exists_mem_norm_toLp_sub_le` — Metric.IsCover

**P9** (38)

- `NLAlib/Matrix/Basic/PlaneRotation.lean:149` `NLAlib.sq_div_add_sq_div_one_add_sq`
- `NLAlib/Matrix/Basic/QuadForm.lean:188` `NLAlib.isHermitian_real_smul_one`
- `NLAlib/Matrix/Factorizations/GaussState.lean:383` `NLAlib.exists_perm_forall_le_apply_self`
- `NLAlib/Matrix/Factorizations/Givens.lean:398` `NLAlib.givensHessenbergStep_plane_ne`
- `NLAlib/Matrix/Functions/Complexification.lean:318` `NLAlib.continuousOn_cfc_log`
- `NLAlib/Matrix/Functions/Exponential.lean:399` `NLAlib.continuous_re_trace_exp`
- `NLAlib/Matrix/Functions/HermitianCalculus.lean:174` `NLAlib.cfc_diagonal`
- `NLAlib/Matrix/Functions/LogDet.lean:194` `NLAlib.strictConcaveOn_log_re_det`
- `NLAlib/Matrix/Functions/LogDet.lean:302` `NLAlib.strictConvexOn_re_trace_inv`
- `NLAlib/Matrix/Functions/OperatorMonotone.lean:97` `NLAlib.concaveOn_rpow`
- `NLAlib/Matrix/Functions/Polynomial.lean:61` `NLAlib.aeval_diagonal`
- `NLAlib/Matrix/Functions/Polynomial.lean:73` `NLAlib.aeval_diagonal_self`
- `NLAlib/Matrix/Functions/TraceFunctions.lean:266` `NLAlib.convexOn_re_trace_cfc`
- `NLAlib/Matrix/Functions/TraceFunctions.lean:414` `NLAlib.convexOn_re_trace_exp`
- `NLAlib/Matrix/Inequalities/EntrywiseFunctions.lean:268` `NLAlib.posDef_exp_mul_of_injective`
- `NLAlib/Matrix/Inequalities/Minkowski.lean:163` `NLAlib.concaveOn_re_det_rpow`
- `NLAlib/Matrix/Inequalities/Order.lean:492` `NLAlib.convex_setOf_posDef`
- `NLAlib/Matrix/Inequalities/Order.lean:501` `NLAlib.convex_setOf_posSemidef`
- `NLAlib/Matrix/Majorization/Basic.lean:247` `NLAlib.sum_le_sum_range_card_of_antitone`
- `NLAlib/Matrix/Majorization/Basic.lean:412` `NLAlib.exists_equiv_antitone_comp`
- `NLAlib/Matrix/Majorization/Horn.lean:177` `NLAlib.sum_range_rpow_le_of_forall_prod_range_le`
- `NLAlib/Matrix/Norms/Loewner.lean:109` `NLAlib.smul_one_le_diagonal_iff`
- `NLAlib/Matrix/Norms/Loewner.lean:125` `NLAlib.smul_one_le_smul_one`
- `NLAlib/Matrix/Norms/Loewner.lean:133` `NLAlib.smul_one_le_smul_one_iff`
- `NLAlib/Matrix/Norms/Loewner.lean:446` `NLAlib.inv_mul_smul_vecMulVec_star_self_le`
- `NLAlib/Matrix/Norms/Net.lean:46` `NLAlib.finrank_real_fun`
- `NLAlib/Matrix/Norms/Net.lean:52` `Metric.IsCover.exists_mem_norm_toLp_sub_le`
- `NLAlib/Matrix/Norms/Net.lean:167` `NLAlib.exists_finite_isCover_sphere`
- `NLAlib/Matrix/Norms/SymmetricGauge.lean:57` `NLAlib.exists_forall_le_apply_eq_zero`
- `NLAlib/Matrix/Perturbation/Continuity.lean:193` `NLAlib.isClosed_setOf_rank_le`
- `NLAlib/Matrix/Perturbation/Continuity.lean:223` `NLAlib.isOpen_setOf_le_rank`
- `NLAlib/Matrix/Perturbation/Continuity.lean:236` `NLAlib.isOpen_setOf_injective_mulVec`
- `NLAlib/Matrix/Spectral/RankOneUpdate.lean:106` `NLAlib.charpoly_diagonal_add_vecMulVec`
- `NLAlib/Matrix/Spectral/RankOneUpdate.lean:137` `NLAlib.det_diagonal_add_vecMulVec`
- `NLAlib/Matrix/Spectral/RankOneUpdate.lean:164` `NLAlib.charpoly_fromBlocks_diagonal_replicateCol`
- `NLAlib/Matrix/Spectral/Schur.lean:382` `NLAlib.dense_setOf_separable_charpoly`
- `NLAlib/Matrix/Structured/Circulant.lean:46` `NLAlib.circulant_mulVec_pow`
- `NLAlib/Matrix/Structured/Circulant.lean:271` `NLAlib.isStarNormal_circulant`

**S4** (3)

- `NLAlib/Matrix/Factorizations/NystromOrder.lean:399` `NLAlib.HasOrthonormalCols.nuclearNorm_fromBlocks_sub_nystrom` — 86 lines
- `NLAlib/Matrix/Spectral/BestRankApprox.lean:387` `NLAlib.IsBestRankApprox.exists_isSVD_eq` — 125 lines
- `NLAlib/Matrix/Spectral/LowRank.lean:699` `NLAlib.exists_hasOrthonormalCols_conjTranspose_mul_self_mul_eq_mul_diagonal` — 102 lines

**T9** (10)

- `NLAlib/Matrix/Factorizations/Givens.lean:398` `NLAlib.givensHessenbergStep_plane_ne`
- `NLAlib/Matrix/Factorizations/Givens.lean:403` `NLAlib.givensHessenbergStep_of_lt`
- `NLAlib/Matrix/Factorizations/GivensHessenberg.lean:229` `NLAlib.pinv_submatrix_mulVec_single_eq_backSubst`
- `NLAlib/Matrix/Factorizations/GivensHessenberg.lean:257` `NLAlib.norm_sub_mulVec_pinv_submatrix_mulVec_single_eq`
- `NLAlib/Matrix/Norms/GaugeExamples.lean:155` `NLAlib.lpGauge_top_apply`
- `NLAlib/Matrix/Norms/GaugeExamples.lean:159` `NLAlib.lpGauge_one_apply`
- `NLAlib/Matrix/Norms/SymmetricGauge.lean:145` `NLAlib.SymmetricGauge.map_abs`
- `NLAlib/Matrix/Norms/UnitarilyInvariant.lean:387` `NLAlib.lpGauge_top_matrixNorm`
- `NLAlib/Matrix/Norms/UnitarilyInvariant.lean:392` `NLAlib.lpGauge_two_matrixNorm`
- `NLAlib/Matrix/Norms/UnitarilyInvariant.lean:397` `NLAlib.lpGauge_one_matrixNorm`

## Polynomial (20)

**C2** (1)

- `NLAlib/Polynomial/Chebyshev/ResidualMinimax.lean:247` `NLAlib.exists_residualMinimax_sq_le_sum_mul_norm_sq` — [Greenbaum1979]

**D1** (9)

- `NLAlib/Polynomial/Approximation/AnalyticApproximation.lean:96` `NLAlib.isUniformApproxOn_chebyshevTrunc_of_open_ellipse`
- `NLAlib/Polynomial/Approximation/AnalyticApproximation.lean:135` `NLAlib.exists_degree_le_isUniformApproxOn_of_open_ellipse_interval`
- `NLAlib/Polynomial/Approximation/AnalyticCoefficients.lean:168` `NLAlib.norm_chebyshevCoeff_le_of_open_ellipse`
- `NLAlib/Polynomial/Approximation/ChebyshevTruncation.lean:83` `NLAlib.chebyshevTrunc_eval_eq`
- `NLAlib/Polynomial/Approximation/Inverse.lean:37` `NLAlib.exists_degree_lt_isUniformApproxOn_inv`
- `NLAlib/Polynomial/Approximation/Jackson.lean:339` `NLAlib.isUniformApproxOn_jacksonApprox_of_lipschitz`
- `NLAlib/Polynomial/Chebyshev/Residual.lean:104` `NLAlib.isUniformApproxOn_chebyshevResidual`
- `NLAlib/Polynomial/Chebyshev/Residual.lean:132` `NLAlib.isUniformApproxOn_chebyshevResidual_two_mul_pow`
- `NLAlib/Polynomial/Chebyshev/Residual.lean:204` `NLAlib.isLeast_chebyshev_minimax`

**P9** (10)

- `NLAlib/Polynomial/Approximation/Inverse.lean:28` `NLAlib.exists_degree_lt_isUniformApproxOn_inv`
- `NLAlib/Polynomial/Approximation/Stieltjes.lean:195` `NLAlib.rpow_mul_add_le`
- `NLAlib/Polynomial/Chebyshev/Residual.lean:150` `NLAlib.inv_eval_T_real_le_of_isUniformApproxOn`
- `NLAlib/Polynomial/Chebyshev/Residual.lean:197` `NLAlib.isLeast_chebyshev_minimax`
- `NLAlib/Polynomial/Chebyshev/Residual.lean:262` `NLAlib.inv_eval_T_real_eq_two_mul_pow_div`
- `NLAlib/Polynomial/Chebyshev/Residual.lean:323` `NLAlib.exists_degree_le_eval_eq_zero_abs_eval_le_two_mul_mul_pow`
- `NLAlib/Polynomial/Interpolation/DividedDifference.lean:66` `NLAlib.nodalWeight_map`
- `NLAlib/Polynomial/Interpolation/DividedDifference.lean:110` `NLAlib.exists_eq_mul_nodalWeight`
- `NLAlib/Polynomial/Interpolation/Stieltjes.lean:67` `NLAlib.inv_add_sub_eval_interpolate`
- `NLAlib/Polynomial/Interpolation/Stieltjes.lean:117` `NLAlib.div_add_sub_eval_interpolate`

## Probability (68)

**C1** (4)

- `NLAlib/Probability/Isotropic.lean:98` `NLAlib.IsIsotropic.integral_quadForm`
- `NLAlib/Probability/SubGaussianVector/Norm.lean:448` `NLAlib.IsSubgaussianVector.measureReal_norm_mulVec_sq_ge_le`
- `NLAlib/Probability/Tail.lean:57` `NLAlib.measureReal_ge_le_integral_div`
- `NLAlib/Probability/Tail.lean:81` `NLAlib.measureReal_ge_le_variance_div_sq`

**C2** (13)

- `NLAlib/Probability/BoundedDifferences.lean:135` `NLAlib.hasSubgaussianMGF_sub_integral_of_abs_update_sub_le` — [McDiarmid1989]
- `NLAlib/Probability/BoundedDifferences.lean:158` `NLAlib.measureReal_sub_integral_ge_le_mcdiarmid` — [McDiarmid1989]
- `NLAlib/Probability/ConvexOrder.lean:248` `ConvexOn.integral_uniformOn_injective_le_integral_pi` — [Hoeffding1963]
- `NLAlib/Probability/ConvexOrder.lean:248` `ConvexOn.integral_uniformOn_injective_le_integral_pi` — [GrossNesme2010]
- `NLAlib/Probability/Distributions/GaussianComparison.lean:419` `NLAlib.integral_comp_le_integral_comp_of_hasGaussianLaw` — [Kahane1986]
- `NLAlib/Probability/Distributions/GaussianComparison.lean:1031` `NLAlib.integral_iInf_iSup_le_integral_iInf_iSup_of_hasGaussianLaw` — [Gordon1985]
- `NLAlib/Probability/Distributions/GaussianLogOverlap.lean:457` `NLAlib.measureReal_log_norm_sq_div_sq_ge_le_of_hasLaw_gaussianVector` — [KuczynskiWozniakowski1992]
- `NLAlib/Probability/Distributions/GaussianLogOverlap.lean:491` `NLAlib.integral_log_norm_sq_div_sq_le_of_hasLaw_gaussianVector` — [KuczynskiWozniakowski1992]
- `NLAlib/Probability/MatrixConcentration/ChernoffWithoutReplacement.lean:90` `NLAlib.integral_re_trace_exp_sum_le_of_hasLaw_uniformOn_injective` — [GrossNesme2010]
- `NLAlib/Probability/MatrixConcentration/ChernoffWithoutReplacement.lean:90` `NLAlib.integral_re_trace_exp_sum_le_of_hasLaw_uniformOn_injective` — [Tropp2011a]
- `NLAlib/Probability/MatrixConcentration/ChernoffWithoutReplacement.lean:187` `NLAlib.measureReal_eigenvalue_zero_sum_ge_le_chernoff_of_hasLaw_uniformOn_injective` — [Tropp2011a]
- `NLAlib/Probability/MatrixConcentration/ChernoffWithoutReplacement.lean:213` `NLAlib.measureReal_eigenvalue_sum_le_le_chernoff_of_hasLaw_uniformOn_injective` — [Tropp2011a]
- `NLAlib/Probability/Tail.lean:208` `NLAlib.measureReal_ge_le_exp_neg_of_mgf_le` — [BoucheronLugosiMassart2013]

**D1** (2)

- `NLAlib/Probability/QuadraticForm/Moments.lean:364` `NLAlib.variance_quadForm_of_hasLaw_gaussianVector`
- `NLAlib/Probability/QuadraticForm/Moments.lean:386` `NLAlib.variance_quadForm_of_hasLaw_rademacherVector`

**D2** (16)

- `NLAlib/Probability/MatrixConcentration/Bernstein.lean:381` `NLAlib.integral_eigenvalue_zero_sum_le_bernstein`
- `NLAlib/Probability/MatrixConcentration/Bernstein.lean:448` `NLAlib.integral_specNorm_sum_le_bernstein`
- `NLAlib/Probability/MatrixConcentration/Chernoff.lean:316` `NLAlib.measureReal_eigenvalue_zero_ge_le_card_mul_exp_of_integral_le`
- `NLAlib/Probability/MatrixConcentration/Chernoff.lean:340` `NLAlib.measureReal_eigenvalue_le_le_card_mul_exp_of_integral_le`
- `NLAlib/Probability/MatrixConcentration/ChernoffSum.lean:90` `NLAlib.measureReal_eigenvalue_sum_le_le_chernoff`
- `NLAlib/Probability/MatrixConcentration/ChernoffSum.lean:136` `NLAlib.integral_eigenvalue_zero_sum_le_chernoff`
- `NLAlib/Probability/MatrixConcentration/ChernoffSum.lean:173` `NLAlib.le_integral_eigenvalue_sum_chernoff`
- `NLAlib/Probability/MatrixConcentration/ChernoffSum.lean:221` `NLAlib.measureReal_specNorm_sum_sub_one_ge_le`
- `NLAlib/Probability/MatrixConcentration/ChernoffWithoutReplacement.lean:221` `NLAlib.measureReal_eigenvalue_sum_le_le_chernoff_of_hasLaw_uniformOn_injective`
- `NLAlib/Probability/MatrixConcentration/ChernoffWithoutReplacement.lean:246` `NLAlib.measureReal_eigenvalue_zero_sum_ge_le_card_mul_exp_of_hasLaw_uniformOn_injective`
- `NLAlib/Probability/MatrixConcentration/ChernoffWithoutReplacement.lean:270` `NLAlib.measureReal_eigenvalue_sum_le_le_card_mul_exp_of_hasLaw_uniformOn_injective`
- `NLAlib/Probability/MatrixConcentration/Series.lean:136` `NLAlib.integral_eigenvalue_zero_sum_smul_le`
- `NLAlib/Probability/MatrixConcentration/Series.lean:224` `NLAlib.integral_specNorm_sum_smul_le`
- `NLAlib/Probability/MatrixConditionalExpectation.lean:178` `Matrix.IsHermitian.condExp_cfc`
- `NLAlib/Probability/QuadraticForm/HansonWright.lean:184` `NLAlib.measureReal_quadForm_sub_integral_ge_le`
- `NLAlib/Probability/QuadraticForm/HansonWright.lean:199` `NLAlib.measureReal_quadForm_sub_integral_le_le`

**P8** (24)

- `NLAlib/Probability/ConvexOrder.lean:266` `ConvexOn.integral_uniformOn_injective_le_integral_pi` — ConvexOn
- `NLAlib/Probability/MatrixConditionalExpectation.lean:56` `Matrix.condExp_apply` — Matrix
- `NLAlib/Probability/MatrixConditionalExpectation.lean:74` `Matrix.condExp_conjTranspose` — Matrix
- `NLAlib/Probability/MatrixConditionalExpectation.lean:88` `Matrix.condExp_trace` — Matrix
- `NLAlib/Probability/MatrixConditionalExpectation.lean:94` `Matrix.ae_isHermitian_condExp` — Matrix
- `NLAlib/Probability/MatrixConditionalExpectation.lean:102` `Matrix.ae_posSemidef_condExp` — Matrix
- `NLAlib/Probability/MatrixConditionalExpectation.lean:132` `Matrix.ae_posDef_condExp` — Matrix
- `NLAlib/Probability/MatrixConditionalExpectation.lean:211` `Matrix.condExp_dilation` — Matrix
- `NLAlib/Probability/MatrixConditionalExpectation.lean:226` `Matrix.condExp_dilation_sq` — Matrix
- `NLAlib/Probability/MatrixIntegral.lean:65` `Matrix.integrable_iff` — Matrix
- `NLAlib/Probability/MatrixIntegral.lean:72` `Matrix.memLp_iff` — Matrix
- `NLAlib/Probability/MatrixIntegral.lean:87` `Matrix.integral_apply` — Matrix
- `NLAlib/Probability/MatrixIntegral.lean:111` `Matrix.integral_conjTranspose` — Matrix
- `NLAlib/Probability/MatrixIntegral.lean:117` `Matrix.integral_reindex` — Matrix
- `NLAlib/Probability/MatrixIntegral.lean:124` `Matrix.integral_submatrix` — Matrix
- `NLAlib/Probability/MatrixIntegral.lean:134` `Matrix.integral_trace` — Matrix
- `NLAlib/Probability/MatrixIntegral.lean:141` `Matrix.integral_const_mul` — Matrix
- `NLAlib/Probability/MatrixIntegral.lean:152` `Matrix.integral_mul_const` — Matrix
- `NLAlib/Probability/MatrixIntegral.lean:171` `Matrix.integral_quadForm` — Matrix
- `NLAlib/Probability/MatrixIntegral.lean:183` `Matrix.isHermitian_integral` — Matrix
- `NLAlib/Probability/MatrixIntegral.lean:190` `Matrix.posSemidef_integral` — Matrix
- `NLAlib/Probability/MatrixIntegral.lean:196` `Matrix.posDef_integral` — Matrix
- `NLAlib/Probability/Measurability/Matrix.lean:251` `Measurable.truncatedSVD` — Measurable
- `NLAlib/Probability/Measurability/Matrix.lean:257` `AEMeasurable.truncatedSVD` — AEMeasurable

**P9** (6)

- `NLAlib/Probability/Distributions/GaussianConcentration.lean:43` `NLAlib.lipschitzWith_ofLp_iff`
- `NLAlib/Probability/MatrixConcentration/Bernstein.lean:116` `NLAlib.exp_mul_le_bernstein`
- `NLAlib/Probability/MatrixConcentration/Bernstein.lean:134` `NLAlib.mul_lt_three_of_mem_Ioo`
- `NLAlib/Probability/MatrixConcentration/Bernstein.lean:142` `NLAlib.sq_div_two_div_nonneg_of_mem_Ioo`
- `NLAlib/Probability/MatrixConcentration/Bernstein.lean:147` `NLAlib.exists_bernstein_exponent`
- `NLAlib/Probability/MatrixConcentration/Chernoff.lean:119` `NLAlib.exp_div_rpow_rpow_eq_exp`

**T2** (1)

- `NLAlib/Probability/QuadraticForm/HansonWright/OffDiagonal.lean:392` `NLAlib.hasSubexponentialMGF_quadForm_sub_diagonal`

**T9** (2)

- `NLAlib/Probability/MatrixConcentration/Freedman.lean:83` `NLAlib.HasCondMatrixMGFBound.supermartingale_re_trace_exp`
- `NLAlib/Probability/MatrixConcentration/Freedman.lean:141` `NLAlib.HasCondMatrixMGFBound.measureReal_exists_eigenvalue_zero_sum_ge_le`

## Krylov (81)

**C1** (24)

- `NLAlib/Krylov/Functions/LanczosFA.lean:140` `NLAlib.HasOrthonormalCols.compressedCfc_eq`
- `NLAlib/Krylov/Functions/LanczosFA.lean:151` `Matrix.IsHermitian.compressedCfc_inv_eq_galerkinInverse`
- `NLAlib/Krylov/Functions/LanczosFA.lean:344` `Matrix.IsHermitian.lanczosFA_inv_add_eq_cgIterate`
- `NLAlib/Krylov/LinearSystems/CG.lean:121` `Matrix.PosDef.conjTranspose_krylovMatrix_mulVec_sub_mulVec_cgIterate_eq_zero`
- `NLAlib/Krylov/LinearSystems/CG.lean:137` `Matrix.PosDef.eq_cgIterate_of_conjTranspose_krylovMatrix_mulVec_sub_eq_zero`
- `NLAlib/Krylov/LinearSystems/GMRES.lean:120` `NLAlib.eq_gmresIterate_of_conjTranspose_mul_krylovMatrix_mulVec_sub_eq_zero`
- `NLAlib/Krylov/LinearSystems/GMRESArnoldi.lean:93` `NLAlib.gmresIterate_eq_mgsArnoldiMatrix`
- `NLAlib/Krylov/LinearSystems/MINRES.lean:176` `Matrix.IsHermitian.norm_sub_mulVec_gmresIterate_le_two_mul_pow_of_forall_le`
- `NLAlib/Krylov/LinearSystems/MINRES.lean:200` `Matrix.IsHermitian.norm_sub_mulVec_gmresIterate_le_iSup_mul`
- `NLAlib/Krylov/LinearSystems/MINRES.lean:314` `NLAlib.pminresIterate_eq_mulVec_gmresIterate`
- `NLAlib/Krylov/LinearSystems/MINRES.lean:365` `Matrix.IsHermitian.re_quadForm_sub_mulVec_pminresIterate_le`
- `NLAlib/Krylov/LinearSystems/MINRES.lean:438` `NLAlib.pminresIterate_eq_of_krylovGrade_le`
- `NLAlib/Krylov/LinearSystems/MINRESRecurrence.lean:585` `Matrix.IsHermitian.minresState_x_eq_gmresIterate`
- `NLAlib/Krylov/LinearSystems/MINRESRecurrence.lean:593` `Matrix.IsHermitian.norm_minresState_phi_sq`
- `NLAlib/Krylov/LinearSystems/PCG.lean:259` `Matrix.PosDef.re_quadForm_sub_pcgIterate_le_four_mul_sq_mul_pow`
- `NLAlib/Krylov/LinearSystems/PCG.lean:279` `Matrix.PosDef.re_quadForm_sub_pcgIterate_le_residualMinimax_sq_mul`
- `NLAlib/Krylov/LinearSystems/PCG.lean:292` `Matrix.PosDef.pcgIterate_eq_of_krylovGrade_le`
- `NLAlib/Krylov/LinearSystems/PCGRecurrence.lean:287` `Matrix.PosDef.star_pcgState_p_dotProduct_mulVec_eq_zero`
- `NLAlib/Krylov/LinearSystems/WorstCase.lean:219` `NLAlib.re_quadForm_sub_cgIterate_chebyshevExtremaMatrix_eq_four_mul_pow_div`
- `NLAlib/Krylov/Processes/Lanczos.lean:168` `NLAlib.isGradedKrylovBasis_arnoldiMatrix`
- `NLAlib/Krylov/Processes/Lanczos.lean:185` `NLAlib.IsGradedKrylovBasis.eq_arnoldiMatrix`
- `NLAlib/Krylov/Processes/LanczosRecurrence.lean:371` `Matrix.IsHermitian.lanczosTridiagonal_eq`
- `NLAlib/Krylov/Processes/LanczosRecurrence.lean:394` `Matrix.IsHermitian.lanczosState_beta_eq_zero_iff`
- `NLAlib/Krylov/Processes/PreconditionedLanczos.lean:262` `Matrix.IsHermitian.preconditionedLanczosTridiagonal_eq`

**C2** (22)

- `NLAlib/Krylov/Functions/Optimality.lean:396` `Matrix.PosDef.exists_inv_add_le_re_quadForm_cfc_cfc_mulVec_sub_lanczosFA` — [Greenbaum1979]
- `NLAlib/Krylov/LinearSystems/CG.lean:68` `NLAlib.cgIterate` — [HestenesStiefel1952]
- `NLAlib/Krylov/LinearSystems/CGRecurrence.lean:56` `NLAlib.cgStep` — [HestenesStiefel1952]
- `NLAlib/Krylov/LinearSystems/CGRecurrence.lean:71` `NLAlib.cgState` — [HestenesStiefel1952]
- `NLAlib/Krylov/LinearSystems/CGRecurrence.lean:288` `Matrix.PosDef.conjTranspose_krylovMatrix_mulVec_cgState_r_eq_zero` — [HestenesStiefel1952]
- `NLAlib/Krylov/LinearSystems/CGRecurrence.lean:309` `Matrix.PosDef.span_cgState_p` — [HestenesStiefel1952]
- `NLAlib/Krylov/LinearSystems/CGRecurrence.lean:321` `Matrix.PosDef.star_cgState_r_dotProduct_eq_zero` — [HestenesStiefel1952]
- `NLAlib/Krylov/LinearSystems/CGRecurrence.lean:331` `Matrix.PosDef.star_cgState_p_dotProduct_mulVec_eq_zero` — [HestenesStiefel1952]
- `NLAlib/Krylov/LinearSystems/CGRecurrence.lean:340` `Matrix.PosDef.cgState_x_eq` — [HestenesStiefel1952]
- `NLAlib/Krylov/LinearSystems/GMRES.lean:67` `NLAlib.gmresIterate` — [SaadSchultz1986]
- `NLAlib/Krylov/LinearSystems/GMRES.lean:67` `NLAlib.gmresIterate` — [PaigeSaunders1975]
- `NLAlib/Krylov/LinearSystems/GMRES.lean:130` `NLAlib.isMinOn_gmresIterate` — [SaadSchultz1986]
- `NLAlib/Krylov/LinearSystems/GMRESArnoldi.lean:62` `NLAlib.gmresIterate_eq_arnoldiMatrix` — [SaadSchultz1986]
- `NLAlib/Krylov/LinearSystems/GMRESArnoldi.lean:129` `NLAlib.gmresIterate_eq_backSubst_givensHessenberg` — [SaadSchultz1986]
- `NLAlib/Krylov/LinearSystems/MINRESLanczos.lean:41` `Matrix.IsHermitian.gmresIterate_eq_lanczosMatrix` — [PaigeSaunders1975]
- `NLAlib/Krylov/LinearSystems/MINRESRecurrence.lean:83` `NLAlib.minresStep` — [PaigeSaunders1975]
- `NLAlib/Krylov/LinearSystems/MINRESRecurrence.lean:541` `Matrix.IsHermitian.minresState_x_eq` — [PaigeSaunders1975]
- `NLAlib/Krylov/LinearSystems/WorstCase.lean:499` `Matrix.PosDef.exists_re_quadForm_sub_cgIterate_eq_residualMinimax_sq_mul` — [Greenbaum1979]
- `NLAlib/Krylov/LinearSystems/WorstCase.lean:547` `Matrix.PosDef.isGreatest_re_quadForm_sub_cgIterate_div` — [Greenbaum1979]
- `NLAlib/Krylov/LinearSystems/WorstCase.lean:571` `Matrix.IsHermitian.exists_norm_sub_mulVec_gmresIterate_eq_residualMinimax_mul` — [GreenbaumGurvits1994]
- `NLAlib/Krylov/LinearSystems/WorstCase.lean:615` `Matrix.IsHermitian.isGreatest_norm_sub_mulVec_gmresIterate_div` — [GreenbaumGurvits1994]
- `NLAlib/Krylov/Processes/LanczosRecurrence.lean:61` `NLAlib.lanczosStep` — [Paige1972]

**D1** (2)

- `NLAlib/Krylov/Basic/Grade.lean:166` `NLAlib.finrank_krylovSpace`
- `NLAlib/Krylov/Processes/Lanczos.lean:168` `NLAlib.isGradedKrylovBasis_arnoldiMatrix`

**D2** (1)

- `NLAlib/Krylov/Processes/PreconditionedLanczos.lean:262` `Matrix.IsHermitian.preconditionedLanczosTridiagonal_eq`

**M2** (31)

- `NLAlib/Krylov/Functions/LanczosFA.lean:368` `NLAlib.lanczosFA_eq_arnoldiMatrix` — arnoldiMatrix
- `NLAlib/Krylov/LinearSystems/CG.lean:105` `Matrix.PosDef.cgIterate_eq` — cgIterate
- `NLAlib/Krylov/LinearSystems/CG.lean:118` `Matrix.PosDef.conjTranspose_krylovMatrix_mulVec_sub_mulVec_cgIterate_eq_zero` — cgIterate
- `NLAlib/Krylov/LinearSystems/CG.lean:404` `Matrix.PosDef.re_quadForm_sub_cgIterate_le_residualMinimax_sq_mul` — residualMinimax
- `NLAlib/Krylov/LinearSystems/CG.lean:466` `Matrix.PosDef.cgIterate_eq_of_krylovGrade_le` — cgIterate
- `NLAlib/Krylov/LinearSystems/CGLanczos.lean:64` `NLAlib.cgIterate_eq_arnoldiMatrix` — arnoldiMatrix
- `NLAlib/Krylov/LinearSystems/GMRES.lean:114` `NLAlib.eq_gmresIterate_of_conjTranspose_mul_krylovMatrix_mulVec_sub_eq_zero` — gmresIterate
- `NLAlib/Krylov/LinearSystems/GMRES.lean:130` `NLAlib.isMinOn_gmresIterate` — gmresIterate
- `NLAlib/Krylov/LinearSystems/GMRES.lean:205` `NLAlib.gmresIterate_eq_of_krylovGrade_le` — gmresIterate
- `NLAlib/Krylov/LinearSystems/GMRESArnoldi.lean:62` `NLAlib.gmresIterate_eq_arnoldiMatrix` — arnoldiMatrix
- `NLAlib/Krylov/LinearSystems/GMRESArnoldi.lean:90` `NLAlib.gmresIterate_eq_mgsArnoldiMatrix` — gmresIterate
- `NLAlib/Krylov/LinearSystems/GMRESArnoldi.lean:188` `NLAlib.norm_sub_mulVec_gmresIterate_eq_norm_givensHessenbergQ` — gmresIterate
- `NLAlib/Krylov/LinearSystems/MINRES.lean:173` `Matrix.IsHermitian.norm_sub_mulVec_gmresIterate_le_two_mul_pow_of_forall_le` — gmresIterate
- `NLAlib/Krylov/LinearSystems/MINRES.lean:212` `Matrix.IsHermitian.norm_sub_mulVec_gmresIterate_le_residualMinimax_mul` — residualMinimax
- `NLAlib/Krylov/LinearSystems/MINRES.lean:286` `Matrix.PosDef.isMinOn_pminresIterate` — pminresIterate
- `NLAlib/Krylov/LinearSystems/MINRES.lean:434` `NLAlib.pminresIterate_eq_of_krylovGrade_le` — pminresIterate
- `NLAlib/Krylov/LinearSystems/MINRESRecurrence.lean:582` `Matrix.IsHermitian.minresState_x_eq_gmresIterate` — gmresIterate
- `NLAlib/Krylov/LinearSystems/PCG.lean:129` `Matrix.PosDef.isMinOn_pcgIterate` — pcgIterate
- `NLAlib/Krylov/LinearSystems/PCG.lean:273` `Matrix.PosDef.re_quadForm_sub_pcgIterate_le_residualMinimax_sq_mul` — residualMinimax
- `NLAlib/Krylov/LinearSystems/PCG.lean:289` `Matrix.PosDef.pcgIterate_eq_of_krylovGrade_le` — pcgIterate
- `NLAlib/Krylov/LinearSystems/WorstCase.lean:215` `NLAlib.re_quadForm_sub_cgIterate_chebyshevExtremaMatrix_eq_four_mul_pow_div` — cgIterate
- `NLAlib/Krylov/LinearSystems/WorstCase.lean:499` `Matrix.PosDef.exists_re_quadForm_sub_cgIterate_eq_residualMinimax_sq_mul` — residualMinimax
- `NLAlib/Krylov/Processes/ArnoldiRecurrence.lean:205` `NLAlib.mgsArnoldiMatrix_eq_arnoldiMatrix` — arnoldiMatrix
- `NLAlib/Krylov/Processes/ArnoldiRecurrence.lean:215` `NLAlib.mgsArnoldiHessenberg_eq` — arnoldiMatrix
- `NLAlib/Krylov/Processes/Lanczos.lean:166` `NLAlib.isGradedKrylovBasis_arnoldiMatrix` — arnoldiMatrix
- `NLAlib/Krylov/Processes/Lanczos.lean:181` `NLAlib.IsGradedKrylovBasis.eq_arnoldiMatrix` — arnoldiMatrix
- `NLAlib/Krylov/Processes/Lanczos.lean:235` `NLAlib.mul_arnoldiMatrix` — arnoldiMatrix
- `NLAlib/Krylov/Processes/LanczosRecurrence.lean:357` `Matrix.IsHermitian.lanczosMatrix_eq_arnoldiMatrix` — arnoldiMatrix
- `NLAlib/Krylov/Processes/LanczosRecurrence.lean:367` `Matrix.IsHermitian.lanczosTridiagonal_eq` — arnoldiMatrix
- `NLAlib/Krylov/Processes/PreconditionedLanczos.lean:241` `Matrix.IsHermitian.preconditionedLanczosMatrix_eq` — arnoldiMatrix
- `NLAlib/Krylov/Processes/PreconditionedLanczos.lean:257` `Matrix.IsHermitian.preconditionedLanczosTridiagonal_eq` — arnoldiMatrix

**S4** (1)

- `NLAlib/Krylov/Functions/NearOptimality.lean:116` `Matrix.IsHermitian.re_quadForm_cfc_sub_le_of_sub_eq_aeval_mulVec` — 84 lines

## RandomMatrix (10)

**D2** (7)

- `NLAlib/RandomMatrix/Gaussian/BlockMoments.lean:191` `NLAlib.integral_frobNorm_pinv_mul_mul_sq_of_hasLaw_gaussianMatrix`
- `NLAlib/RandomMatrix/Gaussian/BlockMoments.lean:228` `NLAlib.integral_specNorm_mul_mul_pinv_le_of_hasLaw_gaussianMatrix`
- `NLAlib/RandomMatrix/Gaussian/BlockMoments.lean:431` `NLAlib.integral_specNorm_pinv_mul_mul_sq_le_of_hasLaw_gaussianMatrix`
- `NLAlib/RandomMatrix/Gaussian/BlockTail.lean:630` `NLAlib.measureReal_specNorm_mul_mul_pinv_gt_le_of_hasLaw_gaussianMatrix`
- `NLAlib/RandomMatrix/Gaussian/BlockTail.lean:683` `NLAlib.measureReal_frobNorm_mul_mul_pinv_gt_le_of_hasLaw_gaussianMatrix`
- `NLAlib/RandomMatrix/Haar/Transfer.lean:184` `NLAlib.measureReal_gt_eq_measureReal_gaussianMatrix_of_isLeftUnitarilyInvariant`
- `NLAlib/RandomMatrix/UnitaryInvariance.lean:250` `NLAlib.integral_conjTranspose_mul_mul_mul_conjTranspose_of_isLeftUnitarilyInvariant`

**S4** (3)

- `NLAlib/RandomMatrix/Gaussian/BlockTail.lean:224` `NLAlib.measureReal_lt_sum_le` — 89 lines
- `NLAlib/RandomMatrix/Gaussian/InverseMoments.lean:90` `NLAlib.inv_mul_conjTranspose_mulVec_single` — 90 lines
- `NLAlib/RandomMatrix/Gaussian/InverseMoments.lean:662` `NLAlib.lintegral_inv_mul_conjTranspose_apply_sq` — 82 lines

## Sketching (30)

**C1** (15)

- `NLAlib/Sketching/Gaussian/Gaussian.lean:797` `NLAlib.isObliviousSubspaceInjection_of_hasLaw_gaussianMatrix_of_gaussianInjectionDim_le`
- `NLAlib/Sketching/Gaussian/Gaussian.lean:845` `NLAlib.hasJLProperty_of_hasLaw_gaussianMatrix_of_jlDim_le`
- `NLAlib/Sketching/Gaussian/Haar.lean:391` `NLAlib.hasJLProperty_of_hasLaw_haarFrame_of_jlDim_le`
- `NLAlib/Sketching/Gaussian/HaarEmbedding.lean:323` `NLAlib.HasOrthonormalCols.hasSubspaceEmbedding_of_hasLaw_haarFrame`
- `NLAlib/Sketching/Gaussian/HaarEmbedding.lean:350` `NLAlib.HasOrthonormalCols.hasSubspaceEmbedding_of_hasLaw_haarFrame_of_lt_sqrt_sub_sqrt`
- `NLAlib/Sketching/Gaussian/HaarEmbedding.lean:546` `NLAlib.HasOrthonormalCols.hasSubspaceEmbedding_of_hasLaw_haarFrame_of_card_add_eq`
- `NLAlib/Sketching/Gaussian/HaarEmbedding.lean:596` `NLAlib.isObliviousSubspaceInjection_of_hasLaw_haarFrame`
- `NLAlib/Sketching/Gaussian/HaarEmbedding.lean:626` `NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_haarFrame`
- `NLAlib/Sketching/Gaussian/HaarEmbedding.lean:660` `NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_haarFrame_of_lt_sqrt_sub_sqrt`
- `NLAlib/Sketching/Gaussian/Rademacher.lean:301` `NLAlib.hasJLProperty_of_hasLaw_rademacherMatrix_of_jlDim_le`
- `NLAlib/Sketching/Gaussian/Rademacher.lean:340` `NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_rademacherMatrix_of_jlDim_le`
- `NLAlib/Sketching/Sampling/RowSampling.lean:784` `NLAlib.hasSubspaceInjection_of_hasLaw_samplingSketch_of_samplingInjectionDim_le`
- `NLAlib/Sketching/Sampling/WithoutReplacement.lean:543` `NLAlib.hasSubspaceInjection_of_hasLaw_samplingSketchWithoutReplacement_of_samplingInjectionDim_le`
- `NLAlib/Sketching/Sparse/CountSketch.lean:583` `NLAlib.integral_frobNorm_conjTranspose_mul_sub_sq_of_hasLaw_countSketch`
- `NLAlib/Sketching/Structured/SRHT.lean:963` `NLAlib.isObliviousSubspaceInjection_of_hasLaw_srhtWithReplacement_of_samplingInjectionDim_le`

**C2** (15)

- `NLAlib/Sketching/Properties/ProjectionCost.lean:551` `NLAlib.projectionCostTailDim` — [CohenElderMuscoMuscoPersu2015]
- `NLAlib/Sketching/Sampling/WithoutReplacement.lean:352` `NLAlib.hasSubspaceInjection_of_hasLaw_samplingSketchWithoutReplacement` — [Tropp2011a]
- `NLAlib/Sketching/Sampling/WithoutReplacement.lean:388` `NLAlib.hasSubspaceEmbedding_zero_of_hasLaw_samplingSketchWithoutReplacement` — [Tropp2011a]
- `NLAlib/Sketching/Sampling/WithoutReplacement.lean:425` `NLAlib.hasSubspaceEmbedding_of_hasLaw_samplingSketchWithoutReplacement` — [Tropp2011a]
- `NLAlib/Sketching/Sampling/WithoutReplacement.lean:457` `NLAlib.hasSubspaceEmbedding_coherence_of_hasLaw_samplingSketchWithoutReplacement` — [Tropp2011a]
- `NLAlib/Sketching/Sampling/WithoutReplacement.lean:471` `NLAlib.hasSubspaceEmbedding_of_hasLaw_samplingSketchWithoutReplacement_of_samplingEmbeddingDim_le` — [Tropp2011a]
- `NLAlib/Sketching/Structured/Flattening.lean:81` `NLAlib.srhtRowBound` — [Tropp2011a]
- `NLAlib/Sketching/Structured/Flattening.lean:257` `NLAlib.measureReal_exists_leverageScore_mul_diagonal_gt_le_of_hasLaw_rademacherVector` — [Tropp2011a]
- `NLAlib/Sketching/Structured/Flattening.lean:391` `NLAlib.hasSubspaceInjection_mul_of_indepFun_of_leverageScore_le` — [Tropp2011a]
- `NLAlib/Sketching/Structured/Flattening.lean:412` `NLAlib.hasSubspaceEmbedding_mul_of_indepFun_of_leverageScore_le` — [Tropp2011a]
- `NLAlib/Sketching/Structured/SRHT.lean:128` `NLAlib.srht` — [Tropp2011a]
- `NLAlib/Sketching/Structured/SRHT.lean:536` `NLAlib.isObliviousSubspaceInjection_of_hasLaw_srht` — [Tropp2011a]
- `NLAlib/Sketching/Structured/SRHT.lean:564` `NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_srht` — [Tropp2011a]
- `NLAlib/Sketching/Structured/SRHT.lean:668` `NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_srht_of_samplingEmbeddingDim_le` — [Tropp2011a]
- `NLAlib/Sketching/Structured/SRHT.lean:763` `NLAlib.isObliviousSubspaceInjection_of_hasLaw_srht_of_samplingInjectionDim_le` — [Tropp2011a]

## Regression (2)

**T13** (2)

- `NLAlib/Regression/SketchAndSolve.lean:804` `NLAlib.integral_frobNorm_sub_mul_sketchAndSolve_sq_le_one_add_mul_of_hasLaw_gaussianMatrix` — _hε
- `NLAlib/Regression/SketchAndSolve.lean:829` `NLAlib.integral_frobNorm_sub_mul_sketchAndSolve_sq_le_one_add_mul_of_hasLaw_haarFrame` — _hε

## LowRank (43)

**C1** (5)

- `NLAlib/LowRank/Oblivious/CountSketch.lean:221` `NLAlib.exists_forall_measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_countSketch`
- `NLAlib/LowRank/Oblivious/CountSketch.lean:329` `NLAlib.exists_forall_measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_countSketch`
- `NLAlib/LowRank/Oblivious/SubGaussian.lean:201` `NLAlib.exists_forall_measureReal_frobNorm_sub_rsvd_sq_gt_le_of_isSubgaussianVector`
- `NLAlib/LowRank/Oblivious/SubGaussian.lean:330` `NLAlib.exists_forall_measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_isSubgaussianVector`
- `NLAlib/LowRank/Oblivious/SubGaussian.lean:611` `NLAlib.exists_forall_measureReal_frobNorm_sub_rsvd_sq_gt_le_mul_of_isSubgaussianVector`

**C2** (1)

- `NLAlib/LowRank/Oblivious/EarlyTruncation.lean:513` `NLAlib.HasProjectionCostPreserving.measureReal_mul_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_gt_le` — [CohenElderMuscoMuscoPersu2015]

**D1** (3)

- `NLAlib/LowRank/Structural/RangeFinder.lean:255` `NLAlib.HasOrthonormalCols.specNorm_sub_rsvd_sq_le`
- `NLAlib/LowRank/Structural/RangeFinder.lean:271` `NLAlib.HasOrthonormalCols.specNorm_sub_rsvd_le`
- `NLAlib/LowRank/Structural/RangeFinder.lean:286` `NLAlib.HasOrthonormalCols.frobNorm_sub_rsvd_sq_le`

**D2** (20)

- `NLAlib/LowRank/Gaussian/NystromTail.lean:117` `Matrix.PosSemidef.measureReal_schattenNorm_sub_nystrom_gt_le_of_hasLaw_gaussianMatrix`
- `NLAlib/LowRank/Gaussian/NystromTail.lean:140` `Matrix.PosSemidef.measureReal_nuclearNorm_sub_nystrom_gt_le_of_hasLaw_gaussianMatrix`
- `NLAlib/LowRank/Gaussian/NystromTail.lean:163` `Matrix.PosSemidef.measureReal_specNorm_sub_nystrom_gt_le_of_hasLaw_gaussianMatrix`
- `NLAlib/LowRank/Gaussian/NystromTail.lean:192` `Matrix.PosSemidef.measureReal_nuclearNorm_sub_truncatedSVD_nystrom_gt_le_of_hasLaw_gaussianMatrix`
- `NLAlib/LowRank/Gaussian/NystromTail.lean:229` `Matrix.PosSemidef.measureReal_specNorm_sub_gt_le_of_isBestRankApprox_nystrom_of_hasLaw_gaussianMatrix`
- `NLAlib/LowRank/Gaussian/NystromTail.lean:265` `Matrix.PosSemidef.measureReal_specNorm_sub_truncatedSVD_nystrom_gt_le_of_hasLaw_gaussianMatrix`
- `NLAlib/LowRank/Gaussian/RangeFinderTail.lean:253` `NLAlib.measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_gaussianMatrix`
- `NLAlib/LowRank/Gaussian/RangeFinderTail.lean:277` `NLAlib.measureReal_specNorm_sub_rsvd_sq_gt_le_of_hasLaw_gaussianMatrix`
- `NLAlib/LowRank/Gaussian/RangeFinderTail.lean:300` `NLAlib.measureReal_frobNorm_sub_truncatedSVD_rsvd_sq_gt_le_of_hasLaw_gaussianMatrix`
- `NLAlib/LowRank/Gaussian/RangeFinderTail.lean:335` `NLAlib.measureReal_specNorm_sub_sq_gt_le_of_isBestRankApprox_of_hasLaw_gaussianMatrix`
- `NLAlib/LowRank/Gaussian/RangeFinderTail.lean:372` `NLAlib.measureReal_specNorm_sub_truncatedSVD_rsvd_sq_gt_le_of_hasLaw_gaussianMatrix`
- `NLAlib/LowRank/Gaussian/RangeFinderTail.lean:454` `NLAlib.measureReal_specNorm_sub_rsvd_gt_le_of_hasLaw_gaussianMatrix`
- `NLAlib/LowRank/Oblivious/GeneralizedNystrom.lean:152` `NLAlib.HasSubspaceInjection.measureReal_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_gt_le`
- `NLAlib/LowRank/Oblivious/RangeFinder.lean:239` `NLAlib.HasSubspaceInjection.measureReal_specNorm_sub_rsvd_sq_gt_le`
- `NLAlib/LowRank/Oblivious/RangeFinder.lean:271` `NLAlib.HasSubspaceInjection.measureReal_frobNorm_sub_truncatedSVD_rsvd_sq_gt_le`
- `NLAlib/LowRank/Oblivious/RangeFinder.lean:604` `NLAlib.IsObliviousSubspaceInjection.measureReal_matrixNorm_sub_nystrom_gt_le`
- `NLAlib/LowRank/Oblivious/RangeFinder.lean:628` `NLAlib.IsObliviousSubspaceInjection.measureReal_specNorm_sub_nystrom_gt_le`
- `NLAlib/LowRank/Oblivious/RangeFinder.lean:647` `NLAlib.IsObliviousSubspaceInjection.measureReal_nuclearNorm_sub_truncatedSVD_nystrom_gt_le`
- `NLAlib/LowRank/Structural/EarlyTruncation.lean:159` `NLAlib.IsSubspaceInjection.mul_frobNorm_sub_mul_sq_le`
- `NLAlib/LowRank/Structural/EarlyTruncation.lean:191` `NLAlib.IsSubspaceInjection.frobNorm_sub_mul_sq_le`

**M2** (2)

- `NLAlib/LowRank/Structural/Truncation.lean:375` `NLAlib.frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_frobNorm_truncatedSVD` — rsvd
- `NLAlib/LowRank/Structural/Truncation.lean:408` `NLAlib.frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_specNorm` — rsvd

**P9** (6)

- `NLAlib/LowRank/Gaussian/BlockKrylov.lean:686` `NLAlib.one_half_le_log_div`
- `NLAlib/LowRank/Gaussian/BlockKrylov.lean:696` `NLAlib.le_add_mul_of_le_add_mul_exp`
- `NLAlib/LowRank/Gaussian/BlockKrylov.lean:737` `NLAlib.one_le_and_log_div_le_sub_one_mul`
- `NLAlib/LowRank/Gaussian/BlockKrylovGapless.lean:865` `NLAlib.two_le_and_exp_log_four_mul_sq_div_le_one_add`
- `NLAlib/LowRank/Gaussian/BlockKrylovGapless.lean:905` `NLAlib.rpow_one_div_two_mul_add_one_le_one_add`
- `NLAlib/LowRank/Gaussian/RangeFinder.lean:556` `NLAlib.natCast_div_sub_sub_one_nonneg`

**S4** (6)

- `NLAlib/LowRank/Gaussian/BlockKrylov.lean:208` `NLAlib.exists_rbki_filter` — 83 lines
- `NLAlib/LowRank/Gaussian/BlockKrylovGapless.lean:350` `NLAlib.exists_forall_integral_specNorm_sub_truncatedSVD_rbki_sq_le_of_hasLaw_gaussianMatrix` — 106 lines
- `NLAlib/LowRank/Gaussian/BlockKrylovGapless.lean:647` `NLAlib.integral_specNorm_sub_rbki_sq_le_mul_exp_of_hasLaw_gaussianMatrix` — 117 lines
- `NLAlib/LowRank/Gaussian/EarlyTruncation.lean:617` `NLAlib.integral_frobNorm_sq_mul_inv_sq_le` — 93 lines
- `NLAlib/LowRank/Gaussian/RotationInvariant.lean:512` `NLAlib.integral_nuclearNorm_diagonal_sub_nystrom_le` — 97 lines
- `NLAlib/LowRank/Oblivious/SubGaussian.lean:461` `NLAlib.measureReal_frobNorm_sub_rsvd_sq_gt_le_mul_of_isSubgaussianVector` — 129 lines

## Estimation (2)

**C2** (1)

- `NLAlib/Estimation/Trace/HutchPlusPlus.lean:683` `NLAlib.variance_hutchpp_le_of_hasLaw_gaussianMatrix_of_rank_le` — [EpperlyWebber2026]

**T13** (1)

- `NLAlib/Estimation/Trace/HutchPlusPlus.lean:288` `NLAlib.HasOrthonormalCols.hutchpp_eq` — _hQ

## ForMathlib (12)

**C1** (1)

- `NLAlib/ForMathlib/Probability/Martingale/OptionalStopping.lean:40` `MeasureTheory.Supermartingale.measureReal_exists_ge_le`

**C2** (2)

- `NLAlib/ForMathlib/MeasureTheory/Constructions/BorelSpace/MeasurableSelection.lean:162` `IsClosed.measurable_of_forall_toLex_equivFun_le` — [KuratowskiRyllNardzewski1965]
- `NLAlib/ForMathlib/MeasureTheory/Constructions/BorelSpace/MeasurableSelection.lean:189` `IsClosed.exists_measurable_forall_prodMk_mem` — [KuratowskiRyllNardzewski1965]

**D1** (8)

- `NLAlib/ForMathlib/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Extremal.lean:55` `Polynomial.Chebyshev.abs_eval_le_abs_eval_T_real_of_isUniformApproxOn`
- `NLAlib/ForMathlib/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Extremal.lean:142` `Polynomial.Chebyshev.isLeast_chebyshev_monic_minimax`
- `NLAlib/ForMathlib/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Growth.lean:61` `Polynomial.Chebyshev.eval_T_real_eq_of_one_le`
- `NLAlib/ForMathlib/LinearAlgebra/Matrix/CauchyBinet.lean:102` `Matrix.det_conjTranspose_mul_self_eq_sum_powersetCard`
- `NLAlib/ForMathlib/LinearAlgebra/Matrix/PosDef.lean:163` `Matrix.PosSemidef.trace_mul_nonneg`
- `NLAlib/ForMathlib/LinearAlgebra/Matrix/PosDef.lean:174` `Matrix.PosSemidef.trace_mul_eq_zero_iff`
- `NLAlib/ForMathlib/LinearAlgebra/Matrix/PosDef.lean:204` `Matrix.PosSemidef.trace_mul_le_trace_mul`
- `NLAlib/ForMathlib/LinearAlgebra/Matrix/Rank.lean:265` `Matrix.rank_toBlock_add_card_eq_rank_inv_toBlock_not_add_card`

**D2** (1)

- `NLAlib/ForMathlib/MeasureTheory/Constructions/BorelSpace/MeasurableSelection.lean:197` `IsClosed.exists_measurable_forall_prodMk_mem`

## Documents (13)

**G1** (13)

- `docs/design/Mathlib-deviations.md:76` `2. Singular values` — missing Bridge, Status
- `docs/design/Mathlib-deviations.md:87` `3. Matrix norms are named functions` — missing Status
- `docs/design/Mathlib-deviations.md:101` `4. Orthonormal columns and unitaries` — missing Status
- `docs/design/Mathlib-deviations.md:114` `5. Vectors and column spaces` — missing Status
- `docs/design/Mathlib-deviations.md:126` `6. The matrix logarithm` — missing Bridge, Status
- `docs/design/Mathlib-deviations.md:135` `7. Spectral radius` — missing Status
- `docs/design/Mathlib-deviations.md:146` `8. Eigenvalues of a general matrix` — missing Status
- `docs/design/Mathlib-deviations.md:158` `9. Diagonalisability` — missing Cost
- `docs/design/Mathlib-deviations.md:167` `10. Derivatives of matrix-valued curves` — missing Cost, Status
- `docs/design/Mathlib-deviations.md:174` `11. Inertia` — missing Bridge, Cost
- `docs/design/Mathlib-deviations.md:183` `12. A measurable space on matrices` — missing Bridge, Cost
- `docs/design/Mathlib-deviations.md:206` `13. Integrals of matrix-valued functions` — missing Status
- `docs/design/Mathlib-deviations.md:289` `16. The uniform law on the sphere` — missing Cost

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
