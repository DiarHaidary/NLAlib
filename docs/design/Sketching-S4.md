# Design note: Sketching stage S4, row sampling and leverage scores

Status: drafted 2026-10-15 under `docs/PORT_SKETCHING.md` (D3 row "row sampling", D4, D5, D8, D9, D12;
§3); reviewed 2026-10-15, amendments in §8, which overrides §0 to §7 where they disagree. No question
for the maintainer remains (Q1 decided by the orchestrator, D4 unamended; Q7 deferred to an S1 interface
review). No missing lower-layer infrastructure (§1). Three files, as the brief lists them.

## 0. Scope and consumers

A fixed `U : Matrix n r 𝕜` of any shape and rank, weights `p : n → ℝ≥0` with `∑ i, p i = 1`, and the
sketch whose `card k` rows are `(√(card k · p ι_j))⁻¹ e_{ι_j}ᴴ` for i.i.d. indices `ι_j ~ p` (D9).
Over `𝕜` throughout. In this note `d := U.rank`; the Lean statements write `U.rank`.

| Item | Consumers |
|---|---|
| `leverageScore`, `coherence`, `leverageScoreDistribution` | the domination hypothesis of every S4 theorem; S5 (uniform subsets: coherence); S6 (flattening bounds the coherence of `H D U`); LowRank (Nyström and CUR with column sampling); Solvers (leverage-sampled sketch-and-solve) |
| `samplingSketchMatrix`, `samplingSketch`, the Gram-atoms identity | S5 (same constructor, uniform-injection law); S6 (`√(n/k) Pᵀ` is the constructor at uniform `p`); Nyström column sampling through `selectionMatrix` |
| fixed-`U` injection, upper half, embedding; sizes | Solvers (`U = [A, y]` or `U = A`, through S0); with isotropy (every `p i > 0`), S1's CEMT tails (sketch-and-solve, Theorem 2.7; Lemma 2.1 for LowRank) |
| AMM by sampling: unbiasedness, exact second moment, domination bound and tail | LowRank (CUR and column-sampling bounds in Frobenius norm); Estimation users of sampled products |

Not in S4: any oblivious statement (`p` depends on `U`, brief D2's OSI section), approximating leverage
scores (brief §0), sampling without replacement (S5).

## 1. Objects

New §5.3 rows (§7 Q5):

| Concept | Spelling | Bridge |
|---|---|---|
| leverage score | `leverageScore A i := re (rangeProjector A i i)`, any shape and rank (D8) | `HasOrthonormalCols.leverageScore_eq` (squared row norm), `leverageScore_eq_norm_sq` (`‖P e_i‖²`) |
| coherence | `coherence A := card m * ⨆ i, leverageScore A i` | `leverageScore_le_coherence_mul_inv` (the domination hypothesis at uniform `p`) |
| row-sampling sketch | constructor `samplingSketchMatrix p ι`, law `samplingSketch k p` (D4, §7 Q1, Q2) | `samplingSketchMatrix_eq_diagonal_mul` (to `selectionMatrix`), `hasLaw_samplingSketchMatrix` (to `Measure.pi fun _ => samplingMeasure p`) |

`leverageScoreDistribution A i := ‖leverageScore A i‖₊ / A.rank : ℝ≥0` is a named weight vector, not a
row of its own (Woodruff's Definition 16, MT §9.6.1).

Used directly: `samplingMeasure` and `samplingMeasure_const_inv_card` (P2, `Distributions/Sampling`);
`HasLaw.iIndepFun_eval` (`Probability/Law`); Mathlib's `Measure.pi`, `Measure.pi_pi`,
`Measure.ext_of_singleton`, `posSemidef_vecMulVec_star_self`; the Matrix layer's `rangeProjector` API,
`rangeProjector_mono`, `rangeProjector_inj`, `rank_rangeProjector`,
`rangeProjector_eq_mul_inv_mul_conjTranspose`, `exists_hasOrthonormalCols_range_eq`,
`specNorm_vecMulVec`, `frobNorm_vecMulVec`, `selectionMatrix`; `ProjectorPair.lean`'s
`IsStarProjection.re_apply_self_mem_Icc`, `.sum_re_apply_self`, `.re_apply_self_eq_norm_sq` (D8's
overlap search: these are the diagonal facts, so the first leverage lemmas are one-line corollaries
citing them; no independent proof); matrix Chernoff `measureReal_eigenvalue_sum_le_le_card_mul_exp`
and `measureReal_eigenvalue_zero_sum_ge_le_card_mul_exp` (`MatrixConcentration/ChernoffSum.lean`);
`integral_sum_mul_sum_of_iIndepFun` (`MatrixConcentration/Variance.lean`); P0's Markov; S0 and S1.
Searched Mathlib for leverage, coherence, row sampling: none. **Nothing is missing below Sketching**:
the Chernoff sums already take independent PSD summands with an a.s. Loewner bound and any mean, which
is exactly D9's shape. No deviation from Mathlib.

## 2. Interfaces

None new. Taken: `HasLaw S (samplingSketch k p) μ`, `hp : ∑ i, p i = 1`, and D8's domination
hypothesis `hdom : ∀ i, leverageScore U i ≤ L * p i`; for AMM its analogue
`∀ i, ‖WithLp.toLp 2 (A i)‖ * ‖WithLp.toLp 2 (B i)‖ ≤ L * p i` (§7 Q6). Concluded: `IsIsotropicSketch`,
`HasSubspaceInjection`, `HasSubspaceEmbedding` (S1). AMM concludes tails and integrals, no predicate (D2).

## 3. Statement shapes

`namespace NLAlib`, `open MeasureTheory ProbabilityTheory`, `open scoped Matrix MatrixOrder NNReal
Matrix.Norms.L2Operator`. Variables `{Ω} {mΩ} {μ : Measure Ω} {𝕜} [RCLike 𝕜] {k m n q r : Type*}`,
`[Fintype _]`, `[DecidableEq n] [DecidableEq k]`, `{S : Ω → Matrix k n 𝕜} {U : Matrix n r 𝕜}
{p : n → ℝ≥0} {L ε δ t : ℝ}`. Probabilities are `p`; column types are `q`, `r`.

Degenerate cases. `d = 0` (`U = 0` or rank zero): every bound is `0` and every failure event is empty.
`card k = 0`: `S = 0`; the lower bound is `d · e^0 ≥ 1` when `U ≠ 0`, the upper half holds surely; not
isotropic and AMM's mean is wrong, hence `[Nonempty k]` on isotropy and on all of §3.3. `p i = 0`: the
sketch row is `0` (junk `(√0)⁻¹ = 0`); `hdom` forces `leverageScore U i = 0`, hence row `i` of `U` is `0`
(`leverageScore_eq_zero_iff`), so the mean Gram is still `Uᴴ U`; the sketch is isotropic only if every
`p i > 0`. `L ≤ 0`: `hdom` forces every score to `0`, so `d = 0`; no `0 < L` hypothesis. `ε ≥ 1`: the
injection is vacuous (`isSubspaceInjection_of_nonpos`), so the lower half needs no `ε < 1`; `ε < 0`
excluded (`0 ≤ ε`). The simplified upper exponent needs `ε ≤ 1` (§7 Q4). Rank-deficient `U`: everything
is about `range U`, with `d = U.rank` (§7 Q3). `∑ p ≠ 1` is excluded by `hp`; in the two corollaries
whose weights may fail it (`U = 0`, empty `n`) the law is the zero measure, `HasLaw` forces `μ = 0`, and
the statement holds with no hypothesis.

### 3.1 `Sketching/Sampling/Leverage.lean` (18)

`{A : Matrix m n 𝕜} {B : Matrix m q 𝕜}`; deterministic.
```lean
/-- The **leverage score** of row `i`: the `i`-th diagonal entry of the projector onto `range A`.
[Woodruff2014, Definition 16 and the paragraph after it] (there `ℓ²ᵢ`, for a basis of the range);
[MartinssonTropp2020, §9.6.1] (there `‖P_L δ_i‖²`). Result: leverage-scores -/
noncomputable def leverageScore (A : Matrix m n 𝕜) (i : m) : ℝ := RCLike.re (rangeProjector A i i)
theorem leverageScore_nonneg (A) (i) : 0 ≤ leverageScore A i      -- IsStarProjection.re_apply_self_mem_Icc
theorem leverageScore_le_one (A) (i) : leverageScore A i ≤ 1
theorem sum_leverageScore (A) : ∑ i, leverageScore A i = A.rank   -- .sum_re_apply_self, rank_rangeProjector
theorem leverageScore_eq_norm_sq (A) (i) :
    leverageScore A i = ‖WithLp.toLp 2 ((rangeProjector A).col i)‖ ^ 2      -- MT's `‖P δ_i‖²`
/-- For orthonormal columns, the squared norm of row `i`. [Woodruff2014, Definition 16]. -/
theorem HasOrthonormalCols.leverageScore_eq {U : Matrix m r 𝕜} (hU : HasOrthonormalCols U) (i : m) :
    leverageScore U i = ‖WithLp.toLp 2 (U i)‖ ^ 2
/-- Basis independence [Woodruff2014, after Definition 16]. -/
theorem leverageScore_eq_of_range_eq (h : LinearMap.range A.mulVecLin = LinearMap.range B.mulVecLin) :
    leverageScore A = leverageScore B
/-- Domination passes to a subspace (`range A ≤ range [A, y]`). -/
theorem leverageScore_le_of_range_le (h : LinearMap.range B.mulVecLin ≤ LinearMap.range A.mulVecLin)
    (i : m) : leverageScore B i ≤ leverageScore A i
theorem leverageScore_eq_zero_iff (A) (i) : leverageScore A i = 0 ↔ A i = 0
/-- The statistician's hat-matrix diagonal `aᵢᴴ (Aᴴ A)⁻¹ aᵢ`, full column rank. -/
theorem leverageScore_eq_re_dotProduct_inv_mulVec [DecidableEq n] (hA : Function.Injective A.mulVec) (i : m) :
    leverageScore A i = RCLike.re (A i ⬝ᵥ ((Aᴴ * A)⁻¹ *ᵥ star (A i)))
/-- **Coherence** [MartinssonTropp2020, §9.6.1]; `0` for empty `m`. -/
noncomputable def coherence (A : Matrix m n 𝕜) : ℝ := Fintype.card m * ⨆ i, leverageScore A i
theorem leverageScore_le_coherence_mul_inv (A) (i) : leverageScore A i ≤ coherence A * (Fintype.card m : ℝ)⁻¹
theorem rank_le_coherence (A) : (A.rank : ℝ) ≤ coherence A
theorem coherence_le_card (A) : coherence A ≤ Fintype.card m
/-- The **leverage-score distribution** [Woodruff2014, Definition 16]; [MartinssonTropp2020, §9.6.1].
Junk: `0` when `A = 0`. -/
noncomputable def leverageScoreDistribution (A : Matrix m n 𝕜) (i : m) : ℝ≥0 :=
  ‖leverageScore A i‖₊ / A.rank
theorem coe_leverageScoreDistribution (A) (i) : (leverageScoreDistribution A i : ℝ) = leverageScore A i / A.rank
theorem sum_leverageScoreDistribution (hA : A ≠ 0) : ∑ i, leverageScoreDistribution A i = 1
theorem leverageScore_le_rank_mul_leverageScoreDistribution (A) (i) :
    leverageScore A i ≤ A.rank * leverageScoreDistribution A i
```
Proofs: the first three and the norm form are the `ProjectorPair` lemmas at
`isStarProjection_rangeProjector A`; orthonormal form by `HasOrthonormalCols.rangeProjector_eq`; range
forms by `rangeProjector_inj` and `rangeProjector_mono` (the diagonal of the PSD difference); zero iff
`P e_i = 0` iff `e_i ⊥ range A` iff `Aᴴ e_i = 0`; hat matrix by
`rangeProjector_eq_mul_inv_mul_conjTranspose` and `isUnit_conjTranspose_mul_self_iff`; coherence by
`ciSup` over a finite type (`Finite.le_ciSup`), `sum_leverageScore`, `leverageScore_le_one`.

### 3.2 `Sketching/Sampling/RowSampling.lean` (23)

`(hS : HasLaw S (samplingSketch k p) μ) (hp : ∑ i, p i = 1) (hdom : ∀ i, leverageScore U i ≤ L * p i)`.
```lean
/-- The **row-sampling sketch**: row `j` is `(√(card k · p (ι j)))⁻¹ e_{ι j}ᴴ`. Junk: `0` where
`p (ι j) = 0`. D9; [Woodruff2014, Definition 16] (there `D Ωᵀ`); [MartinssonTropp2020, §9.6.3]. -/
def samplingSketchMatrix (p : n → ℝ≥0) (ι : k → n) : Matrix k n 𝕜 :=
  Matrix.of fun j i => if ι j = i then (((√((Fintype.card k : ℝ) * p i))⁻¹ : ℝ) : 𝕜) else 0
/-- Its law for i.i.d. indices with law `samplingMeasure p`, as a finite mixture of Diracs (§7 Q1). -/
noncomputable def samplingSketch (k : Type*) [Fintype k] [DecidableEq k] (p : n → ℝ≥0) :
    Measure (Matrix k n 𝕜) :=
  ∑ ι : k → n, (∏ j, (p (ι j) : ℝ≥0∞)) • Measure.dirac (samplingSketchMatrix p ι)
theorem isProbabilityMeasure_samplingSketch (hp) : IsProbabilityMeasure (samplingSketch (𝕜 := 𝕜) k p)
theorem samplingSketch_eq_map [MeasurableSpace n] [MeasurableSingletonClass n] (p) :
    samplingSketch (𝕜 := 𝕜) k p = (Measure.pi fun _ : k => samplingMeasure p).map (samplingSketchMatrix p)
/-- D4's bridge from the user's own indices. -/
theorem hasLaw_samplingSketchMatrix [MeasurableSpace n] [MeasurableSingletonClass n] {ι : Ω → k → n}
    (hι : HasLaw ι (Measure.pi fun _ : k => samplingMeasure p) μ) :
    HasLaw (fun ω => (samplingSketchMatrix p (ι ω) : Matrix k n 𝕜)) (samplingSketch k p) μ
theorem samplingSketchMatrix_eq_diagonal_mul (p) (ι : k → n) : (samplingSketchMatrix p ι : Matrix k n 𝕜) =
    diagonal (fun j => (((√((Fintype.card k : ℝ) * p (ι j)))⁻¹ : ℝ) : 𝕜)) * (selectionMatrix ι)ᴴ
/-- The sketched cross-Gram matrix is an average of `card k` rank-one atoms (S5 and S6 reuse it). -/
theorem conjTranspose_samplingSketchMatrix_mul_mul (p) (ι : k → n) (A : Matrix n q 𝕜) (B : Matrix n r 𝕜) :
    (samplingSketchMatrix p ι * A)ᴴ * (samplingSketchMatrix p ι * B) =
      ∑ j, ((Fintype.card k : ℝ) * p (ι j))⁻¹ • vecMulVec (star (A (ι j))) (B (ι j))
theorem isIsotropicSketch_of_hasLaw_samplingSketch [Nonempty k] (hS) (hp) (hpos : ∀ i, 0 < p i) :
    IsIsotropicSketch S μ
/-- Lower half, matrix Chernoff's lower tail, with its own exponent `2L` (D2's OSI section, D9).
[Tropp2015, Theorem 5.1.1, (5.1.5), weakened after (5.1.8)]. -/
theorem hasSubspaceInjection_of_hasLaw_samplingSketch (hS) (hp) (hdom) (hε : 0 ≤ ε) :
    HasSubspaceInjection S U (1 - ε) (U.rank * Real.exp (-ε ^ 2 * Fintype.card k / (2 * L))) μ
/-- Upper half. [Tropp2015, Theorem 5.1.1, (5.1.6)], with `ε - (1 + ε) log (1 + ε) ≤ -ε²/3` on `[0, 1]`. -/
theorem hasSubspaceEmbedding_zero_of_hasLaw_samplingSketch (hS) (hp) (hdom) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    HasSubspaceEmbedding S U 0 (1 + ε) (U.rank * Real.exp (-ε ^ 2 * Fintype.card k / (3 * L))) μ
/-- **Row sampling under leverage domination** (D9). [Woodruff2014, Theorem 17] (there
`s > 144 k ln (2k/δ)/(β ε²)` through a Bernstein form, Fact 1; here Chernoff, `L = k/β`).
Result: leverage-sampling-ose -/
theorem hasSubspaceEmbedding_of_hasLaw_samplingSketch (hS) (hp) (hdom) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    HasSubspaceEmbedding S U (1 - ε) (1 + ε) (2 * U.rank * Real.exp (-ε ^ 2 * Fintype.card k / (3 * L))) μ
/-- Exact leverage scores, `L = d`. [MartinssonTropp2020, §9.6.3]. Result: leverage-sampling-ose -/
theorem hasSubspaceEmbedding_of_hasLaw_samplingSketch_leverageScoreDistribution
    (hS : HasLaw S (samplingSketch k (leverageScoreDistribution U)) μ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    HasSubspaceEmbedding S U (1 - ε) (1 + ε) (2 * U.rank * Real.exp (-ε ^ 2 * Fintype.card k / (3 * U.rank))) μ
/-- Uniform sampling, `L = coherence U`. [MartinssonTropp2020, §9.6.2] (there `d ≥ 2 ε⁻² μ log (2k)`). -/
theorem hasSubspaceEmbedding_of_hasLaw_samplingSketch_const_inv_card
    (hS : HasLaw S (samplingSketch k fun _ : n => (Fintype.card n : ℝ≥0)⁻¹) μ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    HasSubspaceEmbedding S U (1 - ε) (1 + ε)
      (2 * U.rank * Real.exp (-ε ^ 2 * Fintype.card k / (3 * coherence U))) μ
/-- Rows for `2 d e^{-ε² k/(3L)} ≤ δ`; the proof's constant, [Woodruff2014, Theorem 17]'s is 48 times
larger at `L = d/β`. Junk: `≤ 0` for `δ ≥ 2d`, where the tail is trivial. -/
noncomputable irreducible_def samplingSize (d : ℕ) (L ε δ : ℝ) : ℝ := 3 * L * Real.log (2 * d / δ) / ε ^ 2
noncomputable irreducible_def samplingInjectionSize (d : ℕ) (L ε δ : ℝ) : ℝ := 2 * L * Real.log (d / δ) / ε ^ 2
-- each: `_nonneg (hL : 0 ≤ L) (hδ : 0 < δ) (hδd : δ ≤ 2 * d)` (resp. `δ ≤ d`); `_mono` (monotone in `d`
-- and `0 ≤ L`, antitone in `ε > 0` and `δ > 0`); `_le`, the body as an upper bound, which an improved
-- body keeps true (6)
theorem hasSubspaceEmbedding_of_hasLaw_samplingSketch_of_samplingSize_le (hS) (hp) (hdom) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hδ : 0 < δ) (hk : samplingSize U.rank L ε δ ≤ Fintype.card k) :
    HasSubspaceEmbedding S U (1 - ε) (1 + ε) δ μ
theorem hasSubspaceInjection_of_hasLaw_samplingSketch_of_samplingInjectionSize_le (hS) (hp) (hdom)
    (hε : 0 < ε) (hδ : 0 < δ) (hk : samplingInjectionSize U.rank L ε δ ≤ Fintype.card k) :
    HasSubspaceInjection S U (1 - ε) δ μ
```
Proofs. Law: `Measure.ext_of_singleton` (`k → n` is finite), `Measure.pi_pi` on `Set.pi univ {ι j}`,
`samplingMeasure_singleton`; `hasLaw_samplingSketchMatrix` is `HasLaw.comp` with it. Fixed `U`:
1. `d = 0` gives `U = 0`. Otherwise `exists_hasOrthonormalCols_range_eq` gives `Q : Matrix n (Fin d) 𝕜`
   with the range of `U`; the failure sets for `U` and `Q` are equal (S0's `of_range_le` both ways);
   `leverageScore_eq_of_range_eq` and `HasOrthonormalCols.leverageScore_eq` turn `hdom` into
   `‖Q i‖² ≤ L p i`. `L ≤ 0` gives `d = 0` (`sum_leverageScore`); empty `k` is direct.
2. To the primitive space: S1's `HasLaw.hasSubspaceInjection_iff`, `samplingSketch_eq_map` under a local
   `⊤` measurable space on `n`, `HasLaw.id`; coordinates independent by `HasLaw.iIndepFun_eval`.
3. Atoms `X j ι := (card k · p (ι j))⁻¹ • vecMulVec (star (Q (ι j))) (Q (ι j))`: PSD; `≤ (L / card k) • 1`
   by `specNorm_vecMulVec` and `hdom` (`0` where `p = 0`); `∑ j, E X j = ∑_{p i ≠ 0} vecMulVec … = Qᴴ Q = 1`
   by `integral_samplingMeasure` and `leverageScore_eq_zero_iff`; the Gram identity above at `A = B = Q`.
4. Lower: `measureReal_eigenvalue_sum_le_le_card_mul_exp` at `j + 1 = d`, the event `{¬ injection}`
   inside `{λ_min ≤ 1 - ε}` (`HasOrthonormalCols.isSubspaceInjection_iff`, Loewner by eigenvalues);
   `ε ≥ 1` vacuous. Upper: `measureReal_eigenvalue_zero_sum_ge_le_card_mul_exp`. Two-sided: S1's
   `HasSubspaceInjection.hasSubspaceEmbedding`, `exp (-x/2) ≤ exp (-x/3)`.
5. Corollaries: `hdom` from `leverageScore_le_rank_mul_leverageScoreDistribution`, resp.
   `leverageScore_le_coherence_mul_inv`; `hp` from `sum_leverageScoreDistribution`, resp. `card n ≠ 0`.
   Isotropy: the Gram identity at `A = B = 1`, `hpos`. Sizes: `log` inversion, `d = 0` separately.

### 3.3 `Sketching/Sampling/MatrixMultiplication.lean` (5)

`[Nonempty k]`, `(hS) (hp)`, `A : Matrix n q 𝕜`, `B : Matrix n r 𝕜`; the event and error are S1 §3.6's,
`frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B)`, here over `𝕜` (no polarization is needed).
```lean
/-- Unbiased [MartinssonTropp2020, §7.1]. -/
theorem integral_conjTranspose_mul_mul_of_hasLaw_samplingSketch (hS) (hp) (hpos : ∀ i, 0 < p i) (A) (B) :
    ∫ ω, Aᴴ * (S ω)ᴴ * S ω * B ∂μ = Aᴴ * B
theorem integrable_frobNorm_conjTranspose_mul_sub_sq_of_hasLaw_samplingSketch (hS) (A) (B) :
    Integrable (fun ω => frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B) ^ 2) μ   -- no `[Nonempty k]`, no `hp`
/-- **AMM by sampling, exact second moment.** [MartinssonTropp2020, §7.1] (the estimator); Drineas,
Kannan and Mahoney 2006, Lemma 4 (to confirm, brief §7.2). Result: amm-sampling -/
theorem integral_frobNorm_conjTranspose_mul_sub_sq_of_hasLaw_samplingSketch (hS) (hp) (hpos) (A) (B) :
    ∫ ω, frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B) ^ 2 ∂μ =
      (∑ i, ‖WithLp.toLp 2 (A i)‖ ^ 2 * ‖WithLp.toLp 2 (B i)‖ ^ 2 / p i - frobNorm (Aᴴ * B) ^ 2) /
        Fintype.card k
/-- Domination form; zero weights allowed. At `p i ∝ ‖A i‖ ‖B i‖` it is DKM's `‖A‖_F² ‖B‖_F² / k`.
Result: amm-sampling -/
theorem integral_frobNorm_conjTranspose_mul_sub_sq_le_of_hasLaw_samplingSketch (hS) (hp)
    (hdom : ∀ i, ‖WithLp.toLp 2 (A i)‖ * ‖WithLp.toLp 2 (B i)‖ ≤ L * p i) :
    ∫ ω, frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B) ^ 2 ∂μ ≤ L * frobNorm A * frobNorm B / Fintype.card k
theorem measureReal_frobNorm_conjTranspose_mul_sub_ge_le_of_hasLaw_samplingSketch (hS) (hp) (hdom)
    (ht : 0 < t) : μ.real {ω | t ≤ frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B)} ≤
      L * frobNorm A * frobNorm B / (Fintype.card k * t ^ 2)
```
Proofs: §3.2's Gram identity; `Y j := (card k · p (ι j))⁻¹ • vecMulVec (star (A (ι j))) (B (ι j))`
i.i.d. with mean `Aᴴ B / card k` (`hpos`, resp. the support that `hdom` forces); the Frobenius
variance of the sum is the sum of variances (`integral_sum_mul_sum_of_iIndepFun` with
`f = (· - c)ᴴ`, then `re ∘ trace`, `frobNorm_sq_eq_re_trace`); `E ‖Y j‖_F² = ∑ i, w_i² / (card k² p i)`
by `frobNorm_vecMulVec`, `w_i = ‖A i‖ ‖B i‖`. Domination: `w_i² / p i ≤ L w_i`, drop
`- ‖Aᴴ B‖_F²`, Cauchy–Schwarz `∑ w_i ≤ ‖A‖_F ‖B‖_F`. `L < 0` contradicts `hp`. Tail: Markov
(`measureReal_ge_le_integral_div`) on the square.

## 4. Files

In `NLAlib/Sketching/Sampling/`, 46 statements, about 1250 lines against the brief's 950 (the coherence
block, the law bridge and the sizes are the overrun):
1. `Leverage.lean` (18: 3 definitions, 15 theorems); imports `Matrix/Basic/{Projector,Orthonormal}`,
   `Matrix/Subspaces/ProjectorPair`. About 300 lines.
2. `RowSampling.lean` (23: 4 definitions, 19 theorems); imports 1, `Matrix/Basic/{Selection,OrthonormalBasis}`,
   `Probability/Distributions/Sampling`, `Probability/Law`, `MatrixConcentration/ChernoffSum`,
   `Sketching/Properties/{FixedSubspace,Isotropic}`. About 700 lines.
3. `MatrixMultiplication.lean` (5); imports 2, `MatrixConcentration/Variance`, `Probability/Tail`.
   About 250 lines.
Sequential: 2 needs 1, 3 needs 2's law and Gram identity. Bibliography: nothing new; Drineas, Kannan and
Mahoney 2006 cited by name only until checked (brief §7.2, D16).

## 5. Material

Read: the prototype's `Sketching/Sampling/{Leverage,LeverageSampling,SamplingMultiplication,
SamplingMultiplicationBounds}.lean` (846 lines, 40 declarations: ℝ for leverage, ℂ for sampling, `Fin k`,
the `finiteSamplingLaw p hp` with a proof term); Woodruff §2.4 (Definition 16, Theorem 17, Fact 1); MT
§7.1 to §7.3, §9.6; Tropp 2015 Theorem 5.1.1 and its discussion; the inventory §2.2, §4 item 2, §10
item 7. Ledger (prototype → here):
- `Leverage.lean` (6): `leverageScore` (`A * A⁺`, ℝ) → `leverageScore` (`rangeProjector`, `𝕜`); `_nonneg`,
  `_le_one`, `sum_leverageScore_eq_rank` → §3.1; `leverageScore_eq_sum_sq_of_hasOrthonormalCols` (two
  hypotheses spelling "basis of the range") → `leverageScore_eq_of_range_eq` plus
  `HasOrthonormalCols.leverageScore_eq`; `…_of_self` → `HasOrthonormalCols.leverageScore_eq`.
- `LeverageSampling.lean` (9): `leverageSamplingSketch` → `samplingSketchMatrix`; `_mul`,
  `conjTranspose_…_mul_self` → `conjTranspose_samplingSketchMatrix_mul_mul`;
  `measure_le_norm_leverage_gram_sub_one` (`2 d e^{-βkε²/(3d)}`, orthonormal `Fin d`) →
  `hasSubspaceEmbedding_of_hasLaw_samplingSketch` (`L = d/β`, any `U`);
  `leverage_tail_le_of_sample_size`, `measure_leverage_embedding_failure_le_of_sample_size` → the
  `samplingSize` corollary; `sampledRowMatrix_conjTranspose`, `norm_leverage_mulVec_sq_bounds_of_gram_le`,
  `norm_mulVec_sq_bounds_of_zero_range` → not ported (`simp`; S0's range forms; the `d = 0` case).
- `SamplingMultiplication.lean` (23), `…Bounds.lean` (2): `integral_frobenius_sampled_mul_sub_sq` →
  the exact identity; `…_le_of_probability_domination` → the domination form (DKM's `β w_i / W ≤ p_i` is
  `L = W/β`); `frobenius_norm_sq_vecMulVec` → `frobNorm_vecMulVec` (exists);
  `integral_frobenius_average_sub_mean_sq`, `sum_probability_…`, `sum_columnRowWeight_sq_le` → proof
  material; `columnRowSample`, `sampledColumnMatrix`, `sampledRowMatrix` and their product lemma →
  replaced by the sketch and the Gram identity; `columnRowWeight` and its four lemmas,
  `columnRowProbabilities` and its two, the `…_of_columnRowProbabilities` pair → not ported (§6); the
  `map_ofReal` and `frobSq` twins and `…_zero_samples` → not ported (twins; empty `k`).
Result ids: `leverage-scores`, `leverage-sampling-ose`, `amm-sampling` (all atlas).

## 6. Cut, and why

`Fin` sizes, `ℂ`-only and real twins, proof terms in laws (D5, brief §6). Oblivious statements (not
oblivious). The Chernoff source forms `(e^{∓ε}/(1 ∓ ε)^{1 ∓ ε})^{k/L}`, which dominate the simplified
ones (§7 Q4). A named DKM law (`columnRowProbabilities`): the domination form covers every law, and its
only extra content, the exact value `(W² - ‖Aᴴ B‖²)/k` at that law, has no consumer. The embedding from
sampled AMM at `A = B = U` (`L d / (k ε²)` by Markov): S0's `isSubspaceEmbedding_of_frobNorm_le` gives
it in two lines. Spectral-norm AMM (§7 Q8). Injection and size twins of the two corollaries (the main
theorems at the corollary's `p` and `L`). A law-free "atoms" theorem (inventory §10 item 7): S5 needs
its own Chernoff and S6 applies the law form after conditioning, so the public Gram identity and the
leverage lemmas are all they share.

## 7. Questions and decisions

**For the maintainer:** Q1 (not hard to reverse; it amends D4's wording, hence asked).
**For the orchestrator:** Q7. **Decisions taken** (open to correction): the rest.

**Q1. The law is a finite mixture of Diracs, not defined as a pushforward.** D4 says each law is
"defined as the pushforward of its primitive randomness". For sampling the primitive is `ι : k → n`
under `Measure.pi fun _ => samplingMeasure p`, which needs `[MeasurableSpace n] [MeasurableSingletonClass n]`
on the row index of the data matrix. Defined as a pushforward, every theorem of §3.2 and §3.3 and every
consumer (a sketch-and-solve on `A : Matrix n q 𝕜`) would carry those two instances on `n`, which
otherwise has none. Defined as `∑ ι, (∏ j, p (ι j)) • dirac (samplingSketchMatrix p ι)`, no statement
needs them; `samplingSketch_eq_map` and `hasLaw_samplingSketchMatrix` are D4's bridge, under the
instances, for a user who holds the indices. D4's intent (one law hypothesis, a public constructor, a
bridge) is kept. *Recommendation: the mixture.* Reversal changes the body and the instance arguments,
no statement's conclusion. S5's uniform-injection law faces the same choice (`uniformOn` on `k → n`
needs a measurable space on `n` too), and should follow this answer.

**Q2. Names**: law `samplingSketch k p`, constructor `samplingSketchMatrix p ι`, parallel to
`countSketch`/`countSketchMatrix` and `srht`/`srhtMatrix` (D14). D4's parenthetical called the
constructor `samplingSketch p ι`; amended. `𝕜` implicit in the law (inferred from `S` in `HasLaw`).
Cheap now, not after S5 and S6.

**Q3. The dimension in every tail is `U.rank`, for any `U`** (D8: any shape and rank; brief §3: a fixed
`U` assumes orthonormality only when the proof needs it, and this proof does not). For orthonormal `U`,
`rank = card r`. *Hard to reverse*: consumers' tails and `samplingSize U.rank …` depend on it.

**Q4. D9's simplified exponents only**: lower `d e^{-ε² k/(2L)}` for every `ε ≥ 0`, upper
`d e^{-ε² k/(3L)}` for `ε ≤ 1`, two-sided `2 d e^{-ε² k/(3L)}`, as two half theorems joined by S1's union
lemma (brief §3). The source forms dominate them and give the upper half for `ε > 1`; they are added
when a consumer wants them, and then the simplified ones are reproved from them and keep their names
(rule 6). Woodruff's Bernstein route (Fact 1) is dominated by this one.

**Q5. Three named quantities.** `leverageScore` (D8), and `coherence` (MT §9.6.1; D9's "card times the
largest score", named by CONTRIBUTING §4 since it enters the uniform corollary, its size, S5 and S6's
flattening), each a new §5.3 row, two approvals by §9. `leverageScoreDistribution` is a definition,
not a row; its values use `‖·‖₊` (§5.1). Alternative to `coherence`: state uniform sampling through
`hdom` at `p = 1/n` with a free `L`; rejected, since every uniform statement would re-spell
`card n * max`.

**Q6. AMM hypotheses.** The exact identity and unbiasedness take `hpos : ∀ i, 0 < p i` (with a zero
weight and a nonzero product the mean is wrong; the alternative, a support condition
`p i = 0 → A i = 0 ∨ B i = 0`, would be a raw condition written twice). The domination form,
`‖A i‖ ‖B i‖ ≤ L p i` in D8's shape, allows zero weights and covers DKM's optimal law (`L = ∑ w`) and
its `β`-approximations (`L = W/β`). The tail is in a free threshold `t`, not S1's `ε ‖A‖_F ‖B‖_F`,
so it needs no `A ≠ 0`, `B ≠ 0`.

**Q7 (open, for the orchestrator). Sub-isotropy for S1's CEMT tails.** S1's Lemma 2.1 and
sketch-and-solve tails use `IsIsotropicSketch` only through `E ‖S M‖_F² ≤ ‖M‖_F²`. A sampling sketch
with zero weights (exact leverage sampling of a `U` with zero rows) has `E Sᴴ S = diagonal (1_{p > 0}) ≤ 1`,
which is enough. Weakening those tails to `∫ (S ω)ᴴ * S ω ≤ 1` is an S1 change (a §5.4 matter).
*Recommendation: not now.* A user mixes in uniform weights, `p = (ℓ/d + 1/n)/2` with `L = 2d`, gets
isotropy, and loses a factor 2 in `L`. Revisit when a consumer wants zero weights with the OSI route.
Not hard to reverse while those tails have no consumer.

**Q8. Spectral-norm AMM by sampling deferred.** The brief cites MT §7.3 for "the exact variance"; MT
§7.3 (and Tropp 2015 §6.4) is the spectral analysis through matrix Monte Carlo (MT Theorem 7.2, Tropp
Corollary 6.2.1), not the Frobenius identity. The rectangular Bernstein it needs exists
(`measureReal_specNorm_sum_ge_le_bernstein`), so it costs about 150 lines, but no consumer of the next
rounds asks for it. Docstrings cite MT §7.1 for the estimator and DKM by name for the identity.

**Q9.** Leverage scores stay in `Sketching/Sampling/` (D15), though deterministic: no layer below 3
consumes them, and LowRank and Solvers import Sketching. **Q10.** About 1250 lines against the brief's
950 (§4). **Q11.** `[DecidableEq k]` on the law (the finite index `k → n`) costs nothing at use.

## 8. Amendments from the review (2026-10-15)

Fable review of this note (0 blocker, 2 major, 10 minor), all findings accepted by the orchestrator;
Q1 decided as the review recommends, Q7 deferred. The review verified every cited name and signature,
the exponents (`2L` lower, `3L` upper, `2d · 3L` two-sided), the Chernoff parameter `L / card k`, the
factor 48 against Woodruff's 144, MT's coherence and the §9.6.2 and §9.6.3 sizes, Q8 (MT §7.3 is the
spectral analysis), the AMM second-moment identity and its domination bound, the size inversions and
the degenerate cases, and that S1's CEMT tails take the fixed-`U` pair. Where an item below
contradicts §0 to §7, it supersedes them; §3 stays as drafted. Skeletons: the three files of item 13,
every proof `sorry`.

1. **Q1 decided: the law is a pushforward, D4 unamended.** The draft's reason for the mixture is
   false: instances fixed inside the body leak into no statement. *Skeleton*:
   ```lean
   noncomputable def samplingSketch (k : Type*) [Fintype k] (p : n → ℝ≥0) : Measure (Matrix k n 𝕜) :=
     letI : MeasurableSpace n := ⊤
     (Measure.pi fun _ : k => samplingMeasure p).map (samplingSketchMatrix p)
   ```
   This is D4's wording verbatim and drops `[DecidableEq k]` from the law (`Measure.pi` does not
   need it; only `Fintype (k → n)` did, so Q11 is withdrawn). The mixture becomes the lemma
   `samplingSketch_eq_sum_smul_dirac [DecidableEq k] (p) : samplingSketch k p =
   ∑ ι, (∏ j, (p (ι j) : ℝ≥0∞)) • Measure.dirac (samplingSketchMatrix p ι)`, proved once and
   instance-polymorphically (`Measure.ext_of_singleton` on `k → n` through
   `Pi.instMeasurableSingletonClass`, `Measure.pi_pi` on `Set.pi univ (fun j => {ι j})`,
   `samplingMeasure_singleton`, the map of a finite sum of scaled Diracs by `mapₗ_apply_of_measurable`
   and `map_dirac`, measurability of `samplingSketchMatrix p` by `measurable_of_countable`). Every
   proof of §3.2 and §3.3 proceeds from this lemma, so the proofs are those of the draft.
   `samplingSketch_eq_map` under a user's instances is the lemma applied twice;
   `hasLaw_samplingSketchMatrix` stays as D4's bridge. §3's "Law" proof paragraph is replaced by
   this. **Pattern for S5, S6 and S7**: a law whose primitive randomness lives on a data or sketch
   index (S5's `uniformOn` on `k → n`, S6, S7's uniform hash `n → k`) is defined as the pushforward
   with the needed measurable space fixed by `letI := ⊤` inside the body, and its finite-mixture
   form is a lemma; no statement carries an instance on the index.
2. **Q1 relabelled** (§0 status, §7 header): an orchestrator decision, not a maintainer question
   (the brief's §1 kind (a) would have blocked the skeleton; it is not of that kind).
3. **§3.3, the D2-shaped AMM tail** (major). D2 fixes the AMM conclusion for every family as
   `μ.real {ω | ε * frobNorm A * frobNorm B ≤ frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B)} ≤ δ`, and
   S1 states it so (`HasJLMoment.measure_frobNorm_conjTranspose_mul_sub_ge_le`, with `hA hB : ≠ 0`).
   The free-threshold tail stays primary (it is more general); the instance `t = ε ‖A‖_F ‖B‖_F` is
   added so that an Estimation consumer takes the same event from every family. *Skeleton*:
   `measureReal_frobNorm_conjTranspose_mul_sub_ge_le_of_hasLaw_samplingSketch_of_ne_zero (hS) (hp)
   (hdom) (hε : 0 < ε) (hA : A ≠ 0) (hB : B ≠ 0)`, bound
   `L / (Fintype.card k * ε ^ 2 * frobNorm A * frobNorm B)`. Q6's last sentence now reads: the tail
   in `t` is primary, the `ε` form is its D2 instance.
4. **§3.2, `isFiniteMeasure_samplingSketch`**, an unconditional instance (as
   `isFiniteMeasure_samplingMeasure` in P2). `HasSubspaceEmbedding.mono` and `.of_range_le` and the
   `hp`-free corollaries (`U = 0`, empty `n`) need `[IsFiniteMeasure μ]`, which `HasLaw` transports
   only from a finite law; `isProbabilityMeasure_samplingSketch` needs `hp`, which they lack.
5. **§3.3, integrability beside unbiasedness.** New
   `integrable_conjTranspose_mul_mul_of_hasLaw_samplingSketch (hS) (A) (B)`, no `hp`, no
   `[Nonempty k]` (the sketch takes finitely many values a.e.), as the brief's §3 asks beside every
   expectation statement; the isotropy proof needs the entries' `MemLp 2` anyway.
6. **Q6, the support condition is the public hypothesis.** The prototype's identity holds under
   support alone (the junk `w_i² / 0 = 0` matches `w_i = 0`), which is strictly more general than
   `hpos` with the same conclusion (CONTRIBUTING §5.2, minimal hypotheses), and the domination
   form's proof needs exactly this lemma. Of the review's two options, the public one is taken: the
   unbiasedness and the exact identity take `hsupport : ∀ i, p i = 0 → A i = 0 ∨ B i = 0` in place
   of `hpos` (the review quotes the prototype's `vecMulVec (star (A i)) (B i) = 0`; the disjunction
   is equivalent, readable, and is what `hdom` yields through `mul_eq_zero` and `norm_eq_zero`).
   A user with `hpos` discharges it by `fun i h => absurd h (hpos i).ne'`; no `hpos` twin is
   stated. The draft's objection ("a raw condition written twice") is outweighed. Isotropy keeps
   `hpos` (at `A = B = 1` the support condition is `hpos`).
7. **§3.1, `leverageScore_eq_re_dotProduct_inv_mulVec` cut** (CONTRIBUTING §8.4): no consumer in §0,
   and a statistics bridge in a docstring is not one. `rangeProjector_eq_mul_inv_mul_conjTranspose`
   gives it in a few lines when a consumer asks; §1's "used directly" list loses that name, and
   `Leverage.lean` needs no `Matrix/Basic/Gram`.
8. **§3, degenerate paragraph corrected.** "The law is the zero measure, `HasLaw` forces `μ = 0`"
   holds for nonempty `k` only. For empty `k` the space `k → n` has one point, the law is
   `dirac 0`, a probability measure. The corollaries hold in both subcases (`U = 0` or empty `n`
   gives rank `0`, and every embedding event is full). *Skeleton*: `RowSampling.lean`'s module
   docstring states both.
9. **Q3, `U.rank` kept, justification replaced.** "Hard to reverse" is withdrawn. `U.rank` is the
   dominant form (rule 6): a `card r` form follows from it by `HasSubspaceEmbedding.mono` with
   `Matrix.rank_le_card_width` (and `samplingSize_mono` in `d`), and the converse is not derivable;
   it is also the form D2 (α) speaks in, and keeps the rank-deficient and `[A, y]` cases sharp. A
   later `card r` twin is a one-line corollary, never a rework.
10. **Q7 deferred, recorded.** Not now; open work for an S1 interface review. *Skeleton*: the
    docstring of `isIsotropicSketch_of_hasLaw_samplingSketch` says that zero weights give
    `E Sᴴ S = diagonal 1_{p > 0} ≤ 1` and that mixing `p = (ℓ/d + 1/n)/2` restores isotropy at
    `L = 2d` (`ℓ_i ≤ 2d p_i`). The round report's open work names the S1 change: replace `hiso` in
    the three fixed-`U` CEMT tails by `MemLp 2` entries plus `∫ (S ω)ᴴ * S ω ≤ 1`, or by a predicate
    with that field (sub-isotropy), under its own §5.4 review.
11. **§3.2 proof step 2.** After `HasLaw.hasSubspaceInjection_iff` the statement is about `id` under
    `samplingSketch`; reaching `Measure.pi` needs the same iff a second time, with
    `HasLaw (samplingSketchMatrix p) (samplingSketch k p) (Measure.pi …)`. With item 1's body this
    is the definition (the pushforward, with measurability of `samplingSketchMatrix p` by
    `measurable_of_countable` under the local `⊤`); the step-2 text of §3.2 is read with this
    second application.
12. **§3.3 instance needs.** The matrix-valued integrals (values in `Matrix q r 𝕜`) elaborate under the
    `L2Operator` normed group, and S1 §8 found `[DecidableEq p]` necessary for its square case:
    expect `[DecidableEq q]` on the Bochner statements of §3.3 at skeleton time.
13. **Files** (amends §4), 49 statements:
    1. `Leverage.lean` (17: 3 definitions, 14 theorems), item 7; imports
       `Matrix/Basic/{Projector,Orthonormal}`, `Matrix/Subspaces/ProjectorPair`.
    2. `RowSampling.lean` (25: 4 definitions, 1 instance, 20 theorems), §3.2 plus
       `samplingSketch_eq_sum_smul_dirac` (item 1) and `isFiniteMeasure_samplingSketch` (item 4).
    3. `MatrixMultiplication.lean` (7), §3.3 plus the integrability (item 5) and the D2-shaped tail
       (item 3).
14. §7: Q2, Q4, Q5, Q8, Q9 and Q10 stand; Q1 is decided by item 1, Q3's justification is item 9,
    Q6 is amended by items 3 and 6, Q7 is item 10, Q11 is withdrawn (item 1).
