# Design note: Sketching stage S2, Gaussian and Haar sketches

Status: drafted 2026-10-14 under `docs/PORT_SKETCHING.md` (D1 to D5; D12 to D14; §3, a guarantee `X ≤ c`
fails on `{c < X}`). No question of the brief's §2 kind (§7). Two lower-layer skeleton files (§3.1,
§3.2). **Maintainer checkpoint after this stage.**

## 0. Scope and consumers

`S = (√k)⁻¹ • G` for `HasLaw G (gaussianMatrix k n) μ` and `S = √(n / k) • Qᴴ` for
`HasLaw Q (haarFrame n k) μ`, `k ≤ n` (D13). In this note only `√k := √(Fintype.card k : ℝ)`, likewise
`√n`, `√p`, and `√d := √(d : ℝ)`. The Lean statements spell these out.

| Item | Consumers |
|---|---|
| isotropy (both), `specNorm S = √(n/k)` a.s. (Haar) | the OSIs; CEMT tails (S1 §3.4); LowRank R5, R6 (Haar test matrices) |
| fixed-`U` injection and embedding, oblivious OSE and OSI, tails in `t` (and `s`) | Solvers (sketch-and-solve, -precondition, `U = [A, y]`); LowRank R1, R2, R5, R6, HMT §11 through S1's Lemma 2.1; S1's transfer (generalized Nyström) |
| sizes `gaussianEmbeddingDim`, `gaussianInjectionDim`, `jlDim`; JL lemma (existence) | users holding `ε`, `δ`; Solvers |
| JL tail (DG form), exact JL second moment | Estimation (Hutch++, XTrace, through S1's AMM at `p = 2`) |
| Haar-to-Gaussian transfer of `(S U)ᴴ (S U)`; χ² and sphere tails, sphere fourth moment | the Haar embedding and JL; later Haar statements; E6 (random start) |

## 1. Objects

**No new law** (D4: "the Gaussian and sub-Gaussian sketches need no new law"; D13 for Haar): the
constructor is the scaling, written in each conclusion (§7 Q1). New named quantities (D5, §5.2 rule 2),
each an `irreducible_def` with nonnegativity or positivity, monotonicity and an explicit comparison:
- `gaussianEmbeddingDim d ε δ := 9 * (√d + √(2 * log (2 / δ))) ^ 2 / ε ^ 2`; comparison
  `≤ 18 * (d + 2 * log (2 / δ)) / ε ^ 2` (the prototype's constant);
- `gaussianInjectionDim d ε δ := 4 * (√d + √(2 * log (1 / δ))) ^ 2 / ε ^ 2`; comparison
  `≤ 8 * (d + 2 * log (1 / δ)) / ε ^ 2`;
- `jlDim ε δ := log (2 / δ) / (ε ^ 2 / 4 - ε ^ 3 / 6)`; comparison `≤ 12 * log (2 / δ) / ε ^ 2` for `ε ≤ 1`.

Used directly: S0, S1, R1, R3, R5 (names in the proof routes), P0's `measureReal_abs_ge_le_add`. No
deviation from Mathlib.

## 2. Interfaces

None new. Taken: `HasLaw G (gaussianMatrix k n) μ`, `HasLaw Q (haarFrame n k) μ`. Concluded: S1's seven
predicates other than `HasGramTraceMoment` (`HasJLMoment` at `p = 2`).

## 3. Statement shapes

`namespace NLAlib`, `open MeasureTheory ProbabilityTheory`, `open scoped Matrix MatrixOrder
Matrix.Norms.L2Operator`. Variables `{Ω} {mΩ} {μ : Measure Ω} {k n p ι : Type*}`, `[Fintype _]`,
`[DecidableEq _]` where `1` or `haarFrame` needs it, `{U : Matrix n p ℝ} {d : ℕ} {t s ε δ β : ℝ}`.

Degenerate cases. `card k = 0`: `(√0)⁻¹ = 0` and `√(n/0) = 0`, so `S = 0`; not isotropic (hence
`[Nonempty k]` on isotropy, OSI and moments); `htk : t ≤ √k - √p` then forces `p` empty and the fixed-`U`
predicates hold; JL bounds are `2`. `p` empty, `d = 0`: trivial. `t = 0` or `s = 0`: bounds `≥ 1`.
`t > √k - √p`: the squared lower base is wrong, hence `htk` (R3's `htn`). `ε ≥ 3/2`: the JL bound is
`≥ 2`; `1 ≤ ε`: the lower JL event is null; `ε < 0`: excluded (`0 ≤ ε`). `d > card n`: parameters at
`min d (card n)` and `mono` (S1 review item 4). Haar `k = n`: `S` orthogonal, the JL moment is `0`; the
upper half needs `hsk : s < √n - √k`, so it is stated for `k < n` only (§7 Q6).

### 3.1 `Probability/Distributions/ChiSquareTails.lean` (skeleton, 4)

`{X : Ω → n → ℝ} (hX : HasLaw X (gaussianVector n) μ)`.
```lean
theorem integral_exp_sum_mul_sq_of_hasLaw_gaussianVector (hX) {θ : n → ℝ} (hθ : ∀ i, 2 * θ i < 1) :
    ∫ ω, Real.exp (∑ i, θ i * X ω i ^ 2) ∂μ = ∏ i, (1 - 2 * θ i) ^ (-(1 / 2 : ℝ))
/-- **Upper Chernoff tail of `χ²_n`**; beside Laurent–Massart (the other shape, rule 4).
Result: chi-square-upper-tail -/
theorem measureReal_mul_card_le_norm_sq_le_of_hasLaw_gaussianVector (hX) (hβ : 1 ≤ β) :
    μ.real {ω | β * Fintype.card n ≤ ‖WithLp.toLp 2 (X ω)‖ ^ 2} ≤
      Real.exp (Fintype.card n / 2 * (1 - β + Real.log β))
/-- Result: chi-square-lower-tail -/
theorem measureReal_norm_sq_le_mul_card_le_of_hasLaw_gaussianVector (hX) (hβ0 : 0 < β) (hβ : β ≤ 1) :
    μ.real {ω | ‖WithLp.toLp 2 (X ω)‖ ^ 2 ≤ β * Fintype.card n} ≤
      Real.exp (Fintype.card n / 2 * (1 - β + Real.log β))
theorem measureReal_abs_norm_sq_div_card_sub_one_ge_le_of_hasLaw_gaussianVector (hX) (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |‖WithLp.toLp 2 (X ω)‖ ^ 2 / Fintype.card n - 1|} ≤
      2 * Real.exp (-(Fintype.card n * (ε ^ 2 / 4 - ε ^ 3 / 6)))
```
Proofs: `integral_fintype_prod_eq_prod`; Chernoff (`measure_ge_le_exp_mul_mgf`) with
`integral_exp_mul_norm_sq_of_hasLaw_gaussianVector` at `θ = (1 - 1/β)/2`; `log (1 + ε) ≤ ε - ε²/2 + ε³/3`,
`log (1 - ε) ≤ -ε - ε²/2` (the private `log_one_sub_le`, made public), small ball at `u = 0` for `ε ≥ 1`.
Searched: Mathlib has no χ² tail; NLAlib has only the lower Laurent–Massart form.

### 3.2 `RandomMatrix/Haar/Sphere.lean` (skeleton, 6)

`{u : Ω → n → ℝ} (hu : HasLaw u (uniformSphereVector n) μ) {V : Matrix n k ℝ} (hV : HasOrthonormalCols V)`.
```lean
/-- `Qᴴ x` for a unit `x` has the law of `Vᴴ u` for any frame `V` (`hV` gives `card k ≤ card n`). -/
theorem hasLaw_conjTranspose_mulVec_of_hasLaw_haarFrame {Q : Ω → Matrix n k ℝ}
    (hQ : HasLaw Q (haarFrame n k) μ) (hV) {x : n → ℝ} (hx : ‖WithLp.toLp 2 x‖ = 1) :
    HasLaw (fun ω => (Q ω)ᴴ *ᵥ x) ((uniformSphereVector n).map (Vᴴ *ᵥ ·)) μ
/-- **Projection of a uniform unit vector**, upper tail. [Vershynin2018, Lemma 5.3.2 (2020 draft)];
Dasgupta and Gupta 2003, Lemma 2.2 (to confirm, brief §7.2). -/
theorem measureReal_mul_div_le_norm_conjTranspose_mulVec_sq_le_of_hasLaw_uniformSphereVector (hu) (hV)
    (hβ : 1 ≤ β) : μ.real {ω | β * (Fintype.card k / Fintype.card n) ≤ ‖WithLp.toLp 2 (Vᴴ *ᵥ u ω)‖ ^ 2} ≤
      Real.exp (Fintype.card k / 2 * (1 - β + Real.log β))
-- lower twin (hβ0 : 0 < β) (hβ : β ≤ 1); two-sided, `ε ≤ |n / k * ‖Vᴴ u‖² - 1|`, `≤ 2 exp (-(k (ε²/4 - ε³/6)))`
/-- Fourth moment, from invariance alone (§7 Q5). -/
theorem integral_norm_conjTranspose_mulVec_pow_four_of_hasLaw_uniformSphereVector [Nonempty n] (hu) (hV) :
    ∫ ω, ‖WithLp.toLp 2 (Vᴴ *ᵥ u ω)‖ ^ 4 ∂μ =
      Fintype.card k * (Fintype.card k + 2) / (Fintype.card n * (Fintype.card n + 2))  -- + integrable_…
```
Proofs: the law by left invariance (`HasOrthonormalCols.exists_mul_eq` sends `x` to `Pi.single i 1`),
`Q ~ P V` (`hasLaw_mul_const_of_hasLaw_haarFrame`), a column of `Pᴴ` (`hasLaw_col_of_hasLaw_haarFrame`).
Tails (DG's proof): a coordinate frame by invariance, `u = g / ‖g‖`, the event `0 ≤ ∑ θᵢ gᵢ²` with two
weights, Chernoff with §3.1's first theorem.

### 3.3 `Sketching/Gaussian/Gaussian.lean` (27)

`{G : Ω → Matrix k n ℝ} (hG : HasLaw G (gaussianMatrix k n) μ)`; `S_G := fun ω => (√k)⁻¹ • G ω` in
this note (spelled out in Lean); `(ht : 0 ≤ t)`.
```lean
theorem isIsotropicSketch_of_hasLaw_gaussianMatrix [Nonempty k] (hG) : IsIsotropicSketch S_G μ
/-- One-sided, `e^{-t²/2}`. [MartinssonTropp2020, §8.7.2] (there `1 - (1 + √p)/√k - t`). -/
theorem HasOrthonormalCols.hasSubspaceInjection_of_hasLaw_gaussianMatrix (hU : HasOrthonormalCols U) (hG) (ht)
    (htk : t ≤ √k - √p) : HasSubspaceInjection S_G U ((1 - (√p + t) / √k) ^ 2) (Real.exp (-t ^ 2 / 2)) μ
/-- [Woodruff2014, Theorem 6] (`Θ`, no constant); [MartinssonTropp2020, §8.7.2]. Result: gaussian-ose -/
theorem HasOrthonormalCols.hasSubspaceEmbedding_of_hasLaw_gaussianMatrix (hU) (hG) (ht) (htk) : HasSubspaceEmbedding
    S_G U ((1 - (√p + t) / √k) ^ 2) ((1 + (√p + t) / √k) ^ 2) (2 * Real.exp (-t ^ 2 / 2)) μ
/-- The upper half alone: no `htk`, one tail. -/
theorem HasOrthonormalCols.hasSubspaceEmbedding_zero_of_hasLaw_gaussianMatrix (hU) (hG) (ht) :
    HasSubspaceEmbedding S_G U 0 ((1 + (√p + t) / √k) ^ 2) (Real.exp (-t ^ 2 / 2)) μ
/-- [CamanoEpperlyMeyerTropp2025, Definition 1.6, §1.5.0], who cite MT §8.7.2. Result: gaussian-osi -/
theorem isObliviousSubspaceInjection_of_hasLaw_gaussianMatrix [Nonempty k] (hG) (d : ℕ) (ht) (htd : t ≤ √k - √d) :
    IsObliviousSubspaceInjection S_G d ((1 - (√d + t) / √k) ^ 2) (Real.exp (-t ^ 2 / 2)) μ
theorem isObliviousSubspaceEmbedding_of_hasLaw_gaussianMatrix (hG) (d : ℕ) (ht) (htd) : IsObliviousSubspaceEmbedding
    S_G d ((1 - (√d + t) / √k) ^ 2) ((1 + (√d + t) / √k) ^ 2) (2 * Real.exp (-t ^ 2 / 2)) μ
/-- **Distributional JL**, Dasgupta–Gupta's exponent (D12). [Woodruff2014, Theorem 4, proof in
Lemma 18]; [MartinssonTropp2020, §8.6]. Result: jl-distributional -/
theorem hasJLProperty_of_hasLaw_gaussianMatrix (hG) (hε : 0 ≤ ε) :
    HasJLProperty S_G ε (2 * Real.exp (-(Fintype.card k * (ε ^ 2 / 4 - ε ^ 3 / 6)))) μ
/-- Exact: `E (‖S x‖² - ‖x‖²)² = 2 ‖x‖⁴ / k` (`Var χ²_k = 2k`). -/
theorem integral_norm_mulVec_sq_sub_norm_sq_sq_of_hasLaw_gaussianMatrix [Nonempty k] (hG) (x : n → ℝ) :
    ∫ ω, (‖WithLp.toLp 2 (S_G ω *ᵥ x)‖ ^ 2 - ‖WithLp.toLp 2 x‖ ^ 2) ^ 2 ∂μ =
      2 / Fintype.card k * ‖WithLp.toLp 2 x‖ ^ 4                            -- + integrable_…
/-- [Woodruff2014, Definition 12] at `p = 2`. -/
theorem hasJLMoment_of_hasLaw_gaussianMatrix [Nonempty k] (hG) (hε : 0 < ε) :
    HasJLMoment S_G ε (2 / (Fintype.card k * ε ^ 2)) 2 μ
-- sizes (§1): three defs, each with `_nonneg`/`_pos`, `_mono`, `_le` (9); then:
theorem isObliviousSubspaceEmbedding_of_hasLaw_gaussianMatrix_of_gaussianEmbeddingDim_le (hG)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hk : gaussianEmbeddingDim d ε δ ≤ Fintype.card k) :
    IsObliviousSubspaceEmbedding S_G d (1 - ε) (1 + ε) δ μ
theorem isObliviousSubspaceInjection_of_hasLaw_gaussianMatrix_of_gaussianInjectionDim_le (hG)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ < 1) (hk : gaussianInjectionDim d ε δ ≤ Fintype.card k) :
    IsObliviousSubspaceInjection S_G d (1 - ε) δ μ
theorem hasJLProperty_of_hasLaw_gaussianMatrix_of_jlDim_le (hG) (hε : 0 < ε) (hε1 : ε < 3 / 2)
    (hδ : 0 < δ) (hk : jlDim ε δ ≤ Fintype.card k) : HasJLProperty S_G ε δ μ
/-- **Johnson–Lindenstrauss lemma**, existence form. Result: jl-lemma -/
theorem exists_forall_abs_norm_mulVec_sq_sub_le_of_jlDim_le [Fintype ι] (x : ι → n → ℝ) (hε : 0 < ε)
    (hε1 : ε < 3 / 2) (hk : jlDim ε (1 / ((Fintype.card ι).choose 2 + 1)) ≤ Fintype.card k) :
    ∃ S : Matrix k n ℝ, ∀ i j, |‖WithLp.toLp 2 (S *ᵥ (x i - x j))‖ ^ 2 -
      ‖WithLp.toLp 2 (x i - x j)‖ ^ 2| ≤ ε * ‖WithLp.toLp 2 (x i - x j)‖ ^ 2
```
Proofs. Isotropy: S1's `isIsotropicSketch_smul_of_isIsotropic`, rows by `hasLaw_col_of_hasLaw_gaussianMatrix`
of `Gᴴ`. Fixed `U`: `G U` Gaussian (`hasLaw_mul_const_…`), R3's
`measureReal_not_smul_one_le_conjTranspose_mul_self_le_of_hasLaw_gaussianMatrix`, its upper twin, the
sandwich, `HasOrthonormalCols.isSubspaceInjection_iff`, `…smul_real` (S0 review item 3; `c ^ 2 = 1/k`).
Oblivious: S1's `…of_hasOrthonormalCols` at `Fin (min d (card n))` inside the proof, then `mono`. JL: `hasLaw_mulVec_…`
and §3.1's two-sided tail (`‖S x‖² = ‖G x‖² / k`), homogeneity. Moment: `integral_norm_sq_rpow_of_hasLaw_gaussianVector`
at `s = 1, 2` (`E (χ²_k)² = k (k + 2)`). Sizes: `t = √(2 log (2/δ))`, `(√d + t)/√k ≤ ε/3` gives
`1 - ε ≤ (1 - x)²`, `(1 + x)² ≤ 1 + ε`; injection `x ≤ ε/2`. Existence: S1's JL lemma, failure `< 1`.

### 3.4 `Sketching/Gaussian/Haar.lean` (12)

`{Q : Ω → Matrix n k ℝ} (hQ : HasLaw Q (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n)`;
`S_H := fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ`; `(ht : 0 ≤ t) (hs : 0 ≤ s)`;
`a_H := (1 - (√p + t) / √k) ^ 2 / (1 + (√k + s) / √n) ^ 2`,
`b_H := (1 + (√p + t) / √k) ^ 2 / (1 - (√k + s) / √n) ^ 2` (with `√d` for `√p` in the oblivious forms).
```lean
/-- Exact isotropy, which a Gaussian also has; and, unlike it, a deterministic norm. [MartinssonTropp2020, §8.9] -/
theorem isIsotropicSketch_of_hasLaw_haarFrame [Nonempty k] (hQ) (hk) : IsIsotropicSketch S_H μ
theorem ae_specNorm_eq_of_hasLaw_haarFrame [Nonempty k] (hQ) (hk) :
    ∀ᵐ ω ∂μ, specNorm (S_H ω) = √(Fintype.card n / Fintype.card k : ℝ)
/-- **Gaussian transfer** (R5, `Transfer.lean` at `A = 1`): the Haar Gram matrix on `U` has the law of
`(n/k) Uᴴ P_G U`, `P_G` the range projector of an `n × k` Gaussian. -/
theorem hasLaw_conjTranspose_mul_self_mul_of_hasLaw_haarFrame (hQ) (hk) (U : Matrix n p ℝ) :
    HasLaw (fun ω => (S_H ω * U)ᴴ * (S_H ω * U))
      ((gaussianMatrix n k).map fun G => (Fintype.card n / Fintype.card k : ℝ) • (Uᴴ * rangeProjector G * U)) μ
theorem HasOrthonormalCols.hasSubspaceInjection_of_hasLaw_haarFrame (hU) (hQ) (hk) (ht) (htk : t ≤ √k - √p) (hs) :
    HasSubspaceInjection S_H U a_H (Real.exp (-t ^ 2 / 2) + Real.exp (-s ^ 2 / 2)) μ
theorem HasOrthonormalCols.hasSubspaceEmbedding_of_hasLaw_haarFrame (hU) (hQ) (hk) (ht) (htk) (hs) (hsk : s < √n - √k) :
    HasSubspaceEmbedding S_H U a_H b_H (2 * Real.exp (-t ^ 2 / 2) + 2 * Real.exp (-s ^ 2 / 2)) μ
-- oblivious forms (2): `isObliviousSubspaceInjection_of_hasLaw_haarFrame [Nonempty k] (hQ) (hk) (d) (ht) (htd) (hs)`,
-- `isObliviousSubspaceEmbedding_of_hasLaw_haarFrame (hQ) (hk) (d) (ht) (htd) (hs) (hsk)`, same `δ`. Result: haar-sketch-ose (new)
/-- The Gaussian's constants. [Vershynin2018, Lemma 5.3.2 (2020 draft)]. -/
theorem hasJLProperty_of_hasLaw_haarFrame (hQ) (hk) (hε : 0 ≤ ε) :
    HasJLProperty S_H ε (2 * Real.exp (-(Fintype.card k * (ε ^ 2 / 4 - ε ^ 3 / 6)))) μ
/-- Exact: `2 (n - k) / (k (n + 2))`, below the Gaussian's `2 / k`; `0` at `k = n`. -/
theorem integral_norm_mulVec_sq_sub_norm_sq_sq_of_hasLaw_haarFrame [Nonempty k] (hQ) (hk) (x : n → ℝ) : -- + integrable_…
    ∫ ω, (‖WithLp.toLp 2 (S_H ω *ᵥ x)‖ ^ 2 - ‖WithLp.toLp 2 x‖ ^ 2) ^ 2 ∂μ =
      2 * (Fintype.card n - Fintype.card k) / (Fintype.card k * (Fintype.card n + 2)) * ‖WithLp.toLp 2 x‖ ^ 4
theorem hasJLMoment_of_hasLaw_haarFrame [Nonempty k] (hQ) (hk) (hε : 0 < ε) : HasJLMoment S_H ε
    (2 * (Fintype.card n - Fintype.card k) / (Fintype.card k * (Fintype.card n + 2) * ε ^ 2)) 2 μ
theorem hasJLProperty_of_hasLaw_haarFrame_of_jlDim_le (hQ) (hk) (hε : 0 < ε) (hε1 : ε < 3 / 2)
    (hδ : 0 < δ) (hk' : jlDim ε δ ≤ Fintype.card k) : HasJLProperty S_H ε δ μ
```
Proofs. Isotropy: `integral_mul_conjTranspose_of_hasLaw_haarFrame`, `memLp_apply_of_hasLaw_haarFrame`;
norm: `HasOrthonormalCols.specNorm_eq_one`. Transfer: `HasOrthonormalCols.rangeProjector_eq` a.s.,
`hasLaw_rangeProjector_mul_of_hasLaw_haarFrame` (`A = 1`), `HasLaw.comp`. Embedding (D13): a.s.
`IsUnit (Gᴴ G)` (`ae_isUnit_conjTranspose_mul_self_mul_…`), `rangeProjector_eq_mul_inv_mul_conjTranspose`
gives `Uᴴ P_G U = (Gᴴ U)ᴴ (Gᴴ G)⁻¹ (Gᴴ U)` with `Gᴴ U` a `k × p` Gaussian; R3's tails for `Gᴴ U` (`t`) and
`G` (`s`), a union bound (no independence), `Matrix.PosDef.inv_le_inv_of_le`,
`inv_le_inv_smul_one_of_smul_one_le`, `conjTranspose_mul_mul_le_conjTranspose_mul_mul`; two tails for the
injection, four for the embedding. JL, moment: §3.2, `‖S x‖² = (n/k) ‖Vᴴ u‖²`, `E ‖Vᴴ u‖² = k/n`.

## 4. Files

1. `NLAlib/Probability/Distributions/ChiSquareTails.lean` (skeleton): §3.1 (4); imports `ChiSquare`.
2. `NLAlib/RandomMatrix/Haar/Sphere.lean` (skeleton): §3.2 (6); imports 1, `Haar/Uniqueness`.
3. `Sketching/Gaussian/Gaussian.lean`: §3.3 (27); imports 1, S1, R3 `ExtremeSingularValues`, `ChiSquareMoments`.
4. `Sketching/Gaussian/Haar.lean`: §3.4 (12); imports 2, 3, `Haar/{Moments,Transfer}`.
1 and 2 merge into `ChiSquare.lean` and a Haar owner file at the wrap-up. About 1000 lines against the
brief's 650; the overrun is §3.1, §3.2 (§7 Q8). Bibliography: nothing new (`Woodruff2014`,
`MartinssonTropp2020`, `Vershynin2018`, `CamanoEpperlyMeyerTropp2025` from S0).

## 5. Material

Read: the prototype's `Sketching/Gaussian/GaussianEmbedding.lean` (2 declarations) and
`Properties/JL/JL.lean` (six left by S1); it has no Haar sketch. CEMT §1.5.0, Definition 1.6; MT §8.5 to
§8.9; Woodruff Theorems 4, 6, Lemma 18; Vershynin Lemma 5.3.2. Ledger:
`one_sub_le_measure_isSubspaceEmbedding_gaussianMatrix` (`k ≥ 18 (d + 2 log (2/δ)) / ε²`) → the
`gaussianEmbeddingDim` corollary (that constant is its comparison); `isSubspaceEmbedding_of_forall_sqrt_le`
(`3 a ≤ ε`) → not ported (D1); `jl_distributional`, `…_of_hasLaw` → `hasJLProperty_of_hasLaw_gaussianMatrix`
(no `ε < 1`); `sq_div_four_sub_pow_three_div_six_pos`, `sq_mul_two_mul_exp_neg_mul_le_of_inv_mul_log_le`,
`jl_lemma_prob_le_of_log_le` → `jlDim` and its corollary; `jl_lemma_prob_le_half` → dominated (rule 6);
`jl_lemma_exists` → the existence form. Result ids: `gaussian-ose`, `jl-distributional`, `jl-lemma`,
`chi-square-upper-tail`, `chi-square-lower-tail`; new `gaussian-osi`, `haar-sketch-ose`.

## 6. Cut, and why

Success forms, `Fin`, `ENNReal`, `_of_hasLaw` twins (brief §6); unnormalized `G` (`smul_real` and R3
give it); `HasGramTraceMoment` (not asked; the Gaussian's exact `d (d + 1) / k` gives an OSE dominated
by Gordon's); AMM from the exact Gaussian variance (same worst case as S1's); the JL moment at `p ≠ 2`
(Q4); Haar sizes and a sharp Haar embedding near `k = n` (Q6); sketch-level one-sided JL halves.

## 7. Questions and decisions

**For the maintainer:** none of the brief's §2 kind. **Decisions taken** (open to correction):

**Q1. No new law**, by D4's text ("need no new law") and D13. Named laws `gaussianSketch k n`,
`haarSketch k n` (pushforwards under the scalings) would change only each S2 hypothesis; added when a
consumer holds `S` rather than `G` or `Q`.

**Q2. CEMT give no Gaussian or Haar OSI theorem**: §1.5.0 defers to MT §8.7.2 (`α ≥ 1/2` at `k = O(r)`).
The OSI's better constant is the one-sided tail `e^{-t²/2}` (R3) against `2 e^{-t²/2}`; R3's
`√k - √p - t` also beats MT's `√k - 1 - √p - t`. Cited: MT §8.7.2, CEMT Definition 1.6.

**Q3. JL in Dasgupta–Gupta form for both families and every `ε ≥ 0`** (no `ε < 1`). Lower layers carry
DG Lemma 2.2's `exp ((k/2)(1 - β + log β))`; sketches the polynomial exponent (D12). DG is not in hand:
docstrings cite Woodruff Theorem 4 / Lemma 18, Vershynin Lemma 5.3.2, "constant of Dasgupta and Gupta
2003, locator to confirm".

**Q4. JL moment at `p = 2`, exact** (amends the brief's "from the tail"): what S1's AMM and Estimation
take. General `p` needs the tail for all `t` and a named Gamma-integral constant; deferred to a consumer.

**Q5. The sphere's fourth moment from invariance alone**, correcting R5 §7 Q4: `∑ uᵢ² = 1` and the `45°`
rotation give `E u₁⁴ = 3 E u₁² u₂²`, `n (n + 2) E u₁² u₂² = 1`. No radius–direction independence.

**Q6. Haar embedding by D13's Gaussian route**, parameters `t` (subspace) and `s` (frame). Lossy near
`k = n` (`a_H ≈ (1 - √(p/n))² / 4` at `k = n`, truth `1`); the upper half needs `k < n`. No Haar sizes:
inversion needs a condition on `n` too. A sharp form (`Q⊥`, or convex order after S5) is later work.

**Q7.** Sizes are `irreducible_def`s whose bodies are what S2's proofs reach. **Q8.** Two lower-layer
skeleton files amend the brief's list; about 1000 lines against its 650. **Q9.** `hk` explicit in §3.4;
§3.2's law lemma drops it (`hV` implies it).

## 8. Amendments from the review (2026-10-14)

Fable review of this note, all findings accepted by the orchestrator; finding 3 adopted as two new
statements (`k ≈ n` is the regime the Haar family exists for). Where an item below contradicts §0
to §7, it supersedes them. Skeletons: the four §4 files, every proof `sorry`.

1. **§3.1, χ² lower tail: rule 6, not rule 4.** The new lower tail `exp ((n/2)(1 - β + log β))`
   dominates both existing lower bounds: Laurent–Massart (`β = 1 - 2√(t/n)`, with
   `log (1 - u) ≤ -u - u²/2`) and the small ball `(e u / n)^{n/2}` (`β = u/n`, the same Chernoff
   parameter `s = (n/u - 1)/2`, after dropping `e^{-u/2} ≤ 1`); the private
   `measureReal_norm_sq_le_le_exp_mul_rpow` (`ChiSquare.lean`) is the lower tail before
   optimisation. Correction to §3.1's "NLAlib has only the lower Laurent–Massart form": it has
   Laurent–Massart, the small ball and that private Chernoff bound. *Skeleton*: the lower tail's
   docstring says so and that at the merge both older bounds are reproved from it and keep their
   names; the upper tail's docstring says it is at least as good as Laurent–Massart's upper tail
   at every threshold, which stays as `IsSubgaussianVector.measure_norm_sq_ge_le` at proxy `1`.
2. **Haar upper half, deterministic.** `(S_H U)ᴴ (S_H U) ≤ (n/k) • (Uᴴ U)` a.s., no parameter
   (`Q Qᴴ ≤ 1`). *Skeleton*: `ae_conjTranspose_mul_self_mul_le_smul_of_hasLaw_haarFrame`, for
   every `U` and every shape (no `hk`: `ae_specNorm_le_one_of_hasLaw_haarFrame` holds in every
   shape); `HasOrthonormalCols.hasSubspaceEmbedding_of_hasLaw_haarFrame` now has constants
   `a_H`, `n/k` and failure `e^{-t²/2} + e^{-s²/2}`, with no `hsk` and no `k < n`; the `b_H` form
   is kept, incomparable (rule 4), as `…_of_lt_sqrt_sub_sqrt` (named by its hypothesis `hsk`).
   The §3 caveat "the upper half … is stated for `k < n` only" and §7 Q6's "the upper half needs
   `k < n`" are withdrawn. The oblivious forms follow the same split:
   `isObliviousSubspaceEmbedding_of_hasLaw_haarFrame` (`n/k`, added) and
   `…_of_lt_sqrt_sub_sqrt` (`b_H`).
3. **Lower half near `k = n`, complement route** (two statements in `Haar.lean`). `Q ~ P V₁`,
   `Q⊥ := P V₂` (`hasLaw_mul_const_of_hasLaw_haarFrame` on a square Haar `P`, selection
   matrices), `Uᴴ Q Qᴴ U = 1 - Uᴴ Q⊥ Q⊥ᴴ U`, the inverse-Gram step on an `n × (n - k)` Gaussian.
   *Skeleton*: `HasOrthonormalCols.hasSubspaceInjection_of_hasLaw_haarFrame_of_card_add_eq` and
   `…hasSubspaceEmbedding_…_of_card_add_eq` (upper constant `n/k` by item 2). The codimension is
   an auxiliary `c : ℕ` with `hc : card k + c = card n` (§5.3 "index shift"; it replaces `hk`),
   so `√(n - k)` is `√c`; constant `(n/k)(1 - (√c + √p + t)² / (√n - √c - s)²)`, failure
   `e^{-t²/2} + e^{-s²/2}`, for `t ≥ 0`, `0 ≤ s < √n - √c` (strict: at equality the denominator
   is `0` and `x / 0 = 0` would make the constant `n/k`). No `t` condition: a negative constant
   is vacuous. Docstrings: tends to `1` as `c/n → 0`, vacuous at `k = n/2`, incomparable with
   `a_H` (rule 4). Oblivious forms of this route are not stated (`of_hasOrthonormalCols` and
   `mono` give them when a consumer asks).
4. **Citations.** JL (Gaussian): `[Woodruff2014, Lemma 18] (there ε² k / 16);
   [MartinssonTropp2020, §8.6]`, exponent of Dasgupta and Gupta (D12); the JL lemma cites
   `[Woodruff2014, Theorem 4]` (the f-point JLT). §3.2's "Lemma 2.2" is dropped (Dasgupta and
   Gupta 2003 cited by name only). MT §8.7.2 is cited as "there `… - t/√k` for our `t`".
   Vershynin's Lemma 5.3.2 (2020 draft) is cited "with an unspecified constant `c`".
5. **Hypotheses.** The Haar moment and JL-moment `δ` are written with `((card n : ℝ) - card k)`.
   The OSE size corollary drops `hδ1 : δ ≤ 1` (`δ ≥ 2` is trivial, `δ < 2` is the proof); the
   OSI size corollary has `hε2 : ε ≤ 2` in place of `ε ≤ 1`. `jlDim_le` takes `0 < δ ≤ 2`, and
   `jlDim`'s docstring states the junk value for `ε ≥ 3/2`. `[Nonempty k]` is not a hypothesis of
   the size corollaries: `gaussianInjectionDim_pos` (`δ < 1`) gives it.
6. **§3.2 routes; `k = n`.** No sphere-invariance lemma exists: the tails go through
   `u = g / ‖g‖`, `W = [V, V⊥]ᴴ` from `HasOrthonormalCols.exists_fromCols` and
   `hasLaw_mulVec_of_hasLaw_gaussianVector` (module docstring of `Sphere.lean`). The fourth
   moment's `45°` rotation needs `card n ≥ 2`; `card n = 1` is `u = ±1` (docstring). At `k = n`:
   `hasSubspaceEmbedding_of_hasLaw_haarFrame_of_card_eq`, `HasSubspaceEmbedding S_H U 1 1 0 μ`
   for every `U`.
7. Files correctly placed. §7: Q1 to Q5 and Q7 to Q9 stand (Q4: `p = 2` only); Q6 is replaced by
   items 2 and 3.

**Skeleton-level changes** (same meaning unless said): `ae_specNorm_eq_of_hasLaw_haarFrame` drops
`[Nonempty k]` (both sides are `0` for empty `k`); the Sphere `integrable_…` lemma takes any `V`
(no `hV`); the Gaussian isotropy docstring carries no MT locator (none in hand); the Haar OSI gets
the new id `haar-sketch-osi`. **File list** (amends §4): `ChiSquareTails.lean` 4, `Sphere.lean` 6,
`Sketching/Gaussian/Gaussian.lean` 26 (3 definitions, 9 size lemmas, 14 theorems),
`Sketching/Gaussian/Haar.lean` 18 (the 12 of §3.4, its two `hsk` shapes renamed
`…_of_lt_sqrt_sub_sqrt`; plus the a.s. upper half, the `n/k` embedding and OSE, the `k = n`
embedding and the two complement statements).

**Wrap-up (2026-10-15).** `Sketching/Gaussian/Haar.lean` (1091 lines) is split by topic: `Haar.lean`
keeps isotropy, the norm, the Gaussian transfer, the deterministic halves and the JL results, and
the new `Sketching/Gaussian/HaarEmbedding.lean` holds the fixed-subspace and oblivious embeddings
(§3.4's tails). The Gram identity of the sketch is public as
`conjTranspose_mul_self_sqrt_card_div_smul_conjTranspose_mul`, used by both. `Sphere.lean` stays a
topic file in `RandomMatrix/Haar` (the uniform unit vector: its projected law, tails and fourth
moment), not merged into `Moments.lean` (second moments of a frame): together they would be
about 990 lines on two topics. `Gaussian.lean` gains the public
inversion `two_mul_exp_le_of_jlDim_le`, shared by the Gaussian, Haar and sign sketches.
