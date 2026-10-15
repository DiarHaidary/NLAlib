# Design note: Sketching stage S6, the subsampled randomized trigonometric transform (SRHT)

Status: drafted 2026-10-15 under `docs/PORT_SKETCHING.md` (D3 row "SRHT and SRFT", D4, D5, D9, D10,
D11, D12, D14, D15; §3; the S6 entry of §4); reviewed 2026-10-15, amendments in §8, which overrides
§0 to §7 where they disagree. Builds on S4 (proved:
`NLAlib/Sketching/Sampling/{Leverage,RowSampling,MatrixMultiplication}.lean`) and on S5
(`docs/design/Sketching-S5.md`, reviewed, not yet in Lean; this note relies on its §3, on the law
`samplingSketchWithoutReplacement k n` and on its domination shape
`∀ i, leverageScore U i ≤ L * (Fintype.card n : ℝ)⁻¹`; if S5's §8 renames any of them, S6 follows).
Laws follow S4 §8 item 1 (pushforward of a public constructor, `letI := ⊤` inside the body, the
explicit form a lemma). The Walsh–Hadamard and unitary Fourier matrices exist
(`NLAlib/Matrix/Structured/{Walsh,Circulant}.lean`). **Missing below Sketching** (§8 item 15): the
general Hsu–Kakade–Zhang tail with its sub-gamma Chernoff step (three Probability statements, §8
item 2), one independence lemma (sections of a product event, §7 Q5), the transform interface
`IsBoundedOrthonormal` with its instances (§8 item 6), and one identity in S4's file. Two
Sketching files, as the brief lists. Q1 and Q2 decided by the orchestrator (§8 items 1, 6); nothing
for the maintainer.

## 0. Scope and consumers

A fixed unitary transform `F : Matrix n n 𝕜` whose entries are uniformly small,
`card n * ‖F i j‖ ^ 2 ≤ β` (`β = 1` for Walsh–Hadamard and Fourier, `β = 2` for the discrete
Hartley and cosine transforms), independent signs `ξ ~ rademacherVector n`, `D = diagonal ξ`, and
`k` indices `ι : k → n`, either a uniform injection (without replacement, the classical SRHT of
Tropp 2011a and HMT §11) or i.i.d. uniform (with replacement). The sketch is
`S = √(n/k) • Pᴴ * F * D`, where `√(n/k) • Pᴴ` is S4's `samplingSketchMatrix` at uniform weights.
Over `𝕜` throughout (D11): the signs are real for both fields, `F` is any `RCLike` matrix.
In this note `d := U.rank`, `D ξ := Matrix.diagonal fun i => (ξ i : 𝕜)`, and
`L_d(t) := β * (d + 2 * √(d * t) + 2 * t)`; the Lean statements spell these out.

The proof is two steps, each a public theorem: **flattening** (`F D U` has all leverage scores at
most `L / n` outside `n e^{-t}`) and **flatten, then sample** (a sampler that injects every
`L`-incoherent subspace, independent of a random unitary `T` that makes `T U` incoherent, injects
`range U` after `T`). The family theorems instantiate the second with S4's and S5's tails.

| Item | Consumers |
|---|---|
| flattening tail, `srhtRowBound` | the SRHT theorems here; CEMT's SparseRTT (Theorem 4.2, through their Imported Theorem 4.3, which this is), when sparse samplers are taken up (brief §4a); any "rotate, then sample uniformly" analysis in LowRank (column sampling after a random transform) |
| flatten-then-sample transfer (injection, embedding) | both SRHT models here; rerandomized transforms (MT Remark 9.2, `T = F D' F D`); SparseRTT later with CEMT's SparseCol sampler (their Theorem 4.4 is exactly its `hsample`); a Haar-rotated sampler |
| `srhtMatrix`, `srht`, `srhtWithReplacement`, the bridges | users who hold signs and indices; LowRank test matrices; Solvers' Blendenpik-type preconditioners |
| isotropy | the OSI (S1); S1's CEMT tails (Lemma 2.1, sketch-and-solve Theorem 2.7) |
| `S Sᴴ = (n/k) • 1`, `specNorm S = √(n/k)` a.s. (without replacement) | LowRank: HMT Theorem 11.2 and MT Theorem 11.6 bound `‖Ω₂‖ ≤ √(n/ℓ)` with it |
| OSI (lower Chernoff half) | LowRank: the range finder (CEMT Theorem 2.2; HMT §11 uses only the lower half), Nyström, generalized Nyström; Solvers: constant-factor sketch-and-solve (CEMT Theorem 2.7) |
| OSE | Solvers: sketch-and-precondition and Blendenpik (both halves, `√(b/a)`, S0), sketch-and-solve |
| size corollaries | consumers who fix `δ` and invert; the comparison with Woodruff's Theorem 7 and MT Theorem 11.6 |

Not in S6: JL and AMM for the SRHT (D3 lists OSE and OSI only), complex Steinhaus signs (HMT's SRFT,
§6), random permutations `Π` (MT §9.3; not needed by the analysis), sparse samplers (brief §4a).

## 1. Objects

New §5.3 row (§7 Q3; two approvals by CONTRIBUTING §9):

| Concept | Spelling | Bridge |
|---|---|---|
| subsampled randomized trigonometric transform | constructor `srhtMatrix F ξ ι` (S4's `samplingSketchMatrix` at uniform weights, times `F`, times `D ξ`); laws `srht k F` (uniform injection) and `srhtWithReplacement k F` (i.i.d. uniform), pushforwards with `letI := ⊤` inside | `srht_eq_map_prod` (signs ⊗ S5's law), `srhtWithReplacement_eq_map_prod` (signs ⊗ S4's law), `hasLaw_srhtMatrix_of_hasLaw_uniformOn_injective`, `hasLaw_srhtMatrix_of_hasLaw_pi` |

One named quantity, `srhtRowBound n d δ` (D5, D11), an `irreducible_def` (§7 Q6). No other new
definition: the transform `F * D ξ` and the per-row matrices of the flattening proof are inline or
private (the prototype's `srhtSignedFrame`, `srhtNormalizedRow`, `srhtPopulationAtom` are not
reproduced).

**Used directly.** Matrix layer: `walshHadamard`, `hasOrthonormalCols_smul_walshHadamard`,
`norm_smul_walshHadamard_apply` (`Structured/Walsh`); `fourierMatrix`,
`hasOrthonormalCols_fourierMatrix`, `norm_fourierMatrix_apply` (`Structured/Circulant`, over `ℂ`);
`exists_hasOrthonormalCols_range_eq`, `HasOrthonormalCols.rank_mul`,
`HasOrthonormalCols.conjTranspose_mul_mul`, `frobNorm_sq_eq_sum`,
`frobNorm_mul_le_specNorm_mul_frobNorm`, `specNorm_transpose`, `specNorm_diagonal_le`. Probability:
`rademacherVector`, `ae_sq_eq_one_of_hasLaw_rademacherVector`,
`isSubgaussianVector_of_hasLaw_rademacherVector`, `IsSubgaussianVector.mulVec`, `.mono`,
`.measure_norm_sq_ge_le`, `measurable_rangeProjector` (`Probability/Measurability/Matrix`),
`samplingMeasure`, `samplingMeasure_const_inv_card`. Mathlib: `Matrix.IsHadamard`,
`Measure.prod`, `Measure.prod_apply`, `measurable_measure_prodMk_left`,
`indepFun_iff_hasLaw_prodMk_prod` (`IndepFun.hasLaw_prod`), `measurable_from_prod_countable_left`,
`uniformOn`, `measureReal_iUnion_fintype_le`. S0 and S1: `isClosed_setOf_isSubspaceInjection`,
`isClosed_setOf_isSubspaceEmbedding`, `HasLaw.hasSubspaceInjection_iff`,
`HasLaw.hasSubspaceEmbedding_iff`, `HasLaw.isIsotropicSketch_iff`, `IsIsotropicSketch.mul`,
`HasSubspaceInjection.mono`, `HasSubspaceEmbedding.mono`, the two oblivious structures. S4:
`samplingSketchMatrix`, `samplingSketch`, `hasSubspaceInjection_of_hasLaw_samplingSketch`,
`hasSubspaceEmbedding_of_hasLaw_samplingSketch`, `isIsotropicSketch_of_hasLaw_samplingSketch`,
`leverageScore_eq_of_range_eq`, `HasOrthonormalCols.leverageScore_eq`, `samplingSize`,
`samplingInjectionSize` and their `_le`, `_mono`. S5 (§3.4 of its note):
`samplingSketchWithoutReplacement`, `isFiniteMeasure_…`, `isProbabilityMeasure_…`,
`isIsotropicSketch_of_hasLaw_samplingSketchWithoutReplacement`,
`hasSubspaceInjection_of_hasLaw_samplingSketchWithoutReplacement`,
`hasSubspaceEmbedding_of_hasLaw_samplingSketchWithoutReplacement`.

**Searched, none.** Mathlib: no SRHT, SRTT, fast JL or randomized Hadamard sketch; `Matrix.IsHadamard`
is the unnormalized `±1` (or unimodular) matrix with `A Aᴴ = n • 1`, not the normalized transform
(bridge below). No tail for `‖A X‖²` with a general `A` (Mathlib or NLAlib; NLAlib has `A = 1`). No
lemma bounding `μ` of an event of two independent variables through its sections with an
exceptional set (Mathlib has the ingredients, `Measure.prod_apply`; NLAlib has the special case
`δ₂ = 0` as the private `measureReal_not_le_of_indepFun` in `Properties/Oblivious.lean`). No
realification of a `𝕜`-matrix acting on real vectors.

**Lower-layer additions** (each a public statement, owner file named; §4 counts them):
1. *Probability* (`Probability/SubGaussianVector/Norm.lean`): the tail of `‖A X‖²` for a real
   sub-Gaussian vector and a real matrix `A`, Hsu, Kakade and Zhang's Theorem 2.1 in full:
   ```lean
   theorem IsSubgaussianVector.measure_norm_mulVec_sq_ge_le {m : Type*} [Fintype m]
       {X : Ω → n → ℝ} (h : IsSubgaussianVector X c μ) (hc : c ≠ 0) {A : Matrix m n ℝ}
       (hA : A ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
       μ.real {ω | c * (frobNorm A ^ 2 + 2 * frobNorm (Aᴴ * A) * √t + 2 * specNorm A ^ 2 * t) ≤
         ‖WithLp.toLp 2 (A *ᵥ X ω)‖ ^ 2} ≤ Real.exp (-t)
   ```
   The existing `measure_norm_sq_ge_le` is its case `A = 1` and is reproved from it, keeping its
   name (CONTRIBUTING §5.2 rule 6). Proof: `Aᴴ A = V diag(λ) Vᴴ` (Mathlib's spectral theorem over
   `ℝ`), `Y = Vᴴ X` has proxy `c` (`IsSubgaussianVector.mulVec`, `specNorm Vᴴ = 1`),
   `‖A X‖² = ∑ λ_i Y_i²`; the file's private Gaussian linearization with `u = √λ ⊙ g` in place of
   `g` gives `E exp (θ ∑ λ_i Y_i²) ≤ ∏ (1 - 2θcλ_i)^{-1/2}`; then Laurent and Massart's weighted
   optimization with `∑ λ = ‖A‖_F²`, `∑ λ² = ‖Aᴴ A‖_F²`, `max λ = ‖A‖²`. About 250 lines;
   moderate. Why it is needed: §7 Q1.
2. *ForMathlib* (new `ForMathlib/Probability/Independence/Basic.lean`, upstream candidate): the
   sections lemma, §3.1; `Properties/Oblivious.lean`'s private helper is reproved from it in the
   same PR (an exact overlap ships as a one-line proof, CONTRIBUTING §8).
3. *Matrix layer*: in `Structured/Walsh.lean`, `card_mul_norm_smul_walshHadamard_apply_sq`
   (`card * ‖((√(2^b))⁻¹ • walshHadamard 𝕜 b) x y‖ ^ 2 = 1`) and the Mathlib bridge
   `Matrix.IsHadamard.hasOrthonormalCols_inv_sqrt_smul`,
   `Matrix.IsHadamard.card_mul_norm_inv_sqrt_smul_apply_sq` (for `H.IsHadamard` over `𝕜`, the matrix
   `(√card n)⁻¹ • H` satisfies the transform hypotheses at `β = 1`); in `Structured/Circulant.lean`,
   `card_mul_norm_fourierMatrix_apply_sq` (`= 1`). Four one- or few-line lemmas (§7 Q2, Q8).
4. *S4's file* (`Sampling/RowSampling.lean`, the owner of the constructor; a dated amendment to S4's
   note): for an injective `ι`, `samplingSketchMatrix p ι * (samplingSketchMatrix p ι)ᴴ =
   diagonal fun j => (((card k * p (ι j))⁻¹ : ℝ) : 𝕜)` (the rows have disjoint supports). S5 §6
   left this to S6 (§7 Q7).

**Deviation from Mathlib**: the transform hypothesis is `HasOrthonormalCols F` plus an entry bound,
not Mathlib's `Matrix.IsHadamard` (§7 Q2); an entry in `docs/design/Mathlib-deviations.md` in the
skeleton's commit, with the bridge of item 3.

## 2. Interfaces

None new. Taken: `HasLaw S (srht k F) μ`, `HasLaw S (srhtWithReplacement k F) μ`,
`HasLaw ξ (rademacherVector n) μ`; the transform hypotheses `hF : HasOrthonormalCols F` and
`hFβ : ∀ i j, (Fintype.card n : ℝ) * ‖F i j‖ ^ 2 ≤ β` (§7 Q2; the hypothesis shape is fixed here,
as D8 fixed the domination shape); S5's domination at uniform weights
`∀ i, leverageScore V i ≤ L * (Fintype.card n : ℝ)⁻¹`, which the flattening concludes and the
transfer consumes. Concluded: `IsIsotropicSketch`, `HasSubspaceInjection`, `HasSubspaceEmbedding`,
`IsObliviousSubspaceInjection`, `IsObliviousSubspaceEmbedding` (S1). The transfer's sampler
hypothesis `hsample` (injection on every incoherent subspace of rank at most `d`) is a raw
quantified hypothesis in two theorems of one file; it becomes a predicate when a second consumer
appears (§7 Q4).

## 3. Statement shapes

`namespace NLAlib`, `open MeasureTheory ProbabilityTheory`, `open scoped Matrix MatrixOrder NNReal
ENNReal`, and `Matrix.Norms.L2Operator` where an integral of matrices appears. Variables
`{Ω} {mΩ} {μ : Measure Ω} {𝕜} [RCLike 𝕜] {k n r : Type*} [Fintype k] [Fintype n] [Fintype r]
[DecidableEq n] {S : Ω → Matrix k n 𝕜} {F : Matrix n n 𝕜} {ξ : Ω → n → ℝ} {β L a b ε t δ δ₁ δ₂ : ℝ}`.

Degenerate cases.
- `d = 0`: every leverage score of `F D U` is `0`, so the flattening event is empty, and every
  sketch event is empty (S4 §3.2).
- `card k = 0`: `S = 0`; the injection bound `d · e⁰ ≥ 1` for `d ≥ 1`; not isotropic, hence
  `[Nonempty k]` on isotropy and on the OSI.
- `card n < card k` (without replacement): no injection, `uniformOn ∅ = 0`, the law is `0` and
  `HasLaw` forces `μ = 0`; every tail holds, so no `card k ≤ card n` on a tail (S5 Q8); it is needed
  for the probability instance and for isotropy.
- `card k = card n` (without replacement): `S` is unitary, every event is empty.
- `n` empty: `U` has no rows; with replacement the law is `0` for nonempty `k` (S4 §8 item 8),
  hence `[Nonempty n]` on that model's isotropy and OSI.
- `β`: for nonempty `n`, unitarity forces `1 ≤ β` (a row of `F` has norm `1`); no hypothesis on
  `β`, and `β ≤ 0` only with `n` empty.
- `t = 0`: the flattening bound is `card n ≥ 1`; trivial. `ε ≥ 1`: the injection is vacuous
  (`isSubspaceInjection_of_nonpos`); the embedding keeps S4's `ε ≤ 1`.
- Signs off `{±1}ⁿ`: a null set; `F D ξ` is unitary only almost surely, so the flattening and the
  transfer pass to almost-sure inclusions (`measure_mono_ae`).
- The transfer with `L < 0`: `hflat`'s event is everything (leverage scores are nonnegative), so
  `δ₂ ≥ 1`; `0 ≤ δ₁` follows from `hsample` at `V = 0` when `L ≥ 0`. The skeleton adds `0 ≤ δ₁`
  only if this case split costs more than the hypothesis.
- Rank-deficient `U`: everything is about `range U`, `d = U.rank` (S4 §8 item 9).

### 3.1 `ForMathlib/Probability/Independence/Basic.lean` (1, lower layer)

```lean
/-- **Sections of an event of two independent variables.** If `X` and `Y` are independent, the
section `{ω | (X ω, y) ∈ E}` has probability at most `δ₁` for every `y ∈ G`, and `Y ∉ G` has
probability at most `δ₂`, then `(X, Y) ∈ E` has probability at most `δ₁ + δ₂`. Fubini on the joint
law `μ.map X ⊗ μ.map Y`. Upstream candidate. -/
theorem ProbabilityTheory.IndepFun.measureReal_mem_le_add [IsProbabilityMeasure μ]
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {X : Ω → α} {Y : Ω → β}
    (hXY : IndepFun X Y μ) (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    {E : Set (α × β)} (hE : MeasurableSet E) {G : Set β} (hG : MeasurableSet G) {δ₁ δ₂ : ℝ}
    (hδ₁ : 0 ≤ δ₁) (hsec : ∀ y ∈ G, μ.real {ω | (X ω, y) ∈ E} ≤ δ₁)
    (hGc : μ.real {ω | Y ω ∉ G} ≤ δ₂) :
    μ.real {ω | (X ω, Y ω) ∈ E} ≤ δ₁ + δ₂
```
Proof: `indepFun_iff_map_prod_eq_prod_map_map`, `Measure.prod_apply_symm` (as in the private
helper), `lintegral` split over `G` and `Gᶜ`.

### 3.2 `Sketching/Structured/Flattening.lean` (9)

`(hF : HasOrthonormalCols F) (hFβ : ∀ i j, (Fintype.card n : ℝ) * ‖F i j‖ ^ 2 ≤ β)
(hξ : HasLaw ξ (rademacherVector n) μ)`.
```lean
/-- A unitary times a diagonal of random signs is unitary almost surely. -/
theorem ae_hasOrthonormalCols_mul_diagonal_of_hasLaw_rademacherVector (hF) (hξ) :
    ∀ᵐ ω ∂μ, HasOrthonormalCols (F * Matrix.diagonal fun i => (ξ ω i : 𝕜))
/-- **Flattening**: a randomized unitary transform makes every subspace incoherent. For any `U`,
outside probability `card n · e^{-t}`, every leverage score of `F D U` is at most
`β (d + 2√(dt) + 2t) / n`. [CamanoEpperlyMeyerTropp2025, Imported Theorem 4.3] (there
`O((d + log (n/δ))/n)` for a unitary WHT, DCT or DFT with entries `O(n^{-1/2})`; they note the
argument needs only these two features); Tropp 2011a, Lemma 3.3 (real signs, Walsh;
`(√d + √(8 log (βn)))² / n`; locator through CEMT, paper not in hand). Here any `F` with
`n ‖F i j‖² ≤ β`, any field, any `U`, the Hsu–Kakade–Zhang constant.
Result: srht-flattening (new) -/
theorem measureReal_not_forall_leverageScore_mul_diagonal_le_of_hasLaw_rademacherVector (hF) (hFβ)
    (hξ) (U : Matrix n r 𝕜) (ht : 0 ≤ t) :
    μ.real {ω | ¬ ∀ i, leverageScore (F * (Matrix.diagonal fun l => (ξ ω l : 𝕜)) * U) i ≤
        β * (U.rank + 2 * √(U.rank * t) + 2 * t) * (Fintype.card n : ℝ)⁻¹} ≤
      Fintype.card n * Real.exp (-t)
/-- The **SRHT row bound** `d + 2√(d log (n/δ)) + 2 log (n/δ)`: flattening with failure `δ` makes
every leverage score at most `β` times this over `n`. The value the proof reaches at
`t = log (n/δ)`; Tropp 2011a, Lemma 3.3, has `(√d + √(8 log (n/δ)))²` (unverified), which is larger
(`srhtRowBound_le`). Consumers use the API. Junk: for `δ > n` the logarithm is negative, the root
is `0`, and the value may be below `d`; the flattening tail is then trivial. -/
noncomputable irreducible_def srhtRowBound (n d : ℕ) (δ : ℝ) : ℝ :=
  d + 2 * √(d * Real.log (n / δ)) + 2 * Real.log (n / δ)
theorem srhtRowBound_nonneg {n d : ℕ} (hδ : 0 < δ) (hδn : δ ≤ n) : 0 ≤ srhtRowBound n d δ
theorem srhtRowBound_mono {n n' d d' : ℕ} {δ' : ℝ} (hn : 0 < n) (hnn' : n ≤ n') (hd : d ≤ d')
    (hδ : 0 < δ) (hδδ' : δ ≤ δ') : srhtRowBound n d δ' ≤ srhtRowBound n' d' δ
/-- The explicit comparison consumers invert with; Tropp's form with `2` in place of `8`. -/
theorem srhtRowBound_le (n d : ℕ) (δ : ℝ) :
    srhtRowBound n d δ ≤ (√(d : ℝ) + √(2 * Real.log (n / δ))) ^ 2
/-- Flattening in `δ` form. -/
theorem measureReal_not_forall_leverageScore_mul_diagonal_le_srhtRowBound_of_hasLaw_rademacherVector
    (hF) (hFβ) (hξ) (U : Matrix n r 𝕜) (hδ : 0 < δ) :
    μ.real {ω | ¬ ∀ i, leverageScore (F * (Matrix.diagonal fun l => (ξ ω l : 𝕜)) * U) i ≤
        β * srhtRowBound (Fintype.card n) U.rank δ * (Fintype.card n : ℝ)⁻¹} ≤ δ
/-- **Flatten, then sample** (injection). A sampler `P` that injects every fixed subspace of rank
at most `U.rank` whose leverage scores are at most `L / n`, with failure `δ₁`, composed with an
independent random unitary `T` that makes `T U` so incoherent outside `δ₂`, injects `range U`
outside `δ₁ + δ₂`. [Tropp2011a] (the structure of the SRHT proof; unverified);
[CamanoEpperlyMeyerTropp2025, §4.5] (the same two steps for SparseRTT). -/
theorem hasSubspaceInjection_mul_of_indepFun_of_leverageScore_le [IsProbabilityMeasure μ]
    {P : Ω → Matrix k n 𝕜} {T : Ω → Matrix n n 𝕜} (hind : IndepFun P T μ)
    (hP : AEMeasurable P μ) (hT : AEMeasurable T μ) (hTU : ∀ᵐ ω ∂μ, HasOrthonormalCols (T ω))
    {U : Matrix n r 𝕜}
    (hsample : ∀ V : Matrix n r 𝕜, V.rank ≤ U.rank →
      (∀ i, leverageScore V i ≤ L * (Fintype.card n : ℝ)⁻¹) → HasSubspaceInjection P V a δ₁ μ)
    (hflat : μ.real {ω | ¬ ∀ i, leverageScore (T ω * U) i ≤ L * (Fintype.card n : ℝ)⁻¹} ≤ δ₂) :
    HasSubspaceInjection (fun ω => P ω * T ω) U a (δ₁ + δ₂) μ
/-- **Flatten, then sample** (embedding); the same with `HasSubspaceEmbedding … a b`. -/
theorem hasSubspaceEmbedding_mul_of_indepFun_of_leverageScore_le [IsProbabilityMeasure μ] … :
    HasSubspaceEmbedding (fun ω => P ω * T ω) U a b (δ₁ + δ₂) μ
```
Proofs.
- *Unitary*: `(F D)ᴴ (F D) = D Fᴴ F D = D² = 1` on `{∀ i, ξ i ^ 2 = 1}`
  (`ae_sq_eq_one_of_hasLaw_rademacherVector`).
- *Flattening*: `d = 0` directly. Otherwise `exists_hasOrthonormalCols_range_eq` gives
  `Q : Matrix n (Fin d) 𝕜` with the range of `U`. Then `range (F D U) = range (F D Q)` for every
  `ξ`, so the leverage scores agree (`leverageScore_eq_of_range_eq`), and almost surely `F D Q` is
  orthonormal, so score `i` is `‖(F D Q) i‖²` (`HasOrthonormalCols.leverageScore_eq`). Row `i` is
  `n^{-1/2} M_i (ξ : n → 𝕜)` with `M_i := Qᵀ * diagonal (fun l => √n * F i l)`, where
  `‖M_i‖ ≤ √β` (`specNorm_transpose`, `specNorm_diagonal_le`) and `‖M_i‖_F² ≤ β d`
  (`frobNorm_sq_eq_sum`, `‖Q‖_F² = d`). Realify: `M_i' := Matrix.fromRows (M_i.map re) (M_i.map im)`,
  a real matrix with `‖M_i' x‖ = ‖M_i x‖` for real `x`, `‖M_i'‖_F = ‖M_i‖_F`, `‖M_i'‖ ≤ ‖M_i‖`
  (three private helpers; the prototype's `norm_toLp_ofReal_eq` and
  `specNorm_le_specNorm_map_ofReal` are the material). The signs have proxy `1`
  (`isSubgaussianVector_of_hasLaw_rademacherVector`). The new HKZ form (§1 item 1) at `A = M_i'`,
  with `‖M_i'ᴴ M_i'‖_F ≤ ‖M_i'‖ ‖M_i'‖_F ≤ β √d` (`frobNorm_mul_le_specNorm_mul_frobNorm`), bounds
  `{L_d(t) ≤ ‖M_i' ξ‖²}` by `e^{-t}` (`M_i' = 0` makes the row event empty). Finally the union
  over `i` (`measureReal_iUnion_fintype_le`); the strict failure `L/n < score` sits inside the
  non-strict HKZ event.
- *`δ` form*: `t = log (n/δ)` for `δ ≤ n`, `n e^{-t} = δ`, and `srhtRowBound_def`; for `δ > n ≥ 1`
  the bound exceeds `1`.
- *Row bound API*: `t ↦ d + 2√(d t) + 2t` is monotone for every real `t` (Lean's `√` of a negative is
  `0`), and `√(d t) ≤ √(2 d t)`.
- *Transfer*: `E := {(A, B) | ¬ IsSubspaceInjection A (B * U) a}` is open
  (`isClosed_setOf_isSubspaceInjection` composed with `(A, B) ↦ (A, B * U)`), and
  `G := {B | HasOrthonormalCols B ∧ ∀ i, leverageScore (B * U) i ≤ L / n}` is measurable
  (`measurable_rangeProjector`; the orthonormal set is closed). For `B ∈ G` the section is
  `hsample (B * U)` (`Matrix.rank_mul_le_right`). `{T ∉ G}` is a null set plus `hflat`'s event.
  On `{T ω ∈ G}` the event `¬ IsSubspaceInjection (P T) U a` equals `¬ IsSubspaceInjection P (T U) a`,
  since `(T U)ᴴ (T U) = Uᴴ U`. §3.1 concludes. The embedding is identical with
  `isClosed_setOf_isSubspaceEmbedding`.

### 3.3 `Sketching/Structured/SRHT.lean` (23)

`(hF) (hFβ)` as in §3.2; `hS : HasLaw S (srht k F) μ` or `HasLaw S (srhtWithReplacement k F) μ`.
```lean
/-- The **SRHT built from given signs and indices**: `√(n/k) Pᴴ F D`, with `P` the selection by
`ι` and `D = diagonal ξ`; row `j` is `√(card n / card k)` times row `ι j` of `F D`. Its laws are
`NLAlib.srht` (a uniform injection) and `NLAlib.srhtWithReplacement` (i.i.d. uniform indices).
[MartinssonTropp2020, §9.3] (there `√(n/d) R F E Π`, no `Π` here);
[HalkoMartinssonTropp2011, §4.6] (the SRFT, there with complex unimodular `D`);
[Woodruff2014, Theorem 7]. -/
noncomputable def srhtMatrix (F : Matrix n n 𝕜) (ξ : n → ℝ) (ι : k → n) : Matrix k n 𝕜 :=
  samplingSketchMatrix (fun _ : n => (Fintype.card n : ℝ≥0)⁻¹) ι * F *
    Matrix.diagonal fun i => (ξ i : 𝕜)
variable (k) in
/-- The **SRHT law**: the pushforward by `srhtMatrix F` of independent signs and a uniform
injection `k → n` (sampling without replacement). `⊤` on `n` inside the definition (S4 §8 item 1);
`srht_eq_map_prod` writes it through S5's law. The zero measure when `card n < card k`. -/
noncomputable def srht (F : Matrix n n 𝕜) : Measure (Matrix k n 𝕜) :=
  letI : MeasurableSpace n := ⊤
  ((rademacherVector n).prod (uniformOn {ι : k → n | Function.Injective ι})).map
    fun x => srhtMatrix F x.1 x.2
variable (k) in
/-- The SRHT law with i.i.d. uniform indices (sampling with replacement). -/
noncomputable def srhtWithReplacement (F : Matrix n n 𝕜) : Measure (Matrix k n 𝕜) :=
  letI : MeasurableSpace n := ⊤
  ((rademacherVector n).prod
      (Measure.pi fun _ : k => samplingMeasure fun _ : n => (Fintype.card n : ℝ≥0)⁻¹)).map
    fun x => srhtMatrix F x.1 x.2
instance isFiniteMeasure_srht (F) : IsFiniteMeasure (srht k F)
instance isFiniteMeasure_srhtWithReplacement (F) : IsFiniteMeasure (srhtWithReplacement k F)
theorem isProbabilityMeasure_srht (F) (hk : Fintype.card k ≤ Fintype.card n) :
    IsProbabilityMeasure (srht k F)
theorem isProbabilityMeasure_srhtWithReplacement [Nonempty n] (F) :
    IsProbabilityMeasure (srhtWithReplacement k F)
/-- The SRHT law as signs times S5's sampling law; the form the proofs use. -/
theorem srht_eq_map_prod (F) : srht k F =
    ((rademacherVector n).prod (samplingSketchWithoutReplacement k n)).map
      fun x => x.2 * F * Matrix.diagonal fun i => (x.1 i : 𝕜)
theorem srhtWithReplacement_eq_map_prod (F) : srhtWithReplacement k F =
    ((rademacherVector n).prod (samplingSketch k fun _ : n => (Fintype.card n : ℝ≥0)⁻¹)).map
      fun x => x.2 * F * Matrix.diagonal fun i => (x.1 i : 𝕜)
/-- D4's bridge from the user's own signs and injection. -/
theorem hasLaw_srhtMatrix_of_hasLaw_uniformOn_injective [MeasurableSpace n]
    [MeasurableSingletonClass n] {ι : Ω → k → n} (hξ : HasLaw ξ (rademacherVector n) μ)
    (hι : HasLaw ι (uniformOn {f : k → n | Function.Injective f}) μ) (hind : IndepFun ξ ι μ) :
    HasLaw (fun ω => srhtMatrix F (ξ ω) (ι ω)) (srht k F) μ
theorem hasLaw_srhtMatrix_of_hasLaw_pi [MeasurableSpace n] [MeasurableSingletonClass n]
    {ι : Ω → k → n} (hξ)
    (hι : HasLaw ι (Measure.pi fun _ : k => samplingMeasure fun _ : n => (Fintype.card n : ℝ≥0)⁻¹) μ)
    (hind : IndepFun ξ ι μ) : HasLaw (fun ω => srhtMatrix F (ξ ω) (ι ω)) (srhtWithReplacement k F) μ
/-- The SRHT is isotropic. [CamanoEpperlyMeyerTropp2025, §1.5.2]. -/
theorem isIsotropicSketch_of_hasLaw_srht [Nonempty k] (hF) (hS : HasLaw S (srht k F) μ)
    (hk : Fintype.card k ≤ Fintype.card n) : IsIsotropicSketch S μ
theorem isIsotropicSketch_of_hasLaw_srhtWithReplacement [Nonempty k] [Nonempty n] (hF)
    (hS : HasLaw S (srhtWithReplacement k F) μ) : IsIsotropicSketch S μ
/-- **The SRHT is a scaled partial isometry**: `S Sᴴ = (n/k) • 1` almost surely.
[HalkoMartinssonTropp2011, §11.1]; [MartinssonTropp2020, §9.3]. -/
theorem ae_mul_conjTranspose_eq_of_hasLaw_srht [DecidableEq k] (hF) (hS : HasLaw S (srht k F) μ) :
    ∀ᵐ ω ∂μ, S ω * (S ω)ᴴ = ((Fintype.card n : ℝ) / Fintype.card k) • (1 : Matrix k k 𝕜)
theorem ae_specNorm_eq_of_hasLaw_srht (hF) (hS : HasLaw S (srht k F) μ) :
    ∀ᵐ ω ∂μ, specNorm (S ω) = √(Fintype.card n / Fintype.card k : ℝ)
/-- **The SRHT OSI**: for every `ε ≥ 0`, `t ≥ 0`, failure `d e^{-ε² k/(2 L_d(t))} + n e^{-t}`;
the lower Chernoff half after flattening. [CamanoEpperlyMeyerTropp2025, §1.5.2] (the OSI view;
`k = Ω(d log d)` is necessary, their citation of Tropp 2011a, §3.3); Tropp 2011a, main theorem
(unverified). Result: srht-osi (new) -/
theorem isObliviousSubspaceInjection_of_hasLaw_srht [Nonempty k] (hF) (hFβ)
    (hS : HasLaw S (srht k F) μ) (hk : Fintype.card k ≤ Fintype.card n) (d : ℕ) (hε : 0 ≤ ε)
    (ht : 0 ≤ t) :
    IsObliviousSubspaceInjection S d (1 - ε)
      (d * Real.exp (-ε ^ 2 * Fintype.card k / (2 * (β * (d + 2 * √(d * t) + 2 * t)))) +
        Fintype.card n * Real.exp (-t)) μ
/-- **The SRHT OSE**, `0 ≤ ε ≤ 1`, failure `2 d e^{-ε² k/(3 L_d(t))} + n e^{-t}`.
[Woodruff2014, Theorem 7] (there `r = Ω(ε^{-2} log d (√d + √log n)²)` rows, probability `0.99`,
real Walsh, `n` a power of two); [MartinssonTropp2020, §9.3] (`d = O(k log k)`, any SRTT);
[HalkoMartinssonTropp2011, Theorem 11.1] (the SRFT with Steinhaus signs, `0.40 ≤ σ_min`,
`σ_max ≤ 1.48`, failure `O(1/k)`); Tropp 2011a (unverified). Here any `𝕜`, any `F` with entry
bound `β`, the tail in natural parameters. Result: srht-ose -/
theorem isObliviousSubspaceEmbedding_of_hasLaw_srht (hF) (hFβ) (hS : HasLaw S (srht k F) μ)
    (d : ℕ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (ht : 0 ≤ t) :
    IsObliviousSubspaceEmbedding S d (1 - ε) (1 + ε)
      (2 * d * Real.exp (-ε ^ 2 * Fintype.card k / (3 * (β * (d + 2 * √(d * t) + 2 * t)))) +
        Fintype.card n * Real.exp (-t)) μ
-- the same two for `srhtWithReplacement`, same bounds (S5 Q6), the OSI with
-- `[Nonempty k] [Nonempty n]` and no `hk`; Result: srht-osi, srht-ose
theorem isObliviousSubspaceInjection_of_hasLaw_srhtWithReplacement …
theorem isObliviousSubspaceEmbedding_of_hasLaw_srhtWithReplacement …
-- sizes: S4's quantities at `L = β * srhtRowBound (card n) d (δ / 2)`, failure split `δ/2 + δ/2`
theorem isObliviousSubspaceEmbedding_of_hasLaw_srht_of_samplingSize_le (hF) (hFβ) (hS) (d : ℕ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hk : samplingSize d (β * srhtRowBound (Fintype.card n) d (δ / 2)) ε (δ / 2) ≤ Fintype.card k) :
    IsObliviousSubspaceEmbedding S d (1 - ε) (1 + ε) δ μ
theorem isObliviousSubspaceInjection_of_hasLaw_srht_of_samplingInjectionSize_le [Nonempty k] (hF)
    (hFβ) (hS) (hkn : Fintype.card k ≤ Fintype.card n) (d : ℕ) (hε : 0 < ε) (hδ : 0 < δ)
    (hk : samplingInjectionSize d (β * srhtRowBound (Fintype.card n) d (δ / 2)) ε (δ / 2) ≤
      Fintype.card k) :
    IsObliviousSubspaceInjection S d (1 - ε) δ μ
-- and the two for `srhtWithReplacement` (4 size corollaries in all)
```
Proofs.
- *Law*: `srhtMatrix F` is measurable on `(n → ℝ) × (k → n)` with `⊤` on `n`
  (`measurable_from_prod_countable_left`; continuous in the signs). `srht_eq_map_prod`: the map of a
  product is the product of maps on the second factor (`Measure.map_prod_map`), and S5's law is the
  map of the uniform injection by `samplingSketchMatrix` (S5's definition, the same `⊤`); likewise
  with S4's law. Bridges: `IndepFun.hasLaw_prod`, then `HasLaw.comp`, under the user's instances
  (S4's `samplingSketch_eq_map`, S5's `…_eq_map`).
- *Isotropy*: on the product space, `S = P * T` with `P := x.2` (isotropic by S5's, resp. S4's,
  theorem) and `T := F D x.1` (isotropic: `Tᴴ T = 1` a.s. and bounded entries; a private lemma),
  independent (`indepFun_iff_hasLaw_prodMk_prod` with the coordinate laws); `IsIsotropicSketch.mul`;
  transport by `HasLaw.isIsotropicSketch_iff` and `srht_eq_map_prod`.
- *Partial isometry*: with `P = √(n/k) Pᴴ` for injective `ι`, `S Sᴴ = P (F D)(F D)ᴴ Pᴴ = P Pᴴ`,
  and §1 item 4 at uniform weights gives `(n/k) • 1`; the injection and the signs are almost surely
  injective and `±1`. `specNorm` from `specNorm S ^ 2 = specNorm (S Sᴴ)`; empty `k` gives `0 = √0`.
- *Oblivious*: `card n < card k` gives `μ = 0` (§3 degenerate cases). Otherwise `μ` is a probability
  measure; transport to the product space; for each `U` with `U.rank ≤ d`, apply §3.2's transfer
  with `P = x.2`, `T = F D x.1`, `L = L_d(t)`. `hsample` is S5's (resp. S4's at uniform weights,
  with `hp` from `card n ≠ 0`) fixed-`V` tail, monotone from `V.rank` to `d`; `hflat` is
  §3.2's flattening at `U.rank ≤ d`, whose threshold is monotone in the rank. The OSI adds isotropy.
- *Sizes*: the same transfer with `hflat` from the `δ` form at `δ/2` (and `srhtRowBound_mono` from
  `U.rank` to `d`), and `hsample` from S4's `samplingSize_le`, `samplingInjectionSize_le` inversions
  at `δ/2` (the size corollaries of S4 and S5 verbatim). No unfolding of `srhtRowBound` outside
  `Flattening.lean`.

### 3.4 Instances

No family-level Walsh or Fourier theorem. The instances are the hypothesis discharges of §1 item 3:
- Walsh, any `𝕜`: `hasOrthonormalCols_smul_walshHadamard b` and
  `fun x y => (card_mul_norm_smul_walshHadamard_apply_sq x y).le` at `β = 1`, index
  `Fin b → ZMod 2`.
- Fourier, `𝕜 = ℂ`: `hasOrthonormalCols_fourierMatrix n` and
  `fun j k => (card_mul_norm_fourierMatrix_apply_sq j k).le`.
- Any Mathlib Hadamard matrix (Sylvester products, Paley): `Matrix.IsHadamard.…` at
  `(√card n)⁻¹ • H`.

`SRHT.lean`'s module docstring shows the Walsh OSE in three lines (§7 Q8).

## 4. Files

S6 proper: 32 statements in two files, about 1050 lines against the brief's 750 (the transfer pair,
the isotropy and norm facts and the four size corollaries are the overrun).
1. `Sketching/Structured/Flattening.lean` (9: 1 definition, 8 theorems); imports
   `Probability/Distributions/Rademacher`, `Probability/SubGaussianVector/Norm`,
   `Probability/Measurability/Matrix`, `ForMathlib/Probability/Independence/Basic`,
   `Sketching/Sampling/Leverage`, `Sketching/Properties/FixedSubspace`. About 400 lines.
2. `Sketching/Structured/SRHT.lean` (23: 3 definitions, 2 instances, 18 theorems); imports 1,
   `Sketching/Sampling/{RowSampling,WithoutReplacement}`, `Sketching/Properties/{Isotropic,Oblivious}`;
   not the Walsh and Fourier files (the instances are a docstring example, §3.4). About 650 lines.

Lower-layer additions, 7 statements (§1): `Probability/SubGaussianVector/Norm.lean` (+1, about 250
lines; the file reaches about 510); new `ForMathlib/Probability/Independence/Basic.lean` (1, about
80 lines; `Properties/Oblivious.lean`'s private helper reproved from it); `Matrix/Structured/Walsh.lean`
(+3), `Matrix/Structured/Circulant.lean` (+1); `Sketching/Sampling/RowSampling.lean` (+1).

Order: the Probability theorem and the ForMathlib lemma first (independent of each other, one
agent each or one agent for both); the Matrix and RowSampling lemmas with them (small, independent);
then 1, then 2. 2 also waits for S5's `WithoutReplacement.lean`. Bibliography: `Tropp2011a` (D16;
added by S5 if it lands first), locators unverified (§7 Q9); Hsu, Kakade and Zhang cited by name as
`Norm.lean` already does, or a new key `HsuKakadeZhang2012` with the locator flagged.

## 5. Material

Read: the prototype's `Sketching/Structured/{SRHTCore,SRHTFlattening,SRHTParameters,SRHT,
SRHTWithReplacement}.lean` (1001 lines, 48 declarations: `ℝ` only, `Fin n`, `ExactRowSubset`,
complex Chernoff through `map ofReal`, `open scoped Classical`, `maxHeartbeats 600000`), and the
files they lean on: `ForMathlib/Probability/FiniteProductEvents.lean` (the sections lemmas),
`Matrix/Structured/WalshFin.lean`, `Probability/ChiSquare/DirectionalSquaredNorm.lean`,
`Matrix/Norms/Core.lean`'s `ofReal` transport; the atlas (`srht-ose` on the two `…_sample_size`
theorems); HMT §4.6, §11 (Theorems 11.1, 11.2, Remarks 11.1, 11.2); MT §9.3, §9.6, Theorem 11.6;
Woodruff §2.1 Theorem 7; CEMT §1.5.2, Definition 1.10, Theorem 1.11, §4.5 and Imported Theorem 4.3;
Tropp and Webber §3.3 (cites Tropp 2011a among SRTT references only). Ledger (prototype to here):
- `SRHTCore.lean` (11): `srhtSketch` to `srhtMatrix` (injection `k → n` in place of an ordered
  subset; `𝕜`; any `F`); `measurable_srhtSketch` to the law's body (not public);
  `srhtSketch_mul_apply`, `sum_srhtRowEnumeration`, `transpose_srhtSketch_mul_self` to S4's
  `conjTranspose_samplingSketchMatrix_mul_mul` (exists; no SRHT twin); `srhtPopulationAtom` and its
  `_posSemidef`, `trace_`, `mean_` lemmas to S5's population atoms inside its proof (not ported);
  `map_ofReal_srhtSketch_gram` not ported (an `ℝ`-to-`ℂ` transport; everything is over `𝕜`);
  `transpose_srhtSketch_full_rows_mul_self` not ported (`card k = card n` is a degenerate case of
  the main theorems; no consumer for the identity).
- `SRHTFlattening.lean` (9): `srhtSignedFrame`, `srhtNormalizedRow` and the measurability lemma not
  ported (inline `F * D * U`, private `M_i`); `hasOrthonormalCols_srhtSignedFrame` to
  `ae_hasOrthonormalCols_mul_diagonal_of_hasLaw_rademacherVector`;
  `hasSubgaussianMGF_srhtNormalizedRow_dotProduct` to `IsSubgaussianVector.mulVec` (exists) on the
  realified row; `measure_srht_row_sq_ge_add_two_sqrt_mul_add_le` to the per-row step through §1
  item 1; `srhtSharpRowBound` to `srhtRowBound` (now at failure `δ`, not `δ/2`, and smaller);
  `srht_chi_square_threshold_le` to `srhtRowBound_le`; `measure_srhtSharpRowBound_failure_le` to
  the `δ` form of flattening (any `U`, leverage scores, `𝕜`, entry bound `β`).
- `SRHTParameters.lean` (3): `srhtManuscriptRowBound`, `srhtSharpRowBound_le_manuscript`,
  `srhtManuscriptRowBound_le_additive` not ported (the Hanson–Wright bound with `256 e²` is dominated,
  D11, §5.2 rule 6; its manuscript is dropped as a source, D16).
- `SRHT.lean` (14): `srhtLaw` and its instance to `srht` and `isProbabilityMeasure_srht`;
  `measure_srht_gram_failure_le_of_flat_rows` to the transfer theorem with S5's tail;
  `srht_tail_le_half_of_sample_size` to S4's `samplingSize_le` inside the size corollary;
  `measure_srht_gram_failure_le_of_sharp_sample_size` to
  `isObliviousSubspaceEmbedding_of_hasLaw_srht_of_samplingSize_le` (and the `(ε, t)` primary);
  `_of_manuscript_sample_size` not ported (dominated); `srhtCappedRowCount`, `_le`,
  `measure_srht_capped_gram_failure_le`, `…_with_capped_width` (two) not ported (rounded widths, D5;
  the full-row branch is the `k = n` degenerate case); `measure_srht_full_rows_failure_eq_zero`,
  `measure_srht_zero_rank_failure_eq_zero` not ported (degenerate cases of the main theorems);
  `measure_walsh_srht_gram_failure_le` to the Walsh instance lemma (§3.4).
- `SRHTWithReplacement.lean` (11): the sketch, its measurability, law and instance to `srhtMatrix`
  and `srhtWithReplacement`; `_mul_apply`, `map_ofReal_…_gram` to S4's Gram identity, not ported;
  `_of_flat_rows` to the transfer with S4's tail; `_sharp_sample_size` to the size corollary;
  `_manuscript_` not ported; the Walsh theorem to §3.4; `zero_rank` a degenerate case.
- Outside the five, ledgered by their owners and recorded here: `FiniteProductEvents` (4) to §3.1
  (one lemma, independence form; the `Finite` twins not ported); `WalshFin` (4) not ported (`Fin`
  reindexing; `walshHadamard` is indexed by bit strings, D5); `specNorm_le_specNorm_map_ofReal`,
  `norm_toLp_ofReal_eq` to the private realification helpers;
  `measureReal_sq_norm_ge_add_two_sqrt_mul_add_le` is `IsSubgaussianVector.measure_norm_sq_ge_le`
  (exists).
Result ids: `srht-ose` (atlas), `srht-osi`, `srht-flattening` (new); `hsu-kakade-zhang` (existing)
on §1 item 1.

## 6. Cut, and why

- `Fin` sizes, `ExactRowSubset`, `ℝ`-only statements and the `map ofReal` transport (D5, D10, D11).
- The second row bound and the capped-width and Walsh variants (D11; dominated, §5.2 rule 6).
- Fixed-`U` SRHT theorems: the oblivious ones applied at `d = U.rank`
  (`IsObliviousSubspaceEmbedding.hasSubspaceEmbedding`) give them for any shape in one line.
- Upper-half-only theorems (`HasSubspaceEmbedding … 0 (1 + ε)`): no consumer; joining two halves
  would also pay the flattening failure twice.
- A sampler-parametrized law (`srht` over any law `ν` of the sampler): the transfer theorem already
  serves a new sampler at the level of random variables (§7 Q3).
- Complex Steinhaus signs (HMT's SRFT exactly): the complex sign law is later work (brief §0;
  `Probability-REPORT.md` §4 item 11). CEMT split complex signs into real and imaginary parts; when
  the law exists, the flattening proof applies to the realified `2n` signs with the same `β`.
- A random permutation `Π` (MT §9.3) and rerandomization (MT Remark 9.2): no analysis needs them; the
  transfer covers `T = F D' F D` when a consumer wants it.
- JL, the JL moment and AMM for the SRHT (D3 lists OSE and OSI); the lower-bound example
  (HMT Remark 11.2, Tropp 2011a §3.3) is cited in the docstrings, not formalized.
- The mixture-of-Diracs form of the SRHT law: the sign law is not a finite sum over `n → ℝ` without
  an encoding of the cube (`n → ℤˣ`), and no proof or consumer uses it; `srht_eq_map_prod` is the
  explicit form (S4 §8 item 1's pattern, adapted).
- The source forms of the Chernoff exponents (S4 Q4) and Tropp's sharper `(1 + ι) d log d` regime
  (HMT Remark 11.1, Tropp 2011a Theorem 3.2 as HMT cite it): a new theorem named by its parameter
  if a consumer asks (§5.2 rule 4).

## 7. Questions and decisions

**Hard to reverse:** Q1 and Q2 (they fix the hypotheses and the constant of every SRHT statement).
Q2 generalizes D11's hypothesis and touches Mathlib's `IsHadamard`, so it goes to the maintainer
or the orchestrator's Fable review before the skeleton. **Decisions taken** (open to correction):
the rest.

**Q1 (hard to reverse; missing infrastructure). The flattening constant over `𝕜`.** Row `i` of
`F D Q` is `n^{-1/2} M_i ξ` with `M_i` complex and `ξ` real. Over `ℝ` the existing API suffices:
`IsSubgaussianVector.mulVec` and the `A = 1` tail in dimension `d` give `β(d + 2√(dt) + 2t)`. Over
`ℂ` it does not: the library's tail is for real vectors, and `‖M_i ξ‖² = ‖Re M_i ξ‖² + ‖Im M_i ξ‖²`.
Options:
- (i) D11's literal route, `sum_const_mul_of_iIndepFun` on real and imaginary parts and a union of two
  tails: `2 β (d + 2√(dt) + 2t)` with failure `2 n e^{-t}`, the same statement over `ℝ`. It doubles
  the sample size for the real Walsh SRHT, the main use.
- (ii) Realify the vector through an orthonormal `ℝ`-basis of `𝕜`, in real dimension
  `Module.finrank ℝ 𝕜 * d`: exact over `ℝ`, `2d` over `ℂ`. It puts `Module.finrank ℝ 𝕜` into
  `srhtRowBound`'s argument and still loses a factor near 2 over `ℂ`.
- (iii) Hsu, Kakade and Zhang's Theorem 2.1 for a general matrix `A` (§1 item 1), applied to the real
  matrix `M_i' = [Re M_i; Im M_i]`: `‖M_i'‖_F² = ‖M_i‖_F² ≤ βd` over both fields, so the bound is
  `β(d + 2√(dt) + 2t)` over `ℝ` and `ℂ` alike, with no field in the statement.

*Recommendation (iii).* It is the source's own general theorem, it dominates the `A = 1` case already
in the library (which is reproved from it), it costs about 250 lines in one Probability file with no
new dependency (the linearization is the existing one, with weights), and it gives one statement over
`𝕜` with the real constant, which is what D11 asks ("the constant valid over both fields"). D11's
mention of `sum_const_mul_of_iIndepFun` describes a proof route; the statement D11 fixes is kept.
*Fallback* if the weighted Laurent–Massart step stalls: (ii), not (i). *Reversal*: the `(ε, t)`
statements of §3.2 and §3.3 change their constant; the size corollaries and their consumers do not
(they see only `srhtRowBound`'s API). Decide before the skeleton.

**Q2 (hard to reverse). The hypothesis on the transform.** D11 has `HasOrthonormalCols H` and
`‖H i j‖ ^ 2 = 1 / card n`. Options:
- (a) D11 literally.
- (b) Mathlib's `Matrix.IsHadamard H` on the unnormalized matrix, with `(√n)⁻¹` inside the
  constructor. Mathlib first, no deviation; Walsh is immediate (`isHadamard_walshHadamard`), Fourier
  needs one lemma. It excludes the discrete Hartley and cosine transforms, which are not Hadamard
  (entries up to `√(2/n)`), though MT §9.3 lists them and reports, after Avron et al., that the
  Hartley transform is the best real choice (Blendenpik, a named S6 consumer).
- (c) `HasOrthonormalCols F` and `∀ i j, card n * ‖F i j‖ ^ 2 ≤ β`, the bounded orthonormal system of
  CEMT's remark after their Imported Theorem 4.3 ("the proof only depends on these two features").
  `β` enters the bound linearly (`L = β · srhtRowBound`), at no proof cost.
- (d) (c) as a named predicate.

*Recommendation (c)*, with the shape fixed here as D8 fixed the domination shape. Equality is
replaced by `≤` because the proof needs only the bound and DHT and DCT satisfy only the bound
(`β = 2`). Writing the hypothesis as `card n * ‖F i j‖ ^ 2 ≤ β` lets the instances discharge it with
`(… ).le` at `β = 1`. Not (b), because of DHT and DCT; Mathlib's `IsHadamard` enters through the
two bridge lemmas of §1 item 3, and a deviation entry records the choice: generality, not convenience.
Not (d) yet: the pair appears only in S6's statements, and CONTRIBUTING §5.4 asks for a design note
before a new interface. If the review applies "a raw condition written twice is an interface"
strictly, (d) is a structure `IsBoundedOrthonormal F β` with the two fields, a constructor from
`IsHadamard`, and the same instances. *Reversal*: every SRHT statement's hypotheses and its
consumers'.

**Q3. The laws and their names.** Two laws, `srht k F` (uniform injection, the classical SRHT of
Tropp 2011a and HMT §11) and `srhtWithReplacement k F`, with one constructor `srhtMatrix F ξ ι`
(D4). Each is defined as S4 §8 item 1 asks: the pushforward of the primitive signs and indices, with
`⊤` on `n` inside the body, and the explicit form a lemma (`srht_eq_map_prod`, through S5's or S4's
matrix law; the proofs use it). The order `srht k F`, sketch index first, amends D14's `srht H k`.
Every sketch law takes `k` first (`samplingSketch k p`, `samplingSketchWithoutReplacement k n`,
`countSketch k n`, `gaussianMatrix k n`); `haarFrame n k` is a frame, not a sketch. The name `srht`
is kept for every `F` (MT's "SRTT" is the general term): D14 fixed it and users search for SRHT.
*Alternative*: one law over a sampler law `ν : Measure (Matrix k n 𝕜)`, `((rademacherVector n).prod
ν).map …`, which needs no `⊤` and would serve CEMT's SparseCol later. It is rejected for now: D4
wants a pushforward of primitives, the two named laws are what users hold, and the transfer
theorem already serves a new sampler. Cheap now, moderate after LowRank uses the names.

**Q4. The transfer theorems are public and generic in the random unitary `T`.** They are the reusable
half of the SRHT proof (CEMT §4.5 runs the same two steps for SparseRTT; MT Remark 9.2's
rerandomized transform and a Haar-rotated sampler are other instances). `hsample` is a raw
quantified hypothesis ("`P` injects every subspace of rank at most `d` with leverage scores at most
`L / n`, failure `δ₁`"): CEMT's Theorem 4.4 proves exactly this for SparseCol. A predicate
(`IsIncoherentSubspaceInjection P d L a δ μ`, say) is added when the sparse round brings that second
consumer. Not hard to reverse (the predicate would be a definitional repackaging).

**Q5. The sections lemma is general and goes to `ForMathlib`.** D11 asks for "one sections lemma".
Its statement has no NLAlib vocabulary (independence, a measurable event, an exceptional set), so it
goes in `ForMathlib/Probability/Independence/Basic.lean` as an upstream candidate, in the
`ProbabilityTheory.IndepFun` namespace for dot notation. `Properties/Oblivious.lean`'s private
Fubini helper is its case `δ₂ = 0` and is reproved from it in the same PR. *Alternative*: a public
lemma in `Oblivious.lean`; rejected, the subject is not sketching. The prototype's product-measure
form (`measureReal_prod_le_measureReal_add_of_sections_le`) is less convenient here: the SRHT
theorems hold `HasLaw S`, not a product measure. Not hard to reverse.

**Q6. Constants, parameters and sizes.**
- The primary family tails are in the natural parameters `(ε, t)` (D5), with every constant explicit:
  S4's Chernoff exponents (`2L` lower, `3L` two-sided), the HKZ threshold and the union over `n` rows.
- The constant is better than the source's: Tropp's `(√d + √(8 log (n/δ)))²` against our
  `d + 2√(d log (n/δ)) + 2 log (n/δ) ≤ (√d + √(2 log (n/δ)))²`. By §5.2 rule 2 the statement writes
  the proof's constant, and the docstring gives the source's.
- `srhtRowBound` is the only new named quantity, an `irreducible_def` with positivity, monotonicity
  and the explicit comparison `srhtRowBound_le` (§5.2 rule 2; D5).
- The sizes reuse S4's `samplingSize` and `samplingInjectionSize` at `L = β · srhtRowBound n d (δ/2)`,
  with the failure split `δ/2 + δ/2`; this is the prototype's split, with flattening at `δ/2`. So the
  user inverts one size for the four families S4, S5 and S6 (two models). No `srhtSize` definition:
  it would be a composite of two named quantities.
- Not hard to reverse: sizes are corollaries.

**Q7. Isotropy and the partial isometry are stated.** Isotropy is needed for the OSI (D2). The
identity `S Sᴴ = (n/k) • 1` and `specNorm S = √(n/k)` (without replacement only; with replacement,
repeated rows break it) are stated because HMT Theorem 11.2 and MT Theorem 11.6 use
`‖Ω₂‖ ≤ ‖Ω‖ = √(n/ℓ)`, and the Haar sketch has the same pair
(`ae_specNorm_eq_of_hasLaw_haarFrame`). The deterministic identity for injective `ι` (§1 item 4) is
about S4's constructor at any weights. It goes to `RowSampling.lean`, recorded as a dated amendment
to S4's note, rather than to S5's file (S5 §6 deferred it to S6) or to `SRHT.lean` (wrong owner).
Not hard to reverse.

**Q8. No Walsh or Fourier family twins.** The brief's "Walsh and Fourier instances" are the
hypothesis lemmas of §1 item 3 (in the Matrix files that own the matrices) plus a docstring example.
Family-level instance theorems would be eight one-line restatements (two transforms, two models, two
predicates) whose only content is `(h x y).le`. *Alternative*: one Walsh OSE corollary as a showcase;
rejected as a twin (CONTRIBUTING §1.4). Not hard to reverse (additive).

**Q9. Literature.**
- In hand and confirmed:
  - HMT §4.6 and §11: Theorem 11.1, Remarks 11.1 and 11.2, Theorem 11.2, `‖Ω‖ = √(n/ℓ)`. Their
    SRFT has complex unimodular `D`, not signs.
  - MT §9.3: the SRTT `√(n/d) R F E Π` with any unitary trigonometric transform; `d = O(k log k)`
    after "Tropp (2011b)"; DHT best in the real case after Avron et al.
  - MT §9.6, which cites "Tropp (2011b, Lemma 3.4)" for uniform sampling.
  - MT Theorem 11.6.
  - Woodruff Theorem 7.
  - CEMT §1.5.2, Definition 1.10 (Rademacher `D`, WHT, DCT or DFT), Imported Theorem 4.3 (the
    flattening, "adapted from [111, Lem. 3.3]", with the remark on what the proof uses), and
    [111, Sec. 3.3] (the `d log d` lower bound).
- Not in hand: Tropp 2011a (`Tropp2011a`, D16), cited by name with every locator flagged:
  - Lemma 3.3, the flattening (secondhand through CEMT);
  - Lemma 3.4, the sampling step (secondhand through MT);
  - §3.3, the lower bound (secondhand through CEMT);
  - Theorem 3.2, as HMT Remark 11.1 cites it;
  - the main theorem's number is unknown, so it is cited without one.
  - MT calls the paper Tropp 2011b and HMT number it [134]; the key stays `Tropp2011a`.
- Also not in hand: Hsu, Kakade and Zhang 2012, Theorem 2.1, cited by name as `Norm.lean` does;
  Ailon and Chazelle (the randomized Hadamard step), by name.
- Tropp and Webber cite Tropp 2011a only in a list of SRTT references.

**Q10. Real signs over `𝕜`.** The signs are `rademacherVector n` (real), coerced into `D` (D11, CEMT
Definition 1.10, MT's "sign flip"). The flattening proof needs real signs: it realifies `M_i`, not
`ξ`. HMT's complex unimodular signs need the complex sign law, which is later work (§6).

**Q11. Size.** About 1050 lines in S6's two files against the brief's 750, plus about 400 lines of
lower-layer additions (§4). The prototype's 1001 lines lose the parameter file, the capped and Walsh
variants and the `ℂ` transport, and gain the general `F`, the field, the transfer pair, isotropy, the
norm facts and the with-replacement oblivious forms.

## 8. Amendments from the review (2026-10-15)

Fable review of this note (0 blocker, 3 major, 10 minor), all thirteen amendments accepted by the
orchestrator, two corrected on inspection (A2's first ingredient exists, item 2; A11's transpose is
a conjugate transpose over `ℂ`, item 11) and A10's case split reordered (item 10); none rejected.
Q1 decided as (iii), Q2 as (c) packaged as a named predicate, D14's argument order amended;
nothing for the maintainer. The review verified the mathematics (the constant
`β (d + 2√(dt) + 2t) / n` with failure `n e^{-t}` from the general HKZ tail at `M_i`, the union over
rows, the `δ` form, `srhtRowBound_le`, the transfer, the degenerate cases), every dependency named in
§1 except D11's `sum_const_mul_of_iIndepFun` (item 4), the file sizes, the consumers' needs, and that
no statement is dominated. Where an item below contradicts §0 to §7, it supersedes them; §3 stays as
drafted. Skeletons: the files of item 15, every new proof `sorry`.

1. **Q1 decided: (iii), the general Hsu–Kakade–Zhang tail (A1, A13).** The draft's comparison is
   replaced. Option (i) (real and imaginary parts in dimension `d`, a union of two tails) is
   dominated by (ii) in every regime (`2β(d + …)` with failure `2n e^{-t}` against
   `β(2d + 2√(2dt) + 2t)` with `n e^{-t}`), so its cost for real Walsh is beside the point. The real
   choice is (ii) against (iii). Over `ℝ` they give the same constant: `M_i ξ` is a real sub-Gaussian
   vector of dimension `d` with proxy `‖M_i‖² ≤ β`, and `IsSubgaussianVector.mulVec` with the
   existing `A = 1` tail gives exactly `β(d + 2√(dt) + 2t)`, since HKZ's gain over "dimension times
   proxy" is `‖A‖_F² < rank A · ‖A‖²`, which the row matrices do not exhibit beyond what the proof
   uses. Over `ℂ` (DFT with real signs) (ii) has `2d` in place of `d` on the leading term, so the
   sample size doubles for that instance only. (iii) is still taken: the same constant over both
   fields with no field in any statement, one Probability agent-file of general-purpose work (any
   `‖A X‖²` or weighted `χ²` tail; Estimation reuses the diagonal form, item 2), and no cheaper route
   reaches the constant (item 5). *Reversal to (ii)*, corrected: every `(ε, t)` statement of §3.2 and
   §3.3 changes its constant, and a `Module.finrank ℝ 𝕜` factor enters `srhtRowBound`'s argument (or
   a `𝕜`-indexed definition), visible to every consumer that inverts a size; the draft's "the size
   corollaries do not change" was wrong. *Schedule*: the S6 skeleton does not wait for the
   Probability proof. The skeleton step adds item 2's three statements with `sorry` bodies in their
   owner files and writes `Flattening.lean` against them. If the Probability agent stalls, the
   statements stay `sorry` and the round report says so; the draft's fallback to (ii) is withdrawn,
   and no S6 statement is weakened.
2. **A2, A3: the Probability statements, files and proofs** (replaces §1 item 1). Budget 300 to 400
   lines in all, one agent, two existing files, no new dependency.
   (a) `Probability/Tail.lean` (+1; imports also `Mathlib.Probability.Moments.Basic`), the sub-gamma
       Chernoff inversion, root level:
       ```lean
       /-- **Chernoff's bound for a sub-gamma upper tail.** If `E e^{θX} ≤ exp (θ² v / (2 (1 - bθ)))`
       for `0 ≤ θ < 1/b`, then `P(√(2vt) + bt ≤ X) ≤ e^{-t}` for `t ≥ 0`.
       [BoucheronLugosiMassart2013, §2.4] (locator as the review gives it; checked against the book
       before the docstring carries it). -/
       theorem measureReal_ge_le_exp_neg_of_mgf_le {X : Ω → ℝ} {v b : ℝ} (hv : 0 < v) (hb : 0 ≤ b)
           (hint : ∀ θ : ℝ, 0 ≤ θ → b * θ < 1 → Integrable (fun ω => Real.exp (θ * X ω)) μ)
           (hmgf : ∀ θ : ℝ, 0 ≤ θ → b * θ < 1 →
             mgf X μ θ ≤ Real.exp (θ ^ 2 * v / (2 * (1 - b * θ))))
           {t : ℝ} (ht : 0 ≤ t) :
           μ.real {ω | √(2 * v * t) + b * t ≤ X ω} ≤ Real.exp (-t)
       ```
       No `[IsFiniteMeasure μ]` (`hint` at `θ = 0`). `hv` is needed: at `v = b = 0` the constant `0`
       satisfies `hmgf` and the event is everything. Proof: `measure_ge_le_exp_mul_mgf` at
       `θ = s / (1 + b s)`, `s = √(2t/v)`; then `1 - bθ = (1 + bs)⁻¹`, `θ √(2vt) = 2t / (1 + bs)`, and
       the exponent `-θ (√(2vt) + bt) + θ² v / (2 (1 - bθ))` is exactly `-t`. About 50 lines. It is
       public because every exact-constant Bernstein-type tail needs it, and
       `SubExponential/Tail.lean` has only the `min (t²/v, t/b)` forms, which lose the constant. Its
       hypothesis is a raw MGF inequality, not an interface: P1 Q3 fixed one sub-exponential
       parametrisation and rejected a sub-gamma one, and this is a Chernoff tool whose hypotheses
       are produced inside proofs, like Mathlib's `measure_ge_le_exp_mul_mgf`. If a statement ever
       carries the condition between theorems, a `HasSubgammaMGF` predicate goes through its own §8
       decision with this lemma as its tail.
   (b) `Probability/SubGaussianVector/Norm.lean` (+2; imports also
       `NLAlib.Probability.Tail`, `NLAlib.Probability.Distributions.ChiSquareTails` (or
       `ChiSquare` after S2's wrap-up merge; no cycle, nothing below imports `Norm`) and
       `NLAlib.Matrix.Norms.Frobenius`). In `namespace IsSubgaussianVector`, before
       `measure_norm_sq_ge_le`:
       ```lean
       /-- **Weighted squares of a sub-Gaussian vector**, the diagonal Hsu–Kakade–Zhang tail: for a
       real sub-Gaussian `x` with proxy `c`, weights `0 ≤ w i ≤ b`, `w ≠ 0`, and `t ≥ 0`,
       `P(c (∑ w + 2 √(∑ w²) √t + 2 b t) ≤ ∑ w_i x_i²) ≤ e^{-t}`. Hsu, Kakade and Zhang 2012,
       Theorem 2.1 for a diagonal matrix; for a Gaussian vector, Laurent and Massart's weighted bound.
       The form Gaussian Hutchinson tails use. -/
       theorem measure_sum_mul_sq_ge_le (h : IsSubgaussianVector x c μ) (hc : c ≠ 0) {w : n → ℝ}
           (hw : ∀ i, 0 ≤ w i) (hw0 : w ≠ 0) {b : ℝ} (hwb : ∀ i, w i ≤ b) {t : ℝ} (ht : 0 ≤ t) :
           μ.real {ω | c * (∑ i, w i + 2 * √(∑ i, w i ^ 2) * √t + 2 * b * t) ≤
             ∑ i, w i * x ω i ^ 2} ≤ Real.exp (-t)
       /-- **The Hsu–Kakade–Zhang tail** for a real sub-Gaussian `x` with proxy `c` and a matrix
       `A ≠ 0` over `𝕜` acting on `x`: `P(c (‖A‖_F² + 2 ‖Aᴴ A‖_F √t + 2 ‖A‖² t) ≤ ‖A x‖²) ≤ e^{-t}`.
       Hsu, Kakade and Zhang 2012, Theorem 2.1 (there `𝕜 = ℝ`; the real case is this one through
       `RCLike.ofReal_real_eq_id`). No field factor because `x` is real: the stacked real matrix
       `[Re A; Im A]` has the same Frobenius norm, spectral norm at most `‖A‖`, `‖Aᵣᵀ Aᵣ‖_F ≤ ‖Aᴴ A‖_F`
       (it is `Re (Aᴴ A)`), and the same image norm on real vectors. A complex `x` would double
       `‖A‖_F²` (the realified operator is `[[Re A, -Im A], [Im A, Re A]]`). -/
       theorem measure_norm_mulVec_sq_ge_le {m : Type*} [Fintype m] {𝕜 : Type*} [RCLike 𝕜]
           (h : IsSubgaussianVector x c μ) (hc : c ≠ 0) {A : Matrix m n 𝕜} (hA : A ≠ 0) {t : ℝ}
           (ht : 0 ≤ t) :
           μ.real {ω | c * (frobNorm A ^ 2 + 2 * frobNorm (Aᴴ * A) * √t + 2 * specNorm A ^ 2 * t) ≤
             ‖WithLp.toLp 2 (A *ᵥ fun i => (x ω i : 𝕜))‖ ^ 2} ≤ Real.exp (-t)
       ```
       `measure_norm_sq_ge_le` is reproved from the matrix form at `𝕜 = ℝ`, `A = 1` (nonempty `n`;
       the empty case stays as it is) and keeps its name (§5.2 rule 6); the private
       `measure_norm_sq_ge_le_aux` goes. No separate public real-matrix statement: it is the `𝕜 = ℝ`
       case up to `RCLike.ofReal_real_eq_id` (§5.2 rule 6). Proof of the diagonal form:
       linearise `exp (θ ∑ w_i y_i²)` with a Gaussian `g` at `√w ⊙ g`
       (`lintegral_exp_mul_dotProduct_gaussianVector`, as the file's private linearisation does),
       swap, apply the proxy, and evaluate with the **existing** weighted `χ²` transform
       `integral_exp_sum_mul_sq_of_hasLaw_gaussianVector` (`ChiSquareTails.lean`; A2's ingredient
       (a) is not missing), giving `E e^{θ ∑ w x²} ≤ ∏ (1 - 2θ c w_i)^{-1/2}` for `2θcb < 1`. Centre
       at `c ∑ w`; Laurent and Massart's log-MGF step `-(1/2) ∑ log (1 - u_i) ≤ (1/2) ∑ u_i +
       ∑ u_i² / (4 (1 - max u))` at `u_i = 2θ c w_i`, from the private scalar
       `-log (1 - u) ≤ u + u² / (2 (1 - u))` on `[0, 1)` (series bound as `ChiSquareTails`'
       `log_one_sub_le'`; promoted to `ForMathlib/Analysis/SpecialFunctions/Log/Deriv.lean` when a
       second file wants it); this is (a) at `v = 2c² ∑ w²`, `b' = 2cb`, whose threshold
       `√(2vt) + b't` is `2c √(∑ w²) √t + 2cbt`. Proof of the matrix form: a private real-matrix
       lemma through Mathlib's spectral theorem for `Aᵀ A` (`Y = Vᵀ x` has proxy `c` by
       `IsSubgaussianVector.mulVec` and `.mono`; weights the eigenvalues, `∑ = ‖A‖_F²`,
       `√(∑ λ²) = ‖Aᵀ A‖_F`, `λ_i ≤ ‖A‖²`), then the stacking `Matrix.fromRows (A.map re)
       (A.map im)` for `𝕜` (three private facts, each a few lines). The module docstring's sentence
       "the complex versions are the real ones in dimension `2n`" is replaced by the field remark of
       the matrix form's docstring. Result id `hsu-kakade-zhang` moves to the matrix form; the
       diagonal form and (a) carry none.
   Line estimate: (a) about 50; (b) about 300 net of the deleted helper; `Norm.lean` reaches about
   560 lines, `Tail.lean` about 210.
3. **A3, flattening without realification** (amends §3.2's proof and §5's ledger). Row `i` of
   `F D Q` is `n^{-1/2} M_i (ξ : n → 𝕜)` with `M_i := Qᵀ * diagonal (fun l => √n * F i l)`. Item 2's
   matrix form at `A = M_i`, proxy `1` (`isSubgaussianVector_of_hasLaw_rademacherVector`), with
   `‖M_i‖_F² ≤ βd`, `‖M_i‖ ≤ √β`, `‖M_iᴴ M_i‖_F ≤ ‖M_i‖ ‖M_i‖_F ≤ β√d`
   (`frobNorm_mul_le_specNorm_mul_frobNorm`, `specNorm_conjTranspose`), bounds the row event by
   `e^{-t}`; `M_i = 0` makes the row event empty (the `hA` case). `Flattening.lean` has no
   realification helpers; the prototype's `norm_toLp_ofReal_eq` and `specNorm_le_specNorm_map_ofReal`
   are the `ℝ`-to-`𝕜` cast, not the Re/Im stacking, and are not used anywhere (§5's ledger line on
   them reads "not ported").
4. **A4, a nonexistent name.** `HasSubgaussianMGF.sum_const_mul_of_iIndepFun`, which D11 names,
   exists in neither Mathlib nor NLAlib; Mathlib's lemma is `HasSubgaussianMGF.sum_of_iIndepFun`.
   No S6 proof uses either (item 1). Q1's mention of it reads so.
5. **A5, the rejected routes and the constant 8, recorded in Q1.** Entrywise Hoeffding with a union
   over the `n d` entries gives a squared row norm at most `2βd log (2nd/δ) / n`, a `log (nd)` factor
   on the leading term against `d + O(log (n/δ))` here (the pre-Tropp bound). Tropp's vector route
   (convex Lipschitz concentration on the cube, Ledoux's `e^{-t²/8}`) gives
   `(√d + √(8 log (n/δ)))²` and needs Talagrand-type concentration on the cube, which the library
   lacks (`BoundedDifferences.lean` is McDiarmid, whose deviation here is multiplicative in `√d`).
   HKZ is the cheapest route to the sharp constant and the sharpest (`2` against `8` in the log
   term). The `8` is located in hand through [HalkoMartinssonTropp2011, Theorem 11.1]
   (`[√k + √(8 log (kn))]²`). Tropp 2011a is cited by name only (key `[Tropp2011a]`, no theorem,
   lemma or section number, as S5 §8 item 3): every "Tropp 2011a, Lemma 3.3", "§3.3", "Theorem 3.2"
   and "main theorem" in the docstrings of §3.2 and §3.3 becomes the bare name, and
   `srhtRowBound`'s docstring gives the `8` through HMT. Q9's list of unverified locators stays as
   a record, not as citations.
6. **Q2 decided: generality (c), packaged as the interface `IsBoundedOrthonormal` (A8).**
   CONTRIBUTING §5.4 ("theorems take the interface, never the raw condition") applies: the pair
   `hF`, `hFβ` is one hypothesis bundle in ten S6 signatures, with four instance producers (Walsh,
   Fourier, Mathlib's Hadamard matrices, and DCT and DHT when they exist), and the literature names
   it (a bounded orthonormal system, Foucart and Rauhut, `K² = β`; chapter 12 per the review). D8's raw domination is
   one inequality, not a bundle, and is no precedent here. Name: library style is `Is…` for a
   property of a matrix (`IsSVD`, `IsQR`, `IsCholesky`) and `Has…` for one of its columns
   (`HasOrthonormalCols`); `IsBoundedOrthonormal` keeps the literature's term. New file
   `NLAlib/Matrix/Structured/BoundedOrthonormal.lean` (imports `NLAlib.Matrix.Basic.Orthonormal`,
   `Mathlib.LinearAlgebra.Matrix.HadamardMatrix`), 4 statements:
   ```lean
   /-- `F` is a **bounded orthonormal transform** with constant `β`: a unitary
   (`HasOrthonormalCols F`, `F` square) whose entries satisfy `card n * ‖F i j‖² ≤ β`. `β = 1` for the
   normalised Walsh–Hadamard and Fourier matrices and every normalised Hadamard matrix, `β = 2` for
   the discrete cosine and Hartley transforms. For nonempty `n`, `1 ≤ β`. The bounded orthonormal
   systems of Foucart and Rauhut's book on compressive sensing, with `K² = β` (by name);
   [CamanoEpperlyMeyerTropp2025, Imported Theorem 4.3] (the two features the flattening uses). -/
   structure IsBoundedOrthonormal (F : Matrix n n 𝕜) (β : ℝ) : Prop where
     hasOrthonormalCols : HasOrthonormalCols F
     card_mul_norm_sq_le : ∀ i j, (Fintype.card n : ℝ) * ‖F i j‖ ^ 2 ≤ β
   /-- A Hadamard matrix scaled by `(√card n)⁻¹` is bounded orthonormal with `β = 1`. -/
   theorem _root_.Matrix.IsHadamard.isBoundedOrthonormal_inv_sqrt_smul {H : Matrix n n 𝕜}
       (hH : H.IsHadamard) : IsBoundedOrthonormal (((√(Fintype.card n : ℝ))⁻¹ : ℝ) • H) 1
   theorem IsBoundedOrthonormal.transpose (hF : IsBoundedOrthonormal F β) :
       IsBoundedOrthonormal Fᵀ β
   theorem IsBoundedOrthonormal.conjTranspose (hF : IsBoundedOrthonormal F β) :
       IsBoundedOrthonormal Fᴴ β
   ```
   (`transpose` and `conjTranspose`: square `F`, `Matrix.mul_eq_one_comm`, `norm_star`; their
   consumer is LowRank's HMT test matrix, item 11.) Instances, replacing §1 item 3's four lemmas:
   `isBoundedOrthonormal_smul_walshHadamard (b : ℕ) : IsBoundedOrthonormal
   (((√((2 : ℝ) ^ b))⁻¹ : ℝ) • walshHadamard 𝕜 b) 1` in `Structured/Walsh.lean` (+1, from
   `hasOrthonormalCols_smul_walshHadamard`, `norm_smul_walshHadamard_apply` and
   `Fintype.card (Fin b → ZMod 2) = 2 ^ b`) and `isBoundedOrthonormal_fourierMatrix (n : ℕ) :
   IsBoundedOrthonormal (fourierMatrix n) 1` in `Structured/Circulant.lean` (+1); both files import
   the new one. `card_mul_norm_smul_walshHadamard_apply_sq`,
   `IsHadamard.hasOrthonormalCols_inv_sqrt_smul`, `IsHadamard.card_mul_norm_inv_sqrt_smul_apply_sq`
   and `card_mul_norm_fourierMatrix_apply_sq` are not stated (fields of the instances). **S6
   signatures**: `(hF : IsBoundedOrthonormal F β)` replaces `(hF) (hFβ)` in the two flattening
   theorems, the four oblivious theorems and the four size corollaries; the a.s. unitary lemma,
   isotropy and the partial-isometry pair keep `(hF : HasOrthonormalCols F)`, all they use
   (§5.2, minimal hypotheses; a user passes `hF.hasOrthonormalCols`). §2's "None new" now reads:
   one new interface, `IsBoundedOrthonormal` (Matrix layer), designed here; a §5.3 row "bounded
   orthonormal transform | `IsBoundedOrthonormal F β` | `Matrix.IsHadamard.isBoundedOrthonormal_inv_sqrt_smul`"
   beside §1's SRHT row (both §5.3/§5.4 changes, two approvals, CONTRIBUTING §9). §3.4's instances
   read with these names. Foucart and Rauhut are cited by name, with no key or chapter (not in
   `docs/references.bib`, not in hand).
7. **A7, the Hadamard bridge and the deviation entry.** The entry bound uses `apply_mem` (`H i j ∈
   unitary 𝕜`) and Mathlib's `CStarRing.norm_of_mem_unitary` for `‖H i j‖ = 1`; orthonormality is
   `conjTranspose_mul` with the scalar `(√n)⁻² n = 1`; for empty `n` both fields hold vacuously (the
   scalar is `0`, `0ᴴ 0 = 1` in the empty type). The `docs/design/Mathlib-deviations.md` entry says the
   library's hypothesis is **strictly weaker** than `Matrix.IsHadamard` on the unnormalised matrix
   (an inequality on the entries admits DCT and DHT, which are not Hadamard), not a respelling; the
   bridge is item 6's constructor.
8. **A6, the transfer's events** (amends §3.2's transfer proof). `E := {(A, B) | ¬ IsSubspaceInjection
   (A * B) U a}`, open by `isClosed_setOf_isSubspaceInjection` composed with matrix multiplication;
   `hTU` enters only through `G := {B | HasOrthonormalCols B ∧ ∀ i, leverageScore (B * U) i ≤
   L * (card n)⁻¹}`. For `B ∈ G` the section identity `IsSubspaceInjection (A * B) U a ↔
   IsSubspaceInjection A (B * U) a` is deterministic (`(B U)ᴴ (B U) = Uᴴ U`), so the section is
   `hsample (B * U)` and `{(P, T) ∈ E}` is literally the failure event: no almost-everywhere
   congruence of the final event. The embedding is the same with `isClosed_setOf_isSubspaceEmbedding`.
9. **A9, where `hk : card k ≤ card n` goes.** On `isProbabilityMeasure_srht`, isotropy, the OSI (its
   `isotropic` field) and the OSI size corollary, never on the OSE or a tail: for `card n < card k`
   the law is `0`, `HasLaw` forces `μ = 0`, every tail holds, but `IsIsotropicSketch` fails (the
   integral is `0`, not `1`). The skeleton keeps this placement; §3's degenerate list and
   `SRHT.lean`'s module docstring say so.
10. **A10, the case split of the size proofs**, reordered on inspection. `L := β * srhtRowBound n d (δ/2)`
    is negative when `δ/2 > n` and `d` is small, and `samplingSize_mono` needs `0 ≤ L` and
    `δ/2 ≤ 2d'` (S4's skeleton notes). The review's first branch ("`δ/2 > n` gives `δ > 1`") fails for
    empty `n`. The proofs split first on `1 ≤ δ` (trivial: `μ` is a probability measure or `0`, so
    `μ.real _ ≤ 1 ≤ δ`; the OSI's isotropy field is the isotropy theorem), then on empty `n` or
    `d = 0` (every event is empty). For `δ < 1`, nonempty `n` and `d' ≥ 1`, `δ/2 < card n` and
    `δ/2 ≤ 2d'`, so `srhtRowBound_nonneg` and `samplingSize_mono` (resp. `samplingInjectionSize_mono`)
    apply.
11. **A11, HMT's test matrix**, corrected on inspection. HMT's `Ω = √(n/ℓ) D F R` acts on the right.
    It is `Sᵀ` with our `F := F_HMTᵀ`, or `Sᴴ` with `F := F_HMTᴴ` (the review's "`Sᴴ` with `Fᵀ`"
    conjugates `F` over `ℂ`; harmless for the real Walsh case, wrong for the DFT). Item 6's
    `transpose` and `conjTranspose` carry the hypothesis across, so LowRank uses the S6 theorems
    unchanged. `srhtMatrix`'s docstring says so.
12. **A12, `srhtRowBound_le`** stays hypothesis-free; its docstring says it covers the junk range
    (Lean's `√` of a negative is `0`: for `log (n/δ) < 0` the left side is `d + 2 log (n/δ) < d` and
    the right side is `d`).
13. **D14's argument order.** `srht k F` and `srhtWithReplacement k F`, sketch index first, as Q3
    proposes; accepted by the orchestrator, who amends D14's `srht H k` in the brief.
14. **Citations.** HKZ by name, as `Norm.lean` does (not in hand; no new key). Tropp 2011a by name
    only (item 5). The `8` through HMT Theorem 11.1. BLM §2.4 for (a) as item 2 says. CEMT, MT,
    HMT, Woodruff as drafted.
15. **Files** (amends §4 and §1's lower-layer list). S6 proper unchanged: 32 statements,
    1. `Sketching/Structured/Flattening.lean` (9: 1 definition, 8 theorems), imports also
       `Matrix/Structured/BoundedOrthonormal`; about 380 lines (no realification);
    2. `Sketching/Structured/SRHT.lean` (23: 3 definitions, 2 instances, 18 theorems).
    Lower layers, 11 statements:
    - `Probability/Tail.lean` (+1, item 2 (a));
    - `Probability/SubGaussianVector/Norm.lean` (+2, item 2 (b); one theorem reproved);
    - `ForMathlib/Probability/Independence/Basic.lean` (new, 1, §3.1);
    - `Matrix/Structured/BoundedOrthonormal.lean` (new, 4: 1 structure, 3 theorems; item 6);
    - `Matrix/Structured/Walsh.lean` (+1), `Matrix/Structured/Circulant.lean` (+1) (item 6);
    - `Sketching/Sampling/RowSampling.lean` (+1, §1 item 4).
    In all, 43 statements. Order: the skeleton step writes every new statement, the lower-layer ones
    with `sorry` in their owner files, then the two S6 files (item 1: nothing waits for the
    Probability proof). Proofs: the Probability pair (one agent), the ForMathlib lemma, the Matrix
    file and instances, the RowSampling identity, independent of each other; then `Flattening.lean`,
    then `SRHT.lean`, which also waits for S5's `WithoutReplacement.lean`.
16. §7: Q3 to Q11 stand (Q3's D14 order by item 13, Q9 read with items 5 and 14, Q11's lower-layer
    count by item 15); Q1 is decided by item 1 (its comparison, fallback and reversal replaced, with
    items 4 and 5), Q2 by item 6.
