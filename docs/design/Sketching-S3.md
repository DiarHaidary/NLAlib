# Design note: Sketching stage S3, sub-Gaussian and Rademacher sketches

Status: drafted 2026-10-15 under `docs/PORT_SKETCHING.md` (D1 to D5; D12, D14; §3). One question for the
orchestrator (§7 Q6), none of the brief's §2 kind. One amendment to D12's last sentence (§7 Q1). Two
small skeleton files beside the family file (§3.1, §3.2).

## 0. Scope and consumers

`S = (√k)⁻¹ • X` for `X : Ω → Matrix k n ℝ` with independent, isotropic, sub-Gaussian rows (R3's three
hypotheses), for independent sub-Gaussian entries (a bridge to the rows), and for
`HasLaw X (rademacherMatrix k n) μ`. As in S2, in this note `√k := √(Fintype.card k : ℝ)` and
`S_X := fun ω => (√k)⁻¹ • X ω`; the Lean statements spell these out.

| Item | Consumers |
|---|---|
| JL plus a net gives an embedding (any sketch, over `𝕜`) | S3's OSEs; any later family with a JL tail and no Gram-level tail |
| JL tail, `subgaussianJLConstant`; JL moment at `p = 2` | users with sign sketches; Estimation (Hutch++, XTrace) through S1's AMM; closes `Probability-REPORT.md` §6.1 item 5 |
| OSE and OSI, sizes `subgaussianJLDim`, `subgaussianEmbeddingDim` | Solvers (sketch-and-solve, -precondition with sign sketches); LowRank R1, R2, R5, R6 through S1 |
| `rademacherMatrix`, its isotropy, exact JL second moment | the sign sketch users hold; S6 and S7 reuse nothing of it |

## 1. Objects

New, by D14: `rademacherMatrix k n := Measure.pi fun _ : k => rademacherVector n` (an `abbrev`, as
`gaussianMatrix`; no existing spelling: `Rademacher.lean` has `rademacherMeasure`, `rademacherVector`
only). By D12, `subgaussianJLConstant` (§5.2 rule 2). By D5, two sizes, each an `irreducible_def` with
`_nonneg`, `_mono`, `_le`. Used directly: R3, P1, P3 (names in the proof routes), S1, the Matrix
layer's `exists_finset_specNorm_le_div_of_isHermitian`. No deviation from Mathlib.

## 2. Interfaces

None new. Taken: R3's suffix `_of_isSubgaussianVector`, the three row hypotheses in this order,
`hind : iIndepFun (fun i ω => X ω i) μ`, `hsub : ∀ i, IsSubgaussianVector (fun ω => X ω i) c μ`,
`hiso : ∀ i, IsIsotropic (fun ω => X ω i) μ` (`c : ℝ≥0`, the variance proxy, Vershynin's `K²`); the
entry hypotheses of `HasLaw.iIndepFun_entry`'s shape; `HasLaw X (rademacherMatrix k n) μ`. Concluded:
`HasJLProperty`, `HasJLMoment` (`p = 2`), `IsObliviousSubspaceEmbedding`, `IsObliviousSubspaceInjection`,
`IsIsotropicSketch`. Isotropy of the rows family is S1's `isIsotropicSketch_smul_of_isIsotropic`
(no independence needed), so the rows family gets no isotropy statement.

## 3. Statement shapes

`namespace NLAlib`, `open MeasureTheory ProbabilityTheory`, `open scoped Matrix MatrixOrder NNReal`.

Degenerate cases. `card k = 0`: `S = 0`, the JL bounds are `2` and the OSE bounds `2 · 9^d`, all true;
not isotropic, hence `[Nonempty k]` on isotropy, OSI and moments. `card n = 0`: rows are empty vectors,
everything holds. `c = 0`: with rows and columns the hypotheses are contradictory (isotropy and
`HasSubgaussianMGF.integral_sq_le` force `1 ≤ c`, R3's private `one_le_of_isSubgaussianVector`);
otherwise `ε / 0 = 0` and the bound is `2`. No `0 ≤ ε` on the tails: for `ε < 0`, `min (ε²/c²) (ε/c) < 0`
and the bound exceeds `2` (unlike S2, whose polynomial exponent is positive there). `ε ≥ 1`: the lower
JL event is null and the lower OSE constant `1 - ε ≤ 0` is vacuous (`isSubspaceInjection_of_nonpos`).
`d = 0`, `p` empty: trivial; `d > card n`: S1's constructors at `Fin (min d (card n))` and `mono`, which
needs `0 ≤ δ` (hence `hδ` in §3.1). JL moment: `ε = 0` and empty `k` excluded (`hε`, `[Nonempty k]`).

### 3.1 `Sketching/Properties/JohnsonLindenstraussNet.lean` (skeleton, 2)

Over `𝕜`, any sketch. `{S : Ω → Matrix k n 𝕜} {U : Matrix n p 𝕜} [Fintype p] [DecidableEq p]`.
```lean
/-- **JL plus a net**: a JL tail at `ε` gives a `1 ∓ 2ε` embedding of a fixed orthonormal `U`, failing
with probability at most `9^{dim_ℝ} δ`. [Vershynin2018, proof of Theorem 4.6.1, (4.22) (2020 draft)];
[Woodruff2014, Lemma 5 and Theorem 6], there a `1/2`-net and `O(ε)`. -/
theorem HasJLProperty.hasSubspaceEmbedding [IsFiniteMeasure μ] (h : HasJLProperty S ε δ μ)
    (hδ : 0 ≤ δ) (hU : HasOrthonormalCols U) : HasSubspaceEmbedding S U (1 - 2 * ε) (1 + 2 * ε)
      (9 ^ (Fintype.card p * Module.finrank ℝ 𝕜) * δ) μ
theorem HasJLProperty.isObliviousSubspaceEmbedding [IsFiniteMeasure μ] (h : HasJLProperty S ε δ μ)
    (hδ : 0 ≤ δ) (d : ℕ) : IsObliviousSubspaceEmbedding S d (1 - 2 * ε) (1 + 2 * ε)
      (9 ^ (d * Module.finrank ℝ 𝕜) * δ) μ
```
Proof: `exists_finset_specNorm_le_div_of_isHermitian 𝕜 p` at `1/4` (card `≤ 9 ^ finrank ℝ (p → 𝕜)`,
`finrank_real_fun`) on `E = (S U)ᴴ (S U) - 1`; `re (quadForm E x) = ‖S (U x)‖² - 1` with `‖U x‖ = 1`;
off the union of the JL events `max_N |·| < ε`, so `specNorm E < 2ε`; `measureReal_biUnion_finset_le`,
then S1's `HasOrthonormalCols.hasSubspaceEmbedding_of_measureReal_le`. Oblivious: S1's
`IsObliviousSubspaceEmbedding.of_hasOrthonormalCols` at `Fin (min d (card n))`, `mono`. No `hε`: for
`ε ≤ 0` and `N` nonempty the union is everything. Searched: no JL-to-embedding lemma in NLAlib or
Mathlib; R3 has the same net step privately, specialised to rows (`measureReal_not_specNorm_lt`).

### 3.2 `Probability/IndependentRows.lean` (skeleton, 1)

```lean
/-- Independent entries give independent rows. Mathlib has the converse (`iIndepFun_uncurry'`). -/
theorem iIndepFun_row_of_iIndepFun_entry {X : Ω → Matrix m n α}
    (hind : iIndepFun (fun p : m × n => fun ω => X ω p.1 p.2) μ)
    (hX : ∀ i j, AEMeasurable (fun ω => X ω i j) μ) : iIndepFun (fun i ω => X ω i) μ
```
Proof: `hasLaw_pi_pi_iff` with `ν i j := μ.map (X · i j)` (hence `hX`), then `HasLaw.iIndepFun_eval`.
`hX` goes if a Mathlib grouping lemma (`iIndepFun` over a partition of the index) turns up.

### 3.3 `Sketching/Gaussian/SubGaussian.lean` (28)

`{X : Ω → Matrix k n ℝ} [DecidableEq n] {c : ℝ≥0}`; `(hind) (hsub) (hiso)` as in §2; `c` coerced to `ℝ`.
```lean
/-- The constant of the sub-Gaussian JL tail `2 exp (-C k min (ε²/c², ε/c))`. Unspecified in
[Vershynin2018, Exercise 5.3.3, Theorem 2.8.1 (2020 draft)]; prototype `1/(256 e²)` (`ε < 1` only).
The proof reaches `min (ε²/(64 c²)) (ε/(8 c))` (P1's `(32 c², 4 c)` and Bernstein), whose linear part is
8 times this one's. Larger is better; use only `_pos`, `le_subgaussianJLConstant`. -/
noncomputable irreducible_def subgaussianJLConstant : ℝ := 1 / 64
theorem subgaussianJLConstant_pos : 0 < subgaussianJLConstant
theorem le_subgaussianJLConstant : 1 / 64 ≤ subgaussianJLConstant
/-- **Sub-Gaussian distributional JL**. [Vershynin2018, Exercise 5.3.3 (2020 draft)]. Replaces the
prototype's `measure_lt_abs_mulVec_sq_sub_le_of_independent_isotropic_rows`. Result: jl-subgaussian -/
theorem hasJLProperty_of_isSubgaussianVector (hind) (hsub) (hiso) : HasJLProperty S_X ε
    (2 * Real.exp (-(subgaussianJLConstant * Fintype.card k * min (ε ^ 2 / c ^ 2) (ε / c)))) μ
/-- `E (‖S x‖² - 1)² = (E ⟨Xᵢ, x⟩⁴ - 1)/k`, with `E ⟨Xᵢ, x⟩⁴ ≤ 16 c²`. -/
theorem hasJLMoment_of_isSubgaussianVector [Nonempty k] (hind) (hsub) (hiso) (hε : 0 < ε) :
    HasJLMoment S_X ε ((16 * c ^ 2 - 1) / (Fintype.card k * ε ^ 2)) 2 μ
/-- **Sub-Gaussian OSE**: §3.1 at `ε/2`. [Vershynin2018, Theorem 4.6.1, (4.22) (2020 draft)], there
`K² max (δ, δ²)` with unspecified `C`. Result: subgaussian-ose (new) -/
theorem isObliviousSubspaceEmbedding_of_isSubgaussianVector (hind) (hsub) (hiso) (d : ℕ) :
    IsObliviousSubspaceEmbedding S_X d (1 - ε) (1 + ε) (2 * 9 ^ d * Real.exp
      (-(subgaussianJLConstant * Fintype.card k * min (ε ^ 2 / (4 * c ^ 2)) (ε / (2 * c))))) μ
theorem isObliviousSubspaceInjection_of_isSubgaussianVector [Nonempty k] (hind) (hsub) (hiso) (d : ℕ) :
    IsObliviousSubspaceInjection S_X d (1 - ε) (2 * 9 ^ d * Real.exp (-(…same…))) μ
/-- Junk: for `δ ≥ 2` or `δ ≤ 0` the logarithm's sign is wrong; `0` at `ε = 0`. -/
noncomputable irreducible_def subgaussianJLDim (c ε δ : ℝ) : ℝ :=
  c ^ 2 * Real.log (2 / δ) / (subgaussianJLConstant * ε ^ 2)
noncomputable irreducible_def subgaussianEmbeddingDim (c : ℝ) (d : ℕ) (ε δ : ℝ) : ℝ :=
  4 * c ^ 2 * (d * Real.log 9 + Real.log (2 / δ)) / (subgaussianJLConstant * ε ^ 2)
-- `_nonneg (hδ : 0 < δ) (hδ2 : δ ≤ 2)`, `_mono` (monotone in `0 ≤ c` and `d`, antitone in `ε > 0`, `δ > 0`) (4);
theorem subgaussianJLDim_le (c ε : ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 2) :
    subgaussianJLDim c ε δ ≤ 64 * c ^ 2 * Real.log (2 / δ) / ε ^ 2
/-- Comparison: `256 log 9 ≤ 576`; [Woodruff2014, Theorem 6]'s `Θ ((d + log (1/δ))/ε²)`. -/
theorem subgaussianEmbeddingDim_le (c : ℝ) (d : ℕ) (ε : ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 2) :
    subgaussianEmbeddingDim c d ε δ ≤ 576 * c ^ 2 * (d + Real.log (2 / δ)) / ε ^ 2
theorem hasJLProperty_of_isSubgaussianVector_of_subgaussianJLDim_le (hind) (hsub) (hiso) (hε : 0 < ε)
    (hεc : ε ≤ c) (hδ : 0 < δ) (hk : subgaussianJLDim c ε δ ≤ Fintype.card k) : HasJLProperty S_X ε δ μ
theorem isObliviousSubspaceEmbedding_of_isSubgaussianVector_of_subgaussianEmbeddingDim_le (hind) (hsub)
    (hiso) (hε : 0 < ε) (hεc : ε ≤ 2 * c) (hδ : 0 < δ)
    (hk : subgaussianEmbeddingDim c d ε δ ≤ Fintype.card k) : IsObliviousSubspaceEmbedding S_X d (1 - ε) (1 + ε) δ μ
-- the OSI twin, `[Nonempty k]`, same hypotheses (1)
/-- Entries: independent, sub-Gaussian with proxy `c`, unit variance (the mean is `0` by
`HasSubgaussianMGF.integral_eq_zero`; the prototype's `hmean` is dropped). The other rows theorems
apply to entries through the same three steps (proof below). Replaces the prototype's
`…_of_independent_subgaussian_entries`. Result: jl-subgaussian -/
theorem hasJLProperty_of_iIndepFun_entry (hind : iIndepFun (fun p : k × n => fun ω => X ω p.1 p.2) μ)
    (hsub : ∀ i j, HasSubgaussianMGF (fun ω => X ω i j) c μ) (hvar : ∀ i j, ∫ ω, X ω i j ^ 2 ∂μ = 1) :
    HasJLProperty S_X ε (2 * Real.exp (-(subgaussianJLConstant * Fintype.card k * min (ε ^ 2 / c ^ 2) (ε / c)))) μ
noncomputable abbrev rademacherMatrix (k n : Type*) [Fintype k] [Fintype n] : Measure (Matrix k n ℝ) :=
  Measure.pi fun _ : k => rademacherVector n
instance isProbabilityMeasure_rademacherMatrix : IsProbabilityMeasure (rademacherMatrix k n)
theorem isIsotropicSketch_of_hasLaw_rademacherMatrix [Nonempty k] (hX : HasLaw X (rademacherMatrix k n) μ) :
    IsIsotropicSketch S_X μ
/-- [Woodruff2014, §2.1, after Theorem 6] attributes sign JL to Achlioptas (2003), with Gaussian
constants; here Bernstein's (§7 Q6). -/
theorem hasJLProperty_of_hasLaw_rademacherMatrix (hX) :
    HasJLProperty S_X ε (2 * Real.exp (-(subgaussianJLConstant * Fintype.card k * min (ε ^ 2) ε))) μ
/-- Exact: `2 (‖x‖⁴ - ∑ xⱼ⁴)/k`, at most the Gaussian's `2 ‖x‖⁴/k`. -/
theorem integral_norm_mulVec_sq_sub_norm_sq_sq_of_hasLaw_rademacherMatrix [Nonempty k] (hX) (x : n → ℝ) :
    ∫ ω, (‖WithLp.toLp 2 (S_X ω *ᵥ x)‖ ^ 2 - ‖WithLp.toLp 2 x‖ ^ 2) ^ 2 ∂μ =
      2 / Fintype.card k * (‖WithLp.toLp 2 x‖ ^ 4 - ∑ j, x j ^ 4)   -- + integrable_… (no `[Nonempty k]`)
theorem hasJLMoment_of_hasLaw_rademacherMatrix [Nonempty k] (hX) (hε : 0 < ε) :
    HasJLMoment S_X ε (2 / (Fintype.card k * ε ^ 2)) 2 μ
-- `isObliviousSubspaceEmbedding_of_hasLaw_rademacherMatrix (hX) (d)`, `…Injection… [Nonempty k] (hX) (d)`:
-- the rows forms at `c = 1`, `min (ε ^ 2 / 4) (ε / 2)` (2). Result: rademacher-ose (new)
```
Proofs. JL: R3's `hasSubexponentialMGF_norm_mulVec_sq_sub_of_isSubgaussianVector` (`(32 c² k, 4 c)`, a
Bernstein sum: P1's `HasSubgaussianMGF.hasSubexponentialMGF_sq_sub_integral`, `sum_of_iIndepFun`; the
same exponent as `measure_sum_ge_le_of_iIndepFun`, two-sided), `HasSubexponentialMGF.measure_abs_ge_le`
at `t = ε k`, `‖S x‖² = ‖X x‖²/k`, `min (ε² k/(64 c²)) (ε k/(8 c)) ≥ k min (ε²/c²) (ε/c) / 64`; `ε < 0`
and empty `k` by `measureReal_le_one`. Moment: `IndepFun.variance_sum` over rows, `E ⟨Xᵢ,x⟩² = 1`
(`IsIsotropic.integral_norm_dotProduct_sq`), `HasSubgaussianMGF.integral_abs_rpow_le` at `p = 4`
(`4 (2c)² Γ(2) = 16 c²`). OSE: §3.1 at `ε/2` with `finrank ℝ ℝ = 1`; OSI: `.isObliviousSubspaceInjection`
and `isIsotropicSketch_smul_of_isIsotropic`. Sizes: for `ε ≤ c` (resp. `ε/2 ≤ c`) the `min` is its
quadratic part; `δ ≥ 2` is trivial. Entries: §3.2 (`HasSubgaussianMGF.aemeasurable`); row coordinates
by `iIndepFun.precomp` (injectivity of `(i, ·)`), then `IsSubgaussianVector.of_iIndepFun` and
`IsIsotropic.of_iIndepFun`. Rademacher: `HasLaw.eval`, `HasLaw.iIndepFun_eval`,
`isSubgaussianVector_of_hasLaw_rademacherVector`, `isIsotropic_of_hasLaw_rademacherVector`; the moment
from `variance_quadForm_of_hasLaw_rademacherVector` at `A = vecMulVec x x` (`‖A‖_F² = ‖x‖⁴`) and
`IndepFun.variance_sum`.

## 4. Files

1. `NLAlib/Sketching/Properties/JohnsonLindenstraussNet.lean` (skeleton): §3.1 (2); imports
   `Properties/{JohnsonLindenstrauss,FixedSubspace,Oblivious}`, `Matrix/Norms/Net`. Merges into
   `JohnsonLindenstrauss.lean` at the wrap-up.
2. `NLAlib/Probability/IndependentRows.lean` (skeleton): §3.2 (1); imports `Probability/Law`. Merges
   into `Law.lean`.
3. `NLAlib/Sketching/Gaussian/SubGaussian.lean` (skeleton): §3.3 (28: 4 definitions and an instance,
   8 constant and size lemmas, 15 theorems); imports 1, 2, R3 `SubGaussian/ExtremeSingularValues`,
   `Distributions/Rademacher`, `QuadraticForm/Moments`, `Properties/Isotropic`.
About 700 lines against the brief's 400: the net step (120) and the Rademacher block (150) are the
overrun. Bibliography: nothing new; Achlioptas 2003 is cited by name only (brief §7.2).

## 5. Material

Read: the prototype's `RandomMatrix/SubGaussian/SubGaussianJL.lean` (the two ledger entries, strict
events, `ε < 1`, `K ≥ 1`, `1/(256 e²)`); it has no sub-Gaussian or sign sketch in `Sketching/`.
Vershynin (2020 draft; theorem numbers from the draft, section numbers agree with the print, brief
§7.1): Theorem 4.6.1 with (4.22) and its net proof (Corollary 4.2.13, Lemma 4.4.1, Exercise 4.4.3),
Exercise 5.3.3, Theorem 2.8.1. Woodruff §2.1: (2), Lemma 5, Theorem 6 and the Achlioptas paragraph
after it. MT §8.8, Theorem 8.7 (universality of the minimum restricted singular value, Oymak and Tropp
2018): asymptotic only, not used. Ledger: `measure_lt_abs_mulVec_sq_sub_le_of_independent_isotropic_rows`
→ `hasJLProperty_of_isSubgaussianVector` (dominates it: `1/64` against `1/(256 e²)`, no `ε < 1`, `hK`
from the hypotheses); `…_of_independent_subgaussian_entries` → `hasJLProperty_of_iIndepFun_entry`.
`IsIsotropic.mulVec` and `IsSubgaussianVector.mulVec`, which the brief's R3 route needed, are unused
(§7 Q1). Result ids: `jl-subgaussian`; new `subgaussian-ose`, `rademacher-ose`.

## 6. Cut, and why

The OSE from R3's rows theorem (dominated, §7 Q1); Hanson–Wright for entries (dominated, Q2); entries
twins of the moment, OSE, OSI and sizes (Q5); fixed-`U` family forms (`IsObliviousSubspaceEmbedding
.hasSubspaceEmbedding` gives them); a net radius other than `1/4` (an incomparable family in `η`, rule 4,
when wanted); Rademacher size twins (rows corollaries at `c = 1`); JL moment at `p ≠ 2` (S2 Q4);
complex sign sketches (brief §0).

## 7. Questions and decisions

**For the orchestrator:** Q6. **Decisions taken** (open to correction):

**Q1. The OSE goes through JL plus a net; R3's rows route is dominated** (rule 6), which amends D12's
"sub-Gaussian sample sizes are written in R3's shape". At matched failure `2 e^{-t²}`, R3 gives
`(1 ∓ x)²` with `x = 24 c (√d + t)/√k` (htk: `x ≤ 1`); §3.3 gives `1 ∓ ε` with, in the quadratic regime,
`ε = 16 c √(d log 9 + t²)/√k ≤ 16 c (1.483 √d + t)/√k ≤ x`, so `(1 - x)² ≤ 1 - x ≤ 1 - ε` and
`(1 + x)² ≥ 1 + ε`; in the linear regime (`ε > 2c`, possible only when `x > 2`) `x² ≥ 262 c² L/k ≥
128 c L/k = ε` for `c ≥ 1`, which the hypotheses force (`L = d log 9 + t²`). Checked numerically on a
grid (`c ≤ 20`, `d ≤ 1000`, `k ≤ 10^10`): no exception. It also dominates R3's private (4.22) form
`1 ∓ max (x, x²)`. Sizes: `576 c² (d + log (2/δ))/ε²` against about `5184 c² (√d + √log (2/δ))²/ε²`
from R3. Follow-up, not this stage: R3's rows theorem is §3.1 at `U = 1`; at the wrap-up it can be
reproved from it, keeping its name (rule 6). Not costly to reverse: no consumer yet.

**Q2. Bernstein, not Hanson–Wright.** For entries, HW at `A = 1_k ⊗ x xᵀ` (`‖A‖_F² = k`, `‖A‖ = 1`)
gives `hansonWrightConstant · k min (ε²/c², ε/c)`, `1/196 < 1/64`, under stronger hypotheses.

**Q3. `subgaussianJLConstant` in Vershynin's two-regime shape** `C k min (ε²/c², ε/c)` (`c = K²`), the
shape of `hansonWrightConstant`'s statements; the proof's sharper linear part is given up (docstring).

**Q4. Moment constants written in statements**: `16 c² - 1` is `integral_abs_rpow_le`'s closed form at
`p = 4` (that lemma "improves only with the tail"); Rademacher's is exact. A name if a consumer asks.

**Q5. Entries through a bridge**, not twins: §3.2 and three proof steps; only the JL (the ledger
entry) is stated for entries.

**Q6 (open, for the orchestrator). Rademacher with Gaussian constants (Achlioptas).** For rows whose
directional proxy is `1` and `E ⟨Xᵢ,x⟩⁴ ≤ 3`, the JL tail is `2 exp (-k (ε²/4 - ε³/6))`, S2's: the upper
half from `HasSubgaussianMGF.integral_exp_mul_sq_le` (`E exp (θ Y²) ≤ (1 - 2θ)^{-1/2}`) and S2's
arithmetic; the lower half from `exp (-θ y²) ≤ 1 - θ y² + θ² y⁴/2` at `θ = ε/(2(1 + ε))` (checked on
`(0, 1)`). Rademacher has `E ⟨ξ,x⟩⁴ = 3‖x‖⁴ - 2 ∑ xⱼ⁴`. Exponent 16 times §3.3's at small `ε`; reuses
`jlDim`. Cost about 180 lines (a rows theorem named by its hypothesis, `…_of_integral_pow_four_le`,
rule 4). *Recommendation: now*, so `hasJLProperty_of_hasLaw_rademacherMatrix` and the Rademacher OSE
carry the better bound from the start; later, rule 6 would deprecate the Bernstein instance. Default
if no answer: §3.3 as written. Achlioptas 2003 is not in hand (brief §7.2).

**Q7.** Sizes and the constant are `irreducible_def`s; sizes are stated through the constant's name,
so an improvement of the constant changes no size statement. **Q8.** Two small skeleton files amend
the brief's file list (§4). **Q9.** `9 ^ (card p * finrank ℝ 𝕜)` in §3.1 is `9 ^ card p` over `ℝ` and
`81 ^ card p` over `ℂ` (real dimension of the net).

## 8. Amendments from the review (2026-10-15)

Fable review of this note, all findings accepted by the orchestrator; Q6 decided **yes**
(Rademacher with Gaussian constants this round), as changed by items 1 to 3. The review verified
every cited name, the citations, the arithmetic of `1/64`, `16 c²`, the Rademacher variance, the
net factor `9^(card p · finrank ℝ 𝕜)` with its factor `2`, the OSE at `ε/2` and the sizes
(`4 · 64 · log 9 ≈ 562.5 ≤ 576`), and confirmed Q1 (the R3-rows route is dominated by JL plus a
net in every regime: dropped by rule 6, D12's last sentence amended in `docs/PORT_SKETCHING.md`).
Where an item below contradicts §0 to §7, it supersedes them. Skeletons: the files of item 7,
every proof `sorry`.

1. **§3, `ε ≥ 1`: the lower JL event is not null.** For signs `S x = 0` has probability `2^{-k}`
   (`x = (1, 1)/√2`), so "`ε ≥ 1`: the lower JL event is null" is false at `ε = 1`; it is empty
   only for `ε > 1`. The Dasgupta–Gupta proof must cover `ε = 1` (lower Chernoff at `θ = 1/4`:
   `(27/32)^k ≤ exp (-k/12)`). *Skeleton*: the module docstrings of `SubGaussian.lean` and
   `Rademacher.lean` state the corrected degenerate case; the generic tail's docstring (item 2)
   says its lower half covers `ε = 1`.
2. **Q6 route (Achlioptas).** Upper half: `HasSubgaussianMGF ⟨ξ, x⟩ 1`
   (`isSubgaussianVector_of_hasLaw_rademacherVector`) and `integral_exp_mul_sq_le` give
   `E exp (θ Y²) ≤ (1 - 2θ)^{-1/2}`, then S2's arithmetic. Lower half: the fourth moment,
   `E exp (-θ Y²) ≤ 1 - θ + 3θ²/2`, and
   `θ (1 - ε) + log (1 - θ + 3θ²/2) ≤ -(ε²/4 - ε³/6)` at `θ = ε/(2(1 + ε))` on `(0, 1]` (margin
   about `ε³/48` at small `ε`; on a grid it is at least `0.0176 ε³` on `(0, 1]`, so the review's
   `0.0208 ε³` holds only near `0`, the inequality itself holds). `1 + v ≤ exp v` is too weak; the
   second-order log term comes from `log (1 + u) ≤ u - u²/2 + u³/3` for `-1 < u ≤ 0`, new (S2 has
   only the `u ≥ 0` version, the private `log_one_add_le_cubic` of `ChiSquareTails.lean`, shared at
   the wrap-up). One generic theorem carries the probability, then a rows theorem and the
   Rademacher instance (`E ⟨ξ, x⟩⁴ = Var (⟨ξ, x⟩²) + ‖x‖⁴` from
   `variance_quadForm_of_hasLaw_rademacherVector` at `vecMulVec x x`). *Skeleton*:
   - `Real.log_one_add_le_cubic_of_nonpos (h1 : -1 < u) (h0 : u ≤ 0)`, in the new
     `NLAlib/ForMathlib/Analysis/SpecialFunctions/Log/Deriv.lean` (upstream candidate for
     `Mathlib.Analysis.SpecialFunctions.Log.Deriv`); at the wrap-up it and the private `u ≥ 0`
     lemma become one public statement for `-1 < u`.
   - `measureReal_abs_sum_sq_div_card_sub_one_ge_le_of_iIndepFun (hind : iIndepFun Y μ)
     (hsub : ∀ i, HasSubgaussianMGF (Y i) 1 μ) (h2 : ∀ i, ∫ Y i ^ 2 = 1) (h4 : ∀ i, ∫ Y i ^ 4 ≤ 3)
     (hε : 0 ≤ ε)`: `P(ε ≤ |(∑ Yᵢ²)/card ι - 1|) ≤ 2 exp (-card ι (ε²/4 - ε³/6))`, in the new
     `NLAlib/Probability/SubGaussian/SquareSum.lean` (merges into `Square.lean` at the wrap-up).
     It dominates S2's `χ²` relative deviation (same bound, weaker hypotheses), which can then be
     reproved from it and keep its name (rule 6).
   - `hasJLProperty_of_isSubgaussianVector_of_integral_pow_four_le (hind) (hsub : … 1 μ) (hiso)
     (h4 : ∀ i x, ∫ (x ⬝ᵥ X ω i) ^ 4 ≤ 3 ‖x‖⁴) (hε : 0 ≤ ε)`, failure
     `2 exp (-k (ε²/4 - ε³/6))`, in `SubGaussian.lean` (the rows theorem, named by its extra
     hypothesis, rule 4).
3. **Q6 makes the Bernstein sign JL not dominated** (at `c = 1`, `min (ε², ε)/64` beats
   `ε²/4 - ε³/6` for `ε ≳ 1.43`). No Bernstein Rademacher instance is named (it is the rows theorem
   at `c = 1` with `isSubgaussianVector_of_hasLaw_rademacherVector`); the docstrings of both say in
   which regime each is better. §7 Q6's "later, rule 6 would deprecate the Bernstein instance" is
   dropped. *Skeleton*: `hasJLProperty_of_hasLaw_rademacherMatrix (hX) (hε : 0 ≤ ε)` with
   `2 exp (-k (ε²/4 - ε³/6))`; the Rademacher OSE and OSI with `hε : 0 ≤ ε` and failure
   `2 · 9^d exp (-k (ε²/16 - ε³/48))` (§3.1 at `ε/2`). Sizes are S2's `jlDim`: since §6's reason for
   cutting the Rademacher size twins (rows corollaries at `c = 1`) no longer holds, three are
   stated, `hasJLProperty_of_hasLaw_rademacherMatrix_of_jlDim_le` (`0 < ε < 3/2`, `jlDim ε δ`) and
   the OSE and OSI `…_of_jlDim_le` (`0 < ε < 3`, `jlDim (ε/2) (δ/9^d)`).
4. **Citation.** The sign JL cites "[Woodruff2014, §2.1, after Theorem 6]; constants of
   [Achlioptas2003, Theorem 1.1], locator to confirm (`docs/PORT_SKETCHING.md` §7.2)".
   `Achlioptas2003` is added to `docs/references.bib` (§4's "cited by name only" is withdrawn).
5. **Optional, not taken.** `subgaussianJLDim` could absorb `hεc` through
   `log (2/δ)/(C min (ε²/c², ε/c))`; the current form is honest and stays.
6. **§3.1 proof** starts with a case split on `IsEmpty p` (the net may be empty, `specNorm E = 0`,
   every sketch is an embedding); recorded in the module docstring of
   `JohnsonLindenstraussNet.lean`.
7. **Files** (amends §4, under §8 of CONTRIBUTING). The Rademacher block moves out of
   `SubGaussian.lean` into its own topic file, since with Q6 it has its own route and sizes and
   the combined file would hold 32 statements:
   1. `NLAlib/ForMathlib/Analysis/SpecialFunctions/Log/Deriv.lean` (1), new.
   2. `NLAlib/Probability/SubGaussian/SquareSum.lean` (1), new; imports 1 and `Square.lean`.
   3. `NLAlib/Probability/IndependentRows.lean` (1), as §3.2.
   4. `NLAlib/Sketching/Properties/JohnsonLindenstraussNet.lean` (2), as §3.1.
   5. `NLAlib/Sketching/Gaussian/SubGaussian.lean` (20: 3 definitions, 8 constant and size
      lemmas, 9 theorems), §3.3 without its Rademacher block, plus item 2's rows theorem; imports
      2, 3, 4, R3, `Properties/Isotropic`.
   6. `NLAlib/Sketching/Gaussian/Rademacher.lean` (12: `rademacherMatrix`, its instance, isotropy,
      JL, the integrable and exact second moment, the JL moment, OSE, OSI, three sizes); imports 5,
      S2's `Gaussian.lean` (`jlDim`), `Distributions/Rademacher`, `QuadraticForm/Moments`.
8. §7: Q1 to Q5 and Q7 to Q9 stand; Q6 is decided yes as above.

**Skeleton-level changes** (same meaning): `iIndepFun_row_of_iIndepFun_entry` takes
`[Finite m] [Finite n]` (the `unusedFintypeInType` linter); the size definitions take a real `c`,
the rows theorems the proxy `c : ℝ≥0`, coerced; result ids `jl-subgaussian` (the three
sub-Gaussian JL tails), `subgaussian-ose`, `rademacher-ose`, and the new `jl-rademacher` (the sign
JL).
