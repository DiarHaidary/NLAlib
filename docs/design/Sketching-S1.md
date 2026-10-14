# Design note: Sketching stage S1, the probabilistic predicates

Status: drafted 2026-10-14 under `docs/PORT_SKETCHING.md` (D2 (i), (α), (A); the OSI addition; D7).
Eight predicates on a random `S : Ω → Matrix k n 𝕜` (law form `HasLaw.id`), their `HasLaw` lemmas and
consequences. No question of the brief's §2 kind (§7). No Matrix- or Probability-layer additions.

## 0. Scope and consumers

| Item | Consumers |
|---|---|
| `IsIsotropicSketch` | the OSI; the two CEMT tails; S2 (Haar, exact), S3 (rows), S4 (`p i > 0`), S6 |
| `HasSubspaceInjection`, `HasSubspaceEmbedding` (fixed `U`) | S4 (leverage sampling); Solvers (`U = [A, y]`); every family, through the oblivious constructors |
| `IsObliviousSubspaceEmbedding`, `IsObliviousSubspaceInjection`, transfer, composition | concluded by S2, S3, S6, S7; LowRank R1, R2, R5, R6 and HMT §11 (generalized Nyström sketches twice); Solvers |
| `HasJLProperty`, `HasJLMoment`, JL lemma, AMM; `HasGramTraceMoment` | S2, S3, S7 (`p = 2`, `q = 1`); Estimation (Hutch++, XTrace); deferred sparse families (§4a, general `q`) |
| CEMT Lemma 2.1 and sketch-and-solve, tail form | LowRank (CEMT Theorem 2.2, Corollaries 2.5, 2.8); Solvers (Theorem 2.7) |

## 1. Objects

New §5.3 rows, one per predicate of §2, bridged by its `HasLaw.…_iff`. Used directly: Mathlib's
`HasLaw`, `IndepFun`, `MemLp`, `μ.real`; P0's `Matrix.integral_quadForm`, `IsIsotropic`, Markov
(`measureReal_ge_le_integral_div`, `measureReal_abs_ge_le_integral_rpow_div`); the Matrix layer's
`specNorm_pow_le_re_trace_pow`, `exists_hasOrthonormalCols_range_le`; S0. No deviation from Mathlib.

## 2. Interfaces

`open MeasureTheory ProbabilityTheory`, `open scoped Matrix MatrixOrder Matrix.Norms.L2Operator`.

```lean
/-- **Isotropic sketch**: `E [Sᴴ S] = 1`. [CamanoEpperlyMeyerTropp2025, Definition 1.2 (1.2)]. -/
structure IsIsotropicSketch [DecidableEq n] (S : Ω → Matrix k n 𝕜) (μ : Measure Ω) : Prop where
  memLp : ∀ i j, MemLp (fun ω => S ω i j) 2 μ
  integral_conjTranspose_mul_self : ∫ ω, (S ω)ᴴ * S ω ∂μ = 1
def HasSubspaceInjection (S : Ω → Matrix k n 𝕜) (U : Matrix n p 𝕜) (a δ : ℝ) (μ : Measure Ω) : Prop :=
  μ.real {ω | ¬ IsSubspaceInjection (S ω) U a} ≤ δ
def HasSubspaceEmbedding (S : Ω → Matrix k n 𝕜) (U : Matrix n p 𝕜) (a b δ : ℝ) (μ : Measure Ω) : Prop :=
  μ.real {ω | ¬ IsSubspaceEmbedding (S ω) U a b} ≤ δ
/-- **OSE**, D2 (α). [Woodruff2014, Definition 2]; [CamanoEpperlyMeyerTropp2025, Definition 1.1]. Result: ose-def -/
def IsObliviousSubspaceEmbedding (S : Ω → Matrix k n 𝕜) (d : ℕ) (a b δ : ℝ) (μ : Measure Ω) : Prop :=
  ∀ U : Matrix n n 𝕜, U.rank ≤ d → HasSubspaceEmbedding S U a b δ μ
/-- **OSI** [CamanoEpperlyMeyerTropp2025, Definition 1.2]; there `19/20`, `α ∈ (0, 1]`. Result: osi-def -/
structure IsObliviousSubspaceInjection [DecidableEq n] (S : Ω → Matrix k n 𝕜) (d : ℕ) (a δ : ℝ) (μ : Measure Ω) : Prop where
  isotropic : IsIsotropicSketch S μ
  injection : ∀ U : Matrix n n 𝕜, U.rank ≤ d → HasSubspaceInjection S U a δ μ
/-- **Distributional JL**, on unit vectors. [Woodruff2014, Theorem 4] (Gaussian). -/
def HasJLProperty (S : Ω → Matrix k n 𝕜) (ε δ : ℝ) (μ : Measure Ω) : Prop :=
  ∀ x : n → 𝕜, ‖WithLp.toLp 2 x‖ = 1 → μ.real {ω | ε ≤ |‖WithLp.toLp 2 (S ω *ᵥ x)‖ ^ 2 - 1|} ≤ δ
/-- **JL moment property**, `p : ℝ`; junk for `ε < 0`. [Woodruff2014, Definition 12]. -/
structure HasJLMoment (S : Ω → Matrix k n 𝕜) (ε δ p : ℝ) (μ : Measure Ω) : Prop where
  integrable : ∀ x : n → 𝕜, ‖WithLp.toLp 2 x‖ = 1 →
    Integrable (fun ω => |‖WithLp.toLp 2 (S ω *ᵥ x)‖ ^ 2 - 1| ^ p) μ
  integral_le : ∀ x : n → 𝕜, ‖WithLp.toLp 2 x‖ = 1 →
    ∫ ω, |‖WithLp.toLp 2 (S ω *ᵥ x)‖ ^ 2 - 1| ^ p ∂μ ≤ ε ^ p * δ
/-- `E re tr E^{2q} ≤ B` for the Gram error `E = (S U)ᴴ (S U) - 1` (used for orthonormal `U`). -/
structure HasGramTraceMoment [DecidableEq p] (S : Ω → Matrix k n 𝕜) (U : Matrix n p 𝕜) (q : ℕ)
    (B : ℝ) (μ : Measure Ω) : Prop where
  integrable : Integrable (fun ω => RCLike.re (((S ω * U)ᴴ * (S ω * U) - 1) ^ (2 * q)).trace) μ
  integral_le : ∫ ω, RCLike.re (((S ω * U)ᴴ * (S ω * U) - 1) ^ (2 * q)).trace ∂μ ≤ B
```
Constructors are the definitions; each `HasLaw.…_iff (hS : HasLaw S ν μ) : P S … μ ↔ P id … ν` (S0's sets).

## 3. Statement shapes

Variables `{Ω} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜} [RCLike 𝕜] {k l n p q r : Type*}`,
`[Fintype _]`, `[DecidableEq _]` where `1` appears, `{S : Ω → Matrix k n 𝕜} {U : Matrix n p 𝕜}
{a b δ δ' ε t B : ℝ} {d : ℕ} {ν : Measure (Matrix k n 𝕜)}`; `[IsFiniteMeasure μ]` on theorems that
compare two events, `[IsProbabilityMeasure μ]` on independence statements. Twins are `…`. In §3.5
and §3.6 `p : ℝ` is the moment exponent (D2's name) and no column type `p` occurs.

Degenerate cases. `δ < 0`: tail predicates fail unless vacuous (empty `n`), so non-vacuous conclusions
take `0 ≤ δ` (JL lemma, JL moment to embedding). `card k = 0` or `S = 0`: not isotropic (nonempty `n`);
JL forces `1 ≤ δ`. `d = 0`: only `U = 0`. `a ≤ 0`: injection vacuous, isotropy not. `ε = 0`: JL events
are everything (`0 < ε`). `q = 0`: `card p · μ univ ≤ B`, consequences still true. `p i = 0` (S4):
fixed-`U` predicates need no isotropy. `B Zᴴ = 0`, `r = 0`: §7 Q1. `t ≤ 0`, `p ≤ 0`: excluded.

### 3.1 `Sketching/Properties/Isotropic.lean` (10)

```lean
theorem isIsotropicSketch_iff : IsIsotropicSketch S μ ↔ (∀ i j, MemLp (fun ω => S ω i j) 2 μ) ∧
    ∀ x : n → 𝕜, ∫ ω, ‖WithLp.toLp 2 (S ω *ᵥ x)‖ ^ 2 ∂μ = ‖WithLp.toLp 2 x‖ ^ 2
theorem IsIsotropicSketch.integral_norm_mulVec_sq (h : IsIsotropicSketch S μ) (x : n → 𝕜) :
    ∫ ω, ‖WithLp.toLp 2 (S ω *ᵥ x)‖ ^ 2 ∂μ = ‖WithLp.toLp 2 x‖ ^ 2      -- + integrable_…
theorem IsIsotropicSketch.integral_frobNorm_mul_sq (h) (M : Matrix n p 𝕜) :
    ∫ ω, frobNorm (S ω * M) ^ 2 ∂μ = frobNorm M ^ 2                      -- + integrable_…
theorem IsIsotropicSketch.integral_conjTranspose_mul_mul (h) (U : Matrix n p 𝕜) :
    ∫ ω, (S ω * U)ᴴ * (S ω * U) ∂μ = Uᴴ * U
/-- Isotropic rows, scaled; no independence; `[Nonempty k]` (else `S = 0`). -/
theorem isIsotropicSketch_smul_of_isIsotropic [Nonempty k] {X : Ω → Matrix k n 𝕜}
    (hX : ∀ i, IsIsotropic (fun ω => X ω i) μ) :
    IsIsotropicSketch (fun ω => ((√(Fintype.card k : ℝ))⁻¹ : ℝ) • X ω) μ
theorem IsIsotropicSketch.mul [IsProbabilityMeasure μ] [DecidableEq k] {S₂ : Ω → Matrix l k 𝕜}
    (h₂ : IsIsotropicSketch S₂ μ) (h : IsIsotropicSketch S μ) (hind : IndepFun S₂ S μ) :
    IsIsotropicSketch (fun ω => S₂ ω * S ω) μ
-- HasLaw.isIsotropicSketch_iff. Proofs: `Matrix.integral_quadForm`, `IsHermitian.ext_quadForm`; Fubini.
```

### 3.2 `Sketching/Properties/FixedSubspace.lean` (12)

```lean
-- HasSubspaceInjection, HasSubspaceEmbedding (§2); HasLaw.hasSubspaceInjection_iff, …Embedding_iff
theorem HasSubspaceEmbedding.hasSubspaceInjection (h : HasSubspaceEmbedding S U a b δ μ) : HasSubspaceInjection S U a δ μ
theorem HasSubspaceInjection.hasSubspaceEmbedding (h : HasSubspaceInjection S U a δ μ)
    (hb : μ.real {ω | ¬ (S ω * U)ᴴ * (S ω * U) ≤ b • (Uᴴ * U)} ≤ δ') :
    HasSubspaceEmbedding S U a b (δ + δ') μ
-- from a Gram-error tail (matrix Chernoff; S4, S6), resp. a `σ_min` tail (R3, Chernoff's lower tail)
theorem HasOrthonormalCols.hasSubspaceEmbedding_of_measureReal_le (hU : HasOrthonormalCols U)
    (h : μ.real {ω | ε ≤ specNorm ((S ω * U)ᴴ * (S ω * U) - 1)} ≤ δ) :
    HasSubspaceEmbedding S U (1 - ε) (1 + ε) δ μ
theorem HasOrthonormalCols.hasSubspaceInjection_of_measureReal_le (hU : HasOrthonormalCols U)
    {j : ℕ} (hj : j + 1 = Fintype.card p) (h : μ.real {ω | singularValues (S ω * U) j ^ 2 ≤ a} ≤ δ) :
    HasSubspaceInjection S U a δ μ
theorem HasSubspaceInjection.mono (h : HasSubspaceInjection S U a δ μ) (ha : a' ≤ a) (hδ : δ ≤ δ') :
    HasSubspaceInjection S U a' δ' μ
theorem HasSubspaceInjection.of_range_le (h : HasSubspaceInjection S U a δ μ) {V : Matrix n q 𝕜}
    (hVU : LinearMap.range V.mulVecLin ≤ LinearMap.range U.mulVecLin) : HasSubspaceInjection S V a δ μ
-- + HasSubspaceEmbedding.mono, HasSubspaceEmbedding.of_range_le
```

### 3.3 `Sketching/Properties/Oblivious.lean` (15)

```lean
-- IsObliviousSubspaceEmbedding, IsObliviousSubspaceInjection (§2); their HasLaw.…_iff (2)
theorem IsObliviousSubspaceEmbedding.hasSubspaceEmbedding (h : IsObliviousSubspaceEmbedding S d a b δ μ)
    {U : Matrix n p 𝕜} (hU : U.rank ≤ d) : HasSubspaceEmbedding S U a b δ μ   -- + Injection twin
-- the constructor families use (§7 Q4)
theorem IsObliviousSubspaceEmbedding.of_hasOrthonormalCols (hp : Fintype.card p ≤ Fintype.card n)
    (h : ∀ U : Matrix n p 𝕜, HasOrthonormalCols U → HasSubspaceEmbedding S U a b δ μ) :
    IsObliviousSubspaceEmbedding S (Fintype.card p) a b δ μ      -- + Injection twin, with `hiso`
theorem IsObliviousSubspaceEmbedding.isObliviousSubspaceInjection (h : IsObliviousSubspaceEmbedding S d a b δ μ)
    (hiso : IsIsotropicSketch S μ) : IsObliviousSubspaceInjection S d a δ μ
theorem IsObliviousSubspaceEmbedding.mono (h : IsObliviousSubspaceEmbedding S d a b δ μ) (hd : d' ≤ d)
    (ha : a' ≤ a) (hb : b ≤ b') (hδ : δ ≤ δ') : IsObliviousSubspaceEmbedding S d' a' b' δ' μ  -- + twin
-- transfer to an independent random subspace (Fubini on S0's closed set)
theorem IsObliviousSubspaceEmbedding.measure_not_isSubspaceEmbedding_le_of_indepFun
    [IsProbabilityMeasure μ] (h : IsObliviousSubspaceEmbedding S d a b δ μ) {V : Ω → Matrix n q 𝕜}
    (hind : IndepFun S V μ) (hS : AEMeasurable S μ) (hV : AEMeasurable V μ)
    (hrank : ∀ᵐ ω ∂μ, (V ω).rank ≤ d) :
    μ.real {ω | ¬ IsSubspaceEmbedding (S ω) (V ω) a b} ≤ δ                  -- + Injection twin
theorem IsObliviousSubspaceEmbedding.mul [IsProbabilityMeasure μ] {S₂ : Ω → Matrix l k 𝕜}
    (h₂ : IsObliviousSubspaceEmbedding S₂ d a₂ b₂ δ₂ μ) (h : IsObliviousSubspaceEmbedding S d a b δ μ)
    (hind : IndepFun S₂ S μ) (hS₂ : AEMeasurable S₂ μ) (hS : AEMeasurable S μ) (ha₂ : 0 ≤ a₂) (hb₂ : 0 ≤ b₂) :
    IsObliviousSubspaceEmbedding (fun ω => S₂ ω * S ω) d (a₂ * a) (b₂ * b) (δ₂ + δ) μ  -- + twin (`ha₂`)
```

### 3.4 `Sketching/Properties/Injection.lean` (6)

`Q : Matrix n p 𝕜`, `Z : Matrix n r 𝕜`, `B : Matrix l r 𝕜`, `A : Matrix n q 𝕜`, `y : n → 𝕜`, `Y : Matrix n r 𝕜`, `ha : 0 < a`, `ht : 0 < t`.

```lean
/-- **OSIs respect orthogonality** [CamanoEpperlyMeyerTropp2025, Lemma 2.1]; there `Qᴴ Q⊥ = 0` (unused), `t = 20`. -/
theorem HasSubspaceInjection.measure_frobNorm_mul_pinv_sq_gt_le (h : HasSubspaceInjection S Q a δ μ)
    (hiso : IsIsotropicSketch S μ) (hQ : HasOrthonormalCols Q) (ha) (ht) (B) (Z) :
    μ.real {ω | t * frobNorm (B * Zᴴ) ^ 2 / a <
      frobNorm (B * (S ω * Z)ᴴ * pinv ((S ω * Q)ᴴ)) ^ 2} ≤ δ + 1 / t
-- + IsObliviousSubspaceInjection twin in CEMT's form: (hpd : card p ≤ d) (hZ : HasOrthonormalCols Z), `frobNorm B`
/-- **Sketch-and-solve with an OSI** [CamanoEpperlyMeyerTropp2025, Theorem 2.7]. Result: sketch-and-solve-ls -/
theorem HasSubspaceInjection.measure_norm_sub_mulVec_sq_gt_le (h : HasSubspaceInjection S A a δ μ)
    (hiso : IsIsotropicSketch S μ) (ha) (ht) (y) {x : Ω → q → 𝕜}
    (hx : ∀ᵐ ω ∂μ, IsLeastSquaresSolution (S ω * A) (S ω *ᵥ y) (x ω)) :
    μ.real {ω | (1 + t / a) * ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2 <
      ‖WithLp.toLp 2 (y - A *ᵥ x ω)‖ ^ 2} ≤ δ + 1 / t
theorem HasSubspaceInjection.measure_frobNorm_sub_mul_pinv_mul_sq_gt_le (h) (hiso) (ha) (ht) (Y) :
    μ.real {ω | (1 + t / a) * frobNorm ((1 - rangeProjector A) * Y) ^ 2 <
      frobNorm (Y - A * (pinv (S ω * A) * (S ω * Y))) ^ 2} ≤ δ + 1 / t
-- IsObliviousSubspaceInjection twins of both, with `hA : A.rank ≤ d`
```

Proofs: the event lies in `{¬ injection} ∪ {t ‖M‖_F² < ‖S M‖_F²}` by S0; the second set is empty for
`M = 0` and has measure `≤ 1 / t` otherwise (Markov, `integral_frobNorm_mul_sq`).

### 3.5 `Sketching/Properties/JohnsonLindenstrauss.lean` (11)

```lean
-- HasJLProperty, HasJLMoment (§2); HasLaw.hasJLProperty_iff, HasLaw.hasJLMoment_iff
theorem HasJLProperty.mono (h : HasJLProperty S ε δ μ) (hε : ε ≤ ε') (hδ : δ ≤ δ') : HasJLProperty S ε' δ' μ
theorem HasJLMoment.mono (h : HasJLMoment S ε δ p μ) (hε : ε ≤ ε') (hδ : δ ≤ δ') (hε0 : 0 ≤ ε)
    (hp : 0 ≤ p) (hδ0 : 0 ≤ δ) : HasJLMoment S ε' δ' p μ
theorem HasJLProperty.measure_abs_norm_mulVec_sq_sub_ge_le (h : HasJLProperty S ε δ μ) {x : n → 𝕜}
    (hx : x ≠ 0) : μ.real {ω | ε * ‖WithLp.toLp 2 x‖ ^ 2 ≤
      |‖WithLp.toLp 2 (S ω *ᵥ x)‖ ^ 2 - ‖WithLp.toLp 2 x‖ ^ 2|} ≤ δ
/-- **Johnson–Lindenstrauss lemma**, union over unordered pairs [Woodruff2014, Definition 3]. Result: jl-lemma -/
theorem HasJLProperty.measure_exists_abs_norm_mulVec_sq_sub_ge_le (h : HasJLProperty S ε δ μ)
    (hδ : 0 ≤ δ) {ι : Type*} [Fintype ι] (x : ι → n → 𝕜) :
    μ.real {ω | ∃ i j, x i ≠ x j ∧ ε * ‖WithLp.toLp 2 (x i - x j)‖ ^ 2 ≤
      |‖WithLp.toLp 2 (S ω *ᵥ (x i - x j))‖ ^ 2 - ‖WithLp.toLp 2 (x i - x j)‖ ^ 2|} ≤
      (Fintype.card ι).choose 2 * δ
theorem HasJLMoment.hasJLProperty (h : HasJLMoment S ε δ p μ) (hε : 0 < ε) (hp : 0 < p) : HasJLProperty S ε δ μ
theorem HasJLMoment.integral_abs_norm_mulVec_sq_sub_rpow_le (h) (hp : 0 < p) (x : n → 𝕜) :
    ∫ ω, |‖WithLp.toLp 2 (S ω *ᵥ x)‖ ^ 2 - ‖WithLp.toLp 2 x‖ ^ 2| ^ p ∂μ ≤
      ε ^ p * δ * ‖WithLp.toLp 2 x‖ ^ (2 * p)                              -- + integrable_…
```

### 3.6 `Sketching/Properties/MatrixMultiplication.lean` (5; over ℝ, §7 Q2)

`{S : Ω → Matrix k n ℝ}`, `A : Matrix n q ℝ`, `B : Matrix n r ℝ`, `(hp : 2 ≤ p) (hS : AEMeasurable S μ)`.

```lean
/-- **AMM from the JL moment** [Woodruff2014, Theorem 13]; there `3 ε`, here `ε` (§7 Q2). Result: amm-ose -/
theorem HasJLMoment.integral_frobNorm_conjTranspose_mul_sub_rpow_le (h : HasJLMoment S ε δ p μ)
    (hε : 0 ≤ ε) (hp) (hS) (A) (B) :
    ∫ ω, frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B) ^ p ∂μ ≤ (ε * frobNorm A * frobNorm B) ^ p * δ  -- + integrable_…
theorem HasJLMoment.measure_frobNorm_conjTranspose_mul_sub_ge_le (h) (hε : 0 < ε) (hp) (hS) (hA : A ≠ 0) (hB : B ≠ 0) :
    μ.real {ω | ε * frobNorm A * frobNorm B ≤ frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B)} ≤ δ
theorem HasJLMoment.hasSubspaceEmbedding [DecidableEq q] (h) (hε : 0 < ε) (hp) (hS) (hδ : 0 ≤ δ) {U : Matrix n q ℝ}
    (hU : HasOrthonormalCols U) : HasSubspaceEmbedding S U (1 - ε * Fintype.card q) (1 + ε * Fintype.card q) δ μ
theorem HasJLMoment.isObliviousSubspaceEmbedding (h) (hε : 0 < ε) (hp) (hS) (hδ : 0 ≤ δ) (d : ℕ) :
    IsObliviousSubspaceEmbedding S d (1 - ε * d) (1 + ε * d) δ μ
```

### 3.7 `Sketching/Properties/TraceMoment.lean` (6)

```lean
-- HasGramTraceMoment (§2); HasLaw.hasGramTraceMoment_iff; HasGramTraceMoment.mono (in `B`)
/-- **Trace-moment Markov step**, `‖E‖^{2q} ≤ re tr E^{2q}` [Woodruff2014, proof of Theorem 9]. -/
theorem HasGramTraceMoment.measure_specNorm_ge_le (h : HasGramTraceMoment S U q B μ) (hε : 0 < ε) :
    μ.real {ω | ε ≤ specNorm ((S ω * U)ᴴ * (S ω * U) - 1)} ≤ B / ε ^ (2 * q)
theorem HasGramTraceMoment.hasSubspaceEmbedding (h) (hU : HasOrthonormalCols U) (hε : 0 < ε) : HasSubspaceEmbedding S U (1 - ε) (1 + ε) (B / ε ^ (2 * q)) μ
theorem isObliviousSubspaceEmbedding_of_hasGramTraceMoment (hp : Fintype.card p ≤ Fintype.card n)
    (h : ∀ U : Matrix n p 𝕜, HasOrthonormalCols U → HasGramTraceMoment S U q B μ) (hε : 0 < ε) :
    IsObliviousSubspaceEmbedding S (Fintype.card p) (1 - ε) (1 + ε) (B / ε ^ (2 * q)) μ
```

## 4. Files

In `Sketching/Properties/`, 65 statements, about 1000 lines, in order (imports): `Isotropic` (10; P0),
`FixedSubspace` (12; S0), `Oblivious` (15; both), `Injection` (6; S0 `LeastSquares`, P0 `Tail`),
`JohnsonLindenstrauss` (11; P0 `Tail`, independent of the first four), `MatrixMultiplication` (5),
`TraceMoment` (6; `Matrix/Norms/SchattenPowers`); the last three are independent of each other.

## 5. Material

Read: `Properties/JL/JL.lean`, `Properties/ApproxMatrixMultiplication/ApproxMultiplication.lean`,
`Sparse/MomentMethod/GramTail.lean`; CEMT §1.1, §2.1, §2.4; Woodruff §2.1, §2.2. Ledger: `jl_lemma` → the
JL lemma (`choose 2`, not `N²`); the other six JL declarations → S2 (Gaussian tails, sizes); the four AMM
declarations → §3.6 (Bochner, `p ≥ 2`; polarization as proof material);
`FiniteLaw.prob_le_norm_le_expect_trace_pow_div` → `measure_specNorm_ge_le`; the three `sparseStack_…`
tails → deferred (D6). No material for the OSI.

## 6. Cut, and why

Success, `∫⁻` and `ENNReal.ofReal` forms, `Fin` sizes (brief §3, D5); an AMM predicate (D2); a
`HasJLTail` name (the brief's `HasJLProperty`); AMM over `𝕜` (§7 Q2); trace moments of non-orthonormal `U`.

## 7. Questions and decisions

**For the maintainer:** none of the brief's §2 kind. **Decisions taken** (open to correction):

**Q1. The CEMT tails' events negate the guarantee** (`c < X` for `X ≤ c`), as `HasSubspaceEmbedding`
does: `B Zᴴ = 0`, `r = 0` need no hypothesis. Thresholds (`t ≤ X`) stay non-strict. Proposed for brief
§3: "a guarantee `X ≤ c` fails on `{c < X}`".

**Q2. AMM over ℝ only this round, constant `ε`.** Every JL-moment family this round is real (D3). Over
ℂ the hypothesis gives only `√2 ε`, sharply (`Sᴴ S - 1 = c (ξ₁ σx + ξ₂ σy)`, Rademacher `ξ`, `c ≤ 1/√2`:
`E (x*Ex)² ≤ c² ‖x‖⁴`, `E |e₁* E e₂|² = 2 c²`); the `𝕜` form with `√2 ε` comes with the complex laws. `1` beats
Woodruff's `3` and is optimal (deterministic `S`), so it is written, not named as D12 would have it:
rule 2's purpose (improve without a rename) cannot arise.

**Q3. `HasJLMoment` takes `p : ℝ`** (`rpow`, as the Markov lemma). AMM's proof: polarization by
`a ± b` and Minkowski in `L^{p/2}` (`eLpNorm_sum_le`); over budget, it goes to the scaffold, unweakened.

**Q4. Oblivious constructors quantify over orthonormal `U : Matrix n p 𝕜`**, `d = card p ≤ card n`;
the predicate keeps (α), bridged by `exists_hasOrthonormalCols_range_le`, with no `Fin`.

**Q5.** `FixedSubspace.lean` is split from `Oblivious.lean` (27 statements together; amends the brief's
file list). **Q6.** `.toInjection` is named `…isObliviousSubspaceInjection` (§4). **Q7.** Transfer and
composition take `AEMeasurable` sketches (`HasLaw` gives them). **Q8.** New result id `osi-def`.

## 8. Amendments from the review (2026-10-14)

Review of S0 and S1 (2026-10-14); all findings and the author decisions of §7 accepted by the
orchestrator. Skeletons in `NLAlib/Sketching/Properties/`: `Isotropic` (10), `FixedSubspace` (12),
`Oblivious` (15), `Injection` (6), `JohnsonLindenstrauss` (11), `MatrixMultiplication` (5),
`TraceMoment` (6); 65 statements, every proof `sorry`.

1. **JL citations.** `HasJLProperty` cites [Woodruff2014, proof of Lemma 18] and
   [MartinssonTropp2020, §8.6] (Theorem 4 is the `f`-point JLT). The JL lemma cites
   [Woodruff2014, Definition 3] with "there inner products on a finite set, here squared norms of
   differences".
2. **`[IsFiniteMeasure μ]` explicit** (`measureReal_mono` needs the larger set finite; `μ.real` of a
   set of infinite measure is `0`). On the listed `HasOrthonormalCols.hasSubspaceEmbedding_of_measureReal_le`,
   `HasJLProperty.mono`, the six tails of `Injection`,
   `HasGramTraceMoment.measure_specNorm_ge_le`; and, by §3's rule, on every other theorem that
   compares two different events: `HasSubspaceEmbedding.hasSubspaceInjection` (false without it:
   Lebesgue on `ℝ`, `S = 0` on `[0, 1]` and `2 • 1` elsewhere, `a = b = 1`, `δ = 0`),
   `HasOrthonormalCols.hasSubspaceInjection_of_measureReal_le`, the four `mono`/`of_range_le` of
   `FixedSubspace`, the two oblivious constructors, `isObliviousSubspaceInjection`, the two
   oblivious `mono`, `HasGramTraceMoment.hasSubspaceEmbedding` and
   `isObliviousSubspaceEmbedding_of_hasGramTraceMoment`. Not on: the `HasLaw` lemmas;
   `HasSubspaceInjection.hasSubspaceEmbedding` (the failure event is the union, `measureReal_union_le`);
   the OSE/OSI-to-any-shape lemmas (the event depends only on the range, so the sets are equal); the
   JL lemma (union bound); `HasJLMoment.hasJLProperty` (Markov); the §3.6 statements (each event is a
   superlevel set of an integrable function at a positive level, or empty).
3. **`measure_specNorm_ge_le` at `q = 0`** keeps `q : ℕ` unrestricted; the route splits on `q = 0`
   (`specNorm_pow_le_re_trace_pow` needs `p ≠ 0`): there `re tr 1 = card p`, so `B ≥ card p · μ.real
   univ`, and for empty `p` the event is empty (`specNorm = 0 < ε`).
4. **JL moment to embeddings.** `HasJLMoment.hasSubspaceEmbedding` and `.isObliviousSubspaceEmbedding`
   (`1 ∓ ε · dim`) cite [Woodruff2014, proof of Theorem 9] (Theorems 13 and 14). The oblivious form
   needs no `d ≤ card n`: the proof uses an orthonormal basis indexed by `Fin (min d (card n))` and
   `mono`.
5. **`IsIsotropicSketch.mul`, `memLp` field**: entries of `S₂ S` are sums of products of independent
   `L²` entries; the route is `IndepFun.comp` with `Matrix.measurable_apply`.
6. **`CamanoEpperlyMeyerTropp2025`** is in `docs/references.bib` (arXiv:2508.21189, title and
   authors from the PDF's first page).

Author decisions adopted: failure events negate the guarantee (`docs/PORT_SKETCHING.md` §3 has the
sentence); AMM over `ℝ` with constant `ε`, the complex counterexample `c (ξ₁ σx + ξ₂ σy)` in the
docstrings, and "Woodruff has 3ε; 1 is optimal"; `p : ℝ` in `HasJLMoment`; oblivious constructors
over orthonormal `U : Matrix n p 𝕜` with `hp : card p ≤ card n`.

Skeleton-level changes, same meaning:

- `IsIsotropicSketch.integral_conjTranspose_mul_mul` takes `[DecidableEq p]`: the integral of a
  `Matrix p p 𝕜`-valued function needs the `L2Operator` normed group, which needs it.
- `integrable_…` companions written out: `IsIsotropicSketch.integrable_norm_mulVec_sq`,
  `.integrable_frobNorm_mul_sq`, `HasJLMoment.integrable_abs_norm_mulVec_sq_sub_rpow` (with
  `hp : 0 < p`: at `p = 0`, `x = 0` the integrand is `1`), and
  `HasJLMoment.integrable_frobNorm_conjTranspose_mul_sub_rpow` (no `hε`).
- The `+ twin` lines are written out: `IsObliviousSubspaceInjection.hasSubspaceInjection`,
  `.of_hasOrthonormalCols` (with `hiso`), `.mono`,
  `.measure_not_isSubspaceInjection_le_of_indepFun`, `.mul` (with `[DecidableEq k]`, `ha₂`), and
  the OSI forms of the three CEMT tails.
- Instance placement as in S0 §8: `[Fintype p]`, `[Fintype q]` on the declarations that use them.
