# Design note: Sketching stage S7, CountSketch

Status: drafted 2026-10-15 under `docs/PORT_SKETCHING.md` (D2, the D3 row "CountSketch", D4, D5, D12,
D14, D15, D16; §3; the S7 entry of §4; §4a); reviewed 2026-10-15, amendments in §8, which overrides
§0 to §7 where they disagree. The last stage of the round:
SparseStack and OSNAP stay deferred (D6, §4a), and the statements they will reuse (the hollow Gram
identity and the exact second moment) are public here. Laws follow S4 §8 item 1 (pushforward of a
public constructor, `letI := ⊤` inside the body, the explicit form a lemma; the sign factor is not
finite, so the explicit form is the pushforward under the user's instances, as S6 §6 decided for the
SRHT). **Missing below Sketching**: one Probability lemma (the collision probability of i.i.d.
indices, §3.1), and S4's private `pi_samplingMeasure_eq_sum` made public in the same file (S7 is its
second user); nothing else. The prototype's `integral_quadForm_sq_rademacherVector_of_diag_zero` is
not needed: P3 cut it as an instance of `integral_norm_quadForm_sub_trace_sq`, which the conditional
step uses directly. One Sketching file, as the brief lists. Q1 is decided as (b), not hard to reverse (§8 item 2).

## 0. Scope and consumers

A hash `h : n → k` and signs `σ : n → ℝ`; the sketch `S = countSketchMatrix h σ : Matrix k n 𝕜` has
column `i` equal to `σ i • e (h i)`, one nonzero per column. The law `countSketch k n` takes `h` with
i.i.d. uniform values and `σ ~ rademacherVector n`, independent. Write `m := card k`,
`H := Sᴴ S - 1`. The whole stage rests on one computation: for signs in `{±1}`, `H` is hollow (zero
diagonal, entry `σ i σ j` where `i ≠ j` collide), so for every `M : Matrix n n 𝕜`
```
E |tr (M H)|² = (‖M‖_F² + ⟨M, Mᵀ⟩_F - 2 ∑ i, |M i i|²) / m,
```
the second moment of a hollow Rademacher quadratic form (P3) averaged over collisions of
probability `1/m`. Its instances are the AMM identity (`M` rank one per entry), the Gram-error
identity (`A = B = U`), the JL moment (`M = x xᴴ`), and from these the trace moment at `q = 1`, the
OSE, the OSI and the sizes.

Over `𝕜` throughout (§7 Q1): the entries are `0, ±1`, coerced. Complex inputs `U`, `A`, `B`, `x` are
handled by the same statements: the exact identities carry a transpose term (`⟨M, Mᵀ⟩_F`,
`‖Aᵀ B‖_F²`, `‖Uᵀ U‖_F²`) that equals the conjugate-transpose one over `ℝ` and over `ℂ` is in
general neither equal to it nor bounded by it (§8 item 1). Each is at most its Cauchy–Schwarz value
(`‖M‖_F²`, `‖A‖_F² ‖B‖_F²`, `d`), which is all the bounds use, so every bound is the same over both
fields.

| Item | Consumers |
|---|---|
| `countSketchMatrix`, `countSketch`, the bridge | users who hold a hash and signs; Solvers (input-sparsity-time sketch-and-solve and sketch-and-precondition, Woodruff Theorem 9 and the composition with a Gaussian or SRHT after Theorem 8, through S1's `IsObliviousSubspaceEmbedding.mul`); LowRank test matrices (CEMT Table 3 lists CountSketch as an OSE with `k = O(r²)` for generalized Nyström); the deferred SparseStack, which is `ζ^{-1/2}` times a stack of `ζ` independent CountSketches (CEMT (B.2)) |
| hollow Gram identity | the deferred SparseStack and OSNAP (§4a): Route 1's trace moments at general `q` expand `Sᴴ S - 1` blockwise; Route 2's second moment |
| exact second moment, trace form | §4a Route 2, item 3: CEMT's Lemma B.1 is this identity for self-adjoint `M` plus `(tr M)²`; SparseStack's second moment is its average over `ζ` blocks |
| AMM: exact identity, bound, tail | Estimation (Hutch++ and XTrace with sparse sketches), LowRank (sketched products); over `ℂ` it is sharper than S1's JL-moment route (§7 Q6) |
| exact Gram-error mean, `HasGramTraceMoment` at `q = 1` | the OSE here; the deferred families' comparison (§4a Route 1 compares trace moments) |
| `isIsotropicSketch` | the OSI (S1); S1's CEMT tails (Lemma 2.1, sketch-and-solve Theorem 2.7) |
| OSE, OSI, `countSketchRows` | Solvers (both halves for preconditioning; the injection for constant-factor sketch-and-solve); LowRank through the OSI |
| JL moment at `p = 2` | S1's AMM, JL tail and JL lemma over `ℝ`; Estimation |

Not in S7: SparseStack, OSNAP and every `ζ > 1` law (D6, §4a); hashing with limited independence
(Woodruff Theorem 9 allows a pairwise-independent hash and 4-wise independent signs; §4a item 3, §7
Q8); complex Steinhaus signs (§6).

## 1. Objects

New §5.3 row (two approvals by CONTRIBUTING §9):

| Concept | Spelling | Bridge |
|---|---|---|
| CountSketch | constructor `countSketchMatrix h σ` (column `i` is `σ i • e (h i)`); law `countSketch k n`, the pushforward of i.i.d. uniform hash values and independent Rademacher signs with `⊤` on `k` inside | `countSketch_eq_map` (under any measurable space on `k` with measurable singletons), `hasLaw_countSketchMatrix` (from the user's hash and signs); `countSketchMatrix h σ = selectionMatrix h * diagonal σ` is noted in the docstring, not stated |

One named quantity, `countSketchRows d ε δ` (D5), an `irreducible_def` (§7 Q5).

**Used directly.** Probability: `samplingMeasure`, `isFiniteMeasure_samplingMeasure`,
`isProbabilityMeasure_samplingMeasure`, `integral_samplingMeasure`, `samplingMeasure_const_inv_card`
(P2, `Distributions/Sampling`); `rademacherVector`, `integral_rademacherMeasure`,
`integrable_rademacherMeasure`, `integral_of_hasLaw_rademacherMeasure`,
`integral_sq_of_hasLaw_rademacherMeasure`, `integral_pow_four_of_hasLaw_rademacherMeasure`,
`ae_sq_eq_one_of_hasLaw_rademacherVector` (P2, `Distributions/Rademacher`);
`integral_norm_quadForm_sub_trace_sq` and `memLp_quadForm` (P3, `QuadraticForm/Moments`; the
conditional step, with the hollow coefficient matrix, `s = 1`, `m₄ = 1`); `HasLaw.iIndepFun_eval`
(`Probability/Law`); `measureReal_ge_le_integral_div` (`Probability/Tail`). Matrix layer:
`frobNorm_sq_eq_re_trace`, `frobInner_eq_sum`, `frobNorm_transpose`, `frobNorm_mul_le`,
`frobNorm_mul_le_specNorm_mul_frobNorm`, `specNorm_transpose`, `HasOrthonormalCols.specNorm_mul_left`
(for `specNorm U ≤ 1`), `frobNorm_vecMulVec`. Sketching: S1's `HasGramTraceMoment`,
`isObliviousSubspaceEmbedding_of_hasGramTraceMoment`, `IsObliviousSubspaceEmbedding.isObliviousSubspaceInjection`,
`HasJLMoment`, `HasJLMoment.mono`, `IsIsotropicSketch`, `HasLaw.isIsotropicSketch_iff`,
`HasLaw.hasGramTraceMoment_iff`; S4's `leverageScore`, `HasOrthonormalCols.leverageScore_eq`. Mathlib:
`HasLaw`, `HasLaw.isFiniteMeasure_iff`, `HasLaw.isProbabilityMeasure_iff`, `HasLaw.integral_comp`,
`indepFun_iff_hasLaw_prodMk_prod`, `Measure.pi`, `Measure.pi_pi`, `iIndepFun_pi`, `Measure.prod`,
`integral_prod`, `integrable_prod_iff`, `measurable_from_prod_countable_left`, `uniformOn_pi` (the
bridge to a uniform hash function, docstring only), `Matrix.replicateCol`.

**Searched, none.** Mathlib: no CountSketch, sparse embedding or hash-collision lemma; `uniformOn`
has `uniformOn_pi` but no probability of a coincidence of two coordinates. NLAlib: no collision
probability (the prototype's `UniformCollision.lean` is unported; S5 §5 left it to S7). No named
Cauchy–Schwarz for `frobInner`; the proofs avoid it (the transpose terms are bounded through
`frobNorm_mul_le`).

**Lower-layer additions** (§3.1), both in `Probability/Distributions/Sampling.lean`:
1. the collision probability of two coordinates of an i.i.d. `samplingMeasure p` sample,
   `∑ r, p r ^ 2` (new; §7 Q7);
2. `pi_samplingMeasure_eq_sum`, the i.i.d. law as a finite mixture of Diracs, now private in
   `Sketching/Sampling/RowSampling.lean`: moved and made public, not reproved (CONTRIBUTING §8, exact
   overlap). S7's `countSketch_eq_map` decomposes the hash factor with it; RowSampling then uses the
   public lemma. A dated amendment to S4's note.

**No deviation from Mathlib.** The hash law is P2's `samplingMeasure` at uniform weights, already
bridged to `uniformOn Set.univ` (`samplingMeasure_const_inv_card`), as S4 and S6 use it.

## 2. Interfaces

None new. Taken: `HasLaw S (countSketch k n) μ`; `HasOrthonormalCols U` where the Gram error is
meant. Concluded: `IsIsotropicSketch`, `HasGramTraceMoment` (`q = 1`), `IsObliviousSubspaceEmbedding`,
`IsObliviousSubspaceInjection`, `HasJLMoment` (`p = 2`), all S1's. AMM concludes integrals and a
D2-shaped tail, no predicate (D2). Fixed-`U` embeddings are the oblivious statements at
`d = U.rank` (`IsObliviousSubspaceEmbedding.hasSubspaceEmbedding`), so none is stated.

## 3. Statement shapes

`namespace NLAlib`, `open MeasureTheory ProbabilityTheory`, `open scoped Matrix MatrixOrder NNReal
ENNReal`. Variables `{Ω} {mΩ} {μ : Measure Ω} {𝕜} [RCLike 𝕜] {k n q r : Type*} [Fintype k]
[Fintype n] [Fintype q] [Fintype r] [DecidableEq k] [DecidableEq n] {S : Ω → Matrix k n 𝕜}
{ε δ : ℝ}`. `[DecidableEq k]` is the constructor's `if h i = r`; `[DecidableEq n]` is `i ≠ j` in the
hollow identity and the OSI structure.

Degenerate cases.
- `card k = 0`, `n` nonempty: there is no hash, the law is the zero measure, and `HasLaw` forces
  `μ = 0`. Every integral is `0` and every right side divides by `card k = 0`, so the identities read
  `0 = 0`; every tail holds; `HasJLMoment` holds (`δ = 2 / 0 = 0`, integral `0`). Isotropy fails,
  hence `[Nonempty k]` on isotropy, on the OSI and on the probability instance, and nowhere else.
- `n` empty: one hash, the law is `dirac 0` on `k × 0` matrices, a probability measure; `A`, `B`, `U`
  have no rows, every Gram product is `0`, every identity reads `0 = 0`, no unit vector exists.
- `card k = 1`: every pair collides; `S = σᵀ`, the bound `(d² + d)/ε²` is at least `1` for `d ≥ 1`.
- `d = 0` (or `card r = 0`): every bound is `0` and every embedding event is empty.
- `d > card n`: every `U : Matrix n n 𝕜` has rank at most `card n`, so the OSE at `d` is the one at
  `min d (card n)`, whose bound is smaller; no `d ≤ card n`.
- Signs off `{±1}`: a null set; the hollow identity takes `hσ : ∀ i, σ i ^ 2 = 1`, and the law
  statements pass to it almost surely (`ae_sq_eq_one_of_hasLaw_rademacherVector`).
- `ε`: `0 < ε` on every tail and on the JL moment (at `ε = 0` the moment bound would be `0`). No
  `ε ≤ 1`: for `ε ≥ 1` the injection is vacuous and the bound is still true.
- `A = 0` or `B = 0`: the AMM identities read `0 = 0`; the D2-shaped tail takes `A ≠ 0`, `B ≠ 0` as
  S1 does (at `A = 0` the non-strict event is everything).
- `U` not orthonormal: the Gram identity and the trace moment take `hU`; the OSE handles every `U`
  through S1.

### 3.1 `Probability/Distributions/Sampling.lean` (+2, lower layer)

```lean
/-- **Collision probability.** Two distinct coordinates of an i.i.d. sample from
`NLAlib.samplingMeasure p` agree with probability $\sum_r p_r^2$; at uniform weights
$1/\lvert \iota \rvert$ this is $1/\lvert \iota \rvert$. -/
theorem measureReal_pi_samplingMeasure_setOf_apply_eq_apply {κ : Type*} [Fintype κ]
    (hp : ∑ i, p i = 1) {i j : κ} (hij : i ≠ j) :
    (Measure.pi fun _ : κ => samplingMeasure p).real {f | f i = f j} = ∑ r, (p r : ℝ) ^ 2
```
Proof: `{f | f i = f j}` is the disjoint union over `r` of the boxes `{f i = r} ∩ {f j = r}`;
`Measure.pi_pi` gives `p r * p r * ∏ 1`; `measurableSet` by finiteness. About 40 lines. The
prototype's form (`integral_ite_coordinate_eq_coordinate_pi_uniformOfFintype`, uniform `PMF` only)
is its case at uniform weights, through `integral_indicator_one`.

The moved lemma keeps S4's statement:
```lean
theorem pi_samplingMeasure_eq_sum {κ : Type*} [Fintype κ] [DecidableEq κ] (p : ι → ℝ≥0) :
    Measure.pi (fun _ : κ => samplingMeasure p) =
      ∑ f : κ → ι, (∏ j, (p (f j) : ℝ≥0∞)) • Measure.dirac f
```

### 3.2 `Sketching/Sparse/CountSketch.lean` (26)

*The sketch and its law.*
```lean
/-- The **CountSketch matrix** of a hash $h : n \to k$ and signs $\sigma : n \to \mathbb{R}$:
$\mathbf{S}_{r,i} = \sigma_i$ if $h(i) = r$ and $0$ otherwise, so column $i$ is
$\sigma_i \mathbf{e}_{h(i)}$ and $\mathbf{S} = \mathbf{P}_h \operatorname{diag}(\sigma)$ for the
selection matrix of $h$ (`NLAlib.selectionMatrix h`). Real entries, in any `RCLike` field. Its law
for uniform hashes and Rademacher signs is `NLAlib.countSketch`. [Woodruff2014, §2.1, before
Theorem 8] (the sparse embedding matrix, $S_{h(i),i} = \sigma(i)$);
[CamanoEpperlyMeyerTropp2025, (B.1)] (there $\boldsymbol{\Phi} = \mathbf{S}^{\mathsf{T}}$, over
$\mathbb{C}$ with Rademacher signs); [MartinssonTropp2020, Remark 9.1] (history). -/
def countSketchMatrix (h : n → k) (σ : n → ℝ) : Matrix k n 𝕜 :=
  Matrix.of fun r i => if h i = r then (σ i : 𝕜) else 0
variable (k n) in
/-- The **CountSketch law**: the pushforward by `countSketchMatrix` of i.i.d. uniform hash values
(`samplingMeasure` at weights $1/\lvert k \rvert$, Mathlib's `uniformOn Set.univ` by
`samplingMeasure_const_inv_card`; by `uniformOn_pi`, a uniform function $n \to k$) and independent
Rademacher signs. `⊤` on `k` inside the definition (S4 §8 item 1); `countSketch_eq_map` restates it.
Junk value: the zero measure when `k` is empty and `n` is not. [Woodruff2014, §2.1];
[CamanoEpperlyMeyerTropp2025, (B.1)]. -/
noncomputable def countSketch : Measure (Matrix k n 𝕜) :=
  letI : MeasurableSpace k := ⊤
  ((Measure.pi fun _ : n => samplingMeasure fun _ : k => (Fintype.card k : ℝ≥0)⁻¹).prod
      (rademacherVector n)).map fun x => countSketchMatrix x.1 x.2
instance isFiniteMeasure_countSketch : IsFiniteMeasure (countSketch (𝕜 := 𝕜) k n)
theorem isProbabilityMeasure_countSketch [Nonempty k] : IsProbabilityMeasure (countSketch (𝕜 := 𝕜) k n)
/-- The law as a pushforward under any measurable space on `k` with measurable singletons; the
explicit form (the sign factor is not finite, so there is no finite mixture; S6 §6). -/
theorem countSketch_eq_map [MeasurableSpace k] [MeasurableSingletonClass k] :
    countSketch (𝕜 := 𝕜) k n =
      ((Measure.pi fun _ : n => samplingMeasure fun _ : k => (Fintype.card k : ℝ≥0)⁻¹).prod
        (rademacherVector n)).map fun x => countSketchMatrix x.1 x.2
/-- D4's bridge from the user's own hash and signs. A uniform hash function
`HasLaw h (uniformOn Set.univ) μ` gives `hh` by `uniformOn_pi` and `samplingMeasure_const_inv_card`. -/
theorem hasLaw_countSketchMatrix [MeasurableSpace k] [MeasurableSingletonClass k]
    {h : Ω → n → k} {σ : Ω → n → ℝ}
    (hh : HasLaw h (Measure.pi fun _ : n => samplingMeasure fun _ : k => (Fintype.card k : ℝ≥0)⁻¹) μ)
    (hσ : HasLaw σ (rademacherVector n) μ) (hind : IndepFun h σ μ) :
    HasLaw (fun ω => (countSketchMatrix (h ω) (σ ω) : Matrix k n 𝕜)) (countSketch k n) μ
```

*The hollow Gram identity and isotropy.*
```lean
/-- **The hollow Gram identity.** For signs with $\sigma_i^2 = 1$, the Gram error
$\mathbf{S}^{\mathsf{H}}\mathbf{S} - \mathbf{I}$ of a CountSketch has zero diagonal, and entry
$\sigma_i \sigma_j$ at $i \ne j$ when $h(i) = h(j)$, $0$ otherwise. The deferred sparse families
(SparseStack, a stack of independent CountSketches) expand their Gram errors through it.
[Woodruff2014, proof of Theorem 14] (the same expansion, for $\|\mathbf{S}\mathbf{x}\|^2$);
[CamanoEpperlyMeyerTropp2025, proof of Lemma B.1]. -/
theorem conjTranspose_countSketchMatrix_mul_self_sub_one (h : n → k) {σ : n → ℝ}
    (hσ : ∀ i, σ i ^ 2 = 1) :
    (countSketchMatrix h σ : Matrix k n 𝕜)ᴴ * countSketchMatrix h σ - 1 =
      Matrix.of fun i j => if i ≠ j ∧ h i = h j then ((σ i * σ j : ℝ) : 𝕜) else 0
/-- CountSketch is isotropic, $\mathbb{E}[\mathbf{S}^{\mathsf{H}}\mathbf{S}] = \mathbf{I}$.
[CamanoEpperlyMeyerTropp2025, Lemma B.1] (first part, $\mathbb{E}[\Phi\Phi^*] = \mathbf{I}$). -/
theorem isIsotropicSketch_of_hasLaw_countSketch [Nonempty k] (hS : HasLaw S (countSketch k n) μ) :
    IsIsotropicSketch S μ
```

*The exact second moment.* `(hS : HasLaw S (countSketch k n) μ)`.
```lean
theorem integrable_norm_trace_mul_conjTranspose_mul_self_sub_one_sq_of_hasLaw_countSketch (hS)
    (M : Matrix n n 𝕜) : Integrable (fun ω => ‖(M * ((S ω)ᴴ * S ω - 1)).trace‖ ^ 2) μ
/-- **The second moment of a CountSketch**: for every $\mathbf{M}$,
$$\mathbb{E}\lvert \operatorname{tr}(\mathbf{M}(\mathbf{S}^{\mathsf{H}}\mathbf{S} - \mathbf{I}))\rvert^2
= \frac{\|\mathbf{M}\|_{\mathsf{F}}^2 + \langle \mathbf{M}, \mathbf{M}^{\mathsf{T}} \rangle_{\mathsf{F}}
- 2 \sum_i \lvert \mathbf{M}_{i,i} \rvert^2}{\lvert k \rvert}\,.$$
[CamanoEpperlyMeyerTropp2025, Lemma B.1 and its proof] (there for self-adjoint $\mathbf{M}$, the
uncentred moment $\mathbb{E}[\operatorname{tr}(\mathbf{M}\Phi\Phi^*)^2]$, which adds
$(\operatorname{tr}\mathbf{M})^2$; the exact expression is in the proof, the statement is the bound
$(\operatorname{tr}\mathbf{M})^2 + \frac{2}{b}\|\mathbf{M}\|_{\mathsf{F}}^2$). Here centred, any
$\mathbf{M}$, any field. Result: countsketch-second-moment (new) -/
theorem integral_norm_trace_mul_conjTranspose_mul_self_sub_one_sq_of_hasLaw_countSketch (hS)
    (M : Matrix n n 𝕜) :
    ∫ ω, ‖(M * ((S ω)ᴴ * S ω - 1)).trace‖ ^ 2 ∂μ =
      (frobNorm M ^ 2 + frobInner M Mᵀ - 2 * ∑ i, ‖M i i‖ ^ 2) / Fintype.card k
```

*Approximate matrix multiplication.* `(hS)`, `A : Matrix n q 𝕜`, `B : Matrix n r 𝕜`.
```lean
theorem integrable_frobNorm_conjTranspose_mul_sub_sq_of_hasLaw_countSketch (hS) (A) (B) :
    Integrable (fun ω => frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B) ^ 2) μ
/-- **AMM with a CountSketch, exact second moment**:
$$\mathbb{E}\|\mathbf{A}^{\mathsf{H}}\mathbf{S}^{\mathsf{H}}\mathbf{S}\mathbf{B} - \mathbf{A}^{\mathsf{H}}\mathbf{B}\|_{\mathsf{F}}^2
= \frac{\|\mathbf{A}\|_{\mathsf{F}}^2\|\mathbf{B}\|_{\mathsf{F}}^2 + \|\mathbf{A}^{\mathsf{T}}\mathbf{B}\|_{\mathsf{F}}^2
- 2\sum_i \|\mathbf{a}_i\|^2 \|\mathbf{b}_i\|^2}{\lvert k \rvert}$$
for the rows $\mathbf{a}_i$, $\mathbf{b}_i$. Proved without a literature source; Woodruff's proof
of Theorem 14 computes its case $\mathbf{A} = \mathbf{B} = \mathbf{x}$ over $\mathbb{R}$.
Result: amm-countsketch (new) -/
theorem integral_frobNorm_conjTranspose_mul_sub_sq_of_hasLaw_countSketch (hS) (A) (B) :
    ∫ ω, frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B) ^ 2 ∂μ =
      (frobNorm A ^ 2 * frobNorm B ^ 2 + frobNorm (Aᵀ * B) ^ 2 -
        2 * ∑ i, ‖WithLp.toLp 2 (A i)‖ ^ 2 * ‖WithLp.toLp 2 (B i)‖ ^ 2) / Fintype.card k
/-- The bound $2\|\mathbf{A}\|_{\mathsf{F}}^2\|\mathbf{B}\|_{\mathsf{F}}^2/\lvert k \rvert$, over any
field. [Woodruff2014, Theorems 13 and 14] (there $3\varepsilon$ through the JL moment, over
$\mathbb{R}$). Result: amm-countsketch -/
theorem integral_frobNorm_conjTranspose_mul_sub_sq_le_of_hasLaw_countSketch (hS) (A) (B) :
    ∫ ω, frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B) ^ 2 ∂μ ≤
      2 * frobNorm A ^ 2 * frobNorm B ^ 2 / Fintype.card k
/-- D2's AMM event (S4 §8 item 3). Over $\mathbb{R}$ it is also
`HasJLMoment.measure_frobNorm_conjTranspose_mul_sub_ge_le` at `hasJLMoment_of_hasLaw_countSketch`,
with the same bound; over $\mathbb{C}$ that route loses a factor $2$ (§7 Q6). -/
theorem measureReal_frobNorm_conjTranspose_mul_sub_ge_le_of_hasLaw_countSketch (hS) (hε : 0 < ε)
    {A : Matrix n q 𝕜} {B : Matrix n r 𝕜} (hA : A ≠ 0) (hB : B ≠ 0) :
    μ.real {ω | ε * frobNorm A * frobNorm B ≤ frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B)} ≤
      2 / (Fintype.card k * ε ^ 2)
```

*The Gram error and the embedding.* `(hS)`, `[DecidableEq r] {U : Matrix n r 𝕜}`.
```lean
/-- **The exact mean of the squared Gram error** for orthonormal $\mathbf{U}$, $d = \lvert r \rvert$:
$$\mathbb{E}\|(\mathbf{S}\mathbf{U})^{\mathsf{H}}\mathbf{S}\mathbf{U} - \mathbf{I}\|_{\mathsf{F}}^2
= \frac{d^2 + \|\mathbf{U}^{\mathsf{T}}\mathbf{U}\|_{\mathsf{F}}^2 - 2 \sum_i \ell_i^2}{\lvert k \rvert}\,,$$
$\ell_i$ the leverage scores; over $\mathbb{R}$ the middle term is $d$. Proved without a literature
source. Result: countsketch-second-moment -/
theorem HasOrthonormalCols.integral_frobNorm_conjTranspose_mul_self_sub_one_sq_of_hasLaw_countSketch
    (hU : HasOrthonormalCols U) (hS) :
    ∫ ω, frobNorm ((S ω * U)ᴴ * (S ω * U) - 1) ^ 2 ∂μ =
      ((Fintype.card r : ℝ) ^ 2 + frobNorm (Uᵀ * U) ^ 2 - 2 * ∑ i, leverageScore U i ^ 2) /
        Fintype.card k
/-- The trace moment at $q = 1$: $B = (d^2 + d)/\lvert k \rvert$. [Woodruff2014, proof of
Theorem 9] (the trace-moment Markov step at $\ell = 2$). -/
theorem hasGramTraceMoment_of_hasLaw_countSketch (hS) (hU : HasOrthonormalCols U) :
    HasGramTraceMoment S U 1 (((Fintype.card r : ℝ) ^ 2 + Fintype.card r) / Fintype.card k) μ
/-- **CountSketch OSE**: for $\varepsilon > 0$, an OSE for dimension $d$ with constants
$1 \mp \varepsilon$ and failure probability $(d^2 + d)/(\lvert k \rvert \varepsilon^2)$.
[Woodruff2014, Theorem 9] (there $O(d^2/(\delta\varepsilon^2))$ rows, after Meng and Mahoney and
Nelson and Nguyen; Woodruff's own route through Theorems 13 and 14 reaches
$18 d^2/(\delta\varepsilon^2)$). The constant $d^2 + d$ is the proof's; Nelson and Nguyen 2013 are
reported to state it (unverified, not in hand). Result: sparse-ose -/
theorem isObliviousSubspaceEmbedding_of_hasLaw_countSketch (hS) (d : ℕ) (hε : 0 < ε) :
    IsObliviousSubspaceEmbedding S d (1 - ε) (1 + ε)
      (((d : ℝ) ^ 2 + d) / (Fintype.card k * ε ^ 2)) μ
/-- **CountSketch OSI**: the lower half of the OSE, with isotropy.
[CamanoEpperlyMeyerTropp2025, Definition 1.2] for the notion; their Table 3 lists CountSketch only as
an OSE (`k = O(r²)`). Result: countsketch-osi (new) -/
theorem isObliviousSubspaceInjection_of_hasLaw_countSketch [Nonempty k] (hS) (d : ℕ) (hε : 0 < ε) :
    IsObliviousSubspaceInjection S d (1 - ε) (((d : ℝ) ^ 2 + d) / (Fintype.card k * ε ^ 2)) μ
/-- **CountSketch JL moment** at $p = 2$, $\delta = 2/(\lvert k \rvert\varepsilon^2)$, any field:
$\mathbb{E}(\|\mathbf{S}\mathbf{x}\|^2 - 1)^2 \le 2/\lvert k \rvert$ for unit $\mathbf{x}$.
[Woodruff2014, Theorem 14] (after Thorup and Zhang, not in hand; over $\mathbb{R}$, there in size
form). Result: countsketch-jl-moment (new) -/
theorem hasJLMoment_of_hasLaw_countSketch (hS) (hε : 0 < ε) :
    HasJLMoment S ε (2 / (Fintype.card k * ε ^ 2)) 2 μ
```

*Sizes.*
```lean
/-- **CountSketch rows** $(d^2 + d)/(\delta\varepsilon^2)$: a CountSketch with at least this many
rows is an OSE (and, with a row, an OSI) for dimension $d$ with constants $1 \mp \varepsilon$ and
failure probability $\delta$. The value the proof reaches; [Woodruff2014, Theorem 9] has
$O(d^2/(\delta\varepsilon^2))$ with no constant. Consumers use the API. Junk: $0$ at $\varepsilon = 0$
or $\delta = 0$. -/
noncomputable irreducible_def countSketchRows (d : ℕ) (ε δ : ℝ) : ℝ := ((d : ℝ) ^ 2 + d) / (δ * ε ^ 2)
theorem countSketchRows_nonneg (d : ℕ) (ε : ℝ) (hδ : 0 ≤ δ) : 0 ≤ countSketchRows d ε δ
theorem countSketchRows_mono {d d' : ℕ} {ε' δ' : ℝ} (hd : d ≤ d') (hε : 0 < ε) (hεε' : ε ≤ ε')
    (hδ : 0 < δ) (hδδ' : δ ≤ δ') : countSketchRows d ε' δ' ≤ countSketchRows d' ε δ
/-- The explicit comparison consumers invert with; an improved body keeps it true. -/
theorem countSketchRows_le (d : ℕ) (ε δ : ℝ) : countSketchRows d ε δ ≤ ((d : ℝ) ^ 2 + d) / (δ * ε ^ 2)
theorem isObliviousSubspaceEmbedding_of_hasLaw_countSketch_of_countSketchRows_le (hS) (d : ℕ)
    (hε : 0 < ε) (hδ : 0 < δ) (hk : countSketchRows d ε δ ≤ Fintype.card k) :
    IsObliviousSubspaceEmbedding S d (1 - ε) (1 + ε) δ μ
theorem isObliviousSubspaceInjection_of_hasLaw_countSketch_of_countSketchRows_le [Nonempty k] (hS)
    (d : ℕ) (hε : 0 < ε) (hδ : 0 < δ) (hk : countSketchRows d ε δ ≤ Fintype.card k) :
    IsObliviousSubspaceInjection S d (1 - ε) δ μ
/-- Woodruff's Theorem 14 as stated: at least $2/(\varepsilon^2\delta)$ rows give the
$(\varepsilon, \delta, 2)$ JL moment. The source's formula, so not a named size (D5, §7 Q5). -/
theorem hasJLMoment_of_hasLaw_countSketch_of_le_card (hS) (hε : 0 < ε) (hδ : 0 < δ)
    (hk : 2 / (ε ^ 2 * δ) ≤ Fintype.card k) : HasJLMoment S ε δ 2 μ
```

Proofs.
- *Law.* `countSketchMatrix` is measurable on `(n → k) × (n → ℝ)` under `⊤` on `k`
  (`measurable_from_prod_countable_left`; linear in the signs). Finiteness from the finite factors;
  probability from `isProbabilityMeasure_samplingMeasure` (uniform weights sum to `1` for nonempty
  `k`). `countSketch_eq_map`: under either measurable space on `k` (with measurable singletons), the
  hash factor is `∑ h, m^{-card n} • dirac h` (§3.1's moved lemma), the product distributes over the
  finite sum (`Measure.dirac_prod`), and both sides equal
  `∑ h, m^{-card n} • (rademacherVector n).map (countSketchMatrix h)`. Bridge: `indepFun_iff_hasLaw_prodMk_prod`, then `HasLaw.comp`
  (`IsFiniteMeasure μ` from `hσ`).
- *Hollow identity.* `((Sᴴ S) i j) = ∑ r, [h i = r][h j = r] σ i σ j`, one surviving term; the
  diagonal is `σ i ^ 2 = 1`.
- *Isotropy.* `MemLp 2` since the entries are bounded by `1` almost surely; the mean of the hollow
  entries is `0` (`E σ i σ j = 0` for `i ≠ j` by independence), so `E Sᴴ S = 1`. On the product
  space, then `HasLaw.isIsotropicSketch_iff`.
- *Trace form*, the main proof (about 150 lines). Transport to the product space by
  `HasLaw.integral_comp` and the definition; Fubini (`integral_prod`, integrability by
  `integrable_prod_iff`: the hash space is finite and each section is the conditional moment below).
  For a fixed hash, almost surely `tr (M H) = quadForm A_h (σ : n → 𝕜)` with
  `A_h i j = if i ≠ j ∧ h i = h j then M j i else 0` (the hollow identity and the trace expanded),
  `tr A_h = 0`, and P3's `integral_norm_quadForm_sub_trace_sq` with the coerced signs (independent by
  `iIndepFun.comp`; mean `0`, `E |x|² = E x² = E |x|⁴ = 1`, from P2's Rademacher moments; three
  private helpers) gives `∑_{i ≠ j, h i = h j} (‖M i j‖² + re (star (M i j) * M j i))`. Averaging over
  the hash: §3.1 at uniform weights, `∑ r, (1/m)² = 1/m`. Rearranging: `frobInner_eq_sum`,
  `frobNorm M ^ 2 = frobInner M M`, the diagonal terms split off.
- *AMM.* `Aᴴ Sᴴ S B - Aᴴ B = Aᴴ H B`, and entry `(a, b)` is `tr (M_ab H)` for the rank-one
  `M_ab := vecMulVec (fun j => B j b) (fun i => star (A i a))`. Summing the trace form over `(a, b)`:
  `∑ ‖M_ab‖_F² = ‖A‖_F² ‖B‖_F²` (`frobNorm_vecMulVec`), `∑ ⟨M_ab, M_abᵀ⟩_F = ‖Aᵀ B‖_F²`,
  `∑ ∑ i |M_ab i i|² = ∑ i ‖a_i‖² ‖b_i‖²`. Integrability by the finite sum. Bound:
  `‖Aᵀ B‖_F ≤ ‖Aᵀ‖_F ‖B‖_F = ‖A‖_F ‖B‖_F` (`frobNorm_mul_le`, `frobNorm_transpose`), drop the sum.
  Tail: `measureReal_ge_le_integral_div` on the square at `(ε ‖A‖_F ‖B‖_F)²`.
- *Gram error.* The AMM identity at `A = B = U`, with `Uᴴ U = 1`, `‖U‖_F² = d`
  (`frobNorm_sq_eq_re_trace`), `‖U i‖² = leverageScore U i`.
- *Trace moment.* `E` Hermitian, so `re tr E² = ‖E‖_F²`; integrability from the AMM's;
  `‖Uᵀ U‖_F ≤ ‖Uᵀ‖₂ ‖U‖_F ≤ √d` (`frobNorm_mul_le_specNorm_mul_frobNorm`, `specNorm_transpose`,
  `specNorm U ≤ 1` from `HasOrthonormalCols.specNorm_mul_left` at `1`); drop the leverage sum.
- *OSE.* S1's `isObliviousSubspaceEmbedding_of_hasGramTraceMoment` at `p = Fin (min d (card n))`
  (as `HasJLMoment.isObliviousSubspaceEmbedding` does), then rank at most `card n` and monotonicity of
  `(d² + d)`. *OSI*: S1's `.isObliviousSubspaceInjection` with isotropy (`IsFiniteMeasure μ` from
  the law).
- *JL moment.* The AMM bound at `A = B = replicateCol Unit x`: the error is the `1 × 1` matrix
  `‖S x‖² - ‖x‖²`, so `E |‖S x‖² - 1|² ≤ 2/m` for unit `x`; `Real.rpow_two`.
- *Sizes.* `countSketchRows_def` inside the file only; `hk` gives `(d² + d)/(m ε²) ≤ δ` (for `d ≥ 1`
  it forces `m > 0`; `d = 0` is direct); `HasJLMoment.mono` for Woodruff's form.

## 4. Files

S7 proper: 26 statements in one file, about 650 lines against the brief's 450 (the general-`M` trace
form, the AMM block over `𝕜`, the bridge and the size API are the overrun).
1. `Sketching/Sparse/CountSketch.lean` (26: 3 definitions, 1 instance, 22 theorems); imports
   `Probability/Distributions/{Sampling,Rademacher}`, `Probability/QuadraticForm/Moments`,
   `Probability/Law`, `Probability/Tail`, `Matrix/Norms/{Frobenius,Compare,Spectral}`,
   `Sketching/Properties/{TraceMoment,Isotropic,Oblivious,JohnsonLindenstrauss}`,
   `Sketching/Sampling/Leverage`. Order inside: law; hollow identity and isotropy; trace form; AMM;
   Gram error and embedding; sizes.

Lower layer: `Probability/Distributions/Sampling.lean` (+2, about 70 lines, one of them moved from
`Sketching/Sampling/RowSampling.lean`), §3.1.

Order: §3.1 first (one small agent task), then the file; the trace form before everything after it.
Bibliography: no new key. Clarkson and Woodruff (2013), Meng and Mahoney (2013), Nelson and Nguyen
(2013), Thorup and Zhang (2012) and Charikar, Chen and Farach-Colton (2004) are cited by name only,
through Woodruff's references [27], [92], [97], [115], [24], each marked "not in hand" (brief §7.2).

## 5. Material

Read: the prototype's `Sketching/Sparse/{CountSketch,CountSketchMoments,CountSketchExpectation,
CountSketchTail}.lean` (425 lines, 21 declarations: `ℝ` only, transpose, `countSketchLaw` on the
primitive space, `PMF.uniformOfFintype`, sources the dropped manuscript, D16); the files they lean on,
`Sketching/Sampling/UniformCollision.lean` and `Matrix/Subspaces/FrameFourthContractions.lean`;
`atlas/declarations.json` (`sparse-ose` on four theorems, "partial"); Woodruff §2.1 (the construction,
Theorems 8 to 10 and the proof of Theorem 9 through the trace moment at `ℓ = 2`), §2.2 (Definition 12,
Theorems 13 and 14 and its proof); CEMT Appendix B ((B.1), (B.2), Lemma B.1 and §B.1), Table 3; MT
§9.2 and Remark 9.1. Ledger (prototype to here):
- `CountSketch.lean` (8): `countSketchMatrix` to `countSketchMatrix` (`𝕜`, signs coerced);
  `countSketchLaw` and `isProbabilityMeasure_countSketchLaw` to `countSketch` (the pushforward, D4)
  and `isProbabilityMeasure_countSketch`; `transpose_countSketchMatrix_mul_apply` and
  `mul_countSketchGram_sub_one_mul_apply_eq_quadForm` to `conjTranspose_countSketchMatrix_mul_self_sub_one`
  (the entry formula and the quadratic form are its proof); `countSketchHollowCoefficient`, `_diag`
  to the private coefficient matrix `A_h` of the trace-form proof; `countSketch_gram_error_eq` not
  ported (`Uᴴ U = 1` algebra inside the Gram corollary).
- `CountSketchMoments.lean` (5): `ae_countSketch_gram_error_apply_eq_quadForm`,
  `integrable_countSketch_gram_error_apply_sq`, `integral_countSketch_gram_error_apply_sq`,
  `integral_frobSq_countSketch_gram_error` to the conditional step of the trace form (private; the
  sign moment is P3's `integral_norm_quadForm_sub_trace_sq`); `integral_countSketch_gram_error_apply_eq_zero`
  to the isotropy proof.
- `CountSketchExpectation.lean` (4): `measurable_frobSq_countSketch_gram_error` to the measurability
  inside the law (not public); `integrable_frobSq_countSketch_gram_error` to
  `integrable_frobNorm_conjTranspose_mul_sub_sq_of_hasLaw_countSketch` (any `A`, `B`);
  `integral_frobSq_countSketch_gram_error_eq_scaled_contractions` private;
  `integral_frobSq_countSketch_gram_error_eq` to
  `HasOrthonormalCols.integral_frobNorm_conjTranspose_mul_self_sub_one_sq_of_hasLaw_countSketch`
  (`𝕜`, `‖Uᵀ U‖_F²` in place of `d`).
- `CountSketchTail.lean` (4): `integral_frobSq_countSketch_gram_error_le` to
  `hasGramTraceMoment_of_hasLaw_countSketch`; `measure_countSketch_gram_failure_le` to S1's
  `HasGramTraceMoment.measure_specNorm_ge_le` (exists; at `q = 1` the trace is the Frobenius square);
  `measure_countSketch_gram_failure_le_of_rows` and `measure_countSketch_embedding_failure_le_of_rows`
  to `isObliviousSubspaceEmbedding_of_hasLaw_countSketch_of_countSketchRows_le` (oblivious, any `U`,
  the rows named).
- Outside the four, ledgered here: `UniformCollision.lean` (2; S5 §5 left it to S7):
  `integral_ite_eq_uniformOfFintype` is `integral_samplingMeasure` at uniform weights (exists),
  `integral_ite_coordinate_eq_coordinate_pi_uniformOfFintype` to §3.1 (general weights).
  `FrameFourthContractions.lean`: M5 ledgered `sum_offDiagonal_frame_contractions_eq` as "returns with
  the CountSketch second moment"; it is subsumed by the AMM identity at `A = B = U`
  (`‖Uᵀ U‖_F²` is its cross contraction), not ported; the other four are M5's.
Result ids: `sparse-ose` (atlas) on the OSE; `countsketch-osi`, `countsketch-jl-moment`,
`countsketch-second-moment`, `amm-countsketch` (new).

## 6. Cut, and why

- `Fin` sizes, `PMF.uniformOfFintype`, `ℝ`-only statements and the transpose spelling (D5, §5.1).
- Fixed-`U` OSE and OSI: the oblivious statements at `d = U.rank` give them in one line.
- The OSE through the JL moment (`HasJLMoment.isObliviousSubspaceEmbedding`: failure `2 d²/(m ε²)`
  at distortion `ε`): dominated by the trace-moment route's `(d² + d)/(m ε²)` for every `d ≥ 1`
  (CONTRIBUTING §5.2 rule 6). Woodruff's Theorem 8 (polylogarithmic rows) is dominated by Theorem 9.
- A JL property theorem and the JL lemma for `N` points: S1's `HasJLMoment.hasJLProperty` and
  `HasJLProperty.measure_exists_abs_norm_mulVec_sq_sub_ge_le` give them from the JL moment in one
  line each; no consumer asks for a CountSketch-named form.
- A free-threshold AMM tail (S4 has one): the integral bound and `measureReal_ge_le_integral_div`
  give it in one line; the D2-shaped tail is the one consumers take (§7 Q6).
- A bound form of the trace identity (`≤ 2 ‖M‖_F² / m`, CEMT's): its only consumer is §4a Route 2,
  which needs the uncentred moment anyway and will state it there; the exact identity is the
  reusable part.
- Limited independence (pairwise hashes, 4-wise signs; Woodruff Theorems 9 and 14): no `k`-wise
  predicate exists (§4a item 3); the fully independent law is the case every consumer holds (§7 Q8).
- Complex Steinhaus signs: the complex sign law is later work (brief §0); with it, the trace form's
  proof is P3's identity with `s = 0`, and the transpose term drops.
- SparseStack, OSNAP, the `IIDComparison`, `FockModel`, `Bands`, `FiniteLaw`, `MomentMethod` blocks:
  deferred (D6, §4a), ledgered as such by the round.

## 7. Questions and decisions

**Hard to reverse:** Q1 (the field of the law fixes the type of every CountSketch statement and every
consumer's hypothesis). It amends D3's "ℝ", so it goes to the orchestrator's Fable review before the
skeleton. **Decisions taken** (open to correction): the rest; none is hard to reverse.

**Q1 (hard to reverse). The law is over `𝕜`, with real signs coerced.** D3 lists CountSketch over `ℝ`,
with "real laws conclude the `𝕜` predicates at `𝕜 = ℝ`; their complex analogues, later". Options:
- (a) `countSketch k n : Measure (Matrix k n ℝ)`, as D3 says. A complex user (complex `U` in
  sketch-and-solve, a complex `A` in generalized Nyström) then needs `S.map ofReal` and a transport of
  every predicate from `ℝ` to `ℂ`, which the library does not have; and "the complex analogue" of a
  matrix with entries `0, ±1` is the same matrix.
- (b) `countSketch k n : Measure (Matrix k n 𝕜)`, entries `(σ i : 𝕜)`, as S6 does with `srhtMatrix`
  (D11, S6 Q10). CEMT work this way (their (B.1) is a complex matrix with Rademacher entries).

*Recommendation (b).* It costs nothing in the proofs (P3's quadratic-form identity is over `𝕜` with
`s = E x² = 1` for real signs), every bound is field-independent (§0), and the real case is
`𝕜 = ℝ` with no corollary. *Reversal*: every statement's type and every consumer's.

**Q2. The primary statement is the trace form, for every `M`.** The brief names "the exact mean of
`frobNorm G ^ 2`". Three forms of one computation exist: the trace form `E |tr (M H)|²` (CEMT's), the
AMM form `E ‖Aᴴ H B‖_F²`, the Gram form at `A = B = U`. The trace form is primary because each other
form is a finite sum of its instances, and it is what §4a Route 2 needs. The AMM form is stated
because Estimation consumes it; the Gram form because the brief and D16 name it and the trace moment
is its corollary. All three exact identities are over `𝕜` with transpose terms
(`⟨M, Mᵀ⟩_F`, `‖Aᵀ B‖_F²`, `‖Uᵀ U‖_F²`); over `ℝ` the last is `d` by
`conjTranspose_eq_transpose_of_trivial` and `hU`, in two rewrites; no real twin (CONTRIBUTING §5.1). The trace form's
docstring cites CEMT (the identity is in their proof); the AMM and Gram forms say "proved without a
literature source" (D16). Not hard to reverse (additive).

**Q3. The hash law is P2's `samplingMeasure` at uniform weights, per column, i.i.d.** As S6's
`srhtWithReplacement` (the same primitive: i.i.d. uniform indices) and S4. Alternatives: Mathlib's
`uniformOn Set.univ` per coordinate, or `uniformOn` on `n → k` (a uniform hash function). Both are one
rewrite away (`samplingMeasure_const_inv_card`, `uniformOn_pi`), named in the bridge's docstring.
`samplingMeasure` keeps the round's sampling laws in one spelling and supplies the integral API
(`integral_samplingMeasure`) the collision step uses. Not hard to reverse (the body and the bridge's
hypothesis).

**Q4. The OSE's constant and attribution.** The trace-moment route at `q = 1` with the exact Gram
identity gives `(d² + d)/(m ε²)`, written in the statement (D12), better than the JL-moment route's
`2 d²/(m ε²)` (§6) and Woodruff's `18 d²/(δ ε²)`. The brief attributes the constant to Nelson and
Nguyen, unconfirmed: the docstring says "the proof's constant; reported to be Nelson and Nguyen's
(unverified, not in hand)" and cites Woodruff Theorem 9 for the `O`. The OSI has the same failure
probability: no one-sided bound better than the two-sided Markov step is available from a second
moment of the matrix. Not hard to reverse (an improvement adds a theorem, rule 6).

**Q5. Sizes.** `countSketchRows d ε δ := (d² + d)/(δ ε²)` is an `irreducible_def` with `_nonneg`,
`_mono`, `_le` (S4's pattern): its body is the proof's constant, and the source's is unconfirmed, so
D5's exception does not apply. The JL size is written inline as Woodruff's `2 / (ε ^ 2 * δ)`: it is
the confirmed source formula (Woodruff Theorem 14), so by D5 and CONTRIBUTING §5.2 rule 2 it needs no
name. Not hard to reverse.

**Q6. AMM over `𝕜` directly.** S1's AMM is over `ℝ` only, because over `ℂ` the JL moment gives only
`√2 ε` (S1's Pauli example). For CountSketch the direct identity gives `2 ‖A‖_F² ‖B‖_F²/m` over both
fields, so over `ℂ` it is twice as good as any route through the JL moment and not a twin. Stated:
the exact identity, its integrability, the bound, and D2's tail (S4 §8 item 3); not the
free-threshold tail (§6). Not hard to reverse.

**Q7. The collision probability is a public Probability lemma, with general weights.** It has no
NLAlib vocabulary and a general statement (`∑ r, p r ²`, the collision probability of a
distribution), it is the only missing lower-layer fact, and the deferred SparseStack and OSNAP hash
averages are its next users. *Alternative*: a private helper in `CountSketch.lean` at uniform weights;
rejected by CONTRIBUTING's "a lemma a second file could want is public from the start". Owner: P2's
`Distributions/Sampling.lean`, beside `samplingMeasure_singleton`. Not hard to reverse.

**Q8. Full independence only.** Woodruff's Theorems 9 and 14 hold for a pairwise-independent hash and
4-wise independent signs, and the proofs here use only those moments. Stating that needs a `k`-wise
independence predicate on a law (§4a item 3), which does not exist and is deferred with the sparse
families. When it lands, the theorems are restated on it and the current ones become corollaries at
`countSketch`. Not hard to reverse (additive).

**Q9. The hollow identity is stated deterministically, with `hσ : ∀ i, σ i ^ 2 = 1`, in entry form.**
The factored form `D_σ ((1 : Matrix k k 𝕜).submatrix h h - 1) D_σ` (through `selectionMatrix`) is its
proof, not a second statement. Not hard to reverse.

**Q10. Size.** About 650 lines and 26 statements in one file against the brief's 450, near the
twenty-five-statement budget, so no split; plus about 70 lines in P2 (one statement new, one moved).

## 8. Amendments from the review (2026-10-15)

Fable review of this note (0 blocker, 2 major, 13 minor). Of the fifteen amendments the orchestrator
accepted fourteen, two of them corrected on inspection (A6's instance list, item 6; A11's shared
step, item 11), and rejected one on inspection (A10: the lemma exists, item 10); the optional A9 is
taken. Q1 decided as (b) with a dated amendment of D3; nothing for the maintainer. The review
verified the hollow Gram identity over any `RCLike` field, the exact second moment (recomputed by a
direct fourth-moment expansion and through P3), the AMM identity and bound, the Gram mean, the
trace moment `(d² + d)/m`, the OSE and OSI routes, the JL moment and Woodruff's `2/(ε²δ)` (Theorem
14 verbatim), CEMT's Lemma B.1 and (B.2), the degenerate cases except those of items 5 and 8, every
name of §1, the statement count, and that no statement is dominated. Where an item below
contradicts §0 to §7, it supersedes them; §3 stays as drafted. §0's false sentence is also
corrected in place (item 1). Skeletons: the files of item 17, every new proof `sorry`.

1. **A1 (major), the transpose terms.** §0 claimed that each transpose term is at most its
   conjugate-transpose counterpart over `ℂ`. False for two of the three: at `A = x = (1, i)/√2`,
   `B = conj x`, `‖Aᵀ B‖_F = 1` but `‖Aᴴ B‖_F = 0`; at `M = [[0, i], [i, 0]]`, `⟨M, Mᵀ⟩_F = 2` but
   `⟨M, Mᴴ⟩_F = -2`. What is true, and all the proofs use: each is at most its Cauchy–Schwarz value
   (`‖M‖_F²`, `‖A‖_F² ‖B‖_F²`, `d`), so every bound is field independent. §0 now says this (prose
   only); §7 Q1's "every bound is field-independent (§0)" reads with this reason. The §3.2
   docstrings do not repeat the claim and must not.
2. **A2 (major), Q1 decided: (b), the law over `𝕜` with real signs coerced.** (b) strictly contains
   (a): the `ℝ` law is the instance `𝕜 = ℝ` of (b) with no corollary, while (a) could not later be
   promoted to (b) without a parallel law or an `ofReal` transport of every predicate, which the
   library lacks. Reversal from (b) to (a) is a specialisation nobody would ask for, so "hard to
   reverse" was misapplied (as S4 §8 item 9 withdrew it for `U.rank`); the rework, if the maintainer
   ever objected, is an ascription `(𝕜 := ℝ)` at consumers, not a restatement. Precedent: S6 Q10,
   `srhtMatrix` with real signs coerced into `Matrix k n 𝕜`, reviewed with nothing for the
   maintainer; CONTRIBUTING §5.1 restricts `ℝ` "for now" to the Gaussian and Haar laws only. The
   choice does amend the field column of D3, a maintainer-approved table: `docs/PORT_SKETCHING.md`
   carries a dated amendment under D3 (2026-10-15, pointing here), and the stage report names it.
   Two honest costs: the two exact identities read `‖Uᵀ U‖_F²` and `‖Aᵀ B‖_F²` where a real reader
   expects `d` and `‖Aᴴ B‖_F²` (two rewrites over `ℝ`, Q2), and nothing over `ℂ` is sharper than
   over `ℝ`. §7's "Hard to reverse" paragraph is withdrawn: no S7 decision is hard to reverse, and
   Q1's *Reversal* line reads as above.
3. **A3, the trace-moment citation.** Woodruff's printed proof of Theorem 9 is Nguyen's AMM route
   (Theorems 13 and 14); the `ℓ = 2` trace-moment argument is described after Theorem 9 as the
   proof of his [92] and [97]. `hasGramTraceMoment_of_hasLaw_countSketch` cites
   "[Woodruff2014, Theorem 9 and the discussion following it] (the proof of Meng and Mahoney and of
   Nelson and Nguyen, as Woodruff describes it)". S1's `HasJLMoment.hasSubspaceEmbedding` keeps
   "proof of Theorem 9", which matches the printed proof.
4. **A4, Q4's attribution, accepted with the reviewer's wording.** The OSE docstring's last
   sentence becomes: "The constant is the proof's; the second-moment route is Meng and Mahoney 2013
   and Nelson and Nguyen 2013 (Woodruff, Theorem 9), neither in hand, so the constant is not
   attributed." Q4's quoted docstring reads the same. D12's "attributed to Nelson and Nguyen,
   unconfirmed" stays in the brief as the provenance of the question.
5. **A5, empty `k` in the trace-form proof.** The collision lemma takes `hp : ∑ p = 1`, which fails
   for empty `k` (weights `0⁻¹ = 0`). The proof splits on `Nonempty k` before the hash average; in
   the empty case the law is `0` (`n` nonempty) or `dirac 0` (`n` empty) and both sides are `0`. The
   nonempty branch is also where `isProbabilityMeasure_samplingMeasure` is discharged.
6. **A6, instance placement** (as S0 and S1 §8 did), corrected on inspection. The trace form and its
   integrable companion also need `[DecidableEq n]`: their `- 1` is `1 : Matrix n n 𝕜`. Section
   variables: `[Fintype k] [Fintype n] [DecidableEq k]`. On the declarations: `[DecidableEq n]` on
   the hollow identity (item 9's general entry formula has no `1` and does not need it), isotropy,
   the trace form and its companion, the OSI and the OSI size corollary; `[Fintype q] [Fintype r]`
   on the AMM block; `[Fintype r] [DecidableEq r]` on the Gram block (the Gram mean, item 7's
   companion, the trace moment). The AMM block, the OSE, the JL moment and the sizes carry no
   `[DecidableEq n]`; proofs that pass through the trace form open `classical`.
7. **A7, the Gram error's integrable companion** (brief §3: every expectation upper bound beside
   its `integrable_` companion). Added, for every `U` (no `hU`: the AMM companion at `A = B = U`
   plus the constant `Uᴴ U - 1`, on a finite measure):
   ```lean
   theorem integrable_frobNorm_conjTranspose_mul_self_sub_one_sq_of_hasLaw_countSketch (hS)
       (U : Matrix n r 𝕜) : Integrable (fun ω => frobNorm ((S ω * U)ᴴ * (S ω * U) - 1) ^ 2) μ
   ```
   The trace moment's integrability field comes from it with `re tr E² = ‖E‖_F²`.
8. **A8.** §3's degenerate case `card k = 1`: the clause "the bound `(d² + d)/ε²` is at least `1`
   for `d ≥ 1`" is deleted (false for `ε² > d² + d`; the theorem holds for every `ε` by Markov).
9. **A9, the general entry formula first** (CONTRIBUTING §5.2, general form first), for arbitrary
   real signs:
   ```lean
   theorem conjTranspose_countSketchMatrix_mul_self_apply (h : n → k) (σ : n → ℝ) (i j : n) :
       ((countSketchMatrix h σ : Matrix k n 𝕜)ᴴ * countSketchMatrix h σ) i j =
         if h i = h j then ((σ i * σ j : ℝ) : 𝕜) else 0
   ```
   The hollow identity stays, as its corollary under `hσ`, with its own consumers (SparseStack,
   OSNAP). A deferred family that scales the signs rather than the stack takes the general form.
   §5's ledger: the prototype's `transpose_countSketchMatrix_mul_apply` maps to this one; Q9 reads
   with it.
10. **A10 rejected on inspection.** `HasOrthonormalCols.specNorm_le_one` exists
    (`Matrix/Norms/Compare.lean`, line 267, proved through `specNorm_mul_left` exactly as the note
    planned to inline). Nothing is added; the trace-moment proof uses it by name, and §1's
    "Used directly" reads `HasOrthonormalCols.specNorm_le_one` in place of
    "`HasOrthonormalCols.specNorm_mul_left` (for `specNorm U ≤ 1`)".
11. **A11, the law's explicit form, corrected on inspection: no mixture step, one shared public
    lemma.** S6's `srht_eq_map_prod` is proved with `Measure.map_prod_map` (the definition is
    already the pushforward of a product); neither it nor `countSketch_eq_map` distributes a product
    over a finite sum. The step S6 and S7 share is that a measurable space with measurable
    singletons on a finite type is `⊤`: private `measurableSpace_eq_top` in
    `Sketching/Structured/SRHT.lean`, used by S6's two "any measurable space" bridges through
    `obtain rfl`. `countSketch_eq_map` is then `obtain rfl := …; rfl`, and the bridge is
    `IndepFun.hasLaw_prod` (Mathlib's alias of `indepFun_iff_hasLaw_prodMk_prod`) and `HasLaw.comp`
    with the measurable constructor, as S6's. The shared step becomes one public lemma, in Mathlib's
    generality (Mathlib's instance `MeasurableSingletonClass.toDiscreteMeasurableSpace` covers the
    finite case), named after Mathlib's `DiscreteTopology.eq_bot`, in the new file
    `NLAlib/ForMathlib/MeasureTheory/MeasurableSpace/Defs.lean` (imports
    `Mathlib.MeasureTheory.MeasurableSpace.Defs`; upstream candidate):
    ```lean
    /-- A discrete measurable space is `⊤`: every set is measurable. -/
    theorem DiscreteMeasurableSpace.eq_top {α : Type*} [m : MeasurableSpace α]
        [DiscreteMeasurableSpace α] : m = ⊤
    ```
    S7's skeleton writes it (S7 needs it; `SRHT.lean` is being worked on and is not touched). At
    the round's wrap-up, `SRHT.lean`'s private copy is deleted and its uses point here;
    RowSampling's `samplingSketch_eq_map` may be shortened the same way. Consequence: §1's
    lower-layer item 2 is withdrawn. S7 has no use for the mixture form (the hash average goes
    through the collision lemma, item 12), so `pi_samplingMeasure_eq_sum` stays private in
    `RowSampling.lean` and S4's note is not amended.
12. **A12, the uniform collision probability inline.** At uniform weights with `[Nonempty k]` the
    trace-form proof computes `∑ r, ((card k)⁻¹)² = (card k)⁻¹` inline (`Finset.sum_const`,
    `Finset.card_univ`, `mul_inv_cancel₀`); no corollary is stated.
13. **A13, the empty corners.** `isProbabilityMeasure_countSketch` keeps `[Nonempty k]`; the module
    docstring records both subcases of empty `k` (`n` nonempty: the law is `0`; `n` empty: it is
    `dirac 0`, a probability measure the theorem leaves out), as S4 §8 item 8 did for RowSampling.
14. **A14, Q6 accepted with the reviewer's wording.** Q6 and the AMM tail's docstring say: "S1's
    AMM route is over `ℝ` only, where it gives the same `2/(m ε²)`; the direct identity is the only
    AMM for a complex CountSketch, and is a factor `2` better in the failure probability than the
    `√2 ε` form S1 would state." The stage report notes that S1's `𝕜` form of AMM stays open for
    the other families.
15. **A15, the import.** `Probability/Distributions/Sampling.lean` imports also
    `Mathlib.MeasureTheory.Constructions.Pi` (`Measure.pi`, `Measure.pi_pi`) for the collision
    lemma; no cycle (RowSampling already imports it).
16. **Docstrings in LaTeX** (CONTRIBUTING §6, item 5). The skeleton writes every docstring's
    mathematics in LaTeX: §3's docstrings already do, and the texts items 3, 4, 7, 9, 13 and 14 add
    or rewrite, quoted here with Unicode mathematics, are converted (`$2/(m\varepsilon^2)$`,
    `$\sqrt{2}\,\varepsilon$`); Lean names stay in code spans.
17. **Files** (amends §4 and §1's lower-layer list). S7 proper: 28 statements,
    1. `Sketching/Sparse/CountSketch.lean` (28: 3 definitions, 1 instance, 24 theorems; items 7 and
       9 add one each), about 680 lines.
    Lower layers, 2 statements:
    - `Probability/Distributions/Sampling.lean` (+1, the collision lemma; item 15's import);
    - `ForMathlib/MeasureTheory/MeasurableSpace/Defs.lean` (new, 1, item 11).
    In all, 30 statements. Order: the two lower-layer lemmas first (one small task), then the file,
    the trace form before everything after it.
18. §7: Q1 decided by item 2; Q4 by item 4; Q6 by item 14; Q9 with item 9; Q10's count by item 17;
    Q2, Q3, Q5, Q7 and Q8 stand.
