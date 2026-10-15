# Design note: Sketching stage S5, sampling without replacement

Status: drafted 2026-10-15 under `docs/PORT_SKETCHING.md` (D4, D5, D8, D9, D10, D12, D14, D15; §3;
the S5 entry of §4; §4a Route 1 item 1). Builds on `docs/design/Sketching-S4.md` as amended by its §8
(the law is a pushforward with `letI := ⊤` inside the body, S4 §8 item 1; the mixture form is a lemma);
reviewed 2026-10-15, amendments in §8, which overrides §0 to §7 where they disagree. No question of
the brief's §2(a) kind (§7; Q9 decided by the orchestrator). No missing lower-layer infrastructure
(§1); five small promotions into S4's, S1's and a ForMathlib file (§8 item 1). Four files where the
brief lists two (§7 Q1).

## 0. Scope and consumers

Two layers of content.
- **General probability (D10).** Hoeffding's comparison: a sum over a uniformly random injection
  `ι : k → n` is dominated in convex order by the same sum over i.i.d. uniform indices. It is
  proved once from a Markov kernel with a barycenter identity. The matrix Chernoff tails without
  replacement follow, with P5a's trace forms `…_of_integral_le` doing the rest.
- **Sketching.** The sketch `√(card n / card k) • Pᴴ`, `P` the selection by a uniform injection, is
  S4's constructor at uniform weights. Its law, isotropy, and the fixed-`U` injection and embedding
  with S4's exponents and sizes.

In this note `d := U.rank`, `√(n/k) := √(Fintype.card n / Fintype.card k)`, and "uniform weights"
is `fun _ : n => (Fintype.card n : ℝ≥0)⁻¹`; the Lean statements spell these out.

| Item | Consumers |
|---|---|
| convex order from a barycenter (kernel form) | Hoeffding's comparison (here); the deferred sparse comparison with an i.i.d. model and OSNAP's fill/thin coupling (brief §4a Route 1 item 1) |
| Hoeffding's comparison for `uniformOn {f : k → n \| Injective f}` | the matrix Chernoff tails here; any later scalar or matrix tail without replacement (one convex `f` each) |
| the uniform injection: probability, junk value, singleton mass, invariance, marginals | this stage's law and isotropy; S6 (the SRHT law is signs times this injection); OSNAP positions (§4a) |
| matrix Chernoff without replacement (trace bound, four tails) | the sketch tails here; LowRank column sampling without replacement (Nyström, CUR) on a population of PSD atoms; Tropp 2011a's SRHT argument, through S6 |
| `samplingSketchWithoutReplacement`, isotropy, fixed-`U` injection, upper half, embedding, sizes | S6 (the SRHT is this sketch applied to `H D U` given the signs); Solvers (sketch-and-solve for an incoherent `A` by subsampling, through S0); S1's fixed-`U` CEMT tails (isotropy plus `HasSubspaceInjection`) |

Not in S5: oblivious statements (the tail depends on `coherence U`; S6 gets obliviousness by
flattening), non-uniform weights without replacement (no comparison, §6), AMM without replacement
(§6).

## 1. Objects

New §5.3 row (§7 Q9; two approvals by CONTRIBUTING §9):

| Concept | Spelling | Bridge |
|---|---|---|
| uniform sampling without replacement | the law `uniformOn {f : k → n \| Function.Injective f}` on index maps (Mathlib's, D10); the sketch law `samplingSketchWithoutReplacement k n`, the pushforward of it by S4's `samplingSketchMatrix` at uniform weights | `hasLaw_samplingSketchMatrix_of_hasLaw_uniformOn_injective`, `samplingSketchWithoutReplacement_eq_map`, `…_eq_sum_smul_dirac` |

No convex-order predicate (§7 Q3). No new named quantity: the tails and sizes are S4's (§7 Q6).

Used directly. Mathlib: `uniformOn`, `uniformOn_univ`, `uniformOn_pi`, `uniformOn_singleton`,
`uniformOn_empty_meas`, `isProbabilityMeasure_uniformOn`, `Function.Embedding.nonempty_of_card_le`,
`Fintype.card_embedding_eq`, `Equiv.subtypeInjectiveEquivEmbedding`,
`Equiv.Perm.exists_smul_eq_embedding`, `ConvexOn.map_integral_le` (Jensen),
`ConvexOn.comp_linearMap`, `ProbabilityTheory.integral_comp` with
`Measure.comp_eq_comp_const_apply` (or `Measure.integral_compProd` with `Measure.snd_compProd`),
`Kernel.ofFunOfCountable`, `iIndepFun_pi`, `measurePreserving_eval`, `HasLaw.integral_comp`. NLAlib:
`convexOn_re_trace_exp` (`Matrix/Functions/TraceFunctions`), `convex_setOf_posSemidef`
(`Matrix/Inequalities/Order`), `isClosed_setOf_posSemidef` (`ForMathlib/LinearAlgebra/Matrix/PosDef`),
`Matrix.IsHermitian.re_trace_exp_pos`; P5a's `hasMatrixMGFBound_of_posSemidef_of_le`,
`HasMatrixMGFBound.integral_re_trace_exp_sum_le`, `HasMatrixMGFBound.integrable_re_trace_exp_sum` and
the four trace-form tails `measureReal_eigenvalue_{zero_ge,le}_le_{chernoff,card_mul_exp}_of_integral_le`
(`MatrixConcentration/Chernoff`, whose module docstring names sampling without replacement as their
second instance); P2's `samplingMeasure_const_inv_card`; S4's `samplingSketchMatrix`,
`conjTranspose_samplingSketchMatrix_mul_mul`, `leverageScore` and its API, `coherence`,
`leverageScore_le_coherence_mul_inv`, `samplingSize`, `samplingInjectionSize` with their `_le`
lemmas; S1's `HasLaw.hasSubspaceInjection_iff`, `HasLaw.hasSubspaceEmbedding_iff`,
`HasSubspaceInjection.hasSubspaceEmbedding`, `HasSubspaceEmbedding.of_range_le`; S0's
`HasOrthonormalCols.isSubspaceInjection_iff`, `isSubspaceInjection_of_nonpos`.

Searched, none: convex order or Hoeffding's comparison in Mathlib (`grep -rn "convex order\|ConvexOrder"`);
a Bochner `integral_bind` or `integral_comp` for `κ ∘ₘ μ` (Mathlib has `lintegral_bind` and the kernel
form `ProbabilityTheory.integral_comp`; the measure form is two lines through
`Measure.comp_eq_comp_const_apply`, a private helper); a `MeasurableSpace (Equiv.Perm n)` instance (the
permutation step of §3.2 is private and fixes `⊤` locally); `map` and integral lemmas for `uniformOn`
beyond `uniformOn_pi` (singleton masses through `Measure.ext_of_singleton`); `IsClosed
{A | A.IsHermitian}` (not needed: the comparison runs on the PSD cone, which is closed and convex in
NLAlib already). **Nothing is missing below Sketching.** No deviation from Mathlib.

## 2. Interfaces

None new. Taken: `HasLaw ι (uniformOn {f : k → n | Function.Injective f}) μ` (Probability),
`HasLaw S (samplingSketchWithoutReplacement k n) μ` (Sketching), D8's domination hypothesis at
uniform weights `hdom : ∀ i, leverageScore U i ≤ L * (Fintype.card n : ℝ)⁻¹` (§7 Q7), P5a's population
hypotheses `hpsd : ∀ i, (X i).PosSemidef`, `hle : ∀ i, X i ≤ L • (1 : Matrix m m 𝕜)`. Concluded:
`IsIsotropicSketch`, `HasSubspaceInjection`, `HasSubspaceEmbedding` (S1).

## 3. Statement shapes

`namespace NLAlib`, `open MeasureTheory ProbabilityTheory`, `open scoped Matrix MatrixOrder NNReal
ENNReal`, and `Matrix.Norms.L2Operator` in the two matrix files. Variables per file below; `[Fintype _]`
throughout.

Degenerate cases.
- `card n < card k`: there is no injection. `uniformOn ∅ = 0`, so the injection law and the sketch
  law are the zero measure, and `HasLaw` (which carries `AEMeasurable`) forces `μ = 0`. Every tail is
  then `0 ≤ bound`, with the bound nonnegative, and holds. Hence no `card k ≤ card n` on any tail
  (§7 Q8). It is needed by the comparison of measures (§3.2: a convex `f` may be negative, so `0 ≤ ∫ f`
  can fail), by `isProbabilityMeasure_…`, by the marginal lemma and by isotropy (`∫ = 0 ≠ 1`).
- `card k = 0`: one injection, the empty map; `S = 0`, the sum over `j` is `0`, the law is `dirac 0`.
  The lower bound is `d · e⁰ ≥ 1` when `d ≥ 1`; the upper half holds surely; Chernoff's
  `card m · (…)^0 ≥ 1`. Not isotropic, hence `[Nonempty k]` there.
- `card k = card n`: `S` is a permutation matrix (`√(n/k) = 1`), the Gram matrix is `Uᴴ U` surely, and
  every bound holds.
- `card n = 0`: then `card k = 0` or the law is `0`; `hdom` is vacuous and `U` has no rows, so
  `d = 0`.
- `L ≤ 0` (Sketching): `hdom` forces every score to `0`, so `d = 0` (as S4); no `0 < L`. In the
  Probability tails `0 < L` stays (P5a's hypothesis; `L ≤ 0` with `hle` forces every atom to `0`).
- `ε ≥ 1`: the injection is vacuous (`isSubspaceInjection_of_nonpos`), so the lower half needs no
  `ε < 1`; the simplified upper exponent needs `ε ≤ 1` (S4 Q4).
- Rank-deficient `U`: everything is about `range U`, `d = U.rank` (S4 §8 item 9).
- The comparison with `k` empty: both sides are `f 0`. With `μ` non-probability in §3.2's kernel lemma:
  only `SFinite` is used (Jensen is applied fibrewise, to the Markov `κ a`).

### 3.1 `Probability/Distributions/UniformInjection.lean` (6)

`{k n : Type*} [Fintype k] [Fintype n] [MeasurableSpace n] [MeasurableSingletonClass n]`; the
measurable space on `k → n` is `MeasurableSpace.pi`, discrete because `k` is finite (§7 Q2).
```lean
/-- The uniform law on injections `k → n` (sampling `card k` indices without replacement, in order)
is a probability measure when `card k ≤ card n`. -/
theorem isProbabilityMeasure_uniformOn_injective (hk : Fintype.card k ≤ Fintype.card n) :
    IsProbabilityMeasure (uniformOn {f : k → n | Function.Injective f})
/-- Junk value: with no injection, the law is the zero measure. -/
theorem uniformOn_injective_of_card_lt (hk : Fintype.card n < Fintype.card k) :
    uniformOn {f : k → n | Function.Injective f} = 0
/-- Each injection has mass `1 / (card n)_(card k)`, the falling factorial. -/
theorem uniformOn_injective_singleton {f : k → n} (hf : Function.Injective f) :
    uniformOn {f : k → n | Function.Injective f} {f} =
      ((Fintype.card n).descFactorial (Fintype.card k) : ℝ≥0∞)⁻¹
/-- Invariance under relabelling the population. -/
theorem map_perm_comp_uniformOn_injective (σ : Equiv.Perm n) :
    (uniformOn {f : k → n | Function.Injective f}).map (fun f => ⇑σ ∘ f) =
      uniformOn {f : k → n | Function.Injective f}
/-- Invariance under reordering the sample. -/
theorem map_comp_perm_uniformOn_injective (τ : Equiv.Perm k) :
    (uniformOn {f : k → n | Function.Injective f}).map (fun f => f ∘ ⇑τ) =
      uniformOn {f : k → n | Function.Injective f}
/-- **One draw without replacement is uniform.** -/
theorem map_eval_uniformOn_injective (hk : Fintype.card k ≤ Fintype.card n) (j : k) :
    (uniformOn {f : k → n | Function.Injective f}).map (fun f => f j) = uniformOn (Set.univ : Set n)
```
Proofs: `isProbabilityMeasure_uniformOn` with finiteness and `Function.Embedding.nonempty_of_card_le`;
the junk value from `Set.eq_empty_iff_forall_notMem` (`Fintype.card_le_of_injective`) and
`uniformOn_empty_meas`; the singleton mass by `uniformOn_singleton` and the cardinality
`Fintype.card_embedding_eq` through `Equiv.subtypeInjectiveEquivEmbedding`; invariance by
`Measure.ext_of_singleton`, the preimage of `{f}` being `{σ⁻¹ ∘ f}` (resp. `{f ∘ τ⁻¹}`), injective
iff `f` is; the marginal by `Measure.ext_of_singleton` and counting: `{f | f j = i}` among injections
has `(card n - 1)_(card k - 1)` elements, or, shorter, by the invariance in `σ` (every `i` has the same
mass, `Equiv.swap`) and total mass `1`. These replace the prototype's counting and marginal files
(`UniformSamplingCounts`, `UniformSamplingMarginals`), as the brief expects.

### 3.2 `Probability/ConvexOrder.lean` (2)

`{α β E : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} [NormedAddCommGroup E]
[NormedSpace ℝ E] [CompleteSpace E] {s : Set E} {f : E → ℝ}`.
```lean
/-- **Convex order from a conditional barycenter.** If a Markov kernel `κ` moves `μ` to `κ ∘ₘ μ` and
`Y` has barycenter `X a` under each `κ a`, then `∫ f ∘ X ∂μ ≤ ∫ f ∘ Y ∂(κ ∘ₘ μ)` for every `f` convex
and continuous on a closed set `s` holding the values of `Y`. Jensen in each fibre, then integration
in `a`. This is the easy direction of Strassen's theorem; proved without a literature source beyond
Jensen, and said so in the docstring (brief D16). Result: convex-order-barycenter (new) -/
theorem _root_.ConvexOn.integral_comp_le_integral_comp_of_integral_eq (hf : ConvexOn ℝ s f)
    (hfc : ContinuousOn f s) (hs : IsClosed s) {μ : Measure α} [SFinite μ] {κ : Kernel α β}
    [IsMarkovKernel κ] {X : α → E} {Y : β → E} (hY : ∀ᵐ a ∂μ, Integrable Y (κ a))
    (hYs : ∀ᵐ a ∂μ, ∀ᵐ b ∂(κ a), Y b ∈ s) (hbar : ∀ᵐ a ∂μ, ∫ b, Y b ∂(κ a) = X a)
    (hfX : Integrable (fun a => f (X a)) μ) (hfY : Integrable (fun b => f (Y b)) (κ ∘ₘ μ)) :
    ∫ a, f (X a) ∂μ ≤ ∫ b, f (Y b) ∂(κ ∘ₘ μ)
/-- **Hoeffding's comparison**: a population sum sampled without replacement is dominated in convex
order by the same sum sampled with replacement. [Hoeffding1963, Theorem 4] (there scalar, `f`
continuous and convex; locator unverified, the paper is not in hand); [GrossNesme2010] (the matrix
form; locator unverified). Here any real Banach space and any `f` convex and continuous on a closed
convex `s` holding every with-replacement sum. Port of the prototype's
`integral_uniform_subset_convex_le_iid` (there on `ExactRowSubset`, `PMF`, `Fin k`, `s = univ`).
Result: hoeffding-sampling-without-replacement (new) -/
theorem _root_.ConvexOn.integral_uniformOn_injective_le_integral_pi {k n : Type*} [Fintype k]
    [Fintype n] [MeasurableSpace n] [MeasurableSingletonClass n] (hf : ConvexOn ℝ s f)
    (hfc : ContinuousOn f s) (hs : IsClosed s) (hk : Fintype.card k ≤ Fintype.card n) (A : n → E)
    (hA : ∀ J : k → n, ∑ j, A (J j) ∈ s) :
    ∫ ι, f (∑ j, A (ι j)) ∂uniformOn {ι : k → n | Function.Injective ι} ≤
      ∫ J, f (∑ j, A (J j)) ∂Measure.pi fun _ : k => uniformOn (Set.univ : Set n)
```
Proof of the kernel form: `ConvexOn.map_integral_le` at each `κ a` (probability, `hYs`, `hY`, and the
fibrewise integrability of `f ∘ Y` from `hfY`), giving `f (X a) ≤ ∫ b, f (Y b) ∂(κ a)` a.e. by
`hbar`; `integral_mono_ae` with `hfX` and `hfY.integral_comp`-type integrability; then
`∫ a, ∫ b, f (Y b) ∂(κ a) ∂μ = ∫ b, f (Y b) ∂(κ ∘ₘ μ)` (private helper, §1).

Proof of Hoeffding's comparison: the kernel form with `α = β = k → n`, `μ = uniformOn {injective}`,
`X ι = ∑ j, A (ι j)`, `Y J = ∑ j, A (J j)`, and a private kernel `κ ι := ρ.map (fun π => ι ∘ π)`
(`Kernel.ofFunOfCountable`), where `ρ` is a law on patterns `π : k → k`:
1. *Factorisation.* For `card k ≤ card n` every `J : k → n` is `e_J ∘ π_J` for some injection `e_J`
   whose range contains that of `J` (choice; `Finset.exists_superset_card_eq`) and some
   `π_J : k → k`. Let `ρ` be the law of `τ ∘ π_J` for `J` uniform on `k → n` and `τ` uniform on
   `Equiv.Perm k`, independent (local `⊤` on `Perm k`).
2. *Barycenter.* `∫ ∑ j, A (ι (π j)) ∂ρ = ∑ l, c l • A (ι l)` with `c l` the `ρ`-mean of
   `card (π ⁻¹' {l})`. Left composition by `τ` preserves `ρ`, so `c` is constant; `∑ l, c l = card k`,
   so `c l = 1`, and the barycenter is `X ι` (for `k` nonempty; empty `k` is trivial).
3. *Marginal.* `κ ∘ₘ μ` is the law of `ι ∘ τ ∘ π_J`; `ι ∘ τ` is again uniform and independent of
   `J` (§3.1, right invariance); for each fixed `J` the law of `σ ∘ e_J`, `σ` uniform on `Perm n`, is
   the uniform injection (private: invariant under `Perm n` by left invariance, and transitive by
   `Equiv.Perm.exists_smul_eq_embedding`, so all masses are equal), whence the law is that of
   `σ ∘ e_J ∘ π_J = σ ∘ J`, uniform on `k → n` (left composition by `σ` is a bijection), which is
   `Measure.pi fun _ => uniformOn univ` by `uniformOn_pi`.
4. Integrability is automatic (finite measures on finite discrete spaces); `hYs` is `hA`.
The prototype's coupling (support extension, one uniform permutation, explicit conditional weights) is
the same mathematics on subsets; steps 1 to 3 replace its 29 counting and weight declarations with one
private law and three invariance facts.

### 3.3 `Probability/MatrixConcentration/ChernoffWithoutReplacement.lean` (6)

`{Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜] {k m n : Type*}
[Fintype k] [Fintype m] [Fintype n] [DecidableEq m] [MeasurableSpace n] [MeasurableSingletonClass n]
{ι : Ω → k → n} {X : n → Matrix m m 𝕜} {L δ : ℝ}`;
`(hι : HasLaw ι (uniformOn {f : k → n | Function.Injective f}) μ) (hL : 0 < L) (hpsd) (hle)` as in §2.
In this paragraph `V := ((Fintype.card k : ℝ) / Fintype.card n) • ∑ i, X i`, the mean of the sum; the
Lean statements write it out.
```lean
theorem integrable_re_trace_exp_sum_of_hasLaw_uniformOn_injective (hι) (θ : ℝ) :
    Integrable (fun ω => RCLike.re (exp (θ • ∑ j, X (ι ω j))).trace) μ
/-- **The trace bound without replacement**: the sum over a uniform injection has the matrix Chernoff
trace bound of the i.i.d. sum with the same mean, `E tr exp (θ Y) ≤ tr exp ((e^{θL} - 1)/L • V)` for
every `θ`; the hypothesis `htr` of the trace-form tails of `MatrixConcentration/Chernoff`.
[GrossNesme2010]; [Tropp2011a, proof of Theorem 2.2] (locators unverified); [Tropp2015, Matrix
Concentration: Resources] cites both. -/
theorem integral_re_trace_exp_sum_le_of_hasLaw_uniformOn_injective (hι) (hL) (hpsd) (hle) (θ : ℝ) :
    ∫ ω, RCLike.re (exp (θ • ∑ j, X (ι ω j))).trace ∂μ ≤
      RCLike.re (exp (((Real.exp (θ * L) - 1) / L) •
        (((Fintype.card k : ℝ) / Fintype.card n) • ∑ i, X i))).trace
/-- **Matrix Chernoff without replacement, upper tail**, source form.
[Tropp2011a, Theorem 2.2] (locator unverified); [Tropp2015, Theorem 5.1.1] (the i.i.d. form).
Result: matrix-chernoff-without-replacement (new) -/
theorem measureReal_eigenvalue_zero_sum_ge_le_chernoff_of_hasLaw_uniformOn_injective [Nonempty m]
    (hι) (hL) (hpsd) (hle) (hδ : 0 ≤ δ) :
    μ.real {ω | (1 + δ) * eigenvalue (((Fintype.card k : ℝ) / Fintype.card n) • ∑ i, X i) 0 ≤
        eigenvalue (∑ j, X (ι ω j)) 0} ≤
      Fintype.card m * (Real.exp δ / (1 + δ) ^ (1 + δ)) ^
        (eigenvalue (((Fintype.card k : ℝ) / Fintype.card n) • ∑ i, X i) 0 / L)
/-- Lower tail, source form, `0 ≤ δ < 1`. Result: matrix-chernoff-without-replacement (new) -/
theorem measureReal_eigenvalue_sum_le_le_chernoff_of_hasLaw_uniformOn_injective (hι) (hL) (hpsd)
    (hle) {j : ℕ} (hj : j + 1 = Fintype.card m) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    μ.real {ω | eigenvalue (∑ j', X (ι ω j')) j ≤
        (1 - δ) * eigenvalue (((Fintype.card k : ℝ) / Fintype.card n) • ∑ i, X i) j} ≤
      Fintype.card m * (Real.exp (-δ) / (1 - δ) ^ (1 - δ)) ^
        (eigenvalue (((Fintype.card k : ℝ) / Fintype.card n) • ∑ i, X i) j / L)
-- simplified forms, from the source forms as in ChernoffSum (§5.2 rule 6):
-- `measureReal_eigenvalue_zero_sum_ge_le_card_mul_exp_of_hasLaw_uniformOn_injective [Nonempty m]
--    (hι) (hL) (hpsd) (hle) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)`, bound `card m * exp (-δ ^ 2 * eigenvalue V 0 / (3 * L))`;
-- `measureReal_eigenvalue_sum_le_le_card_mul_exp_of_hasLaw_uniformOn_injective (hι) (hL) (hpsd) (hle)
--    (hj) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)`, bound `card m * exp (-δ ^ 2 * eigenvalue V j / (2 * L))` (2)
```
Proofs. Integrability: `HasLaw.integral_comp`'s companion on a finite law (the integrand factors
through `ι`). Trace bound:
1. `card n < card k`: `uniformOn_injective_of_card_lt` and `HasLaw` give `μ = 0`; the left side is
   `0` and the right side is nonnegative (`Matrix.IsHermitian.re_trace_exp_pos`, or `0` for empty
   `m`).
2. Otherwise transport to the law by `HasLaw.integral_comp`; apply §3.2's comparison with
   `f A = re (tr (exp (θ • A)))`, `s = {A | A.PosSemidef}` (closed, `isClosed_setOf_posSemidef`;
   convex, `convex_setOf_posSemidef`; `f` convex there by `convexOn_re_trace_exp` composed with
   `θ • ·` and restricted; continuous under `L2Operator`), `hA` by `Matrix.posSemidef_sum`.
3. On `Measure.pi fun _ => uniformOn univ` the summands `J ↦ X (J j)` are independent (`iIndepFun_pi`),
   PSD, `≤ L • 1`, with mean `(card n)⁻¹ • ∑ i, X i` (`measurePreserving_eval`, `uniformOn_univ`);
   `hasMatrixMGFBound_of_posSemidef_of_le` and `HasMatrixMGFBound.integral_re_trace_exp_sum_le`,
   with `∑ j, (card n)⁻¹ • ∑ i, X i = V`.
Tails: for `card k ≤ card n`, `μ` is a probability measure (§3.1 and `HasLaw`), and the trace-form
tails `…_of_integral_le` apply with `Y ω = ∑ j, X (ι ω j)` (a.s. Hermitian, sums of PSD) and the PSD
`V`; otherwise `μ = 0`. Each simplified form is the public `…_card_mul_exp_of_integral_le` applied
to the same trace bound, so `Chernoff.lean`'s private scalar inequalities are not needed here.

### 3.4 `Sketching/Sampling/WithoutReplacement.lean` (13)

`{Ω} {mΩ} {μ : Measure Ω} {𝕜} [RCLike 𝕜] {k n r : Type*} [Fintype k] [Fintype n] [Fintype r]
[DecidableEq n] {S : Ω → Matrix k n 𝕜} {U : Matrix n r 𝕜} {L ε δ : ℝ}`;
`(hS : HasLaw S (samplingSketchWithoutReplacement k n) μ)`,
`(hdom : ∀ i, leverageScore U i ≤ L * (Fintype.card n : ℝ)⁻¹)`.
```lean
variable (k n) in
/-- The **law of the row-sampling sketch without replacement**: the pushforward by
`samplingSketchMatrix` at uniform weights of a uniform injection `ι : k → n`; row `j` of the sketch
is `√(card n / card k) e_{ι j}ᴴ`, the sketch is `√(n/k) • Pᴴ` for the selection `P`. The measurable
space on `n` is `⊤` inside the definition (S4 §8 item 1); `…_eq_map` restates it under any measurable
space with measurable singletons, `…_eq_sum_smul_dirac` as a finite mixture. The zero measure when
`card n < card k`. D10; [HalkoMartinssonTropp2011, §4.6] (the `R` of the SRFT);
[MartinssonTropp2020, §9.6.2] (mentioned there, not analysed). -/
noncomputable def samplingSketchWithoutReplacement : Measure (Matrix k n 𝕜) :=
  letI : MeasurableSpace n := ⊤
  (uniformOn {ι : k → n | Function.Injective ι}).map
    (samplingSketchMatrix fun _ => (Fintype.card n : ℝ≥0)⁻¹)
instance isFiniteMeasure_samplingSketchWithoutReplacement :
    IsFiniteMeasure (samplingSketchWithoutReplacement (𝕜 := 𝕜) k n)
theorem isProbabilityMeasure_samplingSketchWithoutReplacement (hk : Fintype.card k ≤ Fintype.card n) :
    IsProbabilityMeasure (samplingSketchWithoutReplacement (𝕜 := 𝕜) k n)
theorem samplingSketchWithoutReplacement_eq_sum_smul_dirac [DecidableEq k] :
    samplingSketchWithoutReplacement (𝕜 := 𝕜) k n =
      ∑ e : k ↪ n, ((Fintype.card n).descFactorial (Fintype.card k) : ℝ≥0∞)⁻¹ •
        Measure.dirac (samplingSketchMatrix (fun _ => (Fintype.card n : ℝ≥0)⁻¹) e)
theorem samplingSketchWithoutReplacement_eq_map [MeasurableSpace n] [MeasurableSingletonClass n] :
    samplingSketchWithoutReplacement (𝕜 := 𝕜) k n =
      (uniformOn {ι : k → n | Function.Injective ι}).map
        (samplingSketchMatrix fun _ => (Fintype.card n : ℝ≥0)⁻¹)
/-- D4's bridge from the user's own injection. -/
theorem hasLaw_samplingSketchMatrix_of_hasLaw_uniformOn_injective [MeasurableSpace n]
    [MeasurableSingletonClass n] {ι : Ω → k → n}
    (hι : HasLaw ι (uniformOn {f : k → n | Function.Injective f}) μ) :
    HasLaw (fun ω => (samplingSketchMatrix (fun _ => (Fintype.card n : ℝ≥0)⁻¹) (ι ω) : Matrix k n 𝕜))
      (samplingSketchWithoutReplacement k n) μ
/-- Isotropic: each draw is uniform (`map_eval_uniformOn_injective`). -/
theorem isIsotropicSketch_of_hasLaw_samplingSketchWithoutReplacement [Nonempty k] (hS)
    (hk : Fintype.card k ≤ Fintype.card n) : IsIsotropicSketch S μ
/-- Lower half, D2's fixed-`U` injection, S4's exponent `2L`. [Tropp2011a, Theorem 2.2] (locator
unverified); [Tropp2015, Theorem 5.1.1, (5.1.5), weakened after (5.1.8)] (the i.i.d. form). -/
theorem hasSubspaceInjection_of_hasLaw_samplingSketchWithoutReplacement (hS) (hdom) (hε : 0 ≤ ε) :
    HasSubspaceInjection S U (1 - ε) (U.rank * Real.exp (-ε ^ 2 * Fintype.card k / (2 * L))) μ
/-- Upper half, `0 ≤ ε ≤ 1`; [Tropp2015, Theorem 5.1.1, (5.1.6)] with `ε - (1 + ε) log (1 + ε) ≤ -ε²/3`. -/
theorem hasSubspaceEmbedding_zero_of_hasLaw_samplingSketchWithoutReplacement (hS) (hdom)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    HasSubspaceEmbedding S U 0 (1 + ε) (U.rank * Real.exp (-ε ^ 2 * Fintype.card k / (3 * L))) μ
/-- **Row sampling without replacement**, any `U`, any `L` dominating the scaled leverage scores.
Sampling without replacement is never worse than with (`hasSubspaceEmbedding_of_hasLaw_samplingSketch`
at uniform weights, the same bound). [Tropp2011a, Theorem 2.2 and Lemma 3.4] (the sampling step of
the SRHT; locators unverified). Result: sampling-without-replacement-ose (new) -/
theorem hasSubspaceEmbedding_of_hasLaw_samplingSketchWithoutReplacement (hS) (hdom) (hε : 0 ≤ ε)
    (hε1 : ε ≤ 1) : HasSubspaceEmbedding S U (1 - ε) (1 + ε)
      (2 * U.rank * Real.exp (-ε ^ 2 * Fintype.card k / (3 * L))) μ
/-- Coherence as the constant, `L = coherence U`. [MartinssonTropp2020, §9.6.2] (with replacement). -/
theorem hasSubspaceEmbedding_coherence_of_hasLaw_samplingSketchWithoutReplacement (hS) (hε : 0 ≤ ε)
    (hε1 : ε ≤ 1) : HasSubspaceEmbedding S U (1 - ε) (1 + ε)
      (2 * U.rank * Real.exp (-ε ^ 2 * Fintype.card k / (3 * coherence U))) μ
-- sizes, S4's quantities (no new named quantity):
theorem hasSubspaceEmbedding_of_hasLaw_samplingSketchWithoutReplacement_of_samplingSize_le (hS) (hdom)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hk : samplingSize U.rank L ε δ ≤ Fintype.card k) :
    HasSubspaceEmbedding S U (1 - ε) (1 + ε) δ μ
theorem hasSubspaceInjection_of_hasLaw_samplingSketchWithoutReplacement_of_samplingInjectionSize_le
    (hS) (hdom) (hε : 0 < ε) (hδ : 0 < δ) (hk : samplingInjectionSize U.rank L ε δ ≤ Fintype.card k) :
    HasSubspaceInjection S U (1 - ε) δ μ
```
Proofs. Law: as S4 §8 item 1. The uniform injection is the finite sum
`∑ ι, uniformOn {…} {ι} • dirac ι` (`Measure.ext_of_singleton` on the finite `k → n`), with masses
from `uniformOn_injective_singleton` and the injections reindexed by `k ↪ n` through
`Equiv.subtypeInjectiveEquivEmbedding`; then the map of a finite sum of Diracs (`mapₗ_apply_of_measurable`,
`map_dirac`), with `samplingSketchMatrix _` measurable by `measurable_of_countable` under the local
`⊤`. The bridge is `HasLaw.comp`. Isotropy: S4's Gram identity at `A = B = 1`, each `ι j` uniform
(§3.1), so `∫ Sᴴ S = ∑ j, (card n / card k) • (card n)⁻¹ • 1 = 1`; `memLp` since the entries take
finitely many values. Fixed `U`:
1. As S4 §3.2 step 1: reduce to orthonormal `Q` with the range of `U` (S1's `of_range_le` both
   ways, `leverageScore_eq_of_range_eq`), `d = 0` and empty `k` directly; `hdom` becomes
   `‖Q i‖² ≤ L / card n`.
2. S1's `HasLaw.hasSubspaceInjection_iff` twice, to `uniformOn {injective}` under the local `⊤`
   (the definition), with `ι = id` and `HasLaw.id`.
3. Population atoms `X i := ((card n : ℝ) / card k) • vecMulVec (star (Q i)) (Q i)`: PSD, `≤ (L / card k) • 1`
   (`specNorm_vecMulVec` and `hdom`), with `((card k : ℝ) / card n) • ∑ i, X i = Qᴴ Q = 1`; the Gram
   matrix is `∑ j, X (ι j)` by S4's `conjTranspose_samplingSketchMatrix_mul_mul`.
4. §3.3's simplified tails at `L / card k`, `j + 1 = d`, `eigenvalue 1 = 1`; the events as in S4 §3.2
   step 4; two-sided by S1's `HasSubspaceInjection.hasSubspaceEmbedding` and `exp (-x/2) ≤ exp (-x/3)`.
5. Coherence: `hdom` from `leverageScore_le_coherence_mul_inv`. Sizes: S4's `samplingSize_le` and
   `samplingInjectionSize_le`, the `log` inversion of S4's corollaries, verbatim.

## 4. Files

27 statements, about 1150 lines against the brief's 900 (the brief's two files plus the two topic
files of §7 Q1). Sequential in the order below (each imports the one before); 1 and 2 form a short
import chain and may go to one agent (CONTRIBUTING §11).
1. `Probability/Distributions/UniformInjection.lean` (6 theorems); imports
   `Mathlib.Probability.UniformOn`, `Mathlib.Data.Fintype.CardEmbedding`. About 200 lines.
2. `Probability/ConvexOrder.lean` (2 theorems, the private pattern law and kernel); imports 1,
   `Mathlib.Analysis.Convex.Integral`, `Mathlib.Probability.Kernel.Composition.IntegralCompProd`,
   `Mathlib.GroupTheory.GroupAction.MultipleTransitivity`. About 350 lines.
3. `Probability/MatrixConcentration/ChernoffWithoutReplacement.lean` (6 theorems); imports 2,
   `MatrixConcentration/{Chernoff,MGFBound}`, `Matrix/Functions/TraceFunctions`,
   `Matrix/Inequalities/Order`, `ForMathlib/LinearAlgebra/Matrix/PosDef`. About 200 lines.
4. `Sketching/Sampling/WithoutReplacement.lean` (13: 1 definition, 1 instance, 11 theorems); imports 3,
   `Sketching/Sampling/RowSampling` (S4), `Sketching/Properties/{FixedSubspace,Isotropic}`. About 400
   lines.
Bibliography: new keys `Hoeffding1963`, `GrossNesme2010`, `Tropp2011a` (the last fixed by D16; added
here if S6 has not), all with unverified locators (§7 Q10).

## 5. Material

Read: the prototype's `Sketching/Sampling/{SamplingWithoutReplacement,SamplingWithoutReplacementTails}.lean`
and the seven `Uniform*` files (`UniformCollision`, `UniformIidSampling`, `UniformProduct`,
`UniformSamplingCounts`, `UniformSamplingCoupling`, `UniformSamplingJensen`,
`UniformSamplingMarginals`): 1138 lines, 56 declarations, `ℂ`, `Fin d`, `Fin k`, `PMF`, the subset
type `ForMathlib/Data/ExactRowSubset` (`{T : Finset α // T.card = k}`), `lambdaMax`/`lambdaMin`,
`traceExp`, `open scoped Classical`, `maxHeartbeats 600000`; the atlas entries `srht-ose`,
`matrix-chernoff`, `matrix-chernoff-sampling`; Tropp 2015 Theorem 5.1.1 and its "Matrix Concentration:
Resources" notes on [GN] and [Tro11d]; MT §9.6.2; HMT §4.6 and §11. Ledger (prototype to here):
- `SamplingWithoutReplacement.lean` (2): `integral_traceExp_uniform_subset_le_iid` is step 2 of the
  trace bound (§3.3), not a statement; `integral_traceExp_uniform_iid_le` is P5a's
  `HasMatrixMGFBound.integral_re_trace_exp_sum_le` (exists), not ported.
- `SamplingWithoutReplacementTails.lean` (4): `integral_traceExp_uniform_subset_le` to
  `integral_re_trace_exp_sum_le_of_hasLaw_uniformOn_injective`; `matrix_chernoff_uniform_subset_upper`,
  `_lower` to the simplified tails (the `(1/k) •` normalisation and `lambdaMax`/`lambdaMin` replaced by
  `V` and `eigenvalue`; `hmean : (1/n) • ∑ A = 1` dropped, any mean); `measure_norm_uniform_subset_sub_one_le`
  not ported (§6).
- `UniformSamplingJensen.lean` (5): `uniformExactRowSubsetPMF` to Mathlib's `uniformOn {injective}`
  (D10); `…_toReal_apply` to `uniformOn_injective_singleton`; `uniform_subset_average_convex_le_iid`,
  `integral_uniform_subset_convex_le_iid` to `ConvexOn.integral_uniformOn_injective_le_integral_pi`;
  `sum_uniformSubset_mul_conditionalWeight` to step 3 of §3.2 (private).
- `UniformSamplingCoupling.lean` (13, MIT-licensed adaptation of Heidary's SRHT coupling, credited in
  the docstring of the private construction if any of its code is reused): `toReal_map_pmf_apply`,
  `sum_toReal_pmf`, `toReal_map_pmf_invariant` not ported (`PMF` bookkeeping; `Measure.map`);
  `card_image_univ_sequence_le`, `sequenceSupportExtension`, `image_univ_subset_…` are step 1's
  factorisation; `permuteExactRowSubset`, `…Equiv`, `exists_perm_exactRowSubset` to Mathlib's
  `Equiv.Perm.exists_smul_eq_embedding`; `iidSubsetOutcome`, `iidSubsetJointPMF`, `…_support_subset`,
  `…_eq_zero_of_not_subset` replaced by the private pattern law.
- `UniformSamplingCounts.lean` (16): `sequenceLabelCount` and its two lemmas, `sum_sequence_eq_sum_count_smul`
  are step 2's count (private); `iidSubsetConditionalWeight` and its four lemmas,
  `iidSubsetExpectedCount` and its six lemmas, `permuteExactRowSubset_swap_eq`,
  `sum_conditionalWeight_smul_sequence_sum` replaced by the invariance argument of step 2.
- `UniformSamplingMarginals.lean` (10): `permuteSequenceEquiv`, `iidSubsetSourceAct`, `iidSubsetPairAct`,
  `iidSubsetOutcome_act`, `iidSubsetJointPMF_toReal_invariant` replaced by
  `map_perm_comp_uniformOn_injective` and `map_comp_perm_uniformOn_injective`;
  `iidSubsetJointPMF_toReal_first_marginal`, `iidSubsetMarginal`, `_invariant`, `_eq`, `_eq_uniform` are
  step 3 (private).
- `UniformProduct.lean` (3): `uniform_function_toMeasure_eq_pi` is Mathlib's `uniformOn_pi`;
  `iIndepFun_uniform_sequence_comp` is `iIndepFun_pi`; `integral_uniform_sequence_comp_eval` is P2's
  `integral_samplingMeasure` with `samplingMeasure_const_inv_card`. None ported.
- `UniformIidSampling.lean` (1): `measure_norm_uniform_iid_sub_one_le` is P5a's
  `measureReal_specNorm_sum_sub_one_ge_le` (exists) and, for the sketch, S4's uniform corollary.
- `UniformCollision.lean` (2): hash collisions of CountSketch, S7's material; ledgered there.
- `ForMathlib/Data/ExactRowSubset.lean` (outside the nine; 2): not ported here (D10's injections). Its
  other user, Cauchy–Binet's index type, is a Matrix-layer matter.
Result ids: `convex-order-barycenter`, `hoeffding-sampling-without-replacement`,
`matrix-chernoff-without-replacement`, `sampling-without-replacement-ose` (all new); `srht-ose` stays
with S6.

## 6. Cut, and why

- Subsets in place of injections (D10), `PMF` in place of `Measure`, `Fin` sizes, `ℂ`-only statements,
  `s = univ` on `selfAdjoint` subtypes (the prototype's `convexOn_traceExp_smul_selfAdjoint` route):
  the closed convex `s` of §3.2 takes the PSD cone directly.
- A convex-order predicate, the conditional-expectation twin of §3.2's kernel form (Mathlib's
  `ConvexOn.map_condExp_le_of_finiteDimensional` with `integral_condExp` gives it in three lines when
  a consumer holds a conditional expectation), and a public Hoeffding kernel (§7 Q3, Q4).
- The two-sided population form `ε ≤ ‖Y/k - 1‖` (prototype `measure_norm_uniform_subset_sub_one_le`):
  the sketch goes through S1's union lemma; a population consumer joins the two halves as
  `measureReal_specNorm_sum_sub_one_ge_le` does. Chernoff means without replacement: no consumer.
- Finite-population improvements (Serfling-type factors `1 - (k - 1)/n`): no source in hand, no matrix
  analogue in Chernoff form, and the comparison gives exactly the i.i.d. tails; a sharper form would be
  a new theorem named by its parameter (§5.2 rule 4), never a rename.
- Non-uniform weights without replacement: the comparison is Hoeffding's for the uniform case only;
  there is no law here that a consumer asked for.
- AMM without replacement (exact variance with the factor `(n - k)/(n - 1)`): no consumer; S4's AMM is
  with replacement.
- Scalar Hoeffding and Bernstein without replacement (§3.2 at `f = exp (θ ·)` with P1's tails): no
  consumer this round; one short corollary when one appears.
- `S Sᴴ = (card n / card k) • 1` and `specNorm S = √(n/k)` for the injective sketch: no consumer this
  round; S6 adds them for the SRHT if it needs them.
- Oblivious forms (OSE, OSI): the tail is in `coherence U`, which is `card n` in the worst case; S6's
  flattening supplies the oblivious statement.

## 7. Questions and decisions

**For the maintainer:** none. No decision here is hard to reverse in the brief's sense (an interface
every later theorem takes, a carrier, a naming scheme, a global instance): the carrier of the law is
fixed by D10, the interfaces are S1's, the domination hypothesis is D8's. The costliest to change
later is Q9 (the law's name), cheap now and moderate after S6; the orchestrator should settle it before
S6's skeleton. **Decisions taken** (open to correction): all.

**Q1. Four files, not two.** The brief lists `Probability/ConvexOrder.lean` and
`Sampling/WithoutReplacement.lean`. Added: `Probability/Distributions/UniformInjection.lean` (the law's
API; S6 and the deferred OSNAP use it without the comparison) and
`Probability/MatrixConcentration/ChernoffWithoutReplacement.lean` (a population theorem with no
sketch, in the layer and directory of `ChernoffSum`, whose sibling `Chernoff.lean` was written for it).
*Alternative:* the brief's two files, with the law API in `ConvexOrder.lean` and the population tails in
the Sketching file; rejected because LowRank's column sampling without replacement would import a
sketch file for a matrix-concentration fact. Not hard to reverse (file moves).

**Q2. Instances on the population index in Probability statements.** §3.1 to §3.3 carry
`[MeasurableSpace n] [MeasurableSingletonClass n]`, as P2's `samplingMeasure` does: `uniformOn` on
`k → n` is Mathlib's measure and needs a measurable space, and these statements are about a random
index, not a data matrix. The Sketching law fixes `⊤` inside its body (S4 §8 item 1), so no statement
of Sketching or above carries an instance on `n`. *Alternative:* a named law `uniformInjection k n`
with `⊤` inside; rejected (D10: "no new definition"; a second spelling of `uniformOn`). Not hard to
reverse: only S5's and S6's proofs use the Probability statements.

**Q3. The comparison's generality.** D10's kernel form, in a real Banach space (Mathlib's Jensen needs
completeness, not finite dimension; D10's finite-dimensional space is an instance), any `f` convex and
continuous on a closed `s`, hypotheses fibrewise and almost everywhere. `hfX` (integrability of `f ∘ X`)
is kept: it follows only through a supporting hyperplane and measurability of `f ∘ X`, and every
consumer has it from finiteness. No convex-order predicate: each consumer instantiates one `f`, and a
predicate quantifying over all convex `f` would need integrability fields that fail for unbounded laws.
The two theorems have no NLAlib vocabulary; they stay in Probability per D10, declared
`_root_.ConvexOn.…` for dot notation (CONTRIBUTING §3), and the module docstring marks them as
upstream candidates. Not hard to reverse (a predicate later is additive).

**Q4. The Hoeffding kernel is private.** Only the comparison is public. The pattern law `ρ` and the
kernel are proof devices; the deferred sparse coupling (§4a) is a different kernel and reuses only
§3.2's kernel form. Making them public later is additive.

**Q5. Hoeffding's comparison takes `hk` and a closed convex `s` holding every with-replacement sum.**
`hk` is needed (§3, degenerate cases). `s = univ` would exclude `re tr exp`, which is convex only on
Hermitian matrices; `hA : ∀ J, ∑ j, A (J j) ∈ s` is the weakest form that makes the fibrewise Jensen
apply, and the PSD cone discharges it by `Matrix.posSemidef_sum`.

**Q6. S4's exponents and sizes, no new quantity.** The tails without replacement are those with
replacement (`2L` lower, `3L` upper, `2 d · 3L` two-sided), which is what the comparison gives (and,
as recalled, what Tropp 2011a's Theorem 2.2 states; unverified, Q10); `samplingSize` and
`samplingInjectionSize` are reused, so a consumer inverts one size for both models. Source forms are
stated only in Probability (§3.3), as in P5a; the sketch has the simplified forms, as S4 (S4 Q4).

**Q7. Domination at uniform weights with a free `L`.** `hdom : ∀ i, leverageScore U i ≤ L * (card n)⁻¹`
is D8's hypothesis at `p = 1/n`, in the shape of `leverageScore_le_coherence_mul_inv`. S6's flattening
yields exactly this (row norms of `H D U` at most `L / n`); the `coherence U` form is a corollary.
*Alternative:* `coherence U ≤ L`; rejected, since S6 would pass through `ciSup_le`.

**Q8. No `card k ≤ card n` on the tails.** The zero law forces `μ = 0` and the tails hold (§3); the
hypothesis appears where the statement is false without it (probability measure, marginal, isotropy,
the comparison of two measures). Minimal hypotheses, CONTRIBUTING §5.2.

**Q9. Names.** The law `samplingSketchWithoutReplacement k n` (`𝕜` implicit), with S4's constructor
`samplingSketchMatrix` at uniform weights and no constructor of its own: S6's `√(n/k) Pᵀ` is that
constructor on an injection (S4 §0). Alternatives: `uniformSubsetSketch` (but the law is on ordered
injections, D10), `subsampleSketch` (vague). Theorems as S4's with the law's name; the coherence
corollary is `…_coherence_of_hasLaw_…` (S4's `_const_inv_card` names the weights, and here there is only
one law). Probability names spell the conclusion with the suffix `_of_hasLaw_uniformOn_injective`, as
ChernoffSum's tails do without the suffix. The mixture lemma sums over `k ↪ n` (cardinality
`Fintype.card_embedding_eq`) rather than a filtered `Finset` of maps (no `DecidablePred Injective`
in the statement). Cheap now, not after S6.

**Q10. Literature and unverified locators.** Not in hand: Hoeffding 1963 (Theorem 4, the comparison;
locator from the prototype and the standard citation, unverified), Gross and Nesme 2010
(arXiv:1001.2738, the matrix form; no theorem number cited), Tropp 2011a (Theorem 2.2, matrix Chernoff
without replacement, and Lemma 3.4, the sampling step; numbers from memory and the atlas, unverified;
the atlas's `matrix-chernoff-sampling` entry cites "Thm 2.2" but describes an i.i.d. sample, which
disagrees, so the number is checked against the paper before it enters a docstring, or the docstring
cites the paper without a number). Confirmed in hand: Tropp 2015, Theorem 5.1.1, and its "Matrix
Concentration: Resources" section, which describes [GN] as extending Hoeffding's method to matrices and
[Tro11d] as combining it with Theorem 5.1.1 for PSD matrices sampled without replacement; MT §9.6.2,
which mentions sampling without replacement as better but harder to analyse; HMT §4.6, whose SRFT
selects columns without replacement. The kernel form (§3.2) is proved without a literature source
beyond Jensen and says so (D16).

**Q11.** About 1150 lines against the brief's 900 (§4; the prototype's 1138 less two foreign files and
the subset type). **Q12.** `[DecidableEq k]` appears only on the mixture lemma (`Fintype (k ↪ n)`); the
invariance lemmas take the permutation as a parameter and need none; `[DecidableEq n]` is already in
S4's variables.

## 8. Amendments from the review (2026-10-15)

Fable review of this note (0 blocker, 2 major, 11 minor), all thirteen amendments accepted by the
orchestrator, A1 as corrected on inspection of the now fully proved S4 file (item 1); Q9 decided
(the name stands), nothing for the maintainer. The review verified the mathematics and the
constants (Chernoff parameter `L / card k`, `V = 1`, `2L` lower, `3L` upper, `2d` two-sided, against
the atom bound and `(card k / card n) • ∑ i, X i = Qᴴ Q`), the degenerate cases, Hoeffding's
comparison in the kernel form (fibrewise `ConvexOn.map_integral_le`, no conditional expectation),
that ordinary trace convexity suffices (`OperatorConvexOn` is not needed), the match of §3.3's
hypotheses with P5a's `…_of_integral_le` tails, the four files and Q2, and that no statement is
improperly dominated. Where an item below contradicts §0 to §7, it supersedes them; §3 stays as
drafted. Skeletons: the files of item 15, every new proof `sorry`; the promotions of item 1 carry
S4's proofs and stay proved.

1. **A1, reuse of S4's reduction (major), corrected on inspection.** `RowSampling.lean` is now
   fully proved, so the route of §3.4 has been executed once and the review's scaffold contingency
   is moot. S4's proof also corrects two points of the review. Its lemma (a) is not the form needed:
   the reduction uses `range U ≤ range Q` and one `.of_range_le`, not `of_range_le` "both ways".
   And S1's `HasOrthonormalCols.hasSubspaceInjection_of_measureReal_le` (FixedSubspace.lean,
   line 115) takes a smallest-singular-value tail, not a `specNorm` tail (that is the line-102
   lemma); with `sq_singularValues` (`Matrix/Spectral/SingularValues`) and the Gram identity
   `conjTranspose_samplingSketchMatrix_mul_mul` it is exactly Chernoff's lower eigenvalue event, so
   the lower inclusion needs no new lemma. Only the upper inclusion is missing. The S5 skeleton step
   makes public, before S5's own files, these five, each with S5 as a consumer; S4's public
   statements do not change, its proofs are rerouted through them, and its files stay `sorry`-free.
   (a) `RowSampling.lean`, as is:
       `exists_hasOrthonormalCols_of_leverageScore_le (hdom : ∀ i, leverageScore U i ≤ L * p i) :
       ∃ Q : Matrix n (Fin U.rank) 𝕜, HasOrthonormalCols Q ∧ LinearMap.range U.mulVecLin ≤
       LinearMap.range Q.mulVecLin ∧ ∀ i, ‖WithLp.toLp 2 (Q i)‖ ^ 2 ≤ L * p i`. Docstring: an
       orthonormal `Q` whose range contains that of `U` and whose rows inherit the domination,
       `‖Q i‖² ≤ L p i`; the reduction of every fixed-`U` row-sampling tail, with or without
       replacement, to orthonormal columns. S5 applies it at `p = fun _ => (card n : ℝ≥0)⁻¹`,
       `hdom` converted by `NNReal.coe_inv` and `NNReal.coe_natCast` as in `…_const_inv_card`.
   (b) `RowSampling.lean`, as is (already flagged in S4's skeleton notes):
       `rank_le_of_leverageScore_le (hp : ∑ i, p i = 1) (hdom : ∀ i, leverageScore U i ≤ L * p i) :
       (U.rank : ℝ) ≤ L`. Docstring: under leverage domination with weights summing to one the rank
       is at most the domination constant; it gives `0 < L` for the Chernoff call when `U ≠ 0`. S5
       uses it in the `d ≥ 1` branch, where `n` is nonempty and the uniform weights sum to one.
   (c) `RowSampling.lean`, `samplingAtom_le` restated by row vector and weight rather than by
       `(j, ι)`, the sample count a real scale:
       ```lean
       theorem inv_mul_smul_vecMulVec_star_self_le [DecidableEq r] {c L : ℝ} {w : ℝ≥0}
           (hc : 0 ≤ c) (hL : 0 ≤ L) {b : r → 𝕜} (hb : ‖WithLp.toLp 2 b‖ ^ 2 ≤ L * w) :
           (c * w)⁻¹ • Matrix.vecMulVec (star b) b ≤ (L / c) • (1 : Matrix r r 𝕜)
       ```
       Docstring: the importance-weighted rank-one atom of row sampling,
       `(c w)⁻¹ • vecMulVec (star b) b` for `c` samples and weight `w`, is at most `L / c` in the Loewner order when `‖b‖² ≤ L w` (junk
       `w = 0` or `c = 0`: both sides `0`); the `hle` of matrix Chernoff. S4 applies it at
       `c = card k`, `b = Q (ι j)`, `w = p (ι j)`; S5 at `b = Q i`, `w = (card n)⁻¹`.
   (d) `ForMathlib/LinearAlgebra/Matrix/ConjTranspose.lean`, not `RowSampling.lean` (no NLAlib
       vocabulary, absent from Mathlib, CONTRIBUTING §2): the general form of the private
       `conjTranspose_mul_self_eq_sum_vecMulVec`,
       `Matrix.conjTranspose_mul_eq_sum_vecMulVec (A : Matrix n q α) (B : Matrix n r α) :
       Aᴴ * B = ∑ i, vecMulVec (star (A i)) (B i)`, in the generality of its Mathlib neighbour
       `conjTranspose_vecMulVec`. Docstring: the cross-Gram matrix is the sum of the rank-one
       products of the rows; upstream candidate for `Mathlib.LinearAlgebra.Matrix.ConjTranspose`.
       It replaces both private copies in S4 (that one, and `sum_vecMulVec_star_eq_conjTranspose_mul`
       in `MatrixMultiplication.lean`, used reversed). S5: the mean identity of item 2 step 3.
   (e) `Sketching/Properties/FixedSubspace.lean`, beside its line-115 sibling, not
       `RowSampling.lean` (no sampling content):
       ```lean
       theorem HasOrthonormalCols.hasSubspaceEmbedding_zero_of_measureReal_le [IsFiniteMeasure μ]
           [Fintype p] [DecidableEq p] (hU : HasOrthonormalCols U)
           (h : μ.real {ω | b ≤ singularValues (S ω * U) 0 ^ 2} ≤ δ) :
           HasSubspaceEmbedding S U 0 b δ μ
       ```
       Docstring: **from a largest-singular-value tail**: for `U` with orthonormal columns,
       `P(b ≤ σ_max(S U)²) ≤ δ` gives the upper half `(S U)ᴴ (S U) ≤ b • Uᴴ U` with failure
       probability `δ`, the lower constant `0` holding surely; the form matrix Chernoff's upper tail
       produces. No `[Nonempty p]` (for empty `p` the failure event is empty). Its proof is the
       inclusion inside S4's private `hasSubspaceEmbedding_zero_samplingSketchMatrix`.
   Private, with reasons: `samplingAtom` (no public definition: (c) states the atom as an
   expression, which is S5's `X i` at uniform weights up to beta reduction);
   `posSemidef_samplingAtom` (one term, Mathlib's `posSemidef_vecMulVec_star_self` with `.smul`);
   `iIndepFun_samplingAtom`, `sum_integral_samplingAtom` (about `Measure.pi … samplingMeasure`,
   which S5 never sees: its i.i.d. side is inside §3.3 on a generic `X`); `eq_zero_of_norm_sq_le`
   (zero weights; uniform weights are positive); `measureReal_not_isSubspaceEmbedding_zero` (a
   `simp` on the definitions); and the two product-space tails, which become Chernoff on
   `Measure.pi` plus S1's line-115 lemma (lower) or (e) (upper) and have no second law to serve.
   §1's "used directly" gains (a) to (e) and `sq_singularValues`. S4's note gets a dated skeleton
   note recording the promotions when they land.
2. **§3.4 fixed-`U` proof, restated with item 1.**
   1. `card n < card k`: `μ = 0`. Otherwise `μ` is a probability measure. `d = 0`: the failure
      event is empty. `d ≥ 1`: `n` is nonempty, the uniform weights sum to one, `0 < L` by (b),
      `Q` by (a); empty `k` as S4 (`measureReal_le_one`, bound `≥ 1`).
   2. S1's `HasLaw.hasSubspaceInjection_iff` (resp. `…Embedding_iff`) twice under the local `⊤`
      (`hS`, then `hasLaw_samplingSketchMatrix_of_hasLaw_uniformOn_injective HasLaw.id`); the
      conclusion by `.of_range_le` once.
   3. Atoms `X i := ((card k : ℝ) * ((card n : ℝ≥0)⁻¹ : ℝ≥0))⁻¹ • vecMulVec (star (Q i)) (Q i)`,
      S4's atom at uniform weights, so the Gram identity is `conjTranspose_samplingSketchMatrix_mul_mul`
      verbatim (the draft's `(card n / card k) •` is the value, not the spelling); `hpsd` by
      `posSemidef_vecMulVec_star_self`, `hle` by (c) at `c = card k`, the mean
      `((card k : ℝ) / card n) • ∑ i, X i = Qᴴ Q = 1` by (d) and cancelling scalars.
   4. Lower: §3.3's simplified lower tail at `L / card k`, `j + 1 = d`, `eigenvalue_one`, fed to
      S1's line-115 lemma after `simp only [sq_singularValues, conjTranspose_samplingSketchMatrix_mul_mul]`
      on its event. Upper: the same, fed to (e). Two-sided as drafted.
3. **A2, citations (major, process).** Until the locators are checked against the papers, the
   docstrings of §3.2 to §3.4 cite `[Tropp2011a]`, `[Hoeffding1963]`, `[GrossNesme2010]` by key
   only, naming the paper in prose and giving no theorem, lemma or section number (D16's fallback);
   the i.i.d. comparison keeps `[Tropp2015, Theorem 5.1.1]`, which is in hand. Every "locator
   unverified" of the drafted docstrings goes. The three keys are added to `docs/references.bib`
   before any docstring cites them (`check_refs.py`; `Tropp2011` is the Freedman paper, D16).
   Locators to verify, then add as labels:
   - Tropp 2011a, "Improved analysis of the subsampled randomized Hadamard transform" (Adv. Adapt.
     Data Anal. 3, 2011): Theorem 2.2, matrix Chernoff for sampling without replacement (§3.3's
     tails, §3.4's halves and OSE); its proof, attributed to Gross and Nesme (§3.3's trace bound);
     Lemma 3.4, uniform row subsampling of an orthonormal `W` with `M = n max_j ‖e_jᵀ W‖²` (§3.4's
     OSE); Lemma 3.3, flattening (S6); Theorem 2.1, the i.i.d. form (not cited here).
   - Hoeffding 1963, "Probability inequalities for sums of bounded random variables" (J. Amer.
     Statist. Assoc. 58): Theorem 4, the comparison for continuous convex `f` (§3.2).
   - Gross and Nesme 2010, "Note on sampling without replacing from a finite collection of
     matrices" (arXiv:1001.2738): the number of the matrix comparison or trace-exponential bound
     (§3.2, §3.3).
   The atlas's `matrix-chernoff-sampling` "disagreement" is the atlas's (it describes the
   prototype's i.i.d. theorem), not evidence against Theorem 2.2.
4. **A3, §3.1 singleton mass.** Mathlib's `uniformOn_singleton` conditions on a singleton; it is
   not the mass of one. The mass is `uniformOn` unfolded to `cond_apply` with
   `Measure.count_singleton` and `Measure.count_apply_finite` (or `uniformOn_apply_finset` on
   `Finset.univ.filter Injective` under `classical`); the count is `Fintype.card (k ↪ n)` through
   `Equiv.subtypeInjectiveEquivEmbedding` and `Fintype.card_embedding_eq`. §1's list and §3.1's and
   §3.4's proofs read so.
5. **A4, no `[DecidableEq k]`.** `samplingSketchWithoutReplacement_eq_sum_smul_dirac` drops it:
   Mathlib's `Function.Embedding.fintype` takes no decidability. Q12 now reads: no `[DecidableEq k]`
   anywhere in S5.
6. **A5, the kernel's Markov instance.** `Kernel.ofFunOfCountable` has no `IsMarkovKernel` instance
   in Mathlib. The private kernel supplies it by hand, `⟨fun ι => inferInstance⟩` once each
   `ρ.map _` is a probability measure.
7. **A6, counting in place of permutation measures.** No measure on `Equiv.Perm`. `ρ` is the finite
   mixture `∑ τ, ∑ J, c • dirac (τ ∘ π_J)` with `c = ((card k)! * card n ^ card k)⁻¹` in `ℝ≥0∞`;
   §3.2 step 3's uniformity of `σ ∘ e_J` is a fibre count (each fibre `{σ | σ ∘ e = g}` is a coset
   of the stabiliser of `e`, nonempty by `Equiv.Perm.exists_smul_eq_embedding`). §1's remark on a
   local `⊤` for `Perm n` and step 1's local `⊤` on `Perm k` go. A proof-length matter only.
8. **A7, file and result id of the kernel form.** D10 is followed: both theorems stay in
   `Probability/ConvexOrder.lean`, as `_root_.ConvexOn.…` marked as upstream candidates. CONTRIBUTING
   §2 permits but does not require `ForMathlib/Analysis/Convex/Integral.lean`, and D10 names the
   file; the kernel form's consumer here is Hoeffding's comparison, which needs §3.1's law, so
   splitting the pair across layers buys nothing. `Result: convex-order-barycenter` is dropped
   (§6.4): the docstring says "the easy direction of Strassen's theorem (Strassen 1965, not in
   hand, D16); proved from Jensen's inequality". Result ids: `hoeffding-sampling-without-replacement`,
   `matrix-chernoff-without-replacement`, `sampling-without-replacement-ose`.
9. **A8, Q3 records the generalisation of D10.** D10 asks for values in a finite-dimensional real
   vector space; the statement takes a real Banach space, which is what `ConvexOn.map_integral_le`
   needs, and contains D10's case.
10. **A9, §3.3 trace bound case split.** First `card n < card k` (`μ = 0`), then empty `k` (the
    sum is `0`, the bound `re tr exp 0 ≤ re tr exp (c • 0)` with equality), then
    `haveI : Nonempty n` for `iIndepFun_pi`'s probability instances on `uniformOn univ`.
11. **A10, names in §1 and §3.3.** `Matrix.isClosed_setOf_posSemidef`,
    `NLAlib.convex_setOf_posSemidef`, Mathlib's `Matrix.posSemidef_sum`. `HasLaw.integral_comp` is
    Mathlib's (with an `AEStronglyMeasurable` hypothesis); its integrability companion is NLAlib's
    `HasLaw.integrable_comp_iff` or `Integrable.of_finite` on the law. The kernel proof's
    integrability is `Measure.integrable_comp_iff`, `Measure.ae_integrable_of_integrable_comp` and
    `Measure.integrable_integral_norm_of_integrable_comp`; the Bochner `∫ ∂(κ ∘ₘ μ) = ∫∫` is
    `Measure.comp_eq_comp_const_apply` with the kernel `ProbabilityTheory.integral_comp`, as drafted.
12. **A11, §3.3 continuity.** The `L2Operator` topology is the Pi topology, so
    `Matrix.isClosed_setOf_posSemidef` applies as is; continuity of `exp` is obtained as in
    `Chernoff.lean` (line 164, `open scoped Matrix.Norms.Operator in exact NormedSpace.exp_continuous`),
    since `L2Operator` has no `NormedAlgebra` instance for `exp_continuous` to see.
13. **A12, §0 table.** The consumer cell of the sketch row reads "S6, which supplies the sections
    lemma (D11) and applies the fixed-`U` theorems at `H * diagonal ξ * U` for each sign vector".
    SRHT isotropy is `IsIsotropicSketch.mul`; §6's cut of `S Sᴴ` and `specNorm S` is confirmed (S6
    needs neither).
14. **A13, §3 degenerate list.** Added: `card n = 0 = card k`, where `uniformOn (univ : Set n) = 0`
    but the empty `Measure.pi` is `dirac`; Hoeffding's comparison holds (both sides `f 0`) and is
    settled by the empty-`k` case first, not by `uniformOn_pi`.
15. **Files** (amends §4). S5's four files keep their counts, 27 statements:
    1. `Probability/Distributions/UniformInjection.lean` (6).
    2. `Probability/ConvexOrder.lean` (2).
    3. `Probability/MatrixConcentration/ChernoffWithoutReplacement.lean` (6).
    4. `Sketching/Sampling/WithoutReplacement.lean` (13); imports also the ForMathlib file of (d)
       if `RowSampling` does not bring it.
    Promotions of item 1, done first: `Sketching/Sampling/RowSampling.lean` (25 to 28: (a), (b),
    (c)), `Sketching/Properties/FixedSubspace.lean` (+1: (e)),
    `ForMathlib/LinearAlgebra/Matrix/ConjTranspose.lean` (+1: (d)); `MatrixMultiplication.lean`
    loses a private duplicate, no statement change. In all, 32 statements.
16. §7: Q1, Q2, Q4 to Q8 and Q11 stand; Q3 is amended by items 8 and 9, Q9 is decided (the name
    `samplingSketchWithoutReplacement` is accepted), Q10 by item 3, Q12 by item 5.
