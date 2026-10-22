# Design note: consolidation of re-proved helpers

**Approved by the maintainer, 2026-10-22:** D1 as recommended (option (a)); every other item as recommended.

Draft of 2026-10-21, for `docs/design/Consolidation.md`. Branch `cleanup/consolidation` (worktree
`nlalib-block`, head `572999b`). Nothing was edited or built while drafting.

**What this round is.** It adds no new mathematics. Each fact that an upper layer re-proves
privately, or that two files prove twice, becomes one public lemma in the file where its topic
lives (CONTRIBUTING §3, "a lemma a second file could want is public"; rule S5; placement, §8 item
5). The copies are deleted. A hypothesis that exists only because a fact was private is dropped.
Where Mathlib already has the fact, the copy is deleted and the call site uses Mathlib (§1 rule 3).

**How the scope was checked.** The orchestrator's list and the four gap surveys
(`scratchpad/gaps/{matrix-polynomial,probability,sketching-regression,lowrank-krylov}.md`,
entries marked duplicates, private, workaround or misplaced) were checked against the code by four
read-only agents. Each agent compared statements verbatim, searched Mathlib, and checked that every
proposed home is importable by every user (transitive imports, no layer violation, no cycle). I
spot-checked their main claims. Two more sources:
* `python3 scripts/check_rules.py --only S5 --warnings --warn` lists 34 warnings: 17
  same-name private pairs.
* A list of all 1,731 private declarations with their signatures,
  `scratchpad/consol/privs.txt`, was swept by layer.

**Summary.**
* **New public declarations: 49.**
  * 14 in ForMathlib, 3 of which (F6) can be dropped;
  * 18 in Matrix, counting `IsQR.isUnit`, which goes public;
  * 5 in Polynomial and 1 in Krylov;
  * 2 in Probability, 7 in RandomMatrix and 2 in Estimation.
* **Private copies and inline re-proofs deleted or shrunk: about 60.** About 20 more are deleted in
  favour of an existing Mathlib or library lemma (§3.1, F7).
* **Public statement changes: 1**, `[Finite n]` dropped from
  `conjTranspose_mul_mul_le_conjTranspose_mul_mul`. `IsUnit R` stays on all three Regression
  `IsQR` theorems (§3.3).
* **Public removals: 1.** **Moves: 2**, `rademacherMatrix` and its instance; their names stay.
* **Size.** Roughly 900 lines deleted and 300 added. This is an estimate with about ±30%
  uncertainty.
* **The S5 checker goes from 17 same-name pairs to 0.**

**Premises of the brief that turned out wrong** (details in §3 and §7):
1. **`IsQR.isUnit` (private, `Matrix/Factorizations/QR.lean:77`) assumes `∀ i, R i i ≠ 0`, not
   injectivity.** The three Regression theorems that carry `hR : IsUnit R` do not carry it because
   of that privacy:
   * In `IsQR.sketchAndPrecondition_eq_mulVec_cgIterate` and `IsQR.iterativeSketching_succ` the
     hypothesis is genuine; counterexamples are in §3.3.
   * In `IsSubspaceEmbedding.pseudoConditionNumber_mul_inv_sq_le_of_isQR` it could be dropped
     only through the junk value `R⁻¹ = 0`. §5.2 says a theorem excludes the junk value by
     hypothesis, and the three `IsQR` theorems keep one hypothesis list, so it stays.
   * What the three really share is the hand-rebuilt identity $\mathbf{A}\mathbf{R}^{-1} = \mathbf{Q}$.
     It is rebuilt in 5 places, and it becomes public (`IsQR.mul_inv_eq`).
2. **The complementary-frame lemma is not one statement proved six times.** It is three
   statements:
   * frames adapted to a projector: 3 copies;
   * a complement with no projector: 2 copies;
   * a wrapper of an existing public lemma: 1 copy.
3. **The Kaczmarz private lemmas are not instances of the sketch-and-project ones.** Kaczmarz is
   indexed by rows, sketch-and-project by sketch matrices. Kaczmarz's measurability and
   `DependsOn` lemmas already call the public sketch-and-project ones. The two files share only a
   scalar power bound.
4. **The Hanson–Wright sub-exponential MGF has no consumer outside its file.**
   Girard–Hutchinson's tail goes through a block-diagonal quadratic form, and the MGF route would be
   longer. It stays private.
5. **Two of the listed Polynomial facts are not proved anywhere** outside Polynomial: the
   Chebyshev-residual recurrence and Jackson's theorem on an interval. They would be new
   mathematics, so they are out of scope.
6. **Two same-name pairs from the S5 checker are different statements:** `continuous_pullback`
   and `re_quadForm_smul_add_smul`. So are `extendFin` and, nearly, `exists_eigencoordinates`.

## Decisions for the maintainer

There is one. Everything else proceeds as recommended, because it is an internal API or a
placement that is cheap to change later.

**D1. The shape and names of the public conditioning lemma.** It will be the most-used lemma of
this round. It is the step "integrate out an independent factor", used by every two-sketch proof:
the Gaussian Chevet bounds, generalized Nyström, early truncation, Hutch++ and future XTrace. Its
hypothesis shape fixes every call site. The §5.3 row "independent test matrices" names the
Bochner equality `ProbabilityTheory.IndepFun.integral_comp_eq_integral_integral` as the
conditioning spelling. The amendment is an addition to that row's bridge column only: the
spelling (`IndepFun S G μ`) and the row's text do not change.

* **(a) Recommended.** Four lemmas in `ForMathlib/Probability/Independence/Basic.lean`, namespace
  `ProbabilityTheory` (signatures in §3.1, F1):
  * `IndepFun.lintegral_comp_eq_lintegral_lintegral_of_hasLaw`, the `ℝ≥0∞` equality
    $\int^- f(U, W)\,d\mu = \int^- \int^- f(U(\omega), w)\,d\nu(w)\,d\mu(\omega)$ for measurable
    $f \ge 0$, with no integrability hypothesis;
  * `IndepFun.lintegral_ofReal_comp_eq_lintegral_ofReal_integral`, its corollary for real
    $F \ge 0$ with the inner Bochner integral (the form the Nyström copies use);
  * `IndepFun.integrable_comp_of_integral_le`;
  * `IndepFun.integral_comp_le_of_integral_le`.

  The name `…_of_hasLaw` (a generic law $\nu$, so no `<law>` token after it, rule N9) is part of
  the decision.

  Their properties:
  * The law of the integrated factor is a `HasLaw W ν μ` hypothesis, so the inner integral is
    against the named law (`gaussianMatrix`, `haarFrame`). The other factor only needs
    `AEMeasurable U μ`.
  * The inner hypotheses are almost-sure in `ω`, `∀ᵐ ω ∂μ, … U ω …`. A caller with a pointwise
    bound passes `ae_of_all`. Generalized Nyström's almost-sure rank hypothesis fits directly,
    which deletes its transfer to `μ.map U`.
  * The bound `H : Ω → ℝ` is any integrable function, not a function of `U`. This drops the
    `Measurable H` that the private copy needs.
  * The conjunction "integrable ∧ ≤" is split into two theorems (rule T11: integrability is useful
    alone).
* **(b)** Pointwise hypotheses `∀ x, …` with `H : α → ℝ` and `Measurable H`: the private copy in
  `TruncatedGeneralizedNystrom.lean:205` made public as it stands. This is simpler to read, but
  the generalized Nyström copies keep their almost-sure transfer, and every caller proves
  `Measurable H`.
* **(c)** One conjunction lemma, `IndepFun.integrable_and_integral_comp_le`, the private name
  without `_of_indepFun`, and no `ℝ≥0∞` form (the corollary is derived from the map-measure lemma
  `IndepFun.lintegral_comp_eq_lintegral_lintegral`, :66, at each use). It has fewer names, but
  rule T11 warns on it.

Also in F1, not part of the decision: `IndepFun.integrable_comp_iff`, the transfer of
integrability between $\mu$ and the product of the two laws. With it, the Bochner equality
already in the §5.3 row covers the remaining equality-form users, and the public duplicate in
`GaussianIntegrationByParts.lean` can go.

Recommendation: **(a)**.

## 1. Objects

No new definitions. No §5.3 row is added. The one row amended is "independent test matrices":
its bridge column adds the F1 lemmas, and nothing else in the row changes (D1).

`rademacherMatrix` and `isProbabilityMeasure_rademacherMatrix` move from
`Sketching/Gaussian/Rademacher.lean` to a new `RandomMatrix/Rademacher/Basic.lean` (§3.6, R1).
Their full names `NLAlib.rademacherMatrix` and `NLAlib.isProbabilityMeasure_rademacherMatrix` do
not change, so this is not a rename.

No Mathlib deviation is introduced or removed, so `docs/design/Mathlib-deviations.md` is unchanged.

## 2. Interfaces

No new hypothesis predicate or structure. The F1 lemmas are API of Mathlib's `IndepFun` and
`HasLaw`.

## 3. Statement shapes

Conventions for this section:
* Each table row gives the new public declaration, its home, and the copies it replaces
  (file:line in `NLAlib/`, current lines).
* Signatures are written with the binders the home file's `variable` line does not already supply.
  Matrix files supply `{𝕜 : Type*} [RCLike 𝕜] {m n p : Type*} [Fintype _]`.
* Docstrings follow §6. These are helpers and bridges, so they carry no citation and no `Result:`
  id.
* Names follow §4.

### 3.1 ForMathlib (layer −1)

**F1. Conditioning on an independent factor.** Home: `ForMathlib/Probability/Independence/Basic.lean`.
The file's variables are `{Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}`, namespace
`ProbabilityTheory`. The new lemmas go after `IndepFun.integral_comp_eq_integral_integral` (:128).
The file needs `public import Mathlib.Probability.HasLaw`, which is legal at layer −1 (the sibling
`InfinitePi.lean` already has it).

```lean
/-- Integrating out an independent factor, in `ℝ≥0∞`: if $W$ has law $\nu$ and is independent
of $U$, and $f \ge 0$ is measurable, then
$\int^- f(U, W)\,d\mu = \int^- \int^- f(U(\omega), w)\,d\nu(w)\,d\mu(\omega)$. -/
theorem IndepFun.lintegral_comp_eq_lintegral_lintegral_of_hasLaw [IsFiniteMeasure μ]
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {U : Ω → α} {W : Ω → β}
    {ν : Measure β} (hUW : IndepFun U W μ) (hU : AEMeasurable U μ) (hW : HasLaw W ν μ)
    {f : α × β → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, f (U ω, W ω) ∂μ = ∫⁻ ω, ∫⁻ w, f (U ω, w) ∂ν ∂μ

/-- The real form of `IndepFun.lintegral_comp_eq_lintegral_lintegral_of_hasLaw`: if $W$ has law
$\nu$ and is independent of $U$, and $F \ge 0$ is measurable with $F(U(\omega), \cdot)$ integrable for almost every
$\omega$, then
$\int^- F(U, W)\,d\mu = \int^- \bigl(\int F(U(\omega), w)\,d\nu(w)\bigr)\,d\mu(\omega)$. -/
theorem IndepFun.lintegral_ofReal_comp_eq_lintegral_ofReal_integral [IsFiniteMeasure μ]
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {U : Ω → α} {W : Ω → β}
    {ν : Measure β} (hUW : IndepFun U W μ) (hU : AEMeasurable U μ) (hW : HasLaw W ν μ)
    {F : α × β → ℝ} (hF : Measurable F) (hF0 : ∀ q, 0 ≤ F q)
    (hint : ∀ᵐ ω ∂μ, Integrable (fun w => F (U ω, w)) ν) :
    ∫⁻ ω, ENNReal.ofReal (F (U ω, W ω)) ∂μ = ∫⁻ ω, ENNReal.ofReal (∫ w, F (U ω, w) ∂ν) ∂μ

theorem IndepFun.integrable_comp_of_integral_le [IsFiniteMeasure μ] {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {U : Ω → α} {W : Ω → β} {ν : Measure β}
    (hUW : IndepFun U W μ) (hU : AEMeasurable U μ) (hW : HasLaw W ν μ) {F : α × β → ℝ}
    (hF : Measurable F) (hF0 : ∀ q, 0 ≤ F q) {H : Ω → ℝ}
    (hint : ∀ᵐ ω ∂μ, Integrable (fun w => F (U ω, w)) ν)
    (hle : ∀ᵐ ω ∂μ, ∫ w, F (U ω, w) ∂ν ≤ H ω) (hH : Integrable H μ) :
    Integrable (fun ω => F (U ω, W ω)) μ

theorem IndepFun.integral_comp_le_of_integral_le [IsFiniteMeasure μ] {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {U : Ω → α} {W : Ω → β} {ν : Measure β}
    (hUW : IndepFun U W μ) (hU : AEMeasurable U μ) (hW : HasLaw W ν μ) {F : α × β → ℝ}
    (hF : Measurable F) (hF0 : ∀ q, 0 ≤ F q) {H : Ω → ℝ}
    (hint : ∀ᵐ ω ∂μ, Integrable (fun w => F (U ω, w)) ν)
    (hle : ∀ᵐ ω ∂μ, ∫ w, F (U ω, w) ∂ν ≤ H ω) (hH : Integrable H μ) :
    ∫ ω, F (U ω, W ω) ∂μ ≤ ∫ ω, H ω ∂μ

theorem IndepFun.integrable_comp_iff [IsFiniteMeasure μ] {α β E : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [NormedAddCommGroup E] {U : Ω → α} {W : Ω → β}
    (hUW : IndepFun U W μ) (hU : AEMeasurable U μ) (hW : AEMeasurable W μ) {f : α × β → E}
    (hf : AEStronglyMeasurable f ((μ.map U).prod (μ.map W))) :
    Integrable (fun ω => f (U ω, W ω)) μ ↔ Integrable f ((μ.map U).prod (μ.map W))
```

* **Proof route** for the `ℝ≥0∞` equality: Tonelli (`IndepFun.lintegral_comp_eq_lintegral_lintegral`,
  :66), then `hW.map_eq`, then `lintegral_map'` applied to the measurable
  $g(u) = \int^- f(u, w)\,d\nu$ (`Measurable.lintegral_prod_right'`).
* The real form is that lemma at $f = \operatorname{ofReal} \circ F$, then
  `ofReal_integral_eq_lintegral_ofReal` a.e. in $\omega$. That last step is why `hint` is
  almost-sure in $\omega$ and needs no measurable set.
* The two `≤` lemmas follow by `lintegral_mono_ae`. $H \ge 0$ a.e. comes from `hF0` and `hle`.
* `hint` could be dropped from the integral `≤`: a non-integrable left side is $0$. Keep it unless
  the proof gets shorter without it.
* Mathlib: searched `Probability/Independence` and `Probability/HasLaw` for iterated integrals and
  `integral_comp`. It has only the product-law facts (`IndepFun.hasLaw_prod`,
  `indepFun_iff_map_prod_eq_prod_map_map`).

Replaced copies:

| copy | kind | becomes |
|---|---|---|
| `LowRank/Gaussian/TruncatedGeneralizedNystrom.lean:189` `lintegral_comp_le_of_indepFun` | private, 14 lines | deleted (its one use takes the F1 equality and `lintegral_mono`) |
| `LowRank/Gaussian/TruncatedGeneralizedNystrom.lean:205` `integrable_and_integral_comp_le_of_indepFun` | private, 17 lines, 2 uses | deleted; the call sites' `have hH : Measurable …` blocks go too |
| `RandomMatrix/Gaussian/SpectralNorm.lean:410` `lintegral_specNorm_mul_mul_le`, `:498` `lintegral_specNorm_mul_mul_sq_le` | private, 34 and 30 lines | deleted. The public proofs at :448, :467 and :539 become about 3 lines each, with $U = Y$, $W = X$, $\nu$ = `gaussianMatrix`, and `hint`/`hle` from the fixed-factor public lemmas at `HasLaw.id` |
| `Probability/QuadraticForm/HansonWright/OffDiagonal.lean:195` `lintegral_comp_eq_lintegral_lintegral` | private copy of the public :66 in $\omega$-form (same short name) | deleted; it is `IndepFun.lintegral_comp_eq_lintegral_lintegral_of_hasLaw` at `hW : HasLaw W (μ.map W) μ` plus one `lintegral_map'` on the inner integral; add the import |
| `Probability/Distributions/GaussianIntegrationByParts.lean:230` `NLAlib.integral_comp_eq_integral_integral_of_indepFun` | **public** duplicate; 2 uses, both in that file (:433, :437) | **removed**. Uses become `hUW.symm.integral_comp_eq_integral_integral` with `f := fun p => F (p.2, p.1)` and `IndepFun.integrable_comp_iff`; add the import |
| `Estimation/Trace/HutchPlusPlus.lean:243` `integral_comp_eq_integral_integral_of_norm_le` | private, 15 lines, 2 uses | deleted; uses become :128 plus `integrable_comp_iff` and the domination. If the `integral_map` rewrites make the call sites longer, a 3-line local wrapper may stay |
| `RandomMatrix/Gaussian/Moments.lean:110` `lintegral_frobNorm_mul_mul_sq_of_isIsotropic_of_indepFun` | private, 28 lines, 2 uses | shrinks to the F1 equality plus the fixed-factor identity (stays private, single file) |
| `LowRank/Gaussian/GeneralizedNystrom.lean:142` and `:417`; `LowRank/Gaussian/EarlyTruncation.lean:153`; `LowRank/Gaussian/EarlyTruncationHaar.lean:125` (the `lintegral_frobNorm_sub_…_sq[_haar]` privates) | private, about 30 lines each | each shrinks to about 10 lines: F1 equality, then the fixed-design identity. They stay private because their statements use LowRank vocabulary |

**F2. A.e. monotonicity of `μ.real`.** Home: a new `ForMathlib/MeasureTheory/Measure/Real.lean`,
named after Mathlib's `MeasureTheory/Measure/Real.lean`, namespace `MeasureTheory`, written in
Mathlib's style beside `measureReal_mono`:
```lean
theorem measureReal_mono_ae {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {s t : Set α}
    (h : s ≤ᵐ[μ] t) (ht : μ t ≠ ∞ := by finiteness) : μ.real s ≤ μ.real t
```
It replaces:
* `LowRank/Gaussian/RangeFinderTail.lean:92` `measureReal_le_of_ae_imp` (private);
* `Probability/MatrixConcentration/Freedman.lean:65` `measureReal_mono_ae'` (private, 4 uses);
* inline copies at `Probability/MatrixConcentration/Laplace.lean:119`, `:136` and
  `Probability/Tail.lean:131`.

Mathlib has `measureReal_mono` and `measureReal_mono_null` only (searched `Measure/Real.lean`).

**F3. Smooth cutoff sequence.** Home: a new `ForMathlib/Analysis/Calculus/BumpFunction/Basic.lean`,
named after Mathlib's `Analysis/Calculus/BumpFunction/Basic.lean`, in the root namespace:
```lean
theorem exists_seq_contDiff_hasCompactSupport_eventuallyEq_one {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    ∃ (χ : ℕ → E → ℝ) (K : ℝ), (∀ n, ContDiff ℝ 1 (χ n)) ∧ (∀ n, HasCompactSupport (χ n)) ∧
      (∀ n x, 0 ≤ χ n x ∧ χ n x ≤ 1) ∧ (∀ n x, ‖fderiv ℝ (χ n) x‖ ≤ K) ∧
      (∀ x, ∀ᶠ n in Filter.atTop, χ n =ᶠ[nhds x] fun _ => 1)
```
* It replaces the private `exists_cutoff` at `Probability/LogSobolev.lean:350` (46 lines) and at
  `Probability/Distributions/GaussianLogSobolev.lean:50` (41 lines). The latter is the $E = \mathbb{R}$
  case with `|deriv|`, converted by `norm_deriv_eq_norm_fderiv`.
* The instance hypotheses could probably weaken to `[NormedSpace ℝ E] [HasContDiffBump E]`; this is
  unchecked. Keep the source's.
* Mathlib: searched the ContDiffBump files and "cutoff"; none.

**F4. Power of a contraction factor.** Home: `ForMathlib/Analysis/SpecialFunctions/Log/Basic.lean`,
namespace `Real`, after `mul_pow_le_of_mul_log_le` (:184):
```lean
theorem one_sub_pow_le_of_log_le_mul {c ε : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (hε : 0 < ε) {q : ℕ}
    (hq : Real.log (1 / ε) ≤ c * q) : (1 - c) ^ q ≤ ε
```
*Amendment 2026-10-22 (A3):* `hc0 : 0 < c` is dropped; the proof does not use it (the unused-variable
linter fails the `--wfail` build), and the statement holds for every $c \le 1$.

It replaces:
* `Solvers/Kaczmarz.lean:418` `one_sub_one_div_frobPseudoConditionNumber_sq_pow_le` (private,
  21 lines; $c = 1/\kappa^2$). It becomes a 2-line corollary or is inlined.
* The inline calc at `Solvers/SketchAndProject.lean:600–610`.

**F5. Chebyshev polynomial composed with an affine map** (the shifted filter
$T_j(2x/s - 1)$). Both lemmas use only Mathlib objects, so they go in ForMathlib, namespace
`Polynomial.Chebyshev`:
```lean
-- new ForMathlib/RingTheory/Polynomial/Chebyshev.lean (Mathlib's file with `natDegree_T`)
theorem natDegree_T_comp_le {R : Type*} [CommRing R] [IsDomain R] [NeZero (2 : R)] (n : ℤ)
    {p : R[X]} (hp : p.natDegree ≤ 1) : ((T R n).comp p).natDegree ≤ n.natAbs

-- ForMathlib/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Growth.lean, after
-- `monotoneOn_eval_T_real`
theorem abs_eval_T_comp_C_mul_X_sub_one_le (n : ℤ) {s x : ℝ} (hs : 0 < s)
    (hx : x ∈ Set.Icc 0 s) : |((T ℝ n).comp (C (2 / s) * X - 1)).eval x| ≤ 1
```
*Amendment 2026-10-22 (A3):* inside `namespace Polynomial.Chebyshev` the bare `C` is Mathlib's
`Polynomial.Chebyshev.C`, so the second statement writes `Polynomial.C (2 / s)`; the statement is
the one above.

They replace three copies of the degree argument and two copies of the bound:
* `LowRank/Gaussian/BlockKrylovGapless.lean:623` `degree_T_comp_C_mul_X_sub_one_lt` and `:637`
  `abs_eval_T_comp_C_mul_X_sub_one_le` (private);
* the inline blocks at `LowRank/Gaussian/BlockKrylov.lean:283–292` and `:295–303`, inside
  `exists_rbki_filter`;
* lines 82–86 of `degree_chebyshevResidual_le` (`Polynomial/Chebyshev/Residual.lean:74`), whose
  statement stays the same.

Notes:
* **No new definition.** `chebyshevResidual 0 s j` equals the filter only up to sign, and every
  `chebyshevResidual` lemma assumes $0 < a$.
* **No public evaluation lemma.** It is `simp [eval_comp]`; the private one-liner
  `BlockKrylovGapless.lean:615` may stay.
* Not moved: the single-use privates `hasSupportingLineOn_mul_eval_T_div_sq` (:462),
  `le_mul_exp_of_mul_eval_T_sq_le` (:484) and the exp/2 lower bound in
  `exp_div_two_le_abs_eval_T_comp` (`BlockKrylov.lean:206`). Moving them is placement only, and
  `Polynomial-Chebyshev.md` "Upstreaming" already asks to take application material out of
  `Growth.lean`.
* Mathlib: searched `T_comp`, `comp (C` and `natDegree_T_le`; none.

**F6. Even part of a polynomial.** These are single-use privates of `Krylov/LinearSystems/WorstCase.lean`
about Mathlib's `Polynomial.contract` (`Mathlib/Algebra/Polynomial/Expand.lean:185`). Mathlib has
no eval or degree lemma for `contract`. Home: a new `ForMathlib/Algebra/Polynomial/Expand.lean`,
namespace `Polynomial`. This is placement (P10), not S5, so it is the last ForMathlib commit and
can be dropped.
```lean
theorem two_mul_eval_contract_two_sq {R : Type*} [CommRing R] (p : R[X]) (x : R) :
    2 * (contract 2 p).eval (x ^ 2) = p.eval x + p.eval (-x)
theorem degree_contract_le_of_degree_le {R : Type*} [Semiring R] {n : ℕ} (hn : n ≠ 0)
    {f : R[X]} {q : ℕ} (hf : f.degree ≤ q) : (contract n f).degree ≤ (q / n : ℕ)
theorem eval_zero_contract {R : Type*} [Semiring R] {n : ℕ} (hn : n ≠ 0) (f : R[X]) :
    (contract n f).eval 0 = f.eval 0
```
* These replace `WorstCase.lean:251` and `:266`, the latter split into two.
* `sum_range_two_mul` (`:241`) and the RCLike inequality `mul_norm_eval_contract_two_sq_le`
  (`:277`) stay private.

**F7. Deletions in favour of Mathlib** (no new declaration; each is a single-file edit):

| private copy | Mathlib (or existing) replacement |
|---|---|
| `Sketching/Structured/SRHT.lean:281` `hasLaw_fst_prod`, `:287` `hasLaw_snd_prod` | `measurePreserving_fst.hasLaw`, `measurePreserving_snd.hasLaw` (`Probability/HasLaw.lean:76`) |
| `Sketching/Sparse/CountSketch.lean:240` `integral_eq_of_ae_rademacherVector` | `MeasureTheory.integral_eq_const` (`Integral/Bochner/Basic.lean:963`) |
| `Probability/LogSobolev.lean:78` `integrable_exp_mul_of_abs_le` (and the `.1` of the same-name private in `Probability/BoundedDifferences.lean:72`, whose `.2` stays) | `ProbabilityTheory.integrable_exp_mul_of_mem_Icc` (`Probability/Moments/Basic.lean:500`) |
| `LowRank/Random/RangeFinder.lean:87` `integrable_comp_of_abs_le`, `Estimation/Trace/HutchPlusPlus.lean:272` `integrable_comp_of_norm_le` | `MeasureTheory.Integrable.of_bound` |
| `Regression/Embedding.lean:59` `le_div_of_mul_le'` | `(le_div_iff₀' ha).2` |
| `Matrix/Spectral/SingularValueInequalities.lean:215`, `Sketching/Gaussian/HaarEmbedding.lean:88` `conjTranspose_mul_smul_one_mul` | `simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]` |
| `Matrix/Norms/Compare.lean:42` `col_mul`, `Sketching/Properties/JohnsonLindenstrauss.lean:282` `col_mul_eq_mulVec` | `rfl` at the use (both proofs are `rfl`) |
| `Probability/MatrixConcentration/Laplace.lean:88` `re_trace_exp_smul_nonneg` (with an unneeded `hj`) | `((IsSelfAdjoint.all θ).smul hA).re_trace_exp_nonneg` (`Matrix.IsHermitian.re_trace_exp_nonneg`, `Matrix/Functions/Exponential.lean:340`) |
| `LowRank/Gaussian/RotationInvariantFactor.lean:117` `range_polarFactor` | `(rangeProjector_inj.mp (rangeProjector_polarFactor A)).symm` (`Matrix/Factorizations/PolarFrames.lean:78`) |
| `LowRank/Gaussian/Filter.lean:87–90` (hand proof of a column-selection frame) | `hZ.submatrix (Equiv.refl _) (Fin.castLE_injective hrt)` (`HasOrthonormalCols.submatrix`) |
| `RandomMatrix/Gaussian/Invariance.lean:111` `hasOrthonormalCols_conjTranspose_kronecker` | `HasOrthonormalCols.kronecker` (`Matrix/Structured/Kronecker.lean:46`) after `conjTranspose_kronecker`; add the Kronecker import |
| `LowRank/Oblivious/SubGaussian.lean:420` `frobNorm_one_kronecker_sq`, `:426` `specNorm_one_kronecker_le` | `frobNorm_kronecker` with `frobNorm_one_sq`; `specNorm_kronecker` with `specNorm_one_le` (`Kronecker.lean:312, :325`). Add `public import NLAlib.Matrix.Structured.Kronecker`. `:408` and `:486` stay private (single use) |
| `RandomMatrix/Gaussian/InverseMoments.lean:212` `exists_norm_one_sub_rangeProjector_mulVec_eq` | inline: `IsStarProjection.exists_hasOrthonormalCols_mul_conjTranspose_eq` (`Matrix/Basic/OrthonormalBasis.lean:129`) and `hV.norm_toLp_mulVec` |
| `Matrix/Functions/OperatorConvex.lean:371`, `Matrix/Functions/TracePowers.lean:336` `cfc_mul_cfc` (same name, opposite orientations) | Mathlib's `cfc_mul f g A` with both continuity arguments `A.finite_real_spectrum.continuousOn _`, the library's existing pattern (40 uses). A public wrapper would be one line, and its Mathlib-orientation name would be `cfc_mul` itself, which inside `namespace NLAlib` would shadow Mathlib's; so it is dropped (former M9) |
| `Polynomial/Approximation/Jackson.lean:96` `continuous_pullback`, and the inline `have hfc` at `Polynomial/Approximation/ChebyshevSeries.lean:72` | `hf.comp_continuous Real.continuous_cos Real.cos_mem_Icc` (`Real.cos_mem_Icc`, Mathlib `Trigonometric/Basic.lean:604`). The other `continuous_pullback` (`ChebyshevSeries.lean:167`, on `AddCircle`) is a different statement and stays |

### 3.2 Matrix (layer 0)

| # | new public declaration | home (beside) | replaces |
|---|---|---|---|
| M1 | statement change, see §3.8 | `Norms/Loewner.lean:83` | private copies `Sketching/Properties/SubspaceEmbedding.lean:99` `conjTranspose_mul_mul_le`, `Sketching/Gaussian/Haar.lean:83` `conjTranspose_mul_mul_le_conjTranspose_mul_mul'` |
| M2 | `HasOrthonormalCols.sub_mul_mul_conjTranspose_mul_eq_zero` | `Basic/Orthonormal.lean` (`mul_conjTranspose_mul_cancel_right`, :179) | `LowRank/Oblivious/RangeFinder.lean:97`, `LowRank/Structural/RangeFinder.lean:114` (same name, private), inline `LowRank/Oblivious/EarlyTruncation.lean:119–123` |
| M3a | `IsStarProjection.exists_hasOrthonormalCols_fromCols_mul_conjTranspose_eq` | `Basic/OrthonormalBasis.lean` (:129) | `RandomMatrix/Gaussian/InverseMoments.lean:582` `exists_frame_rangeProjector` (direct instance); `Regression/SketchAndSolve.lean:89` `exists_frames` (deleted: weaker than :547); `:547` `exists_compl_frames` (shrinks to a 5-line private corollary for its 3 call sites) |
| M3b | `exists_hasOrthonormalCols_fromCols` | `Subspaces/Frames.lean` (`exists_hasOrthonormalCols_of_card_le`, :69; OrthonormalBasis cannot hold it, Frames imports it) | `Sketching/Gaussian/HaarEmbedding.lean:392` `exists_complementary_frames`, `RandomMatrix/Haar/Blocks.lean:113` `exists_hasOrthonormalCols_compl` |
| M4 | `exists_hasOrthonormalCols_range_eq_range_conjTranspose_truncatedSVD` | `Spectral/LowRank.lean` (:527) | `LowRank/Oblivious/RangeFinder.lean:78` `exists_frame_head` (7 uses) and `:89` `card_frame_head_le` (inlined, 2 uses); inline `LowRank/Oblivious/SubGaussian.lean:583–591`, `LowRank/Oblivious/EarlyTruncation.lean:113–118` |
| M5a | `quadForm_mul_conjTranspose_self` | `Basic/QuadForm.lean` (`quadForm_conjTranspose_mul_self`, :138) | `Krylov/LinearSystems/MINRESRecurrence.lean:445` `sqrt_re_quadForm_eq_norm`, `Krylov/Processes/PreconditionedLanczos.lean:132` `sqrt_re_quadForm_mul_conjTranspose`; inline `MINRESLanczos.lean:83–87`, `MINRESRecurrence.lean:488–491`, `MINRES.lean:391–394` |
| M5b | `star_mulVec_dotProduct` | `Basic/QuadForm.lean` (`Matrix.IsHermitian.star_dotProduct_mulVec_comm`, :210) | `Krylov/LinearSystems/PCGRecurrence.lean:97` `star_mulVec_dotProduct`, `:105` and `CGRecurrence.lean:163` `star_dotProduct_mulVec_eq` (same name, different statements) |
| M6 | `Matrix.PosDef.exists_isUnit_eq_mul_conjTranspose` | `Spectral/Congruence.lean` (:85) | `Krylov/LinearSystems/PCGRecurrence.lean:120` `exists_factor`; the 2-line idiom (`exists_eq_mul_conjTranspose_and_eq_mul_diagonal_mul_conjTranspose hM.isHermitian` plus `isUnit_iff_isUnit_det`) at `Richardson.lean:187`, `MINRESLanczos.lean:76`, `PCG.lean:192, :240, :314`, `MINRESRecurrence.lean:556, :611`, `PreconditionedLanczos.lean:287`, `MINRES.lean:389` |
| M7 | `range_mulVecLin_mul_eq_of_range_eq` | `Basic/Projector.lean` (`range_le_iff_exists_mul`, :262) | `Krylov/LinearSystems/MinResidual.lean:72` `range_mulVecLin_mul_rangeProjector`, `Sketching/Structured/Flattening.lean:160` `range_mul_eq_of_range_eq` |
| M8 | `uncurry_mul_mul` | `Structured/Kronecker.lean` (its docstring already cites `Matrix.kronecker_mulVec_vec`) | `RandomMatrix/Gaussian/Invariance.lean:98` (ℝ), `RandomMatrix/Gaussian/Moments.lean:62` (𝕜), same name, private |
| M10 | `trace_hermitianPart` (general `𝕜` form) | `Spectral/HermitianPart.lean` (`quadForm_hermitianPart`, :96) | `Estimation/Trace/HutchPlusPlus.lean:173` (private), inline `RandomMatrix/Haar/Moments.lean:622`, `:700` |
| M11 | `specNorm_one_sub_smul_le_of_smul_one_le_hermitianPart` | `Spectral/HermitianPart.lean` (`re_quadForm_hermitianPart`, :84) | inline `hB` in `Krylov/LinearSystems/GMRES.lean:282` (Elman, about 38 lines; its iteration `hpow` becomes `specNorm_pow_le`) |
| M12 | `specNorm_aeval_le_pseudoConditionNumber_mul` | `Functions/Polynomial.lean` (`Matrix.IsHermitian.specNorm_aeval_le`, :166); add `public import NLAlib.Matrix.Pseudoinverse.ConditionNumber` (no cycle) | inline `hpA`/`hnorm` in `Krylov/LinearSystems/GMRES.lean:248` and the private `norm_toLp_eq_zero_of_isEmpty` (:234), which the empty case no longer needs |
| M13 | `IsQR.isUnit` (made public), `IsQR.isUnit_iff`, `IsQR.isUnit_iff_injective_mulVec`, `IsQR.mul_inv_eq` | `Factorizations/QR.lean`, section "What R knows" (:74) | `Q = A R⁻¹` rebuilt by hand at `QR.lean:269–272`, `Factorizations/Hessenberg.lean:341–343`, `Regression/Embedding.lean:199–201`, `Regression/SketchAndPrecondition.lean:142–144`, `Regression/IterativeSketching.lean:107–109` |
| M14 | `conjTranspose_mul_self_le_add_smul_one_of_specNorm_sub_smul_one_le`, `sub_smul_one_le_conjTranspose_mul_self_of_specNorm_sub_smul_one_le` | `Norms/Loewner.lean` (the $N = 1$ pair, :377, :390, which become corollaries without a statement change) | `RandomMatrix/SubGaussian/ExtremeSingularValues.lean:153` `isHermitian_gram_sub`, `:159`, `:166` (private, ℝ); inline `hH`/`hle` in `Spectral/SingularValueInequalities.lean:407, :436` |
| M15 | `Matrix.PosSemidef.fromBlocks_zero₁₂_zero₂₁` | `ForMathlib/LinearAlgebra/Matrix/PosDef.lean` (Mathlib vocabulary only; beside `PosSemidef.conjTranspose_mul_mul_same'`, :114) | `Factorizations/NystromOrder.lean:320` `posSemidef_fromBlocks_smul_one` (𝕜, private, 4 uses), `LowRank/Gaussian/RotationInvariantFactor.lean:109` `posSemidef_fromBlocks_smul_one'` (ℝ); at each use the smul-one case is the one-liner `(posSemidef_one.smul ha).fromBlocks_zero₁₂_zero₂₁ (posSemidef_one.smul hb)`; with `NystromOrder.lean:311` `fromBlocks_smul_one_eq_diagonal` and `LowRank/Gaussian/RotationInvariant.lean:510` `diagonal_sumElim_const` replaced by Mathlib's `Matrix.fromBlocks_diagonal` |

Signatures (Matrix files, namespace `NLAlib`):
```lean
theorem HasOrthonormalCols.sub_mul_mul_conjTranspose_mul_eq_zero {Q : Matrix m n 𝕜}
    (hQ : HasOrthonormalCols Q) (A : Matrix p m 𝕜) : (A - A * Q * Qᴴ) * Q = 0

theorem _root_.IsStarProjection.exists_hasOrthonormalCols_fromCols_mul_conjTranspose_eq
    [Fintype m] [Fintype p] [Fintype q] [DecidableEq m] [DecidableEq p] [DecidableEq q]
    {P : Matrix m m 𝕜} (hP : IsStarProjection P) (hp : Fintype.card p = P.rank)
    (hpq : Fintype.card p + Fintype.card q = Fintype.card m) :
    ∃ (Q₁ : Matrix m p 𝕜) (Q₂ : Matrix m q 𝕜), HasOrthonormalCols (Matrix.fromCols Q₁ Q₂) ∧
      Q₁ * Q₁ᴴ = P ∧ Q₂ * Q₂ᴴ = 1 - P

theorem exists_hasOrthonormalCols_fromCols [DecidableEq p] [DecidableEq q] (𝕜 : Type*)
    [RCLike 𝕜] (h : Fintype.card p + Fintype.card q = Fintype.card n) :
    ∃ (Q₁ : Matrix n p 𝕜) (Q₂ : Matrix n q 𝕜), HasOrthonormalCols (Matrix.fromCols Q₁ Q₂)

theorem exists_hasOrthonormalCols_range_eq_range_conjTranspose_truncatedSVD {p : Type*}
    [Fintype p] [DecidableEq p] (A : Matrix m n 𝕜) (k : ℕ)
    (hp : Fintype.card p = (truncatedSVD A k).rank) :
    ∃ Z : Matrix n p 𝕜, HasOrthonormalCols Z ∧
      LinearMap.range Z.mulVecLin = LinearMap.range (truncatedSVD A k)ᴴ.mulVecLin ∧
      Z * Zᴴ = rangeProjector (truncatedSVD A k)ᴴ ∧ A * Z * Zᴴ = truncatedSVD A k

theorem quadForm_mul_conjTranspose_self [Fintype m] (A : Matrix n m 𝕜) (z : n → 𝕜) :
    quadForm (A * Aᴴ) z = ((‖WithLp.toLp 2 (Aᴴ *ᵥ z)‖ ^ 2 : ℝ) : 𝕜)

theorem star_mulVec_dotProduct [Fintype m] (C : Matrix n m 𝕜) (u : m → 𝕜) (v : n → 𝕜) :
    star (C *ᵥ u) ⬝ᵥ v = star u ⬝ᵥ (Cᴴ *ᵥ v)

theorem _root_.Matrix.PosDef.exists_isUnit_eq_mul_conjTranspose {A : Matrix n n 𝕜}
    (hA : A.PosDef) : ∃ S : Matrix n n 𝕜, IsUnit S ∧ A = S * Sᴴ

theorem range_mulVecLin_mul_eq_of_range_eq {q : Type*} [Fintype n] [Fintype p] [Fintype q]
    (A : Matrix m n 𝕜) {X : Matrix n p 𝕜} {Y : Matrix n q 𝕜}
    (h : LinearMap.range X.mulVecLin = LinearMap.range Y.mulVecLin) :
    LinearMap.range (A * X).mulVecLin = LinearMap.range (A * Y).mulVecLin

theorem uncurry_mul_mul {R : Type*} [CommSemiring R] {a b : Type*} [Fintype m] [Fintype n]
    (S : Matrix a m R) (X : Matrix m n R) (T : Matrix n b R) :
    Function.uncurry (S * X * T) = (S ⊗ₖ Tᵀ) *ᵥ Function.uncurry X

theorem trace_hermitianPart (A : Matrix n n 𝕜) :
    (hermitianPart A).trace = ((RCLike.re A.trace : ℝ) : 𝕜)

theorem specNorm_one_sub_smul_le_of_smul_one_le_hermitianPart [DecidableEq n]
    {A : Matrix n n 𝕜} {a a' : ℝ} (ha : 0 ≤ a) (hH : a • (1 : Matrix n n 𝕜) ≤ hermitianPart A)
    (hA : specNorm A ≤ a') : specNorm (1 - (a / a' ^ 2) • A) ≤ √(1 - (a / a') ^ 2)

theorem specNorm_aeval_le_pseudoConditionNumber_mul [DecidableEq n] {A V : Matrix n n 𝕜}
    {d : n → 𝕜} (hV : IsUnit V) (hAV : A * V = V * Matrix.diagonal d) (p : 𝕜[X]) {η : ℝ}
    (hη : ∀ i, ‖p.eval (d i)‖ ≤ η) : specNorm (aeval A p) ≤ pseudoConditionNumber V * η

-- QR.lean, file variables `{A Q : Matrix m n 𝕜} {R : Matrix n n 𝕜}`
theorem IsQR.isUnit (h : IsQR A Q R) (hR : ∀ i, R i i ≠ 0) : IsUnit R
theorem IsQR.isUnit_iff (h : IsQR A Q R) : IsUnit R ↔ ∀ i, R i i ≠ 0
theorem IsQR.isUnit_iff_injective_mulVec (h : IsQR A Q R) :
    IsUnit R ↔ Function.Injective A.mulVec
theorem IsQR.mul_inv_eq (h : IsQR A Q R) (hR : IsUnit R) : A * R⁻¹ = Q

theorem conjTranspose_mul_self_le_add_smul_one_of_specNorm_sub_smul_one_le [DecidableEq n]
    {T : Matrix m n 𝕜} {N ε : ℝ} (h : specNorm (Tᴴ * T - N • (1 : Matrix n n 𝕜)) ≤ ε) :
    Tᴴ * T ≤ (N + ε) • (1 : Matrix n n 𝕜)
theorem sub_smul_one_le_conjTranspose_mul_self_of_specNorm_sub_smul_one_le [DecidableEq n]
    {T : Matrix m n 𝕜} {N ε : ℝ} (h : specNorm (Tᴴ * T - N • (1 : Matrix n n 𝕜)) ≤ ε) :
    (N - ε) • (1 : Matrix n n 𝕜) ≤ Tᴴ * T

-- ForMathlib/LinearAlgebra/Matrix/PosDef.lean, namespace `Matrix`, the file's `𝕜`
theorem PosSemidef.fromBlocks_zero₁₂_zero₂₁ {s t : Type*} [Fintype s] [Fintype t]
    {A : Matrix s s 𝕜} {D : Matrix t t 𝕜} (hA : A.PosSemidef) (hD : D.PosSemidef) :
    (fromBlocks A 0 0 D).PosSemidef
```

Notes on the Matrix rows:
* **M1.** `[Finite n]` came from Mathlib's `Matrix.PosSemidef.conjTranspose_mul_mul_same`. The
  library's `PosSemidef.conjTranspose_mul_mul_same'` (ForMathlib, imported by `Loewner.lean`) has
  none.
* **M6.** Mathlib has no `∃ S, IsUnit S ∧ A = S * Sᴴ`. It has `Matrix.PosDef.isUnit` and
  `posSemidef_iff_eq_conjTranspose_mul_self`. `Cholesky.lean` is not the home because it needs
  `[LinearOrder n]`.
* **M5a** is a convenience twin of `quadForm_conjTranspose_mul_self` at `Aᴴ` (plus
  `conjTranspose_conjTranspose`), not a duplicate. Five call sites currently do that rewrite by
  hand, which is why it is worth a name.
* **M8.** Rule T5 (a warning) prefers `ᴴ`, but the identity is a transpose over any commutative
  semiring; the docstring says so.
  * Mathlib's `Matrix.kronecker_mulVec_vec` is column-major (`vec X = uncurry Xᵀ`). The proof is
    that lemma at `(Tᵀ, Xᵀ, S)` plus `transpose_mul`.
  * The private `frobNorm_mul_mul_eq` (`Moments.lean:71`) stays.
* **M10** is stated over `𝕜`. The trace of the Hermitian part is the real part of the trace.
  The ℝ users (HutchPlusPlus, Haar/Moments) close with `simpa using trace_hermitianPart B`
  (`RCLike.re_to_real`). There is no former M9: `cfc_mul_cfc` is dropped (§3.1, F7).
* **M11.** Hypotheses:
  * Loewner form, by §5.3 ("bounds on it are stated in Loewner form"). GMRES's
    `spectrum ℝ (hermitianPart A) ⊆ Set.Ici a` reaches it through
    `smul_one_le_iff_spectrum_subset_Ici`.
  * The real scalar action, by §5.3. GMRES currently writes `((α : ℝ) : 𝕜) •`; the bridge is
    `RCLike.real_smul_eq_coe_smul`.
  * $a' = 0$ is covered by the junk value $a/0 = 0$.
  * `ha` is needed: with $A = 0$ and $a < 0 < a'$ the statement is false.
* **M12.** It holds for empty `n`. Alternative home: `Spectral/PowerBounds.lean`, beside its
  power analogue `specNorm_pow_le_pseudoConditionNumber_mul` (:70). The bound is about `aeval`, so
  it goes with `IsHermitian.specNorm_aeval_le`.
* **M13.**
  * `IsQR.isUnit_iff` is 3 lines from `isUpperTriangular.isUnit_det_iff`.
  * `IsQR.isUnit_iff_injective_mulVec` combines it with the public `IsQR.injective_mulVec_iff`
    (:123).
  * `IsQR.mul_inv_eq` has 5 users, so it is the declaration that removes real duplication.
* **M15.** It is API of Mathlib's `Matrix.PosSemidef` in Mathlib vocabulary only, written in the
  shape an upstream PR would take. The name follows the §4.3 spelling `fromBlocks_zero₁₂_zero₂₁`
  (`Naming.md`, D9 synonyms, line 76). The smul-one special case is not a separate lemma.
  Mathlib's `Matrix.fromBlocks_diagonal` makes the two diagonal privates unnecessary.

### 3.3 The three Regression `IsQR` theorems: `hR` stays

No Regression statement changes.

* **`IsSubspaceEmbedding.pseudoConditionNumber_mul_inv_sq_le_of_isQR`**
  (`Regression/Embedding.lean:196`) **keeps `(hR : IsUnit R)`**.
  * It would hold without `hR`, but only through the junk value: for singular $\mathbf{R}$,
    `R⁻¹ = 0` and the bound reads `0 ≤ b / a`.
  * §5.2 says the theorem carries the hypothesis that excludes the junk value.
  * The three `IsQR` theorems keep the same hypothesis list.
* **`IsQR.sketchAndPrecondition_eq_mulVec_cgIterate`** (`SketchAndPrecondition.lean:138`) **keeps
  `hR`**. At $q = 0$ the left side is $\mathbf{x}_0$, while for singular $\mathbf{R}$ the right
  side is $\mathbf{0}$.
* **`IsQR.iterativeSketching_succ`** (`IterativeSketching.lean:103`) **keeps `hR`**.
  Counterexample: $\mathbf{S} = \mathbf{I}$ and $\mathbf{A} = \operatorname{diag}(1, 0)$, so
  $\mathbf{R} = \operatorname{diag}(1, 0)$. The right side is $\mathbf{x}_q$, but the left side is
  $\mathbf{x}_q + \omega\mathbf{A}^{+}(\mathbf{y} - \mathbf{A}\mathbf{x}_q)$.
* Changes to the proofs only:
  * All three use `IsQR.mul_inv_eq` (kept) in place of the hand-built `hQ`.
  * A caller that holds injectivity of `(S * A).mulVec` gets `hR` from
    `IsQR.isUnit_iff_injective_mulVec`.

The Cholesky–QR converse (`IsCholesky (Aᴴ * A) L → IsQR A (A * (Lᴴ)⁻¹) Lᴴ`) is about 12 lines from
existing API. It has no consumer in the library, so it is new API, not consolidation. It is
deferred to the first randomized-Cholesky-QR consumer.

### 3.4 Polynomial (layer 0)

Home: `Polynomial/Chebyshev/Residual.lean`, namespace `NLAlib`. All statements use only `ℝ[X]`,
`comp`, `X`, `chebyshevResidual`, `chebyshevWeight` and `T`, so P11 holds. MINRES imports
Residual directly; WorstCase gets it through `ResidualMinimax`.

```lean
-- after `isUniformApproxOn_chebyshevResidual` (:104)
theorem degree_chebyshevResidual_comp_X_sq_le (a b : ℝ) (q : ℕ) :
    ((chebyshevResidual a b q).comp (X ^ 2)).degree ≤ (2 * q : ℕ)
theorem eval_chebyshevResidual_comp_X_sq_zero {a b : ℝ} (q : ℕ) (ha : 0 < a) (hab : a < b) :
    ((chebyshevResidual a b q).comp (X ^ 2)).eval 0 = 1
theorem abs_eval_chebyshevResidual_comp_X_sq_le {a b : ℝ} (q : ℕ) (ha : 0 < a) (hab : a < b) :
    ∀ x ∈ Set.Icc (-b) (-a) ∪ Set.Icc a b,
      |((chebyshevResidual (a ^ 2) (b ^ 2) q).comp (X ^ 2)).eval x| ≤
        ((T ℝ (q : ℤ)).eval ((b ^ 2 + a ^ 2) / (b ^ 2 - a ^ 2)))⁻¹

-- after `exists_degree_le_eval_eq_zero_abs_eval_le_two_mul_mul_pow` (:333)
theorem exists_degree_le_eval_eq_zero_abs_eval_le_two_mul_pow_div_two {a b : ℝ} (ha : 0 < a)
    (q : ℕ) : ∃ p : ℝ[X], p.degree ≤ q ∧ p.eval 0 = 1 ∧
      ∀ x ∈ Set.Icc (-b) (-a) ∪ Set.Icc a b, |p.eval x| ≤ 2 * ((b / a - 1) / (b / a + 1)) ^ (q / 2)

-- after `sum_chebyshevWeight` (:508); now private `WorstCase.lean:137`
theorem inv_eval_T_real_le_sum_chebyshevWeight_mul_norm_sq {𝕜 : Type*} [RCLike 𝕜] {a a' : ℝ}
    (ha : 0 < a) (haa : a < a') {q : ℕ} {p : 𝕜[X]} (hp : p.degree ≤ q) (hp₀ : p.eval 0 = 1) :
    ((T ℝ (q : ℤ)).eval ((a' + a) / (a' - a)))⁻¹ ≤
      ∑ k : Fin (q + 1), chebyshevWeight a a' q k * ‖p.eval (chebyshevExtremum a a' q k : 𝕜)‖ ^ 2
```

What each declaration replaces:
* **The three two-interval lemmas** replace the inline `hRn`/`hP`/`hP₀` in
  `Krylov/LinearSystems/WorstCase.lean:435–446` and the private `sq_mem_Icc_of_mem_union` (:290).
  That lemma becomes a private of `Residual.lean`, used twice there.
* **The existence form** replaces `Krylov/LinearSystems/MINRES.lean:121–139`. That theorem has no
  `a < b` hypothesis, which this existence lemma matches; MINRES's theorem becomes 2 lines.
* **The dual certificate** keeps its proof (36 lines, 3 uses in WorstCase).
  * Its name gains `_real` to match its neighbours `inv_eval_T_real_le_of_isUniformApproxOn` and
    `inv_eval_T_real_eq_two_mul_pow_div`. It was private, so no rename-map entry is needed.
  * Home: `Residual.lean`, not `ResidualMinimax.lean`, which is the Sion file, and CG must not
    import Sion.

Bound form:
* I wrote `∀ x ∈ s, |p.eval x| ≤ M`, the form of the neighbour at :333 and of the §5.3 row
  "location of the spectrum". I did not use `Metric.IsUniformApproxOn`.
* Both consumers unpack the predicate at once, and the Polynomial upstreaming notes list the
  predicate as friction.
* The neighbours at :104 and :133 use the predicate. If uniformity with them is preferred, state
  the third lemma as `Metric.IsUniformApproxOn` on the union.

Not moved: `Polynomial.contract` facts beyond F6, and the scalar arithmetic privates of WorstCase.

### 3.5 Krylov (layer 1)

```lean
-- Krylov/Basic/BlockSpace.lean, after `range_aeval_mul_le_blockKrylovSpace` (:286)
theorem range_mul_aeval_mul_le_range_mul_blockKrylovMatrix {R : Type*} [CommSemiring R]
    [Algebra R 𝕜] {l : Type*} (C : Matrix l n 𝕜) (A : Matrix n n 𝕜) (B : Matrix n p 𝕜) {q : ℕ}
    {f : R[X]} (hf : f.degree < q) :
    LinearMap.range (C * aeval A f * B).mulVecLin ≤
      LinearMap.range (C * blockKrylovMatrix A B q).mulVecLin
```
It replaces:
* `LowRank/Gaussian/BlockKrylov.lean:117` (private, same name);
* the inline inclusion in the public `singularValues_sub_rbki_le_of_degree_lt`
  (`LowRank/Structural/BlockKrylov.lean:147–150`);
* `hrange` in `LowRank/Gaussian/BlockKrylovGapless.lean:676–680`.

The proof is 2 lines from `exists_aeval_mul_eq_blockKrylovMatrix_mul` and
`range_le_iff_exists_mul`.

### 3.6 RandomMatrix (layer 2)

**R1. `rademacherMatrix` with a `gaussianMatrix`-style API.** New file
`RandomMatrix/Rademacher/Basic.lean`, mirroring `RandomMatrix/Gaussian/Basic.lean`. Its imports
are `NLAlib.Probability.Distributions.Rademacher` and `NLAlib.Probability.Law`. Variables are
`{Ω} {mΩ} {μ} {m n : Type*} [Fintype m] [Fintype n] {X : Ω → Matrix m n ℝ}`.
```lean
noncomputable abbrev rademacherMatrix (k n : Type*) [Fintype k] [Fintype n] :
    Measure (Matrix k n ℝ) := Measure.pi fun _ : k => rademacherVector n          -- moved
instance isProbabilityMeasure_rademacherMatrix : IsProbabilityMeasure (rademacherMatrix k n)
                                                                                    -- moved
theorem hasLaw_uncurry_of_hasLaw_rademacherMatrix (hX : HasLaw X (rademacherMatrix m n) μ) :
    HasLaw (fun ω => Function.uncurry (X ω)) (rademacherVector (m × n)) μ
theorem hasLaw_rademacherMatrix_of_hasLaw_uncurry
    (hX : HasLaw (fun ω => Function.uncurry (X ω)) (rademacherVector (m × n)) μ) :
    HasLaw X (rademacherMatrix m n) μ
theorem hasLaw_col_of_hasLaw_rademacherMatrix (hX : HasLaw X (rademacherMatrix m n) μ) (j : n) :
    HasLaw (fun ω i => X ω i j) (rademacherVector m) μ
theorem iIndepFun_col_of_hasLaw_rademacherMatrix (hX : HasLaw X (rademacherMatrix m n) μ) :
    iIndepFun (fun j ω i => X ω i j) μ
theorem hasLaw_conjTranspose_of_hasLaw_rademacherMatrix (hX : HasLaw X (rademacherMatrix m n) μ) :
    HasLaw (fun ω => (X ω)ᴴ) (rademacherMatrix n m) μ
```
* **Proofs.** These copy the Gaussian ones with `rademacherMeasure` in place of
  `gaussianReal 0 1`:
  * `measurePreserving_curry_pi`;
  * a private transpose through `measurePreserving_arrowCongr'`;
  * `HasLaw.eval` and `HasLaw.iIndepFun_eval`;
  * for the conjugate transpose, `hasLaw_pi_iff` as in `Gaussian/Invariance.lean:163`.
* **What it replaces.** The private `hasLaw_col_of_hasLaw_conjTranspose_rademacherMatrix`
  (`Estimation/Trace/HutchPlusPlus.lean:475`, 12 lines) becomes
  `hasLaw_col_of_hasLaw_rademacherMatrix (by simpa using hasLaw_conjTranspose_of_hasLaw_rademacherMatrix hG)`.
  It keeps the hypothesis on $\mathbf{G}^{\mathsf{H}}$ of
  `variance_hutchpp_of_hasLaw_rademacherMatrix`, which `Estimation-HutchPP.md:624` chose
  deliberately.
* **Changes in Sketching.** `Sketching/Gaussian/Rademacher.lean` loses the definition and the
  instance and gets `public import NLAlib.RandomMatrix.Rademacher.Basic`. The import must be
  public, so that every file importing the Sketching file still sees `rademacherMatrix`. Its "Main
  definitions" line moves to the new module docstring.
* **Changes in Estimation.** `HutchPlusPlus.lean` can import the RandomMatrix file in place of
  `Sketching.Gaussian.Rademacher`, which it uses for nothing else.
* **Not moved.** `countSketch`, `samplingSketch` and `srht` stay in Sketching: they are sketch
  constructions, and the probability survey (R-3) leaves them to the maintainer.

**R2. Bounds on the projection factors.** These are used for integrability (boundedness) in the
four generalized Nyström and early-truncation files.
```lean
-- RandomMatrix/Gaussian/BlockMoments.lean, after `one_le_gaussianProjectionFactor` (:86)
theorem gaussianProjectionFactor_le_one_add {q c : ℕ} (h : q + 2 ≤ c) :
    gaussianProjectionFactor q c ≤ 1 + c
-- RandomMatrix/Haar/Blocks.lean, after `one_le_haarProjectionFactor` (:358); direct proof
theorem haarProjectionFactor_le_one_add {d q c : ℕ} (h : q + 2 ≤ c) (hcd : c ≤ d) :
    haarProjectionFactor d c q ≤ 1 + c
```
* They replace `LowRank/Gaussian/GeneralizedNystrom.lean:122` `gaussianProjectionFactor_le_one_add`
  and `:396` `haarProjectionFactor_le_one_add`, both private.
* The `_rank_truncatedSVD_mem` pairs (`EarlyTruncation.lean:127`, `EarlyTruncationHaar.lean:97`)
  shrink to about 3 lines.
* `haarProjectionFactor_le_gaussianProjectionFactor` stays in `Regression/SketchAndSolve.lean`
  (`LowRank-S6.md` A6).

### 3.7 Integrability of a projection residual (Probability, layer 1) and Estimation (layer 4)

The two integrability lemmas have no LowRank vocabulary: a random matrix, `rangeProjector` and a
norm. So they go below LowRank, by topic, in `Probability/Measurability/Matrix.lean`, after
`measurable_rangeProjector` (:162). That file already holds the measurability of
`rangeProjector`, `pinv` and the norms; these are their bounded-function corollaries.
* Its closure contains `Matrix/Norms/Projector.lean`, which has the bounds
  `frobNorm_one_sub_rangeProjector_mul_le` (:224) and `specNorm_one_sub_rangeProjector_mul_le`
  (:217).
* It needs `public import Mathlib.MeasureTheory.Integral.IntegrableOn`.
* The three LowRank users already import it transitively (checked).
* If the file is to stay measurability-only, the alternative is a section of
  `Probability/MatrixIntegral.lean`.

```lean
-- Probability/Measurability/Matrix.lean, after `measurable_rangeProjector` (:162)
theorem integrable_frobNorm_one_sub_rangeProjector_mul_sq [IsFiniteMeasure μ] [DecidableEq m]
    {k p : Type*} [Fintype k] [Fintype p] (B : Matrix m n 𝕜) (M : Matrix m p 𝕜)
    {Y : Ω → Matrix n k 𝕜} (hY : AEMeasurable Y μ) :
    Integrable (fun ω => frobNorm ((1 - rangeProjector (B * Y ω)) * M) ^ 2) μ
theorem integrable_specNorm_one_sub_rangeProjector_mul_sq [IsFiniteMeasure μ] [DecidableEq m]
    {k p : Type*} [Fintype k] [Fintype p] (B : Matrix m n 𝕜) (M : Matrix m p 𝕜)
    {Y : Ω → Matrix n k 𝕜} (hY : AEMeasurable Y μ) :
    Integrable (fun ω => specNorm ((1 - rangeProjector (B * Y ω)) * M) ^ 2) μ
```
They replace:
* `LowRank/Gaussian/BlockKrylovGapless.lean:686`
  `integrable_specNorm_one_sub_rangeProjector_mul_sq_of_aemeasurable` (private, ℝ);
* the Frobenius twin written inline at `LowRank/Gaussian/BlockKrylov.lean:146–155` and
  `LowRank/Gaussian/Filter.lean:214–222`.

```lean
-- Estimation/Trace/GirardHutchinson.lean, after
-- `variance_girardHutchinson_sqrt_smul_of_hasLaw_haarFrame` (:206)
theorem integral_norm_trace_sub_girardHutchinson_sq_of_hasLaw_gaussianMatrix {t : Type*}
    [Fintype t] [Nonempty t] {G : Ω → Matrix n t ℝ} (hG : HasLaw G (gaussianMatrix n t) μ)
    (B : Matrix n n ℝ) :
    ∫ ω, ‖B.trace - girardHutchinson B (G ω)‖ ^ 2 ∂μ =
      2 / Fintype.card t * frobNorm (hermitianPart B) ^ 2
theorem integral_norm_trace_sub_girardHutchinson_sq_of_hasLaw_rademacherMatrix {t : Type*}
    [Fintype t] [Nonempty t] {G : Ω → Matrix n t ℝ}
    (hG : HasLaw (fun ω => (G ω)ᴴ) (rademacherMatrix t n) μ) (B : Matrix n n ℝ) :
    ∫ ω, ‖B.trace - girardHutchinson B (G ω)‖ ^ 2 ∂μ =
      2 / Fintype.card t * (frobNorm (hermitianPart B) ^ 2 - ∑ i, hermitianPart B i i ^ 2)
```
* **Changes from the privates.** These are the privates `HutchPlusPlus.lean:446` and `:492`. The
  error is now written `tr B − estimate` in `‖·‖ ^ 2`, the convention of N10 and of the general
  `integral_norm_trace_sub_girardHutchinson_sq` (:117), in place of `(estimate − tr B) ^ 2`.
  Over ℝ the two are equal.
* **Proofs.** They shorten through the public `variance_quadForm_of_hasLaw_gaussianVector_hermitianPart`
  and `…_rademacherVector_hermitianPart` (`Probability/QuadraticForm/Moments.lean:401, :413`), so
  the privates `girardHutchinson_hermitianPart` (:167) and `trace_hermitianPart` (:173, see M10)
  go.
* **Docstrings.** They state the laws and the independence of the probes (D12).
* **Imports.** GirardHutchinson gets `rademacherMatrix` from the R1 file.

### 3.8 Statement changes, removals, renames

| declaration | change | callers to edit |
|---|---|---|
| `NLAlib.conjTranspose_mul_mul_le_conjTranspose_mul_mul` (`Matrix/Norms/Loewner.lean:83`) | drops `[Finite n]` | none. Its 10 callers (SingularValueInequalities :232, :246; HermitianCalculus :428, :430; NystromOrder :188; ProjectorPair :155; DavisKahanGap :158; HaarEmbedding :159, :206) compile unchanged |
| `NLAlib.integral_comp_eq_integral_integral_of_indepFun` (`Probability/Distributions/GaussianIntegrationByParts.lean:230`) | **removed**; its content is `ProbabilityTheory.IndepFun.integral_comp_eq_integral_integral` | its 2 uses, same file |

* No public declaration is renamed.
* Private declarations that change name in going public need no map entry (they are not in the
  explorer).
* No ledger target and no explorer TOML names the removed or changed declarations (grepped
  `docs/port/ledger.json` and `explore/*.toml`).

Rename map, `docs/renames/2026-10-consolidation.json`, in the format of the existing maps:
```json
{
  "date": "2026-10-21",
  "note": "Consolidation round (docs/design/Consolidation.md; CONTRIBUTING §3, rule S5). Before v0.1: no deprecated aliases. Re-proved private helpers became public lemmas in the file of their topic and the copies were deleted. Entries with \"removed\": true delete a public duplicate; \"new\" is the declaration that carries its content, and the explorer redirects the old link there. statementChanged lists declarations whose statements changed: conjTranspose_mul_mul_le_conjTranspose_mul_mul drops an unneeded [Finite n].",
  "renames": [
    {"old": "NLAlib.integral_comp_eq_integral_integral_of_indepFun",
     "new": "ProbabilityTheory.IndepFun.integral_comp_eq_integral_integral",
     "rule": "S5", "removed": true}
  ],
  "statementChanged": [
    "NLAlib.conjTranspose_mul_mul_le_conjTranspose_mul_mul"
  ]
}
```

### 3.9 Same-name private pairs that are not duplicates

The S5 check matches names, so these pairs are false positives. Each is fixed by renaming one
private, which needs no map entry. I prefer this to an allowlist entry, in line with "fewer
exceptions".

| pair | the two statements | rename |
|---|---|---|
| `re_quadForm_smul_add_smul` (`Functions/TraceFunctions.lean:166`, `Inequalities/Kantorovich.lean:137`) | linearity in the matrix, vs the Hermitian expansion in the vector | Kantorovich's to `re_quadForm_smul_add_smul_vec` (name to settle in the commit) |
| `extendFin` (`Majorization/DoublyStochastic.lean:135`, `Norms/SymmetricGauge.lean:60`) | a function `ℕ → ℝ`, vs a finsupp linear map | SymmetricGauge's to `extendFinLinear` |
| `exists_eigencoordinates` (`Spectral/CourantFischer.lean:56`, `Perturbation/Residual.lean:44`) | share only their first conjunct; T is linear in one, a plain function in the other, and Residual adds a residual-norm conjunct | Residual's to `exists_eigencoordinates_residual` |
| `continuous_pullback` | resolved by F7: Jackson's copy is deleted | — |

**Identical private definitions inside Matrix** (no public definition is warranted; each would
need a §5.3 row, rule V7):
* **`finBlocks` and its four entry lemmas** (`Spectral/RealSchur.lean:58–86`,
  `Spectral/QuasiTriangular.lean:86–109`).
  * Both copies are deleted. The uses write
    `(Matrix.fromBlocks S C D T).submatrix finSumFinEquiv.symm finSumFinEquiv.symm`.
  * The entry lemmas are Mathlib `simp` lemmas (`finSumFinEquiv_symm_apply_castAdd`,
    `fromBlocks_apply₁₁`), so they become `simp` calls.
  * If that inflates the two files, the fallback is a public `abbrev` in `QuasiTriangular.lean`
    (RealSchur imports it), with a §5.3 row.
* **`euclideanRange`** (`Basic/OrthonormalBasis.lean:41`, `Basic/Projector.lean:172`).
  OrthonormalBasis imports Projector. The copy in OrthonormalBasis is replaced by the Mathlib
  expression it abbreviates, written out as `rangeProjector`'s definition does.

## 4. Consumers

Every new declaration has at least two users today, listed in §3, except these four:
* `IsQR.isUnit_iff` and `IsQR.isUnit_iff_injective_mulVec`. They are the bridge a caller of the
  two Regression `IsQR` theorems needs, so that `hR` can come from injectivity.
* `exists_hasOrthonormalCols_fromCols` (M3b). It has two users, each saving about 3 lines.
* The F6 `contract` lemmas: one user, placement only.

Future consumers:
* F1: XTrace, every two-sketch generalized Nyström variant, and the joint Haar transfer (survey
  R-7).
* R1: any Rademacher-matrix moment proof.
* M11, M12: the deferred Greenbaum–Gurvits normal-matrix GMRES.
* M14: the sub-Gaussian rows theorem (survey R-4).

## 5. Files and placement

**New files**, each named after its topic or, in ForMathlib, after the Mathlib file it would join:

| file | content | imports |
|---|---|---|
| `ForMathlib/MeasureTheory/Measure/Real.lean` | F2 | `Mathlib.MeasureTheory.Measure.Real` |
| `ForMathlib/Analysis/Calculus/BumpFunction/Basic.lean` | F3 | `Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension` |
| `ForMathlib/RingTheory/Polynomial/Chebyshev.lean` | `natDegree_T_comp_le` (F5) | `Mathlib.RingTheory.Polynomial.Chebyshev` |
| `ForMathlib/Algebra/Polynomial/Expand.lean` | F6 (droppable) | `Mathlib.Algebra.Polynomial.Expand` |
| `RandomMatrix/Rademacher/Basic.lean` | R1 | `NLAlib.Probability.Distributions.Rademacher`, `NLAlib.Probability.Law` |

Each ForMathlib file marks itself as an upstream candidate (P6). Root imports are regenerated with
`lake exe mk_all --module --lib NLAlib`.

**Additions to existing files.** Every home and the reason for it is in §3. Each is the file where
a user looking for the topic would look, and each user imports it (checked transitively). New
imports:
* `ForMathlib/Probability/Independence/Basic.lean` imports `Mathlib.Probability.HasLaw`.
* `Matrix/Functions/Polynomial.lean` imports `Matrix/Pseudoinverse/ConditionNumber`.
* `LowRank/Oblivious/SubGaussian.lean` imports `Matrix/Structured/Kronecker`.
* `RandomMatrix/Gaussian/Invariance.lean` imports `Matrix/Structured/Kronecker`.
* `Probability/Distributions/GaussianIntegrationByParts.lean` and
  `Probability/QuadraticForm/HansonWright/OffDiagonal.lean` import
  `ForMathlib/Probability/Independence/Basic`.
* `Sketching/Gaussian/Rademacher.lean` (a `public import`) and
  `Estimation/Trace/GirardHutchinson.lean` import `RandomMatrix/Rademacher/Basic`.
* `Probability/Measurability/Matrix.lean` imports `Mathlib.MeasureTheory.Integral.IntegrableOn`.

**Flags (placement not by topic):**
* None new.
* One existing flag stays: `haarProjectionFactor_le_gaussianProjectionFactor` in
  `Regression/SketchAndSolve.lean`, decided in `LowRank-S6.md` A6. Moving it to `Haar/Blocks.lean`
  would need `Haar/Blocks` to import `Gaussian/BlockMoments`. That import is legal, but the move is
  outside this round's brief, so it is left as recorded.
* Not moved, recorded: the public `HasOrthonormalCols.mul_pinv_self_of_rank_eq`
  (`LowRank/Structural/RangeFinder.lean:106`). It is a 3-line corollary of
  `mul_pinv_self_of_injective_conjTranspose` (`Matrix/Pseudoinverse/Pinv.lean:432`) with a single
  file of users. Moving it is a P10 placement change with no duplicate behind it; the next round
  that touches Pinv should take it.

## 6. Material

* **Library.** All of it, as above.
* **Quarry** (`atlas/declarations.json`, read only). Searched for the new names and for
  conditioning lemmas:
  * The one relevant entry is `NLAlib.integral_comp_of_indepFun_of_forall_integral_eq`
    (`Estimation.Trace.Unbiased`), an equality-to-a-constant Fubini step.
  * It is covered by the existing Bochner `IndepFun.integral_comp_eq_integral_integral`, so it is
    not reproduced.
  * No quarry entry matches the other items.
* **Not reproduced:**
  * the Hanson–Wright MGF as a public lemma (no consumer; summary, premise 4);
  * public versions of single-use privates with no second user: `quadForm_blockDiagonal_const`,
    the Kaczmarz `measurable_`/`dependsOn_` lemmas, `zero_le_one_sub_one_div_frobPseudoConditionNumber_sq`,
    `smul_gram_le_iff`, `quadForm_rangeProjector`, `range_mul_eq_of_rank_eq`, and the strict
    w-form Gram bounds of `ExtremeSingularValues.lean:200, :214`, which would be new statements;
  * the normal-matrix GMRES equality (new mathematics);
  * the spectral Nyström Gram correspondence (a new statement, survey M8);
  * the inverse-Gram entry formulas (single file, survey M8).

## 7. In this round, and out

**In:** §3 as written.

**Out**, each with the reason:
* the Chebyshev-residual three-term recurrence and Jackson's theorem on $[a, b]$: not proved
  anywhere, so new mathematics;
* the Cholesky–QR converse: no consumer;
* a public Hanson–Wright MGF: no consumer;
* rewriting the Kaczmarz privates through sketch-and-project: they are not instances, and the route
  would be longer;
* survey items M8b–M8e: single-file, or new statements;
* moving `countSketch`, `samplingSketch` and `srht` down to RandomMatrix: the maintainer's question
  in survey R-3, not a consolidation.

## 8. Order of work

Each commit builds on its own. It is checked by a **full library build**,
`LEAN_NUM_THREADS=4 lake build --wfail NLAlib` in the background with a log (§10), not only by
the touched modules, and by `python3 scripts/check_rules.py --files <files>`. Commits go lowest
layer first.

**The shadowing rule.** A public name added in a lower file shadows, without any error, a private
declaration of the same name in a downstream file that has not been edited yet: inside the
downstream proof, Lean resolves the name to the public declaration (`ResolveName.lean:138–142`).
* If the two statements agree, the private copy is silently dead.
* If they differ, the downstream proof breaks far from the commit that caused it, or, worse,
  still elaborates against the wrong statement.
* So a commit that adds a public name also deletes or renames, **in the same commit**, every
  private declaration that clashes with it, in whatever file and layer that is.

The clashes, found by matching every new name against the private list
(`scratchpad/consol/privs.txt`), plus the namespace-opened cases:

| commit | new public name | clashing private (deleted or renamed in that commit) |
|---|---|---|
| A3 | `Polynomial.Chebyshev.abs_eval_T_comp_C_mul_X_sub_one_le` | `LowRank/Gaussian/BlockKrylovGapless.lean:637`, same short name. The private is `NLAlib.…`, but the file opens `Polynomial.Chebyshev` locally (`open … in`, :458, :478), where the two would be ambiguous. Delete it in A3 |
| A4 (F6) | `Polynomial.two_mul_eval_contract_two_sq` | `Krylov/LinearSystems/WorstCase.lean:251` (opens `Polynomial`) |
| A5 QuadForm | `star_mulVec_dotProduct` | `Krylov/LinearSystems/PCGRecurrence.lean:97` |
| A5 HermitianPart | `trace_hermitianPart` | `Estimation/Trace/HutchPlusPlus.lean:173`. The statements differ (ℝ form against the `𝕜` form), so this one would break |
| A5 Kronecker | `uncurry_mul_mul` | `RandomMatrix/Gaussian/Invariance.lean:98` and `RandomMatrix/Gaussian/Moments.lean:62` |
| A7 | `range_mul_aeval_mul_le_range_mul_blockKrylovMatrix` | `LowRank/Gaussian/BlockKrylov.lean:117` (argument order differs) |
| A8 R2 | `gaussianProjectionFactor_le_one_add`, `haarProjectionFactor_le_one_add` | `LowRank/Gaussian/GeneralizedNystrom.lean:122`, `:396` |
| A5 QR | `IsQR.isUnit` | `Matrix/Factorizations/QR.lean:77`, the same file (made public in place) |

* `cfc_mul_cfc` is no longer a new name (§3.1, F7), so its two privates (`OperatorConvex.lean:371`
  and `TracePowers.lean:336`, the latter used with `rw [← cfc_mul_cfc]` in the opposite
  orientation) are only Phase B edits.
* Before each Phase A commit the author re-runs the match against the current private list,
  because line numbers and names move as Phase B proceeds.

* **Phase A** adds each public lemma in its home, with the deletions or renames of the table
  above. Where the private copy sits in the home file itself, that commit also removes it.
* **Phase B** edits the consumers, one file per commit, and deletes the copies. After Phase A,
  Phase B commits are independent of each other and can be done **one file at a time**, in any
  order, by different proof agents (CONTRIBUTING §11: at most two at once).

Phase A, each commit one home file:
1. **A1.** F1 in `ForMathlib/Probability/Independence/Basic.lean`. This is the one item that
   waits for D1.
2. **A2.** F2, F3 and F5's `natDegree_T_comp_le`: the new ForMathlib files, one commit each.
3. **A3.** F4 and F5's `abs_eval_T_comp_C_mul_X_sub_one_le`, in the existing ForMathlib files.
4. **A4.** M15 in `ForMathlib/LinearAlgebra/Matrix/PosDef.lean`. F6 (droppable).
5. **A5. Matrix, one commit per home file:**
   * `Basic/Orthonormal` (M2);
   * `Basic/OrthonormalBasis` (M3a, and `euclideanRange`);
   * `Subspaces/Frames` (M3b);
   * `Basic/QuadForm` (M5a, M5b);
   * `Basic/Projector` (M7);
   * `Spectral/LowRank` (M4);
   * `Spectral/Congruence` (M6);
   * `Spectral/HermitianPart` (M10, M11);
   * `Functions/Polynomial` (M12);
   * `Structured/Kronecker` (M8);
   * `Factorizations/QR` (M13, with its 4 uses in that file);
   * `Norms/Loewner` (the M1 statement change, whose callers compile unchanged, and M14).
6. **A6.** Polynomial `Chebyshev/Residual.lean` (§3.4). The `degree_chebyshevResidual_le` proof
   uses F5.
7. **A7.** Krylov `Basic/BlockSpace.lean` (§3.5).
8. **A8.** RandomMatrix:
   * R1: the new file, with the definition removed from `Sketching/Gaussian/Rademacher.lean` in
     the same commit (2 files: a move cannot be split);
   * R2: `BlockMoments`, `Haar/Blocks`.
9. **A9.** Probability `Measurability/Matrix.lean` (the two integrability lemmas of §3.7). It is
   layer 1, but it comes after A5 and does not depend on A6–A8.
10. **A10.** Estimation `GirardHutchinson.lean` (§3.7; after R1 and M10).

Phase B, one consumer file per commit, by layer:
* **Matrix:** TraceFunctions or Kantorovich (rename), SymmetricGauge (rename), Residual (rename),
  OperatorConvex and TracePowers (`cfc_mul_cfc` to Mathlib's `cfc_mul`), RealSchur and QuasiTriangular (`finBlocks`; 2 files, because both
  lose the same definition and nothing else changes), SingularValueInequalities (F7 and M14),
  NystromOrder (M15), Compare (F7), Hessenberg (M13).
* **Polynomial:** Jackson, ChebyshevSeries (F7).
* **Probability:** LogSobolev, GaussianLogSobolev, BoundedDifferences, Freedman, Laplace, Tail,
  OffDiagonal, GaussianIntegrationByParts (the removal; add the rename map here).
* **Krylov:** MinResidual, MINRESRecurrence, PreconditionedLanczos, MINRESLanczos, MINRES,
  CGRecurrence, PCGRecurrence, PCG, Richardson, GMRES, WorstCase.
* **RandomMatrix:** Invariance, Moments, SpectralNorm, InverseMoments, Haar/Blocks, Haar/Moments,
  ExtremeSingularValues.
* **Sketching:** HaarEmbedding, Flattening, SRHT, CountSketch, JohnsonLindenstrauss.
* **Sketching, continued:** SubspaceEmbedding, Haar (the M1 private copies).
* **Regression:** SketchAndSolve, Embedding (`IsQR.mul_inv_eq`, and the F7 deletion of
  `le_div_of_mul_le'`), SketchAndPrecondition, IterativeSketching. None changes a statement.
* **LowRank:**
  * `Oblivious/`: RangeFinder, SubGaussian, EarlyTruncation;
  * `Structural/`: RangeFinder, BlockKrylov;
  * `Gaussian/`: BlockKrylov, BlockKrylovGapless, Filter, GeneralizedNystrom, EarlyTruncation,
    EarlyTruncationHaar, TruncatedGeneralizedNystrom, RangeFinderTail, RotationInvariant,
    RotationInvariantFactor;
  * `Random/RangeFinder` (F7).
* **Estimation:** HutchPlusPlus, last, because it uses F1, M10, R1 and the §3.7 theorems.
* **Solvers:** Kaczmarz, SketchAndProject.

**Closing commit:**
* the §5.3 row amendment from D1 in CONTRIBUTING (two reviews);
* `docs/renames/2026-10-consolidation.json`, unless it already landed with the removal;
* a `docs/port/status.md` entry;
* `python3 scripts/check_rules.py --only S5 --warnings` reporting 0;
* the full §9 checklist, with `scripts/Duplicates.lean` and `scripts/Reuse.lean` on the touched
  public theorems.

No ledger entry is needed: nothing is ported.

No design note needs an edit for a statement change. The one change, `[Finite n]`, is not
quoted in any note. `Sketching-S0.md:159–161` quotes
`pseudoConditionNumber_mul_inv_sq_le_of_isQR` with `(hR : IsUnit R)`, which stays (checked). The
quote also omits `[LinearOrder q]`, which that note's own amendment (:263) already records.

## 9. Open questions

Each is minor and comes with a recommendation; none blocks the work.
1. **The bound form of `abs_eval_chebyshevResidual_comp_X_sq_le`** (§3.4): raw `∀ x ∈ s, |…| ≤`
   or `Metric.IsUniformApproxOn`. Recommendation: raw, like its neighbour at :333 and the §5.3
   spectrum row.
2. **`hR` on `pseudoConditionNumber_mul_inv_sq_le_of_isQR`** (§3.3). It could go only through
   the junk value `R⁻¹ = 0`. Recommendation: **keep it**, so that the theorem excludes the junk
   value (§5.2) and the three `IsQR` theorems keep one hypothesis list.
3. **F6 (`Polynomial.contract`)** is placement only, with one user. Recommendation: include it as
   the last ForMathlib commit, because a future asymmetric two-interval bound would reuse it.
   Dropping it costs nothing.
4. **`finBlocks`**: delete and use `simp`, or a public `abbrev` with a §5.3 row. Recommendation:
   delete, with the `abbrev` as the fallback if the files grow.
