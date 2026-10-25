# Design note: Probability stage Beta, sphere-probe tails with the sharp Beta constant

Status: approved by the maintainer 2026-10-24 (Q1–Q4 as recommended); skeleton written.

Prerequisite stage of the SLQ design's phase B-sphere (`docs/design/Estimation-SLQ.md` §3.8, its
rows E1–E4; maintainer decisions Q3 (b), Q3′, Q3″, 2026-10-24). Branch `design/ks7-slq`
(worktree `/home/ubuntu/nlalib-design`). Every signature in §3 was elaborated against the built
tree with `sorry` bodies: `/tmp/claude-1000/beta-scratch/ForMathlibShapes.lean` (Mathlib imports
only), `SphereShapes.lean` and `StepShapes.lean` (importing `NLAlib.RandomMatrix.Haar.Sphere`).
`SphereShapes.lean` also elaborates an E1-shaped consumer call (§4). The signatures are final unless
a question in §7 changes them. After the review, the measure-level primaries and the split
helpers were elaborated in `MeasureShapes.lean`, and the public `ae_norm_eq_one_uniformSphereVector`
in `AeNorm.lean`.

## Changes during the skeleton (2026-10-24)

The skeleton (branch `design/ks7-slq`, on the SLQ skeleton `f75d601`) puts every statement of §3
in place as signed there, except item 1. Done for real in `NLAlib/`: R1 (the move, proved) and AE
(the rename). The other 32 declarations of §8 are sorried in `NLAlibScaffold/` (**S 18, M 14**
by declaration; the 26 rows left after R1 and AE are S 12, M 14, L 0). Dispatch targets:
`nlalib-harness/pilot/beta-targets.json`, one entry per declaration (a bundle row's declarations
share its row id). SLQ's E1–E4 are in its scaffold (`Estimation-SLQ.md`, "Changes during the
skeleton"). Deviations and decisions:

1. **`integral_comp_norm_pi_gaussianReal` drops `hφ` and takes `φ` explicitly** (minimal fix):
   polar coordinates hold for every `φ`, both sides being Bochner integrals, so `hφ` was unused,
   which T13 and the unused-variables linter (`--wfail`) reject. The statement is now
   `ProbabilityTheory.integral_comp_norm_pi_gaussianReal [Nonempty ι] (φ : ℝ → ℝ) : …` with the
   conclusion of §3.1 unchanged. `NLAlib.integral_comp_norm_of_hasLaw_gaussianVector` keeps its
   `hφ`, which `HasLaw.integral_comp` needs.
2. **R1 is done in the skeleton, proved**, so it is not dispatched. The new
   `NLAlib/ForMathlib/Probability/Distributions/ChiSquared.lean` holds the private
   `pi_gaussianReal_eq_withDensity` (moved), the private
   `integral_comp_norm_pi_gaussianReal_eq_mul` (the moved `integral_radial_gaussianVector`, the
   normalising constant left unevaluated), a private `integral_pow_mul_exp_neg_sq_div_two` (the
   $\chi_d$ normalising constant $2^{d/2-1}\Gamma(d/2)$, from Mathlib's
   `integral_rpow_mul_exp_neg_mul_rpow`; not a copy of `ChiSquareMoments.lean`'s private
   moment lemma, which stays there for every exponent) and the public polar formula. In
   `ChiSquareMoments.lean` the two private lemmas are deleted, the public polar formula is the
   ForMathlib lemma through `HasLaw.integral_comp` (4 lines), and the private
   `integral_norm_sq_rpow_gaussianVector` is re-derived from it; its `HaarToSphere` import moved
   with the proof.
3. **AE**: `ae_norm_eq_one_uniformSphereVector` is the old private lemma made public under the
   file's variables (`n`, `[Fintype n]`; the same statement as §3.4), its one use updated, listed
   in the module's main results.
4. **No `NLAlib` file for `Beta.lean` or `MeanValue.lean` yet.** Everything in them is sorried,
   and an imports-only file breaks P2. The one definition, the private `betaExpMoment`, is in
   `NLAlibScaffold/ForMathlib/Probability/Distributions/Beta.lean` with the private steps that
   use it (a private definition is invisible from another file); it moves with them. For the
   same reason `NLAlib/RandomMatrix/Haar/Sphere.lean` and `…/ChiSquare.lean` do not yet import
   ForMathlib `Beta.lean` and `ChiSquared.lean` (§5); the proof PRs add the imports.
5. **Scaffold files and imports.** `ForMathlib/Analysis/Calculus/Deriv/MeanValue` (β4e;
   Mathlib's `Deriv.MeanValue`, `Pow.Deriv`); `ForMathlib/Probability/Distributions/ChiSquared`
   (β1a, β1, β1h; the NLAlib file and `HasLaw`); `ForMathlib/Probability/Distributions/Beta`
   (β2a-i–β2h, `betaExpMoment`, β4a-i–β4h; the imports of §5, `HasLaw`, and the scaffold
   `MeanValue`); `Probability/Distributions/ChiSquare` (β1′; the NLAlib file and the scaffold
   `ChiSquared`); `RandomMatrix/Haar/Sphere` (β3a, β3b, β3, β5, β6; the NLAlib file and the
   scaffold `Beta` and `ChiSquare`). Order within files as §5.
6. **Citations** (C1, C2). β1 and β2 carry `Result:` ids and no source, so they say "No printed
   source."; so does β3, since no locator in `Meckes2019` was checked and a bare key is not
   allowed in a declaration docstring. β5 and β6 cite `[MarchalArbel2017, Theorem 1]` for the
   proxy (β6 had the bare key). `MarchalArbel2017` is in `docs/references.bib` with the fields of
   §5.
7. **β3a's helpers take `omit [DecidableEq k] in`**, as the file's existing helpers do: their
   statements do not use it. β6's name is not in the scaffold module docstring's list (a module
   docstring cannot take S8); the docstring describes it in words.
8. Not added yet: the §5.3 row of §1 (with the first proof PR) and no `docs/constants.toml`
   change (no named bound).

## Changes after the Fable review (2026-10-24)

The review found β4f sound and complete and read Marchal–Arbel 2017 (arXiv 1705.00048). Every
[should] is adopted:

1. **Source and locator** (review 1). β4 cites `[MarchalArbel2017, Theorem 1]`, which is now
   confirmed. Its docstring says the Lean proof is a Riccati comparison for $(\log\mathrm{mgf})'$,
   not the source's proof. The source proves it by series comparison (symmetric case) and a
   second-order Kummer-ODE analysis (§2.3, non-symmetric case). The bibliographic fields are
   confirmed (§5). β4f is downgraded from research risk to Lean risk (§8).
2. **`ae_norm_eq_one` public** (review 3). It becomes
   `NLAlib.ae_norm_eq_one_uniformSphereVector` in `Sphere.lean`, listed in the module docstring.
   It is needed by β5 ($k = n$) and by SLQ E3 ("mass exactly 1 a.s.").
3. **Measure-level ForMathlib primaries** (review 4). `map_sum_sq_pi_gaussianReal`,
   `map_div_add_prod_gammaMeasure` and `hasSubgaussianMGF_sub_div_betaMeasure` are the primary
   theorems, in Mathlib's `Measure.map` form. The earlier `HasLaw` signatures stay unchanged as
   3–10-line corollaries, so E1 is unaffected.
4. **Mandatory splits** (review 8). β4a becomes three rows (`HasDerivAt`, `IntervalIntegrable`,
   FTC) and β2a becomes two (the substitution map's image, injectivity and derivative; the
   lintegral). No row is L.

The [consider] items:

* 2 (symmetry route for $t < 0$): **declined as primary, kept as the named fallback.** The
  reflection costs about 10 lines inside β4f. Making $t > 0$ primary would complicate β4g's
  statement. The map lemma `map_one_sub_betaMeasure` elaborates (unconditional) if needed.
* 5 (`stdGaussian`): **adopted as a docstring note.** `ChiSquared.lean`'s module docstring names
  `(stdGaussian (EuclideanSpace ℝ ι)).map (‖·‖ ^ 2)` and `map_pi_eq_stdGaussian` as the upstream
  target. `deriv_cgf` and `iteratedDeriv_two_cgf` are added to §6's search; we keep
  `betaExpMoment` because the Riccati algebra is simpler on raw moments.
* 6 (β4e's size): **adopted.** β4e becomes S (15–25), in a one-lemma `MeanValue.lean`.
* 7 (placement and names): no change needed.
* 9 (`isProbabilityMeasureBeta` is a lemma): **adopted.** β4c's row says `haveI`.
* Q2 comment ("chi-square" in the ForMathlib docstring): **adopted.**

## 0. Scope and consumers

For $\mathbf u$ uniform on the unit sphere of $\mathbb R^n$ and $\mathbf V$ with $k$ orthonormal
columns, $\|\mathbf V^{\mathsf H}\mathbf u\|^2 \sim \mathrm{Beta}(k/2, (n-k)/2)$, and a
$\mathrm{Beta}(\alpha,\beta)$ variable is sub-Gaussian with variance proxy $1/(4(\alpha+\beta+1))$
[MarchalArbel2017]. Together they give proxy $1/(2(n+2))$ for $\|\mathbf V^{\mathsf H}\mathbf u\|^2
- k/n$, and Hoeffding gives the $m$-sample tail
$$\mathbb{P}\Bigl[\tau \le \Bigl\lvert \tfrac1m\textstyle\sum_j \|\mathbf V^{\mathsf H}\mathbf u_j\|^2
- \tfrac kn\Bigr\rvert\Bigr] \le 2e^{-m(n+2)\tau^2}.$$
This tail is what SLQ's E1 consumes. E2–E4 consume only E1.

The scope is set by that consumer, plus the general facts the route needs:

| Item | What | Where |
|---|---|---|
| β1 | $\sum_{i\in\iota} g_i^2 \sim \mathrm{Gamma}(\lvert\iota\rvert/2, 1/2)$ for i.i.d. $N(0,1)$ ($\chi^2$ law) | ForMathlib |
| β2 | $X/(X+Y) \sim \mathrm{Beta}(a,b)$ for independent $X \sim \mathrm{Gamma}(a,r)$, $Y \sim \mathrm{Gamma}(b,r)$ | ForMathlib |
| β3 | $\|\mathbf V^{\mathsf H}\mathbf u\|^2 \sim \mathrm{Beta}(k/2, (n-k)/2)$, $0 < k < n$ | `RandomMatrix/Haar/Sphere.lean` |
| β4 | Beta sub-Gaussian proxy $1/(4(\alpha+\beta+1))$ | ForMathlib |
| β5 | $\|\mathbf V^{\mathsf H}\mathbf u\|^2 - k/n$ has proxy $1/(2(n+2))$, every $0 \le k \le n$ | `RandomMatrix/Haar/Sphere.lean` |
| β6 | the $m$-sample tail above | `RandomMatrix/Haar/Sphere.lean` |

Ids versus the SLQ sketch (§3.8 there): β1–β4 keep their meaning. SLQ's β5 (two-sided Hoeffding
for an average) is Mathlib's `HasSubgaussianMGF.sum_of_iIndepFun` followed by NLAlib's
`HasSubgaussianMGF.measureReal_abs_ge_le`, so it is not a step of its own; here it is the proof of
β6. β5 here is new. It covers ranks $0$ and $n$ (deterministic cases), so E1 needs no rank split.

Two differences from the SLQ sketch:

* **No 2-D Jacobian.** The Gamma ratio (SLQ's L step β2b) is done with one 1-D substitution
  $x = ys/(1-s)$ for fixed $y$, Tonelli, and Mathlib's Gamma integral (§3.2). All steps are M.
* **The Beta proxy has a written proof** (§3.3, β4e–β4g). It is a Riccati comparison for
  $y = (\log\mathrm{mgf})'$ with integrating factor $t^{\alpha+\beta}$, ending in the pointwise
  inequality $y(1-y) \le 1/4$. It covers $\alpha = \beta$ as well. The proof differs from
  Marchal–Arbel's, which is longer and second-order. The reviewer checked it line by line and
  numerically (§6). β4f is the flagged Lean-risk step (§8).

Not in scope, because no consumer: the sum of independent Gammas, Beta moments and mean,
Dirichlet laws, the optimal (smaller) Beta proxy for $\alpha \neq \beta$, Haar-frame
(dependent-column) tails (SLQ Q12, decided later).

## 1. Objects

No new public definition. The stage uses Mathlib's objects directly:

| Concept | Spelling | Mathlib |
|---|---|---|
| Gamma law, shape $a$, rate $r$ | `gammaMeasure a r` | `Probability/Distributions/Gamma.lean` |
| Beta law | `betaMeasure α β` (`IsProbabilityMeasure` by the lemma `isProbabilityMeasureBeta`, not an instance) | `Probability/Distributions/Beta.lean` |
| $\chi^2_d$ | `gammaMeasure (d / 2) (1 / 2)`, no definition (§7 Q2) | — |
| i.i.d. standard normal vector | `Measure.pi fun _ : ι => gaussianReal 0 1` in ForMathlib; `gaussianVector ι` (an `abbrev` of it) in NLAlib | `gaussianReal` |
| uniform unit vector | `uniformSphereVector n` (NLAlib, `RandomMatrix/Haar/Basic.lean`) | — |

Proposed §5.3 row (added in the implementing PR): "Gamma, Beta, chi-square laws | Mathlib's
`gammaMeasure a r` (shape, rate), `betaMeasure α β`; $\chi^2_d$ is `gammaMeasure (d / 2) (1 / 2)`,
no NLAlib definition | Mathlib's; `hasLaw_sum_sq_of_hasLaw_pi_gaussianReal`".

The private helper `betaExpMoment α β k s := ∫ x, x ^ k * Real.exp (s * x) ∂betaMeasure α β` in
ForMathlib `Beta.lean` holds the moment-generating integrals of §3.3. It is private, never in a
public statement, and goes in the skeleton.

No Mathlib deviation: nothing goes in `docs/design/Mathlib-deviations.md`.

## 2. Interfaces

No new interface. Hypotheses are Mathlib's `HasLaw`, `IndepFun`, `iIndepFun` and NLAlib's
`HasOrthonormalCols`. Conclusions are Mathlib's `HasLaw` (β1–β3), Mathlib's `HasSubgaussianMGF`
(β4, β5) and a `μ.real` tail (β6). Because the conclusions are `HasSubgaussianMGF`, every
existing sub-Gaussian theorem applies to sphere projections: Hoeffding, the union bound
`HasSubgaussianMGF.measureReal_exists_ge_le`, and second moments.

## 3. Statement shapes

Docstrings below are abridged. The implementing docstrings state their own hypotheses (D2), name
the laws (D12) and give the source's label (C1).

### 3.1 ForMathlib: the $\chi^2$ law (`NLAlib/ForMathlib/Probability/Distributions/ChiSquared.lean`)

```lean
namespace ProbabilityTheory

/-- **Polar coordinates for a standard normal vector**: for measurable `φ` and `ι` nonempty,
$\mathbb E\,\varphi(\|\mathbf g\|) = (2^{d/2-1}\Gamma(d/2))^{-1}\int_0^\infty y^{d-1}e^{-y^2/2}
\varphi(y)\,dy$, $d = \lvert\iota\rvert$. Moved from NLAlib (R1, §5). -/
theorem integral_comp_norm_pi_gaussianReal {ι : Type*} [Fintype ι] [Nonempty ι] {φ : ℝ → ℝ}
    (hφ : Measurable φ) :
    ∫ x, φ ‖WithLp.toLp 2 x‖ ∂(Measure.pi fun _ : ι => gaussianReal 0 1) =
      (∫ y in Ioi (0 : ℝ), y ^ (Fintype.card ι - 1) * (Real.exp (-y ^ 2 / 2) * φ y)) /
        (2 ^ ((Fintype.card ι : ℝ) / 2 - 1) * Real.Gamma ((Fintype.card ι : ℝ) / 2))

/-- **The chi-square law**: under the product of $d = \lvert\iota\rvert \ge 1$ standard normal
laws, $\sum_i x_i^2$ has law $\mathrm{Gamma}(d/2, 1/2)$, the chi-square law $\chi^2_d$.
Result: chi-square-law -/
theorem map_sum_sq_pi_gaussianReal {ι : Type*} [Fintype ι] [Nonempty ι] :
    (Measure.pi fun _ : ι => gaussianReal 0 1).map (fun x => ∑ i, x i ^ 2) =
      gammaMeasure (Fintype.card ι / 2) (1 / 2)

/-- The `HasLaw` form: the sum of squares of $d \ge 1$ independent standard normal variables is
chi-square with $d$ degrees of freedom. -/
theorem hasLaw_sum_sq_of_hasLaw_pi_gaussianReal {ι : Type*} [Fintype ι] [Nonempty ι]
    {g : Ω → ι → ℝ} (hg : HasLaw g (Measure.pi fun _ : ι => gaussianReal 0 1) μ) :
    HasLaw (fun ω => ∑ i, g ω i ^ 2) (gammaMeasure (Fintype.card ι / 2) (1 / 2)) μ

-- private step β1a
private theorem measureReal_sum_sq_mem_pi_gaussianReal {ι : Type*} [Fintype ι] [Nonempty ι]
    {S : Set ℝ} (hS : MeasurableSet S) :
    (Measure.pi fun _ : ι => gaussianReal 0 1).real {x | ∑ i, x i ^ 2 ∈ S} =
      (gammaMeasure (Fintype.card ι / 2) (1 / 2)).real S
```

`[Nonempty ι]` is needed: for empty `ι` the sum is $0$, while `gammaMeasure 0 (1/2)` is the zero
measure ($\Gamma(0) = 0$ in Mathlib). The NLAlib-vocabulary corollary goes in
`NLAlib/Probability/Distributions/ChiSquare.lean`. That file's docstring already says "$\chi^2$"
without a theorem behind it.

```lean
/-- **The squared norm of a standard Gaussian vector is chi-square** … -/
theorem NLAlib.hasLaw_norm_sq_of_hasLaw_gaussianVector {g : Ω → n → ℝ} [Nonempty n]
    (hg : HasLaw g (gaussianVector n) μ) :
    HasLaw (fun ω => ‖WithLp.toLp 2 (g ω)‖ ^ 2) (gammaMeasure (Fintype.card n / 2) (1 / 2)) μ
```

Proof checked in the scratch file: `(hasLaw_sum_sq_of_hasLaw_pi_gaussianReal hg).congr
(ae_of_all _ fun ω => by simp [EuclideanSpace.real_norm_sq_eq])`. `gaussianVector` unfolds as an
`abbrev`.

### 3.2 ForMathlib: Beta as a ratio of Gammas (`NLAlib/ForMathlib/Probability/Distributions/Beta.lean`)

```lean
/-- **Beta as a ratio of Gammas**: for $a, b, r > 0$, the image of
$\mathrm{Gamma}(a, r) \otimes \mathrm{Gamma}(b, r)$ under $(x, y) \mapsto x/(x+y)$ is
$\mathrm{Beta}(a, b)$.
Result: gamma-ratio-beta -/
theorem map_div_add_prod_gammaMeasure {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    ((gammaMeasure a r).prod (gammaMeasure b r)).map (fun p : ℝ × ℝ => p.1 / (p.1 + p.2)) =
      betaMeasure a b

/-- The `HasLaw` form: for independent $X \sim \mathrm{Gamma}(a, r)$ and
$Y \sim \mathrm{Gamma}(b, r)$, $X/(X+Y) \sim \mathrm{Beta}(a, b)$. -/
theorem hasLaw_div_add_of_hasLaw_gammaMeasure {X Y : Ω → ℝ} {a b r : ℝ} (ha : 0 < a)
    (hb : 0 < b) (hr : 0 < r) (hX : HasLaw X (gammaMeasure a r) μ)
    (hY : HasLaw Y (gammaMeasure b r) μ) (hXY : IndepFun X Y μ) :
    HasLaw (fun ω => X ω / (X ω + Y ω)) (betaMeasure a b) μ

-- private steps
-- β2a-i (one bundle): the substitution map
private theorem image_mul_div_one_sub_Ioo {y : ℝ} (hy : 0 < y) :
    (fun s => y * s / (1 - s)) '' Ioo (0 : ℝ) 1 = Ioi 0
private theorem injOn_mul_div_one_sub (y : ℝ) (hy : 0 < y) :
    InjOn (fun s => y * s / (1 - s)) (Ioo (0 : ℝ) 1)
private theorem hasDerivAt_mul_div_one_sub (y : ℝ) {s : ℝ} (hs : s ≠ 1) :
    HasDerivAt (fun s => y * s / (1 - s)) (y / (1 - s) ^ 2) s
-- β2a-ii: for fixed y > 0, substitute x = y s / (1 - s), s ∈ (0, 1)
private theorem lintegral_Ioi_comp_div_add {F : ℝ → ℝ≥0∞} (hF : Measurable F) {a r y : ℝ}
    (hy : 0 < y) :
    ∫⁻ x in Ioi (0 : ℝ), F (x / (x + y)) * ENNReal.ofReal (x ^ (a - 1) * Real.exp (-(r * x))) =
      ∫⁻ s in Ioo (0 : ℝ) 1, F s * ENNReal.ofReal
        (y ^ a * s ^ (a - 1) * (1 - s) ^ (-a - 1) * Real.exp (-(r * y * s / (1 - s))))
-- β2b: Tonelli swap after β2a
private theorem lintegral_lintegral_comp_div_add_gammaPDF {F : ℝ → ℝ≥0∞} (hF : Measurable F)
    {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    ∫⁻ y, (∫⁻ x, F (x / (x + y)) * gammaPDF a r x) * gammaPDF b r y =
      ∫⁻ s in Ioo (0 : ℝ) 1, F s * ENNReal.ofReal
        (r ^ (a + b) / (Real.Gamma a * Real.Gamma b) * s ^ (a - 1) * (1 - s) ^ (-a - 1) *
          ∫ y in Ioi (0 : ℝ), y ^ (a + b - 1) * Real.exp (-(r / (1 - s) * y)))
-- β2c: the y-integral (Mathlib `Real.integral_rpow_mul_exp_neg_mul_Ioi`) and the constants
private theorem lintegral_lintegral_comp_div_add_gammaPDF_eq_betaPDF {F : ℝ → ℝ≥0∞}
    (hF : Measurable F) {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    ∫⁻ y, (∫⁻ x, F (x / (x + y)) * gammaPDF a r x) * gammaPDF b r y =
      ∫⁻ s, F s * betaPDF a b s
```

Arithmetic of the route (checked by hand). With $x = ys/(1-s)$ we get $dx = y(1-s)^{-2}\,ds$ and
$x^{a-1}\,dx = y^a s^{a-1}(1-s)^{-a-1}\,ds$. The exponents combine as $e^{-rys/(1-s)}e^{-ry} =
e^{-ry/(1-s)}$. The $y$-integral is $\Gamma(a+b)((1-s)/r)^{a+b}$, and the constants are
$r^{a+b}/(\Gamma(a)\Gamma(b)) \cdot \Gamma(a+b) r^{-(a+b)} = 1/B(a,b)$, which leaves
$s^{a-1}(1-s)^{b-1}/B(a,b)$.

### 3.3 ForMathlib: the Beta sub-Gaussian proxy (same file; one lemma in `MeanValue.lean`)

```lean
/-- **Beta laws are sub-Gaussian with proxy $1/(4(\alpha+\beta+1))$**: for
$X \sim \mathrm{Beta}(\alpha, \beta)$, $\alpha, \beta > 0$, the centred variable
$X - \alpha/(\alpha+\beta)$ satisfies
$\mathbb E e^{t(X - \alpha/(\alpha+\beta))} \le e^{t^2/(8(\alpha+\beta+1))}$ for every real $t$.
The proxy equals the variance when $\alpha = \beta$ and exceeds it otherwise.
[MarchalArbel2017, Theorem 1]. The proof here is a comparison for the Riccati equation of
$(\log \mathrm{mgf})'$, not the source's.
Result: beta-subgaussian -/
theorem hasSubgaussianMGF_sub_div_betaMeasure {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    HasSubgaussianMGF (fun x => x - α / (α + β)) ‖1 / (4 * (α + β + 1))‖₊ (betaMeasure α β)

/-- The `HasLaw` form, for $X \sim \mathrm{Beta}(\alpha, \beta)$, by
`HasSubgaussianMGF.id_map_iff`. -/
theorem hasSubgaussianMGF_sub_div_of_hasLaw_betaMeasure {X : Ω → ℝ} {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hX : HasLaw X (betaMeasure α β) μ) :
    HasSubgaussianMGF (fun ω => X ω - α / (α + β)) ‖1 / (4 * (α + β + 1))‖₊ μ
```

The proxy is a small source constant, so it is written in the statement (§5.2 rule 2). It is not a
named bound and needs no `docs/constants.toml` entry. Its coercion to ℝ is
`by rw [coe_nnnorm, Real.norm_eq_abs, abs_of_pos (by positivity)]` (checked).

**Proof (the plan's β4a–β4g).** Write $b = \alpha+\beta$, $\mu_0 = \alpha/b$,
$\sigma^2 = 1/(4(b+1))$, $\varphi_k(t) = \mathbb E X^k e^{tX}$, $y = \varphi_1/\varphi_0$.

1. *Integration by parts* (β4a, β4b). The function $x^\alpha(1-x)^\beta e^{tx}$ vanishes at $0$
   and $1$, and its derivative is $x^{\alpha-1}(1-x)^{\beta-1}e^{tx}(\alpha - bx + tx(1-x))$. So
   $\mathbb E[(\alpha - bX + tX(1-X))e^{tX}] = 0$, that is
   $\alpha\varphi_0 - b\varphi_1 + t(\varphi_1 - \varphi_2) = 0$ (Kummer's equation for
   ${}_1F_1(\alpha; b; t)$).
2. *Riccati* (β4c, β4d). $\varphi_k' = \varphi_{k+1}$, so $y' = \varphi_2/\varphi_0 - y^2$, and
   step 1 gives $ty' + by - \alpha = ty(1-y)$. For $z = y - \mu_0 - \sigma^2 t$ (using
   $b\mu_0 = \alpha$ and $(b+1)\sigma^2 = 1/4$):
   $$tz' + bz = t\bigl(y(1-y) - \tfrac14\bigr).$$
3. *Comparison* (β4e, β4f). Since $y(1-y) \le 1/4$ for every real $y$, $tz' + bz \le 0$ for
   $t > 0$. Then $t^b z$ has derivative $t^{b-1}(tz' + bz) \le 0$ on $(0,\infty)$, is continuous
   on $[0,\infty)$ and is $0$ at $0$, so $z \le 0$ on $(0, \infty)$. For $t < 0$, apply the same
   lemma to $w(s) = -z(-s)$: $sw'(s) + bw(s) = -(tz'(t) + bz(t))|_{t=-s} \le 0$, so $z \ge 0$ on
   $(-\infty, 0)$. In both cases $t\,z(t) \le 0$.
4. *Integrate* (β4g). $g(t) = \log\varphi_0(t) - \mu_0 t - \sigma^2t^2/2$ has $g(0) = 0$ and
   $g' = z$, so $g$ is antitone on $[0,\infty)$ and monotone on $(-\infty,0]$, hence $g \le 0$.
5. *Package* (β4). $\mathrm{mgf}(X - \mu_0)(t) = e^{-\mu_0 t}\varphi_0(t) = e^{g(t) +
   \sigma^2t^2/2}$. Exponential integrability holds because $X \in [0,1]$ almost surely.

```lean
-- ForMathlib/Analysis/Calculus/Deriv/MeanValue.lean, root namespace (β4e)
/-- **Integrating factor**: if $t f'(t) + b f(t) \le 0$ on $(0, \infty)$ with $b > 0$ and $f$ is
continuous from the right at $0$, then $t \mapsto t^b f(t)$ is antitone on $[0, \infty)$. -/
theorem antitoneOn_rpow_mul_of_hasDerivAt {f f' : ℝ → ℝ} {b : ℝ} (hb : 0 < b)
    (hc : ContinuousWithinAt f (Ici 0) 0) (hf : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt f (f' t) t)
    (h : ∀ t ∈ Ioi (0 : ℝ), t * f' t + b * f t ≤ 0) :
    AntitoneOn (fun t => t ^ b * f t) (Ici 0)

-- Beta.lean, private steps
private noncomputable def betaExpMoment (α β : ℝ) (k : ℕ) (s : ℝ) : ℝ :=
  ∫ x, x ^ k * Real.exp (s * x) ∂betaMeasure α β
-- β4a-i, β4a-ii, then β4a-iii (the FTC call)
private theorem hasDerivAt_rpow_mul_rpow_mul_exp {α β t x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun x => x ^ α * (1 - x) ^ β * Real.exp (t * x))
      (x ^ (α - 1) * (1 - x) ^ (β - 1) *
        ((α - (α + β) * x + t * x * (1 - x)) * Real.exp (t * x))) x
private theorem intervalIntegrable_rpow_mul_rpow_mul_exp {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (t : ℝ) :
    IntervalIntegrable (fun x => x ^ (α - 1) * (1 - x) ^ (β - 1) *
      ((α - (α + β) * x + t * x * (1 - x)) * Real.exp (t * x))) volume 0 1
private theorem intervalIntegral_rpow_mul_rpow_mul_exp_eq_zero {α β : ℝ} (hα : 0 < α)
    (hβ : 0 < β) (t : ℝ) :
    ∫ x in (0 : ℝ)..1, x ^ (α - 1) * (1 - x) ^ (β - 1) *
      ((α - (α + β) * x + t * x * (1 - x)) * Real.exp (t * x)) = 0
-- β4b
private theorem integral_sub_mul_add_mul_exp_betaMeasure {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (t : ℝ) :
    ∫ x, (α - (α + β) * x + t * x * (1 - x)) * Real.exp (t * x) ∂betaMeasure α β = 0
-- β4c (one bundle)
private theorem ae_mem_Icc_betaMeasure (α β : ℝ) : ∀ᵐ x ∂betaMeasure α β, x ∈ Icc (0 : ℝ) 1
private theorem hasDerivAt_betaExpMoment {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (k : ℕ) (t : ℝ) :
    HasDerivAt (betaExpMoment α β k) (betaExpMoment α β (k + 1) t) t
private theorem betaExpMoment_zero_pos {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (t : ℝ) :
    0 < betaExpMoment α β 0 t
-- β4d: t z' + b z = t (y (1 - y) - 1/4)
private theorem mul_sub_add_mul_sub_eq {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (t : ℝ) :
    t * (betaExpMoment α β 2 t / betaExpMoment α β 0 t -
        (betaExpMoment α β 1 t / betaExpMoment α β 0 t) ^ 2 - 1 / (4 * (α + β + 1))) +
      (α + β) * (betaExpMoment α β 1 t / betaExpMoment α β 0 t - α / (α + β) -
        t / (4 * (α + β + 1))) =
    t * (betaExpMoment α β 1 t / betaExpMoment α β 0 t *
      (1 - betaExpMoment α β 1 t / betaExpMoment α β 0 t) - 1 / 4)
-- β4f: t z(t) ≤ 0   [Lean risk]
private theorem mul_sub_div_sub_div_nonpos {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (t : ℝ) :
    t * (betaExpMoment α β 1 t / betaExpMoment α β 0 t - α / (α + β) -
      t / (4 * (α + β + 1))) ≤ 0
-- β4g
private theorem log_betaExpMoment_sub_le {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (t : ℝ) :
    Real.log (betaExpMoment α β 0 t) - α / (α + β) * t ≤ t ^ 2 / (8 * (α + β + 1))
```

### 3.4 Sphere projections (`NLAlib/RandomMatrix/Haar/Sphere.lean`, additions)

File variables: `{n k : Type*} [Fintype n] [Fintype k] [DecidableEq k] {u : Ω → n → ℝ}
{V : Matrix n k ℝ}`. `DecidableEq k` is needed by `HasOrthonormalCols V`.

```lean
/-- A uniform unit vector has norm $1$ almost surely (for nonempty $n$). Made public from the
private `ae_norm_eq_one` (review 3); used by β5 and SLQ E3. -/
theorem ae_norm_eq_one_uniformSphereVector {n : Type*} [Fintype n] [Nonempty n] :
    ∀ᵐ v ∂uniformSphereVector n, ‖WithLp.toLp 2 v‖ = 1

/-- **The projection of a uniform unit vector is Beta**: for $\mathbf u$ uniform on the unit
sphere of $\mathbb R^n$ and $\mathbf V$ with $k$ orthonormal columns, $0 < k < n$,
$\|\mathbf V^{\mathsf H}\mathbf u\|^2 \sim \mathrm{Beta}(k/2, (n-k)/2)$.
[Meckes2019, locator to check; otherwise "No printed source."].
Result: sphere-projection-beta -/
theorem hasLaw_norm_conjTranspose_mulVec_sq_of_hasLaw_uniformSphereVector
    (hu : HasLaw u (uniformSphereVector n) μ) (hV : HasOrthonormalCols V)
    (hk : 0 < Fintype.card k) (hkn : Fintype.card k < Fintype.card n) :
    HasLaw (fun ω => ‖WithLp.toLp 2 (Vᴴ *ᵥ u ω)‖ ^ 2)
      (betaMeasure (Fintype.card k / 2) (((Fintype.card n : ℝ) - Fintype.card k) / 2)) μ

/-- **Projections of a uniform unit vector are sub-Gaussian**: for $\mathbf u$ uniform on the
unit sphere of $\mathbb R^n$ and $\mathbf V$ with $k$ orthonormal columns (any $0 \le k \le n$),
$\|\mathbf V^{\mathsf H}\mathbf u\|^2 - k/n$ is sub-Gaussian with proxy $1/(2(n+2))$. For
$0 < k < n$ this is the Beta proxy at $\alpha+\beta = n/2$; for $k \in \{0, n\}$ the variable is
$0$ almost surely. Compared with the Chernoff tails of this file: better when $k \gtrsim n/4$,
worse for small $k$ (the docstring gives the comparison of exponents, §5.2 rule 4). -/
theorem hasSubgaussianMGF_norm_conjTranspose_mulVec_sq_sub_of_hasLaw_uniformSphereVector
    (hu : HasLaw u (uniformSphereVector n) μ) (hV : HasOrthonormalCols V) :
    HasSubgaussianMGF
      (fun ω => ‖WithLp.toLp 2 (Vᴴ *ᵥ u ω)‖ ^ 2 - Fintype.card k / Fintype.card n)
      ‖1 / (2 * ((Fintype.card n : ℝ) + 2))‖₊ μ

set_option linter.style.longLine false in -- one identifier
/-- **The sample mean of projected uniform unit vectors**: for $\mathbf u_1, \dots, \mathbf u_m$
independent and uniform on the unit sphere of $\mathbb R^n$ and $\mathbf V$ with $k$ orthonormal
columns, for $\tau \ge 0$,
$$\mathbb P\Bigl[\tau \le \Bigl\lvert\frac1m\sum_j\|\mathbf V^{\mathsf H}\mathbf u_j\|^2 -
\frac kn\Bigr\rvert\Bigr] \le 2e^{-m(n+2)\tau^2}.$$
[MarchalArbel2017] for the proxy; Hoeffding.
Result: sphere-projection-tail -/
theorem
measureReal_abs_sum_norm_conjTranspose_mulVec_sq_div_card_sub_div_card_ge_le_of_hasLaw_uniformSphereVector
    {m : Type*} [Fintype m] {u : m → Ω → n → ℝ} (hind : iIndepFun u μ)
    (hu : ∀ j, HasLaw (u j) (uniformSphereVector n) μ) (hV : HasOrthonormalCols V) {τ : ℝ}
    (hτ : 0 ≤ τ) :
    μ.real {ω | τ ≤ |(∑ j, ‖WithLp.toLp 2 (Vᴴ *ᵥ u j ω)‖ ^ 2) / Fintype.card m -
        Fintype.card k / Fintype.card n|} ≤
      2 * Real.exp (-(Fintype.card m * (Fintype.card n + 2) * τ ^ 2))

-- private steps (β3a bundle; β3b)
private theorem indepFun_sum_sq_inl_sum_sq_inr_of_hasLaw_gaussianVector {p : Type*} [Fintype p]
    {h : Ω → k ⊕ p → ℝ} (hh : HasLaw h (gaussianVector (k ⊕ p)) μ) :
    IndepFun (fun ω => ∑ i, h ω (Sum.inl i) ^ 2) (fun ω => ∑ j, h ω (Sum.inr j) ^ 2) μ
private theorem hasLaw_sum_sq_inl_of_hasLaw_gaussianVector {p : Type*} [Fintype p] [Nonempty k]
    {h : Ω → k ⊕ p → ℝ} (hh : HasLaw h (gaussianVector (k ⊕ p)) μ) :
    HasLaw (fun ω => ∑ i, h ω (Sum.inl i) ^ 2) (gammaMeasure (Fintype.card k / 2) (1 / 2)) μ
-- and `hasLaw_sum_sq_inr_of_hasLaw_gaussianVector`, the same with `p`, `Sum.inr`
private theorem norm_conjTranspose_mulVec_inv_norm_smul_sq_eq_div {p : Type*} [Fintype p]
    [DecidableEq p] {V' : Matrix n p ℝ} (hVV' : HasOrthonormalCols (Matrix.fromCols V V'))
    (hcard : Fintype.card k + Fintype.card p = Fintype.card n) (g : n → ℝ) :
    ‖WithLp.toLp 2 (Vᴴ *ᵥ (‖WithLp.toLp 2 g‖⁻¹ • g))‖ ^ 2 =
      (∑ i, ((Matrix.fromCols V V')ᴴ *ᵥ g) (Sum.inl i) ^ 2) /
        (∑ i, ((Matrix.fromCols V V')ᴴ *ᵥ g) (Sum.inl i) ^ 2 +
          ∑ j, ((Matrix.fromCols V V')ᴴ *ᵥ g) (Sum.inr j) ^ 2)
```

Shape notes:

* β3's second parameter is a real subtraction, so it does not hit V2 (the SLQ sketch had the
  truncated `(card n - card k : ℕ)`).
* β6's empty-`m` case holds: the left side is at most $1$ (`iIndepFun.isProbabilityMeasure`) and
  the right side is $2$. Empty `n` forces empty `k`, and every quantity is $0$.
* β5 and β6 take no rank hypothesis. The ranks $0$ and $n$ are inside the statement.
* The name of β6 exceeds 100 characters and takes S8, as SLQ's names do. It follows
  `measureReal_abs_sum_sq_div_card_sub_one_ge_le_of_iIndepFun` (`SubGaussian/Square.lean`).

## 4. Consumers

| Item | Consumers, and the form they use |
|---|---|
| β6 | SLQ E1 with `u j := fun ω i => U ω i j`, `V` a frame of the spectral projector. Elaborated: the call `β6 hind hU hV hτ` closes E1's tail in `SphereShapes.lean`. E1 shrinks to the event rewrite plus β6, with no rank split. E2–E4 consume E1 only. |
| β5 | β6; any union bound or second-moment argument over projected sphere vectors (one-dimensional JL with a sphere or Haar-column sketch: `hasLaw_col_unit_of_hasLaw_haarFrame` turns a Haar column into `uniformSphereVector`) |
| β3 | β5; the exact law for users of `Sketching-S2.md`'s Haar variable (`hasLaw_conjTranspose_mulVec_of_hasLaw_haarFrame` has the same law); Haar-frame tails later (SLQ Q12) |
| β4 | β5; any Beta-distributed quantity (upstream: Mathlib users of `betaMeasure`) |
| β2 (primary `map_div_add_prod_gammaMeasure`, corollary `HasLaw`) | β3 through the corollary; Dirichlet laws later (Q12); upstream |
| β1, β1′ | β3a; the $\chi^2$ statements of `ChiSquare.lean` (the law behind them); upstream |
| `ae_norm_eq_one_uniformSphereVector` | β5 ($k = n$); SLQ E3 (the probe measure has mass exactly $1$ a.s.) |
| `integral_comp_norm_pi_gaussianReal` | β1a; `NLAlib.integral_comp_norm_of_hasLaw_gaussianVector` and the moments in `ChiSquareMoments.lean` (R1) |
| `antitoneOn_rpow_mul_of_hasDerivAt` | β4f; upstream (an integrating-factor comparison Gronwall does not cover, because the coefficient $b/t$ is singular at $0$) |

Amendment for SLQ (for the orchestrator, not made here): in `Estimation-SLQ.md` §9 the E1 row's
deps become `D3, X2, X3, β6`, and its key-lemma column drops the "rank 0 or n" case; it is S/M
(30–45) rather than M.

## 5. Files and placement

| File | New / addition | Content (in order) | Lines |
|---|---|---|---|
| `NLAlib/ForMathlib/Analysis/Calculus/Deriv/MeanValue.lean` | new | `antitoneOn_rpow_mul_of_hasDerivAt` | 45 |
| `NLAlib/ForMathlib/Probability/Distributions/ChiSquared.lean` | new | private `pi_gaussianReal_eq_withDensity` (moved), `integral_comp_norm_pi_gaussianReal` (moved), β1a, `map_sum_sq_pi_gaussianReal`, `hasLaw_sum_sq_of_hasLaw_pi_gaussianReal`; module docstring names "chi-square" and the `stdGaussian` upstream target | 210 |
| `NLAlib/ForMathlib/Probability/Distributions/Beta.lean` | new | β2a-i, β2a-ii, β2b, β2c, `map_div_add_prod_gammaMeasure`, `hasLaw_div_add_of_hasLaw_gammaMeasure`; `betaExpMoment`, β4a-i–iii, β4b, β4c, β4d, β4f, β4g, `hasSubgaussianMGF_sub_div_betaMeasure`, `hasSubgaussianMGF_sub_div_of_hasLaw_betaMeasure` | 660 |
| `NLAlib/Probability/Distributions/ChiSquareMoments.lean` | edit (R1) | delete the private `gaussianVector_eq_withDensity`, `integral_radial_gaussianVector`; `integral_comp_norm_of_hasLaw_gaussianVector` from the ForMathlib lemma by `HasLaw.integral_comp`; the private moment lemma re-derived from it | −50 |
| `NLAlib/Probability/Distributions/ChiSquare.lean` | addition | `hasLaw_norm_sq_of_hasLaw_gaussianVector` | +15 |
| `NLAlib/RandomMatrix/Haar/Sphere.lean` | addition, edit | `ae_norm_eq_one` made public as `ae_norm_eq_one_uniformSphereVector`; β3a, β3b, β3 (after the helpers), then β5, β6 (after the Chernoff tails) | +230 (to ≈ 980) |

Placement of each addition outside the new ForMathlib files:

| Addition | Home | Reason |
|---|---|---|
| R1 (move) | out of `ChiSquareMoments.lean` into ForMathlib `ChiSquared.lean` | polar coordinates for `Measure.pi gaussianReal` is a general fact (P9). The $\chi^2$ law needs it, and ForMathlib cannot import NLAlib (P1). |
| β1′ | `Probability/Distributions/ChiSquare.lean` | the file about $\|\mathbf g\|^2$, whose docstring states the law |
| β3–β6 | `RandomMatrix/Haar/Sphere.lean` | "Projections of a uniform unit vector" is their topic. They reuse that file's private `norm_conjTranspose_mulVec_inv_norm_smul_sq`, and the now-public `ae_norm_eq_one_uniformSphereVector` (§7 Q4). |

The ForMathlib files are named after the Mathlib file they would join (P7). `Beta.lean` goes
with `Mathlib/Probability/Distributions/Beta.lean`, which would then import `…/Gamma.lean`.
`ChiSquared.lean` would be a new Mathlib file beside `Gamma.lean`. `MeanValue.lean` goes with
`Mathlib/Analysis/Calculus/Deriv/MeanValue.lean`. Each module docstring marks the file as an
upstream candidate (P6) and uses no NLAlib vocabulary (P4). Declarations are in
`ProbabilityTheory` (β1, β2, β4) and the root namespace (β4e), as upstream (P5). The primaries are
in Mathlib's measure-level form (`Measure.map` equalities, like `gaussianReal_map_add_const` and
`map_pi_eq_stdGaussian`). The `HasLaw` forms are corollaries. Upstreaming notes:
Mathlib would spell the proxy `(4 * (α + β + 1))⁻¹.toNNReal` or similar (T2 is an NLAlib rule).
It may want a `chiSquared d` abbrev (Q2) and an `IsProbabilityMeasure` instance for
`betaMeasure` under `Fact` hypotheses. Nothing here blocks either.

Imports: `Beta.lean` imports Mathlib's Beta, Gamma, `Moments.SubGaussian`, `Moments.MGFAnalytic`,
`Function.JacobianOneDim`, ForMathlib `MeanValue.lean` and
`ForMathlib/Probability/Independence/Basic.lean`. `ChiSquared.lean` imports Mathlib's Gamma,
Gaussian, `Constructions.HaarToSphere`. `Sphere.lean` adds ForMathlib `Beta.lean`. `ChiSquare.lean`
adds ForMathlib `ChiSquared.lean`. All imports respect the layers (ForMathlib −1 imports only
Mathlib and ForMathlib; RandomMatrix 2 and Probability 1 import lower layers). No placement flags.

Bibliography (implementing PR): add `MarchalArbel2017`: Olivier Marchal, Julyan Arbel, "On the
sub-Gaussianity of the Beta and Dirichlet distributions", Electron. Commun. Probab. 22 (2017),
paper no. 54, 1–14, DOI 10.1214/17-ECP92 (confirmed by the reviewer from the PDF; arXiv
1705.00048). Elder 2016 is not cited.

## 6. Material

* **Marchal–Arbel 2017.** The PDF was not on this machine when this note was drafted. The
  reviewer read it (arXiv 1705.00048; extracted text at `/tmp/claude-1000/beta-review/ma2017/`).
  It confirms Theorem 1 ("Optimal proxy variance for the Beta distribution"): the optimal proxy
  through a transcendental equation in ${}_1F_1$, the explicit bound $1/(4(\alpha+\beta+1))$, and
  equality iff $\alpha = \beta$ (Corollary 1). Its proofs compare series coefficients (symmetric
  case) and analyse the second-order Kummer ODE with Rolle-type arguments (§2.3, non-symmetric).
* **The proof in §3.3 is not the source's**: it is a first-order Riccati comparison, one case,
  about six steps. My numerical check (8 pairs, $t \in [-40, 40]$) gave
  $\max(\log\varphi_0 - \mu_0 t - \sigma^2t^2/2) = -9.8\cdot10^{-4}$ and
  $\max \operatorname{sign}(t)\,z(t) = -1.8\cdot10^{-4}$. The reviewer's independent check
  (10 pairs) gave $\max t\,z(t) = 0$ and $\max g = 4\cdot10^{-9}$ (rounding), plus a
  line-by-line derivation.
* The prototype library is not on this machine. Nothing was read from it.
* Read: CONTRIBUTING §§1–3, 5, 8 and the rules digest, AGENTS, `NLAlib/Probability/RULES.md`,
  `docs/design/Estimation-SLQ.md` (§§0, 3.8, 4–6, 9–11), `docs/design/Probability-P7.md` (style).
  Code read: `Probability/Distributions/{ChiSquare,ChiSquareMoments,Gaussian}.lean`,
  `RandomMatrix/Haar/{Basic,Sphere}.lean`, `Probability/SubGaussian/Basic.lean`,
  `ForMathlib/Probability/Independence/Basic.lean`,
  `ForMathlib/Analysis/SpecialFunctions/Gamma/Basic.lean`. Mathlib read:
  `Probability/Distributions/{Beta,Gamma}.lean`, `Probability/Moments/{SubGaussian,MGFAnalytic}.lean`.
* Reused as proof material: the polar-coordinates proof of `ChiSquareMoments.lean` (moved, R1). In
  `Sphere.lean`, the rotation $\mathbf W = [\mathbf V\ \mathbf V']^{\mathsf H}$ of the private
  `measureReal_mem_le_of_two_weights` (`HasOrthonormalCols.exists_fromCols`,
  `hasLaw_mulVec_of_hasLaw_gaussianVector`), copied into β3 as a pattern, not as a call (that
  helper is about events).

Mathlib search (pinned Mathlib, `0df444a`, 2026-08-21):

| Looked for | Found | Use |
|---|---|---|
| chi-square law | searched `chi`, `chiSq`, `chiSquare` in `Mathlib/`: none | β1 new |
| Gamma ratio, sum of Gammas | none; `gammaMeasure` is used only by `expMeasure` | β2 new |
| Beta facts | `betaMeasure`, `betaPDF`, `betaPDFReal`, `lintegral_betaPDF_eq_one`, `isProbabilityMeasureBeta` (a lemma), `beta_eq_betaIntegralReal`; no moments, no mgf, no support lemma | β4c's support lemma new (private) |
| Beta mgf, ${}_1F_1$ | `OrdinaryHypergeometric` (${}_2F_1$), `RegularizedHypergeometric` (${}_pF_q$, regularized); no Kummer equation, no Beta mgf bound | not used; Kummer's equation is β4a–β4b |
| sub-Gaussian | `HasSubgaussianMGF`; `hasSubgaussianMGF_of_mem_Icc` (Hoeffding's lemma: proxy $1/4$ on $[0,1]$, the dimension-free bound this stage sharpens); `HasSubgaussianMGF.sum_of_iIndepFun`, `.congr`, `.zero`; NLAlib `HasSubgaussianMGF.measureReal_abs_ge_le` | β5, β6 |
| mgf derivatives | `hasDerivAt_integral_pow_mul_exp_real`, `hasDerivAt_mgf`, `iteratedDeriv_mgf`; `deriv_cgf`, `iteratedDeriv_two_cgf` (tilted mean and variance; missed in the draft, review 5) | β4c (exact overlap; one-line use); the cgf forms are an alternative to `betaExpMoment`, not used |
| standard Gaussian on Euclidean space | `stdGaussian E`, `map_pi_eq_stdGaussian` (`Gaussian/Multivariate.lean`; missed in the draft, review 5) | not used (NLAlib's `gaussianVector` is `Measure.pi`); named as the upstream target in `ChiSquared.lean` |
| sub-Gaussian transfer | `HasSubgaussianMGF.id_map_iff` | β4h, the `HasLaw` corollary |
| 1-D substitution | `lintegral_image_eq_lintegral_abs_deriv_mul` (`Function/JacobianOneDim.lean`); `integral_comp_rpow_Ioi` | β2a; β1a ($y \mapsto y^2$) |
| Gamma integral | `Real.integral_rpow_mul_exp_neg_mul_Ioi` | β2c |
| Tonelli, product split | `lintegral_lintegral_swap`; `measurePreserving_sumPiEquivProdPi`, `indepFun_iff_map_prod_eq_prod_map_map`; NLAlib `IndepFun.lintegral_comp_eq_lintegral_lintegral_of_hasLaw` | β2b, β2 (joint law); β3a |
| FTC on $[0,1]$ | `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` | β4a |
| monotone from derivative | `antitoneOn_of_deriv_nonpos`, `monotoneOn_of_deriv_nonneg`; Gronwall `norm_le_gronwallBound_of_norm_deriv_right_le` does not cover a coefficient singular at $0$ | β4e (composition, no exact overlap), β4g |

No exact overlap ships as an independent proof. β4c's derivative lemma is a one-line use of
Mathlib's.

## 7. Open questions

* **Q1. Where the $\chi^2$ law gets its density.**
  (a) Move NLAlib's polar formula into ForMathlib (R1) and derive the law in ForMathlib.
  (b) Prove it in ForMathlib from scratch, as $g^2 \sim \mathrm{Gamma}(1/2,1/2)$ plus "a sum of
  independent Gammas is Gamma" (convolution and the Beta integral, about 3 M steps). This gives an
  extra upstream theorem but has no consumer.
  (c) State it in NLAlib only, with `gaussianVector`.
  **Recommend (a)**: it is the least new proof (the move is mechanical), it puts a general fact
  where P9 wants it, and (c) contradicts the brief's Mathlib-first instruction. Reviewer agrees,
  with the `stdGaussian` docstring note (adopted).
* **Q2. A `chiSquared d` abbrev?** **Recommend no.** Write `gammaMeasure (d / 2) (1 / 2)` (one
  spelling, Mathlib's), and leave an abbrev to the upstream PR. Reviewer agrees; "chi-square"
  goes in the docstring so search finds it (adopted).
* **Q3. Proof route for the Beta proxy.**
  (a) The Riccati comparison of §3.3 now, citing MA 2017 for the result.
  (b) Wait for the PDF and transcribe MA's own proof, which has separate symmetric and
  non-symmetric cases.
  **Recommend (a)**: it is written out to the line level, is checked numerically, has one case,
  and needs no hypergeometric API. Reviewer agrees: MA's proof would be several L rows in Lean.
  The docstring cites Theorem 1 and says the proof differs (adopted).
* **Q4. File for β3–β6.**
  (a) `RandomMatrix/Haar/Sphere.lean`, which grows to about 980 lines, near F10's 1000.
  (b) A new `RandomMatrix/Haar/SphereProjectionLaw.lean`, which needs two private helpers of
  `Sphere.lean` made public.
  **Recommend (a)**, with a dated split amendment (the fourth-moment section into its own file) if
  the implemented file passes 1000. Reviewer: (a) is acceptable. After making
  `ae_norm_eq_one` public, (b) costs one six-line helper, so it is equally fine.

## 8. Proof plan for dispatch

The skeleton (wave 0, the orchestrator) puts every statement of §3, public and private, in place
with a `sorry` body, together with `betaExpMoment`, the module docstrings, the R1 statement move
and the rename of `ae_norm_eq_one`. Definitions are not dispatched. Once the skeleton exists,
**every row runs in parallel**: a row that uses a sibling needs only its statement. The waves are
advisory: they catch a wrong low-level statement before its consumers are attempted. Three chains
are fully independent of each other: the χ² chain {R1, β1a, β1, β1h, β1′}, the Gamma-ratio chain
{β2a-i, β2a-ii, β2b, β2c, β2, β2h} and the Beta-proxy chain {β4a-i–β4g, β4, β4h}. The sphere chain
{AE, β3a, β3b, β3, β5, β6} uses the other three chains' statements. Each proof is at most 80 lines
(S4). The splits below are mandatory (review 8).

Row names: β1, β2 and β4 are the measure-level primaries. β1h, β2h and β4h are their `HasLaw`
corollaries, which keep the draft's names and signatures.

| # | Name | File | Deps | Diff. (lines) | Key lemmas | Wave |
|---|---|---|---|---|---|---|
| R1 | move `integral_comp_norm_pi_gaussianReal` (+ private density lemma); re-derive `integral_comp_norm_of_hasLaw_gaussianVector` and the private moment lemma | ForMathlib ChiSquared; `ChiSquareMoments.lean` | — | M (30–50, mostly moved code) | the existing proofs with `gaussianVector` unfolded to `Measure.pi`; `HasLaw.integral_comp`; `integral_pow_mul_exp_mul_rpow` (stays private in ChiSquareMoments) | 1 |
| β1a | `measureReal_sum_sq_mem_pi_gaussianReal` (private) | ForMathlib ChiSquared | R1 | M (35–55) | `integral_comp_norm_pi_gaussianReal` with `φ := S.indicator 1 ∘ (· ^ 2)` (`EuclideanSpace.real_norm_sq_eq`); `integral_comp_rpow_Ioi` with `p := 2`; `gammaMeasure`, `withDensity_apply`, `gammaPDF_of_nonneg`, `ofReal_integral_eq_lintegral_ofReal`, `measureReal_def`; `Real.rpow_natCast`, `Real.rpow_mul` | 1 |
| β1 | `map_sum_sq_pi_gaussianReal` | ForMathlib ChiSquared | β1a | S (15–25) | `Measure.ext` through `measureReal` with finiteness (`isProbabilityMeasure_gammaMeasure`, `Measure.isProbabilityMeasure_map`), `Measure.map_apply` | 2 |
| β1h | `hasLaw_sum_sq_of_hasLaw_pi_gaussianReal` | ForMathlib ChiSquared | β1 | S (3–6) | `HasLaw.fun_comp`/`HasLaw.comp` with `hg`; β1 | 3 |
| β1′ | `hasLaw_norm_sq_of_hasLaw_gaussianVector` | `ChiSquare.lean` | β1h | S (3) | the checked one-liner (§3.1) | 3 |
| β2a-i | `image_mul_div_one_sub_Ioo`, `injOn_mul_div_one_sub`, `hasDerivAt_mul_div_one_sub` (private, one bundle) | ForMathlib Beta | — | S (20–30 total) | image: inverse $x \mapsto x/(x+y)$, `Set.ext`, `field_simp`; `InjOn` by cross-multiplication; `HasDerivAt.div` (`hasDerivAt_id`, `HasDerivAt.const_mul`, `HasDerivAt.const_sub`) | 1 |
| β2a-ii | `lintegral_Ioi_comp_div_add` (private) | ForMathlib Beta | β2a-i | M (30–45) | `lintegral_image_eq_lintegral_abs_deriv_mul` on `Ioo 0 1` (β2a-i for the image, injectivity and `HasDerivWithinAt`); `Real.mul_rpow`, `Real.div_rpow`, `Real.rpow_neg`, `Real.rpow_add` inside `ENNReal.ofReal`; $x/(x+y) = s$ by `field_simp` | 2 |
| β2b | `lintegral_lintegral_comp_div_add_gammaPDF` (private) | ForMathlib Beta | β2a-ii | M (45–65) | restrict both integrals to `Ioi 0` (`gammaPDF_of_neg`, the point $0$ is null); β2a-ii per $y$; `lintegral_lintegral_swap`; `lintegral_const_mul'`; `ofReal_integral_eq_lintegral_ofReal` for the $y$-integral; `Real.exp_add` | 3 |
| β2c | `lintegral_lintegral_comp_div_add_gammaPDF_eq_betaPDF` (private) | ForMathlib Beta | β2b | M (30–50) | `Real.integral_rpow_mul_exp_neg_mul_Ioi` with $r/(1-s)$; `ProbabilityTheory.beta`, `betaPDF_of_pos_lt_one`, `betaPDF_eq_zero_of_nonpos`, `…_of_one_le` (extend from `Ioo 0 1` to ℝ); constants with `Real.Gamma_pos_of_pos` | 4 |
| β2 | `map_div_add_prod_gammaMeasure` | ForMathlib Beta | β2c | M (25–40) | `Measure.ext`; `Measure.map_apply` (measurability of $p \mapsto p.1/(p.1+p.2)$), `Measure.prod_apply` / `lintegral_prod`, `gammaMeasure`, `lintegral_withDensity_eq_lintegral_mul₀` twice, β2c with $F = 1_S$, `withDensity_apply` | 5 |
| β2h | `hasLaw_div_add_of_hasLaw_gammaMeasure` | ForMathlib Beta | β2 | S (5–10) | `indepFun_iff_map_prod_eq_prod_map_map` gives the law of $(X, Y)$ as `(gammaMeasure a r).prod (gammaMeasure b r)` (`hX.map_eq`, `hY.map_eq`); `HasLaw.comp`; β2 | 6 |
| β4a-i | `hasDerivAt_rpow_mul_rpow_mul_exp` (private) | ForMathlib Beta | — | S (20–30) | `HasDerivAt.rpow_const` (base $\ne 0$ on `Ioo 0 1`), `.mul`, `Real.hasDerivAt_exp`, `HasDerivAt.const_sub`; `Real.rpow_sub_one`; `ring` | 1 |
| β4a-ii | `intervalIntegrable_rpow_mul_rpow_mul_exp` (private) | ForMathlib Beta | — | M (25–35) | a bounded continuous factor (on `Icc 0 1`) times `betaPDFReal`; integrability of `betaPDFReal` from `lintegral_betaPDF_eq_one` (finite `ℝ≥0∞` lintegral of `ofReal`: `integrable_of_lintegral…`/`HasFiniteIntegral`); `IntervalIntegrable.mul_continuousOn`; `intervalIntegrable_iff_integrableOn_Ioo_of_le` | 1 |
| β4a-iii | `intervalIntegral_rpow_mul_rpow_mul_exp_eq_zero` (private) | ForMathlib Beta | β4a-i, β4a-ii | S (10–20) | `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` with `ContinuousOn` on `Icc` (`ContinuousAt.rpow_const` with $0 < \alpha$; `Real.zero_rpow`); endpoint values $0$ | 2 |
| β4b | `integral_sub_mul_add_mul_exp_betaMeasure` (private) | ForMathlib Beta | β4a-iii | M (25–40) | `integral_withDensity_eq_integral_toReal_smul` (`measurable_betaPDFReal`), `ENNReal.toReal_ofReal` (nonnegativity of `betaPDFReal`), `setIntegral_eq_integral_of_forall_compl_eq_zero`, `intervalIntegral.integral_of_le`, `integral_Ioc_eq_integral_Ioo`, `integral_const_mul` | 3 |
| β4c | `ae_mem_Icc_betaMeasure`, `hasDerivAt_betaExpMoment`, `betaExpMoment_zero_pos` (private, one bundle) | ForMathlib Beta | — | S (25–35 total) | `haveI := isProbabilityMeasureBeta hα hβ` (a lemma, not an instance; review 9); `withDensity_apply`, `betaPDF_eq_zero_of_nonpos`, `…_of_one_le`; exponential integrability from boundedness on the support (`Integrable.of_bound`), so `interior (integrableExpSet id _) = univ`; `hasDerivAt_integral_pow_mul_exp_real`; `integral_exp_pos` | 1 |
| β4d | `mul_sub_add_mul_sub_eq` (private) | ForMathlib Beta | β4b, β4c | S (15–25) | β4b split by `integral_add`, `integral_sub`, `integral_const_mul` into $\alpha\varphi_0 - b\varphi_1 + t(\varphi_1 - \varphi_2) = 0$; `field_simp` with `betaExpMoment_zero_pos`; `linear_combination` | 4 |
| β4e | `antitoneOn_rpow_mul_of_hasDerivAt` | ForMathlib MeanValue | — | S (15–25; review 6) | `antitoneOn_of_deriv_nonpos` on `Ici 0` (`convex_Ici`, `interior_Ici`); continuity at $0$ (`Real.continuousAt_rpow_const`, `Real.zero_rpow hb.ne'`, `ContinuousWithinAt.mul`); `Real.hasDerivAt_rpow_const`; derivative $t^{b-1}(tf' + bf)$ by `Real.rpow_sub_one` | 1 |
| β4f | `mul_sub_div_sub_div_nonpos` (private) **— Lean risk** | ForMathlib Beta | β4c, β4d, β4e | M (45–65; split hint: the $t > 0$ and $t < 0$ halves as two private lemmas, 25–35 each) | $z(t) = y(t) - \mu_0 - \sigma^2 t$, `HasDerivAt.div` (β4c, φ₀ > 0); for $t > 0$: β4e with $f = z$, $b = \alpha+\beta$, hypothesis from β4d and $y(1-y) \le 1/4$ (`nlinarith [sq_nonneg (y - 1/2)]`), then evaluation at $0$ (`Real.zero_rpow`) and `Real.rpow_pos_of_pos`; for $t < 0$: β4e with $f(s) = -z(-s)$ (`HasDerivAt.comp_neg`, `HasDerivAt.neg`); $t = 0$ trivial | 5 |
| β4g | `log_betaExpMoment_sub_le` (private) | ForMathlib Beta | β4c, β4f | M (35–55) | $g(t) = \log\varphi_0 - \mu_0 t - t^2/(8(b+1))$, `HasDerivAt.log` with derivative $z$; $g(0) = 0$ (`integral_const`, probability, `Real.log_one`); `antitoneOn_of_deriv_nonpos` on `Ici 0`, `monotoneOn_of_deriv_nonneg` on `Iic 0`, signs from β4f | 6 |
| β4 | `hasSubgaussianMGF_sub_div_betaMeasure` | ForMathlib Beta | β4c, β4g | M (20–35) | `integrable_exp_mul` from β4c's boundedness; `mgf`, `Real.exp_sub`, `Real.exp_log` (β4c positivity), `Real.exp_le_exp`; proxy coercion (§3.3, checked) | 7 |
| β4h | `hasSubgaussianMGF_sub_div_of_hasLaw_betaMeasure` | ForMathlib Beta | β4 | S (5–10) | `HasSubgaussianMGF.id_map_iff` on both sides, `Measure.map_map`, `hX.map_eq` (the pattern of NLAlib's `hasSubgaussianMGF_of_hasLaw_gaussianReal`) | 8 |
| AE | `ae_norm_eq_one_uniformSphereVector` (rename of the private `ae_norm_eq_one`, public; update its uses) | `Sphere.lean` | — | S (0–5) | — | 1 |
| β3a | `indepFun_sum_sq_inl_sum_sq_inr_of_hasLaw_gaussianVector`, `hasLaw_sum_sq_inl_…`, `hasLaw_sum_sq_inr_…` (private, one bundle) | `Sphere.lean` | β1h | M (30–50 total) | `measurePreserving_sumPiEquivProdPi`, `indepFun_iff_map_prod_eq_prod_map_map`, `IndepFun.comp`, `Measure.map_map`, `Measure.map_fst_prod`/`map_snd_prod`; β1h on each block | 2 |
| β3b | `norm_conjTranspose_mulVec_inv_norm_smul_sq_eq_div` (private) | `Sphere.lean` | — | S (20–30) | `norm_conjTranspose_mulVec_inv_norm_smul_sq` (existing, private); `Matrix.fromCols` mulVec on `Sum.inl` (as `hWl` in `measureReal_mem_le_of_two_weights`); $\|\mathbf W\mathbf g\| = \|\mathbf g\|$ for orthogonal $\mathbf W$ (`HasOrthonormalCols.conjTranspose_of_card_eq`); `EuclideanSpace.real_norm_sq_eq`, `Fintype.sum_sum_type` | 1 |
| β3 | `hasLaw_norm_conjTranspose_mulVec_sq_of_hasLaw_uniformSphereVector` | `Sphere.lean` | β3a, β3b, β2h | M (40–55) | `Nat.exists_eq_add_of_le`, `HasOrthonormalCols.exists_fromCols`; reduce to `gaussianVector n` (`uniformSphereVector`, `HasLaw.fun_comp`, `measurable_inv_norm_smul`, `HasLaw.id`); `hasLaw_mulVec_of_hasLaw_gaussianVector` (allows `Matrix (k ⊕ p) n`); β3b pointwise (`HasLaw.congr`); β2h with $a = k/2$, $b = c/2$, $r = 1/2$; `Nat.cast_add` | 3 |
| β5 | `hasSubgaussianMGF_norm_conjTranspose_mulVec_sq_sub_of_hasLaw_uniformSphereVector` | `Sphere.lean` | AE, β3, β4h | M (40–60) | cases: $k = 0$ (`Fintype.card_eq_zero_iff`, `HasSubgaussianMGF.zero` with `congr`); $k = n$ (AE; $\|\mathbf V^{\mathsf H}\mathbf u\| = \|\mathbf u\|$ for square `V` via `HasOrthonormalCols.conjTranspose_of_card_eq`; `congr` to `0`); else β3, β4h, with $\alpha+\beta = n/2$ and $\alpha/(\alpha+\beta) = k/n$ rewritten (`field_simp`; proxies equal in `ℝ≥0` via `NNReal.eq`) | 4 |
| β6 | `measureReal_abs_sum_…_of_hasLaw_uniformSphereVector` | `Sphere.lean` | β5 | M (25–40) | `iIndepFun.isProbabilityMeasure`; empty `m` (`measureReal_le_one`); `iIndepFun.comp`; `HasSubgaussianMGF.sum_of_iIndepFun`; `HasSubgaussianMGF.measureReal_abs_ge_le` at $\varepsilon = m\tau$; event equality (`Finset.sum_sub_distrib`, `Finset.sum_const`, `abs_div`, `le_div_iff₀`); $(m\tau)^2/(2\cdot m/(2(n+2))) = m(n+2)\tau^2$ | 5 |

Counts: 28 dispatched rows: **S 13** (β1, β1h, β1′, β2a-i, β2h, β4a-i, β4a-iii, β4c, β4d, β4e, β4h,
AE, β3b), **M 15**, **L 0**. No row is expected to exceed 65 lines.

**Lean-risk step: β4f** (with β4e, its comparison lemma). The reviewer checked the mathematics
line by line and found it sound and complete (§6), so there is no research risk left. The Lean
risk is the singular point $t = 0$, which costs nothing mathematically since $z(0) = 0$: the
continuity of $z$ there, and the reflected application for $t < 0$. Fallbacks, in order:
(i) prove only $t > 0$ in β4f, and get $t < 0$ from `map_one_sub_betaMeasure : (betaMeasure α
β).map (fun x => 1 - x) = betaMeasure β α` (elaborates; about 30 lines; upstream-worthy). The bound
for $-t$ on $\mathrm{Beta}(\beta, \alpha)$ is the bound for $t$ on $\mathrm{Beta}(\alpha, \beta)$.
(ii) state β4e on `Ioi 0` without the continuity hypothesis, and take the limit at $0$ in β4f.
Brief the β4f worker with §3.3 in full. The statements of β4g, β4 and β4h do not depend on how β4f
is proved.

Suggested waves: **1** R1, β1a, β2a-i, β4a-i, β4a-ii, β4c, β4e, AE, β3b (leaves; β4c, AE and β3b
calibrate). **2** β1, β2a-ii, β4a-iii, β3a. **3** β1h, β1′, β2b, β4b, β3. **4** β2c, β4d, β5. **5**
β2, β4f, β6. **6** β2h, β4g. **7** β4. **8** β4h. Since every statement is fixed, β3, β5 and β6 can
start as soon as they are dispatched; the waves only order acceptance. SLQ's E1–E4 (its wave S)
can start from the skeleton, since they use only β6's statement (E3 also uses AE). Their
acceptance is final when β6 and its dependencies are proved (`#print axioms`).

Memory (CONTRIBUTING §10): the ForMathlib rows import only Mathlib's probability files. Prefer
them for parallel workers. The `Sphere.lean` rows load `NLAlib.RandomMatrix.Haar.Sphere`'s
imports, several GB per Lean server, so run at most two at a time on this machine.
