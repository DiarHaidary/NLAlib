# Estimation: stochastic Lanczos quadrature

Status: drafted 2026-10-24 by an Opus agent from the orchestrator's brief; Fable review folded in
2026-10-24; awaiting the maintainer.

Branch `design/ks7-slq` (worktree `/home/ubuntu/nlalib-design`, head `6a845a2`). This is the SLQ
half of roadmap stage K7 (`docs/PORT_KRYLOV.md` §8, "K7 Hutch++ and SLQ"; Hutch++ is done,
`docs/design/Estimation-HutchPP.md`). It is the Estimation design that `docs/design/Krylov-Spectral.md`
§8 item 6 deferred ("SLQ itself (`slq`, its tails, the spectral-density form) … an Estimation design
using KS3"). Every signature in §3 was elaborated against the built tree with `sorry` bodies
(scratch files under `/tmp/claude-1000/slq-scratch/`, importing only
`NLAlib.Krylov.Functions.Quadrature`, `NLAlib.Estimation.Trace.GirardHutchinson`,
`NLAlib.Polynomial.Approximation.{Jackson,AnalyticApproximation}`); they are final unless a question
in §10 changes them. Exact arithmetic only: finite precision is excluded, as the briefs record
(`docs/PORT_KRYLOV.md` §10 question 4).

## Changes after the Fable review (2026-10-24)

Review: `nlalib-harness/reports/Review-Estimation-SLQ.md` (11 comments: 1 blocking, 4 should,
6 consider). Signatures changed by it were re-elaborated with `sorry` bodies
(`/tmp/claude-1000/slq-scratch/Shapes5.lean`).

1. **[blocking] Deterministic quadrature term in D17, D18. Adopted.** On the complement of the
   Kolmogorov event D13, the CDFs at $\lambda_{\max}$ give
   $\lvert 1 - \|\mathbf\Omega\|_{\mathsf F}^2/(nm)\rvert \le \tau$ (new D20), so the quadrature
   term is $\frac{\pi L(b-a)}{2q+3}(1+\tau)$ at the same probability; `frobNorm (X ω)` is gone from
   both events (§0, §3.5, §3.6). The trace tails T5–T7 keep the random term (Q9(a)); §3.2 says why.
   Q4 and Q9 updated; the ratio-estimator corollary D19 added (comment 11).
2. **[should] Attribution. Adopted.** New key `ChenTrogdonUbaru2021` (ICML 2021, PMLR 139) cited
   on D13, D16–D19 and in §0; `ChenTrogdonUbaru2022` kept for Appendix C, Theorem 38 (D15, T3);
   the SISC version (`ChenTrogdonUbaru2025`) only for its own unified SLQ/KPM results, once a
   locator is confirmed. All bib fields "to check" (§7).
3. **[should] `girardHutchinson_smul`. Adopted:** row G1, wave 1, a dependency of D12.
4. **[should] Public integrability. Adopted:** `integrable_probeSpectralMeasure`,
   `integrable_slqMeasure` (I3, I4, wave 1); D1, D2, D9, D15 use them; D2 no longer reaches for a
   private lemma.
5. **[should] C1 is L. Adopted** (§3.7, §9, §0).
6. **[consider] Kolmogorov over all `x : ℝ`. Adopted** as the deterministic corollary D21 (S):
   a user of eigenvalue counts at arbitrary thresholds gets it without redoing the
   piecewise-constancy argument; D13's statement stays over the spectrum (it is the union bound).
7. **[consider] `Matrix.IsHermitian.im_slq`. Adopted** (T8, S): makes the `RCLike.re` of D2 and
   the density statements visibly harmless over `ℂ`.
8. **[consider] Mathlib route for X2. Adopted** in §6 and the X2 row
   (`isStarProjection_iff_spectrum_subset_and_isSelfAdjoint`, `isIdempotentElem_iff_spectrum_subset`,
   `cfc_map_spectrum`); the worker may use either route.
9. **[consider] F3 near-overlap; `Measure.ext_of_Iic`. Adopted:** §3.1 and §6 say F3 is
   `Measure.restrict_eq_self_of_ae_mem` then `setIntegral_finset`; `MeasureTheory.ext_of_Iic`
   listed in §6.
10. **[consider] `≥` vs `>` events. Adopted:** one paragraph at the head of §3.
11. **[consider] Ratio estimator. Adopted** as D19 (S/M). The review's $2\tau/(1-\tau)$ improves to
    $2\tau$ (§3.5), with $\tau < 1$ kept only to make the mass positive.

Open question 11 (dispatch rules) is removed: the maintainer approved parallel proving (branch
`workflow/agent-hierarchy`, `586dc1a`), and dispatch follows that branch's CONTRIBUTING §11.

## 0. Summary

**Scope proposed (phases A and B; phase C optional).**

* **A. Trace estimation of $\operatorname{tr} f(\mathbf{A})$.** The estimator `slq`; the
  deterministic split of its error into the Girard–Hutchinson error plus a quadrature error
  $2\varepsilon\|\mathbf{\Omega}\|_{\mathsf{F}}^2/m$ (the C6/KS3a consumer), with the Lipschitz
  (Jackson) and analytic (Bernstein ellipse) rates of KS4; and the sub-Gaussian tails, by
  composing the split with the existing Hanson–Wright tail of Girard–Hutchinson. Eight
  declarations, all short: the library already has every analytic ingredient.
* **B. Spectral density estimation.** Two measures, the *probe spectral measure*
  $\frac{1}{nm}\sum_j\mu_{\mathbf{A},\boldsymbol{\omega}_j}$ (SLQ with exact quadrature) and the
  *SLQ measure* $\frac{1}{nm}\sum_j\mathsf{lanczosQuadrature}(\mathbf{A},\boldsymbol{\omega}_j,q)$;
  their integral identities, masses, supports, moment matching; unbiasedness of the probe measure
  for isotropic probes (Gaussian, Rademacher, sphere and Haar-frame probes are instances, no
  independence needed); and **the Chen–Trogdon–Ubaru-type uniform bound**: with $m$ probes with
  independent sub-Gaussian entries, outside probability
  $2n\exp(-\tfrac{1}{196}mn\min(\tau^2/c^2,\tau/c))$, every $L$-Lipschitz test function $f$ on
  $[a,b] \supseteq \operatorname{spec}\mathbf{A}$ has
  $$\Bigl\lvert\int f\,d\nu_{\mathbf{A}} - \int f\,d\,\mathsf{slqMeasure}(\mathbf{A},\mathbf{\Omega},q+1)\Bigr\rvert
  \le (\lvert f(b)\rvert + L(b-a))\tau + \frac{\pi L(b-a)}{2q+3}(1+\tau),$$
  $\nu_{\mathbf{A}}$ the empirical spectral measure [ChenTrogdonUbaru2021], a normalised
  (probability-measure) form with $2L(b-a)\tau + \pi L(b-a)/(2q+3)$; and its "$m = O(c^2\log(n/\delta)/(n\tau^2))$
  suffices" asymptotic form. **I put the uniform bound in scope now** (the brief left it open):
  the route below needs no Wasserstein distance, no Stieltjes integration by parts and no new
  probability. It is a finite Abel summation on the spectrum (the CDFs of both measures jump only
  at eigenvalues), the observation that the CDF of the probe measure at $x$ is a Girard–Hutchinson
  estimate of the trace of the spectral projector $\mathbf{1}_{(-\infty,x]}(\mathbf{A})/n$, the
  existing Girard–Hutchinson tail, and a union bound over at most $n$ eigenvalues. The longest
  proof is about 70 lines.
* **C (optional, recommend a later PR). The bias of SLQ in expectation**,
  $\lvert\operatorname{tr}f(\mathbf{A}) - \mathbb{E}\,\mathsf{slq}\rvert \le 2\varepsilon n$. It
  needs measurability of $\mathbf{b} \mapsto \mathsf{lanczosFA}(\mathbf{A}, f, \mathbf{b}, q)$,
  which the library does not have (§3.7, Q6).

**Out of scope:** KPM (needs M1 and the noisy Jackson coefficient bound J1, both unimplemented;
`Krylov-Spectral.md` §8 item 5); sphere/Haar-probe *tails* with the sharp Beta constant (needs a
sub-Gaussian bound for Beta laws, absent; §11); a named Wasserstein or Kolmogorov distance (Q4);
Gauss–Radau one-sided bounds (needs the Hermite remainder, `Krylov-Spectral.md` §8 item 3); finite
precision.

**Counts** (after the review). 45 declarations in phases A and B (3 definitions, 2 instances,
40 theorems), of which 10 are additions to existing or ForMathlib files; of the 42 dispatched
proofs, S 33, M 9, L 0 (§9; one of the S is a rename). Phase C adds 2 (M, L). No new hypothesis interface. Three new
§5.3 rows. No named bound.

**Nothing from KS7 is needed** (§12): every quadrature fact SLQ uses is already proved in
`Krylov/Functions/Quadrature.lean` (KS3) and `Polynomial/Orthogonal/Moments.lean` (M0).

## 1. Objects

All definitions over `[RCLike 𝕜]`, total, in `namespace NLAlib`, probes as the columns of a test
matrix `Ω : Matrix n m 𝕜`, exactly as `girardHutchinson` (§5.3 row "Girard–Hutchinson estimate").
Columns are written `fun i => Ω i j`, the spelling of `girardHutchinson_eq_sum` (Mathlib's
`Ω.col j` unfolds to it by `Matrix.col_apply`; `frobNorm_sq_eq_sum_col` uses `.col`).

### 1.1 The SLQ trace estimate

```lean
/-- The **stochastic Lanczos quadrature** estimate of $\operatorname{tr} f(\mathbf{A})$ from the
test matrix $\mathbf{\Omega}$, whose $m$ columns $\boldsymbol{\omega}_1, \dots,
\boldsymbol{\omega}_m$ are the probes, with $q$ Lanczos steps per probe:
$$\mathsf{slq}(\mathbf{A}, f, \mathbf{\Omega}, q) := \frac{1}{m}\sum_{j=1}^m
\boldsymbol{\omega}_j^{\mathsf{H}}\,\mathsf{lanczosFA}(\mathbf{A}, f, \boldsymbol{\omega}_j, q)\,,$$
the Girard–Hutchinson estimate with each quadratic form
$\boldsymbol{\omega}_j^{\mathsf{H}}f(\mathbf{A})\boldsymbol{\omega}_j$ replaced by its $q$-node
Gauss (Lanczos) quadrature
$\|\boldsymbol{\omega}_j\|^2\mathbf{e}_1^{\mathsf{T}}f(\mathbf{T}_j)\mathbf{e}_1$
(`Matrix.IsHermitian.integral_lanczosQuadrature_succ`). Uses $mq$ products with $\mathbf{A}$.
Junk value: $0$ when $\mathbf{\Omega}$ has no columns or $q = 0$.
[UbaruChenSaad2017, §3, (3.x), locator to check]; [MartinssonTropp2020, §6.6, Algorithm 6]. -/
noncomputable def slq (A : Matrix n n 𝕜) (f : ℝ → ℝ) (Ω : Matrix n m 𝕜) (q : ℕ) : 𝕜 :=
  (∑ j, star (fun i => Ω i j) ⬝ᵥ lanczosFA A f (fun i => Ω i j) q) / Fintype.card m
```

Normalisation. The brief's form $\frac1m\sum_j\|\boldsymbol\omega_j\|^2\,\mathsf{lanczosQuadrature}(\mathbf A,\boldsymbol\omega_j,q)(f)$
is this one: `lanczosQuadrature A b q` is unnormalised, of mass $\|\mathbf b\|^2$
(`Matrix.IsHermitian.lanczosQuadrature_real_univ`), so
$\int f\,d\,\mathsf{lanczosQuadrature}(\mathbf A,\mathbf b,q) = \operatorname{Re}\mathbf b^{\mathsf H}\mathsf{lanczosFA}(\mathbf A,f,\mathbf b,q)$
(`integral_lanczosQuadrature`) already carries the $\|\mathbf b\|^2$. The value is in `𝕜`, like
`girardHutchinson`, so the error reads `(cfc f A).trace - slq A f Ω q` (N10) and its difference
with `girardHutchinson (cfc f A) Ω` is a sum of the C6 quantities with no `RCLike.re`. For
Hermitian $\mathbf A$ the value is real (each term is a quadratic form of the Hermitian
compression); no theorem needs that.

Argument order follows `lanczosFA A f b q` and `girardHutchinson A Ω`: matrix, function, probes,
steps.

### 1.2 The two spectral-density estimates

```lean
/-- The **probe spectral measure**: the average of the spectral measures of the probes, scaled so
that isotropic probes give the empirical spectral measure in expectation,
$$\mathsf{probeSpectralMeasure}(\mathbf{A}, \mathbf{\Omega}) :=
\frac{1}{\lvert n\rvert m}\sum_{j=1}^m \mu_{\mathbf{A},\boldsymbol{\omega}_j}\,.$$
It is stochastic Lanczos quadrature with exact quadrature
(`Matrix.IsHermitian.slqMeasure_eq_probeSpectralMeasure_of_card_le`), and its integral of $f$ is
the Girard–Hutchinson estimate of $\operatorname{tr} f(\mathbf{A})/\lvert n\rvert$
(`integral_probeSpectralMeasure`). Its mass is
$\|\mathbf{\Omega}\|_{\mathsf{F}}^2/(\lvert n\rvert m)$, not $1$. Junk value: $0$ when $n$ or $m$
is empty ($0^{-1} = 0$ in $\mathbb{R}_{\ge 0}$) and when $\mathbf{A}$ is not Hermitian.
[ChenTrogdonUbaru2022, §2, the averaged weighted spectral measure, locator to check]. -/
noncomputable def probeSpectralMeasure (A : Matrix n n 𝕜) (Ω : Matrix n m 𝕜) : Measure ℝ :=
  ((Fintype.card n * Fintype.card m : ℝ≥0)⁻¹) • ∑ j, spectralMeasure A (fun i => Ω i j)

/-- The **SLQ spectral-density estimate**: the average of the $q$-step Lanczos (Gauss) rules of
the probes, scaled as `probeSpectralMeasure`,
$$\mathsf{slqMeasure}(\mathbf{A}, \mathbf{\Omega}, q) := \frac{1}{\lvert n\rvert m}\sum_{j=1}^m
\mathsf{lanczosQuadrature}(\mathbf{A}, \boldsymbol{\omega}_j, q)\,;$$
atoms at the Ritz values of each probe's Krylov space, weights $\|\boldsymbol\omega_j\|^2$ times
the squared first entries of the eigenvectors of $\mathbf{T}_j$
(`Matrix.IsHermitian.lanczosQuadrature_succ_eq_sum`). Its integral of $f$ is
$\operatorname{Re}\,\mathsf{slq}(\mathbf{A}, f, \mathbf{\Omega}, q)/\lvert n\rvert$
(`integral_slqMeasure`). Junk value: $0$ when $n$ or $m$ is empty or $q = 0$.
[ChenTrogdonUbaru2022, locator to check]; [UbaruChenSaad2017, §3, locator to check]. -/
noncomputable def slqMeasure (A : Matrix n n 𝕜) (Ω : Matrix n m 𝕜) (q : ℕ) : Measure ℝ :=
  ((Fintype.card n * Fintype.card m : ℝ≥0)⁻¹) • ∑ j, lanczosQuadrature A (fun i => Ω i j) q
```

The scalar is an `ℝ≥0`, not the `ℝ≥0∞` of `empiricalSpectralMeasure`: with `ℝ≥0∞` the scalar is
$\top$ for an empty type, and the `IsFiniteMeasure` instances would need a case split; with `ℝ≥0`
they are `infer_instance` and `integral_smul_nnreal_measure` rewrites integrals (checked). The
normalisation $1/(nm)$ is Q1; the consumer table of `Krylov-Spectral.md` §5 wrote
$m^{-1}\sum_j\mathsf{lanczosQuadrature}$, which has mean $n\,\nu_{\mathbf A}$ for isotropic probes.

Relation to `empiricalSpectralMeasure`: for isotropic probes
$\mathbb E\int f\,d\,\mathsf{probeSpectralMeasure} = \int f\,d\nu_{\mathbf A}$ (D11); for
$q \ge n$, `slqMeasure A Ω q = probeSpectralMeasure A Ω` (D10); with the coordinate vectors as
probes ($\mathbf\Omega = \mathbf I$) the probe measure is $\nu_{\mathbf A}$ exactly, by the existing
`Matrix.IsHermitian.sum_spectralMeasure_single` (no new theorem; noted in the docstring).

### 1.3 §5.3 rows (added in the implementing PRs)

| Concept | Spelling | Mathlib bridge |
|---|---|---|
| stochastic Lanczos quadrature | `slq A f Ω q : 𝕜 := (∑ j, star ωⱼ ⬝ᵥ lanczosFA A f ωⱼ q) / card m`, probes the columns of `Ω`; error `(cfc f A).trace - slq A f Ω q` | `integral_slqMeasure`; the split `Matrix.IsHermitian.norm_trace_cfc_sub_slq_le_of_isUniformApproxOn`; Mathlib has none |
| probe spectral measure | `probeSpectralMeasure A Ω := (card n * card m : ℝ≥0)⁻¹ • ∑ j, spectralMeasure A ωⱼ`; mass $\|\mathbf\Omega\|_{\mathsf F}^2/(nm)$; its CDF is `girardHutchinson` of a spectral projector | `integral_probeSpectralMeasure`, `probeSpectralMeasure_real`; Mathlib has none |
| SLQ spectral density | `slqMeasure A Ω q`, the same average of `lanczosQuadrature A ωⱼ q` | `integral_slqMeasure`, `Matrix.IsHermitian.slqMeasure_eq_probeSpectralMeasure_of_card_le` |

and `slq` joins the row "an algorithm's output" of §4.3 (tokens list). The CDF of a finite measure
on $\mathbb R$ is written `μ.real (Set.Iic x)`, not Mathlib's `ProbabilityTheory.cdf`, which is
defined for probability measures only (both estimates have random mass); no row, no deviation.

## 2. Interfaces

**No new interface.** Every hypothesis is an existing one:

* probes for expectations: `∀ j, IsIsotropic (fun ω i => X ω i j) μ` (as
  `integral_girardHutchinson`); Gaussian (`isIsotropic_of_hasLaw_gaussianVector`), Rademacher
  (`isIsotropic_of_hasLaw_rademacherVector`), $\sqrt n$ times uniform-sphere or Haar-frame columns
  (`isIsotropic_sqrt_mul_col_of_hasLaw_haarFrame`) are instances; no independence;
* probes for tails: the triple of `measureReal_abs_trace_sub_girardHutchinson_ge_le`, reused
  verbatim, not re-bundled — `hind : iIndepFun (fun p : n × m => fun ω => X ω p.1 p.2) μ`,
  `hsub : ∀ i j, HasSubgaussianMGF (fun ω => X ω i j) c μ`,
  `hvar : ∀ i j, ∫ ω, X ω i j ^ 2 ∂μ = 1` (Gaussian and sign test matrices: $c = 1$, by
  `hasSubgaussianMGF_of_hasLaw_gaussianReal`, as in the Hutch++ Gaussian instance);
* approximation: `Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a a') ε` with
  `p.degree < 2 * q` (the C6 shape), `LipschitzOnWith L f (Set.Icc a b)`, the Bernstein-ellipse
  triple `hFd hM hExt` of the KS4 analytic theorem;
* spectrum location `spectrum ℝ A ⊆ Set.Icc a b` (§5.3 row "location of the spectrum");
* moment matching `MatchesMoments` (SD2) appears as a conclusion (D9) and is consumed by M0.

Why no interface "probe law $P$": the expectation results need isotropy only and the tail results
need exactly the Girard–Hutchinson triple, so a bundle would wrap one existing interface.
The isotropic sub-Gaussian *vector* interface (`IsSubgaussianVector` + `IsIsotropic`, used by
Hutch++'s sketch) does not give the tails: Hanson–Wright in the library needs independent
coordinates (`Probability/QuadraticForm/HansonWright.lean`), so sphere and Haar probes are not
covered by the tails (Q3).

Why no distance: the Jackson note's W1 decision (`Polynomial-Jackson-Moments.md` §4, "W1
decision") recommends "universal Lipschitz test bounds first … do not invent a new Wasserstein
distance"; Mathlib has none (§6). The uniform statements quantify over test functions
(`∃ f, LipschitzOnWith L f … ∧ bound < |…|` in the event, N15's form for a negated `∀`). Q4.

## 3. Statement shapes

Conventions: `{𝕜 : Type*} [RCLike 𝕜] {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]`,
`{Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}`; `open MeasureTheory ProbabilityTheory
Polynomial`, `open scoped Matrix NNReal ENNReal`. Tails are over ℝ (Hanson–Wright is real);
everything else over `𝕜`. Statements quoted below compile with `sorry` bodies. Docstrings are
drafts in the library's style for headlines; the others say in one line what they are.

Event relations (review comment 10). The trace tails T5–T7 use `τ + … ≤ |…|` (`_ge_le`), the form
of the Girard–Hutchinson tail they are reduced to. The density tails D13, D16–D19 use `<`
(`_gt_le`, §5.3 row "tail"), because their complement is exactly the `≤` hypothesis that the
deterministic D14, D15, D20 consume. Both forms are allowed; they are not mixed within a theorem.

### 3.1 Additions below the stage (X, F)

```lean
-- X1, Matrix/Spectral/SpectralMeasure.lean: make the private `spectralMeasure_real_eq` public
theorem spectralMeasure_real (A : Matrix n n 𝕜) (b : n → 𝕜) (S : Set ℝ) :
    (spectralMeasure A b).real S =
      RCLike.re (quadForm (cfc (S.indicator fun _ => (1 : ℝ)) A) b)

-- X2, same file: the spectral projector 1_S(A) is an orthogonal projector
theorem _root_.Matrix.IsHermitian.isStarProjection_cfc_indicator {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (S : Set ℝ) :
    IsStarProjection (cfc (S.indicator fun _ => (1 : ℝ)) A)

-- X3, same file: the empirical spectral measure of every set (atomic, no measurability)
theorem _root_.Matrix.IsHermitian.empiricalSpectralMeasure_real {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (S : Set ℝ) :
    (empiricalSpectralMeasure A).real S =
      RCLike.re (cfc (S.indicator fun _ => (1 : ℝ)) A).trace / Fintype.card n

-- G1, Estimation/Trace/GirardHutchinson.lean: linearity in the matrix (needed by D12)
theorem girardHutchinson_smul (c : 𝕜) (B : Matrix n n 𝕜) (Ω : Matrix n m 𝕜) :
    girardHutchinson (c • B) Ω = c * girardHutchinson B Ω

-- X4, Krylov/Functions/Quadrature.lean: past the grade the Lanczos rule is the spectral measure
theorem _root_.Matrix.IsHermitian.lanczosQuadrature_eq_spectralMeasure_of_krylovGrade_le
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {b : n → 𝕜} {q : ℕ} (h : krylovGrade A b ≤ q) :
    lanczosQuadrature A b q = spectralMeasure A b
```

ForMathlib (no NLAlib vocabulary; upstream candidates; Mathlib namespaces):

```lean
-- F1, F2: ForMathlib/Topology/MetricSpace/Lipschitz.lean (joins Mathlib's file of that name)
/-- Abel summation against a Lipschitz function on a finite set of reals: if every point of `s`
lies in `[a, t]`, `t ≤ b`, `f` is `L`-Lipschitz on `[a, b]` and every partial sum
`∑ y ∈ s with y ≤ x, d y` (`x ∈ s`) is at most `K` in absolute value, then
`|∑ f x * d x - f t * ∑ d x| ≤ L (t - a) K`. -/
theorem Finset.abs_sum_mul_sub_mul_sum_le_of_lipschitzOnWith {s : Finset ℝ}
    {a b t : ℝ} (hs : ∀ x ∈ s, x ∈ Set.Icc a t) (hat : a ≤ t) (htb : t ≤ b) {f : ℝ → ℝ}
    {L : ℝ≥0} (hf : LipschitzOnWith L f (Set.Icc a b)) (d : ℝ → ℝ) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x ∈ s, |∑ y ∈ s with y ≤ x, d y| ≤ K) :
    |∑ x ∈ s, f x * d x - f t * ∑ x ∈ s, d x| ≤ L * (t - a) * K

theorem Finset.abs_sum_mul_le_of_lipschitzOnWith {s : Finset ℝ} {a b : ℝ}
    (hs : ∀ x ∈ s, x ∈ Set.Icc a b) (hab : a ≤ b) {f : ℝ → ℝ} {L : ℝ≥0}
    (hf : LipschitzOnWith L f (Set.Icc a b)) (d : ℝ → ℝ) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x ∈ s, |∑ y ∈ s with y ≤ x, d y| ≤ K) :
    |∑ x ∈ s, f x * d x| ≤ (|f b| + L * (b - a)) * K

-- F3, F4, F5: ForMathlib/MeasureTheory/Integral/Bochner/SumMeasure.lean (joins Mathlib's
-- file of that name, beside `setIntegral_finset`)
-- F3 is `Measure.restrict_eq_self_of_ae_mem` followed by Mathlib's `setIntegral_finset`
-- (a three-line ForMathlib lemma; `integral_fintype` is its `univ` case)
theorem MeasureTheory.integral_eq_sum_measureReal_singleton_mul {μ : Measure ℝ}
    [IsFiniteMeasure μ] {s : Finset ℝ} (hμ : ∀ᵐ x ∂μ, x ∈ s) (f : ℝ → ℝ) :
    ∫ x, f x ∂μ = ∑ x ∈ s, μ.real {x} * f x

theorem MeasureTheory.measureReal_Iic_eq_sum {μ : Measure ℝ} [IsFiniteMeasure μ]
    {s : Finset ℝ} (hμ : ∀ᵐ x ∂μ, x ∈ s) (x : ℝ) :
    μ.real (Set.Iic x) = ∑ y ∈ s with y ≤ x, μ.real {y}

/-- **Lipschitz test functions against finitely supported measures.** If the finite measures
`μ`, `ν` on `ℝ` live on a finite set `s ⊆ [a, b]`, their distribution functions differ by at
most `K` at every point of `s`, and `f` is `L`-Lipschitz on `[a, b]`, then
`|∫ f dμ - ∫ f dν| ≤ (|f b| + L (b - a)) K`; for equal masses the `|f b|` term can be removed
by applying the theorem to `f - f b`. -/
theorem MeasureTheory.abs_integral_sub_integral_le_of_lipschitzOnWith {μ ν : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {s : Finset ℝ} (hμ : ∀ᵐ x ∂μ, x ∈ s)
    (hν : ∀ᵐ x ∂ν, x ∈ s) {a b : ℝ} (hs : ∀ x ∈ s, x ∈ Set.Icc a b) (hab : a ≤ b)
    {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzOnWith L f (Set.Icc a b)) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x ∈ s, |μ.real (Set.Iic x) - ν.real (Set.Iic x)| ≤ K) :
    |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤ (|f b| + L * (b - a)) * K
```

F5 is the one-dimensional Kantorovich–Rubinstein inequality (for equal masses,
$\lvert\int f\,d(\mu-\nu)\rvert \le L\int_a^b\lvert F_\mu - F_\nu\rvert$) weakened to the sup
norm, with the mass difference kept as the $\lvert f(b)\rvert$ term, and restricted to finite support, where it is a finite Abel summation and needs no Stieltjes
integral. The finite-support hypothesis is what spectral measures and quadrature rules satisfy;
a general version (continuous measures) is not needed by any consumer and is harder (it needs
`LipschitzOnWith` ⇒ absolutely continuous, `LipschitzOnWith.absolutelyContinuousOnInterval`, and
integration by parts against a Stieltjes function); not proposed.

### 3.2 Trace estimation (phase A): `Estimation/Trace/StochasticLanczosQuadrature.lean`

```lean
/-- **The error of stochastic Lanczos quadrature splits** into the Girard–Hutchinson error and a
quadrature error: for Hermitian $\mathbf{A}$ with spectrum in $[a, a']$, if a real polynomial $p$
of degree less than $2q$ is within $\varepsilon$ of $f$ on $[a, a']$, then for every test matrix
$\mathbf{\Omega}$ with $m$ columns
$$\bigl\lvert\operatorname{tr} f(\mathbf{A}) - \mathsf{slq}(\mathbf{A}, f, \mathbf{\Omega}, q)\bigr\rvert
\le \bigl\lvert\operatorname{tr} f(\mathbf{A}) - \mathsf{girardHutchinson}(f(\mathbf{A}),
\mathbf{\Omega})\bigr\rvert + \frac{2\varepsilon\|\mathbf{\Omega}\|_{\mathsf{F}}^2}{m}\,.$$
Each probe's quadratic form is replaced by its Lanczos quadrature, whose error is at most
$2\varepsilon\|\boldsymbol\omega_j\|^2$
(`Matrix.IsHermitian.norm_star_dotProduct_cfc_mulVec_sub_lanczosFA_le_of_isUniformApproxOn`).
[UbaruChenSaad2017, §4, locator to check]; [MartinssonTropp2020, §6.6]; there with the
quadrature error bounded through analytic $f$ and Chebyshev approximation.
Result: stochastic-lanczos-quadrature-error -/
theorem _root_.Matrix.IsHermitian.norm_trace_cfc_sub_slq_le_of_isUniformApproxOn
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a a' : ℝ} (hs : spectrum ℝ A ⊆ Set.Icc a a')
    {f : ℝ → ℝ} {q : ℕ} {p : ℝ[X]} (hp : p.degree < 2 * q) {ε : ℝ}
    (hε : Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a a') ε) (Ω : Matrix n m 𝕜) :
    ‖(cfc f A).trace - slq A f Ω q‖ ≤
      ‖(cfc f A).trace - girardHutchinson (cfc f A) Ω‖ +
        2 * ε * frobNorm Ω ^ 2 / Fintype.card m

/-- Lipschitz rate (Jackson, degree $2q + 1$): the quadrature term is
<!-- value jacksonApproximationConstant -->$\frac{\pi L(a' - a)}{2q + 3}\cdot
\|\mathbf{\Omega}\|_{\mathsf{F}}^2/m$ for $q + 1$ steps.
Result: stochastic-lanczos-quadrature-error -/
theorem _root_.Matrix.IsHermitian.norm_trace_cfc_sub_slq_le_of_lipschitzOnWith
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a a' : ℝ} (haa : a < a')
    (hs : spectrum ℝ A ⊆ Set.Icc a a') {f : ℝ → ℝ} {L : ℝ≥0}
    (hf : LipschitzOnWith L f (Set.Icc a a')) (Ω : Matrix n m 𝕜) (q : ℕ) :
    ‖(cfc f A).trace - slq A f Ω (q + 1)‖ ≤
      ‖(cfc f A).trace - girardHutchinson (cfc f A) Ω‖ +
        jacksonApproximationConstant * L * (a' - a) / (2 * q + 3) *
          (frobNorm Ω ^ 2 / Fintype.card m)

/-- Analytic rate (Bernstein ellipse $E_\rho$, Chebyshev truncation of degree $2q + 1$): the
quadrature term is $\frac{4M}{\rho^{2q + 1}(\rho - 1)}\cdot\|\mathbf{\Omega}\|_{\mathsf{F}}^2/m$.
[UbaruChenSaad2017, Theorem 4.1, locator to check]: the setting of their analysis.
Result: stochastic-lanczos-quadrature-error -/
theorem _root_.Matrix.IsHermitian.norm_trace_cfc_sub_slq_le_of_differentiableOn
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a a' : ℝ} (haa : a < a')
    (hs : spectrum ℝ A ⊆ Set.Icc a a') {f : ℝ → ℝ} {F : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ)
    (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ))
    (hM : Metric.IsUniformApproxOn F (fun _ => 0) (openBernsteinEllipse ρ) M)
    (hExt : Set.EqOn (fun t : ℝ => ((f (((a' - a) * t + a' + a) / 2) : ℝ) : ℂ))
      (fun t : ℝ => F t) (Set.Icc (-1 : ℝ) 1))
    (Ω : Matrix n m 𝕜) (q : ℕ) :
    ‖(cfc f A).trace - slq A f Ω (q + 1)‖ ≤
      ‖(cfc f A).trace - girardHutchinson (cfc f A) Ω‖ +
        4 * M / (ρ ^ (2 * q + 1) * (ρ - 1)) * (frobNorm Ω ^ 2 / Fintype.card m)
```

```lean
/-- For Hermitian $\mathbf A$ the SLQ estimate is real: each term is a quadratic form of the
Hermitian compression. -/
theorem _root_.Matrix.IsHermitian.im_slq {A : Matrix n n 𝕜} (hA : A.IsHermitian) (f : ℝ → ℝ)
    (Ω : Matrix n m 𝕜) (q : ℕ) : RCLike.im (slq A f Ω q) = 0
```

The trace tails keep the quadrature term **random**, inside the event (Q9(a)). Unlike the density
tails (where the Kolmogorov event already controls the mass, §3.5), making it deterministic here
is not free: it needs a second Girard–Hutchinson event, for $\mathbf B = \mathbf I$, bounding
$\|\mathbf\Omega\|_{\mathsf F}^2 \le nm(1+\tau')$, and a union bound; that corollary
($2\varepsilon n(1+\tau')$, probability added) is Q9(b).

```lean
/-- **The tail of stochastic Lanczos quadrature with sub-Gaussian probes.** Let the entries of the
real $n \times m$ test matrix $\mathbf{\Omega}$ be independent, each satisfying the sub-Gaussian
moment generating function bound with variance proxy $c$ (`HasSubgaussianMGF`) and having second
moment $1$. Let $\mathbf{A}$ be real symmetric with spectrum in $[a, a']$ and let a real
polynomial $p$ of degree less than $2q$ be within $\varepsilon$ of $f$ on $[a, a']$. Then for
every $\tau \ge 0$, <!-- value hansonWrightConstant -->
$$\mathbb{P}\Bigl[\tau + \frac{2\varepsilon\|\mathbf{\Omega}\|_{\mathsf{F}}^2}{m} \le
\bigl\lvert\operatorname{tr} f(\mathbf{A}) - \mathsf{slq}(\mathbf{A}, f, \mathbf{\Omega}, q)\bigr\rvert\Bigr]
\le 2\exp\Bigl(-\frac{1}{196}\min\Bigl(\frac{m\tau^2}{c^2\|f(\mathbf{A})\|_{\mathsf{F}}^2},
\frac{m\tau}{c\|f(\mathbf{A})\|_2}\Bigr)\Bigr)\,;$$
the constant is `hansonWrightConstant`. No definiteness of $f(\mathbf{A})$ is needed. Gaussian
and sign test matrices are the case $c = 1$. From
`Matrix.IsHermitian.norm_trace_cfc_sub_slq_le_of_isUniformApproxOn` and
`NLAlib.measureReal_abs_trace_sub_girardHutchinson_ge_le`.
[UbaruChenSaad2017, Theorem 4.1, locator to check], there for positive definite $\mathbf A$ with
Rademacher probes and relative error; [CortinovisKressner2022, locator to check], the
indefinite case. Result: stochastic-lanczos-quadrature-tail -/
theorem measureReal_abs_trace_cfc_sub_slq_ge_le_of_isUniformApproxOn
    {X : Ω → Matrix n m ℝ} {c : ℝ≥0}
    (hind : iIndepFun (fun p : n × m => fun ω => X ω p.1 p.2) μ)
    (hsub : ∀ i j, HasSubgaussianMGF (fun ω => X ω i j) c μ)
    (hvar : ∀ i j, ∫ ω, X ω i j ^ 2 ∂μ = 1) {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {a a' : ℝ} (hs : spectrum ℝ A ⊆ Set.Icc a a') {f : ℝ → ℝ} {q : ℕ} {p : ℝ[X]}
    (hp : p.degree < 2 * q) {ε : ℝ}
    (hε : Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a a') ε) {τ : ℝ}
    (hτ : 0 ≤ τ) :
    μ.real {ω | τ + 2 * ε * frobNorm (X ω) ^ 2 / Fintype.card m ≤
        |(cfc f A).trace - slq A f (X ω) q|} ≤
      2 * Real.exp (-(hansonWrightConstant *
        min (Fintype.card m * τ ^ 2 / ((c : ℝ) ^ 2 * frobNorm (cfc f A) ^ 2))
          (Fintype.card m * τ / ((c : ℝ) * specNorm (cfc f A)))))

theorem measureReal_abs_trace_cfc_sub_slq_ge_le_of_lipschitzOnWith
    {X : Ω → Matrix n m ℝ} {c : ℝ≥0}
    (hind : iIndepFun (fun p : n × m => fun ω => X ω p.1 p.2) μ)
    (hsub : ∀ i j, HasSubgaussianMGF (fun ω => X ω i j) c μ)
    (hvar : ∀ i j, ∫ ω, X ω i j ^ 2 ∂μ = 1) {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {a a' : ℝ} (haa : a < a') (hs : spectrum ℝ A ⊆ Set.Icc a a') {f : ℝ → ℝ} {L : ℝ≥0}
    (hf : LipschitzOnWith L f (Set.Icc a a')) (q : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) :
    μ.real {ω | τ + jacksonApproximationConstant * L * (a' - a) / (2 * q + 3) *
          (frobNorm (X ω) ^ 2 / Fintype.card m) ≤
        |(cfc f A).trace - slq A f (X ω) (q + 1)|} ≤
      2 * Real.exp (-(hansonWrightConstant *
        min (Fintype.card m * τ ^ 2 / ((c : ℝ) ^ 2 * frobNorm (cfc f A) ^ 2))
          (Fintype.card m * τ / ((c : ℝ) * specNorm (cfc f A)))))

/-- The analytic form: the UCS setting, any symmetric $\mathbf A$, absolute error. -/
theorem measureReal_abs_trace_cfc_sub_slq_ge_le_of_differentiableOn
    {X : Ω → Matrix n m ℝ} {c : ℝ≥0}
    (hind : iIndepFun (fun p : n × m => fun ω => X ω p.1 p.2) μ)
    (hsub : ∀ i j, HasSubgaussianMGF (fun ω => X ω i j) c μ)
    (hvar : ∀ i j, ∫ ω, X ω i j ^ 2 ∂μ = 1) {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {a a' : ℝ} (haa : a < a') (hs : spectrum ℝ A ⊆ Set.Icc a a') {f : ℝ → ℝ} {F : ℂ → ℂ}
    {ρ M : ℝ} (hρ : 1 < ρ) (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ))
    (hM : Metric.IsUniformApproxOn F (fun _ => 0) (openBernsteinEllipse ρ) M)
    (hExt : Set.EqOn (fun t : ℝ => ((f (((a' - a) * t + a' + a) / 2) : ℝ) : ℂ))
      (fun t : ℝ => F t) (Set.Icc (-1 : ℝ) 1)) (q : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) :
    μ.real {ω | τ + 4 * M / (ρ ^ (2 * q + 1) * (ρ - 1)) * (frobNorm (X ω) ^ 2 / Fintype.card m) ≤
        |(cfc f A).trace - slq A f (X ω) (q + 1)|} ≤
      2 * Real.exp (-(hansonWrightConstant *
        min (Fintype.card m * τ ^ 2 / ((c : ℝ) ^ 2 * frobNorm (cfc f A) ^ 2))
          (Fintype.card m * τ / ((c : ℝ) * specNorm (cfc f A)))))
```

Measurability: none is needed. `μ.real` of a set is its outer measure; the event is contained in
the Girard–Hutchinson event and `measureReal_mono` applies to arbitrary sets under a finite
measure. This matters: measurability of $\omega \mapsto \mathsf{slq}$ is not available (§3.7).

Flag for downstream users (brief): the tails are stated with $\varepsilon$ and $p$ given; a user
choosing the degree from a target accuracy wants the `_of_lipschitzOnWith`/`_of_differentiableOn`
forms, which are provided. A sample-size form ($m \ge \dots$, $q \ge \dots$) is not proposed for
the trace estimate: `measureReal_abs_trace_sub_girardHutchinson_ge_le` has none either (Q6).

### 3.3 Density estimates, deterministic (phase B): `Estimation/Spectral/SpectralDensity.lean`

```lean
instance isFiniteMeasure_probeSpectralMeasure (A : Matrix n n 𝕜) (Ω : Matrix n m 𝕜) :
    IsFiniteMeasure (probeSpectralMeasure A Ω)
instance isFiniteMeasure_slqMeasure (A : Matrix n n 𝕜) (Ω : Matrix n m 𝕜) (q : ℕ) :
    IsFiniteMeasure (slqMeasure A Ω q)

/-- The probe spectral measure integrates every $f$ to the Girard–Hutchinson estimate of
$\operatorname{tr} f(\mathbf{A})/\lvert n\rvert$, for every square $\mathbf A$ (both sides vanish
off Hermitian). -/
/-- Every function is integrable against the probe spectral measure (a finite atomic measure). -/
theorem integrable_probeSpectralMeasure (A : Matrix n n 𝕜) (Ω : Matrix n m 𝕜) (f : ℝ → ℝ) :
    Integrable f (probeSpectralMeasure A Ω)

theorem integrable_slqMeasure (A : Matrix n n 𝕜) (Ω : Matrix n m 𝕜) (q : ℕ) (f : ℝ → ℝ) :
    Integrable f (slqMeasure A Ω q)

theorem integral_probeSpectralMeasure (A : Matrix n n 𝕜) (f : ℝ → ℝ) (Ω : Matrix n m 𝕜) :
    ∫ x, f x ∂probeSpectralMeasure A Ω =
      RCLike.re (girardHutchinson (cfc f A) Ω) / Fintype.card n

theorem integral_slqMeasure (A : Matrix n n 𝕜) (f : ℝ → ℝ) (Ω : Matrix n m 𝕜) (q : ℕ) :
    ∫ x, f x ∂slqMeasure A Ω q = RCLike.re (slq A f Ω q) / Fintype.card n

/-- The distribution function of the probe spectral measure is a Girard–Hutchinson estimate:
$\mathsf{probeSpectralMeasure}(\mathbf A,\mathbf\Omega)(S) =
\operatorname{Re}\mathsf{girardHutchinson}(\mathbf 1_S(\mathbf A),\mathbf\Omega)/\lvert n\rvert$
for every $S \subseteq \mathbb R$; $\mathbf 1_S(\mathbf A)$ is an orthogonal projector. -/
theorem probeSpectralMeasure_real (A : Matrix n n 𝕜) (Ω : Matrix n m 𝕜) (S : Set ℝ) :
    (probeSpectralMeasure A Ω).real S =
      RCLike.re (girardHutchinson (cfc (S.indicator fun _ => (1 : ℝ)) A) Ω) /
        Fintype.card n

theorem _root_.Matrix.IsHermitian.probeSpectralMeasure_real_univ {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (Ω : Matrix n m 𝕜) :
    (probeSpectralMeasure A Ω).real Set.univ =
      frobNorm Ω ^ 2 / (Fintype.card n * Fintype.card m)

theorem _root_.Matrix.IsHermitian.slqMeasure_real_univ {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (Ω : Matrix n m 𝕜) {q : ℕ} (hq : 0 < q) :
    (slqMeasure A Ω q).real Set.univ =
      frobNorm Ω ^ 2 / (Fintype.card n * Fintype.card m)

theorem ae_mem_spectrum_probeSpectralMeasure (A : Matrix n n 𝕜) (Ω : Matrix n m 𝕜) :
    ∀ᵐ x ∂probeSpectralMeasure A Ω, x ∈ spectrum ℝ A

theorem ae_mem_Icc_probeSpectralMeasure (A : Matrix n n 𝕜) {a a' : ℝ}
    (hs : spectrum ℝ A ⊆ Set.Icc a a') (Ω : Matrix n m 𝕜) :
    ∀ᵐ x ∂probeSpectralMeasure A Ω, x ∈ Set.Icc a a'

theorem _root_.Matrix.IsHermitian.ae_mem_Icc_slqMeasure {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {a a' : ℝ} (hs : spectrum ℝ A ⊆ Set.Icc a a') (Ω : Matrix n m 𝕜)
    (q : ℕ) : ∀ᵐ x ∂slqMeasure A Ω q, x ∈ Set.Icc a a'

/-- **SLQ matches $2q$ moments of the probe spectral measure**: for Hermitian $\mathbf A$, every
$\mathbf\Omega$ and $q$, the two measures give every real polynomial of degree less than $2q$ the
same integral. [GolubMeurant2010, Theorem 6.6], probe by probe.
Result: lanczos-gauss-quadrature -/
theorem _root_.Matrix.IsHermitian.matchesMoments_probeSpectralMeasure_slqMeasure
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (Ω : Matrix n m 𝕜) (q : ℕ) :
    MatchesMoments (probeSpectralMeasure A Ω) (slqMeasure A Ω q) (2 * q)

/-- With at least $\lvert n\rvert$ steps, SLQ is exact: every probe's Krylov space is invariant. -/
theorem _root_.Matrix.IsHermitian.slqMeasure_eq_probeSpectralMeasure_of_card_le
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (Ω : Matrix n m 𝕜) {q : ℕ}
    (hq : Fintype.card n ≤ q) : slqMeasure A Ω q = probeSpectralMeasure A Ω

/-- **Deterministic: distribution functions control Lipschitz test functions.** For Hermitian
$\mathbf A$ with spectrum in $[a,b]$ and any test matrix: if at every eigenvalue $x$ the
distribution functions of $\nu_{\mathbf A}$ and of the probe spectral measure differ by at most
$\tau$, then every $f$ that is $L$-Lipschitz on $[a,b]$ has
$\lvert\int f\,d\nu_{\mathbf A} - \int f\,d\,\mathsf{probeSpectralMeasure}(\mathbf A,\mathbf\Omega)\rvert
\le (\lvert f(b)\rvert + L(b - a))\tau$. -/
theorem
_root_.Matrix.IsHermitian.abs_integral_empiricalSpectralMeasure_sub_integral_probeSpectralMeasure_le
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a b : ℝ} (hab : a ≤ b)
    (hs : spectrum ℝ A ⊆ Set.Icc a b) {Ω : Matrix n m 𝕜} {τ : ℝ} (hτ : 0 ≤ τ)
    (hK : ∀ x ∈ spectrum ℝ A, |(empiricalSpectralMeasure A).real (Set.Iic x) -
      (probeSpectralMeasure A Ω).real (Set.Iic x)| ≤ τ)
    {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzOnWith L f (Set.Icc a b)) :
    |∫ x, f x ∂empiricalSpectralMeasure A - ∫ x, f x ∂probeSpectralMeasure A Ω| ≤
      (|f b| + L * (b - a)) * τ

/-- D20. **The Kolmogorov event controls the mass**: for Hermitian $\mathbf A$, $n$ nonempty, if
the distribution functions of $\nu_{\mathbf A}$ and of the probe spectral measure differ by at
most $\tau$ at every eigenvalue, then
$\lvert 1 - \|\mathbf\Omega\|_{\mathsf F}^2/(\lvert n\rvert m)\rvert \le \tau$ (take
$x = \lambda_{\max}$: both distribution functions equal the masses there). -/
theorem _root_.Matrix.IsHermitian.abs_one_sub_probeSpectralMeasure_real_univ_le [Nonempty n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {Ω : Matrix n m 𝕜} {τ : ℝ}
    (hK : ∀ x ∈ spectrum ℝ A, |(empiricalSpectralMeasure A).real (Set.Iic x) -
      (probeSpectralMeasure A Ω).real (Set.Iic x)| ≤ τ) :
    |1 - (probeSpectralMeasure A Ω).real Set.univ| ≤ τ

/-- D21. **From the eigenvalues to every threshold**: under the same hypothesis, the distribution
functions differ by at most $\tau$ at every $x \in \mathbb R$ (both are constant between
eigenvalues and $0$ below the smallest). -/
theorem
_root_.Matrix.IsHermitian.abs_empiricalSpectralMeasure_real_Iic_sub_probeSpectralMeasure_real_Iic_le
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {Ω : Matrix n m 𝕜} {τ : ℝ} (hτ : 0 ≤ τ)
    (hK : ∀ x ∈ spectrum ℝ A, |(empiricalSpectralMeasure A).real (Set.Iic x) -
      (probeSpectralMeasure A Ω).real (Set.Iic x)| ≤ τ) (x : ℝ) :
    |(empiricalSpectralMeasure A).real (Set.Iic x) -
      (probeSpectralMeasure A Ω).real (Set.Iic x)| ≤ τ

/-- **Deterministic: the quadrature term, uniformly in Lipschitz test functions.** For Hermitian
$\mathbf A$ with spectrum in $[a,b]$, $a < b$, every $\mathbf\Omega$, $q$, and $f$ that is
$L$-Lipschitz on $[a,b]$, <!-- value jacksonApproximationConstant -->
$$\Bigl\lvert\int f\,d\,\mathsf{probeSpectralMeasure}(\mathbf A,\mathbf\Omega) -
\int f\,d\,\mathsf{slqMeasure}(\mathbf A,\mathbf\Omega,q+1)\Bigr\rvert \le
\frac{\pi L(b-a)}{2q+3}\cdot\frac{\|\mathbf\Omega\|_{\mathsf F}^2}{\lvert n\rvert m}\,;$$
M0 (`MatchesMoments.abs_integral_sub_integral_le_of_isUniformApproxOn`) with Jackson's theorem in
degree $2q + 1$. [ChenTrogdonUbaru2022, Appendix C, Theorem 38], the approximation step. -/
theorem
_root_.Matrix.IsHermitian.abs_integral_probeSpectralMeasure_sub_integral_slqMeasure_le_of_lipschitzOnWith
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a b : ℝ} (hab : a < b)
    (hs : spectrum ℝ A ⊆ Set.Icc a b) (Ω : Matrix n m 𝕜) (q : ℕ) {f : ℝ → ℝ} {L : ℝ≥0}
    (hf : LipschitzOnWith L f (Set.Icc a b)) :
    |∫ x, f x ∂probeSpectralMeasure A Ω - ∫ x, f x ∂slqMeasure A Ω (q + 1)| ≤
      jacksonApproximationConstant * L * (b - a) / (2 * q + 3) *
        (frobNorm Ω ^ 2 / (Fintype.card n * Fintype.card m))
```

### 3.4 Unbiasedness (phase B)

```lean
/-- **The probe spectral measure is unbiased**: if every probe is isotropic, then for Hermitian
$\mathbf A$ and every $f$,
$\mathbb E\int f\,d\,\mathsf{probeSpectralMeasure}(\mathbf A,\mathbf\Omega) = \int f\,d\nu_{\mathbf A}$,
$\nu_{\mathbf A}$ the empirical spectral measure. No independence is needed: Gaussian, sign,
and $\sqrt{\lvert n\rvert}$ times uniform-sphere or Haar-frame probes are instances. With
$f = \mathbf 1_S$, the expected measure of every Borel set is $\nu_{\mathbf A}(S)$.
[ChenTrogdonUbaru2022, locator to check]. Result: probe-spectral-measure-unbiased -/
theorem integral_integral_probeSpectralMeasure [Nonempty m] {X : Ω → Matrix n m 𝕜}
    (hX : ∀ j, IsIsotropic (fun ω i => X ω i j) μ) {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (f : ℝ → ℝ) :
    ∫ ω, (∫ x, f x ∂probeSpectralMeasure A (X ω)) ∂μ = ∫ x, f x ∂empiricalSpectralMeasure A
```

`[Nonempty m]` is needed (empty `m`: left side $0$). No `IsProbabilityMeasure`: isotropy fixes the
integrals (as `integral_girardHutchinson`). The measure-valued form
($\mathbb E\,\mathsf{probeSpectralMeasure} = \nu_{\mathbf A}$ as a `Measure.bind`) is not
proposed: no consumer, and the test-function form implies it for every set.

### 3.5 Tails for the density (phase B)

```lean
/-- **The distribution function of the probe spectral measure, at one set.** With the
sub-Gaussian test matrix of `measureReal_abs_trace_sub_girardHutchinson_ge_le` (independent
entries, proxy $c$, second moment $1$), real symmetric $\mathbf A$, every $S \subseteq \mathbb R$
and $\tau \ge 0$, <!-- value hansonWrightConstant -->
$$\mathbb P\bigl[\tau \le \lvert\nu_{\mathbf A}(S) - \mathsf{probeSpectralMeasure}(\mathbf A,
\mathbf\Omega)(S)\rvert\bigr] \le 2\exp\Bigl(-\frac{1}{196}\,m\lvert n\rvert
\min\Bigl(\frac{\tau^2}{c^2}, \frac{\tau}{c}\Bigr)\Bigr)\,:$$
the error is that of Girard–Hutchinson on $\mathbf 1_S(\mathbf A)/\lvert n\rvert$, a projector
divided by $\lvert n\rvert$, of Frobenius norm at most $\lvert n\rvert^{-1/2}$ and spectral norm
at most $\lvert n\rvert^{-1}$. The factor $\lvert n\rvert$ in the exponent is the
"dimension helps" effect. -/
theorem measureReal_abs_empiricalSpectralMeasure_real_sub_probeSpectralMeasure_real_ge_le
    {X : Ω → Matrix n m ℝ} {c : ℝ≥0}
    (hind : iIndepFun (fun p : n × m => fun ω => X ω p.1 p.2) μ)
    (hsub : ∀ i j, HasSubgaussianMGF (fun ω => X ω i j) c μ)
    (hvar : ∀ i j, ∫ ω, X ω i j ^ 2 ∂μ = 1) {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (S : Set ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    μ.real {ω | τ ≤ |(empiricalSpectralMeasure A).real S -
        (probeSpectralMeasure A (X ω)).real S|} ≤
      2 * Real.exp (-(hansonWrightConstant * (Fintype.card m * Fintype.card n *
        min (τ ^ 2 / (c : ℝ) ^ 2) (τ / c))))

/-- **Kolmogorov-distance tail**: the same hypotheses; the distribution functions differ by more
than $\tau$ at some eigenvalue with probability at most
<!-- value hansonWrightConstant -->$2\lvert n\rvert\exp\bigl(-\tfrac{1}{196}m\lvert n\rvert
\min(\tau^2/c^2, \tau/c)\bigr)$ (union bound over the at most $\lvert n\rvert$ eigenvalues; both
distribution functions are constant between eigenvalues; D21 extends the bound to every
threshold). [ChenTrogdonUbaru2021, locator to check]; there for sphere probes.
Result: spectral-density-kolmogorov-tail -/
theorem measureReal_exists_abs_empiricalSpectralMeasure_real_sub_probeSpectralMeasure_real_gt_le
    {X : Ω → Matrix n m ℝ} {c : ℝ≥0}
    (hind : iIndepFun (fun p : n × m => fun ω => X ω p.1 p.2) μ)
    (hsub : ∀ i j, HasSubgaussianMGF (fun ω => X ω i j) c μ)
    (hvar : ∀ i j, ∫ ω, X ω i j ^ 2 ∂μ = 1) {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    μ.real {ω | ∃ x ∈ spectrum ℝ A, τ < |(empiricalSpectralMeasure A).real (Set.Iic x) -
        (probeSpectralMeasure A (X ω)).real (Set.Iic x)|} ≤
      2 * Fintype.card n * Real.exp (-(hansonWrightConstant * (Fintype.card m *
        Fintype.card n * min (τ ^ 2 / (c : ℝ) ^ 2) (τ / c))))

/-- The probe-measure (exact quadrature) uniform bound: outside probability
$2\lvert n\rvert\exp(\dots)$ as above, every $L$-Lipschitz $f$ on $[a, b]$ has
$\lvert\int f\,d\nu_{\mathbf A} - \int f\,d\,\mathsf{probeSpectralMeasure}\rvert \le
(\lvert f(b)\rvert + L(b-a))\tau$. [ChenTrogdonUbaru2021, locator to check].
Result: spectral-density-lipschitz-tail -/
theorem
measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_probeSpectralMeasure_gt_le
    {X : Ω → Matrix n m ℝ} {c : ℝ≥0}
    (hind : iIndepFun (fun p : n × m => fun ω => X ω p.1 p.2) μ)
    (hsub : ∀ i j, HasSubgaussianMGF (fun ω => X ω i j) c μ)
    (hvar : ∀ i j, ∫ ω, X ω i j ^ 2 ∂μ = 1) {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {a b : ℝ} (hab : a ≤ b) (hs : spectrum ℝ A ⊆ Set.Icc a b) (L : ℝ≥0) {τ : ℝ} (hτ : 0 ≤ τ) :
    μ.real {ω | ∃ f : ℝ → ℝ, LipschitzOnWith L f (Set.Icc a b) ∧
        (|f b| + L * (b - a)) * τ <
        |∫ x, f x ∂empiricalSpectralMeasure A - ∫ x, f x ∂probeSpectralMeasure A (X ω)|} ≤
      2 * Fintype.card n * Real.exp (-(hansonWrightConstant * (Fintype.card m *
        Fintype.card n * min (τ ^ 2 / (c : ℝ) ^ 2) (τ / c))))

/-- **Stochastic Lanczos quadrature approximates the spectral density, uniformly in Lipschitz
test functions.** Let the entries of the real $n \times m$ test matrix $\mathbf{\Omega}$ be
independent, each satisfying the sub-Gaussian moment generating function bound with variance
proxy $c$ and having second moment $1$; let $\mathbf A$ be real symmetric with spectrum in
$[a, b]$, $a < b$; let $L \ge 0$, $q \in \mathbb N$ and $\tau \ge 0$. Then, except with
probability at most <!-- value hansonWrightConstant -->
$$2\lvert n\rvert\exp\Bigl(-\frac{1}{196}\,m\lvert n\rvert\min\Bigl(\frac{\tau^2}{c^2},
\frac{\tau}{c}\Bigr)\Bigr)\,,$$
every $f$ that is $L$-Lipschitz on $[a, b]$ satisfies <!-- value jacksonApproximationConstant -->
$$\Bigl\lvert\int f\,d\nu_{\mathbf A} - \int f\,d\,\mathsf{slqMeasure}(\mathbf A,\mathbf\Omega,
q+1)\Bigr\rvert \le (\lvert f(b)\rvert + L(b-a))\tau + \frac{\pi L(b-a)}{2q+3}(1+\tau)\,,$$
$\nu_{\mathbf A}$ the empirical spectral measure; the constants are `hansonWrightConstant` and
`jacksonApproximationConstant`. For test functions with $f(b) = 0$ and equal masses this is a
Wasserstein-1 bound. The factor $1+\tau$ bounds the random mass
$\|\mathbf\Omega\|_{\mathsf F}^2/(\lvert n\rvert m)$ on the same event (D20). Gaussian and
sign test matrices are the case $c = 1$.
[ChenTrogdonUbaru2021, the Wasserstein bound for SLQ, theorem number to check]; there for probes
uniform on the sphere, with the sharper sub-Gaussian constant of Beta laws and the bound in $d_W$;
the Jackson step is [ChenTrogdonUbaru2022, Appendix C, Theorem 38]. Asymptotic form:
`exists_forall_…` below.
Result: spectral-density-lipschitz-tail -/
theorem measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_slqMeasure_gt_le
    {X : Ω → Matrix n m ℝ} {c : ℝ≥0}
    (hind : iIndepFun (fun p : n × m => fun ω => X ω p.1 p.2) μ)
    (hsub : ∀ i j, HasSubgaussianMGF (fun ω => X ω i j) c μ)
    (hvar : ∀ i j, ∫ ω, X ω i j ^ 2 ∂μ = 1) {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {a b : ℝ} (hab : a < b) (hs : spectrum ℝ A ⊆ Set.Icc a b) (L : ℝ≥0) (q : ℕ) {τ : ℝ}
    (hτ : 0 ≤ τ) :
    μ.real {ω | ∃ f : ℝ → ℝ, LipschitzOnWith L f (Set.Icc a b) ∧
        (|f b| + L * (b - a)) * τ +
          jacksonApproximationConstant * L * (b - a) / (2 * q + 3) * (1 + τ) <
        |∫ x, f x ∂empiricalSpectralMeasure A - ∫ x, f x ∂slqMeasure A (X ω) (q + 1)|} ≤
      2 * Fintype.card n * Real.exp (-(hansonWrightConstant * (Fintype.card m *
        Fintype.card n * min (τ ^ 2 / (c : ℝ) ^ 2) (τ / c))))
```

The **normalised (ratio) estimator** (review comment 11; the form CTU print and sphere-probe
users compare against). Dividing by the mass makes both measures probability measures:

```lean
/-- D19. Under the hypotheses of D17 and $\tau < 1$, outside the same event, the SLQ measure
divided by its mass satisfies, for every $L$-Lipschitz $f$ on $[a,b]$,
<!-- value jacksonApproximationConstant -->
$$\Bigl\lvert\int f\,d\nu_{\mathbf A} - \int f\,d\,\frac{\mathsf{slqMeasure}(\mathbf A,
\mathbf\Omega,q+1)}{\mathsf{slqMeasure}(\mathbf A,\mathbf\Omega,q+1)(\mathbb R)}\Bigr\rvert
\le 2L(b-a)\tau + \frac{\pi L(b-a)}{2q+3}\,.$$
[ChenTrogdonUbaru2021, locator to check]. Result: spectral-density-lipschitz-tail -/
theorem
measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_smul_slqMeasure_gt_le
    {X : Ω → Matrix n m ℝ} {c : ℝ≥0}
    (hind : iIndepFun (fun p : n × m => fun ω => X ω p.1 p.2) μ)
    (hsub : ∀ i j, HasSubgaussianMGF (fun ω => X ω i j) c μ)
    (hvar : ∀ i j, ∫ ω, X ω i j ^ 2 ∂μ = 1) {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {a b : ℝ} (hab : a < b) (hs : spectrum ℝ A ⊆ Set.Icc a b) (L : ℝ≥0) (q : ℕ) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτ1 : τ < 1) :
    μ.real {ω | ∃ f : ℝ → ℝ, LipschitzOnWith L f (Set.Icc a b) ∧
        L * (b - a) * (2 * τ) + jacksonApproximationConstant * L * (b - a) / (2 * q + 3) <
        |∫ x, f x ∂empiricalSpectralMeasure A -
          ∫ x, f x ∂((slqMeasure A (X ω) (q + 1) Set.univ)⁻¹ • slqMeasure A (X ω) (q + 1))|} ≤
      2 * Fintype.card n * Real.exp (-(hansonWrightConstant * (Fintype.card m *
        Fintype.card n * min (τ ^ 2 / (c : ℝ) ^ 2) (τ / c))))
```

Proof of the constant: on the good event the mass $M$ satisfies $\lvert 1 - M\rvert \le \tau$
(D20), so $M > 0$; at each eigenvalue
$\lvert F_\nu - F_{\mathsf{probe}}/M\rvert \le \lvert F_\nu - F_{\mathsf{probe}}\rvert +
(F_{\mathsf{probe}}/M)\lvert M - 1\rvert \le 2\tau$ (the review's $2\tau/(1-\tau)$ is not
needed); both measures then have mass $1$, so F5 applied to $f - f(b)$ removes the
$\lvert f(b)\rvert$ term; and the normalised SLQ and probe measures both have mass $1$ and still
match $2(q+1)$ moments, so M0 gives $2\cdot\pi L(b-a)/(2(2q+3))$. The ENNReal normalisation is
inline (junk: $\top \cdot 0 = 0$ for empty $n$, where the event is empty); a named normalised
measure is not proposed (Q4). $\tau < 1$ is used only for $M > 0$.

Why the $\lvert f(b)\rvert$ term: with Gaussian or sign probes neither measure is a probability
measure (masses $\|\mathbf\Omega\|_{\mathsf F}^2/(nm)$ and $1$), so no bound uniform over all
$L$-Lipschitz $f$ exists (add a constant to $f$). The term costs nothing when $f(b) = 0$, and the
Abel summation (F2) makes it exact: it is the mass discrepancy, which the Kolmogorov event already
controls at $x = \lambda_{\max}$. Alternatives in Q4.

Check of the composition (for the reviewer): on the complement of the Kolmogorov event, D14 with
$K = \tau$ gives the first term; D15 the second, with its random mass bounded by $1+\tau$ through
D20 (for empty $n$ both integrals are $0$ and the event is empty); the masses in D15 come from
D4, D5 (both $\|\mathbf\Omega\|_{\mathsf F}^2/(nm)$; the Jackson polynomial has degree $2q+1 < 2(q+1)$ and
error $\pi L(b-a)/(2(2q+3))$, and M0 multiplies it by the sum of the masses). The event of D17 is
contained in the Kolmogorov event, whose bound is D12 summed over
$\lvert\operatorname{spec}\mathbf A\rvert \le \lvert n\rvert$ points
(`measureReal_biUnion_finset_le`). In D12, $\mathbf B = \mathbf 1_S(\mathbf A)/n$ has
$\|\mathbf B\|_{\mathsf F}^2 = \operatorname{rank}/n^2 \le 1/n$ and $\|\mathbf B\|_2 \le 1/n$, so
$\min(m\tau^2/(c^2\|\mathbf B\|_{\mathsf F}^2), m\tau/(c\|\mathbf B\|_2)) \ge
mn\min(\tau^2/c^2,\tau/c)$; the junk cases $\mathbf B = 0$ (event empty for $\tau > 0$) and $c = 0$
(the right side is $2$) are split off.

### 3.6 Asymptotic form (B5)

```lean
set_option linter.style.longLine false in -- one identifier
/-- "$O(c^2\log(\lvert n\rvert/\delta)/(\lvert n\rvert\tau^2))$ probes suffice" … (docstring
states hypotheses and conclusion in words, as §6 requires).
Asymptotic: NLAlib.measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_slqMeasure_gt_le
Result: spectral-density-lipschitz-tail -/
theorem exists_forall_measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_slqMeasure_gt_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω n m : Type} [MeasurableSpace Ω] [Fintype n] [DecidableEq n]
      [Fintype m] (μ : Measure Ω) (X : Ω → Matrix n m ℝ) (c : ℝ≥0)
      (A : Matrix n n ℝ) (a b : ℝ) (L : ℝ≥0) (q : ℕ) (τ δ : ℝ),
      iIndepFun (fun p : n × m => fun ω => X ω p.1 p.2) μ →
      (∀ i j, HasSubgaussianMGF (fun ω => X ω i j) c μ) →
      (∀ i j, ∫ ω, X ω i j ^ 2 ∂μ = 1) → A.IsHermitian → a < b →
      spectrum ℝ A ⊆ Set.Icc a b → 0 < τ → τ ≤ 1 → 0 < δ → δ ≤ 1 →
      C * (c : ℝ) ^ 2 * Real.log (2 * Fintype.card n / δ) / (Fintype.card n * τ ^ 2) ≤
        Fintype.card m →
      μ.real {ω | ∃ f : ℝ → ℝ, LipschitzOnWith L f (Set.Icc a b) ∧
        (|f b| + L * (b - a)) * τ +
          jacksonApproximationConstant * L * (b - a) / (2 * q + 3) * (1 + τ) <
        |∫ x, f x ∂empiricalSpectralMeasure A - ∫ x, f x ∂slqMeasure A (X ω) (q + 1)|} ≤ δ
```

Proof: $C = 196$. For $n$, $m$ nonempty, $c \ge 1$ by `HasSubgaussianMGF.integral_sq_le` and
`hvar` (`hind.isProbabilityMeasure`), so with $\tau \le 1$ the minimum is $\tau^2/c^2$ and the
size hypothesis gives exponent $\ge \log(2n/\delta)$. Empty $n$: the bound is $0$. Empty $m$ with
nonempty $n$: the size hypothesis is false ($\log(2n/\delta) \ge \log 2 > 0$). The cap $\tau \le 1$
is what makes the minimum quadratic; it is in the statement. With the quadrature term now
deterministic (review comment 1) the conclusion holds for every outcome outside an event of
probability at most $\delta$, with no random quantity in the bound: the reading §5.2 rule 3 intends.
Docstring cites [ChenTrogdonUbaru2021]. "$\lvert n\rvert$ in the denominator"
is the headline: for large $n$ a single probe suffices.

### 3.7 Phase C (optional): bias in expectation

```lean
-- Probability/Measurability/Krylov.lean
theorem _root_.Matrix.IsHermitian.measurable_lanczosFA {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {a a' : ℝ} (hs : spectrum ℝ A ⊆ Set.Icc a a') {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a a')) (q : ℕ) : Measurable fun b => lanczosFA A f b q

-- Estimation/Trace/StochasticLanczosQuadrature.lean
/-- **The bias of stochastic Lanczos quadrature**: isotropic probes, $f$ continuous and within
$\varepsilon$ of a polynomial of degree less than $2q$ on $[a, a'] \supseteq \operatorname{spec}
\mathbf A$: $\lvert\operatorname{tr}f(\mathbf A) - \mathbb E\,\mathsf{slq}\rvert \le
2\varepsilon\lvert n\rvert$. Result: stochastic-lanczos-quadrature-error -/
theorem _root_.Matrix.IsHermitian.norm_trace_cfc_sub_integral_slq_le_of_isUniformApproxOn
    [Nonempty m] {X : Ω → Matrix n m 𝕜}
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (hX : ∀ j, IsIsotropic (fun ω i => X ω i j) μ)
    {a a' : ℝ} (hs : spectrum ℝ A ⊆ Set.Icc a a') {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a a')) {q : ℕ} {p : ℝ[X]} (hp : p.degree < 2 * q) {ε : ℝ}
    (hε : Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a a') ε) :
    ‖(cfc f A).trace - ∫ ω, slq A f (X ω) q ∂μ‖ ≤ 2 * ε * Fintype.card n
```

`hf` is there only for measurability (the docstring will say so). Without measurability the
Bochner integral of a non-integrable function is $0$ and the statement would be false, so it
cannot be dropped. The measurability proof: replace $f$ by the continuous
$f \circ \mathrm{projIcc}_{[a,a']}$ (`Matrix.IsHermitian.lanczosFA_congr`), write
$\mathsf{lanczosFA} = \mathbf P\,g(\mathbf P\mathbf A\mathbf P)\,\mathbf P\mathbf b$ with
$\mathbf P$ measurable in $\mathbf b$ (`measurable_rangeProjector`, `measurable_krylovMatrix`)
and $g \mapsto$ `cfc g` continuous on self-adjoint matrices with spectrum in a compact set
(Mathlib `continuousOn_cfc`). The risk is the C*-algebra instance on matrices (scoped
`Matrix.Norms.L2Operator`; Mathlib-deviations entry 13), hence L (80+ lines, split). Then: integrability of
$\mathsf{girardHutchinson} - \mathsf{slq}$ from measurability and the bound of T2, and
$\mathbb E\|\mathbf\Omega\|_{\mathsf F}^2 = nm$ (`IsIsotropic.integral_norm_sq`). Recommend
phase C as its own PR after A and B (Q6).

## 4. Consumers

| Item | Consumers, and the form they use |
|---|---|
| `slq`, T2–T4 | Users of trace estimation of matrix functions (log-determinants, Estrada index, nuclear-norm and spectral-sum estimation): the split, then any Girard–Hutchinson result (variance, tail) for `cfc f A`. Krylov-aware trace estimation (block round, `Krylov-Spectral.md` §5 row C6): Hutch++ with Lanczos replaces the residual term the same way. The explorer's Rates page (degree budgets). |
| T5–T7 | Same; the analytic form is the UCS17 theorem in absolute error; downstream sample-size forms |
| `probeSpectralMeasure`, D1–D3, D11 | The density tails here; KPM (later: its Chebyshev moments are `girardHutchinson` of $T_k(\mathbf A)$, so KPM's moment estimator is `integral_probeSpectralMeasure` with $f = T_k$); M1 (noisy moments) |
| `slqMeasure`, D2, D9, D10, D15 | The SLQ density tail; any future quadrature-type density bound (Gauss–Radau, analytic test functions); KPM vs SLQ comparison (CTU 2025) |
| F1–F5 | D14 here; M1's "universal Lipschitz test bounds" for discrete measures (`Polynomial-Jackson-Moments.md` §4); any Krylov-Sharpness statement about spectral distributions |
| X2 | D12; any spectral-projector argument (eigenvalue counts, `spectralTangentSq` style) |
| X4 | D10; Lanczos-FA/quadrature exactness users past the grade |
| D12, D13 | Spectrum-counting / eigenvalue-histogram estimation (the CDF itself is the number of eigenvalues below $x$ over $n$); stopping rules |
| D16–D19 | Spectral density estimation (D19 is the form CTU print and sphere-probe users compare against); the explorer's Rates page; KPM comparison later |
| Phase C | Mean-square error of SLQ (later), users who average SLQ |

No statement without a consumer except D16 (the $q = \infty$ case), kept because it is CTU's
first theorem and the deterministic-plus-random split users need for other quadratures.

## 5. Files and placement

| File | New / addition | Content (declarations in order) | Lines |
|---|---|---|---|
| `NLAlib/ForMathlib/Topology/MetricSpace/Lipschitz.lean` | new | F1, F2 | 110 |
| `NLAlib/ForMathlib/MeasureTheory/Integral/Bochner/SumMeasure.lean` | new | F3, F4, F5 | 120 |
| `NLAlib/Matrix/Spectral/SpectralMeasure.lean` | addition | X1 (private → public), X2, X3 | +45 |
| `NLAlib/Krylov/Functions/Quadrature.lean` | addition | X4 | +25 |
| `NLAlib/Estimation/Trace/GirardHutchinson.lean` | addition | G1 `girardHutchinson_smul` | +10 |
| `NLAlib/Estimation/Trace/StochasticLanczosQuadrature.lean` | new | `slq`, T2, T3, T4, T8, T5, T6, T7 (phase C: C2) | 320 (+70) |
| `NLAlib/Estimation/Spectral/SpectralDensity.lean` | new | `probeSpectralMeasure`, `slqMeasure`, I1–I4, D1–D11, D14, D20, D21, D15, D12, D13, D16, D17, D19, D18 | 760 |
| `NLAlib/Probability/Measurability/Krylov.lean` | addition, phase C | C1 `Matrix.IsHermitian.measurable_lanczosFA` | +70 |

Placement of each addition outside the new Estimation files:

| Addition | Home | Reason |
|---|---|---|
| F1, F2 (Abel summation against a Lipschitz function) | `ForMathlib/Topology/MetricSpace/Lipschitz.lean` | scalar real-analysis fact, no NLAlib vocabulary (P9); Mathlib's `LipschitzOnWith` file |
| F3–F5 (finite-support integrals; the CDF bound) | `ForMathlib/MeasureTheory/Integral/Bochner/SumMeasure.lean` | measure theory with no NLAlib vocabulary (P4, P8); beside Mathlib's `setIntegral_finset`. Alternative home `Polynomial/Orthogonal/Moments.lean` next to M0, Q10 |
| X1, X2, X3 | `Matrix/Spectral/SpectralMeasure.lean` | about the spectral measure, the spectral projector $\mathbf 1_S(\mathbf A)$ (whose quadratic form *is* the measure) and the empirical measure |
| X4 | `Krylov/Functions/Quadrature.lean` | a fact about `lanczosQuadrature`; uses that file's private `quadForm_cfc_rangeProjector` |
| G1 | `Estimation/Trace/GirardHutchinson.lean` | linearity of the estimator it is about |
| C1 | `Probability/Measurability/Krylov.lean` | beside `measurable_krylovMatrix` (D12 of PORT_KRYLOV) |

Density file in `Estimation/Spectral/` (beside `RandomStart.lean`: spectral quantities estimated
from random probes), trace file in `Estimation/Trace/` (beside `GirardHutchinson.lean`,
`HutchPlusPlus.lean`). The density file imports the trace file (D2 uses `slq`). Imports are
layer-correct (Estimation 4 → Krylov 1, Probability 1, Polynomial 0, ForMathlib −1). No
placement flags.

Lines over 100 characters: the names of D14, D15, D16 and D18 do not fit a line of their own;
each takes `set_option linter.style.longLine false in` with the comment "one identifier", as
CONTRIBUTING §3 (S8) allows. Shorter names would need a shorter spelling of
`probeSpectralMeasure` or `empiricalSpectralMeasure` (Q2).

## 6. Mathlib search (pinned Mathlib in `/home/ubuntu/nlalib/.lake/packages/mathlib`)

| Looked for | Found | Use |
|---|---|---|
| Wasserstein / Kantorovich–Rubinstein distance | none; `MeasureTheory/Measure/LevyProkhorovMetric.lean` only | no distance defined (Q4) |
| distribution function | `ProbabilityTheory.cdf` (probability measures, `StieltjesFunction`) | not used: random masses; `μ.real (Set.Iic x)` |
| Abel summation | `Finset.sum_range_by_parts`, `Finset.sum_Ioc_by_parts` (`Algebra/BigOperators/Module.lean`), over `ℕ` ranges | F1 is on a `Finset ℝ`, by `Finset.induction_on_max`; searched "Lipschitz" with "by_parts": none |
| integral against a measure on a finite set | `setIntegral_finset` (`Integral/Bochner/SumMeasure.lean`), `Measure.restrict_eq_self_of_ae_mem`, `integrableOn_singleton`, `integrableOn_finset_iUnion`; `integral_fintype` is the `univ` case | F3 is these two composed (near-overlap, kept as a ForMathlib three-liner); searched for a direct ae-on-finset form: none |
| finite measures determined by their distribution functions | `MeasureTheory.ext_of_Iic` (`Constructions/BorelSpace/Order.lean`) | not used here; listed for density users, next to F4 |
| union bound | `measureReal_biUnion_finset_le` | D13 |
| projector from `cfc` of an indicator | `isStarProjection_iff` (idempotent ∧ self-adjoint) with `cfc_mul`; or `isStarProjection_iff_spectrum_subset_and_isSelfAdjoint` (`CStarAlgebra/Projection.lean`), `isIdempotentElem_iff_spectrum_subset` (`ContinuousFunctionalCalculus/Projection.lean`) with `cfc_map_spectrum` ($\operatorname{spec} = \mathbf 1_S(\operatorname{spec}\mathbf A) \subseteq \{0,1\}$) and `cfc_predicate`; NLAlib none | X2 (either route, S) |
| norms of a projector | NLAlib `IsStarProjection.frobNorm_sq_eq_rank`, `IsStarProjection.specNorm_le_one`; Mathlib `Matrix.rank_le_card_width` | D12 |
| spectrum and eigenvalues | Mathlib `Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues` | card of the spectrum $\le n$ (private helper of D13) |
| continuity of `cfc` in the element | `continuousOn_cfc`, `Continuous.cfc'` (`ContinuousFunctionalCalculus/Continuity.lean`) | C1 |
| trace estimation, SLQ, spectral density | none | — |
| second moment of a sub-Gaussian variable | NLAlib `ProbabilityTheory.HasSubgaussianMGF.integral_sq_le` | D18 ($c \ge 1$) |

No exact overlap: nothing ships as an alias (F3 is a composition of two Mathlib lemmas, noted above).

## 7. Material

* **The prototype library and the local PDFs named in the briefs are not on this machine.**
  Nothing was read from the prototype; there is no port and no ledger entry. The prototype's SLQ
  material, if any, is unexamined (§11).
* Read: CONTRIBUTING (whole), AGENTS, `docs/rules/DIGEST.md`, `NLAlib/{Estimation,Krylov,Probability}/RULES.md`,
  `docs/PORT_KRYLOV.md` §§8–10, `docs/design/{Krylov-Spectral,Krylov-Functions,Estimation-HutchPP,
  Polynomial-Jackson-Moments,Krylov-Block}.md`, and the code of `Estimation/Trace/*`,
  `Estimation/Spectral/RandomStart.lean`, `Krylov/Functions/{Quadrature,LanczosFA}.lean`,
  `Matrix/Spectral/SpectralMeasure.lean`, `Polynomial/Orthogonal/*`,
  `Polynomial/Approximation/Jackson.lean`, `Probability/Isotropic.lean`,
  `Probability/QuadraticForm/HansonWright.lean`, `RandomMatrix/Haar/{Basic,Sphere,Moments}.lean`.
* Literature, from memory (no PDF here; every locator marked "to check" must be checked against
  the source before the docstrings are committed):
  * Ubaru, Chen, Saad 2017, SIMAX 38(4), 1075–1099 (DOI 10.1137/16M1104974, to check). SLQ for
    $\operatorname{tr} f(\mathbf A)$; main theorem (Theorem 4.1, to check) for SPD $\mathbf A$,
    analytic $f$, Rademacher probes, relative error, sample size
    $m \gtrsim \varepsilon^{-2}\log(2/\eta)$ via Roosta-Khorasani–Ascher. Our T5–T7 are absolute,
    for any symmetric $\mathbf A$, through Hanson–Wright, so they do not depend on definiteness.
  * Cortinovis, Kressner 2022, Found. Comput. Math. 22, 875–903 (DOI 10.1007/s10208-021-09525-9,
    to check). Tail bounds for Girard–Hutchinson on indefinite matrices with explicit constants
    (better than Hanson–Wright's $1/196$), applied to SLQ for log-determinants; they note the
    gap in the indefinite case of earlier SLQ analyses (to check).
  * Chen, Trogdon, Ubaru, "Analysis of stochastic Lanczos quadrature for spectrum
    approximation", ICML 2021, PMLR 139 (new key `ChenTrogdonUbaru2021`; review comment 2). **The
    primary source of the uniform bound**: the Wasserstein bound for SLQ with sphere probes,
    through the CDFs of spectral projectors and a union bound over eigenvalues (the route of
    D12–D19), and the "dimension helps" rate $m \sim \log(n/\delta)/(n\tau^2)$ (theorem numbers
    to check).
  * Chen, Trogdon, Ubaru 2022, arXiv:2204.01941v1 (key `ChenTrogdonUbaru2022`, already cited by
    the Jackson files for Appendix C, Theorem 38): the SLQ–KPM unification; here only the Jackson
    step (D15, T3).
  * The SIAM J. Sci. Comput. version, 2025, DOI 10.1137/23M1600414 ("Randomized matrix-free
    quadrature: unified and uniform bounds for stochastic Lanczos quadrature and the kernel
    polynomial method"). Not cited until PORT_KRYLOV question 3 is answered; Q7 proposes the key.
  * Martinsson, Tropp 2020, §6.6 and Algorithm 6 (verified against a local PDF in an earlier
    round, `docs/PORT_KRYLOV.md` §9).
  * Golub, Meurant 2010 (already cited for the quadrature): Ch. 6–7; their chapter on trace
    estimation, locator to check.
* Proposed `docs/references.bib` entries (not added; each in the commit that first cites it;
  fields to check against the publisher):

```bibtex
@article{UbaruChenSaad2017,
  author  = {Ubaru, Shashanka and Chen, Jie and Saad, Yousef},
  title   = {Fast Estimation of $tr(f(A))$ via Stochastic {L}anczos Quadrature},
  journal = {SIAM Journal on Matrix Analysis and Applications},
  volume  = {38}, number = {4}, pages = {1075--1099}, year = {2017},
  doi     = {10.1137/16M1104974}
}
@article{CortinovisKressner2022,
  author  = {Cortinovis, Alice and Kressner, Daniel},
  title   = {On Randomized Trace Estimates for Indefinite Matrices with an Application to
             Determinants},
  journal = {Foundations of Computational Mathematics},
  volume  = {22}, pages = {875--903}, year = {2022},
  doi     = {10.1007/s10208-021-09525-9}
}
@inproceedings{ChenTrogdonUbaru2021,
  author    = {Chen, Tyler and Trogdon, Thomas and Ubaru, Shashanka},
  title     = {Analysis of Stochastic {L}anczos Quadrature for Spectrum Approximation},
  booktitle = {Proceedings of the 38th International Conference on Machine Learning},
  series    = {Proceedings of Machine Learning Research},
  volume    = {139}, pages = {to check}, year = {2021}
  % all fields to check; the maintainer is a co-author
}
@article{ChenTrogdonUbaru2025,
  author  = {Chen, Tyler and Trogdon, Thomas and Ubaru, Shashanka},
  title   = {Randomized Matrix-Free Quadrature: Unified and Uniform Bounds for Stochastic
             {L}anczos Quadrature and the Kernel Polynomial Method},
  journal = {SIAM Journal on Scientific Computing},
  year    = {2025}, doi = {10.1137/23M1600414}
  % volume, number, pages: copy from the article
}
```

## 8. Deviations

No numbered deviation. `slq`, `probeSpectralMeasure`, `slqMeasure` are additions where Mathlib
has nothing. Text for the "Additions" section of `docs/design/Mathlib-deviations.md`, to go in the
commit that defines them (not now: V6 checks that every Lean name cited there exists):

> SLQ (`docs/design/Estimation-SLQ.md`): `slq`, `probeSpectralMeasure` and `slqMeasure`, the
> stochastic Lanczos quadrature estimate and the two spectral-density estimates, are additions.
> Their distribution functions are written `μ.real (Set.Iic x)`; Mathlib's `ProbabilityTheory.cdf`
> is defined for probability measures only and the estimates have random mass. No numbered
> deviation is introduced.

## 9. Proof plan for dispatch

Every statement is fixed by the skeleton (§3, `sorry` bodies), so **every row can be proved in
parallel**: a proof that uses a sibling only needs its statement. The waves below order the work
so that a wrong statement low in the graph is caught before its consumers are attempted, and so
that the short ones calibrate the agents. Within a wave, rows are independent. Lengths are
expected proof lengths. "Deps" are within the stage; everything else is existing API.

Rules. Dispatch follows CONTRIBUTING §11 of branch `workflow/agent-hierarchy` (`586dc1a`;
parallel proving approved by the maintainer, 2026-10-24): proving is parallel from a fixed
skeleton, "in the dependency order of the note's proof plan", a worker owns "one declaration (or
the small group the plan bundles)", and scripted checks plus a tier-1 review gate acceptance. The
waves are advisory, except that wave 1 finishes first (it calibrates the workers on short proofs
and exercises every new definition). Suggested bundles (one worker each, same file, same proof
pattern): {I1, I2}, {I3, I4}, {D4, D5}, {D6, D7, D8}, {T6, T7}, {D1, D2}, {D20, D21}. Each worker builds in its own copy; the hunks touch
disjoint `sorry`s. Memory (CONTRIBUTING §10): a worker's Lean server holds the imports of
`SpectralDensity.lean`, several GB.

**Skeleton (orchestrator, wave 0):** the three definitions with docstrings, every statement with a
`sorry`, module docstrings, constants-registry markers. Definitions are not dispatched.

| # | Name | File | Deps | Diff. (lines) | Key lemmas | Wave |
|---|---|---|---|---|---|---|
| F1 | `Finset.abs_sum_mul_sub_mul_sum_le_of_lipschitzOnWith` | ForMathlib Lipschitz | — | M (45–65) | `Finset.induction_on_max` generalising `t`; `Finset.sum_insert`, `Finset.filter_insert` (for `y < x₀`, `{z ∈ insert x₀ s' \| z ≤ y} = {z ∈ s' \| z ≤ y}`); IH at `t := x₀`; `LipschitzOnWith.dist_le_mul`, `Real.dist_eq`; `abs_add`, `mul_le_mul` | 1 |
| F3 | `MeasureTheory.integral_eq_sum_measureReal_singleton_mul` | ForMathlib SumMeasure | — | S (15–25) | `Measure.restrict_eq_self_of_ae_mem`, `setIntegral_finset`, `integrableOn_finset_iUnion`, `integrableOn_singleton`, `measure_lt_top` | 1 |
| F4 | `MeasureTheory.measureReal_Iic_eq_sum` | ForMathlib SumMeasure | — | S (15–25) | `measureReal_congr`/ae-restrict to `s`; `Finset.coe_filter`; `measureReal_biUnion_finset` on singletons (`MeasurableSet.singleton`, pairwise disjoint) | 1 |
| X1 | `spectralMeasure_real` | Matrix SpectralMeasure | — | S (0: rename the private `spectralMeasure_real_eq`, update its 3 uses) | — | 1 |
| X2 | `Matrix.IsHermitian.isStarProjection_cfc_indicator` | Matrix SpectralMeasure | — | S (10–20) | either `isStarProjection_iff`, idempotent by `← cfc_mul` (continuity from `A.finite_real_spectrum.continuousOn`) and `Set.indicator` idempotence, self-adjoint by `cfc_predicate`; or `isStarProjection_iff_spectrum_subset_and_isSelfAdjoint` with `cfc_map_spectrum` (spectrum $\subseteq \{0,1\}$) | 1 |
| X3 | `Matrix.IsHermitian.empiricalSpectralMeasure_real` | Matrix SpectralMeasure | — | S (15–25) | `Measure.smul_apply`, `Measure.coe_finsetSum`, `Measure.dirac_apply` (all sets, `MeasurableSingletonClass`), `NLAlib.integral_empiricalSpectralMeasure` with `f := indicator`, `hA.re_trace_cfc` | 1 |
| X4 | `Matrix.IsHermitian.lanczosQuadrature_eq_spectralMeasure_of_krylovGrade_le` | Krylov Quadrature | — | S (15–25) | `Measure.ext`; `lanczosQuadrature`, `spectralMeasure_apply` on both sides, private `quadForm_cfc_rangeProjector`, `Matrix.IsHermitian.lanczosFA_eq_cfc_mulVec_of_krylovGrade_le`, `quadForm_def` | 1 |
| I1, I2 | `isFiniteMeasure_probeSpectralMeasure`, `isFiniteMeasure_slqMeasure` | SpectralDensity | — | S (2 each) | `unfold; infer_instance` (checked) | 1 |
| I3, I4 | `integrable_probeSpectralMeasure`, `integrable_slqMeasure` | SpectralDensity | — | S (5–10 each) | `Integrable.smul_measure_nnreal`, `integrable_finset_sum_measure`, `integrable_spectralMeasure`; for I4 unfold `lanczosQuadrature` to a spectral measure | 1 |
| G1 | `girardHutchinson_smul` | GirardHutchinson | — | S (5) | `girardHutchinson`, `Matrix.mul_smul`, `Matrix.smul_mul`, `Matrix.trace_smul`, `smul_eq_mul`, `mul_div_assoc` | 1 |
| T8 | `Matrix.IsHermitian.im_slq` | Trace SLQ | — | S (15–25) | per probe `HasOrthonormalCols.lanczosFA_eq` with a frame `exists_hasOrthonormalCols_range_eq_krylovSpace`, `star b ⬝ᵥ (Q *ᵥ M *ᵥ Qᴴ *ᵥ b) = quadForm M (Qᴴ *ᵥ b)`, `cfc` of a real function is Hermitian (`cfc_predicate`), imaginary part of a Hermitian quadratic form is $0$ (NLAlib `Matrix.IsHermitian` quadForm lemma, to locate), `map_sum`, `RCLike.im` of a division by a natural | 1 |
| T2 | `Matrix.IsHermitian.norm_trace_cfc_sub_slq_le_of_isUniformApproxOn` | Trace SLQ | — | S/M (25–40) | `girardHutchinson_eq_sum`, `quadForm_def`, `Finset.sum_sub_distrib`, `norm_sub_le` (triangle), `norm_sum_le`, the per-probe `…norm_star_dotProduct_cfc_mulVec_sub_lanczosFA_le_of_isUniformApproxOn`, `frobNorm_sq_eq_sum_col`, `Matrix.col_apply`, `norm_div`, case `card m = 0` | 1 |
| D1 | `integral_probeSpectralMeasure` | SpectralDensity | — | S (15–25) | `integral_smul_nnreal_measure`, `integral_finsetSum_measure` (`integrable_spectralMeasure`), `integral_spectralMeasure`, `girardHutchinson_eq_sum`, `map_sum`, `RCLike.re` of a real division (`RCLike.div_re_ofReal`/`map_div₀` route), `NNReal.coe_inv` | 1 |
| D2 | `integral_slqMeasure` | SpectralDensity | I4 (statement) | S (15–25) | as D1 with `integral_lanczosQuadrature`; integrability from I4 | 1 |
| D4 | `Matrix.IsHermitian.probeSpectralMeasure_real_univ` | SpectralDensity | — | S (10–20) | `measureReal_def`, `Measure.smul_apply`, `Matrix.IsHermitian.spectralMeasure_real_univ`, `frobNorm_sq_eq_sum_col`, `ENNReal.toReal_sum` | 1 |
| D5 | `Matrix.IsHermitian.slqMeasure_real_univ` | SpectralDensity | — | S (10–20) | as D4 with `Matrix.IsHermitian.lanczosQuadrature_real_univ` | 1 |
| D6 | `ae_mem_spectrum_probeSpectralMeasure` | SpectralDensity | — | S (10–15) | `ae_iff`, `Measure.smul_apply`, `Measure.coe_finsetSum`, `spectralMeasure_compl_spectrum_eq_zero` | 1 |
| D8 | `Matrix.IsHermitian.ae_mem_Icc_slqMeasure` | SpectralDensity | — | S (10–15) | as D6 with `Matrix.IsHermitian.ae_mem_Icc_lanczosQuadrature` | 1 |
| F2 | `Finset.abs_sum_mul_le_of_lipschitzOnWith` | ForMathlib Lipschitz | F1 | S (15–25) | F1 at `t := b`; `|∑ d| ≤ K` from `hK` at `s.max'` (`Finset.filter_true_of_mem`, `Finset.le_max'`), empty case; `abs_mul` | 2 |
| D3 | `probeSpectralMeasure_real` | SpectralDensity | X1 | S (15–25) | `measureReal_def`, `Measure.smul_apply`, `Measure.coe_finsetSum`, X1 per probe (`ENNReal.toReal_sum` with finiteness), `girardHutchinson_eq_sum` | 2 |
| D7 | `ae_mem_Icc_probeSpectralMeasure` | SpectralDensity | D6 | S (3–5) | `filter_upwards [D6]` with `hs` | 2 |
| D9 | `Matrix.IsHermitian.matchesMoments_probeSpectralMeasure_slqMeasure` | SpectralDensity | D1, D2 | S/M (20–30) | D1, D2 at `f := p.eval`; `slq` unfolded, `Matrix.IsHermitian.star_dotProduct_lanczosFA_eval`, `cfc` of a polynomial = `aeval` (`Matrix.IsHermitian.cfc_eval`… or `cfc_polynomial`), `girardHutchinson_eq_sum`, `quadForm_def` | 2 |
| D10 | `Matrix.IsHermitian.slqMeasure_eq_probeSpectralMeasure_of_card_le` | SpectralDensity | X4 | S (8–12) | `slqMeasure`, `Finset.sum_congr`, X4 with `krylovGrade_le_card` | 2 |
| D11 | `integral_integral_probeSpectralMeasure` | SpectralDensity | D1 | S (15–25) | D1, `integral_div`, `integral_re` (integrability: `IsIsotropic.integrable_quadForm` summed), `integral_girardHutchinson`, `Matrix.IsHermitian.integral_empiricalSpectralMeasure` | 2 |
| T3 | `…norm_trace_cfc_sub_slq_le_of_lipschitzOnWith` | Trace SLQ | T2 | S (12–20) | `exists_degree_le_isUniformApproxOn_Icc_of_lipschitzOnWith (𝕜 := ℝ) haa hf (2 * q + 1)`, degree `2q+1 < 2(q+1)`, T2, `ring`/`field_simp` on $2\cdot\pi L(b-a)/(2(2q+3))$ (copy the KS4 proof shape) | 2 |
| T4 | `…norm_trace_cfc_sub_slq_le_of_differentiableOn` | Trace SLQ | T2 | S (12–20) | `exists_degree_le_isUniformApproxOn_Icc_of_differentiableOn` at `N := 2 * q + 1`, T2 (copy the KS4 analytic proof) | 2 |
| T5 | `measureReal_abs_trace_cfc_sub_slq_ge_le_of_isUniformApproxOn` | Trace SLQ | T2 | S (15–25) | `measureReal_mono` (finite measure: `hind.isProbabilityMeasure`) into the event of `measureReal_abs_trace_sub_girardHutchinson_ge_le` with `B := cfc f A`; T2 over ℝ (`Real.norm_eq_abs`); `linarith` | 2 |
| F5 | `MeasureTheory.abs_integral_sub_integral_le_of_lipschitzOnWith` | ForMathlib SumMeasure | F2, F3, F4 | S/M (25–35) | F3 for μ and ν, `← Finset.sum_sub_distrib`, `mul_sub`; F2 with `d y := μ.real {y} - ν.real {y}`; F4 and `Finset.sum_sub_distrib` to turn `hK` into the partial-sum hypothesis | 3 |
| T6 | `measureReal_abs_trace_cfc_sub_slq_ge_le_of_lipschitzOnWith` | Trace SLQ | T3 (or T5) | S (15–20) | as T5 with T3 in place of T2 | 3 |
| T7 | `measureReal_abs_trace_cfc_sub_slq_ge_le_of_differentiableOn` | Trace SLQ | T4 | S (15–20) | as T5 with T4 | 3 |
| D12 | `measureReal_abs_empiricalSpectralMeasure_real_sub_probeSpectralMeasure_real_ge_le` | SpectralDensity | D3, X2, X3, G1 | M (45–70; split off a private helper "the exponent decreases when $\|\mathbf B\|_{\mathsf F}^2 \le 1/n$, $\|\mathbf B\|_2 \le 1/n$", 20–30, if longer) | event rewrite: D3, X3 over ℝ (`RCLike.re_to_real`), `B := (1/n) • cfc 1_S A`, `girardHutchinson` linear by G1, `Matrix.trace_smul`; `measureReal_abs_trace_sub_girardHutchinson_ge_le` at `B`; X2 with `IsStarProjection.frobNorm_sq_eq_rank`, `Matrix.rank_le_card_width`, `IsStarProjection.specNorm_le_one`, `frobNorm_smul`, `specNorm_smul`; monotonicity `Real.exp_le_exp`, `min_le_min`, `div_le_div_of_nonneg_left`; cases `B = 0`, `c = 0`, `n` empty | 3 |
| D15 | `…abs_integral_probeSpectralMeasure_sub_integral_slqMeasure_le_of_lipschitzOnWith` | SpectralDensity | D4, D5, D7, D8, D9 | S/M (20–35) | `exists_degree_le_isUniformApproxOn_Icc_of_lipschitzOnWith (𝕜 := ℝ) hab hf (2 * q + 1)`; `(D9 …).abs_integral_sub_integral_le_of_isUniformApproxOn` with D7, D8, integrability (D1/D2's), degree `< 2 (q + 1)`; D4, D5 (`q + 1 > 0`); arithmetic | 3 |
| D13 | `measureReal_exists_abs_empiricalSpectralMeasure_real_sub_probeSpectralMeasure_real_gt_le` | SpectralDensity | D12 | S/M (25–40) | rewrite the event as `⋃ x ∈ A.finite_real_spectrum.toFinset, {τ ≤ |…|}` (`Set.Finite.mem_toFinset`, `le_of_lt`), `measureReal_mono`, `measureReal_biUnion_finset_le`, D12 per point, `Finset.sum_le_card_nsmul`; private helper: card of the spectrum ≤ `card n` (`Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues`, `Set.ncard_range_le` / `Finset.card_image_le`), 10–15 | 4 |
| D14 | `…abs_integral_empiricalSpectralMeasure_sub_integral_probeSpectralMeasure_le` | SpectralDensity | F5, D6 | S (15–25) | F5 with `s := A.finite_real_spectrum.toFinset`; supports: `hA.ae_mem_spectrum_empiricalSpectralMeasure`, D6; `hs` | 4 |
| D20 | `Matrix.IsHermitian.abs_one_sub_probeSpectralMeasure_real_univ_le` | SpectralDensity | D4, D6, X3 | S (15–25) | $x^\ast$ the largest eigenvalue (`hA.spectrum_real_eq_range_eigenvalues`, `Set.Finite.exists_maximal`/`Finset.max'` of the finite spectrum); `(empiricalSpectralMeasure A).real (Iic x*) = 1` (`hA.ae_mem_spectrum_empiricalSpectralMeasure`, `measureReal_univ_eq_one`); the probe CDF at $x^\ast$ is its mass (D6, `measureReal_congr`), so `hK x*` | 4 |
| D21 | `Matrix.IsHermitian.abs_empiricalSpectralMeasure_real_Iic_sub_probeSpectralMeasure_real_Iic_le` | SpectralDensity | F4, D6 | S (20–30) | `s := A.finite_real_spectrum.toFinset`; if no eigenvalue is $\le x$ both CDFs are $0$ (F4: empty filter) and `hτ`; else $x' = $ the largest eigenvalue $\le x$ (`Finset.max'` of the filter) and F4 gives equal CDFs at $x$ and $x'$ (`Finset.filter_congr`) | 4 |
| D16 | `measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_probeSpectralMeasure_gt_le` | SpectralDensity | D13, D14 | S (15–25) | `measureReal_mono` into D13's event: on its complement (`not_lt`, `push_neg`) D14 gives `≤`, contradiction with `<` | 5 |
| D17 | `measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_slqMeasure_gt_le` | SpectralDensity | D13, D14, D15, D20 | S/M (25–35) | as D16, plus D15, D20 (mass $\le 1 + \tau$; empty $n$: both integrals $0$, `isEmpty_or_nonempty`) and `abs_sub_le` (triangle through the probe measure) | 5 |
| D19 | `measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_smul_slqMeasure_gt_le` | SpectralDensity | D13, D20, F5, D9, D15's ingredients | S/M (30–45) | on D13's complement: D20 gives $M > 0$; `integral_smul_measure`; normalised CDF bound $2\tau$ (§3.5); F5 on $f - f(b)$ (`LipschitzOnWith.sub_const`); M0 on the normalised measures (`MatchesMoments` scales: D9 and `integral_smul_measure`); Jackson degree $2q+1$ | 5 |
| D18 | `exists_forall_…_slqMeasure_gt_le` | SpectralDensity | D17 | M (40–60) | `C := 196`; D17; `HasSubgaussianMGF.integral_sq_le` with `hvar` at some `(i, j)` (`hind.isProbabilityMeasure`), so `1 ≤ c`; `min_eq_left` from `τ ≤ 1 ≤ c`; `le_hansonWrightConstant`; `Real.exp_log`, `Real.exp_le_exp`, `Real.log_le_log`; cases `n`, `m` empty | 6 |
| C1 | `Matrix.IsHermitian.measurable_lanczosFA` (phase C) | Probability Measurability Krylov | — | L (80+, review comment 5; split: (a) `lanczosFA` through a continuous extension, `lanczosFA_congr` with `f ∘ Set.projIcc a a' h`; (b) measurability of $\mathbf b \mapsto \mathbf P\,g(\mathbf P\mathbf A\mathbf P)\mathbf P\mathbf b$) | `Matrix.IsHermitian.lanczosFA_congr`, `continuous_projIcc`, `lanczosFA`, `compressedCfc`, `measurable_rangeProjector`, `measurable_krylovMatrix`, `continuousOn_cfc`, `ContinuousOn.comp_measurable`-type step into the closed set of self-adjoint matrices with spectrum in a compact set; under `open scoped Matrix.Norms.L2Operator` | C |
| C2 | `…norm_trace_cfc_sub_integral_slq_le_of_isUniformApproxOn` (phase C) | Trace SLQ | C1, T2 | M (40–60) | C1 per column, `Integrable.mono` with the bound of T2, `integral_girardHutchinson`, `integral_sub`, `norm_integral_le_integral_norm`, `integral_mono`, `IsIsotropic.integral_norm_sq`, `frobNorm_sq_eq_sum_col` | C |

Difficulty count, phases A and B (42 dispatched rows counting I1–I4 separately; the 3
definitions are in the skeleton): S 32 (including the rename X1), S/M 7 (T2, D9, F5, D15, D13,
D17, D19), M 3 (F1, D12 with its optional helper, D18), L 0. Counting an S/M row as M when its
upper estimate exceeds 30 lines (all but D9): S 33, M 9, the figure in §0. Phase C: M 1, L 1. No
phase A/B proof is expected to exceed 70 lines; S4's 80-line limit is the split trigger for D12,
and C1 is planned as two named steps.

Statements I am least sure downstream users want (flags):

1. The "∃ f" event of D16–D19 (users may prefer the deterministic D14 + D13 pair, or a fixed-$f$
   tail; Q8).
2. The $\lvert f(b)\rvert$ term (Q4).
3. The random quadrature term inside the tail events of T5–T7 (Q9; the density tails are now
   deterministic).
4. `slq` valued in `𝕜` rather than `ℝ` (Q2): a real-valued estimate would read
   `RCLike.re (slq …)` in every density statement anyway.
5. D15's name contains `probeSpectralMeasure_sub_…`, which N10 may read as `<alg>_sub_` once
   `probeSpectralMeasure` is an algorithm token; it compares two estimators (as
   `frobNorm_rsvd_sub_truncatedSVD_le` does), so it needs an allowlist entry or the exception list
   of N10.

## 10. Open questions for the maintainer

**Q1. Normalisation of the density estimates.**
(a) $\frac{1}{nm}\sum_j$ (proposed): isotropic probes give $\nu_{\mathbf A}$ in expectation, the
CDF is $\mathsf{girardHutchinson}$ of a projector divided by $n$, and $\sqrt n$-scaled sphere probes
(CTU's unit vectors up to the scale) give probability measures. (b) $\frac1m\sum_j$ (the
`Krylov-Spectral.md` consumer table): unit-norm probes give probability measures directly, but
isotropic probes give mean $n\,\nu_{\mathbf A}$ and every statement carries $n$. (c) normalise by
the mass (a ratio estimator, always a probability measure; costs a factor about $2$ in $\tau$ on
the Kolmogorov event, since the mass deviation is the CDF deviation at $\lambda_{\max}$).
**Recommendation (a)**, with (c) as the inline-normalised corollary D19 of this stage (no
named normalised measure).

**Q2. Names.** `slq` (as `rsvd`, `hutchpp`; the name `Krylov-Spectral.md` §8 already uses),
`slqMeasure`, `probeSpectralMeasure`. Alternatives for the last: `sampleSpectralMeasure`,
`averageSpectralMeasure`, `girardHutchinsonMeasure`; a shorter name would bring D14–D16 under 100
characters. And should `slq` be `ℝ`-valued? **Recommendation:** `slq` in `𝕜` (it composes with
`girardHutchinson`, which is in `𝕜`), `slqMeasure`, `probeSpectralMeasure`.

**Q3. Probe distributions for the tails.**
(a) independent sub-Gaussian entries, unit variance (proposed; Gaussian and Rademacher at
$c = 1$), exactly the Girard–Hutchinson tail's hypotheses; (b) also uniform-sphere / Haar probes,
CTU's main case, with the sharp constant: needs an $m$-sample tail for quadratic forms of sphere
vectors in projectors (sums of independent $\mathrm{Beta}(r/2,(n-r)/2)$), e.g. the optimal
sub-Gaussian proxy $1/(4(\alpha+\beta+1))$ of Beta laws (Marchal–Arbel 2017; Elder 2016;
to check). The library has only the single-vector Dasgupta–Gupta tails
(`RandomMatrix/Haar/Sphere.lean`). (c) isotropic sub-Gaussian vectors with dependent coordinates:
needs a Hanson–Wright for such vectors (false in general without further structure). (d) complex
probes: Hanson–Wright is real. **Recommendation (a) now; (b) as its own Probability stage before a
sphere SLQ corollary**, since the constant matters to users comparing with CTU.

**Q4. Form of the uniform bound.**
(a) for all $L$-Lipschitz $f$, bound $(\lvert f(b)\rvert + L(b-a))\tau +
\frac{\pi L(b-a)}{2q+3}(1+\tau)$ (proposed, D17; exact for the unnormalised measures, the
$(1+\tau)$ from D20); (b) only $f$ with $f(b) = 0$ (shorter; for equal masses it is $W_1$,
otherwise it silently ignores the mass error); (c) the normalised (ratio) estimator, Q1(c): a true
$W_1$-type bound $2L(b-a)\tau + \frac{\pi L(b-a)}{2q+3}$ for $\tau < 1$, now proposed as the
cheap corollary D19 (outside the same event); (d) define a named distance
(`kolmogorovDist μ ν`, or an anchored dual-supremum $W_1$) and state everything in it — the Jackson
note's W1 decision recommends against until reviewed separately. **Recommendation (a) and (c)
together** (D17 and D19), with D13, D14, D20, D21 public so a user can build (b) in a few lines.

**Q5. Constants.**
(a) Inherit Hanson–Wright's $1/196$ (proposed); (b) prove sharper Gaussian or Rademacher
Girard–Hutchinson tails first (Cortinovis–Kressner's explicit constants; the Gaussian exact
chi-square route), which would improve every SLQ tail through the same statements; (c) per-threshold
rank $r_x$ instead of $n$ in D12 (the exponent is $mn^2\tau^2/(c^2 r_x)$ before $r_x \le n$), giving
a sharper but uglier union bound. Inline tail expressions vs a named bound (`slqDensityTail`; N11
says repeated tail expressions should be named, but `girardHutchinson`'s and Hutch++'s tails are
inline): **Recommendation (a), inline (as the Girard–Hutchinson tail), $n$ not $r_x$**; (b) as a
later Probability improvement that changes no statement here if it is exposed through a named
bound, which is an argument for naming the Girard–Hutchinson tail first.

**Q6. Scope.** (a) Phases A and B now, C (bias, measurability of Lanczos-FA) as a separate PR
(proposed); (b) all three now; (c) A only, B later. Also: asymptotic form D18 (B5 review list) —
include (proposed); a sample-size or asymptotic form for the trace tails — not proposed, as
Girard–Hutchinson has none. KPM: later (needs M1, J1). Mean-square error of SLQ: later, after C.
**Recommendation (a).**

**Q7. Citations (PORT_KRYLOV question 3).** The uniform bound is attributed to
`ChenTrogdonUbaru2021` (ICML 2021, review comment 2): confirm key, fields and theorem numbers. The
SISC version of CTU: new key
`ChenTrogdonUbaru2025` beside `ChenTrogdonUbaru2022` (PORT_KRYLOV's recommendation), or update the
existing key? Which theorem numbers to cite for the Wasserstein bound and the dimension-helps
rate, and is it citable now? New keys `UbaruChenSaad2017`, `CortinovisKressner2022`.
**Recommendation:** new key; cite v1 for Appendix C (Jackson, already in use) and the SISC version
for the SLQ/KPM bounds once you confirm locators.

**Q8. The event form.** (a) `∃ f, LipschitzOnWith L f … ∧ bound f < |…|` with $L$ fixed
(proposed; N15's form for "not for all"); (b) $\exists L$ as well (scale-free, but the bound is
linear in $L$ so nothing is gained); (c) fixed-$f$ tails only (weaker: loses the uniformity that
makes it a density estimate); (d) the deterministic pair (D13, D14) only, no combined headline.
**Recommendation (a), keeping D13 and D14 public.**

**Q9. Random quadrature term in the trace tails T5–T7.** (The density tails D17–D19 are
deterministic after the review: the Kolmogorov event controls the mass for free, D20.) For the
trace tails: (a) keep $2\varepsilon\|\mathbf\Omega\|_{\mathsf F}^2/m$ inside the event (proposed; no
extra hypothesis, exact composition); (b) a corollary with $2\varepsilon n(1+\tau')$ on a second
Girard–Hutchinson event for $\mathbf B = \mathbf I$ (probability
$2\exp(-\tfrac{1}{196}\,m\min(n\tau'^2/c^2, n\tau'/c))$ added), giving the deterministic form
sources print. **Recommendation (a) now, (b) as a corollary when a consumer asks** (it is S, from
T5 and the Girard–Hutchinson tail).

**Q10. Home of F3–F5.** ForMathlib (proposed; measure theory without NLAlib vocabulary, beside
Mathlib's `setIntegral_finset`) or `Polynomial/Orthogonal/Moments.lean` next to M0 (where the
Jackson note's M1 Lipschitz bounds were planned). **Recommendation: ForMathlib**; M1 then imports it.

## 11. Deferred, with what is missing

1. **Sphere and Haar probes, sharp constants** (Q3(b)): an $m$-sample tail for
   $\frac1m\sum_j\|\mathbf V^{\mathsf H}\mathbf u_j\|^2$, $\mathbf u_j$ independent uniform on the
   sphere; or the Beta sub-Gaussian proxy. Then a corollary of D13 with $1/196 \to$ the Beta
   constant. Unbiasedness already covers these probes (D11).
2. **KPM** (needs M1 and J1; `Krylov-Spectral.md` §8 item 5). The probe measure's Chebyshev
   moments are the KPM moments (D1 with $f = T_k$), so KPM will consume D1, D11, D12.
3. **Phase C** (bias; measurability of Lanczos-FA in the start vector), §3.7.
4. **Mean-square error and variance of SLQ** (Gaussian exact variance of the probe-measure
   integral is `integral_norm_trace_sub_girardHutchinson_sq_of_hasLaw_gaussianMatrix` for
   `cfc f A / n`, one line after D1; not proposed without a consumer).
5. **Analytic test functions for the density** (uniform over a Bernstein-ellipse class): the
   same composition with the analytic rate; no consumer named.
6. **Krylov-aware trace estimation** (Hutch++ with Lanczos; block round).
7. **The prototype library's SLQ material**: unexamined (not on this machine).

## 12. Relation to KS7 (orthogonal-polynomial structure)

The parallel note `docs/design/Polynomial-OrthogonalStructure.md` did not exist when the first
draft was finished; it appeared before the review was folded in, and its §0 item 7 and consumer
table agree with this section (read, not edited). SLQ needs **no KS7 result**:

* exactness through degree $2q - 1$: `Matrix.IsHermitian.matchesMoments_lanczosQuadrature` (KS3b);
* the Gauss-rule reading below the grade:
  `HasOrthonormalCols.lanczosQuadrature_eq_interpolatoryQuadrature` (KS3c), not used by any
  statement here;
* nodes and weights from $\mathbf T$: `Matrix.IsHermitian.lanczosQuadrature_succ_eq_sum`
  (Golub–Welsch, from the recurrence, without `jacobiMatrix`);
* uniform error transfer: M0.

What KS7 would add for SLQ later: a canonical Gauss rule `gaussQuadrature μ q` would let the SLQ
measure be stated as the average of the Gauss rules of the probes' spectral measures without a
Krylov basis (a bridge, not a new result); Gauss–Radau/Lobatto rules and the sign of the Gauss
error for $f$ with sign-definite derivatives would give one-sided SLQ bounds (needs the Hermite
remainder too). Neither is in this stage, and no statement here would change.
