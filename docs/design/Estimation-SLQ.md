# Estimation: stochastic Lanczos quadrature

Status: approved by the maintainer 2026-10-24 (drafted 2026-10-24 by an Opus agent from the
orchestrator's brief; Fable review folded in 2026-10-24; maintainer decisions applied 2026-10-24).
Skeleton of phases A and B written 2026-10-24 on `design/ks7-slq` (see "Changes during the
skeleton"); phase B-sphere (E1–E4) waits for `Probability-Beta`, phase C for its own PR.

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

## Maintainer decisions and the Gauss-rule restructuring (2026-10-24)

Direction, verbatim: "I want the OP and SLQ stuff to integrate well. I.e. mathematically. we
should think of SLQ and GQ on the individual probe densities." What changed:

1. **SLQ is the per-probe Gauss rule, averaged.** `slq` and `slqMeasure` are now defined through
   KS7's `gaussQuadrature (spectralMeasure A ω_j) q` (§1). Lanczos enters only through KS7's
   `Matrix.IsHermitian.lanczosQuadrature_eq_gaussQuadrature`, in two bridges: T0
   `slq_eq_sum_lanczosFA` (the algorithm) and D22 `slqMeasure_eq_sum_lanczosQuadrature`.
2. **The quadrature-error analysis is KS7's generic Gauss error per probe, then averaged**: T2
   (uniform approximation, #66), T3 and D15 (Lipschitz, #68), T4 (Bernstein ellipse, #66 with the
   KS4 approximant; KS7 left this corollary to SLQ). D5, D8, D9, D10 now come from KS7's mass,
   support, exactness (with `MatchesMoments.smul`/`finsetSum` for the average) and Gauss-rule
   uniqueness. Dropped: X4 (`lanczosQuadrature_eq_spectralMeasure_of_krylovGrade_le`, replaced by
   KS7 uniqueness) and T8 `im_slq` (immediate, `slq` is an `ofReal`).
3. **§12 reversed**: SLQ depends on the KS7 Gauss-rule core; §12 lists each declaration used and
   §9 makes them prerequisites (wave K). The KS7 names are final ("Interface for SLQ",
   `Polynomial-OrthogonalStructure.md`); none is provisional.
4. **Decisions recorded in §10** (all "decided 2026-10-24"): Q1 (a), Q2a (a), Q2b (a), Q3 (b),
   Q4 (a + c), Q5 (a), Q6 (a), Q7a (a), Q7b (b), Q8 (a), Q9 (a), Q10 (a).
5. **Q3 (b): sphere probes with the sharp Beta constant**: new phase B-sphere (§3.8, E1–E4 here)
   on a prerequisite Probability stage (12 named steps; the Beta sub-Gaussian proxy is the one
   research-risk item). The sub-Gaussian-entry tails are kept; Q3′ asks to confirm.
6. **Citations**: `ChenTrogdonUbaru2021` (ICML) and `ChenTrogdonUbaru2025` (SISC) are distinct
   works, each cited only for its own results (Q7a); fields stay "to check".
7. Signatures changed by this revision were re-elaborated with `sorry` bodies against KS7
   stand-ins (`/tmp/claude-1000/slq-scratch/Shapes6.lean`).

## Changes during the skeleton (2026-10-24)

The skeleton (branch `design/ks7-slq`, on the KS7 skeleton `413dabb`) covers phases A and B. Every
statement of §3.1–§3.6 is written as signed there, except X2 (item 3). 37 declarations are sorried
in `NLAlibScaffold/` (S 29, S/M 5, M 3; counting S/M as M, S 29 and M 8, the 42 rows of §9 less
the five proved here); proved in the skeleton: the 3 definitions (`slq`, `probeSpectralMeasure`,
`slqMeasure`), I1 and I2 (the instances, `unfold; infer_instance`), and X1, X2, X3. Dispatch
targets: `nlalib-harness/pilot/slq-targets.json` (with the KS7 **[SLQ-1]** theorems each row uses,
`ks7_deps`). Deviations from the note:

1. **E1–E4 are not in the skeleton.** They need `Probability-Beta` (β3, β4, β5), which is not
   approved; they are deferred until after that stage. Phase C (C1, C2) is a later PR (Q6).
2. **X2 and X3 are proved in `NLAlib/Matrix/Spectral/SpectralMeasure.lean`, not sorried.** Their
   scaffold path, `NLAlibScaffold/Matrix/Spectral/SpectralMeasure.lean`, is a KS7 file that this
   skeleton does not touch; both are short (under 15 lines each). X1 is the rename of the private
   `spectralMeasure_real_eq` (one use updated). The three are added to the module's main results.
3. **X2 loses its Hermitian hypothesis**, as the minimal fix: `cfc_mul` needs no predicate (off
   Hermitian `cfc` is $0$, a star projection), so `hA` was unused, which T13 and the
   unused-variables linter (`--wfail`) reject. The statement is now
   `NLAlib.isStarProjection_cfc_indicator (A : Matrix n n 𝕜) (S : Set ℝ) :
   IsStarProjection (cfc (S.indicator fun _ => (1 : ℝ)) A)`; D12's outline uses that name.
4. **File order in the density scaffold**: I3, I4, D1, D2, D22, D3, D4–D11, D14, D20, D21, D15,
   D12, D13, D16, D17, D19, D18; D22 sits beside D2 (the Lanczos form of the integrals) instead of
   after D11. Dependencies still precede their users.
5. **Imports by file.** The NLAlib files carry only what the definitions need
   (`Matrix/Spectral/SpectralMeasure`, `Polynomial/Orthogonal/Gauss`); the density file does not
   import the trace file, since `slq` appears only in scaffold statements. Each scaffold file
   imports its NLAlib counterpart and the scaffold files it depends on: trace → KS7 scaffold
   `Krylov/Functions/Quadrature` (so #54 and the Gauss scaffold), `Polynomial/Approximation/
   AnalyticApproximation`, `Estimation/Trace/GirardHutchinson`; density → scaffold trace, scaffold
   `GirardHutchinson` (G1), scaffold `SumMeasure` (F3–F5, and through it F1, F2).
6. **Docstrings.** Citations whose locator is unchecked are written `[Key, label] (locator to
   check)`, as in KS7; the note's row labels (D20, D22, …) are not in the docstrings. In T6 the
   Jackson value is shown in an inline span before the display: `scripts/check_constants.py`
   misparses two argument-free value markers in a row (its `MARK` pattern lets the first marker's
   optional arguments run to the second marker's `-->`). Two long names are not listed in the
   density scaffold's module docstring (a module docstring cannot take S8).
7. **Not added yet** (as in KS7): the three §5.3 rows (§1.3) and the Mathlib-deviations
   paragraph (§8), which go in with the first proof PR (this skeleton edits only SLQ's files), and
   no `docs/constants.toml` change (no new named bound). Bibliography: `ChenTrogdonUbaru2021`,
   `ChenTrogdonUbaru2025`, `UbaruChenSaad2017`, `CortinovisKressner2022` added with the fields of
   §7, each with a "to check" note (CTU 2021's pages "to check").

## 0. Summary

**The structure (maintainer, 2026-10-24: "we should think of SLQ and GQ on the individual probe
densities").** Each probe $\boldsymbol\omega_j$ has its spectral measure (probe density)
$\mu_j = \mu_{\mathbf A,\boldsymbol\omega_j}$. SLQ is, probe by probe, KS7's canonical Gauss rule
of $\mu_j$, then averaged:
$$\mathsf{slqMeasure}(\mathbf A,\mathbf\Omega,q) = \frac{1}{nm}\sum_j \mathsf{gaussQuadrature}(\mu_j, q),
\qquad \mathsf{slq}(\mathbf A,f,\mathbf\Omega,q) = \frac1m\sum_j\int f\,d\,\mathsf{gaussQuadrature}(\mu_j,q).$$
Every quadrature fact is KS7's, applied to one $\mu_j$ and averaged: exactness (2q moments), the
generic Gauss error bound $\lvert\int f\,d\mu - \int f\,d\,\mathsf{gauss}\rvert \le
2\varepsilon\mu(\mathbb R)$
(`abs_integral_sub_integral_gaussQuadrature_le_of_isUniformApproxOn` and its Lipschitz corollary),
support and mass. The Lanczos algorithm enters only through KS7's
identification `Matrix.IsHermitian.lanczosQuadrature_eq_gaussQuadrature`, in two bridge theorems
that show the definition is what the algorithm computes. The average of Gauss rules is not the
Gauss rule of the average (it has up to $mq$ nodes and matches only $2q$ moments of the probe
measure); no statement says otherwise.

**Scope (decided 2026-10-24: phases A and B now, C later).**

* **A. Trace estimation of $\operatorname{tr} f(\mathbf{A})$.** `slq`; its Lanczos-FA form; the
  split of its error into the Girard–Hutchinson error plus the averaged Gauss error
  $2\varepsilon\|\mathbf{\Omega}\|_{\mathsf{F}}^2/m$, with the Lipschitz (Jackson) and analytic
  (Bernstein ellipse) rates; the sub-Gaussian tails, by composing with the existing Hanson–Wright
  tail of Girard–Hutchinson (quadrature term random in the event, Q9(a)).
* **B. Spectral density estimation.** `probeSpectralMeasure` $=\frac{1}{nm}\sum_j\mu_j$ (decided
  normalisation, Q1(a)) and `slqMeasure`; identities, masses, supports, moment matching, equality
  for $q \ge n$; unbiasedness for isotropic probes; and the uniform bound over $L$-Lipschitz test
  functions in one event (Q8(a)), in both forms decided under Q4 (a + c):
  with $m$ probes with independent sub-Gaussian entries, outside probability
  $2n\exp(-\tfrac{1}{196}mn\min(\tau^2/c^2,\tau/c))$,
  $$\Bigl\lvert\int f\,d\nu_{\mathbf{A}} - \int f\,d\,\mathsf{slqMeasure}(\mathbf{A},\mathbf{\Omega},q+1)\Bigr\rvert
  \le (\lvert f(b)\rvert + L(b-a))\tau + \frac{\pi L(b-a)}{2q+3}(1+\tau),$$
  and for the mass-normalised estimate $2L(b-a)\tau + \pi L(b-a)/(2q+3)$; plus the asymptotic
  "$m = O(c^2\log(n/\delta)/(n\tau^2))$ suffices". The route: a finite Abel summation on the
  spectrum, the CDF of the probe measure as a Girard–Hutchinson estimate of a spectral projector,
  the Girard–Hutchinson tail, a union bound over at most $n$ eigenvalues.
* **B-sphere (decided Q3(b), 2026-10-24): sphere probes with the sharp Beta constant.** With
  $\boldsymbol\omega_j = \sqrt n\,\mathbf u_j$, $\mathbf u_j$ independent and uniform on the
  sphere, outside probability $2n\exp(-m(n+2)\tau^2)$ every $L$-Lipschitz $f$ has
  $\lvert\int f\,d\nu_{\mathbf A} - \int f\,d\,\mathsf{slqMeasure}\rvert \le L(b-a)\tau +
  \pi L(b-a)/(2q+3)$ (both measures are probability measures here, so no $\lvert f(b)\rvert$ and
  no $1+\tau$) [ChenTrogdonUbaru2021, to check]. It needs two Probability results the library
  lacks: the Beta law of $\|\mathbf V^{\mathsf H}\mathbf u\|^2$ and the sub-Gaussian bound of
  Beta laws with proxy $1/(4(\alpha+\beta+1))$. Both go to a **prerequisite Probability stage**
  (§3.8; two L steps there, the Gamma-ratio change of variables and the Beta proxy, the latter
  a research-risk item). The SLQ
  corollaries are S/M once it exists. The sub-Gaussian-entry tails stay (they come almost free
  from the Girard–Hutchinson tail); Q3′ asks to confirm.
* **C (later, decided Q6(a)). Bias in expectation**,
  $\lvert\operatorname{tr}f(\mathbf{A}) - \mathbb{E}\,\mathsf{slq}\rvert \le 2\varepsilon n$; needs
  measurability of the Gauss rule of $\mu_{\mathbf A,\mathbf b}$ in $\mathbf b$ (§3.7).

**Out of scope:** KPM (needs M1 and J1); Haar-frame probes for the tails (dependent columns; §11);
a named Wasserstein or Kolmogorov distance; Gauss–Radau; finite precision.

**Counts.** Phases A and B: 45 declarations (3 definitions, 2 instances, 40 theorems); 9 are
additions to lower or ForMathlib files; 42 dispatched proofs, S 34, M 8, L 0; 14 KS7
declarations (2 definitions, 1 instance, 11 theorems) are prerequisites. Phase B-sphere: 4 in this stage (S 1, M 3) after a prerequisite
Probability stage of 12 named steps (S 4, M 6, L 2). Phase C: 2 (M, L). No new interface; three new §5.3 rows; no named bound.

**Depends on KS7** (§12): the Gauss-rule core of `Polynomial/Orthogonal/Gauss.lean` and the
identification in `Krylov/Functions/Quadrature.lean`. Those declarations are prerequisites of
the proof plan (§9, wave K).

## 1. Objects

All definitions over `[RCLike 𝕜]`, total, in `namespace NLAlib`, probes as the columns of a test
matrix `Ω : Matrix n m 𝕜`, exactly as `girardHutchinson` (§5.3 row "Girard–Hutchinson estimate").
Columns are written `fun i => Ω i j`, the spelling of `girardHutchinson_eq_sum` (Mathlib's
`Ω.col j` unfolds to it by `Matrix.col_apply`; `frobNorm_sq_eq_sum_col` uses `.col`). KS7 names
are final, from "Interface for SLQ" in `Polynomial-OrthogonalStructure.md` (§12 lists them).

### 1.1 The SLQ trace estimate

```lean
/-- The **stochastic Lanczos quadrature** estimate of $\operatorname{tr} f(\mathbf{A})$ from the
test matrix $\mathbf{\Omega}$, whose $m$ columns $\boldsymbol{\omega}_1, \dots,
\boldsymbol{\omega}_m$ are the probes: the average over the probes of the $q$-point Gauss rule of
each probe's spectral measure $\mu_j = \mu_{\mathbf A,\boldsymbol\omega_j}$ applied to $f$,
$$\mathsf{slq}(\mathbf{A}, f, \mathbf{\Omega}, q) := \frac{1}{m}\sum_{j=1}^m
\int f\,d\,\mathsf{gaussQuadrature}(\mu_j, q)\,,$$
the Girard–Hutchinson estimate with each
$\boldsymbol{\omega}_j^{\mathsf{H}}f(\mathbf{A})\boldsymbol{\omega}_j = \int f\,d\mu_j$ replaced
by its Gauss quadrature. For Hermitian $\mathbf A$ this is what $q$ Lanczos steps per probe
compute, $\frac1m\sum_j\boldsymbol\omega_j^{\mathsf H}\mathsf{lanczosFA}(\mathbf A, f,
\boldsymbol\omega_j, q) = \frac1m\sum_j\|\boldsymbol\omega_j\|^2\mathbf e_1^{\mathsf T}
f(\mathbf T_j)\mathbf e_1$ (`Matrix.IsHermitian.slq_eq_sum_lanczosFA`), with $mq$ products with
$\mathbf A$. A real number in `𝕜`. Junk value: $0$ when $\mathbf{\Omega}$ has no columns, when
$q = 0$ and when $\mathbf A$ is not Hermitian.
[UbaruChenSaad2017, §3, locator to check]; [MartinssonTropp2020, §6.6, Algorithm 6]. -/
noncomputable def slq (A : Matrix n n 𝕜) (f : ℝ → ℝ) (Ω : Matrix n m 𝕜) (q : ℕ) : 𝕜 :=
  ((∑ j, ∫ x, f x ∂gaussQuadrature (spectralMeasure A (fun i => Ω i j)) q : ℝ) : 𝕜) /
    Fintype.card m
```

Valued in `𝕜` (decided, Q2b(a)): the error reads `(cfc f A).trace - slq A f Ω q` (N10) and
composes with `girardHutchinson`, which is in `𝕜`. The value is real by definition, so the old
`im_slq` (review comment 7) is immediate and no longer a row. Argument order follows
`lanczosFA A f b q` and `girardHutchinson A Ω`.

### 1.2 The two spectral-density estimates

```lean
/-- The **probe spectral measure**: the average of the probes' spectral measures (probe
densities), scaled so that isotropic probes give the empirical spectral measure in expectation,
$$\mathsf{probeSpectralMeasure}(\mathbf{A}, \mathbf{\Omega}) :=
\frac{1}{\lvert n\rvert m}\sum_{j=1}^m \mu_{\mathbf{A},\boldsymbol{\omega}_j}\,.$$
SLQ with exact quadrature (`Matrix.IsHermitian.slqMeasure_eq_probeSpectralMeasure_of_card_le`);
its integral of $f$ is the Girard–Hutchinson estimate of
$\operatorname{tr} f(\mathbf{A})/\lvert n\rvert$ (`integral_probeSpectralMeasure`). Mass
$\|\mathbf{\Omega}\|_{\mathsf{F}}^2/(\lvert n\rvert m)$. Junk value: $0$ when $n$ or $m$ is empty
($0^{-1} = 0$ in $\mathbb{R}_{\ge 0}$) and when $\mathbf{A}$ is not Hermitian.
[ChenTrogdonUbaru2021, locator to check]. -/
noncomputable def probeSpectralMeasure (A : Matrix n n 𝕜) (Ω : Matrix n m 𝕜) : Measure ℝ :=
  ((Fintype.card n * Fintype.card m : ℝ≥0)⁻¹) • ∑ j, spectralMeasure A (fun i => Ω i j)

/-- The **SLQ spectral-density estimate**: the average, scaled as `probeSpectralMeasure`, of the
$q$-point Gauss rules of the probe densities,
$$\mathsf{slqMeasure}(\mathbf{A}, \mathbf{\Omega}, q) := \frac{1}{\lvert n\rvert m}\sum_{j=1}^m
\mathsf{gaussQuadrature}(\mu_{\mathbf A,\boldsymbol{\omega}_j}, q)\,.$$
It is not the Gauss rule of `probeSpectralMeasure`: it has up to $mq$ nodes and matches $2q$
moments of it. For Hermitian $\mathbf A$ it is the average of the Lanczos rules, atoms at each
probe's Ritz values (`Matrix.IsHermitian.slqMeasure_eq_sum_lanczosQuadrature`). Its integral of
$f$ is $\operatorname{Re}\,\mathsf{slq}(\mathbf{A}, f, \mathbf{\Omega}, q)/\lvert n\rvert$
(`integral_slqMeasure`). Junk value: $0$ when $n$ or $m$ is empty or $q = 0$.
[ChenTrogdonUbaru2021, locator to check]; [UbaruChenSaad2017, §3, locator to check]. -/
noncomputable def slqMeasure (A : Matrix n n 𝕜) (Ω : Matrix n m 𝕜) (q : ℕ) : Measure ℝ :=
  ((Fintype.card n * Fintype.card m : ℝ≥0)⁻¹) •
    ∑ j, gaussQuadrature (spectralMeasure A (fun i => Ω i j)) q
```

The scalar is an `ℝ≥0` (with `ℝ≥0∞` it is $\top$ for an empty type and the instances need a case
split). Normalisation $1/(nm)$ (decided, Q1(a)). For isotropic probes
$\mathbb E\int f\,d\,\mathsf{probeSpectralMeasure} = \int f\,d\nu_{\mathbf A}$ (D11); for
$q \ge n$, `slqMeasure A Ω q = probeSpectralMeasure A Ω` (D10, from KS7's uniqueness of the Gauss
rule: a measure on at most $q$ points matching its own moments is its own Gauss rule); with
$\mathbf\Omega = \mathbf I$ the probe measure is $\nu_{\mathbf A}$
(`Matrix.IsHermitian.sum_spectralMeasure_single`).

### 1.3 §5.3 rows (added in the implementing PRs)

| Concept | Spelling | Mathlib bridge |
|---|---|---|
| stochastic Lanczos quadrature | `slq A f Ω q : 𝕜`, the average over the probes (columns of `Ω`) of `∫ f ∂gaussQuadrature (spectralMeasure A ωⱼ) q`; error `(cfc f A).trace - slq A f Ω q` | `Matrix.IsHermitian.slq_eq_sum_lanczosFA` (the algorithm), `integral_slqMeasure`; Mathlib has none |
| probe spectral measure | `probeSpectralMeasure A Ω := (card n * card m : ℝ≥0)⁻¹ • ∑ j, spectralMeasure A ωⱼ`; mass $\|\mathbf\Omega\|_{\mathsf F}^2/(nm)$; its CDF is `girardHutchinson` of a spectral projector | `integral_probeSpectralMeasure`, `probeSpectralMeasure_real`; Mathlib has none |
| SLQ spectral density | `slqMeasure A Ω q`, the same average of `gaussQuadrature (spectralMeasure A ωⱼ) q` | `integral_slqMeasure`, `Matrix.IsHermitian.slqMeasure_eq_sum_lanczosQuadrature`, `Matrix.IsHermitian.slqMeasure_eq_probeSpectralMeasure_of_card_le` |

and `slq` joins the row "an algorithm's output" of §4.3 (`probeSpectralMeasure` does not: it is
the exact-quadrature reference, so D15's `probeSpectralMeasure_sub_…` is exact − computed). The
CDF of a finite measure on $\mathbb R$ is written `μ.real (Set.Iic x)`, not
`ProbabilityTheory.cdf` (probability measures only); no row, no deviation.

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
coordinates (`Probability/QuadraticForm/HansonWright.lean`), so sphere probes get their own
tails (B-sphere, §3.8), with hypotheses `hind : iIndepFun (fun j ω i => U ω i j) μ` and
`hU : ∀ j, HasLaw (fun ω i => U ω i j) (uniformSphereVector n) μ` on the unit columns, the test
matrix being `√(card n) • U ω`; Haar-frame probes (dependent columns) are not covered.

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
```

(The former X4, `lanczosQuadrature_eq_spectralMeasure_of_krylovGrade_le`, is dropped: D10 now
follows from KS7's `MatchesMoments.eq_gaussQuadrature` on each probe density.)

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
Probe by probe, $\boldsymbol\omega_j^{\mathsf H}f(\mathbf A)\boldsymbol\omega_j =
\int f\,d\mu_j$ is replaced by its Gauss rule, whose error is at most
$2\varepsilon\mu_j(\mathbb R) = 2\varepsilon\|\boldsymbol\omega_j\|^2$ (KS7's generic Gauss error
bound); the errors are averaged.
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
/-- T0. **SLQ is what the Lanczos algorithm computes**: for Hermitian $\mathbf A$,
$\mathsf{slq}(\mathbf A, f, \mathbf\Omega, q) = \frac1m\sum_j\boldsymbol\omega_j^{\mathsf H}
\mathsf{lanczosFA}(\mathbf A, f, \boldsymbol\omega_j, q)$: each probe's Gauss rule is its Lanczos
rule (`Matrix.IsHermitian.lanczosQuadrature_eq_gaussQuadrature`, KS7) and the Lanczos rule
integrates to the Lanczos-FA quadratic form (`integral_lanczosQuadrature`), which is real. -/
theorem _root_.Matrix.IsHermitian.slq_eq_sum_lanczosFA {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (f : ℝ → ℝ) (Ω : Matrix n m 𝕜) (q : ℕ) :
    slq A f Ω q =
      (∑ j, star (fun i => Ω i j) ⬝ᵥ lanczosFA A f (fun i => Ω i j) q) / Fintype.card m
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

/-- D22. **The SLQ measure is the average of the probes' Lanczos rules** (KS7's identification,
probe by probe); atoms at the Ritz values, weights from the tridiagonal matrices
(`Matrix.IsHermitian.lanczosQuadrature_succ_eq_sum`). -/
theorem _root_.Matrix.IsHermitian.slqMeasure_eq_sum_lanczosQuadrature {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (Ω : Matrix n m 𝕜) (q : ℕ) :
    slqMeasure A Ω q = ((Fintype.card n * Fintype.card m : ℝ≥0)⁻¹) •
      ∑ j, lanczosQuadrature A (fun i => Ω i j) q

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
same integral: each probe density matches $2q$ moments of its Gauss rule
(`matchesMoments_gaussQuadrature`, KS7), and the averages match. [Gautschi2004, Theorem 1.45];
[GolubMeurant2010, Theorem 6.6], probe by probe.
Result: gauss-quadrature -/
theorem _root_.Matrix.IsHermitian.matchesMoments_probeSpectralMeasure_slqMeasure
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (Ω : Matrix n m 𝕜) (q : ℕ) :
    MatchesMoments (probeSpectralMeasure A Ω) (slqMeasure A Ω q) (2 * q)

/-- With at least $\lvert n\rvert$ nodes, SLQ is exact: each probe density lives on at most
$\lvert n\rvert \le q$ points, so it is its own $q$-point Gauss rule
(`MatchesMoments.eq_gaussQuadrature`, KS7). -/
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
per probe, KS7's generic Gauss error bound with Jackson's polynomial of degree $2q + 1$ gives
$2\varepsilon\mu_j(\mathbb R)$, $\varepsilon = \pi L(b-a)/(2(2q+3))$; averaging gives the bound.
[ChenTrogdonUbaru2025, the uniform quadrature bound, locator to check];
[ChenTrogdonUbaru2022, Appendix C, Theorem 38], the approximation step (arXiv v1 of the same
work). -/
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
[ChenTrogdonUbaru2021, locator to check]. Result: probe-spectral-measure-unbiased -/
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

### 3.8 Phase B-sphere: sphere probes with the sharp Beta constant (decided Q3(b))

Probes $\boldsymbol\omega_j = \sqrt{\lvert n\rvert}\,\mathbf u_j$ with $\mathbf u_j$ independent and
uniform on the unit sphere (CTU 2021's setting). Then $\|\boldsymbol\omega_j\|^2 = n$ surely, so
both the probe measure and the SLQ measure are probability measures (no $\lvert f(b)\rvert$ term,
no $1+\tau$), and at a threshold $x$ with spectral projector $\mathbf P$ of rank $r$,
$\mathsf{probe}(\le x) - \nu_{\mathbf A}(\le x) = \frac1m\sum_j(\mathbf u_j^{\mathsf T}\mathbf P
\mathbf u_j - r/n)$, a centred average of $m$ independent $\mathrm{Beta}(r/2,(n-r)/2)$ variables.
With the Beta sub-Gaussian proxy $1/(4(\alpha+\beta+1)) = 1/(2(n+2))$ and Hoeffding, each
threshold fails with probability at most $2\exp(-m(n+2)\tau^2)$; ranks $0$ and $n$ are
deterministic.

**In this stage** (`Estimation/Spectral/SpectralDensity.lean`, gated on the prerequisite stage):

```lean
/-- E1. **Sphere probes, one threshold** … $\mathbb P[\tau \le \lvert\nu_{\mathbf A}(S) -
\mathsf{probeSpectralMeasure}(\mathbf A, \sqrt{\lvert n\rvert}\,\mathbf U)(S)\rvert] \le
2\exp(-m(\lvert n\rvert + 2)\tau^2)$, the columns of $\mathbf U$ independent and uniform on the
unit sphere. [ChenTrogdonUbaru2021, locator to check]. -/
theorem
measureReal_abs_empiricalSpectralMeasure_real_sub_probeSpectralMeasure_real_ge_le_of_hasLaw_uniformSphereVector
    {U : Ω → Matrix n m ℝ} (hind : iIndepFun (fun j ω i => U ω i j) μ)
    (hU : ∀ j, HasLaw (fun ω i => U ω i j) (uniformSphereVector n) μ) {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (S : Set ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    μ.real {ω | τ ≤ |(empiricalSpectralMeasure A).real S -
        (probeSpectralMeasure A (√(Fintype.card n : ℝ) • U ω)).real S|} ≤
      2 * Real.exp (-(Fintype.card m * (Fintype.card n + 2) * τ ^ 2))

/-- E3. **SLQ with sphere probes, uniformly in Lipschitz test functions**: outside probability
$2\lvert n\rvert\exp(-m(\lvert n\rvert + 2)\tau^2)$, every $L$-Lipschitz $f$ on
$[a, b] \supseteq \operatorname{spec}\mathbf A$ has <!-- value jacksonApproximationConstant -->
$\lvert\int f\,d\nu_{\mathbf A} - \int f\,d\,\mathsf{slqMeasure}(\mathbf A,
\sqrt{\lvert n\rvert}\,\mathbf U, q + 1)\rvert \le L(b-a)\tau + \frac{\pi L(b-a)}{2q+3}$.
[ChenTrogdonUbaru2021, the Wasserstein bound for SLQ, locator to check].
Result: spectral-density-lipschitz-tail -/
theorem
measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_slqMeasure_gt_le_of_hasLaw_uniformSphereVector
    {U : Ω → Matrix n m ℝ} (hind : iIndepFun (fun j ω i => U ω i j) μ)
    (hU : ∀ j, HasLaw (fun ω i => U ω i j) (uniformSphereVector n) μ) {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {a b : ℝ} (hab : a < b) (hs : spectrum ℝ A ⊆ Set.Icc a b) (L : ℝ≥0)
    (q : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) :
    μ.real {ω | ∃ f : ℝ → ℝ, LipschitzOnWith L f (Set.Icc a b) ∧
        L * (b - a) * τ + jacksonApproximationConstant * L * (b - a) / (2 * q + 3) <
        |∫ x, f x ∂empiricalSpectralMeasure A -
          ∫ x, f x ∂slqMeasure A (√(Fintype.card n : ℝ) • U ω) (q + 1)|} ≤
      2 * Fintype.card n * Real.exp (-(Fintype.card m * (Fintype.card n + 2) * τ ^ 2))
```

plus E2 (the Kolmogorov union bound, as D13, with $2n\exp(-m(n+2)\tau^2)$) and E4, the explicit
sample size "$m \ge \log(2n/\delta)/((n+2)\tau^2)$ suffices" (no unknown constant: the sharp
route has none) with its `exists_forall_` form. Names over 100 characters take S8. Both signatures
elaborate (`Shapes6.lean`, with KS7 stand-ins).

**Missing Probability results** — a **prerequisite stage**, `Probability-Beta` (its own design
note; layer 1 or 2, placement there), because they are Probability facts with consumers beyond SLQ
(JL with sphere sketches, Haar-frame tails) and the core step is research-grade in Lean:

```lean
-- β3: the projection of a uniform unit vector is Beta (RandomMatrix/Haar/Sphere.lean)
theorem hasLaw_norm_conjTranspose_mulVec_sq_of_hasLaw_uniformSphereVector
    {u : Ω → n → ℝ} (hu : HasLaw u (uniformSphereVector n) μ) {V : Matrix n k ℝ}
    (hV : HasOrthonormalCols V) (hk : 0 < Fintype.card k) (hkn : Fintype.card k < Fintype.card n) :
    HasLaw (fun ω => ‖WithLp.toLp 2 (Vᴴ *ᵥ u ω)‖ ^ 2)
      (betaMeasure (Fintype.card k / 2) ((Fintype.card n - Fintype.card k : ℕ) / 2)) μ

-- β4: Beta laws are sub-Gaussian with proxy 1/(4(α+β+1)) (Probability/Distributions)
theorem hasSubgaussianMGF_sub_div_of_hasLaw_betaMeasure {X : Ω → ℝ} {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hX : HasLaw X (betaMeasure α β) μ) :
    HasSubgaussianMGF (fun ω => X ω - α / (α + β)) ‖1 / (4 * (α + β + 1))‖₊ μ
```

Mathlib has `betaMeasure`, `gammaMeasure` (`Probability/Distributions/{Beta,Gamma}.lean`) and
Hoeffding (`HasSubgaussianMGF.sum_of_iIndepFun`, `measure_sum_ge_le_of_iIndepFun`); it has no
chi-square law, no ratio-of-Gammas theorem and no Beta MGF bound. NLAlib has the Gaussian
representation of the sphere (`uniformSphereVector`, `hasLaw_inv_norm_smul_of_hasLaw_gaussianVector`)
and rotation invariance (`HasOrthonormalCols.uniformSphereVector_map_conjTranspose_mulVec_eq`).
Named steps, each a ≤ 80-line proof (sizes are estimates):

| Step | Statement | Diff. |
|---|---|---|
| β1a | $g^2$ has law `gammaMeasure (1/2) (1/2)` for $g \sim N(0,1)$ (density pushforward by $x \mapsto x^2$) | M (50–70) |
| β1b-i | independent `gammaMeasure a θ`, `gammaMeasure b θ`: the sum's density is the convolution (`MeasureTheory` convolution of densities) | M (50–70) |
| β1b-ii | that convolution is the `gammaMeasure (a+b) θ` density (Beta-integral identity, Mathlib `Complex.betaIntegral` / `Real.Gamma` relations) | M (40–60) |
| β1 | $\sum_{i<k} g_i^2$ has law `gammaMeasure (k/2) (1/2)` (induction on $k$ from β1a, β1b) | S (20–30) |
| β2a | joint law of independent Gammas as a product density | S (15–25) |
| β2b | change of variables $(x,y) \mapsto (x/(x+y), x+y)$ on $(0,\infty)^2$ (`integral_image_eq_integral_abs_det_fderiv_smul`) | L (split in two: the diffeomorphism and its Jacobian; the integral transport) |
| β2c | $X/(X+Y)$ has law `betaMeasure a b` (marginalise β2b; Gamma integral) | M (40–60) |
| β3 | the statement above: $\mathbf u = \mathbf g/\|\mathbf g\|$, rotate $\mathbf V$ to the first $k$ coordinates, $\|\mathbf V^{\mathsf H}\mathbf g\|^2$ and the rest independent, β1, β2c | M (50–70) |
| β4a | Beta moments $\mathbb E X^k = \prod_{i<k}(\alpha+i)/(\alpha+\beta+i)$ | S (20–30) |
| β4b | the centred MGF of a $[0,1]$-valued variable as its moment series (Mathlib `mgf`, `iteratedDeriv` of `mgf`; or dominated summation) | M (50–70) |
| β4c | **the proxy $1/(4(\alpha+\beta+1))$** (Elder 2016 / Marchal–Arbel 2017, to check): comparison of the Kummer series with $e^{\sigma^2 t^2/2}$; at least two L steps (the recurrence inequality; its induction) | L × 2, research risk |
| β5 | average of $m$ independent centred sub-Gaussians: two-sided Hoeffding (Mathlib) | S (10–15) |

Totals: 12 steps, S 4, M 6, L 2 (β2b, β4c, each to be split further by that stage's note into
≤ 80-line pieces). β4c is the only item I would not hand to open-weight workers without a
written proof sketch; its source should be fixed first (Q3′). Then E1–E4 here are M, S, M, M.

## 4. Consumers

| Item | Consumers, and the form they use |
|---|---|
| `slq`, T2–T4 | Users of trace estimation of matrix functions (log-determinants, Estrada index, nuclear-norm and spectral-sum estimation): the split, then any Girard–Hutchinson result (variance, tail) for `cfc f A`. Krylov-aware trace estimation (block round, `Krylov-Spectral.md` §5 row C6): Hutch++ with Lanczos replaces the residual term the same way. The explorer's Rates page (degree budgets). |
| T5–T7 | Same; the analytic form is the UCS17 theorem in absolute error; downstream sample-size forms |
| `probeSpectralMeasure`, D1–D3, D11 | The density tails here; KPM (later: its Chebyshev moments are `girardHutchinson` of $T_k(\mathbf A)$, so KPM's moment estimator is `integral_probeSpectralMeasure` with $f = T_k$); M1 (noisy moments) |
| `slqMeasure`, D2, D9, D10, D15 | The SLQ density tail; any future quadrature-type density bound (Gauss–Radau, analytic test functions); KPM vs SLQ comparison (CTU 2025) |
| F1–F5 | D14 here; M1's "universal Lipschitz test bounds" for discrete measures (`Polynomial-Jackson-Moments.md` §4); any Krylov-Sharpness statement about spectral distributions |
| X2 | D12; any spectral-projector argument (eigenvalue counts, `spectralTangentSq` style) |
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
| `NLAlib/Estimation/Trace/GirardHutchinson.lean` | addition | G1 `girardHutchinson_smul` | +10 |
| `NLAlib/Estimation/Trace/StochasticLanczosQuadrature.lean` | new | `slq`, T0, T2, T3, T4, T5, T6, T7 (phase C: C2) | 320 (+70) |
| `NLAlib/Estimation/Spectral/SpectralDensity.lean` | new | `probeSpectralMeasure`, `slqMeasure`, I1–I4, D1–D11, D22, D14, D20, D21, D15, D12, D13, D16, D17, D19, D18; phase B-sphere E1–E4 | 760 (+180) |
| `NLAlib/Probability/Measurability/Krylov.lean` | addition, phase C | C1 `Matrix.IsHermitian.measurable_lanczosFA` | +70 |

Placement of each addition outside the new Estimation files:

| Addition | Home | Reason |
|---|---|---|
| F1, F2 (Abel summation against a Lipschitz function) | `ForMathlib/Topology/MetricSpace/Lipschitz.lean` | scalar real-analysis fact, no NLAlib vocabulary (P9); Mathlib's `LipschitzOnWith` file |
| F3–F5 (finite-support integrals; the CDF bound) | `ForMathlib/MeasureTheory/Integral/Bochner/SumMeasure.lean` | measure theory with no NLAlib vocabulary (P4, P8); beside Mathlib's `setIntegral_finset`. Alternative home `Polynomial/Orthogonal/Moments.lean` next to M0, Q10 |
| X1, X2, X3 | `Matrix/Spectral/SpectralMeasure.lean` | about the spectral measure, the spectral projector $\mathbf 1_S(\mathbf A)$ (whose quadratic form *is* the measure) and the empirical measure |
| G1 | `Estimation/Trace/GirardHutchinson.lean` | linearity of the estimator it is about |
| C1 | `Probability/Measurability/Krylov.lean` | beside `measurable_krylovMatrix` (D12 of PORT_KRYLOV) |

Density file in `Estimation/Spectral/` (beside `RandomStart.lean`: spectral quantities estimated
from random probes), trace file in `Estimation/Trace/` (beside `GirardHutchinson.lean`,
`HutchPlusPlus.lean`). The density file imports the trace file (D2 uses `slq`). Both import
KS7's `Polynomial/Orthogonal/Gauss.lean` and `Krylov/Functions/Quadrature.lean`; phase B-sphere
also imports the `Probability-Beta` files (β3 in `RandomMatrix/Haar/Sphere.lean`, β4 in
`Probability/Distributions/`; homes to be fixed by that stage's note). Imports are
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
    polynomial method"); new key `ChenTrogdonUbaru2025` (decided, Q7a). A different work from the
ICML 2021 paper: cited only for its own results, here the deterministic uniform quadrature
bound (D15) and the SLQ/KPM unification; `ChenTrogdonUbaru2022` is its arXiv v1, kept only for the
existing Appendix C citation.
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

**Wave K (prerequisites, KS7).** SLQ uses the KS7 declarations listed in §12: the definitions
`gaussQuadrature`, `gaussNodes` and the instance #63; #64, #65, #66, #68 (weights form,
integrability, generic Gauss error and its Lipschitz corollary); #40, #42, #43 (exactness,
support, mass); #45 (uniqueness); #54 (the Lanczos identification); #69, #70 (averaging). These
are the items KS7 tags **[SLQ-1]**. Only #65, #69, #70 (KS7 wave 0) and #64 (KS7 wave 1) are
proved early; #40, #42, #43, #45, #54, #66, #68 come in KS7 waves 8–12, after its zeros and
Gauss-rule uniqueness. Their statements are fixed in the KS7 skeleton, so the SLQ proofs use
them, sorried, from SLQ wave 1. "K" in the Deps column marks such a row; its acceptance is final
when the KS7 items it uses are proved (the harness re-runs `#print axioms`). Per row: T0 #54;
T2 #66; T3, D15 #68; D2, I4 #65 (and #64 for finite sums); D5 #43; D8 #42; D9 #40, #69, #70;
D10 #45; D22 #54.

**Wave S (phase B-sphere).** E1–E4 wait for the `Probability-Beta` stage (§3.8: β1–β5, its own
note and proof plan; S1–S4 are its waves plus one).

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
| I1, I2 | `isFiniteMeasure_probeSpectralMeasure`, `isFiniteMeasure_slqMeasure` | SpectralDensity | — | S (2 each) | `unfold; infer_instance` (checked) | 1 |
| I3, I4 | `integrable_probeSpectralMeasure`, `integrable_slqMeasure` | SpectralDensity | K (I4) | S (5–10 each) | `Integrable.smul_measure_nnreal`, `integrable_finset_sum_measure`, `integrable_spectralMeasure`; for I4 KS7 #65 `integrable_gaussQuadrature` | 1 |
| G1 | `girardHutchinson_smul` | GirardHutchinson | — | S (5) | `girardHutchinson`, `Matrix.mul_smul`, `Matrix.smul_mul`, `Matrix.trace_smul`, `smul_eq_mul`, `mul_div_assoc` | 1 |
| T2 | `Matrix.IsHermitian.norm_trace_cfc_sub_slq_le_of_isUniformApproxOn` | Trace SLQ | K | S/M (25–40) | `girardHutchinson_eq_sum`, `slq`; per probe `quadForm (cfc f A) ωⱼ = ∫ f ∂μⱼ` (`integral_spectralMeasure`; the quadratic form of a Hermitian matrix is real), KS7 #66 on `μⱼ` with `ae_mem_Icc_spectralMeasure`, `integrable_spectralMeasure`, mass `Matrix.IsHermitian.spectralMeasure_real_univ`; `norm_sum_le`, `frobNorm_sq_eq_sum_col`, `norm_div`; case `card m = 0` | 1 |
| T0 | `Matrix.IsHermitian.slq_eq_sum_lanczosFA` | Trace SLQ | K | S (20–30) | per probe `← Matrix.IsHermitian.lanczosQuadrature_eq_gaussQuadrature` (KS7 #54), `integral_lanczosQuadrature`; `star b ⬝ᵥ lanczosFA A f b q` is real: frame form `HasOrthonormalCols.lanczosFA_eq`, a quadratic form of the Hermitian `cfc f (Qᴴ A Q)` (`cfc_predicate`); `RCLike.ofReal_re`-type rewrite | 1 |
| D22 | `Matrix.IsHermitian.slqMeasure_eq_sum_lanczosQuadrature` | SpectralDensity | K | S (3–5) | `slqMeasure`, `Finset.sum_congr` with KS7 #54 | 1 |
| D1 | `integral_probeSpectralMeasure` | SpectralDensity | — | S (15–25) | `integral_smul_nnreal_measure`, `integral_finsetSum_measure` (`integrable_spectralMeasure`), `integral_spectralMeasure`, `girardHutchinson_eq_sum`, `map_sum`, `RCLike.re` of a real division (`RCLike.div_re_ofReal`/`map_div₀` route), `NNReal.coe_inv` | 1 |
| D2 | `integral_slqMeasure` | SpectralDensity | I4, K | S (10–20) | `integral_smul_nnreal_measure`, `integral_finsetSum_measure` (KS7 #65), `slq`, `RCLike.ofReal_re`, `map_div₀` | 1 |
| D4 | `Matrix.IsHermitian.probeSpectralMeasure_real_univ` | SpectralDensity | — | S (10–20) | `measureReal_def`, `Measure.smul_apply`, `Matrix.IsHermitian.spectralMeasure_real_univ`, `frobNorm_sq_eq_sum_col`, `ENNReal.toReal_sum` | 1 |
| D5 | `Matrix.IsHermitian.slqMeasure_real_univ` | SpectralDensity | K | S (10–20) | as D4 with KS7 #43 `gaussQuadrature_real_univ` (q > 0) and `Matrix.IsHermitian.spectralMeasure_real_univ` | 1 |
| D6 | `ae_mem_spectrum_probeSpectralMeasure` | SpectralDensity | — | S (10–15) | `ae_iff`, `Measure.smul_apply`, `Measure.coe_finsetSum`, `spectralMeasure_compl_spectrum_eq_zero` | 1 |
| D8 | `Matrix.IsHermitian.ae_mem_Icc_slqMeasure` | SpectralDensity | K | S (10–15) | as D6 with KS7 #42 `ae_mem_Icc_gaussQuadrature` and `ae_mem_Icc_spectralMeasure` | 1 |
| F2 | `Finset.abs_sum_mul_le_of_lipschitzOnWith` | ForMathlib Lipschitz | F1 | S (15–25) | F1 at `t := b`; `|∑ d| ≤ K` from `hK` at `s.max'` (`Finset.filter_true_of_mem`, `Finset.le_max'`), empty case; `abs_mul` | 2 |
| D3 | `probeSpectralMeasure_real` | SpectralDensity | X1 | S (15–25) | `measureReal_def`, `Measure.smul_apply`, `Measure.coe_finsetSum`, X1 per probe (`ENNReal.toReal_sum` with finiteness), `girardHutchinson_eq_sum` | 2 |
| D7 | `ae_mem_Icc_probeSpectralMeasure` | SpectralDensity | D6 | S (3–5) | `filter_upwards [D6]` with `hs` | 2 |
| D9 | `Matrix.IsHermitian.matchesMoments_probeSpectralMeasure_slqMeasure` | SpectralDensity | K | S (15–25) | an interval containing the finite spectrum; per probe KS7 #40; KS7 #70 `MatchesMoments.finsetSum` (supports: `ae_mem_Icc_spectralMeasure`, #42) and #69 `MatchesMoments.smul` | 1 |
| D10 | `Matrix.IsHermitian.slqMeasure_eq_probeSpectralMeasure_of_card_le` | SpectralDensity | K | S (10–15) | per probe KS7 #45 `MatchesMoments.eq_gaussQuadrature` with `MatchesMoments.refl`, `s := A.finite_real_spectrum.toFinset` (`spectralMeasure_compl_spectrum_eq_zero`), card ≤ card n ≤ q (`Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues`) | 1 |
| D11 | `integral_integral_probeSpectralMeasure` | SpectralDensity | D1 | S (15–25) | D1, `integral_div`, `integral_re` (integrability: `IsIsotropic.integrable_quadForm` summed), `integral_girardHutchinson`, `Matrix.IsHermitian.integral_empiricalSpectralMeasure` | 2 |
| T3 | `…norm_trace_cfc_sub_slq_le_of_lipschitzOnWith` | Trace SLQ | K | S (15–25) | the proof of T2 with KS7 #68 (Lipschitz Gauss error, $k + 1 = q + 1$ nodes) per probe in place of #66; `integrable_spectralMeasure`; arithmetic | 2 |
| T4 | `…norm_trace_cfc_sub_slq_le_of_differentiableOn` | Trace SLQ | T2 | S (12–20) | `exists_degree_le_isUniformApproxOn_Icc_of_differentiableOn` at `N := 2 * q + 1` (the Bernstein corollary KS7 leaves to SLQ), then T2 | 2 |
| T5 | `measureReal_abs_trace_cfc_sub_slq_ge_le_of_isUniformApproxOn` | Trace SLQ | T2 | S (15–25) | `measureReal_mono` (finite measure: `hind.isProbabilityMeasure`) into the event of `measureReal_abs_trace_sub_girardHutchinson_ge_le` with `B := cfc f A`; T2 over ℝ (`Real.norm_eq_abs`); `linarith` | 2 |
| F5 | `MeasureTheory.abs_integral_sub_integral_le_of_lipschitzOnWith` | ForMathlib SumMeasure | F2, F3, F4 | S/M (25–35) | F3 for μ and ν, `← Finset.sum_sub_distrib`, `mul_sub`; F2 with `d y := μ.real {y} - ν.real {y}`; F4 and `Finset.sum_sub_distrib` to turn `hK` into the partial-sum hypothesis | 3 |
| T6 | `measureReal_abs_trace_cfc_sub_slq_ge_le_of_lipschitzOnWith` | Trace SLQ | T3 (or T5) | S (15–20) | as T5 with T3 in place of T2 | 3 |
| T7 | `measureReal_abs_trace_cfc_sub_slq_ge_le_of_differentiableOn` | Trace SLQ | T4 | S (15–20) | as T5 with T4 | 3 |
| D12 | `measureReal_abs_empiricalSpectralMeasure_real_sub_probeSpectralMeasure_real_ge_le` | SpectralDensity | D3, X2, X3, G1 | M (45–70; split off a private helper "the exponent decreases when $\|\mathbf B\|_{\mathsf F}^2 \le 1/n$, $\|\mathbf B\|_2 \le 1/n$", 20–30, if longer) | event rewrite: D3, X3 over ℝ (`RCLike.re_to_real`), `B := (1/n) • cfc 1_S A`, `girardHutchinson` linear by G1, `Matrix.trace_smul`; `measureReal_abs_trace_sub_girardHutchinson_ge_le` at `B`; X2 with `IsStarProjection.frobNorm_sq_eq_rank`, `Matrix.rank_le_card_width`, `IsStarProjection.specNorm_le_one`, `frobNorm_smul`, `specNorm_smul`; monotonicity `Real.exp_le_exp`, `min_le_min`, `div_le_div_of_nonneg_left`; cases `B = 0`, `c = 0`, `n` empty | 3 |
| D15 | `…abs_integral_probeSpectralMeasure_sub_integral_slqMeasure_le_of_lipschitzOnWith` | SpectralDensity | D4, K | S (20–30) | `integral_smul_nnreal_measure`, `integral_finsetSum_measure` (I3, I4), `← Finset.sum_sub_distrib`, `Finset.abs_sum_le_sum_abs`; per probe KS7 #68 with `ae_mem_Icc_spectralMeasure`; masses sum to `frobNorm Ω ^ 2` (D4's lemma) | 3 |
| D13 | `measureReal_exists_abs_empiricalSpectralMeasure_real_sub_probeSpectralMeasure_real_gt_le` | SpectralDensity | D12 | S/M (25–40) | rewrite the event as `⋃ x ∈ A.finite_real_spectrum.toFinset, {τ ≤ |…|}` (`Set.Finite.mem_toFinset`, `le_of_lt`), `measureReal_mono`, `measureReal_biUnion_finset_le`, D12 per point, `Finset.sum_le_card_nsmul`; private helper: card of the spectrum ≤ `card n` (`Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues`, `Set.ncard_range_le` / `Finset.card_image_le`), 10–15 | 4 |
| D14 | `…abs_integral_empiricalSpectralMeasure_sub_integral_probeSpectralMeasure_le` | SpectralDensity | F5, D6 | S (15–25) | F5 with `s := A.finite_real_spectrum.toFinset`; supports: `hA.ae_mem_spectrum_empiricalSpectralMeasure`, D6; `hs` | 4 |
| D20 | `Matrix.IsHermitian.abs_one_sub_probeSpectralMeasure_real_univ_le` | SpectralDensity | D4, D6, X3 | S (15–25) | $x^\ast$ the largest eigenvalue (`hA.spectrum_real_eq_range_eigenvalues`, `Set.Finite.exists_maximal`/`Finset.max'` of the finite spectrum); `(empiricalSpectralMeasure A).real (Iic x*) = 1` (`hA.ae_mem_spectrum_empiricalSpectralMeasure`, `measureReal_univ_eq_one`); the probe CDF at $x^\ast$ is its mass (D6, `measureReal_congr`), so `hK x*` | 4 |
| D21 | `Matrix.IsHermitian.abs_empiricalSpectralMeasure_real_Iic_sub_probeSpectralMeasure_real_Iic_le` | SpectralDensity | F4, D6 | S (20–30) | `s := A.finite_real_spectrum.toFinset`; if no eigenvalue is $\le x$ both CDFs are $0$ (F4: empty filter) and `hτ`; else $x' = $ the largest eigenvalue $\le x$ (`Finset.max'` of the filter) and F4 gives equal CDFs at $x$ and $x'$ (`Finset.filter_congr`) | 4 |
| D16 | `measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_probeSpectralMeasure_gt_le` | SpectralDensity | D13, D14 | S (15–25) | `measureReal_mono` into D13's event: on its complement (`not_lt`, `push_neg`) D14 gives `≤`, contradiction with `<` | 5 |
| D17 | `measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_slqMeasure_gt_le` | SpectralDensity | D13, D14, D15, D20 | S/M (25–35) | as D16, plus D15, D20 (mass $\le 1 + \tau$; empty $n$: both integrals $0$, `isEmpty_or_nonempty`) and `abs_sub_le` (triangle through the probe measure) | 5 |
| D19 | `measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_smul_slqMeasure_gt_le` | SpectralDensity | D13, D20, F5, D9, D15's ingredients | S/M (30–45) | on D13's complement: D20 gives $M > 0$; `integral_smul_measure`; normalised CDF bound $2\tau$ (§3.5); F5 on $f - f(b)$ (`LipschitzOnWith.sub_const`); M0 on the normalised measures (`MatchesMoments` scales: D9 and `integral_smul_measure`); Jackson degree $2q+1$ | 5 |
| D18 | `exists_forall_…_slqMeasure_gt_le` | SpectralDensity | D17 | M (40–60) | `C := 196`; D17; `HasSubgaussianMGF.integral_sq_le` with `hvar` at some `(i, j)` (`hind.isProbabilityMeasure`), so `1 ≤ c`; `min_eq_left` from `τ ≤ 1 ≤ c`; `le_hansonWrightConstant`; `Real.exp_log`, `Real.exp_le_exp`, `Real.log_le_log`; cases `n`, `m` empty | 6 |
| E1 | sphere probes, one threshold (§3.8) | SpectralDensity | D3, X2, X3, β3, β4, β5 | M (50–70) | event as a centred average of $\mathbf u_j^{\mathsf T}\mathbf P\mathbf u_j$ ($\|\sqrt n\,\mathbf u\|^2 = n$ a.s., `uniformSphereVector` lives on the sphere); rank $0$ or $n$: deterministic; else β3 (frame of $\mathbf P$, `IsStarProjection` → `HasOrthonormalCols` via `rangeProjector`), β4 with $\alpha+\beta = n/2$, β5 | S1 |
| E2 | sphere Kolmogorov union | SpectralDensity | E1 | S (20–30) | as D13 | S2 |
| E3 | `…_slqMeasure_gt_le_of_hasLaw_uniformSphereVector` | SpectralDensity | E2, D14, D15, D20 | M (35–50) | mass exactly $1$ a.s. (D4 with $\|\sqrt n\,\mathbf u_j\|^2 = n$), so F5 on $f - f(b)$ removes $\lvert f(b)\rvert$; D15 with mass $1$; `measureReal_mono` into E2's event (an a.e. superset: `measureReal_mono_ae`) | S3 |
| E4 | sphere sample size and its `exists_forall_` form | SpectralDensity | E3 | M (30–45) | `Real.exp_log`; $m(n+2)\tau^2 \ge \log(2n/\delta)$; empty-type cases | S4 |
| C1 | `Matrix.IsHermitian.measurable_lanczosFA` (phase C) | Probability Measurability Krylov | — | L (80+, review comment 5; split: (a) `lanczosFA` through a continuous extension, `lanczosFA_congr` with `f ∘ Set.projIcc a a' h`; (b) measurability of $\mathbf b \mapsto \mathbf P\,g(\mathbf P\mathbf A\mathbf P)\mathbf P\mathbf b$) | `Matrix.IsHermitian.lanczosFA_congr`, `continuous_projIcc`, `lanczosFA`, `compressedCfc`, `measurable_rangeProjector`, `measurable_krylovMatrix`, `continuousOn_cfc`, `ContinuousOn.comp_measurable`-type step into the closed set of self-adjoint matrices with spectrum in a compact set; under `open scoped Matrix.Norms.L2Operator` | C |
| C2 | `…norm_trace_cfc_sub_integral_slq_le_of_isUniformApproxOn` (phase C) | Trace SLQ | C1, T2 | M (40–60) | C1 per column, `Integrable.mono` with the bound of T2, `integral_girardHutchinson`, `integral_sub`, `norm_integral_le_integral_norm`, `integral_mono`, `IsIsotropic.integral_norm_sq`, `frobNorm_sq_eq_sum_col` | C |

Difficulty count, phases A and B (42 dispatched rows counting I1–I4 separately; the 3
definitions are in the skeleton; X4 and T8 dropped, T0 and D22 added): S 33 (including the rename
X1; D15 and D9 are now S), S/M 5 (T2, F5, D13, D17, D19), M 3 (F1, D12 with its optional
helper, D18), L 0; counting each S/M row as M (all exceed 30 lines at the upper estimate): S 34,
M 8, the figure in §0. Phase B-sphere: E2 S, E1, E3, E4 M; its prerequisite stage 12 steps (§3.8). Phase C: M 1, L 1. No
phase A/B proof is expected to exceed 70 lines; S4's 80-line limit is the split trigger for D12,
and C1 is planned as two named steps.

Statement-shape flags: items 1–4 of the reviewed draft (the "∃ f" event, the $\lvert f(b)\rvert$
term, the random term in T5–T7, `slq` in `𝕜`) were decided on 2026-10-24 (Q8, Q4, Q9, Q2b). Still
open for review, not for the maintainer: the definition of `slq` through an integral against
`gaussQuadrature` (T0 gives the algorithmic form; a user who wants the Lanczos-FA spelling rewrites
with it), and the sphere statements' test matrix `√(card n) • U ω` (a user with unit probes and the
$1/m$ convention rescales by `spectralMeasure_smul`).

## 10. Open questions for the maintainer

All twelve questions of the reviewed draft were decided on 2026-10-24 (Q11, dispatch rules, had
already been removed). The decisions and where they are folded in:

* **Q1 (a), decided 2026-10-24.** Normalisation $1/(nm)$ (§1.2).
* **Q2a (a), decided 2026-10-24.** Name `probeSpectralMeasure` (with `slq`, `slqMeasure`).
* **Q2b (a), decided 2026-10-24.** `slq` valued in `𝕜` (§1.1; now an `ofReal` by definition).
* **Q3 (b), decided 2026-10-24, against the draft's recommendation.** Sphere probes with the
  sharp Beta constant: phase B-sphere (§3.8), on a prerequisite Probability stage. The
  sub-Gaussian-entry tails are kept as well (Q3′ below).
* **Q4 (a + c), decided 2026-10-24.** The $\lvert f(b)\rvert$ form (D17) and the ratio estimator
  (D19).
* **Q5 (a), decided 2026-10-24.** Hanson–Wright's $1/196$, inline tail expressions, $n$ not the
  per-threshold rank.
* **Q6 (a), decided 2026-10-24.** Phases A and B now (with B-sphere when its prerequisite exists),
  C later; the asymptotic form D18 included.
* **Q7a (a), decided 2026-10-24.** New key `ChenTrogdonUbaru2025` for the SISC paper. "There are two
  papers that are kind of different": `ChenTrogdonUbaru2021` (ICML) is cited for the random part
  (the CDF/union-bound Wasserstein bound and the dimension-helps rate: D13, D16–D19, E1–E4);
  `ChenTrogdonUbaru2025` (SISC) for its own uniform quadrature bound (D15) and the SLQ/KPM
  unification; `ChenTrogdonUbaru2022` is the arXiv v1 of the SISC work, kept only where the
  library already cites it (Appendix C, Theorem 38).
* **Q7b (b), decided 2026-10-24.** Bib fields and theorem numbers stay "to check".
* **Q8 (a), decided 2026-10-24.** One event, uniform over $L$-Lipschitz $f$, $L$ fixed.
* **Q9 (a), decided 2026-10-24.** Random quadrature term in the trace tails T5–T7; the density
  tails are deterministic (review comment 1).
* **Q10 (a), decided 2026-10-24.** F1–F5 in ForMathlib.

Remaining questions (one line each, with a recommendation):

* **Q3′, decided 2026-10-24: keep.** The sub-Gaussian-entry density tails (D12–D19) stay beside
  the sphere ones (E1–E4). They come almost free from the Girard–Hutchinson tail and cover Gaussian
  and sign probes.
* **Q3″, decided 2026-10-24: Marchal–Arbel 2017.** `Probability-Beta` follows Marchal–Arbel 2017
  ("On the sub-Gaussianity of the Beta and Dirichlet distributions") for the Beta proxy
  $1/(4(\alpha+\beta+1))$. Its proof is the one research-risk item (§3.8, β4c).
* **Q12, decided 2026-10-24: later.** Haar-frame probes (orthonormal, dependent columns) get tails
  later (negative association of the per-column Beta variables); no consumer named.

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

## 12. Relation to KS7: what SLQ uses

The maintainer's direction reverses the draft's "SLQ needs no KS7 result". SLQ is now built on
KS7's Gauss-rule core (`Polynomial-OrthogonalStructure.md`, "Interface for SLQ"; the items
marked **[SLQ-1]** there). The KS7 declarations this stage uses, with the SLQ rows that use them:

| KS7 # | Declaration | Used by |
|---|---|---|
| §2, #63 | `gaussQuadrature`, `gaussNodes`, `isFiniteMeasure_gaussQuadrature` | the definitions `slq`, `slqMeasure`; I2 |
| #65 | `integrable_gaussQuadrature` | I4, D2, T2 |
| #64 | `integral_gaussQuadrature_eq_sum` | D2 (finite-sum integrals), E3 |
| #66 | `abs_integral_sub_integral_gaussQuadrature_le_of_isUniformApproxOn` | T2 (per probe), T4 (with the Bernstein approximant) |
| #68 | `abs_integral_sub_integral_gaussQuadrature_le_of_lipschitzOnWith` | T3, D15, E3 (per probe) |
| #40 | `matchesMoments_gaussQuadrature` | D9 |
| #42 | `ae_mem_Icc_gaussQuadrature` | D8 |
| #43 | `gaussQuadrature_real_univ` | D5 |
| #45 | `MatchesMoments.eq_gaussQuadrature` | D10 |
| #54 | `Matrix.IsHermitian.lanczosQuadrature_eq_gaussQuadrature` | T0, D22 (the only place Lanczos enters) |
| #69, #70 | `MatchesMoments.smul`, `MatchesMoments.finsetSum` | D9 (averaging) |

Not used: #67 `spectralMeasure_map_jacobiMatrix` (Golub–Welsch over `𝕜`; a user's implementation
statement can compose it with D22). The remark of the KS7 interface (the average of Gauss rules is
not the Gauss rule of the average, $G_1(\tfrac12\delta_0 + \tfrac12\delta_1) = \delta_{1/2}$) is
the reason every SLQ bound here is a per-probe Gauss bound averaged plus a probe-averaging error,
and it is repeated in the `slqMeasure` docstring.

Scheduling: KS7 proves #65, #69, #70 in its wave 0, #64 in wave 1, and #40, #42, #43, #45, #54,
#66, #68 only in its waves 8–12 (they need its zeros and the uniqueness of the Gauss rule). Their
statements are fixed in the KS7 skeleton, so the SLQ proofs use them sorried from SLQ wave 1;
acceptance of an SLQ row that depends on a sorried KS7 item is final only when that item is proved
(the harness re-checks axioms at the end). SLQ's skeleton therefore imports the KS7 skeleton.
