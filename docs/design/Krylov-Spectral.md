# Design note: the spectral side of Krylov methods

**Approved by the maintainer, 2026-10-22:** SD1 to SD7 as recommended, with SD4 naming the rule `interpolatoryQuadrature`. On SD3 the maintainer asked whether the support hypothesis `∀ᵐ x ∂μ, x ∈ Set.Icc a b` admits discrete measures; it does (it says only that μ puts no mass outside [a, b]), so finitely supported measures such as spectral measures and quadrature rules qualify.

Spectral measures, moment matching and Gauss quadrature, Lanczos quadrature, rates for
Lanczos-FA, Ritz-value and power-method bounds, and random starts.

Draft of 2026-10-21, for review before any skeleton or proof. Written read-only against
`~/Documents/NLA-lib/nlalib-block` (branch `cleanup/consolidation`) and the quarry's
`atlas/declarations.json`. No Lean was run: none of the signatures below has been elaborated. The
skeleton stage must elaborate them, and every signature here is provisional until it does.

The note covers six stages, KS1 to KS6, plus a deferred KS7. It is one file because the stages
share three objects: the spectral measure, the moment-matching predicate and the
spectral-tangent quantity. If the maintainer prefers, it splits cleanly at approval into four
stage notes: `Matrix-SpectralMeasure.md` (KS1, KS2), `Krylov-Quadrature.md` (KS3, KS4),
`Krylov-Eigenvalues.md` (KS5) and `Estimation-RandomStart.md` (KS6).

## 0. Summary and main findings

The library has the Krylov solvers, Lanczos-FA and its uniform bound, and the Lanczos recurrence.
It has no spectral measure, no quadrature statement, no Ritz-value bound and no consumer of
`GaussianLogOverlap.lean`. I verified every claim of the gap survey that this note relies on
against the tree (§1). The findings that shape the design:

1. **Lanczos quadrature needs no orthogonal-polynomial theory.** Exactness through degree
   $2q - 1$ and the $2\varepsilon\|\mathbf{b}\|^2$ error both follow from the existing
   compression lemmas (`Krylov/Basic/Compression.lean`) and the frame form of `lanczosFA`. The
   C6 checkpoint of `Krylov-Functions.md` was designed and approved that way and can run first,
   unchanged. Orthogonal polynomials explain the rule (its nodes are the zeros of the degree-$q$
   orthogonal polynomial of $\mu_{\mathbf{A},\mathbf{b}}$). They are not a prerequisite for any
   consumer listed in the brief.
2. **The Lanczos rule is a spectral measure.** The Gauss rule of $q$ Lanczos steps is the
   spectral measure of the compressed pair $(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q},
   \mathbf{Q}^{\mathsf{H}}\mathbf{b})$. Written basis-free through `rangeProjector`, it is the
   spectral measure of $(\mathbf{P}\mathbf{A}\mathbf{P}, \mathbf{P}\mathbf{b})$. Its integral of
   $f$ is $\operatorname{Re}\,\mathbf{b}^{\mathsf{H}}\mathsf{lanczosFA}(\mathbf{A}, f,
   \mathbf{b}, q)$, which is also $\|\mathbf{b}\|^2\operatorname{Re} f(\mathbf{T})_{00}$.
   Golub–Welsch (nodes are the Ritz values, weights are the squared first eigenvector entries) is
   then the eigenbasis bridge of the spectral measure applied to $\mathbf{T}$. It needs no theorem
   of its own.
3. **One identity carries every eigenvalue bound.** Kaniel–Paige–Saad, the gap-free Ritz
   bound, the power method, inverse iteration and the Kuczyński–Woźniakowski deterministic steps
   all bound the Rayleigh quotient of a filtered vector $g(\mathbf{A})\mathbf{b}$, which is a
   ratio of integrals against $\mu_{\mathbf{A},\mathbf{b}}$. The gapped bounds (KPS, power,
   inverse) are instances of one filter theorem. The gap-free and Kuczyński–Woźniakowski bounds
   use the same identity but need their own split of the integral; they are not instances of the
   filter theorem. The mass of
   $\mu_{\mathbf{A},\mathbf{b}}$ at an eigenvalue replaces the eigenvector hypotheses of the
   prototype, handles repeated eigenvalues with no extra work, and removes the "almost-sure grade"
   that PORT_KRYLOV K5 planned: the random-start bounds need only
   $\mu_{\mathbf{A},\mathbf{g}}(\{\lambda_0\}) > 0$, which holds almost surely.
4. **Both Chebyshev amplifiers already exist.** The gapped amplifier (KPS) and the gap-free one
   (Musco–Musco) are the existing `chebyshevResidual` reflected about $\lambda_0$, on
   $[\lambda_0 - c, \lambda_0 - a]$ and on $[\varepsilon\lambda_0, \lambda_0]$. The rates come
   from `isUniformApproxOn_chebyshevResidual_two_mul_pow` and from the ForMathlib lemma
   `exp_mul_sqrt_div_two_le_eval_T_real`, which gives the gap-free factor
   $4e^{-4q\sqrt{\varepsilon}}$. That factor is tighter than the prototype's
   $4(1 + \sqrt{2\varepsilon/(1-\varepsilon)})^{-2q}$ in the small-$\varepsilon$ regime; the
   prototype's factor wins as $\varepsilon \to 1$. So Poly8's planned `chebyshevAmplifier` has no consumer here.
   Only the even second-kind filter (Kuczyński–Woźniakowski's Lanczos bound, KS6) is new
   Polynomial material.
5. **Gaps in the lower layers.** The lower layers lack one small thing: Jackson on an interval
   $[a, b]$ (one corollary of the existing $[-1, 1]$ theorem, added in KS4). They also lack things
   this note records and does not schedule: the exponential approximant (P4), the Hermite
   interpolation remainder (Gauss–Radau and the sign of the Gauss error), and the noisy-moment
   bound J1 that KPM needs (§8). Positivity of the Lanczos weights below the grade needs no
   tridiagonal theory (KS3c).
6. **What Mathlib has.** I searched, at the pinned commit `0df444a`. Mathlib has Chebyshev
   orthogonality for `Polynomial.Chebyshev.measureT` and Chebyshev–Gauss quadrature
   (`Polynomial.Chebyshev.integral_eq_sumZeroes`, `ChebyshevGauss.lean`), Lagrange
   interpolation (`Lagrange.basis`, `Lagrange.nodal`, `Lagrange.interpolate`), and integrals of
   finite sums of Dirac measures (`integral_finsetSum_measure`, `integral_dirac`,
   `integrable_dirac`). Searched, none: general orthogonal polynomials, a three-term recurrence,
   Christoffel–Darboux, a general Gauss rule, a spectral measure of a matrix, an empirical
   spectral measure. Mathlib's `jacobiMatrix` is the Jacobian of an algebra presentation
   (`Algebra.PreSubmersivePresentation.jacobiMatrix`), not a tridiagonal matrix. `Hermite` and
   `ShiftedLegendre` carry no orthogonality theorems.

**Small enough to run first.** These need no new vocabulary.
(i) KS3a, C6 as approved: two theorems in `Krylov/Functions/Quadrature.lean`.
(ii) KS4's analytic corollaries: two theorems.
(iii) KS4's Jackson corollaries: one Polynomial lemma and two theorems.
Then come KS1 (the spectral measure) and KS2a (moment matching). The rest follows in dependency
order (§6).

## Decisions for the maintainer

These are the choices that later theorems would be built on, or that fix a carrier or a name.
Everything after this section proceeds as recommended unless the maintainer says otherwise.

**SD1. The spectral measure and the empirical spectral measure: carrier, normalisation, repeated
eigenvalues.**

- Options for $\mu_{\mathbf{A},\mathbf{b}}$:
  - (a) A Mathlib `Measure ℝ`, written as a finite sum of Dirac masses over the distinct
    eigenvalues. The weight at $x$ is $\operatorname{Re}\,\mathbf{b}^{\mathsf{H}}
    \mathbf{P}_x\mathbf{b} = \|\mathbf{P}_x\mathbf{b}\|^2$, with
    $\mathbf{P}_x = $ `cfc (fun t => if t = x then 1 else 0) A` the spectral projector, so the
    definition is basis-free. The mass is $\|\mathbf{b}\|^2$ (unnormalised). The definition is
    total, `spectralMeasure A b`, and gives $0$ for non-Hermitian $\mathbf{A}$ (Mathlib's
    `cfc` junk value). A repeated eigenvalue is one atom carrying the whole eigenspace's weight.
  - (b) The same carrier, defined through Mathlib's `eigenvectorUnitary` as
    $\sum_i |(\mathbf{U}^{\mathsf{H}}\mathbf{b})_i|^2\delta_{\lambda_i}$ (a `dite` on
    `IsHermitian`). Repeated eigenvalues give repeated atoms, and the measure is basis-free only
    through a lemma.
  - (c) The prototype's proof-carrying `spectralMeasure hA v`, over ℝ.
  - (d) A probability measure for $\mathbf{b}/\|\mathbf{b}\|$. This breaks the quadratic scaling
    in $\mathbf{b}$ and needs a junk value at $\mathbf{b} = \mathbf{0}$. The Jackson/moments note
    §4 already asks for the finite-mass version for vector measures.
  - (e) A discrete structure (`PMF`, or weights in `ℝ →₀ ℝ`). `PMF` exists in Mathlib only for
    probability measures. The planned consumers (moment matching M1, Lipschitz test bounds, a
    later Wasserstein distance) are stated on `Measure ℝ`.
- Options for the empirical spectral measure:
  - (a) $\lvert n\rvert^{-1}\sum_{k < \lvert n\rvert}\delta_{\lambda_k(\mathbf{A})}$ through the
    library's `eigenvalue`, called `empiricalSpectralMeasure A`. It is a probability measure for
    nonempty $n$, the zero measure for empty $n$, and $\delta_0$ for non-Hermitian $\mathbf{A}$.
    Multiplicities are counted.
  - (b) $\lvert n\rvert^{-1}\sum_i\mu_{\mathbf{A},\mathbf{e}_i}$, with junk $0$ off Hermitian.
  - (c) The unnormalised counting measure.
- Recommendation: **(a) for both.** The characterising lemmas make the choice inside the
  definition irrelevant to users: $\int f\,d\mu = \operatorname{Re}\,\mathbf{b}^{\mathsf{H}}
  f(\mathbf{A})\mathbf{b}$ for every $f$, with no continuity needed because the measure is atomic.
  The definition of (a) still says what the object is. The eigenvector form of (b) is a bridge
  theorem, `HasOrthonormalCols.spectralMeasure_eq_sum`. The two measures are linked by
  $\sum_i\mu_{\mathbf{A},\mathbf{e}_i} = \lvert n\rvert\cdot\mathrm{ESD}$.
- Home: `Matrix/Spectral/SpectralMeasure.lean`, as the Jackson/moments note §4 placed it. Names
  follow the library's argument order (matrix, then vector).

**SD2. Moment matching: one predicate, strict degree, in Polynomial.**

- Options:
  - (a) `MatchesMoments μ ν N := ∀ p : ℝ[X], p.degree < N → ∫ p dμ = ∫ p dν`, read "the first
    $N$ moments agree". This is strict, like Mathlib's `degreeLT` and Chebyshev–Gauss
    (`P.degree < 2 * n`) and the library's Lanczos-FA exactness (`p.degree < q`). An $n$-node
    Gauss rule matches $2n$ moments, and $q$ Lanczos steps match $2q$. At $n = 0$ the statement is
    vacuous and true, so the natural-subtraction trap of the inclusive form (Jackson/moments note
    §4) never arises.
  - (b) The Jackson note's proposal, `MatchesPolynomialIntegralsUpTo μ ν N` with
    `p.degree ≤ N`. Gauss then needs `n > 0` and budget `2 * n - 1`, or the shift `2 * q + 1`
    at `q + 1` steps.
  - (c) No predicate: write `∀ p, p.degree < N → …` in each statement. That breaks CONTRIBUTING
    §1 rule 2 by the third use.
- Home: the Jackson note put moment comparison in a future `Probability/Moments`. Krylov
  (layer 1) imports only Matrix, Polynomial and ForMathlib (PORT_KRYLOV D12), and Lanczos
  quadrature must conclude the predicate. So the predicate and the transfer bound M0 go in
  `Polynomial/Orthogonal/Moments.lean`. That is allowed by P11, uses only Mathlib vocabulary and
  is upstreamable. The later M1 (exact and noisy spectral-distribution bounds) stays in
  Probability and uses it.
- Recommendation: **(a), in Polynomial, namespace `NLAlib`** (rule F4; P9 does not apply while
  P11 holds).

**SD3. The hypothesis shape for measures in the Polynomial layer.**

- Options:
  - (a) `[IsFiniteMeasure μ]` together with `(hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b)` (compact support),
    as the Jackson note's M0 proposal has it. Spectral measures get it from
    `spectrum ℝ A ⊆ Set.Icc a b` through one lemma.
  - (b) `μ (Set.Icc a b)ᶜ = 0`.
  - (c) Integrability of every polynomial, `∀ k, Integrable (fun x => x ^ k) μ`. This is more
    general (Gauss–Hermite, Laguerre) but is a raw condition that would need its own interface.
  - (d) A new named interface for "finite measure supported in $[a, b]$".
- Recommendation: **(a) everywhere this round.** Every consumer here is compactly supported
  (spectral measures, Lanczos rules, `measureT`), and (a) is Mathlib's idiom. A Gauss theorem
  under (c) can be added later without renaming: its (a) form is then a corollary.

**SD4. The orthogonal-polynomial interface and the Gauss rule.**

- Options:
  - (a) A lower-degree orthogonality predicate
    `IsOrthogonalPolynomial μ k p := ∀ r, r.degree < k → ∫ p r dμ = 0`, with monicity and degree
    kept as separate hypotheses, as the Jackson note OP0 recommends. The quadrature rule is a
    measure built from nodes `s : Finset ℝ` with weights $\int\ell_x\,d\mu$ (Mathlib's
    `Lagrange.basis s id x`). Gauss exactness is stated under
    `IsOrthogonalPolynomial μ s.card (Lagrange.nodal s id)`.
    Name of the rule: (a1) `interpolatoryQuadrature μ s`, the reviewer's proposal: the
    definition is the interpolatory rule at any nodes, and "Gauss" is the theorem about it at
    the zeros of the orthogonal polynomial; (a2) `gaussQuadrature μ s`, the name of its main
    use, which misdescribes it at other nodes.
  - (b) An orthogonal-polynomial-sequence structure, a family $P_k$ with $\deg P_k = k$ that is
    pairwise orthogonal.
  - (c) A canonical Gram–Schmidt definition `orthogonalPolynomial μ k`.
- Recommendation: **(a) now, named (a1) `interpolatoryQuadrature`** (N11: named for what it
  is; this note uses that name throughout). One caveat goes in its docstring: as a measure it is
  the interpolatory rule only where the weights are nonnegative, which holds at Gauss nodes and
  can fail elsewhere. (c) waits for KS7 and a consumer that needs the canonical
  polynomials, such as the Lanczos polynomials or Christoffel–Darboux. The weights are proved
  nonnegative ($\int\ell_x\,d\mu = \int\ell_x^2\,d\mu$), so `ENNReal.ofReal` in the definition
  loses nothing under the hypothesis. The definition's docstring states its junk value (weights
  truncated at $0$) for nodes that are not Gauss nodes.

**SD5. The Lanczos rule as a named measure.**

- Options:
  - (a) Name it: `lanczosQuadrature A b q := spectralMeasure (P * A * P) (P *ᵥ b)`, with
    `P = rangeProjector (krylovMatrix A b q)`. It is basis-free, and at $q = 0$ it is $0$
    because $\mathbf{P}\mathbf{b} = \mathbf{0}$. Bridges give the frame form, the tridiagonal
    form and the scalar form $\operatorname{Re}\,\mathbf{b}^{\mathsf{H}}\mathsf{lanczosFA}$.
  - (b) No name, as `Krylov-Functions.md` §4 decided ("no new name"). The quadrature is then
    $\mathbf{b}^{\mathsf{H}}\mathsf{lanczosFA}(\mathbf{A}, f, \mathbf{b}, q)$, and the measure is
    written in frame form, `spectralMeasure (Qᴴ * A * Q) (Qᴴ *ᵥ b)`, wherever needed.
- Recommendation: **(a), with C6's scalar theorems kept exactly as approved.** The only change
  to the approved design is that the measure gets a name. The reason is that stochastic Lanczos
  quadrature (SLQ) for spectrum approximation outputs the average of these measures over the
  probes ([ChenTrogdonUbaru2022], locator to check). That consumer, and moment matching against
  $\mu_{\mathbf{A},\mathbf{b}}$, need the measure as one object. Option (b) would make every such
  statement choose a frame.

**SD6. How eigenvalue bounds measure the start vector's overlap.**

- Options:
  - (a) A named quantity, `spectralTangentSq A b c` $:= \mu(\mathbb{R}\setminus\{c\})/\mu(\{c\})$
    with $\mu = \mu_{\mathbf{A},\mathbf{b}}$. This is $\tan^2$ of the angle between $\mathbf{b}$
    and the eigenspace of $c$, with junk value $0$ when $\mu(\{c\}) = 0$. It needs no eigenvector
    hypothesis, and it is correct for a repeated eigenvalue, where the eigenvector form is loose.
  - (b) Write the same ratio out in each statement.
  - (c) The eigenvector form $(\|\mathbf{b}\|^2 - |\mathbf{u}^{\mathsf{H}}\mathbf{b}|^2)/
    |\mathbf{u}^{\mathsf{H}}\mathbf{b}|^2$, written out, under hypotheses `A *ᵥ u = c • u` and a
    unit `u`. This is PORT_KRYLOV §1.11's approved spelling, from before rule N11.
- Recommendation: **(a).** The ratio appears in about eight headline statements (KPS, gap-free,
  two Kuczyński–Woźniakowski steps, two power-method bounds, inverse iteration, the filter
  theorem), and N11 asks for a definition when a formula repeats like that. The eigenvector form
  of (c) is one bridge lemma, `Matrix.IsHermitian.spectralTangentSq_le`. Under (a), the
  §1.11 decision is superseded for vectors against eigenvectors.

**SD7. The random-start constants and where they live.**

- Options:
  - (a) Two named bounds, `randomStartPowerBound N q` and `randomStartLanczosBound N q`, in the
    registry. Their values are the proof's ($(\log 2N + 2)/(2q + 1)$, and
    $4((\log 2N + 2 + \log 2)^2 + 4)/((\log 2)^2q^2)$). Their docstrings give
    Kuczyński–Woźniakowski's printed constants (locators to check) and the gap. The theorems live
    in `Estimation/Spectral/RandomStart.lean`, as PORT_KRYLOV D12 approved.
  - (b) The same formulas written inline. Rule §5.2(2) allows this only for the source's own
    small constants, and these are not the source's.
  - (c) Put the theorems in Probability (layer 1). Probability may import Krylov there, as
    `Probability/Measurability/Krylov.lean` does. This would answer P10's warning that a layer-4
    file uses only layer-1 vocabulary.
- Recommendation: **(a)**. The topic is randomized eigenvalue estimation, D12 put it there, and
  P10 is a warning. The deterministic steps go in Krylov (KS5), so the Estimation file is pure
  composition.

## 1. What exists (checked against the tree)

- **Krylov.** The tree has `krylovMatrix`, `krylovSpace`, `krylovGrade`, and
  `exists_hasOrthonormalCols_range_eq_krylovSpace` (in `Grade.lean`). In `Compression.lean`:
  `HasOrthonormalCols.conjTranspose_mulVec_aeval_mulVec_eq` (for $\deg p \le q$),
  `HasOrthonormalCols.mulVec_aeval_conjTranspose_mul_mul_mulVec_eq` (for $\deg p < q$) and the
  Ritz-polynomial orthogonality `HasOrthonormalCols.conjTranspose_mulVec_aeval_nodal_mulVec_eq_zero`.
  Each takes `hK : LinearMap.range Q.mulVecLin = krylovSpace A b q`.
- **Lanczos-FA.** `compressedCfc` and `lanczosFA` exist, with `HasOrthonormalCols.lanczosFA_eq`,
  `Matrix.IsHermitian.lanczosFA_eval`, `lanczosFA_sub`, `lanczosFA_eq_arnoldiMatrix`,
  `Matrix.IsHermitian.lanczosFA_eq_lanczosMatrix` and
  `Matrix.IsHermitian.norm_cfc_mulVec_sub_lanczosFA_le_of_isUniformApproxOn`.
- **The Lanczos recurrence.** `lanczosState`, `lanczosMatrix` and `lanczosTridiagonal` exist, the
  last of type `Matrix (Fin q) (Fin q) 𝕜`. `Matrix.IsHermitian.lanczosTridiagonal_eq` says it
  equals $\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$ for `arnoldiMatrix`.
- **The designed `Krylov/Functions/Quadrature.lean` is absent.** `Krylov-Functions.md` §4 gives
  it two theorems, `Matrix.IsHermitian.star_dotProduct_lanczosFA_eval` (exact for
  $\deg p < 2q$) and `.norm_star_dotProduct_sub_lanczosFA_le_of_isUniformApproxOn`
  ($2\varepsilon\|\mathbf{b}\|^2$), and no quadrature definition. Its status says "C6
  (quadrature) is still open". PORT_KRYLOV §1.10 adds the spectral measure "in `Matrix/Spectral`,
  characterised by its integrals" and defers the Jacobi layer (D6, option (a) "after the
  Polynomial OP stages").
- **The Polynomial OP stages are absent.** Nothing in NLAlib matches `Christoffel`,
  `IsOrthogonal`, `jacobiMatrix`, `MatchesPolynomial` or `spectralMeasure`. OP0 to OP3 exist only
  as proposals (Jackson/moments note §5).
- **Matrix.** The tree has `HasOrthonormalCols.re_quadForm_cfc_eq_sum` (the quadratic form of
  $f(\mathbf{A})$ through any unitary diagonalisation), `Matrix.IsHermitian.re_trace_cfc`,
  `Matrix.IsHermitian.spectrum_eq_image_eigenvalue`,
  `Matrix.IsHermitian.spectrum_conjTranspose_mul_mul_subset_Icc` (Ritz values lie in the
  interval), `Matrix.IsHermitian.eigenvalue_conjTranspose_mul_mul_le` (Poincaré),
  `Matrix.IsHermitian.le_eigenvalue_of_forall_mem` (Courant–Fischer), `rayleighQuotient` (in
  `Basic/QuadForm.lean`) and `tangentMatrix`.
  `Matrix.IsHermitian.exists_star_aeval_mulVec_dotProduct_cfc_mulVec_eq_sum` gives a vector with
  a prescribed spectral distribution.
- **Polynomial.** The tree has `chebyshevResidual` with
  `isUniformApproxOn_chebyshevResidual_two_mul_pow`,
  `exists_degree_le_isUniformApproxOn_Icc_of_differentiableOn` (Bernstein ellipse, any interval),
  `isUniformApproxOn_jacksonApprox_of_lipschitz` (on $[-1, 1]$ only),
  `exists_degree_lt_isUniformApproxOn_inv`, and the ForMathlib Chebyshev growth lemmas
  (`exp_mul_sqrt_div_two_le_eval_T_real`, `pow_div_two_le_eval_T_real`). No Krylov, Estimation or
  LowRank file uses the analytic, Jackson or inverse approximants (grep).
- **Probability.** `Distributions/GaussianLogOverlap.lean` is proved. It gives the tail and the
  first two moments of $\log(\|\mathbf{g}\|^2/\langle\mathbf{u}, \mathbf{g}\rangle^2)$, and no
  file imports it. `Measurability/Krylov.lean` has only `measurable_blockKrylovMatrix`.
  `measurable_eigenvalue` and `measurable_rangeProjector` exist in `Measurability/Matrix.lean`.
  `gaussianVector n` is real (`Measure (n → ℝ)`), so random-start statements are over ℝ
  (CONTRIBUTING §5.1).

**Gap survey, verified.** M1, P2, K1, K2, K3 and K4 are accurate. Three corrections. First, K1
lists "Deps: Poly8 amplifier" and K2 lists "Poly8 even Chebyshev filter": the amplifier is not
needed (finding 4), but the even filter is. Second, K2's "almost-sure grade" is not needed
(finding 3). Third, K3's "Golub–Welsch" is a corollary, not a separate stage (finding 2).

## 2. Objects

Common context in the Matrix and Krylov files:
`{𝕜 : Type*} [RCLike 𝕜] {n r : Type*} [Fintype n] [DecidableEq n] [Fintype r] [DecidableEq r]`,
with `open MeasureTheory Polynomial` and `open scoped Matrix MatrixOrder`.

### 2.1 Spectral measures (KS1, `Matrix/Spectral/SpectralMeasure.lean`)

```lean
open Classical in
/-- The **spectral measure** $\mu_{\mathbf{A},\mathbf{b}}$ of a Hermitian $\mathbf{A}$ and a
vector $\mathbf{b}$: the finite measure on $\mathbb{R}$ with an atom at each distinct eigenvalue
$x$ of weight $\|\mathbf{P}_x\mathbf{b}\|^2$, $\mathbf{P}_x$ the orthogonal projector onto the
eigenspace of $x$. Its integral of every $f$ is
$\operatorname{Re}\,\mathbf{b}^{\mathsf{H}}f(\mathbf{A})\mathbf{b}$
(`integral_spectralMeasure`); its mass is $\|\mathbf{b}\|^2$. A repeated
eigenvalue is one atom. Junk value: $0$ when $\mathbf{A}$ is not Hermitian. The projector
$\mathbf{P}_x$ is `cfc` of the indicator of $\{x\}$; that is a legitimate functional calculus
(not the junk value of `cfc_apply_of_not_continuousOn`) because the spectrum is finite, so every
function is continuous on it. The definition needs `[DecidableEq n]` through Mathlib's
`Matrix.finite_real_spectrum` (`Mathlib/Analysis/Matrix/Spectrum.lean`).
[GolubMeurant2010, Ch. 7]. -/
noncomputable def spectralMeasure (A : Matrix n n 𝕜) (b : n → 𝕜) : Measure ℝ :=
  ∑ x ∈ A.finite_real_spectrum.toFinset,
    ENNReal.ofReal (RCLike.re (quadForm (cfc (fun t : ℝ => if t = x then (1 : ℝ) else 0) A) b)) •
      Measure.dirac x

/-- The **empirical spectral measure** $\lvert n\rvert^{-1}\sum_{k<\lvert n\rvert}
\delta_{\lambda_k(\mathbf{A})}$, eigenvalues counted with multiplicity. A probability measure for
nonempty $n$; $0$ for empty $n$; $\delta_0$ when $\mathbf{A}$ is not Hermitian (every
`eigenvalue A k` is then $0$). -/
noncomputable def empiricalSpectralMeasure (A : Matrix n n 𝕜) : Measure ℝ :=
  (Fintype.card n : ℝ≥0∞)⁻¹ •
    ∑ k ∈ Finset.range (Fintype.card n), Measure.dirac (eigenvalue A k)

/-- The squared tangent of the angle between $\mathbf{b}$ and the eigenspace of $c$, read off
the spectral measure: $\mu_{\mathbf{A},\mathbf{b}}(\mathbb{R}\setminus\{c\}) /
\mu_{\mathbf{A},\mathbf{b}}(\{c\})$. Junk value $0$ when $\mathbf{b}$ has no component in that
eigenspace (in particular when $c$ is not an eigenvalue). -/
noncomputable def spectralTangentSq (A : Matrix n n 𝕜) (b : n → 𝕜) (c : ℝ) : ℝ :=
  (spectralMeasure A b).real {c}ᶜ / (spectralMeasure A b).real {c}
```

Proposed §5.3 rows:

| Concept | Spelling | Mathlib bridge |
|---|---|---|
| spectral measure of a matrix and a vector | `spectralMeasure A b : Measure ℝ`, total, unnormalised (mass $\|\mathbf{b}\|^2$), one atom per distinct eigenvalue, $0$ off Hermitian | `integral_spectralMeasure`; to an eigenbasis, `HasOrthonormalCols.spectralMeasure_eq_sum`; Mathlib has none (searched) |
| empirical spectral measure | `empiricalSpectralMeasure A`, $\lvert n\rvert^{-1}\sum_{k<\lvert n\rvert}\delta_{\lambda_k}$ | `Matrix.IsHermitian.integral_empiricalSpectralMeasure` to `re_trace_cfc`; Mathlib has none |
| angle between a vector and an eigenspace | `spectralTangentSq A b c` | `Matrix.IsHermitian.spectralTangentSq_le` (eigenvector form) |

### 2.2 Moment matching, orthogonality, Gauss rules (KS2, `Polynomial/Orthogonal/`)

```lean
/-- $\mu$ and $\nu$ **match the first $N$ moments**: $\int p\,d\mu = \int p\,d\nu$ for every
real polynomial of degree less than $N$. Total; its equivalence with monomial moments needs
integrability (`matchesMoments_iff_forall_integral_pow`). -/
def MatchesMoments (μ ν : Measure ℝ) (N : ℕ) : Prop :=
  ∀ p : ℝ[X], p.degree < N → ∫ x, p.eval x ∂μ = ∫ x, p.eval x ∂ν

/-- $p$ is **orthogonal to every polynomial of degree less than $k$** in $L^2(\mu)$. -/
def IsOrthogonalPolynomial (μ : Measure ℝ) (k : ℕ) (p : ℝ[X]) : Prop :=
  ∀ r : ℝ[X], r.degree < k → ∫ x, p.eval x * r.eval x ∂μ = 0

/-- The **interpolatory quadrature rule** of $\mu$ at the nodes $s$, as a measure: weight
$\int \ell_x\,d\mu$ at each node $x$, $\ell_x$ the Lagrange basis polynomial. At Gauss nodes the
weights are nonnegative (`IsOrthogonalPolynomial.integral_eval_basis_eq_integral_sq`), and the
rule is the Gauss rule. Junk: negative weights are truncated at $0$. -/
noncomputable def interpolatoryQuadrature (μ : Measure ℝ) (s : Finset ℝ) : Measure ℝ :=
  ∑ x ∈ s, ENNReal.ofReal (∫ t, (Lagrange.basis s id x).eval t ∂μ) • Measure.dirac x
```

Rows: "moment matching | `MatchesMoments μ ν N` (degree $< N$) | `matchesMoments_measureT`
(Mathlib's Chebyshev–Gauss)", "orthogonality to lower degrees | `IsOrthogonalPolynomial μ k p`
| `isOrthogonalPolynomial_T_measureT` (optional, from Mathlib's
`integral_eval_T_real_mul_eval_T_real_measureT_of_ne`)" and "Gauss rule |
`interpolatoryQuadrature μ s` | none in Mathlib beyond `measureT`".

### 2.3 Lanczos quadrature (KS3, `Krylov/Functions/Quadrature.lean`)

```lean
/-- The **Lanczos (Gauss) quadrature rule** of $q$ steps from $\mathbf{b}$:
$\mathsf{lanczosQuadrature}(\mathbf{A}, \mathbf{b}, q) := \mu_{\mathbf{P}\mathbf{A}\mathbf{P},
\mathbf{P}\mathbf{b}}$ with $\mathbf{P} = \mathbf{P}_{\mathbf{K}_q(\mathbf{A},\mathbf{b})}$; for
any orthonormal basis $\mathbf{Q}$ of the Krylov space it is the spectral measure of
$(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}, \mathbf{Q}^{\mathsf{H}}\mathbf{b})$
(`HasOrthonormalCols.lanczosQuadrature_eq`): atoms at the Ritz values. Junk: $0$ at $q = 0$ and
off Hermitian. [GolubMeurant2010, Theorem 6.6] (locator from the quarry). -/
noncomputable def lanczosQuadrature (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) : Measure ℝ :=
  spectralMeasure (rangeProjector (krylovMatrix A b q) * A * rangeProjector (krylovMatrix A b q))
    (rangeProjector (krylovMatrix A b q) *ᵥ b)
```

Row: "Lanczos quadrature rule | `lanczosQuadrature A b q`; the scalar quadrature is
`RCLike.re (star b ⬝ᵥ lanczosFA A f b q)` | `integral_lanczosQuadrature`,
`HasOrthonormalCols.lanczosQuadrature_eq`".

### 2.4 What is deliberately not an object

- No Ritz-value definition (D9(b), approved). Ritz values are written
  `eigenvalue (Qᴴ * A * Q) k` for a frame of the Krylov space, and in projector form only for
  random starts.
- No `powerIterate`, `inverseIterate` or `chebyshevAmplifier`. These are `A ^ q *ᵥ b`,
  `(A - σ • 1)⁻¹ ^ q *ᵥ b`, and the existing `chebyshevResidual` reflected inside proofs.
- No Jacobi matrix or continued fraction (KS7, deferred).

`docs/design/Mathlib-deviations.md`: the new objects are additions with bridges and no numbered
deviation (precedent: `Krylov-Functions.md` §8).

## 3. Interfaces

- `MatchesMoments μ ν N` (SD2). It is the conclusion of Gauss exactness and of Lanczos
  exactness, and the hypothesis of the transfer bound M0 and the later M1. Its raw-condition
  constructor is `matchesMoments_iff` (`Iff.rfl`). Monomial bridge:
  `matchesMoments_iff_forall_integral_pow`. API: `refl`, `symm`, `trans`, `mono`,
  `matchesMoments_zero`, `measureReal_univ_eq`.
- `IsOrthogonalPolynomial μ k p` (SD4). It is the hypothesis of Gauss exactness, and the
  conclusion of the Ritz-polynomial theorem in KS3c. API: `mono`,
  `MatchesMoments.isOrthogonalPolynomial_iff` (moment invariance).
- The support hypothesis (SD3), `[IsFiniteMeasure μ] (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b)`, is
  produced for spectral measures by `Matrix.IsHermitian.ae_mem_Icc_spectralMeasure`.
- The spectrum-location hypotheses keep the approved format (D8, maintainer 2026-10-17):
  `spectrum ℝ A ⊆ Set.Icc a c ∪ {eigenvalue A 0}` for "every other eigenvalue lies in $[a, c]$",
  and `spectrum ℝ A ⊆ s ∪ {c}` in the filter theorem. No eigenvector hypothesis appears in a
  headline. No statement quantifies over `eigenvectorBasis` (T8).

## 4. Statements by stage

A one-line claim follows each signature. Full docstrings are written at the skeleton. A few are
given here to show the citation, B6 and value-marker forms.

### KS1. Spectral measure (`Matrix/Spectral/SpectralMeasure.lean`, new, about 550 lines)

Rule T13: `integral_spectralMeasure`, `spectralMeasure_apply`, `spectralMeasure_cfc_mulVec` and
(KS3b) `integral_lanczosQuadrature` take no Hermitian hypothesis, because both sides vanish (or
agree by definition) off Hermitian. The hypothesis stays where `aeval`, `A ^ k`, the mass or
`rayleighQuotient` appears, since those do not vanish there.

```lean
instance isFiniteMeasure_spectralMeasure (A : Matrix n n 𝕜) (b : n → 𝕜) :
    IsFiniteMeasure (spectralMeasure A b)

theorem integrable_spectralMeasure (A : Matrix n n 𝕜) (b : n → 𝕜) (f : ℝ → ℝ) :
    Integrable f (spectralMeasure A b)
-- every function: the measure is a finite sum of Dirac masses

/-- **The spectral measure integrates the quadratic form**: for every square $\mathbf{A}$
(both sides vanish off Hermitian, so no hypothesis), every
$\mathbf{b}$ and every $f : \mathbb{R} \to \mathbb{R}$,
$\int f\,d\mu_{\mathbf{A},\mathbf{b}} = \operatorname{Re}\,\mathbf{b}^{\mathsf{H}}
f(\mathbf{A})\mathbf{b}$, with $f(\mathbf{A})$ Mathlib's `cfc f A`. No continuity or
measurability of $f$ is needed: the measure is atomic.
[GolubMeurant2010, Ch. 7]; there for real symmetric $\mathbf{A}$ as a Riemann–Stieltjes integral,
here over any `RCLike` field.
Result: spectral-measure -/
theorem integral_spectralMeasure (A : Matrix n n 𝕜) (b : n → 𝕜) (f : ℝ → ℝ) :
    ∫ x, f x ∂spectralMeasure A b = RCLike.re (quadForm (cfc f A) b)

theorem Matrix.IsHermitian.integral_eval_spectralMeasure {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (b : n → 𝕜) (p : ℝ[X]) :
    ∫ x, p.eval x ∂spectralMeasure A b = RCLike.re (quadForm (aeval A p) b)

theorem Matrix.IsHermitian.integral_pow_spectralMeasure {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (b : n → 𝕜) (k : ℕ) :
    ∫ x, x ^ k ∂spectralMeasure A b = RCLike.re (quadForm (A ^ k) b)

theorem Matrix.IsHermitian.measureReal_univ_spectralMeasure {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) :
    (spectralMeasure A b).real Set.univ = ‖WithLp.toLp 2 b‖ ^ 2

theorem spectralMeasure_apply (A : Matrix n n 𝕜) (b : n → 𝕜) (S : Set ℝ) :
    spectralMeasure A b S =
      ENNReal.ofReal (RCLike.re (quadForm (cfc (S.indicator fun _ => (1 : ℝ)) A) b))
-- the characterisation; every set, since the measure is atomic

theorem spectralMeasure_compl_spectrum_eq_zero (A : Matrix n n 𝕜) (b : n → 𝕜) :
    spectralMeasure A b (spectrum ℝ A)ᶜ = 0

theorem Matrix.IsHermitian.ae_mem_Icc_spectralMeasure {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {a a' : ℝ} (hs : spectrum ℝ A ⊆ Set.Icc a a') (b : n → 𝕜) :
    ∀ᵐ x ∂spectralMeasure A b, x ∈ Set.Icc a a'
-- the SD3 hypothesis for spectral measures

theorem HasOrthonormalCols.spectralMeasure_eq_sum {U : Matrix n r 𝕜} (hU : HasOrthonormalCols U)
    (hr : Fintype.card r = Fintype.card n) {A : Matrix n n 𝕜} {d : r → ℝ}
    (hA : A = U * Matrix.diagonal (fun i => ((d i : ℝ) : 𝕜)) * Uᴴ) (b : n → 𝕜) :
    spectralMeasure A b =
      ∑ i, ENNReal.ofReal (‖(Uᴴ *ᵥ b) i‖ ^ 2) • Measure.dirac (d i)
-- the eigenbasis bridge (same hypotheses as `HasOrthonormalCols.re_quadForm_cfc_eq_sum`);
-- repeated eigenvalues give atoms that add up

theorem HasOrthonormalCols.spectralMeasure_mul_mul_conjTranspose {U : Matrix n r 𝕜}
    (hU : HasOrthonormalCols U) {T : Matrix r r 𝕜} (hT : T.IsHermitian) (c : r → 𝕜) :
    spectralMeasure (U * T * Uᴴ) (U *ᵥ c) = spectralMeasure T c
-- isometric invariance, frames included; unitary invariance is the square case

theorem spectralMeasure_smul (A : Matrix n n 𝕜) (c : 𝕜) (b : n → 𝕜) :
    spectralMeasure A (c • b) = ENNReal.ofReal (‖c‖ ^ 2) • spectralMeasure A b

theorem spectralMeasure_cfc_mulVec (A : Matrix n n 𝕜) (g : ℝ → ℝ) (b : n → 𝕜) :
    spectralMeasure A (cfc g A *ᵥ b) =
      (spectralMeasure A b).withDensity (fun x => ENNReal.ofReal (g x ^ 2))
-- filtering multiplies the measure by g²

theorem Matrix.IsHermitian.rayleighQuotient_eq_integral_div {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) :
    rayleighQuotient A b =
      (∫ x, x ∂spectralMeasure A b) / (spectralMeasure A b).real Set.univ

theorem Matrix.IsHermitian.norm_star_dotProduct_sq_le_measureReal_spectralMeasure
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {u : n → 𝕜} {c : ℝ}
    (hu : A *ᵥ u = (c : 𝕜) • u) (hu1 : ‖WithLp.toLp 2 u‖ = 1) (b : n → 𝕜) :
    ‖star u ⬝ᵥ b‖ ^ 2 ≤ (spectralMeasure A b).real {c}

theorem spectralTangentSq_nonneg (A : Matrix n n 𝕜) (b : n → 𝕜) (c : ℝ) :
    0 ≤ spectralTangentSq A b c

theorem Matrix.IsHermitian.one_add_spectralTangentSq {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {b : n → 𝕜} {c : ℝ} (hb : 0 < (spectralMeasure A b).real {c}) :
    1 + spectralTangentSq A b c = ‖WithLp.toLp 2 b‖ ^ 2 / (spectralMeasure A b).real {c}

theorem Matrix.IsHermitian.spectralTangentSq_le {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {u : n → 𝕜} {c : ℝ} (hu : A *ᵥ u = (c : 𝕜) • u) (hu1 : ‖WithLp.toLp 2 u‖ = 1)
    {b : n → 𝕜} (hub : star u ⬝ᵥ b ≠ 0) :
    spectralTangentSq A b c ≤
      (‖WithLp.toLp 2 b‖ ^ 2 - ‖star u ⬝ᵥ b‖ ^ 2) / ‖star u ⬝ᵥ b‖ ^ 2
-- the bridge to the eigenvector overlap (PORT_KRYLOV §1.11); equality for a simple eigenvalue
```

**The filter theorem.** It is the one interface for every eigenvalue bound in KS5. It sits here
because its subject is the Rayleigh quotient of $g(\mathbf{A})\mathbf{b}$, which involves no
Krylov space.

```lean
/-- **Rayleigh quotient of a filtered vector**: let $\mathbf{A}$ be Hermitian with spectrum in
$s \cup \{c\}$, $|x - c| \le D$ and $|g(x)| \le \delta|g(c)|$ for $x \in s$, $g(c) \ne 0$, and
$\mathbf{b}$ with a nonzero component in the eigenspace of $c$. Then
$$\bigl|c - \rho_{\mathbf{A}}(g(\mathbf{A})\mathbf{b})\bigr| \le D\,\delta^2\tan^2\angle(\mathbf{b},
E_c)\,,$$
$\rho_{\mathbf{A}}$ the Rayleigh quotient and $\tan^2\angle(\mathbf{b}, E_c)$ the ratio
$\mu_{\mathbf{A},\mathbf{b}}(\mathbb{R}\setminus\{c\})/\mu_{\mathbf{A},\mathbf{b}}(\{c\})$.
[TrefethenBau1997, Theorem 27.1] (proof); [Saad2011, §6.6.1] (proof): both for a polynomial or
power filter and an eigenvector of a simple eigenvalue; here any filter and any multiplicity. -/
theorem Matrix.IsHermitian.abs_sub_rayleighQuotient_cfc_mulVec_le {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {s : Set ℝ} {c D δ : ℝ} (hs : spectrum ℝ A ⊆ s ∪ {c})
    (hD : ∀ x ∈ s, |x - c| ≤ D) {g : ℝ → ℝ} (hgc : g c ≠ 0)
    (hg : ∀ x ∈ s, |g x| ≤ δ * |g c|) (b : n → 𝕜) (hb : 0 < (spectralMeasure A b).real {c}) :
    |c - rayleighQuotient A (cfc g A *ᵥ b)| ≤ D * δ ^ 2 * spectralTangentSq A b c
```

**The empirical spectral measure.**

```lean
instance isProbabilityMeasure_empiricalSpectralMeasure [Nonempty n] (A : Matrix n n 𝕜) :
    IsProbabilityMeasure (empiricalSpectralMeasure A)

theorem integral_empiricalSpectralMeasure (A : Matrix n n 𝕜) (f : ℝ → ℝ) :
    ∫ x, f x ∂empiricalSpectralMeasure A =
      (∑ k ∈ Finset.range (Fintype.card n), f (eigenvalue A k)) / Fintype.card n

theorem Matrix.IsHermitian.integral_empiricalSpectralMeasure {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (f : ℝ → ℝ) :
    ∫ x, f x ∂empiricalSpectralMeasure A = RCLike.re (cfc f A).trace / Fintype.card n

theorem Matrix.IsHermitian.sum_spectralMeasure_single {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    ∑ i, spectralMeasure A (Pi.single i 1) = (Fintype.card n : ℝ≥0∞) • empiricalSpectralMeasure A

theorem Matrix.IsHermitian.ae_mem_spectrum_empiricalSpectralMeasure {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) : ∀ᵐ x ∂empiricalSpectralMeasure A, x ∈ spectrum ℝ A
```

The definitions and theorems in this block need no `DecidableEq n` (`eigenvalue` does not).

### KS2. Moments, orthogonality, Gauss rules (`Polynomial/Orthogonal/`, new; P11 holds: Mathlib only)

**KS2a, `Moments.lean`** (about 220 lines). Context: `{μ ν : Measure ℝ} {N : ℕ}`.

```lean
theorem matchesMoments_iff : MatchesMoments μ ν N ↔
    ∀ p : ℝ[X], p.degree < N → ∫ x, p.eval x ∂μ = ∫ x, p.eval x ∂ν := Iff.rfl
theorem MatchesMoments.refl (μ : Measure ℝ) (N : ℕ) : MatchesMoments μ μ N
theorem MatchesMoments.symm (h : MatchesMoments μ ν N) : MatchesMoments ν μ N
theorem MatchesMoments.trans {ξ : Measure ℝ} (h : MatchesMoments μ ν N)
    (h' : MatchesMoments ν ξ N) : MatchesMoments μ ξ N
theorem MatchesMoments.mono {M : ℕ} (h : MatchesMoments μ ν N) (hMN : M ≤ N) :
    MatchesMoments μ ν M
theorem matchesMoments_zero (μ ν : Measure ℝ) : MatchesMoments μ ν 0
theorem matchesMoments_iff_forall_mem_degreeLT : MatchesMoments μ ν N ↔
    ∀ p ∈ Polynomial.degreeLT ℝ N, ∫ x, p.eval x ∂μ = ∫ x, p.eval x ∂ν
-- the bridge to Mathlib's `Polynomial.degreeLT` (via `Polynomial.mem_degreeLT`)

theorem matchesMoments_iff_forall_integral_pow [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {a b : ℝ} (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hν : ∀ᵐ x ∂ν, x ∈ Set.Icc a b) :
    MatchesMoments μ ν N ↔ ∀ k < N, ∫ x, x ^ k ∂μ = ∫ x, x ^ k ∂ν
-- the bridge to Mathlib's `ProbabilityTheory.moment id k`

theorem MatchesMoments.measureReal_univ_eq (h : MatchesMoments μ ν N) (hN : 0 < N) :
    μ.real Set.univ = ν.real Set.univ

/-- **Moment matching transfers uniform approximation** (M0) ... -/
theorem MatchesMoments.abs_integral_sub_integral_le_of_isUniformApproxOn
    (h : MatchesMoments μ ν N) [IsFiniteMeasure μ] [IsFiniteMeasure ν] {a b : ℝ}
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hν : ∀ᵐ x ∂ν, x ∈ Set.Icc a b) {f : ℝ → ℝ}
    (hfμ : Integrable f μ) (hfν : Integrable f ν) {p : ℝ[X]} (hp : p.degree < N) {ε : ℝ}
    (hε : Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a b) ε) :
    |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤ (μ.real Set.univ + ν.real Set.univ) * ε
-- the Jackson/moments note's M0; probability measures give 2ε

theorem matchesMoments_measureT {k : ℕ} (hk : k ≠ 0) :
    MatchesMoments Polynomial.Chebyshev.measureT
      (ENNReal.ofReal (Real.pi / k) • ∑ i ∈ Finset.range k,
        Measure.dirac (Real.cos ((2 * i + 1) / (2 * k) * Real.pi))) (2 * k)
-- optional bridge: Mathlib's Chebyshev–Gauss in this vocabulary (`integral_eq_sumZeroes`)
```

**KS2b, `Basic.lean` and `Gauss.lean`** (about 350 lines together). The hypotheses come first so
that the API sits in the predicate's namespace (N9).

```lean
theorem IsOrthogonalPolynomial.mono {μ : Measure ℝ} {j k : ℕ} {p : ℝ[X]}
    (h : IsOrthogonalPolynomial μ k p) (hjk : j ≤ k) : IsOrthogonalPolynomial μ j p

theorem MatchesMoments.isOrthogonalPolynomial_iff {μ ν : Measure ℝ} {N k : ℕ} {p : ℝ[X]}
    (h : MatchesMoments μ ν N) (hN : p.natDegree + k ≤ N) :
    IsOrthogonalPolynomial μ k p ↔ IsOrthogonalPolynomial ν k p
-- moment invariance (OP0)

/-- **Gauss quadrature** ... exact for $\deg p < 2\lvert s\rvert$ ...
[Gautschi2004, Theorems 1.45 and 1.46]; [GolubMeurant2010, Theorem 6.6]. -/
theorem IsOrthogonalPolynomial.integral_eval_eq_sum {μ : Measure ℝ} {s : Finset ℝ}
    (hs : IsOrthogonalPolynomial μ s.card (Lagrange.nodal s id)) [IsFiniteMeasure μ] {a b : ℝ}
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {p : ℝ[X]} (hp : p.degree < 2 * s.card) :
    ∫ x, p.eval x ∂μ = ∑ x ∈ s, (∫ t, (Lagrange.basis s id x).eval t ∂μ) * p.eval x

instance isFiniteMeasure_interpolatoryQuadrature (μ : Measure ℝ) (s : Finset ℝ) :
    IsFiniteMeasure (interpolatoryQuadrature μ s)

theorem IsOrthogonalPolynomial.integral_eval_basis_eq_integral_sq {μ : Measure ℝ}
    {s : Finset ℝ} (hs : IsOrthogonalPolynomial μ s.card (Lagrange.nodal s id))
    [IsFiniteMeasure μ] {a b : ℝ} (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {x : ℝ} (hx : x ∈ s) :
    ∫ t, (Lagrange.basis s id x).eval t ∂μ = ∫ t, (Lagrange.basis s id x).eval t ^ 2 ∂μ
-- the weights are nonnegative

theorem IsOrthogonalPolynomial.matchesMoments_interpolatoryQuadrature {μ : Measure ℝ} {s : Finset ℝ}
    (hs : IsOrthogonalPolynomial μ s.card (Lagrange.nodal s id)) [IsFiniteMeasure μ] {a b : ℝ}
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) :
    MatchesMoments μ (interpolatoryQuadrature μ s) (2 * s.card)

theorem IsOrthogonalPolynomial.integral_interpolatoryQuadrature {μ : Measure ℝ} {s : Finset ℝ}
    (hs : IsOrthogonalPolynomial μ s.card (Lagrange.nodal s id)) [IsFiniteMeasure μ] {a b : ℝ}
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (f : ℝ → ℝ) :
    ∫ x, f x ∂interpolatoryQuadrature μ s = ∑ x ∈ s, (∫ t, (Lagrange.basis s id x).eval t ∂μ) * f x
```

Proof of exactness: divide $p$ by the monic nodal polynomial, $p = \pi_s u + v$ with
$\deg u, \deg v < \lvert s\rvert$. Then $\int\pi_s u = 0$ by the hypothesis,
$v = $ `Lagrange.interpolate s id v` (Mathlib's `eq_interpolate`), and $p = v$ at the nodes. The
existence of Gauss nodes for a given measure (real, distinct roots of the orthogonal polynomial,
inside the support) is not proved here; KS7 records it. For spectral measures, KS3c supplies the
nodes from the Ritz values instead.

### KS3. Lanczos quadrature (`Krylov/Functions/Quadrature.lean`, new, about 400 lines)

**KS3a: C6, as approved in `Krylov-Functions.md` §4.** It needs no new vocabulary and can run
first.

```lean
/-- **Gauss (Lanczos) quadrature is exact through degree $2q - 1$**: for Hermitian
$\mathbf{A}$ and a real polynomial $p$ with $\deg p < 2q$,
$\mathbf{b}^{\mathsf{H}}\mathsf{lanczosFA}(\mathbf{A}, p, \mathbf{b}, q) =
\mathbf{b}^{\mathsf{H}}p(\mathbf{A})\mathbf{b}$; Lanczos-FA itself is exact only through degree
$q - 1$. [GolubMeurant2010, Theorem 6.6] (locator from the quarry).
Result: lanczos-gauss-quadrature -/
theorem Matrix.IsHermitian.star_dotProduct_lanczosFA_eval {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) {q : ℕ} {p : ℝ[X]} (hp : p.degree < 2 * q) :
    star b ⬝ᵥ lanczosFA A (fun x => p.eval x) b q = quadForm (aeval A p) b

theorem Matrix.IsHermitian.norm_star_dotProduct_cfc_mulVec_sub_lanczosFA_le_of_isUniformApproxOn
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a a' : ℝ} (hs : spectrum ℝ A ⊆ Set.Icc a a')
    {f : ℝ → ℝ} {q : ℕ} {p : ℝ[X]} (hp : p.degree < 2 * q) {ε : ℝ}
    (hε : Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a a') ε) (b : n → 𝕜) :
    ‖star b ⬝ᵥ (cfc f A *ᵥ b - lanczosFA A f b q)‖ ≤ 2 * ε * ‖WithLp.toLp 2 b‖ ^ 2
```

C6's approved name was `.norm_star_dotProduct_sub_lanczosFA_le_of_isUniformApproxOn`. The
version above adds the `cfc_mulVec` tokens so that it reads like its vector sibling
`norm_cfc_mulVec_sub_lanczosFA_le_of_isUniformApproxOn`. Question Q5.

Proof route: by the frame form, $\mathbf{b}^{\mathsf{H}}\mathsf{lanczosFA}(p) =
(\mathbf{Q}^{\mathsf{H}}\mathbf{b})^{\mathsf{H}}p(\mathbf{T})\mathbf{Q}^{\mathsf{H}}\mathbf{b}$.
Split each $X^j$ with $j < 2q$ as $X^{j_1}X^{j_2}$, $j_1 \le q$ and $j_2 < q$. Then use
`conjTranspose_mulVec_aeval_mulVec_eq` and
$\mathbf{Q}\mathbf{Q}^{\mathsf{H}}\mathbf{A}^{j_2}\mathbf{b} = \mathbf{A}^{j_2}\mathbf{b}$. The
error bound follows by `lanczosFA_sub`, as for the vector bound: the Ritz values lie in
$[a, a']$.

**KS3b: the rule as a measure (SD5).** After KS1 and KS2a.

```lean
instance isFiniteMeasure_lanczosQuadrature (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) :
    IsFiniteMeasure (lanczosQuadrature A b q)

theorem integral_lanczosQuadrature (A : Matrix n n 𝕜) (f : ℝ → ℝ) (b : n → 𝕜) (q : ℕ) :
    ∫ x, f x ∂lanczosQuadrature A b q = RCLike.re (star b ⬝ᵥ lanczosFA A f b q)

theorem HasOrthonormalCols.lanczosQuadrature_eq {Q : Matrix n r 𝕜} (hQ : HasOrthonormalCols Q)
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {b : n → 𝕜} {q : ℕ}
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b q) :
    lanczosQuadrature A b q = spectralMeasure (Qᴴ * A * Q) (Qᴴ *ᵥ b)

theorem Matrix.IsHermitian.lanczosQuadrature_succ_eq {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (b : n → 𝕜) (q : ℕ) :
    lanczosQuadrature A b (q + 1) =
      spectralMeasure (lanczosTridiagonal A b (q + 1)) ((‖WithLp.toLp 2 b‖ : 𝕜) • Pi.single 0 1)
-- proof by integral extensionality on the two atomic measures: both integrals of every f equal
-- ‖b‖² Re f(T)₀₀ (`lanczosFA_eq_lanczosMatrix`, `conjTranspose_arnoldiMatrix_mulVec_self`). Not
-- through the frame lemma: past the grade `lanczosMatrix` has zero columns and is no frame.

/-- ... $\int f\,d\,\mathsf{lanczosQuadrature}(\mathbf{A}, \mathbf{b}, q + 1) =
\|\mathbf{b}\|^2\operatorname{Re}\,\mathbf{e}_0^{\mathsf{H}}f(\mathbf{T})\mathbf{e}_0$ ... -/
theorem Matrix.IsHermitian.integral_lanczosQuadrature_succ {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (f : ℝ → ℝ) (b : n → 𝕜) (q : ℕ) :
    ∫ x, f x ∂lanczosQuadrature A b (q + 1) =
      ‖WithLp.toLp 2 b‖ ^ 2 * RCLike.re (cfc f (lanczosTridiagonal A b (q + 1)) 0 0)

/-- **Lanczos quadrature matches the first $2q$ moments of the spectral measure** ...
[GolubMeurant2010, Theorem 6.6]; [ChenTrogdonUbaru2022], locator to check.
Result: lanczos-gauss-quadrature -/
theorem Matrix.IsHermitian.matchesMoments_lanczosQuadrature {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) (q : ℕ) :
    MatchesMoments (spectralMeasure A b) (lanczosQuadrature A b q) (2 * q)

theorem Matrix.IsHermitian.ae_mem_Icc_lanczosQuadrature {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {a a' : ℝ} (hs : spectrum ℝ A ⊆ Set.Icc a a') (b : n → 𝕜) (q : ℕ) :
    ∀ᵐ x ∂lanczosQuadrature A b q, x ∈ Set.Icc a a'

theorem Matrix.IsHermitian.measureReal_univ_lanczosQuadrature {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) {q : ℕ} (hq : 0 < q) :
    (lanczosQuadrature A b q).real Set.univ = ‖WithLp.toLp 2 b‖ ^ 2

/-- **Golub–Welsch** ... nodes the eigenvalues of $\mathbf{T}$, weights
$\|\mathbf{b}\|^2|\mathbf{U}_{0i}|^2$ ... [GolubMeurant2010, Ch. 6] (locator from the quarry). -/
theorem Matrix.IsHermitian.lanczosQuadrature_succ_eq_sum {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (b : n → 𝕜) (q : ℕ) {U : Matrix (Fin (q + 1)) (Fin (q + 1)) 𝕜} (hU : HasOrthonormalCols U)
    {d : Fin (q + 1) → ℝ}
    (hT : lanczosTridiagonal A b (q + 1) = U * Matrix.diagonal (fun i => ((d i : ℝ) : 𝕜)) * Uᴴ) :
    lanczosQuadrature A b (q + 1) =
      ∑ i, ENNReal.ofReal (‖WithLp.toLp 2 b‖ ^ 2 * ‖U 0 i‖ ^ 2) • Measure.dirac (d i)
```

For $\mathbf{b}^{\mathsf{H}}f(\mathbf{A})\mathbf{b}$ itself there is no separate measure-form
error theorem. A user applies `MatchesMoments.abs_integral_sub_integral_le_of_isUniformApproxOn`
to `matchesMoments_lanczosQuadrature`, with the two support lemmas and the two integral bridges.
That gives the same $2\varepsilon\|\mathbf{b}\|^2$ as C6, for any test function, which is the form
CTU's spectrum-approximation bounds start from (question Q2).

**KS3c (after KS2b; not optional): the orthogonal-polynomial reading and positive weights.**

```lean
theorem HasOrthonormalCols.card_spectrum_conjTranspose_mul_mul_eq {Q : Matrix n r 𝕜}
    (hQ : HasOrthonormalCols Q) {A : Matrix n n 𝕜} (hA : A.IsHermitian) {b : n → 𝕜} {q : ℕ}
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b q) (hq : q ≤ krylovGrade A b) :
    (Qᴴ * A * Q).finite_real_spectrum.toFinset.card = q
-- distinct Ritz values below the grade: a nodal polynomial of fewer Ritz values would make
-- π(A)b ∈ K_q orthogonal to K_q, hence zero, against the grade; no tridiagonal theory needed

theorem HasOrthonormalCols.isOrthogonalPolynomial_nodal {Q : Matrix n r 𝕜}
    (hQ : HasOrthonormalCols Q) {A : Matrix n n 𝕜} (hA : A.IsHermitian) {b : n → 𝕜} {q : ℕ}
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b q) :
    IsOrthogonalPolynomial (spectralMeasure A b) q
      (Lagrange.nodal (Qᴴ * A * Q).finite_real_spectrum.toFinset id)
-- the Ritz polynomial is the degree-q orthogonal polynomial (from Compression's orthogonality)

theorem HasOrthonormalCols.lanczosQuadrature_eq_interpolatoryQuadrature {Q : Matrix n r 𝕜}
    (hQ : HasOrthonormalCols Q) {A : Matrix n n 𝕜} (hA : A.IsHermitian) {b : n → 𝕜} {q : ℕ}
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b q) (hq : q ≤ krylovGrade A b) :
    lanczosQuadrature A b q =
      interpolatoryQuadrature (spectralMeasure A b) (Qᴴ * A * Q).finite_real_spectrum.toFinset
-- Lanczos quadrature is the Gauss rule of the spectral measure

theorem HasOrthonormalCols.measureReal_lanczosQuadrature_singleton_pos {Q : Matrix n r 𝕜}
    (hQ : HasOrthonormalCols Q) {A : Matrix n n 𝕜} (hA : A.IsHermitian) {b : n → 𝕜} {q : ℕ}
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b q) (hq : q ≤ krylovGrade A b)
    {x : ℝ} (hx : x ∈ spectrum ℝ (Qᴴ * A * Q)) :
    0 < (lanczosQuadrature A b q).real {x}
-- every Ritz value below the grade carries positive weight, so the support of the Lanczos rule
-- is exactly the set of Ritz values. Corollary of `lanczosQuadrature_eq_interpolatoryQuadrature`:
-- the weight is ∫ ℓ_x dμ = ∫ ℓ_x² dμ = ‖ℓ_x(A) b‖² (`integral_eval_basis_eq_integral_sq`,
-- `integral_eval_spectralMeasure`), and ℓ_x(A) b ≠ 0 because ℓ_x is a nonzero polynomial of
-- degree q - 1 < q ≤ grade (`krylovMatrix_mulVec_injective_iff`, Krylov/Basic/Grade.lean).
-- No unreduced-tridiagonal theory is needed.
```

### KS4. Explicit rates for Lanczos-FA and Lanczos quadrature

**Polynomial addition** (`Polynomial/Approximation/Jackson.lean`, about 60 lines). This is the
one missing lower-layer piece, an affine transport of the existing $[-1, 1]$ theorem.

```lean
/-- **Jackson's theorem on an interval**: an $L$-Lipschitz $f$ on $[a, b]$ is within
<!-- value jacksonApproximationConstant -->
$$\frac{\pi L(b - a)}{2(N + 2)}$$
of a polynomial of degree at most $N$ on $[a, b]$ (the constant is
`jacksonApproximationConstant`). The affine image of
`isUniformApproxOn_jacksonApprox_of_lipschitz`. [ChenTrogdonUbaru2022, Appendix C, Theorem 38]
(the label `Jackson.lean` uses); there on
$[-1, 1]$ with the factor $\pi^2/2$. -/
theorem exists_degree_le_isUniformApproxOn_Icc_of_lipschitzOnWith {𝕜 : Type*} [RCLike 𝕜]
    {f : ℝ → 𝕜} {L : ℝ≥0} {a b : ℝ} (hab : a < b) (hf : LipschitzOnWith L f (Set.Icc a b))
    (N : ℕ) :
    ∃ p : 𝕜[X], p.degree ≤ (N : WithBot ℕ) ∧
      Metric.IsUniformApproxOn (fun x : ℝ => p.eval (x : 𝕜)) f (Set.Icc a b)
        (jacksonApproximationConstant * L * (b - a) / (2 * (N + 2)))
```

**In `LanczosFA.lean`**, after the uniform bound (about 120 lines; new import of
`AnalyticApproximation` and `Jackson`):

```lean
theorem Matrix.IsHermitian.norm_cfc_mulVec_sub_lanczosFA_le_of_differentiableOn
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a a' : ℝ} (haa : a < a')
    (hs : spectrum ℝ A ⊆ Set.Icc a a') {f : ℝ → ℝ} {F : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ)
    (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ))
    (hM : Metric.IsUniformApproxOn F (fun _ => 0) (openBernsteinEllipse ρ) M)
    (hExt : Set.EqOn (fun t : ℝ => ((f (((a' - a) * t + a' + a) / 2) : ℝ) : ℂ))
      (fun t : ℝ => F t) (Set.Icc (-1 : ℝ) 1))
    (b : n → 𝕜) (q : ℕ) :
    ‖WithLp.toLp 2 (cfc f A *ᵥ b - lanczosFA A f b (q + 1))‖ ≤
      4 * M / (ρ ^ q * (ρ - 1)) * ‖WithLp.toLp 2 b‖
-- [Saad1992, Theorem 3.4]; [Trefethen2019, Theorem 8.2] (locators from the quarry)

theorem Matrix.IsHermitian.norm_cfc_mulVec_sub_lanczosFA_le_of_lipschitzOnWith
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a a' : ℝ} (haa : a < a')
    (hs : spectrum ℝ A ⊆ Set.Icc a a') {f : ℝ → ℝ} {L : ℝ≥0}
    (hf : LipschitzOnWith L f (Set.Icc a a')) (b : n → 𝕜) (q : ℕ) :
    ‖WithLp.toLp 2 (cfc f A *ᵥ b - lanczosFA A f b (q + 1))‖ ≤
      jacksonApproximationConstant * L * (a' - a) / (q + 2) * ‖WithLp.toLp 2 b‖
```

**In `Quadrature.lean`** (about 100 lines):

```lean
theorem Matrix.IsHermitian.norm_star_dotProduct_cfc_mulVec_sub_lanczosFA_le_of_differentiableOn
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a a' : ℝ} (haa : a < a')
    (hs : spectrum ℝ A ⊆ Set.Icc a a') {f : ℝ → ℝ} {F : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ)
    (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ))
    (hM : Metric.IsUniformApproxOn F (fun _ => 0) (openBernsteinEllipse ρ) M)
    (hExt : Set.EqOn (fun t : ℝ => ((f (((a' - a) * t + a' + a) / 2) : ℝ) : ℂ))
      (fun t : ℝ => F t) (Set.Icc (-1 : ℝ) 1))
    (b : n → 𝕜) (q : ℕ) :
    ‖star b ⬝ᵥ (cfc f A *ᵥ b - lanczosFA A f b (q + 1))‖ ≤
      4 * M / (ρ ^ (2 * q + 1) * (ρ - 1)) * ‖WithLp.toLp 2 b‖ ^ 2

theorem Matrix.IsHermitian.norm_star_dotProduct_cfc_mulVec_sub_lanczosFA_le_of_lipschitzOnWith
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a a' : ℝ} (haa : a < a')
    (hs : spectrum ℝ A ⊆ Set.Icc a a') {f : ℝ → ℝ} {L : ℝ≥0}
    (hf : LipschitzOnWith L f (Set.Icc a a')) (b : n → 𝕜) (q : ℕ) :
    ‖star b ⬝ᵥ (cfc f A *ᵥ b - lanczosFA A f b (q + 1))‖ ≤
      jacksonApproximationConstant * L * (a' - a) / (2 * q + 3) * ‖WithLp.toLp 2 b‖ ^ 2
```

The arithmetic: $q + 1$ steps give degree $q$ for Lanczos-FA and degree $2q + 1$ for quadrature.
The approximant errors are $2M/(\rho^N(\rho - 1))$ and $\pi L(a' - a)/(2(N + 2))$, and the
factor 2 of the uniform bounds is absorbed. The value markers go on the Jackson pair. The
`(q + 1)` indexing matches `lanczosFA_eq_arnoldiMatrix` and avoids `q - 1`.

Not included:
- The inverse. Lanczos-FA for $x^{-1}$ is CG (`lanczosFA_inv_eq_cgIterate`), whose rates are
  already stated. Its quadrature error is the $\mathbf{A}$-norm error, by the Galerkin identity.
- $e^{-x}$, $x^s$ and other functions with dedicated approximants. These need Poly4 (§8). Until
  then the analytic corollary covers $e^{tx}$ with any chosen $\rho$.

### KS5. Ritz values and power-type iterations (`Krylov/Eigenvalues/`, new directory per D12)

**`Ritz.lean`** (about 450 lines). Here $\lambda_0 = $ `eigenvalue A 0` and $\theta_0 =$
`eigenvalue (Qᴴ * A * Q) 0` for a frame of $\mathcal{K}_{q+1}$, which is $q$ multiplications.
The lower bound $\theta_0 \le \lambda_0$ is the existing Poincaré separation.

```lean
/-- **Kaniel–Paige–Saad**: for Hermitian $\mathbf{A}$ whose eigenvalues other than
$\lambda_0 = \lambda_0(\mathbf{A})$ lie in $[a, c]$, $a < c < \lambda_0$, a vector $\mathbf{b}$
with a component in the top eigenspace, and the largest Ritz value $\theta_0$ of
$\mathcal{K}_{q+1}(\mathbf{A}, \mathbf{b})$,
$$\lambda_0 - \theta_0 \le 4(\lambda_0 - a)\tan^2\angle(\mathbf{b}, E_{\lambda_0})
\Bigl(\frac{\sqrt{\lambda_0 - a} - \sqrt{\lambda_0 - c}}{\sqrt{\lambda_0 - a} +
\sqrt{\lambda_0 - c}}\Bigr)^{2q}\,.$$
The proof gives the sharp factor $1/T_q\bigl(1 + 2(\lambda_0 - c)/(c - a)\bigr)^2$ in place of
$4(\cdot)^{2q}$; they differ by $(1 + \rho^{2q})^2 \le 4$ (rule B6). [Saad2011, Theorem 6.4] (the
case $i = 1$; locator from the quarry and PORT_KRYLOV §9, to verify); there with
$a = \lambda_{n}$, $c = \lambda_1$, an eigenvector of a simple eigenvalue and the Chebyshev form.
Result: kaniel-paige-saad -/
theorem Matrix.IsHermitian.eigenvalue_sub_eigenvalue_conjTranspose_mul_mul_le
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a c : ℝ} (hac : a < c) (hc : c < eigenvalue A 0)
    (hs : spectrum ℝ A ⊆ Set.Icc a c ∪ {eigenvalue A 0}) {b : n → 𝕜}
    (hb : 0 < (spectralMeasure A b).real {eigenvalue A 0}) {Q : Matrix n r 𝕜}
    (hQ : HasOrthonormalCols Q) {q : ℕ}
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b (q + 1)) :
    eigenvalue A 0 - eigenvalue (Qᴴ * A * Q) 0 ≤
      4 * (eigenvalue A 0 - a) * spectralTangentSq A b (eigenvalue A 0) *
        ((√(eigenvalue A 0 - a) - √(eigenvalue A 0 - c)) /
          (√(eigenvalue A 0 - a) + √(eigenvalue A 0 - c))) ^ (2 * q)

/-- **The gap-free Ritz-value bound**: for positive semidefinite $\mathbf{A}$, $0 < \varepsilon < 1$
and $\mathbf{b}$ with a component in the top eigenspace,
$$\lambda_0 - \theta_0 \le \varepsilon\lambda_0 +
4e^{-4q\sqrt{\varepsilon}}\lambda_0\tan^2\angle(\mathbf{b}, E_{\lambda_0})\,.$$
Sharp form: $1/T_q((1 + \varepsilon)/(1 - \varepsilon))^2$ in place of $4e^{-4q\sqrt\varepsilon}$
(`exp_mul_sqrt_div_two_le_eval_T_real`; the factor lost tends to 1). [MuscoMusco2015, Theorem 1]
(single-vector case; locator to check; the library cites this paper as Theorem 10 (proof),
Lemmas 2, 5, 9 and Algorithm 2, all for the block method); there with $(1 + \sqrt{2\varepsilon/(1-\varepsilon)})^{-2q}$, weaker for small $\varepsilon$ and
stronger as $\varepsilon \to 1$; constants
composed here.
Result: ritz-value-gap-free -/
theorem Matrix.PosSemidef.eigenvalue_sub_eigenvalue_conjTranspose_mul_mul_le_add
    {A : Matrix n n 𝕜} (hA : A.PosSemidef) {ε : ℝ} (hε₀ : 0 < ε) (hε₁ : ε < 1) {b : n → 𝕜}
    (hb : 0 < (spectralMeasure A b).real {eigenvalue A 0}) {Q : Matrix n r 𝕜}
    (hQ : HasOrthonormalCols Q) {q : ℕ}
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b (q + 1)) :
    eigenvalue A 0 - eigenvalue (Qᴴ * A * Q) 0 ≤
      ε * eigenvalue A 0 +
        4 * Real.exp (-4 * q * √ε) * eigenvalue A 0 * spectralTangentSq A b (eigenvalue A 0)

/-- **Kuczyński–Woźniakowski, deterministic Lanczos step** ... squared logarithmic rate, no gap
... [KuczynskiWozniakowski1992, Theorem 4.2] (locator from the quarry, to check). -/
theorem Matrix.PosSemidef.eigenvalue_sub_eigenvalue_conjTranspose_mul_mul_le_div_sq
    {A : Matrix n n 𝕜} (hA : A.PosSemidef) {b : n → 𝕜}
    (hb : 0 < (spectralMeasure A b).real {eigenvalue A 0}) {Q : Matrix n r 𝕜}
    (hQ : HasOrthonormalCols Q) {q : ℕ} (hq : 1 ≤ q)
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b (q + 1)) :
    eigenvalue A 0 - eigenvalue (Qᴴ * A * Q) 0 ≤
      4 * eigenvalue A 0 *
        (1 + Real.log (1 + spectralTangentSq A b (eigenvalue A 0)) / Real.log 2) ^ 2 / q ^ 2
```

The two PosSemidef bounds are incomparable (rule §5.2(4)). The $\varepsilon$ form is better for a
fixed target accuracy with a good start. The log-square form needs no $\varepsilon$ and degrades
only logarithmically with a poor start, which is the random-start regime. Each docstring names
the other. The right-side tokens `_le_add` and `_le_div_sq` tell them apart (N8, for review).

Proofs. KPS is the filter theorem at $g = p$, $p(x) = r(\lambda_0 - x)$ with
$r = $ `chebyshevResidual (λ₀ - c) (λ₀ - a) q`, plus $\theta_0 \ge \rho(p(\mathbf{A})\mathbf{b})$
by Courant–Fischer (`le_eigenvalue_of_forall_mem` on the span of the frame coordinates). The
gap-free bound uses $r = $ `chebyshevResidual (ε * λ₀) λ₀ q`, with $|r| \le
1/T_q((1+\varepsilon)/(1-\varepsilon))$ on $[\varepsilon\lambda_0, \lambda_0]$. That is the
existing `isUniformApproxOn_chebyshevResidual`, reflected so it controls
$[0, (1-\varepsilon)\lambda_0]$. A private split of the integral above and below
$(1-\varepsilon)\lambda_0$ follows: the part above has Rayleigh quotient at least
$(1-\varepsilon)\lambda_0$ and mass at least $\mu(\{\lambda_0\})$. The Kuczyński–Woźniakowski
bound uses `evenChebyshevFilter` and the filter-mean lemma of KS6.

**`PowerIteration.lean`** (about 250 lines):

```lean
/-- **The power method, gapped**: ... $|c - \rho(\mathbf{A}^q\mathbf{b})| \le
(|c| + r)(r/|c|)^{2q}\tan^2\angle(\mathbf{b}, E_c)$ ... [TrefethenBau1997, Theorem 27.1];
[GolubVanLoan2013, Theorem 8.2.1] (locators from the quarry). -/
theorem Matrix.IsHermitian.abs_sub_rayleighQuotient_pow_mulVec_le {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {c r : ℝ} (hrc : r < |c|) (hs : spectrum ℝ A ⊆ Set.Icc (-r) r ∪ {c})
    (b : n → 𝕜) (hb : 0 < (spectralMeasure A b).real {c}) (q : ℕ) :
    |c - rayleighQuotient A (A ^ q *ᵥ b)| ≤ (|c| + r) * (r / |c|) ^ (2 * q) * spectralTangentSq A b c

/-- **Kuczyński–Woźniakowski, deterministic power step** ...
[KuczynskiWozniakowski1992, Theorem 4.1] (locator from the quarry, to check). -/
theorem Matrix.PosSemidef.eigenvalue_sub_rayleighQuotient_pow_mulVec_le {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) (b : n → 𝕜) (hb : 0 < (spectralMeasure A b).real {eigenvalue A 0})
    (q : ℕ) :
    eigenvalue A 0 - rayleighQuotient A (A ^ q *ᵥ b) ≤
      eigenvalue A 0 * Real.log (1 + spectralTangentSq A b (eigenvalue A 0)) / (2 * q + 1)

theorem Matrix.IsHermitian.abs_sub_rayleighQuotient_inv_pow_mulVec_le {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {s : Set ℝ} {c σ d D : ℝ} (hs : spectrum ℝ A ⊆ s ∪ {c})
    (hσc : σ ≠ c) (hd : 0 < d) (hds : ∀ x ∈ s, d ≤ |x - σ|)
    (hD : ∀ x ∈ s, |x - c| ≤ D) (b : n → 𝕜) (hb : 0 < (spectralMeasure A b).real {c}) (q : ℕ) :
    |c - rayleighQuotient A ((A - σ • (1 : Matrix n n 𝕜))⁻¹ ^ q *ᵥ b)| ≤
      D * (|c - σ| / d) ^ (2 * q) * spectralTangentSq A b c
-- optional (Q1): inverse iteration, [TrefethenBau1997, Theorem 27.2] (from the quarry)
```

The constant in the KW power step, $\log(1 + \tan^2)/(2q + 1)$, is read off the quarry's expected
bound $(\log 2N + 2)/(2q + 1)$, which is this bound integrated against `GaussianLogOverlap`'s
first moment. The quarry proves the deterministic step privately. I saw only its statement, so
the constant is to confirm at the skeleton. The scalar fact behind it is $1 - t \le -\log t$
together with concavity of $y\log(1/y)$.

**Subspace iteration (optional, KS5c).** The angle contraction
$\|\tan\Theta(\mathbf{U}, \mathbf{A}^k\mathbf{\Omega})\| \le (\beta/\alpha)^k
\|\tan\Theta(\mathbf{U}, \mathbf{\Omega})\|$ in the library's `tangentMatrix`, from the exact
identity `tangentMatrix U (A ^ k * Ω) = A ^ k * tangentMatrix U Ω * (Uᴴ * A * U)⁻¹ ^ k` for an
invariant frame:

```lean
theorem HasOrthonormalCols.specNorm_tangentMatrix_pow_mul_le {U : Matrix n r 𝕜}
    (hU : HasOrthonormalCols U) {A : Matrix n n 𝕜} {d : r → ℝ}
    (hAU : A * U = U * Matrix.diagonal (fun i => ((d i : ℝ) : 𝕜))) {α β : ℝ} (hα : 0 < α)
    (hd : ∀ i, α ≤ |d i|) (hβ : specNorm (A * (1 - U * Uᴴ)) ≤ β) {Ω : Matrix n r 𝕜}
    (hΩ : IsUnit (Uᴴ * Ω)) (k : ℕ) :
    specNorm (tangentMatrix U (A ^ k * Ω)) ≤ (β / α) ^ k * specNorm (tangentMatrix U Ω)
-- [Saad2011, Theorem 5.2]; [GolubVanLoan2013, Theorem 8.2.2] (from the quarry)
```

Subspace-iteration *eigenvalue* bounds are deferred (§8): they need per-index Ritz bounds, which
the filter theorem does not give.

### KS6. Random start (Gaussian), over ℝ

**Polynomial addition** (`Polynomial/Chebyshev/EvenFilter.lean`, new, about 300 lines; a port of
the quarry's `Polynomial.Chebyshev.EvenChebyshevFilter`, plus the filter-mean lemmas of
`Estimation.Spectral.RandomStartLanczos` restated for a measure):

```lean
/-- The even Chebyshev filter $U_{2k}(\sqrt{x})/(2k + 1)$, a polynomial of degree $k$ in $x$. -/
noncomputable def evenChebyshevFilter (k : ℕ) : ℝ[X]

theorem natDegree_evenChebyshevFilter_le (k : ℕ) : (evenChebyshevFilter k).natDegree ≤ k
theorem eval_evenChebyshevFilter_one (k : ℕ) : (evenChebyshevFilter k).eval 1 = 1
theorem abs_eval_evenChebyshevFilter_le_one (k : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |(evenChebyshevFilter k).eval x| ≤ 1
theorem one_sub_mul_eval_evenChebyshevFilter_sq_le (k : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (1 - x) * (evenChebyshevFilter k).eval x ^ 2 ≤ 1 / (2 * k + 1) ^ 2
-- (the exact quarry form to be copied at the skeleton)

theorem exists_natDegree_le_one_sub_integral_mul_div_le {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : ∀ᵐ x ∂ν, x ∈ Set.Icc (0 : ℝ) 1) (h1 : 0 < ν.real {1}) {q : ℕ} (hq : 1 ≤ q) :
    ∃ p : ℝ[X], p.natDegree ≤ q ∧ p.eval 1 = 1 ∧
      1 - (∫ x, x * p.eval x ^ 2 ∂ν) / (∫ x, p.eval x ^ 2 ∂ν) ≤
        4 * (1 + Real.log (ν.real Set.univ / ν.real {1}) / Real.log 2) ^ 2 / q ^ 2
-- the KW filter step (quarry `exists_polynomial_filter_mean_le_log_sq`, weights → a measure)
```

**Additions below Estimation.** All are short. The first three are needed by the integrability
and almost-sure claims of the headlines (`GaussianLogOverlap.lean` has no `∀ᵐ` statement).

```lean
-- Probability/Distributions/Gaussian.lean, beside `hasLaw_dotProduct_of_hasLaw_gaussianVector`
theorem ae_dotProduct_ne_zero_of_hasLaw_gaussianVector {g : Ω → n → ℝ}
    (hg : HasLaw g (gaussianVector n) μ) {u : n → ℝ} (hu : ‖WithLp.toLp 2 u‖ = 1) :
    ∀ᵐ ω ∂μ, u ⬝ᵥ g ω ≠ 0
-- proof: u ⬝ g has law gaussianReal 0 1 (`hasLaw_dotProduct_of_hasLaw_gaussianVector`), which
-- has no atoms. The reviewer's suggested source `ae_eval_ne_zero_of_ne_zero`
-- (RandomMatrix/Gaussian/Rank.lean:113) also gives it, but RandomMatrix is layer 2 and
-- Probability cannot import it (P1); if that route is preferred, the lemma lives in Rank.lean.

-- Probability/Measurability/Matrix.lean, beside `measurable_eigenvalue`
theorem measurable_quadForm (A : Matrix n n 𝕜) : Measurable fun x : n → 𝕜 => quadForm A x
theorem measurable_rayleighQuotient (A : Matrix n n 𝕜) :
    Measurable fun x : n → 𝕜 => rayleighQuotient A x

-- Probability/Measurability/Krylov.lean (planned by PORT_KRYLOV D12)
theorem measurable_krylovMatrix (A : Matrix n n 𝕜) (q : ℕ) :
    Measurable fun b : n → 𝕜 => krylovMatrix A b q

-- Matrix/Spectral/Eigenvalues.lean: the D9 bridge between projector and frame forms
theorem HasOrthonormalCols.eigenvalue_mul_mul_conjTranspose {U : Matrix n r 𝕜}
    (hU : HasOrthonormalCols U) {T : Matrix r r 𝕜} (hT : T.PosSemidef) (k : ℕ) :
    eigenvalue (U * T * Uᴴ) k = eigenvalue T k
```

**`Estimation/Spectral/RandomStart.lean`** (new, about 400 lines). Context:
`{Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : Type*} [Fintype n] [DecidableEq n]
{g : Ω → n → ℝ} {A : Matrix n n ℝ}`.

```lean
/-- The random-start power-method factor
<!-- value randomStartPowerBound N q -->$(\log(2N) + 2)/(2q + 1)$. Source: Kuczyński and
Woźniakowski's printed constant (locator to check) ... gap ... -/
noncomputable irreducible_def randomStartPowerBound (N q : ℕ) : ℝ :=
  (Real.log (2 * N) + 2) / (2 * q + 1)

noncomputable irreducible_def randomStartLanczosBound (N q : ℕ) : ℝ :=
  4 * ((Real.log (2 * N) + 2 + Real.log 2) ^ 2 + 4) / (Real.log 2 ^ 2 * q ^ 2)

theorem randomStartPowerBound_nonneg (N q : ℕ) : 0 ≤ randomStartPowerBound N q
theorem randomStartLanczosBound_nonneg (N q : ℕ) : 0 ≤ randomStartLanczosBound N q
theorem randomStartPowerBound_le {N q : ℕ} (hN : 2 ≤ N) (hq : 1 ≤ q) :
    randomStartPowerBound N q ≤ 3 * Real.log N / q
-- the quarry's coarse form `integral_powerRayleighRelativeError_le_three_log_div`

/-- **Random-start power method**: for positive semidefinite real $\mathbf{A}$ and a standard
Gaussian start $\mathbf{g}$, after $q$ multiplications, <!-- value randomStartPowerBound
\lvert n \rvert q -->
$$\mathbb{E}\bigl[\lambda_0(\mathbf{A}) - \rho_{\mathbf{A}}(\mathbf{A}^q\mathbf{g})\bigr] \le
\frac{\log(2\lvert n\rvert) + 2}{2q + 1}\,\lambda_0(\mathbf{A})\,,$$
for every $q$ (including $0$), every dimension, repeated top eigenvalues and $\mathbf{A} = 0$;
no gap. The bound $\lambda_0(\mathbf{A})$ itself holds trivially. Asymptotic form:
`NLAlib.exists_forall_integral_eigenvalue_sub_rayleighQuotient_pow_mulVec_le_of_hasLaw_gaussianVector`.
[MartinssonTropp2020, Theorems 6.1, 6.2] (verified per PORT_KRYLOV §9; which is the power method
to check); [KuczynskiWozniakowski1992, Theorem 4.1] (locator to check); there as a relative error
with a different constant; constants composed here.
Result: random-start-power -/
theorem integral_eigenvalue_sub_rayleighQuotient_pow_mulVec_le_of_hasLaw_gaussianVector
    (hg : HasLaw g (gaussianVector n) μ) (hA : A.PosSemidef) (q : ℕ) :
    ∫ ω, (eigenvalue A 0 - rayleighQuotient A (A ^ q *ᵥ g ω)) ∂μ ≤
      randomStartPowerBound (Fintype.card n) q * eigenvalue A 0

/-- **Random-start Lanczos** ... largest Ritz value of $\mathcal{K}_{q+1}(\mathbf{A},
\mathbf{g})$, in the projector form ... Result: random-start-lanczos -/
theorem integral_eigenvalue_sub_eigenvalue_rangeProjector_mul_mul_le_of_hasLaw_gaussianVector
    (hg : HasLaw g (gaussianVector n) μ) (hA : A.PosSemidef) {q : ℕ} (hq : 1 ≤ q) :
    ∫ ω, (eigenvalue A 0 -
        eigenvalue (rangeProjector (krylovMatrix A (g ω) (q + 1)) * A *
          rangeProjector (krylovMatrix A (g ω) (q + 1))) 0) ∂μ ≤
      randomStartLanczosBound (Fintype.card n) q * eigenvalue A 0

theorem integrable_eigenvalue_sub_rayleighQuotient_pow_mulVec_of_hasLaw_gaussianVector
    (hg : HasLaw g (gaussianVector n) μ) (A : Matrix n n ℝ) (q : ℕ) :
    Integrable (fun ω => eigenvalue A 0 - rayleighQuotient A (A ^ q *ᵥ g ω)) μ
-- and the Lanczos twin; bounded and measurable

/-- ... "$O(\log(\lvert n\rvert)/\varepsilon)$ multiplications suffice" ...
Asymptotic: integral_eigenvalue_sub_rayleighQuotient_pow_mulVec_le_of_hasLaw_gaussianVector -/
theorem exists_forall_integral_eigenvalue_sub_rayleighQuotient_pow_mulVec_le_of_hasLaw_gaussianVector :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {n : Type} [Fintype n]
      [DecidableEq n] {g : Ω → n → ℝ}, HasLaw g (gaussianVector n) μ →
      ∀ {A : Matrix n n ℝ}, A.PosSemidef → ∀ (ε : ℝ) (q : ℕ), 0 < ε →
        C * Real.log (2 * Fintype.card n) / ε ≤ q →
          ∫ ω, (eigenvalue A 0 - rayleighQuotient A (A ^ q *ᵥ g ω)) ∂μ ≤ ε * eigenvalue A 0

theorem exists_forall_integral_eigenvalue_sub_eigenvalue_rangeProjector_mul_mul_le_of_hasLaw_gaussianVector :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {n : Type} [Fintype n]
      [DecidableEq n] {g : Ω → n → ℝ}, HasLaw g (gaussianVector n) μ →
      ∀ {A : Matrix n n ℝ}, A.PosSemidef → ∀ (ε : ℝ) (q : ℕ), 0 < ε →
        C * Real.log (2 * Fintype.card n) / √ε ≤ q →
          ∫ ω, (eigenvalue A 0 -
              eigenvalue (rangeProjector (krylovMatrix A (g ω) (q + 1)) * A *
                rangeProjector (krylovMatrix A (g ω) (q + 1))) 0) ∂μ ≤ ε * eigenvalue A 0
```

The proofs compose, pointwise in $\omega$, four facts:
1. The deterministic step from KS5.
2. $\mu_{\mathbf{A},\mathbf{g}}(\{\lambda_0\}) \ge \langle\mathbf{u}, \mathbf{g}\rangle^2$ for a
   unit eigenvector (KS1), hence $\log(1 + \tan^2) \le \log(\|\mathbf{g}\|^2/\langle\mathbf{u},
   \mathbf{g}\rangle^2)$ on the full-measure event $\langle\mathbf{u}, \mathbf{g}\rangle \ne 0$.
3. The frame bridge, with $\mathbf{P} = \mathbf{Q}\mathbf{Q}^{\mathsf{H}}$ for
   `exists_hasOrthonormalCols_range_eq_krylovSpace` and
   `HasOrthonormalCols.eigenvalue_mul_mul_conjTranspose`.
4. `integral_log_norm_sq_div_sq_le_of_hasLaw_gaussianVector` (power) or `…_sq_sq_le_…` (Lanczos),
   with $\mathbb{E}(1 + L/\log 2)^2 \le ((T + 2 + \log 2)^2 + 4)/(\log 2)^2$.

The integrands are measurable by `measurable_rayleighQuotient` (power) and by
`measurable_krylovMatrix`, `measurable_rangeProjector` and `measurable_eigenvalue` (Lanczos); the
event $\langle\mathbf{u}, \mathbf{g}\rangle \ne 0$ has full measure by
`ae_dotProduct_ne_zero_of_hasLaw_gaussianVector`. Following N9, the law hypothesis comes first and is a suffix, so the
theorems stay in the root namespace. Tail forms are deferred (§8).

## 5. Consumers

| Item | Consumers (later stage or layer, and the form they use) |
|---|---|
| `spectralMeasure` and its integral lemmas | KS3b (the Lanczos rule is one), KS5 (the filter theorem, `spectralTangentSq`), KS6. Estimation: SLQ's unbiasedness, $\mathbb{E}_{\mathbf{b}}\int f\,d\mu_{\mathbf{A},\mathbf{b}} = \operatorname{tr} f(\mathbf{A})$ for isotropic $\mathbf{b}$ (one line from `IsIsotropic.integral_quadForm`), and KPM's Chebyshev moments. Probability: M1. Krylov-Sharpness's "vectors with a prescribed spectral measure" (an existing theorem, restatable) |
| `empiricalSpectralMeasure` | M1 (Probability/Moments, exact and noisy spectral-distribution bounds); SLQ and KPM spectral-density approximation (Estimation, [ChenTrogdonUbaru2022]). No Lean consumer this round, but the brief asks for it and the Jackson note §4 places it |
| `MatchesMoments`, M0 | KS2b, KS3b; SLQ spectrum approximation in Lipschitz test functions (M0 with the KS4 Jackson lemma: $\pi L(a'-a)/(2q+1)$-type bounds); M1; KPM |
| `IsOrthogonalPolynomial`, `interpolatoryQuadrature` | KS3c; M1 for discrete measures; later Gauss–Radau and Lobatto bounds (KS7) |
| C6 (KS3a) | SLQ for $\operatorname{tr} f(\mathbf{A})$ (Estimation/Trace: the deterministic split into Girard–Hutchinson error plus $2\varepsilon\|\mathbf{\Omega}\|_{\mathsf{F}}^2/m$, [MartinssonTropp2020, §6.6, Algorithm 6]); Hutch++ with Lanczos (Krylov-aware trace estimation, block round) |
| `lanczosQuadrature` (KS3b) | SLQ spectral-density output, $m^{-1}\sum_j\mathsf{lanczosQuadrature}(\mathbf{A}, \boldsymbol{\omega}_j, q)$; its Wasserstein-type error through M0 |
| KS4 rates | Matrix-function users (actions of $e^{t\mathbf{A}}$, $\log$, $\sqrt{\cdot}$); SLQ degree budgets; the explorer's Rates page |
| KS5 bounds | KS6; spectral-norm estimation (normalising Hutch++ and XTrace, condition estimation); later block Lanczos for eigenvalues; Krylov-Sharpness's planned lower bounds for Lanczos (§12 there) |
| KS6 | The Rates page. Possibly LowRank: adaptive-rank and stopping rules that need a $\|\mathbf{A}\|_2$ estimate. No current file |

## 6. Files, placement, imports, order

| File | New / addition | Content | Lines |
|---|---|---|---|
| `Matrix/Spectral/SpectralMeasure.lean` | new | `spectralMeasure`, `empiricalSpectralMeasure`, `spectralTangentSq`, about 22 theorems, the filter theorem | 550 |
| `Matrix/Spectral/Eigenvalues.lean` | addition | `HasOrthonormalCols.eigenvalue_mul_mul_conjTranspose` | +60 |
| `Polynomial/Orthogonal/Moments.lean` | new | `MatchesMoments` and API, M0, the optional `measureT` bridge | 220 |
| `Polynomial/Orthogonal/Basic.lean` | new | `IsOrthogonalPolynomial`, `mono`, moment invariance | 100 |
| `Polynomial/Orthogonal/Gauss.lean` | new | `interpolatoryQuadrature`, exactness, weights | 250 |
| `Polynomial/Approximation/Jackson.lean` | addition | Jackson on $[a, b]$ | +60 |
| `Polynomial/Chebyshev/EvenFilter.lean` | new | `evenChebyshevFilter`, the filter-mean lemma | 300 |
| `Krylov/Functions/Quadrature.lean` | new (designed in K2 as C6) | C6, `lanczosQuadrature` and bridges, KS4 quadrature rates, KS3c | 450 |
| `Krylov/Functions/LanczosFA.lean` | addition | KS4 Lanczos-FA rates | +120 |
| `Krylov/Eigenvalues/Ritz.lean` | new | KPS, gap-free, KW Lanczos step | 450 |
| `Krylov/Eigenvalues/PowerIteration.lean` | new | power (gapped, KW), optional inverse and subspace iteration | 250 |
| `Probability/Measurability/Krylov.lean` | addition | `measurable_krylovMatrix` | +30 |
| `Probability/Measurability/Matrix.lean` | addition | `measurable_quadForm`, `measurable_rayleighQuotient` | +20 |
| `Probability/Distributions/Gaussian.lean` | addition | `ae_dotProduct_ne_zero_of_hasLaw_gaussianVector` | +20 |
| `Estimation/Spectral/RandomStart.lean` | new | named bounds, two headlines, integrability, asymptotic forms | 400 |

Total: about 3,300 lines, or about 3,000 without the optional pieces (inverse iteration,
KS5c).

**Placement** (CONTRIBUTING §8 item 5). Every declaration outside a new file of its own topic,
with its home and the reason:

| Declaration | Home | Reason |
|---|---|---|
| filter theorem `abs_sub_rayleighQuotient_cfc_mulVec_le` | `Matrix/Spectral/SpectralMeasure.lean` | its subject is the Rayleigh quotient of $g(\mathbf{A})\mathbf{b}$ as a ratio of spectral integrals, with no Krylov vocabulary; KS5 consumes it |
| `spectralTangentSq` | SpectralMeasure | a quantity of the spectral measure |
| `HasOrthonormalCols.eigenvalue_mul_mul_conjTranspose` | `Matrix/Spectral/Eigenvalues.lean` | eigenvalues under a frame conjugation, beside `HasOrthonormalCols.eigenvalue_eq_of_eq_mul_diagonal_mul_conjTranspose` |
| `MatchesMoments`, M0 | `Polynomial/Orthogonal/Moments.lean` | **flag**: the Jackson note §4 had moment comparison in `Probability/Moments`; Krylov must conclude the predicate and cannot import Probability (D12); M1 stays in Probability |
| Jackson on $[a, b]$ | `Polynomial/Approximation/Jackson.lean` | beside the $[-1, 1]$ theorem, as the analytic file has its interval form |
| `evenChebyshevFilter` and the filter-mean lemma | `Polynomial/Chebyshev/EvenFilter.lean` | a scalar polynomial and a scalar measure inequality (P9-exempt, P11); the quarry had the lemma in Estimation |
| KS4 rates | `LanczosFA.lean`, `Quadrature.lean` | corollaries of each file's topic theorem, in the same file (§5.2 "general form first") |
| KW deterministic steps | `Krylov/Eigenvalues/` | deterministic; the quarry had them in Estimation; Estimation keeps only the composition |
| `measurable_krylovMatrix` | `Probability/Measurability/Krylov.lean` | planned there by D12 |
| `measurable_quadForm`, `measurable_rayleighQuotient` | `Probability/Measurability/Matrix.lean` | measurability of matrix quantities, beside `measurable_eigenvalue` |
| `ae_dotProduct_ne_zero_of_hasLaw_gaussianVector` | `Probability/Distributions/Gaussian.lean` | a fact about the Gaussian vector law, beside the law of $\langle\mathbf{u}, \mathbf{g}\rangle$ |
| random-start theorems | `Estimation/Spectral/RandomStart.lean` | D12 (approved); **flag** P10, because the vocabulary is layer 1 (SD7) |

Open flags: the two marked above.

**Imports.**
- `SpectralMeasure` imports `Matrix/Functions/HermitianCalculus`, `Matrix/Functions/Polynomial`,
  `Matrix/Spectral/Eigenvalues`, `Matrix/Basic/QuadForm` and Mathlib's
  `MeasureTheory/Integral/Bochner/SumMeasure`, `Measure/Dirac` and `Measure/WithDensity`.
- `Polynomial/Orthogonal/*` import Mathlib only (`LinearAlgebra/Lagrange`, the Bochner integral,
  `Chebyshev/Orthogonality` and `ChebyshevGauss` for the bridges) and
  `NLAlib.ForMathlib.Topology.UniformSpace.UniformApproximation` for `Metric.IsUniformApproxOn`.
  P11 holds.
- `Quadrature.lean` imports `LanczosFA`, `SpectralMeasure` and `Polynomial/Orthogonal/Moments`
  (and `Gauss` for KS3c).
- `Ritz` and `PowerIteration` import `SpectralMeasure`, `Krylov/Basic/Grade`,
  `Polynomial/Chebyshev/Residual` and `EvenFilter`.
- `RandomStart` imports `Ritz`, `PowerIteration`, `GaussianLogOverlap` and
  `Measurability/Krylov`.

**Order and commit checkpoints.** This is one file per proof agent, at most two at once.
1. **KS3a**: C6. It is approved and independent, so it can start now.
2. **KS4a**: the two analytic corollaries. They are independent and can run beside 1.
3. **KS4b**: Jackson on $[a, b]$, then the two Lipschitz corollaries.
4. **KS1**: `SpectralMeasure.lean`. Commit, and the maintainer can review the carrier in use.
5. **KS2a**: `Moments.lean`. It is independent of KS1 and can run beside 4.
6. **KS3b**: the measure form of the Lanczos rule.
7. **KS5**: `Ritz.lean`, then `PowerIteration.lean`. Commit.
8. **KS6**: `EvenFilter.lean`, the four small additions, then `RandomStart.lean`. Commit.
9. **KS2b**, then **KS3c**. KS2b is independent of everything in Krylov and can run
   whenever a slot is free after KS2a.

## 7. Material (quarry `atlas/declarations.json`; signatures and docstrings only, no proof bodies)

I read these modules: `Krylov.Quadrature.{SpectralMeasure, GaussQuadrature, Jacobi,
JacobiFraction, AnalyticQuadrature, LipschitzQuadrature, ExponentialQuadrature}`,
`Krylov.Spectral.{Ritz, PowerMethod, MeasurableRitz, SubspaceIteration,
CharacteristicPolynomial}`, `Estimation.Spectral.{RandomStartPower, RandomStartLanczos}`,
`Estimation.Quadrature.SLQ*` (for consumers), `Polynomial.Chebyshev.{EvenChebyshevFilter,
Growth}` and `LowRank.PolynomialMethods.PolynomialFilter`. All the entries I used are proved
(`sorry = False`), except `sq_overlapTangentNorm_replicateCol_eq_overlapTangentSq` (a scaffold).

**Reused as mathematics**, restated in the library's vocabulary:
- `integral_spectralMeasure` and its polynomial, moment and quadratic-form forms. These are kept
  over `RCLike` with a basis-free definition.
- `dotProduct_aeval_mulVec_eq_of_degree_lt_two_mul` becomes C6.
- `abs_dotProduct_cfc_mulVec_sub_le_of_degree_lt_two_mul` becomes C6's error bound.
- The Golub–Welsch lemmas `cfc_T_apply_zero_zero`, `sum_sq_eigenvectorBasis_T_apply_zero` and
  `dotProduct_cfc_T_mulVec_eq_sum` become `integral_lanczosQuadrature_succ` and
  `lanczosQuadrature_succ_eq_sum`.
- `integral_eval_charpoly_mul_eq_zero` becomes KS3c, with the nodal polynomial of the Ritz values
  in place of `charpoly`. They are equal below the grade, but the nodal form needs no
  `LanczosDecomp`.
- The analytic, Lipschitz and exponential quadrature bounds become KS4. They are re-derived from
  the library approximants; the Lipschitz constant changes from $\pi L(c-a)/(4q)$ (prototype, sharp
  Jackson) to $\pi L(a'-a)/(2q+3)$ (the library's constructive Jackson, about 2 times worse).
- KPS (`eigenvalues_sub_eigenvalues_transpose_mul_mul_le`), the gap-free bound
  (`exists_eigenvalues_transpose_mul_mul_ge`) and the Chebyshev eigenvector angle
  (`exists_mem_krylovSpace_overlapTangentSq_le`) become KS5 through the filter theorem.
- `overlapTangentSq_powerIterate_le`, `abs_rayleighQuotient_powerIterate_sub_le` and the inverse
  iteration pair become KS5's power and inverse bounds.
- The random-start expected bounds and their constants become KS6.
- `one_sub_filter_mean_le_four_div_sq`, `exists_polynomial_filter_mean_le_log_sq` and the
  `EvenChebyshevFilter` file become KS6's Polynomial file. The weights become a measure.
- `overlapTangentNorm_pow_mul_le` becomes KS5c in `tangentMatrix`.

**Deliberately not reproduced**, with the reason:
- `spectralMeasure hA v` is proof-carrying, real-only and basis-dependent ("repeated atoms").
  Replaced by SD1(a).
- `LanczosDecomp` and `ArnoldiDecomp.restrict` are bundles that PORT_KRYLOV D5 dropped. The
  Lanczos polynomials `LanczosDecomp.poly`, `X_mul_poly` (three-term recurrence),
  `sub_mul_sum_eval_poly_mul` (Christoffel–Darboux) and `charpoly_restrict_T_mul_poly_zero` are
  deferred to KS7, since no consumer was found.
- The interlacing of $\mathbf{T}_{q'}$ in $\mathbf{T}_q$ (`eigenvalues₀_restrict_T_le` and its
  lower half) is not a gap: $\mathbf{T}_{q'}$ is a compression of $\mathbf{T}_q$, so Poincaré
  separation (`eigenvalue_conjTranspose_mul_mul_le` and its lower half) already gives it.
- `jacobiMatrix`, `jacobiFraction` and the resolvent continued fraction have no consumer;
  deferred to KS7. Their name collides with Mathlib's `Algebra.PreSubmersivePresentation.jacobiMatrix`
  in another namespace, which would matter upstream.
- `overlapTangentSq` and `tanSqAngle` were two spellings of one quantity, an eigenvector-basis
  quantity, real-only and proof-carrying. Replaced by `spectralTangentSq` (SD6).
- `powerIterate`, `powerStep`, `inverseIterate`: names for powers (PORT_KRYLOV §1.11).
- `ritzValues`, `lanczosRitzValue` and the rational-supremum measurability: replaced by D9's
  projector form and `measurable_eigenvalue`.
- `exists_degree_le_eval_eq_one_abs_eval_le` (the amplifier) and
  `pow_div_two_le_eval_T_real_one_add_two_mul`: replaced by the reflected `chebyshevResidual` and
  the existing ForMathlib growth lemmas.
- `measurePreserving_eigenvectorBasis_dotProduct_gaussianVector` and
  `ae_eigenvectorBasis_dotProduct_ne_zero_gaussianVector`: `GaussianLogOverlap.lean` already
  works with any unit vector, so no eigenbasis rotation is needed.
- `Krylov.Spectral.CharacteristicPolynomial` (the monic minimality of the Ritz polynomial): no
  consumer. `Krylov-Sharpness.md` took the Galerkin route instead.
- `lanczosRayleighRelativeError` and `powerRayleighRelativeError`: relative errors with a junk
  value at $\mathbf{A} = 0$. Replaced by absolute errors bounded by a multiple of $\lambda_0$,
  which avoids the junk value.

## 8. Deferred, with the missing infrastructure recorded (defer-complex-material rule)

1. **KS7, the orthogonal-polynomial structure theory.** This is the Jackson note's OP1 and the
   rest of OP2. It covers existence and real-rootedness of the degree-$n$ orthogonal polynomial
   for a measure with at least $n$ support points, uniqueness of the monic one, the three-term
   recurrence and normalisation [Gautschi2004, Theorems 1.27, 1.29], Christoffel–Darboux
   [Gautschi2004, Theorem 1.32], the canonical Gram–Schmidt polynomials (SD4(c)), `jacobiMatrix`,
   the continued fraction, and interlacing of zeros [Gautschi2004, Theorems 1.19, 1.20]. I found
   no consumer this round. It needs nothing missing: the work is about 600 lines of scalar
   algebra, and the 2026-10-17 maintainer note (PORT_KRYLOV D6) records that the layer is wanted.
   Recommendation: schedule it after KS3c, when the first consumer appears.
2. **The simple-eigenvalue theory of unreduced Hermitian tridiagonal matrices** (nonzero first
   eigenvector entries; gap survey M4). No stage here needs it: KS3c proves the Ritz-value count
   and the positivity of the Lanczos weights below the grade from the grade alone. It stays
   recorded for consumers that work with $\mathbf{T}$ as a matrix, not as a rule.
3. **Gauss–Radau and Lobatto bounds, and the sign of the Gauss error for $f$ with sign-definite
   derivatives.** They need the Hermite interpolation remainder (gap survey P1), which is missing.
4. **Exponential and monomial approximants** (Poly4, missing). Without them there are no
   $e^{-x}$ or $x^s$ Lanczos-FA or quadrature rates with the prototype's constants.
5. **KPM.** It needs M1 and the noisy coefficient bound J1 (Jackson note §§3–4). Both are
   unimplemented.
6. **SLQ itself** (`slq`, its tails, the spectral-density form). Not in the brief's scope: it is
   an Estimation design using KS3 (§5).
7. **Tail forms of the random-start bounds.** The quarry has none, and Markov on the expectation
   is a one-line corollary when wanted. Deferred until a consumer asks.
8. **Block Lanczos eigenvalue bounds** belong to the block round. **Subspace-iteration
   eigenvalue bounds** need per-index Ritz bounds.
9. **The sharper Jackson constant** ($\pi L/(2(N + 1))$, the sawtooth route) would halve the
   Lipschitz rates (Jackson note §7; outstanding).
10. **From the consolidation round.** Jackson's theorem on an interval $[a, b]$ is new
   mathematics and is scheduled here, in KS4 (`exists_degree_le_isUniformApproxOn_Icc_of_lipschitzOnWith`).
   The three-term recurrence of `chebyshevResidual` (gap survey P6) is **not needed** by any
   stage of this note: KPS and the gap-free bound use only its uniform bound
   (`isUniformApproxOn_chebyshevResidual`, `…_two_mul_pow`) and its value at $0$. It stays with
   its consumers (Chebyshev semi-iteration, LSRN).

## 9. Literature

The following are in `docs/references.bib`, with the locators I saw:
- `GolubMeurant2010`: Theorem 6.6 (Gauss exactness), Chs. 4, 6, 7, from the quarry.
- `Saad2011`: Theorem 6.4 and §6.6.1 (KPS), Theorem 5.2 (subspace iteration), from the quarry.
  PORT_KRYLOV §9 lists Theorem 6.4 as to verify.
- `TrefethenBau1997`: Theorems 27.1, 27.2, from the quarry.
- `GolubVanLoan2013`: Theorems 8.2.1, 8.2.2, from the quarry.
- `MuscoMusco2015`: the library cites Theorem 10 (proof), Lemmas 2, 5, 9 and Algorithm 2 (block
  method); the locator for the single-vector gap-free bound is to check.
- `KuczynskiWozniakowski1992`: Theorems 4.1, 4.2, from the quarry; PORT_KRYLOV §9 lists them as
  to verify.
- `MartinssonTropp2020`: Theorems 6.1, 6.2 and §6.6, Algorithm 6, verified per PORT_KRYLOV §9.
- `Saad1992`: Theorem 3.4, from the quarry.
- `Trefethen2019`: Theorem 8.2, from the quarry.
- `ChenTrogdonUbaru2022`: Appendix C, Theorem 38, as the library already cites it (three times,
  in `Polynomial/Approximation/Jackson*.lean`, with the label "Appendix C, Theorem 38"). The quarry's
  "Thm 2.1" and "Lem. 2.2" refer to another version: locator to check.
- `Parlett1998`: Theorem 11.4.1, from the quarry.

New key: `Gautschi2004` (*Orthogonal Polynomials: Computation and Approximation*, Oxford, 2004).
The Jackson/moments note §2 verified Theorems 1.19, 1.20, 1.27, 1.29, 1.32, 1.45 and 1.46; the
metadata is to confirm when the key is added. No Chen–Persson manuscript is cited.

New result ids: `spectral-measure`, `lanczos-gauss-quadrature` (the quarry atlas id, reused),
`gauss-quadrature`, `kaniel-paige-saad`, `ritz-value-gap-free`, `power-iteration`,
`random-start-power`, `random-start-lanczos`, and `lanczos-fa-uniform-bound` for the KS4
corollaries (existing id). Each is to be checked against the explorer's literature map for
near-duplicates (R2).

## 10. Open questions (not costly; recommendation each)

- **Q1.** Should inverse iteration and the subspace-iteration angle (KS5c) be included? Inverse
  iteration: yes, it is one corollary of the filter theorem, about 30 lines. KS5c: only if the
  maintainer wants deterministic subspace iteration now, since its only consumer (LowRank's RSI)
  has its own proof.
- **Q2.** Should there be a separate measure-form error theorem for Lanczos quadrature? No:
  M0 plus the bridges gives it in three lines, and C6 is the scalar form.
- **Q3.** Should Mathlib's Chebyshev–Gauss be bridged (`matchesMoments_measureT`)? Yes. It is
  cheap and checks that SD2's predicate fits Mathlib's existing statement.
- **Q4.** (Settled by review: KS3c is required, not optional. It carries the positivity of the
  Lanczos weights below the grade, §8 item 2.)
- **Q5.** Should C6's approved name gain the `cfc_mulVec` tokens
  (`norm_star_dotProduct_cfc_mulVec_sub_lanczosFA_le_of_isUniformApproxOn`)? Yes, for the
  grammar's sibling consistency. The statement is unchanged.
- **Q6.** The directory name `Polynomial/Orthogonal/` versus `Polynomial/Quadrature/`: Orthogonal,
  because Gauss quadrature is part of that theory and `Moments.lean` is its first file.

**Not settled here.**
- The exact constant of the KW deterministic power step. It was read off the quarry's integrated
  bound; the proof body was not read.
- The `MuscoMusco2015` single-vector locator, and CTU's locator for Lanczos-quadrature exactness.
- Nothing here has been elaborated.

## Changes during the skeleton (2026-10-22)

The skeleton is on `krylov/spectral` (worktree `nlalib-block`, from `375e005`). Every declaration
of §§2–4 for KS1 to KS6 is stated with its final docstring and elaborates; definitions are written
out in full; theorems not listed under "Proved now" are `sorry`. Changes against the note:

* **Files.** As §6, except that `HasOrthonormalCols.eigenvalue_mul_mul_conjTranspose` is in
  `Matrix/Spectral/SingularValues.lean`, not `Matrix/Spectral/Eigenvalues.lean`. Its proof is two
  lines from the private `eigenvalue_eq_of_X_pow_mul_charpoly_eq` there (with Mathlib's
  `Matrix.charpoly_mul_comm'`), which `Eigenvalues.lean` cannot see, and `Eigenvalues.lean` is
  below the positive semidefinite eigenvalue API it needs. **Flag** (P10): intended home
  `Eigenvalues.lean`, once the charpoly helper is public in a file both can import. The theorem
  takes `[DecidableEq m]` for its frame (`HasOrthonormalCols` needs it) and is proved, so
  `SingularValues.lean` stays sorry-free. KS5c (subspace iteration) is not included (Q1, as
  recommended); inverse iteration is.
* **T13, `ae_mem_Icc_spectralMeasure`.** The note's
  `Matrix.IsHermitian.ae_mem_Icc_spectralMeasure` does not use the Hermitian hypothesis (the
  measure is $0$ off Hermitian), so it is the root-namespace
  `ae_mem_Icc_spectralMeasure (A) (hs) (b)`. §3's producer of the SD3 hypothesis is this name.
  `Matrix.IsHermitian.ae_mem_Icc_lanczosQuadrature` keeps its hypothesis: for a non-Hermitian
  $\mathbf{A}$ the compression can still be Hermitian, with Ritz values outside $[a, a']$.
* **Names (N2, N6, T9).** Statements of the form `(μ).real S` are named by Mathlib's dot reading
  of the measure, as `scripts/check_names.py` requires: `Matrix.IsHermitian.spectralMeasure_real_univ`
  (note: `measureReal_univ_spectralMeasure`), `Matrix.IsHermitian.lanczosQuadrature_real_univ`
  (`measureReal_univ_lanczosQuadrature`), `HasOrthonormalCols.lanczosQuadrature_real_singleton_pos`
  (`measureReal_lanczosQuadrature_singleton_pos`) and, for the same token,
  `Matrix.IsHermitian.norm_star_dotProduct_sq_le_spectralMeasure_real`
  (`…_le_measureReal_spectralMeasure`). The moment form keeps the note's
  `Matrix.IsHermitian.integral_pow_spectralMeasure` (review entry below). KS3c
  wrote the Ritz-value set as `(Qᴴ * A * Q).finite_real_spectrum.toFinset`, a proof term in the
  statement (T9): `HasOrthonormalCols.card_spectrum_conjTranspose_mul_mul_eq` concludes
  `Nat.card (spectrum ℝ (Qᴴ * A * Q)) = q`, and `isOrthogonalPolynomial_nodal` and
  `lanczosQuadrature_eq_interpolatoryQuadrature` take the node set as `{s : Finset ℝ}` with
  `hs : (s : Set ℝ) = spectrum ℝ (Qᴴ * A * Q)`.
* **Review warnings left.** P10 on the three `PowerIteration.lean` statements (Matrix vocabulary
  only; placed in `Krylov/Eigenvalues` per D12 and §6) and V7 on `evenChebyshevFilter` (no §5.3
  row was proposed for it); both for the maintainer. V7 is cleared on review by a §5.3 row.
* **No `open Classical in`** on `spectralMeasure`: the indicator `if t = x` uses Mathlib's
  decidable equality of ℝ, which avoids an instance mismatch in proofs.
* **API added.** `eval_evenChebyshevFilter` (for $x \ge 0$, $b_k(x) = U_{2k}(\sqrt{x})/(2k + 1)$),
  the characterising evaluation of the definition (quarry form). The definition is
  `C ((2 * k + 1 : ℝ)⁻¹) * contract 2 (Chebyshev.U ℝ (2 * k))`.
  `one_sub_mul_eval_evenChebyshevFilter_sq_le` keeps the note's right side
  $1/(2k + 1)^2$ (the quarry writes $((2k + 1)^2)^{-1}$, the same value).
* **Order inside `Quadrature.lean`.** Definition and measure-form bridges first, then exactness
  (C6, moment matching), then the error bound and the KS4 rates, then KS3c (file template:
  definitions, API, main theorems, corollaries). No statement changed.
* **Citations.** C2 forbids a bare key in a declaration docstring, so the note's
  "[ChenTrogdonUbaru2022], locator to check" on `matchesMoments_lanczosQuadrature` is a sentence
  in prose with "locator to check". No new locator was invented: the Lipschitz rates cite only
  the Jackson step ([ChenTrogdonUbaru2022, Appendix C, Theorem 38]); the Gauss weight lemma has no
  citation (the note gives Gautschi's Theorems 1.45 and 1.46 for exactness only); the even filter
  step cites [KuczynskiWozniakowski1992, Theorem 4.2] (to check), its helper nothing. The
  `Gautschi2004` entry (title, series, Oxford University Press, 2004, ISBN 978-0-19-850672-0) is
  from memory and is to confirm. Kuczyński and Woźniakowski's printed constants are not written in
  the named bounds' docstrings: they say the printed constant is to be compared, since I could not
  check it.
* **Result ids.** `ritz-value-gap-free` is on both gap-free Ritz bounds, `power-iteration` on the
  gapped power method; the KW power step and inverse iteration carry none. The interval Jackson
  theorem shares `jackson-lipschitz` with the $[-1, 1]$ one; the KS4 rates carry
  `lanczos-fa-uniform-bound` (Lanczos-FA) and `lanczos-gauss-quadrature` (quadrature).
* **The KW power constant** $\log(1 + \tan^2)/(2q + 1)$ was checked numerically on two-atom
  measures only (the worst ratio found to the bound was $0.995$, at $q = 0$); it remains to be
  proved.
* **Long names.** Five declaration names exceed 100 characters with their keyword; they are on
  their own line under `theorem`. `set_option linter.style.longLine false in`, with a comment,
  remains on three declarations whose lines are still longer (one name, two backticked names in
  docstrings).
* **Proved now.** Lower layers, all sorry-free:
  `exists_degree_le_isUniformApproxOn_Icc_of_lipschitzOnWith` (Jackson on $[a, b]$), the two KS4
  Lanczos-FA rates (`LanczosFA.lean`), `HasOrthonormalCols.eigenvalue_mul_mul_conjTranspose`,
  `ae_dotProduct_ne_zero_of_hasLaw_gaussianVector`, `measurable_quadForm`,
  `measurable_rayleighQuotient`, `measurable_krylovMatrix`. In the new files: the two
  `IsFiniteMeasure` instances (spectral measure, interpolatory rule),
  `isFiniteMeasure_lanczosQuadrature`,
  `isProbabilityMeasure_empiricalSpectralMeasure`, `integrable_spectralMeasure`, the
  polynomial, moment and mass forms of `integral_spectralMeasure` (from it),
  `spectralMeasure_compl_spectrum_eq_zero`, `ae_mem_Icc_spectralMeasure`,
  `rayleighQuotient_eq_integral_div`, `spectralTangentSq_nonneg`, `one_add_spectralTangentSq`,
  both empirical integral forms and its support lemma, the `MatchesMoments` API (`refl`, `symm`,
  `trans`, `mono`, `matchesMoments_zero`, the `degreeLT` bridge, `measureReal_univ_eq`),
  `IsOrthogonalPolynomial.mono`, the two KS4 quadrature rates (from the C6 error bound), and the
  three API lemmas of the named bounds (`randomStartPowerBound_nonneg`,
  `randomStartLanczosBound_nonneg`, `randomStartPowerBound_le`). Fifty statements are `sorry`.
* **Vocabulary.** CONTRIBUTING §5.3 has the seven rows of §2 (spectral measure, empirical
  spectral measure, angle, moment matching with the SD3 support hypothesis, orthogonality, Gauss
  rule, Lanczos rule); `docs/constants.toml` has the two named bounds.
* **Review, 2026-10-22: minimal hypotheses (T13, CONTRIBUTING §5.2).** Dropped as unneeded:
  `hT : T.IsHermitian` from `HasOrthonormalCols.spectralMeasure_mul_mul_conjTranspose`
  ($\mathbf{U}\mathbf{T}\mathbf{U}^{\mathsf{H}}$ is Hermitian exactly when $\mathbf{T}$ is, and
  both sides are $0$ otherwise; `T` is now explicit); `hA : A.IsHermitian` from
  `HasOrthonormalCols.lanczosQuadrature_eq` (the definition and the frame form are both spectral
  measures of the same compression, by the isometric invariance above); `hq : q ≤ krylovGrade A b`
  from `HasOrthonormalCols.lanczosQuadrature_eq_interpolatoryQuadrature` and
  `HasOrthonormalCols.lanczosQuadrature_real_singleton_pos` (past the grade the Krylov space is
  invariant and the rule is $\mu_{\mathbf{A},\mathbf{b}}$ itself, the interpolatory rule at its
  own support; $\deg\ell_x < \dim\mathcal{K}_q \le$ grade still gives
  $\ell_x(\mathbf{A})\mathbf{b} \ne \mathbf{0}$). `hq` stays on
  `HasOrthonormalCols.card_spectrum_conjTranspose_mul_mul_eq`, whose count $q$ is false past the
  grade. Docstrings say what holds past the grade.
* **Review, 2026-10-22: `integral_pow_spectralMeasure` (N6).** The moment form is renamed back to
  the note's `Matrix.IsHermitian.integral_pow_spectralMeasure`, Mathlib's `integral_pow` idiom:
  the power follows its argument `x`. The checker's N6 report on this name, which led to the
  skeleton's `integral_spectralMeasure_pow`, is a false positive (it reads `spectralMeasure` as the
  argument of `pow`); it is allowlisted in `scripts/names_allow.toml`.
