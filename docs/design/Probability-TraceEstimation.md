# Trace estimation: Girard–Hutchinson variances

Design note, 2026-10-18, for the maintainer's request of the same day: "more variance computations
including for real and complex sphere" (Epperly, *Stochastic trace estimation*, 2023, cited as the
blog post `[Epperly2023, <section heading>]`), amended the same day: "the sphere case is a special
case of Haar. Can we actually get something for tr(Q'AQ)?" ... "exact". Written and implemented in
one pass (Probability round rule: the maintainer weighs in on serious, hard-to-reverse decisions;
those are flagged **[maintainer]** below). Hutch++ (`docs/design/Estimation-HutchPP.md`) consumes
the estimator defined here.

## 1. Scope and the formulas

Single-probe variances of $\boldsymbol{\omega}^{\mathsf{H}}\mathbf{A}\boldsymbol{\omega}$, checked
against the post (HTML formulas) and derived independently:

| probe | variance | hypothesis on $\mathbf{A}$ |
|---|---|---|
| real Gaussian | $2\|\mathbf{A}\|_{\mathsf{F}}^2$ | symmetric; any real through $\mathbf{H} = (\mathbf{A} + \mathbf{A}^{\mathsf{T}})/2$ |
| Rademacher | $2(\|\mathbf{A}\|_{\mathsf{F}}^2 - \sum_i \mathbf{A}_{ii}^2)$ | same |
| real sphere, radius $\sqrt n$ | $\frac{2n}{n+2}(\|\mathbf{A}\|_{\mathsf{F}}^2 - (\operatorname{tr}\mathbf{A})^2/n)$ | same |
| Haar frame $n \times k$, $\operatorname{tr}(\mathbf{Q}^{\mathsf{T}}\mathbf{A}\mathbf{Q})$ | $\frac{2k(n-k)}{(n-1)n(n+2)}(\|\mathbf{A}\|_{\mathsf{F}}^2 - (\operatorname{tr}\mathbf{A})^2/n)$ | same, $n \ge 2$ |
| complex Gaussian | $\|\mathbf{A}\|_{\mathsf{F}}^2$ | any complex |
| Steinhaus | $\|\mathbf{A}\|_{\mathsf{F}}^2 - \sum_i \lvert\mathbf{A}_{ii}\rvert^2$ | any complex |
| complex sphere, radius $\sqrt n$ | $\frac{n}{n+1}(\|\mathbf{A}\|_{\mathsf{F}}^2 - \lvert\operatorname{tr}\mathbf{A}\rvert^2/n)$ | any complex |

Haar derivation (ours): $\mathbf{A} = \mathbf{U}\operatorname{diag}(\mathbf{d})\mathbf{U}^{\mathsf{T}}$,
$\mathbf{R} = \mathbf{U}^{\mathsf{T}}\mathbf{Q}$ is a Haar frame, and
$\operatorname{tr}(\mathbf{Q}^{\mathsf{T}}\mathbf{A}\mathbf{Q}) = \sum_i d_i r_i$ with
$r_i = \sum_j \mathbf{R}_{ij}^2$. Then $\mathbb{E} r_i = k/n$,
$a := \mathbb{E} r_i^2 = k(k+2)/(n(n+2))$ (the projected-sphere fourth moment of
`Haar/Sphere.lean`), $\mathbb{E} r_i r_l = c$ for all $i \ne l$ (a pair of rows has the law of a
corner of a Haar orthogonal matrix), and $\sum_l r_l = k$ gives $a + (n-1)c = k^2/n$. So
$\operatorname{Var} = (a - c)\|\mathbf{A}\|_{\mathsf{F}}^2 + (c - k^2/n^2)(\operatorname{tr}\mathbf{A})^2$,
which is the table's line. At $k = 1$ times $n^2$ it is the sphere's; at $k = n$ it is $0$. The
coordinator's first message had the unscaled Haar variance too large by a factor $n$; the
correction (Monte Carlo, $n = 6$) agrees with the derivation and with the Lean.

## 2. Decisions

**D1. Haar first, sphere as its $k = 1$ case** (maintainer). The primary result is the exact
variance of $\operatorname{tr}(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})$ for `haarFrame n k`.
Two statements: multiplied out, valid for every $n$ (at $n = 1$ both sides vanish), and divided,
under `1 < Fintype.card n`, so that no statement relies on $(n - 1)^{-1} = 0$. The sphere form
needs no hypothesis (the $n - 1$ cancels at $k = 1$; $n = 1$ is handled in the proof). Recommended
and done.

**D2. Complex laws as parallel definitions** (as `Probability-P2.md` §7 Q1, R5 Q5 planned).
`complexGaussianMeasure : Measure ℂ` is the product of two $\mathcal{N}(0, 1/2)$ read in ℂ;
`complexGaussianVector n` its product. `steinhausMeasure` is Mathlib's `haarAddCircle` on
`AddCircle 1` pushed by `toCircle`; `steinhausVector n` its product. Both mirror
`gaussianVector`/`rademacherVector` (`abbrev` products, so `HasLaw.eval`, `HasLaw.iIndepFun_eval`
apply). The complex Gaussian departs from Mathlib's `stdGaussian ℂ` (variance 2): deviation entry
20, bridge planned, not proved. **[maintainer]** whether the bridge should be proved before merge.

**D3. Complex sphere as the image of the real sphere** (Epperly's derivation 1, the brief's
recommendation). `complexUniformSphereVector n := (uniformSphereVector (n ⊕ n)).map
complexOfRealPair`, with `complexOfRealPair v i = v (inl i) + v (inr i) * I` a new public map.
Its variance reduces to the real sphere on `n ⊕ n`. Not done: the bridge to `g / ‖g‖` for a
complex Gaussian `g` (entry 20). **[maintainer]** the name `complexOfRealPair` (alternatives:
inline lambda in the definition; a `MeasurableEquiv` `(n ⊕ n → ℝ) ≃ᵐ (n → ℂ)`).

**D4. Complex variance spelled as a second moment about the mean.** Mathlib's `variance` is
real-valued, so complex statements conclude
`∫ ω, ‖quadForm A (x ω) - A.trace‖ ^ 2 ∂μ = …`, Epperly's $\operatorname{Var}(z) =
\mathbb{E}\lvert z - \mathbb{E}z\rvert^2$ (the mean is $\operatorname{tr}\mathbf{A}$ by isotropy).
They hold for every complex $\mathbf{A}$ at once, so no Hermitian / skew-Hermitian corollaries are
needed. Real statements keep `variance`.

**D5. General real $\mathbf{A}$ through the symmetric part**, as separate corollaries carrying the
suffix `_hermitianPart` (their conclusions mention `hermitianPart A`), from two Matrix bridges
`quadForm_hermitianPart` and `trace_conjTranspose_mul_hermitianPart_mul` (ℝ only).
**[maintainer]** the suffix; the existing symmetric theorems keep their names (no `_of_isHermitian`
rename).

**D6. A named estimator** `girardHutchinson A Ω := (Ωᴴ * A * Ω).trace / card m` in the new
`Estimation/Trace/GirardHutchinson.lean` (layer 4, as `PORT_KRYLOV.md` §2 planned), test matrix
form over `RCLike`, junk `0` for no columns: Hutch++ (`Estimation-HutchPP.md` §1.1, TE3) needs a
named object, and the prototype had one (`hutchinsonEstimate`, real). The library had none
(searched `NLAlib/`, Sketching). Probes are the columns `fun ω i => X ω i j`; independence is
`iIndepFun (fun j ω i => X ω i j) μ`. **[maintainer]** the name (Epperly and Hutch++'s note say
Girard–Hutchinson; the prototype said `hutchinsonEstimate`).

**D7. Optimality of Rademacher** stated as a comparison of two probes on possibly different
spaces, `variance_quadForm_of_hasLaw_rademacherVector_le`, from $m_4 \ge 1$. The sphere's
worst-case optimality over unitarily invariant classes is skipped (not short: it needs the
radius–direction decomposition of an isotropic vector).

**D8. Complex Haar frames deferred.** A `complexHaarFrame n k` (polar factor of a complex Gaussian
matrix) needs a complex Gaussian matrix law with unitary invariance and full rank a.s., and the
Haar API of `Haar/{Basic,Uniqueness,Sphere,Blocks}.lean` over ℂ: not modest. Later target, with
expected variance $\frac{k(n-k)}{(n-1)n(n+1)}(\|\mathbf{A}\|_{\mathsf{F}}^2 -
\lvert\operatorname{tr}\mathbf{A}\rvert^2/n)$ (its $k = 1$ case times $n^2$ is the complex sphere
line, which is proved).

## 3. Placement

| Declaration(s) | Home | Reason |
|---|---|---|
| `quadForm_hermitianPart`, `trace_conjTranspose_mul_hermitianPart_mul` | `Matrix/Spectral/HermitianPart.lean` | facts about the Hermitian part |
| `complexGaussianMeasure`, `complexGaussianVector`, moments | new `Probability/Distributions/ComplexGaussian.lean` | a law |
| `steinhausMeasure`, `steinhausVector`, moments | new `Probability/Distributions/Steinhaus.lean` | a law |
| complex Gaussian, Steinhaus, general real Gaussian/Rademacher variances, Rademacher optimality | `Probability/QuadraticForm/Moments.lean` | second moments of quadratic forms with independent coordinates |
| `hasLaw_replicateCol_of_hasLaw_uniformSphereVector`, `complexOfRealPair`, `complexUniformSphereVector` | `RandomMatrix/Haar/Basic.lean` | beside `uniformSphereVector` |
| Haar compression mean and variance, real and complex sphere variances | `RandomMatrix/Haar/Moments.lean` (now "Moments of Haar frames") | moments of Haar frames; the sphere is the one-column frame |
| `girardHutchinson`, mean, $m$-probe variance, Haar test matrix | new `Estimation/Trace/GirardHutchinson.lean` | the estimator's topic |

No flags: everything is at its topic's home. Sphere variances cannot live in `Probability/`
(layer 1), which does not import `RandomMatrix/`.

## 4. Statements

```lean
-- Matrix/Spectral/HermitianPart.lean
theorem quadForm_hermitianPart (A : Matrix n n ℝ) (x : n → ℝ) :
    quadForm (hermitianPart A) x = quadForm A x
theorem trace_conjTranspose_mul_hermitianPart_mul (Q : Matrix n k ℝ) (A : Matrix n n ℝ) :
    (Qᴴ * hermitianPart A * Q).trace = (Qᴴ * A * Q).trace

-- RandomMatrix/Haar/Moments.lean, X : Ω → Matrix n k ℝ, hX : HasLaw X (haarFrame n k) μ,
-- hk : card k ≤ card n
theorem integral_trace_conjTranspose_mul_mul_of_hasLaw_haarFrame (hX) (hk) (A) :
    ∫ ω, ((X ω)ᴴ * A * X ω).trace ∂μ = card k / card n * A.trace
theorem mul_variance_trace_conjTranspose_mul_mul_of_hasLaw_haarFrame (hX) (hk) (hA : A.IsHermitian) :
    (card n - 1) * card n ^ 2 * (card n + 2) * variance (fun ω => ((X ω)ᴴ * A * X ω).trace) μ =
      2 * card k * (card n - card k) * (card n * frobNorm A ^ 2 - A.trace ^ 2)
theorem variance_trace_conjTranspose_mul_mul_of_hasLaw_haarFrame (hX) (hk) (hn : 1 < card n) (hA) :
    variance … = 2 * card k * (card n - card k) / ((card n - 1) * card n * (card n + 2)) *
      (frobNorm A ^ 2 - A.trace ^ 2 / card n)
theorem variance_trace_conjTranspose_mul_mul_of_hasLaw_haarFrame_hermitianPart (hX) (hk) (hn) (A) :
    variance … = … * (frobNorm (hermitianPart A) ^ 2 - A.trace ^ 2 / card n)
theorem variance_quadForm_sqrt_smul_of_hasLaw_uniformSphereVector
    (hu : HasLaw u (uniformSphereVector n) μ) (hA : A.IsHermitian) :
    variance (fun ω => quadForm A (√(card n) • u ω)) μ =
      2 * card n / (card n + 2) * (frobNorm A ^ 2 - A.trace ^ 2 / card n)
theorem variance_quadForm_sqrt_smul_of_hasLaw_uniformSphereVector_hermitianPart (hu) (A) : …
theorem integral_norm_quadForm_sqrt_smul_sub_trace_sq_of_hasLaw_complexUniformSphereVector
    (hw : HasLaw w (complexUniformSphereVector n) μ) (A : Matrix n n ℂ) :
    ∫ ω, ‖quadForm A ((√(card n) : ℂ) • w ω) - A.trace‖ ^ 2 ∂μ =
      card n / (card n + 1) * (frobNorm A ^ 2 - ‖A.trace‖ ^ 2 / card n)

-- Probability/QuadraticForm/Moments.lean
theorem integral_norm_quadForm_sub_trace_sq_of_hasLaw_complexGaussianVector
    (hg : HasLaw g (complexGaussianVector n) μ) (A : Matrix n n ℂ) :
    ∫ ω, ‖quadForm A (g ω) - A.trace‖ ^ 2 ∂μ = frobNorm A ^ 2
theorem integral_norm_quadForm_sub_trace_sq_of_hasLaw_steinhausVector (hz) (A) :
    … = frobNorm A ^ 2 - ∑ i, ‖A i i‖ ^ 2
theorem variance_quadForm_of_hasLaw_gaussianVector_hermitianPart (hg) (A : Matrix n n ℝ) :
    variance … = 2 * frobNorm (hermitianPart A) ^ 2
theorem variance_quadForm_of_hasLaw_rademacherVector_hermitianPart (hx) (A) :
    variance … = 2 * (frobNorm (hermitianPart A) ^ 2 - ∑ i, A i i ^ 2)
theorem variance_quadForm_of_hasLaw_rademacherVector_le (hε : HasLaw ε (rademacherVector n) ν)
    (hind) (hL4) (hmean) (hvar) (hm₄) (hA : A.IsHermitian) :
    variance (fun ω => quadForm A (ε ω)) ν ≤ variance (fun ω => quadForm A (x ω)) μ

-- Estimation/Trace/GirardHutchinson.lean, X : Ω → Matrix n m 𝕜
noncomputable def girardHutchinson (A : Matrix n n 𝕜) (Ω : Matrix n m 𝕜) : 𝕜 :=
  (Ωᴴ * A * Ω).trace / Fintype.card m
theorem girardHutchinson_eq_sum : girardHutchinson A Ω = (∑ j, quadForm A fun i => Ω i j) / card m
theorem integral_girardHutchinson [Nonempty m] (hX : ∀ j, IsIsotropic (fun ω i => X ω i j) μ) A :
    ∫ ω, girardHutchinson A (X ω) ∂μ = A.trace
theorem integral_norm_girardHutchinson_sub_trace_sq [Nonempty m]
    (hind : iIndepFun (fun j ω i => X ω i j) μ) (hX) (hL2 : ∀ j, MemLp (quadForm A ∘ col j) 2 μ)
    (hv : ∀ j, ∫ ω, ‖quadForm A (col j ω) - A.trace‖ ^ 2 ∂μ = v) :
    ∫ ω, ‖girardHutchinson A (X ω) - A.trace‖ ^ 2 ∂μ = v / card m
theorem variance_girardHutchinson … (𝕜 = ℝ, hv in `variance` form) : variance … = v / card m
theorem variance_girardHutchinson_sqrt_smul_of_hasLaw_haarFrame [Nonempty k] (hX) (hk) (hn) (hA) :
    variance (fun ω => girardHutchinson A (√(card n) • X ω)) μ =
      2 * card n * (card n - card k) / (card k * (card n - 1) * (card n + 2)) *
        (frobNorm A ^ 2 - A.trace ^ 2 / card n)
```

No named constants (every constant is exact and small, written in the statement). No asymptotic
forms (none are sample-size results). §5.3 rows proposed: the Girard–Hutchinson estimate
`girardHutchinson A Ω` (`\mathsf{girardHutchinson}`), and the complex probe laws
`complexGaussianVector n`, `steinhausVector n`, `complexUniformSphereVector n` beside the real
ones; not yet added to CONTRIBUTING (a §5.3 change needs two approvals).

## 5. Consumers

Hutch++ (`Estimation-HutchPP.md`: `girardHutchinson`, its unbiasedness and mean-square formula,
the Hermitian-part bridges, and later the sphere formula in dimension $N - r$); XTrace and
Nyström++ (orthonormal and sphere probes); any complex trace estimator (complex laws).

## 6. Material

Prototype atlas (`prove2me/lean/atlas/declarations.json`): `hutchinsonEstimate`,
`integral_hutchinsonEstimate_eq_trace` (`Estimation/Trace/{HutchinsonTail,Unbiased}`), real only,
Gaussian and Rademacher variances (already ported in P3). No sphere, Haar, complex or Steinhaus
variance existed. Reused: the definition's shape; ledger entries for the two names. Not reproduced:
`hutchinsonBlock` (Hutch++'s P7 owns the vectorized tail).

## Implementation (2026-10-18)

All of §4 is proved, no `sorry`. Files: the two new laws, `Estimation/Trace/GirardHutchinson.lean`,
additions to `HermitianPart.lean`, `QuadraticForm/Moments.lean`, `Haar/Basic.lean`,
`Haar/Moments.lean` (903 lines). Proof notes:

- Haar variance: continuous functions of a Haar frame are bounded (entries in $[-1, 1]$ a.s.) hence
  in every $L^p$; the cross-moment invariance uses
  `hasLaw_const_mul_of_hasLaw_haarFrame_of_hasOrthonormalCols` with a two-row selection; the
  diagonalisation is `exists_hasOrthonormalCols_eq_mul_diagonal_mul_conjTranspose`.
- Sphere: `hasLaw_replicateCol_of_hasLaw_uniformSphereVector` makes the sphere vector a
  one-column Haar frame; the radius–direction "camel" argument of the post is not used.
- Complex sphere: the real form $\begin{bmatrix}\operatorname{Re}\mathbf{H} & -\operatorname{Im}
  \mathbf{H}\\ \operatorname{Im}\mathbf{H} & \operatorname{Re}\mathbf{H}\end{bmatrix}$ of the
  Hermitian parts of $\mathbf{A}$ and $-i\mathbf{A}$ carries the real and imaginary parts;
  $\|\mathbf{H}_1\|_{\mathsf{F}}^2 + \|\mathbf{H}_2\|_{\mathsf{F}}^2 = \|\mathbf{A}\|_{\mathsf{F}}^2$
  is the parallelogram law.
- Steinhaus: $\mathbb{E}Z = \mathbb{E}Z^2 = 0$ from invariance of `haarAddCircle` under the quarter
  turn ($Z \mapsto iZ$), no integral computed.

Later targets: complex Haar frames (D8); the bridges of deviation entry 20; the sphere's worst-case
optimality; m-probe corollaries for each law (one line each from `variance_girardHutchinson`).
