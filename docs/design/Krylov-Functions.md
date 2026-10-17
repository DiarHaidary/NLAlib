# Design note: Krylov stage K2, matrix functions and near-optimal Lanczos-FA

Status: draft, 2026-10-17, for review before any proof. Drafted from the brief
`docs/PORT_KRYLOV.md` (D3, D8, D12, O1, O2, roadmap item "Lanczos-FA and Gauss quadrature"), the
K0 note `docs/design/Krylov-CG.md` and the proved K0 files. The statements are in a skeleton
outside the repository, `~/Documents/NLA-lib/krylov-scratch/skeleton-k2/`, one file per planned
library file plus one file per addition to an existing file (`Additions/`). With the script
`check.py` there, all of it elaborates in one file under `lake env lean -DautoImplicit=false
-DmaxSynthPendingDepth=3 -Dlinter.missingDocs=true -Dweak.linter.mathlibStandardSet=true`
with only `sorry` warnings (61 of them; log `check.log`). Since K1's `cgIterate A b x₀ q` (with a
start) is not built, `check.py` checks the CG statements against a local copy of K1's
definition, `cgIterateK1`; the skeleton text uses K1's `cgIterate`. Signatures are not repeated here
except for the headline theorem: the skeleton is the specification.

The maintainer's request: "Then do matrix functions and prove this bound:
https://arxiv.org/abs/2608.07160. Throughout, keep in mind where new functions should be placed
in the library." The paper is Chen and Persson, "Optimal near-optimality bounds for the Lanczos
method for matrix functions", arXiv:2608.07160v1 [math.NA], 7 August 2026 (new key
`ChenPersson2026`, §9). It is the maintainer's paper, citable by his direction.

**Conventions** (maintainer, 2026-10-17, relayed by the coordinator). Nothing is renamed in K1.
The starting vector of Lanczos-FA is `b`, as in K0's `krylovMatrix A b q` and as in the paper.
Spectral intervals are `Set.Icc a a'` with $\kappa = a'/a$, as in K0's Chebyshev bound. The
hypothesis is `spectrum ℝ A ⊆ Set.Icc a a'` with `0 < a` (D8). A solution vector is `xs` with
`hxs : A *ᵥ xs = b`, as in K0. Errors are squared norms, `RCLike.re (quadForm N (w - y))`.

## 1. Overview

The stage has three parts.

1. **Lanczos-FA, defined mathematically.** A compressed functional calculus
   `compressedCfc A f X` $= \mathbf{P}f(\mathbf{P}\mathbf{A}\mathbf{P})\mathbf{P}$ with
   $\mathbf{P}$ = `rangeProjector X`, the third member of K0's family (`galerkinInverse`, and
   K1's `minResidualInverse`), and `lanczosFA A f b q` on the Krylov matrix. First theorem: the
   frame form $\mathbf{Q}f(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})\mathbf{Q}^{\mathsf{H}}\mathbf{b}$
   for every orthonormal basis $\mathbf{Q}$, for every $\mathbf{A}$. Then exactness, interpolation
   at the Ritz values, the $2\varepsilon\|\mathbf{b}\|$ bound, CG for $x^{-1}$, shifted CG for
   $(x + s)^{-1}$, exactness past the grade, and the realisation through K0's Lanczos recurrence.
   Gauss quadrature is two theorems on $\mathbf{b}^{\mathsf{H}}\,\mathsf{lanczosFA}$.
2. **Stieltjes functions, as scalar analysis.** A predicate `HasStieltjesMeasure f μ` and
   `IsStieltjes f`, their monotonicity, the kernel ratio lemma (the paper's Lemma 6), instances,
   and the interpolation error (the paper's Lemma 4) for both classes of the paper.
3. **The near-optimality theorem.** One abstract step (the paper's Theorem 5 with the Lanczos
   specifics removed), the general-norm theorem, the $\mathbf{A}^\alpha$-norm theorem (the
   paper's Theorem 1), its $\kappa$ and Euclidean forms, and the CG and shifted-CG corollaries
   (the paper's Remark 3). The optimality of the constant (Theorem 2) is stated now and proved
   in stage K2b, right after K2 (decided, §6).

**The main design finding: no matrix-valued integral is needed.** The paper works with scalar
functions on the spectrum. Everything that involves the measure is a scalar Bochner integral in
$t$: the interpolation error identity is integrated kernel by kernel, and the ratio bound of the
paper's Lemma 6 is integrated pointwise in $t$. The matrix side only applies `cfc` to scalar
functions on a finite spectrum, through `cfc_congr`, `cfc_mul` and `cfc_polynomial`. The
representation $f(\mathbf{A}) = \int(\mathbf{A} + t\mathbf{I})^{-1}\,d\mu(t)$ is therefore not
built. If a consumer appears it is one line from the existing
`Matrix.IsHermitian.cfc_integral` (`Probability/MatrixIntegral.lean`), which already needs no
continuity, but that file is in Probability and Krylov does not import Probability (D12), so it
would live in Probability.

Dependency list ("X uses Y": the statement or definition of X mentions Y).

- `HasStieltjesMeasure f μ` uses Mathlib's `MeasureTheory.Measure` and Bochner integral;
  `IsStieltjes f` uses it. The bridge to Mathlib uses `MeasureTheory.resolventTransform`.
- The interpolation-error lemmas use `Lagrange.interpolate s id f`, `Lagrange.nodal s id`
  (Mathlib) and `IsStieltjes`.
- `compressedCfc A f X` uses `rangeProjector` and `cfc`; `lanczosFA A f b q` uses
  `compressedCfc` and `krylovMatrix`.
- The compression lemmas use `HasOrthonormalCols`, `krylovSpace`, `Polynomial.aeval`,
  `Lagrange.nodal`.
- The near-optimality theorems use `lanczosFA`, `IsStieltjes`, `quadForm`, Mathlib's `A ^ α`
  (`CFC.rpow`), `krylovSpace`, `pseudoConditionNumber`, `cgIterate`.

## 2. Definitions

Common context `{𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]`, functions
real functions `f` of a real variable (Mathlib's `cfc` over ℝ, as in `Matrix/Functions`).

### 2.1 Stieltjes functions (`Polynomial/Approximation/Stieltjes.lean`)

`structure HasStieltjesMeasure f μ : Prop`, for a real function `f` and `μ : Measure ℝ`, with
fields `measure_Iio : μ (Set.Iio 0) = 0`, `integrable : Integrable (fun t => (1 + t)⁻¹) μ` and
`eq_integral`, which says `f z = ∫ t, (z + t)⁻¹ ∂μ` for every `z` with `0 < z`;
`IsStieltjes f := ∃ μ, HasStieltjesMeasure f μ`.
This is the paper's (6). Choices, each with its reason:

| Question | Choice | Reason |
|---|---|---|
| constant and linear terms | none: the paper's class (6); the atom at $t = 0$ gives $c/z$ | constants are reached through the second class ($f(z)/z = c/z$); $c + g$ with $g$ Stieltjes is a trivial corollary, added only with a consumer (module docstring) |
| domain | values on $(0, \infty)$ only | only they reach a function of a positive definite matrix; $f(0)$ may be infinite ($z^{-1/2}$) |
| measure | `Measure ℝ` vanishing on $(-\infty, 0)$ | integrals over ℝ with Mathlib's API; `Measure.dirac s`, sums, `withDensity` stay in one type; alternatives `Measure ℝ≥0` or a subtype cost coercions in every integrand (§11) |
| integrability | in the structure | without it the Bochner integral's junk value $0$ would make the representation vacuous and every proof would need the hypothesis |
| measure as data | `HasStieltjesMeasure f μ` beside `IsStieltjes f` | proofs (the remainder measure $d\mu/\prod(\theta + t)$) need the measure; users state `IsStieltjes` |
| the class $\mathcal{S}$ of the paper | the hypothesis `IsStieltjes f ∨ IsStieltjes fun z => f z / z`, no name | the paper names it only $\mathcal{S}$; a disjunction of one interface is still that interface, and a third class would get its own lemma, not a wider predicate |

Mathlib search: `StieltjesFunction` (Mathlib) is the distribution function of a
Lebesgue–Stieltjes measure, a different object, so the name `IsStieltjes` avoids that namespace.
`MeasureTheory.resolventTransform μ a = ∫ x, resolvent a x ∂μ`
(`Mathlib/MeasureTheory/Measure/ResolventTransform.lean`) is the Stieltjes transform of a measure;
its API assumes finite measures and complex or algebra values, while (6) needs infinite measures
such as $t^{-\gamma}dt$. The bridge `HasStieltjesMeasure.apply_eq_resolventTransform`
($f(z)$ = `resolventTransform μ (-z)`) ships in the same file. Mathlib's
`Real.exists_measure_rpow_eq_integral_rpowIntegrand₀₁`
(`Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/IntegralRepresentation.lean`)
gives the instance $z^{-\gamma}$, $0 < \gamma < 1$, with a measure known up to a constant, which
is all `IsStieltjes` needs. Searched, none: Pick or Nevanlinna functions, operator monotone
integral representations beyond `rpow`, Stieltjes functions of matrices. An addition, not a
numbered deviation; `docs/design/Mathlib-deviations.md` lists it with the bridge.

§5.3 row: "Stieltjes function | `IsStieltjes f`, `HasStieltjesMeasure f μ` (measure on ℝ, null on
$(-\infty, 0)$, $\int(1+t)^{-1}d\mu < \infty$, values on $(0, \infty)$) | `HasStieltjesMeasure.apply_eq_resolventTransform`".

### 2.2 `compressedCfc` and `lanczosFA` (`Krylov/Functions/LanczosFA.lean`)

`compressedCfc A f X := rangeProjector X * cfc f (rangeProjector X * A * rangeProjector X) * rangeProjector X`
and `lanczosFA A f b q := compressedCfc A f (krylovMatrix A b q) *ᵥ b`, written
$\mathsf{lanczosFA}(\mathbf{A}, f, \mathbf{b}, q)$; argument order matrix, function, vector, depth
(O2). The names are the brief's (D3, O2), kept by the K0 note.

| Candidate | Verdict |
|---|---|
| $\mathbf{Q}f(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})\mathbf{Q}^{\mathsf{H}}\mathbf{b}$ with a chosen basis | depends on a choice, not measurable; recovered as the frame form |
| $\mathbf{K}f(\cdot)\ldots$ on the Krylov matrix itself | $\mathbf{K}^{\mathsf{H}}\mathbf{A}\mathbf{K}$ is not a compression in an orthonormal basis; wrong for every $f$ but polynomials |
| `cfc f (P * A * P) * P` | equal to the adopted one, less symmetric |
| `cfc f (P * A * P) *ᵥ b` | wrong at $q = 0$ (gives $f(0)\mathbf{b}$) |
| $\mathbf{P}f(\mathbf{P}\mathbf{A}\mathbf{P})\mathbf{P}$ (adopted) | depends on the subspace only, total, measurable in $\mathbf{b}$ (`measurable_rangeProjector` and continuity of `cfc` on matrices with a finite spectrum, later), block-ready, and `compressedCfc A (·⁻¹) X = galerkinInverse A X` for Hermitian $\mathbf{A}$ |

The padding: $\mathbf{P}\mathbf{A}\mathbf{P}$ has the Ritz values on the Krylov space and the
eigenvalue $0$ on its complement, so $f(\mathbf{P}\mathbf{A}\mathbf{P}) =
\mathbf{Q}f(\mathbf{T})\mathbf{Q}^{\mathsf{H}} + f(0)(\mathbf{I} - \mathbf{P})$
(`HasOrthonormalCols.cfc_mul_mul_conjTranspose`, a Matrix addition) and the outer projectors
remove $f(0)$. This is K0's observation that `cfc` of a zero-padded compression is fine (finite
spectrum); what fails on padded compressions is a Loewner or spectral bound, so every statement
that needs the Ritz values in $[a, a']$ goes through a genuine frame
(`Matrix.IsHermitian.spectrum_conjTranspose_mul_mul_subset_Icc`).

Junk values, in the docstrings: $q = 0$ gives $\mathbf{0}$; for non-Hermitian $\mathbf{A}$ the
compression is not Hermitian (it is Hermitian exactly when
$\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$ is) and Mathlib's `cfc` returns $\mathbf{0}$
(`cfc_apply_of_not_predicate`), on both sides of the frame form. Arnoldi-FA is out of the round
(brief §4).

§5.3 row: "compressed function, Lanczos-FA | `compressedCfc A f X`, `lanczosFA A f b q` |
`HasOrthonormalCols.lanczosFA_eq`, `Matrix.IsHermitian.compressedCfc_inv_eq_galerkinInverse`".

## 3. The paper in the library's vocabulary

| Paper | Library |
|---|---|
| $\mathbf{A}$ Hermitian positive definite, $\kappa(\mathbf{A}) = \lambda_{\max}/\lambda_{\min}$ | `hA : A.IsHermitian`, `0 < a`, `spectrum ℝ A ⊆ Set.Icc a a'`, $\kappa$ replaced by $a'/a$ (D8); the $\kappa$ form takes `A.PosDef` and `pseudoConditionNumber A` |
| $\mathbf{b} \in \mathbb{C}^n$, $m \ge 1$ | a vector `b`, `q : ℕ`, any $q$ (the bound is trivial at $q = 0$) |
| $\mathcal{K}_m$, $\Pi_{m-1}$ | `krylovSpace A b q`; its elements are the $p(\mathbf{A})\mathbf{b}$, $\deg p < q$ (`mem_krylovSpace_iff`) |
| $f_m = \mathbf{V}_m f(\mathbf{T}_m)\mathbf{V}_m^*\mathbf{b}$, (1) | `lanczosFA A f b q`, frame form `HasOrthonormalCols.lanczosFA_eq` |
| $f(\mathbf{A})$ | `cfc f A` |
| $f$ Stieltjes, (6); $\mathcal{S}$ | `IsStieltjes f`; `IsStieltjes f ∨ IsStieltjes fun z => f z / z` |
| $\|\mathbf{x}\|_\nu^2 = \mathbf{x}^*\nu(\mathbf{A})\mathbf{x}$, $\nu > 0$ on the spectrum | `RCLike.re (quadForm (cfc ν A) x)`, `∀ x ∈ spectrum ℝ A, 0 < ν x` |
| $\|\cdot\|_{\mathbf{A}^\alpha}$ | `RCLike.re (quadForm (A ^ α) x)`, Mathlib's `CFC.rpow` (§5.3 row "real power"), `CFC.rpow_eq_cfc_real` |
| $\min_{\mathbf{x}\in\mathcal{K}_m}\|f(\mathbf{A})\mathbf{b} - \mathbf{x}\|$ and the ratio $C$ of (4) | not named: the conclusion holds against every `y ∈ krylovSpace A b q`, which is the bound on the minimum and needs no convention for $0/0$ |
| $E = \max\{\alpha, 1 - \alpha\}$ | `max α (1 - α)`, inline |
| $\tfrac12(\kappa^{E/2} + \kappa^{-E/2})$ | squared, inline: `(((a' / a) ^ (max α (1 - α) / 2) + (a' / a) ^ (-(max α (1 - α) / 2))) / 2) ^ 2` (§5.2 rule 2: a small constant the proof reaches is written in the statement; no named bound) |
| Ritz values $\theta_j$, $\pi_m = \prod_j(z - \theta_j)$, (7) | the finite set `spectrum ℝ (Qᴴ * A * Q)` for a frame `Q`, and `Lagrange.nodal s id` for a `Finset` `s` containing it; distinct by construction, so the paper's "$m < M$, Ritz values distinct" ([GolubMeurant2010, §4]) is never needed |
| $q_{m-1}$ interpolating $f$ at the Ritz values, (9) | `Lagrange.interpolate s id f`; `HasOrthonormalCols.lanczosFA_eq_aeval_mulVec` for any agreeing polynomial |
| orthogonality (11) | `HasOrthonormalCols.conjTranspose_mulVec_aeval_nodal_mulVec_eq_zero`, spelled $\mathbf{Q}^{\mathsf{H}}\pi(\mathbf{A})\mathbf{b} = \mathbf{0}$ (K0's spelling of orthogonality to a column space) |
| $\varsigma_m$, $\varrho_m$ of Lemma 4 | `∃ ς ρ, HasStieltjesMeasure ς ρ ∧ ρ ≪ μ ∧ …` from `HasStieltjesMeasure.exists_sub_eval_interpolate_eq` (and `_of_div`); the explicit integrals in `sub_eval_interpolate_eq` (and `_of_div`) |
| $R$ of Theorem 5 | a hypothesis on the kernel, $\nu(x)(y + t) \le R\,\nu(y)(x + t)$ for eigenvalues $x, y$ and $\mu$-almost every $t \ge 0$, $\mu$ the measure of $f$ (or of $f(z)/z$); the paper's $R$ depends on $\varsigma_m$, hence on the Ritz values, which no user can supply. The corollary with the bound for every $t \ge 0$ is uniform over Stieltjes functions and loses the dependence on $f$: for $f(z) = (z + s)^{-1}$ ($\mu = \delta_s$) and $\nu(z) = z^\alpha$ the measure form needs only the ratio of $x^\alpha/(x + s)$ on the spectrum, which tends to $(a'/a)^\alpha$ as $s$ grows (below $(a'/a)^E$ when $\alpha < 1/2$) and is smaller still at intermediate $s$, while the all-$t$ form must take $(a'/a)^E$ |
| $\tfrac12(\sqrt R + 1/\sqrt R)$ | squared, `(R + 1) ^ 2 / (4 * R)` |

Deviations from the printed statements, recorded in the docstrings: squared norms; $[a, a']$ in
place of $\kappa(\mathbf{A})$ (the $\kappa$ form is a corollary); any $q$; any `RCLike` field;
Theorem 5's ratio replaced by a kernel bound; Theorem 2's "a Stieltjes function" made explicit
as the shifted inverse its proof uses.

**The abstract step and Theorem 5** (`Krylov/Functions/NearOptimality.lean`):

```lean
theorem _root_.Matrix.IsHermitian.re_quadForm_cfc_sub_le_of_sub_eq_aeval_mulVec
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {ν ς : ℝ → ℝ} {R : ℝ} (hR₁ : 1 ≤ R)
    (hν : ∀ x ∈ spectrum ℝ A, 0 < ν x) (hς : ∀ x ∈ spectrum ℝ A, 0 ≤ ς x)
    (hR : ∀ x ∈ spectrum ℝ A, ∀ y ∈ spectrum ℝ A, ν x * ς x ≤ R * (ν y * ς y))
    {b w y₀ y : n → 𝕜} {q : ℕ} {π : ℝ[X]}
    (hπ : (krylovMatrix A b q)ᴴ *ᵥ (aeval A π *ᵥ b) = 0) (hy₀ : y₀ ∈ krylovSpace A b q)
    (he : w - y₀ = aeval A π *ᵥ (cfc ς A *ᵥ b)) (hy : y ∈ krylovSpace A b q) :
    RCLike.re (quadForm (cfc ν A) (w - y₀)) ≤
      (R + 1) ^ 2 / (4 * R) * RCLike.re (quadForm (cfc ν A) (w - y))

theorem _root_.Matrix.PosDef.re_quadForm_cfc_cfc_mulVec_sub_lanczosFA_le_of_hasStieltjesMeasure
    {A : Matrix n n 𝕜} (hA : A.PosDef) {f : ℝ → ℝ} {μ : MeasureTheory.Measure ℝ}
    (hf : HasStieltjesMeasure f μ ∨ HasStieltjesMeasure (fun z => f z / z) μ)
    {ν : ℝ → ℝ} {R : ℝ} (hν : ∀ x ∈ spectrum ℝ A, 0 < ν x)
    (hR : ∀ x ∈ spectrum ℝ A, ∀ y ∈ spectrum ℝ A, ∀ᵐ t ∂μ, 0 ≤ t →
      ν x * (y + t) ≤ R * (ν y * (x + t)))
    (b : n → 𝕜) {q : ℕ} {y : n → 𝕜} (hy : y ∈ krylovSpace A b q) :
    RCLike.re (quadForm (cfc ν A) (cfc f A *ᵥ b - lanczosFA A f b q)) ≤
      (R + 1) ^ 2 / (4 * R) * RCLike.re (quadForm (cfc ν A) (cfc f A *ᵥ b - y))
```

The abstract step needs `hR₁`: without it the statement is false in a junk case ($\mathbf{A} =
\mathbf{I}$, $\nu = 1$, $\varsigma = 0$, $R = -2$ makes the right side negative). Theorem 5 needs
no such hypothesis: the kernel bound at $x = y$, $t = 0$ gives $R \ge 1$ when the spectrum is
nonempty, and for empty $n$ both sides are $0$. `Matrix.PosDef.re_quadForm_cfc_cfc_mulVec_sub_lanczosFA_le`
is the one-line corollary with `IsStieltjes` and the kernel bound for every $t \ge 0$.

**The headline theorem** (`Krylov/Functions/NearOptimality.lean`):

```lean
theorem _root_.Matrix.IsHermitian.re_quadForm_rpow_cfc_mulVec_sub_lanczosFA_le
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ A ⊆ Set.Icc a a') {f : ℝ → ℝ}
    (hf : IsStieltjes f ∨ IsStieltjes fun z => f z / z) (α : ℝ) (b : n → 𝕜) {q : ℕ}
    {y : n → 𝕜} (hy : y ∈ krylovSpace A b q) :
    RCLike.re (quadForm (A ^ α) (cfc f A *ᵥ b - lanczosFA A f b q)) ≤
      (((a' / a) ^ (max α (1 - α) / 2) + (a' / a) ^ (-(max α (1 - α) / 2))) / 2) ^ 2 *
        RCLike.re (quadForm (A ^ α) (cfc f A *ᵥ b - y))
```

Read back: for Hermitian $\mathbf{A}$ with spectrum in $[a, a']$, $a > 0$, any $f$ such that $f$
or $f(z)/z$ is Stieltjes, any real $\alpha$, any $\mathbf{b}$, $q$ and any $\mathbf{y}$ in the
Krylov space, the squared $\mathbf{A}^\alpha$-norm of the Lanczos-FA error is at most the square
of $\tfrac12((a'/a)^{E/2} + (a'/a)^{-E/2})$ times the squared $\mathbf{A}^\alpha$-norm of
$f(\mathbf{A})\mathbf{b} - \mathbf{y}$. `Result: lanczos-fa-near-optimality`.

## 4. Statements by file

Claims in one line; the skeleton has the docstrings, citations and `Proof:` sketches.

**Matrix additions.** `Matrix/Functions/HermitianCalculus.lean`:
`HasOrthonormalCols.cfc_mul_mul_conjTranspose` ($f(\mathbf{U}\mathbf{T}\mathbf{U}^{\mathsf{H}}) =
\mathbf{U}f(\mathbf{T})\mathbf{U}^{\mathsf{H}} + f(0)(\mathbf{I} - \mathbf{U}\mathbf{U}^{\mathsf{H}})$,
any frame); `Matrix.IsHermitian.spectrum_conjTranspose_mul_mul_subset_Icc` (Ritz values in
$[a, a']$); `Matrix.IsHermitian.cfc_inv_eq_pinv` (the brief's D12 lemma);
`Matrix.IsHermitian.norm_toLp_cfc_mulVec_sq` ($\|\psi(\mathbf{A})\mathbf{x}\|^2 =
\mathbf{x}^{\mathsf{H}}\psi^2(\mathbf{A})\mathbf{x}$); `Matrix.IsHermitian.norm_star_dotProduct_cfc_mulVec_le`
(Cauchy–Schwarz: $\lvert\varphi\rvert \le \lvert\psi\chi\rvert$ on the spectrum gives
$\lvert\mathbf{x}^{\mathsf{H}}\varphi(\mathbf{A})\mathbf{y}\rvert \le
\|\psi(\mathbf{A})\mathbf{x}\|\|\chi(\mathbf{A})\mathbf{y}\|$).
`Matrix/Functions/Polynomial.lean`: `Matrix.IsHermitian.aeval_nodal_eq_zero` (the nodal
polynomial of a set containing the spectrum annihilates). `Krylov/Basic/Space.lean`:
`krylovSpace_add_smul_one` (shift invariance, real shift `s : ℝ` as its consumers use; K1's
skeleton has none, so K2 adds it).

**`Polynomial/Approximation/Stieltjes.lean`** (2 definitions, 16 theorems): the structure and
predicate; `integrable_inv_add`, `congr`, `apply_eq_resolventTransform`, `nonneg`, `pos`,
`antitoneOn`, `monotoneOn_mul_self`; `mul_le_mul_of_ae_le` (kernel ratio, $\mu$-almost
everywhere, to function ratio);
`rpow_mul_add_le` (the kernel inequality $x^\alpha(y + t) \le (a'/a)^E y^\alpha(x + t)$ on
$[a, a']$) and `HasStieltjesMeasure.rpow_mul_le` (Lemma 6); instances `hasStieltjesMeasure_inv`
($\delta_0$), `hasStieltjesMeasure_inv_add` ($\delta_s$), `.add`, `.smul` (by `ℝ≥0`),
`isStieltjes_zero`, `isStieltjes_rpow_neg` (Mathlib's measure restricted to $(0, \infty)$ with
density $t^{p-1}$, $p = 1 - \gamma$).

**`Polynomial/Interpolation/Stieltjes.lean`** (6 theorems): `inv_add_sub_eval_interpolate` and
`div_add_sub_eval_interpolate` (one kernel, an algebraic identity);
`HasStieltjesMeasure.sub_eval_interpolate_eq`, `.exists_sub_eval_interpolate_eq` (Lemma 4.1);
`.sub_eval_interpolate_eq_of_div`, `.exists_sub_eval_interpolate_eq_of_div` (Lemma 4.2, nonempty
nodes). All for any finite set of positive nodes, not only Ritz values. The `exists_` forms return
the remainder's measure $\varrho$ with $\varrho \ll \mu$, so that a ratio bound holding
$\mu$-almost everywhere reaches $\varsigma$.

**`Krylov/Basic/Compression.lean`** (3 theorems, every $\mathbf{A}$ unless stated):
`HasOrthonormalCols.conjTranspose_mulVec_aeval_mulVec_eq` ($\deg p \le q$);
`HasOrthonormalCols.mulVec_aeval_conjTranspose_mul_mul_mulVec_eq` ($\deg p < q$, exactness);
`HasOrthonormalCols.conjTranspose_mulVec_aeval_nodal_mulVec_eq_zero` (Hermitian; orthogonality
(11)). These are the brief's deferred "compression lemmas" (K0 note §6), placed in the file D12
named.

**`Krylov/Functions/LanczosFA.lean`** (2 definitions, 17 theorems): `compressedCfc_eq_of_range_eq`;
`HasOrthonormalCols.compressedCfc_eq` (every $\mathbf{A}$);
`compressedCfc_eq_of_mul_conjTranspose_mul_self` (partial isometries, every $\mathbf{A}$);
`Matrix.IsHermitian.compressedCfc_inv_eq_galerkinInverse`; `lanczosFA_mem_krylovSpace`;
`lanczosFA_zero`; `HasOrthonormalCols.lanczosFA_eq` (`Result: lanczos-fa-formula`);
`HasOrthonormalCols.lanczosFA_eq_aeval_mulVec` (interpolation at Ritz values);
`Matrix.IsHermitian.lanczosFA_eval` (exactness); `.lanczosFA_congr`; `.lanczosFA_sub`;
`.lanczosFA_eq_cfc_mulVec_of_krylovGrade_le`;
`.norm_cfc_mulVec_sub_lanczosFA_le_of_isUniformApproxOn` (the paper's (2),
`Result: lanczos-fa-uniform-bound`); `.lanczosFA_inv_eq_cgIterate`
(`lanczosFA A (fun x => x⁻¹) b q = cgIterate A b 0 q`, K1's `cgIterate` from the zero start, every
Hermitian $\mathbf{A}$, through $0^{-1} = 0$ and `pinv`); `.lanczosFA_inv_add_eq_cgIterate`
(`cgIterate (A + s • 1) b 0 q`); `lanczosFA_eq_arnoldiMatrix` (every $\mathbf{A}$ and every $q$,
with no grade hypothesis: stronger than K0's `Matrix.PosDef.cgIterate_eq_arnoldiMatrix` and
`cgIterate_eq_lanczosMatrix`, which take `q + 1 ≤ krylovGrade A b` because $\mathbf{T}^{-1}$ fails
on the padded compression; for $f(\mathbf{T})$ the partial-isometry frame form
`compressedCfc_eq_of_mul_conjTranspose_mul_self` with
`gramSchmidtQ_mul_conjTranspose_gramSchmidtQ_mul_self` and
$\mathbf{Q}^{\mathsf{H}}\mathbf{b} = \|\mathbf{b}\|\mathbf{e}_0$ suffices);
`Matrix.IsHermitian.lanczosFA_eq_lanczosMatrix` (`Result: lanczos-fa-recurrence`).

**`Krylov/Functions/NearOptimality.lean`** (10 theorems):
`Matrix.IsHermitian.re_quadForm_cfc_sub_le_of_sub_eq_aeval_mulVec` (the abstract step, with
`1 ≤ R`); `Matrix.PosDef.re_quadForm_cfc_cfc_mulVec_sub_lanczosFA_le_of_hasStieltjesMeasure`
(Theorem 5, any $\nu$, measure as data, kernel bound $\mu$-a.e.);
`Matrix.PosDef.re_quadForm_cfc_cfc_mulVec_sub_lanczosFA_le` (its `IsStieltjes` corollary, kernel
bound for every $t$);
`Matrix.IsHermitian.re_quadForm_rpow_cfc_mulVec_sub_lanczosFA_le` (Theorem 1);
`Matrix.PosDef.re_quadForm_rpow_cfc_mulVec_sub_lanczosFA_le_pseudoConditionNumber`;
`Matrix.IsHermitian.norm_cfc_mulVec_sub_lanczosFA_le_mul_norm_sub` (Euclidean, unsquared);
`Matrix.IsHermitian.re_quadForm_rpow_sub_cgIterate_add_smul_one_le` (shifted CG, checkpoint 1);
`Matrix.IsHermitian.re_quadForm_rpow_sub_cgIterate_le` (CG);
`Matrix.IsHermitian.norm_sub_cgIterate_le_mul_norm_sub` (Remark 3). The three CG theorems use
K1's `cgIterate A b x₀ q` with a general start and compare with every $\mathbf{y}$ in
`AffineSubspace.mk' x₀ (krylovSpace A (b - A *ᵥ x₀) q)`, the set of K1's
`Matrix.PosDef.isMinOn_cgIterate`;
`Matrix.PosDef.exists_inv_add_le_re_quadForm_rpow_cfc_mulVec_sub_lanczosFA` (Theorem 2, K2b).

**`Krylov/Functions/Quadrature.lean`** (2 theorems): `Matrix.IsHermitian.star_dotProduct_lanczosFA_eval`
(exact for $\deg p < 2q$); `.norm_star_dotProduct_sub_lanczosFA_le_of_isUniformApproxOn`
($\lvert\mathbf{b}^{\mathsf{H}}(\cdot)\rvert \le 2\varepsilon\|\mathbf{b}\|^2$, the norm in $\Bbbk$ of a
real quantity, so no `re`). No quadrature definition (brief: "no new name").

Names follow §4: conclusion spelled from the head symbols, `_of_<hypothesis>` where two bounds on
the same quantity differ by hypothesis (`_of_isUniformApproxOn` against the near-optimality
form `_le_mul_norm_sub`). None says how good a bound is.

## 5. The proof plan, step by step

Section numbers are the paper's. "Lemma X" names the library lemma; *new* marks a skeleton
statement; sizes are lines of proof.

**Step 0. Reduction to a frame (Theorem 5, setup).** Positive definite $\mathbf{A}$; cases
$q = 0$ or $\mathbf{b} = \mathbf{0}$ are trivial (both sides of the conclusion are explicit, and
$(R + 1)^2/(4R) \ge 1$). Otherwise choose a frame `Q : Matrix n (Fin r) 𝕜` of the Krylov space
(`exists_hasOrthonormalCols_range_eq`, $r$ = `finrank_krylovSpace`, $1 \le r \le q$),
$\mathbf{T} = \mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$, positive definite
(`Matrix.PosDef.conjTranspose_mul_mul_same` with an injective $\mathbf{Q}$), and $s$ = the finite
spectrum of $\mathbf{T}$ as a `Finset` (`Matrix.finite_real_spectrum`): nonempty, positive
(`Matrix.PosDef.spectrum_subset_Ioi`), with at most $r \le q$ elements (the spectrum is the image
of the $r$ eigenvalues, `Matrix.IsHermitian.spectrum_eq_image_eigenvalue`; a private lemma). 40
lines. Easy.

**Step 1. Interpolation at the Ritz values, (9).**
`HasOrthonormalCols.lanczosFA_eq_aeval_mulVec` with $p$ = `Lagrange.interpolate s id f`
(`Lagrange.degree_interpolate_lt`, `Lagrange.eval_interpolate_at_node`): $f_q = p(\mathbf{A})\mathbf{b}$.
Its own proof: the frame form, `Matrix.IsHermitian.cfc_eq_aeval_of_forall_eval_eq` on
$\mathbf{T}$, exactness from Compression. 30 lines plus Compression (130). Easy.

**Step 2. The error representation, Lemma 4.** On $(0, \infty)$, $f - p = \sigma\,\pi_s\,\varsigma$
with $\sigma = \pm 1$ and $\varsigma$ Stieltjes (*new*
`HasStieltjesMeasure.exists_sub_eval_interpolate_eq`, `_of_div`). Scalar proof: the kernel identity
(`inv_add_sub_eval_interpolate`: $1 - (z + t)q_t(z)$ has degree at most $\lvert s\rvert$ and
vanishes on $s$, so it is $c\,\pi_s$ by `Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero`,
and $z = -t$ gives $c$); then integrate in $t$: by `Lagrange.interpolate_apply` the interpolant is
$\sum_{\theta}f(\theta)\ell_\theta(z)$, and $f(\theta) = \int(\theta + t)^{-1}d\mu$, so the
interpolant of $f$ is the integral of the interpolants (`MeasureTheory.integral_finsetSum`,
`MeasureTheory.integral_sub`). Integrability: $(z + t)^{-1}\prod_\theta(\theta + t)^{-1} \le
C(1 + t)^{-1}$ for $t \ge 0$, and in the second class $t/\prod_\theta(\theta + t) \le 1$ with one
node. The remainder measure is `μ.withDensity` of $\prod_\theta(\theta + t)^{-1}$ (resp. $t$ times
it), whose `HasStieltjesMeasure` fields follow from `MeasureTheory.withDensity_apply` and
`integral_withDensity_eq_integral_smul`. Then on the matrix: since the spectrum of $\mathbf{A}$ is
in $(0, \infty)$, `cfc_congr`, `cfc_mul` and `cfc_polynomial` turn the scalar identity into
$f(\mathbf{A})\mathbf{b} - f_q = \sigma\pi_s(\mathbf{A})\varsigma(\mathbf{A})\mathbf{b}$; the sign
is absorbed into the polynomial ($\sigma\pi_s$ is orthogonal too). 300 lines scalar, 40 matrix.
Medium: integrability bookkeeping and the Lagrange API.

**Step 3. Orthogonality, (11).** *new*
`HasOrthonormalCols.conjTranspose_mulVec_aeval_nodal_mulVec_eq_zero`: degree $\lvert s\rvert \le q$,
so $\mathbf{Q}^{\mathsf{H}}\pi_s(\mathbf{A})\mathbf{b} = \pi_s(\mathbf{T})\mathbf{Q}^{\mathsf{H}}\mathbf{b}$
(Compression) and $\pi_s(\mathbf{T}) = \mathbf{0}$ (`Matrix.IsHermitian.aeval_nodal_eq_zero`). The
abstract step wants $\mathbf{K}^{\mathsf{H}}\pi(\mathbf{A})\mathbf{b} = \mathbf{0}$: the frame and
the Krylov matrix have the same range (`rangeProjector_inj`,
`conjTranspose_mul_rangeProjector`, as in `Galerkin.lean`). 40 lines. Easy.

**Step 4. The ratio bound, Lemma 6.** For Theorem 5 the hypothesis is on the kernel,
$\mu$-almost everywhere; it holds $\varrho$-almost everywhere since $\varrho \ll \mu$, and *new*
`HasStieltjesMeasure.mul_le_mul_of_ae_le` integrates it ($\nu(x)/(x + t) \le R\nu(y)/(y + t)$,
`MeasureTheory.integral_mono_ae`, `integral_const_mul`). For Theorem 1, *new*
`rpow_mul_add_le`: for $x \le y$ the ratio of $g(z) = z^\alpha/(z + t)$ lies between
$(x/y)^\alpha$ and $(x/y)^{\alpha - 1}$ because $1 \le (y + t)/(x + t) \le y/x$; with
$x/y \ge a/a'$ and $E \ge 1/2 > 0$ both directions are at most $(a'/a)^E$ (`Real.rpow_le_rpow_left_iff`,
`Real.rpow_natCast`, `Real.div_rpow`). 80 lines. Medium (real powers with signed exponents).

**Step 5. The abstract step, the proof of Theorem 5.** *new*
`Matrix.IsHermitian.re_quadForm_cfc_sub_le_of_sub_eq_aeval_mulVec`. With $g = \nu\varsigma \ge 0$
on the spectrum, $c = \min g$ over the finite spectrum and $g \le Rc$: if $c = 0$ then $g = 0$, so
$\varsigma = 0$ on the spectrum and the error is $\mathbf{0}$; the conclusion $0 \le
(R + 1)^2/(4R)\,\|\cdot\|^2$ then needs $R > 0$, which is why the step assumes $1 \le R$
(Theorem 5 derives it from the kernel bound at $x = y$, $t = 0$ for nonempty $n$; for empty $n$
both sides are $0$). Otherwise set
$\hat g = 2Rc/(R + 1)$ and $\tau = (R - 1)/(R + 1)$; the scalar fact $\lvert g - \hat g\rvert \le
\tau g$ on $[c, Rc]$ is two lines of `field_simp`/`nlinarith`. For
$\mathbf{d} = \mathbf{y} - \mathbf{y}_0 \in \mathcal{K}_q$:
$\langle\mathbf{d}, \mathbf{e}\rangle_\nu = \mathbf{d}^{\mathsf{H}}((g - \hat g)\pi)(\mathbf{A})\mathbf{b}
+ \hat g\,\mathbf{d}^{\mathsf{H}}\pi(\mathbf{A})\mathbf{b}$, the second term zero by
`forall_mem_range_star_dotProduct_eq_zero_iff`; the first is bounded by
`Matrix.IsHermitian.norm_star_dotProduct_cfc_mulVec_le` with $\psi = \sqrt\nu$,
$\chi = \tau\sqrt\nu\,\varsigma\pi$, and `norm_toLp_cfc_mulVec_sq` identifies the two norms with
$\|\mathbf{d}\|_\nu$ and $\tau\|\mathbf{e}\|_\nu$. The paper's Pythagoras and projection are
replaced by one inequality, private: $\lvert\operatorname{Re}\langle\mathbf{d}, \mathbf{e}\rangle\rvert
\le \tau\|\mathbf{d}\|\|\mathbf{e}\|$ implies $(1 - \tau^2)\|\mathbf{e}\|^2 \le
\|\mathbf{e} - \mathbf{d}\|^2$ (complete the square;
`Matrix.IsHermitian.re_quadForm_add`), and $1/(1 - \tau^2) = (R + 1)^2/(4R)$. 150 lines.
Medium; the main risk is the bookkeeping of `cfc` products, which the `cfc_mul`/`cfc_congr`
pattern of `Matrix/Functions` handles.

**Step 6. Theorem 1 and corollaries.** Theorem 5 with $\nu(x) = x^\alpha$
(`CFC.rpow_eq_cfc_real`, positive definite so `0 ≤ A`), $R = (a'/a)^E$ from Step 4, and
$(R + 1)^2/(4R) = (\tfrac12(R^{1/2} + R^{-1/2}))^2$ (`Real.rpow_add`, `Real.rpow_neg`); the
spectrum hypothesis gives positive definiteness as in K0 (`Matrix.IsHermitian.posDef_iff_eigenvalue_pos`).
$\kappa$ form: the extreme eigenvalues, `Matrix.IsHermitian.spectrum_subset_iff`,
`Matrix.PosDef.pseudoConditionNumber_eq` (as K0's $\kappa$ corollary). Euclidean: $\alpha = 0$,
`CFC.rpow_zero`, square roots of both sides. CG: `Matrix.IsHermitian.lanczosFA_inv_eq_cgIterate`,
`Matrix.PosDef.inv_eq_cfc`, and the reduction of a start $\mathbf{x}_0$ to the zero start with
right-hand side $\mathbf{r}_0$ (K1's definition unfolds to it). 140 lines. Easy.

**Checkpoint 1: the single shifted inverse, before any measure theory.** Yes. For
$f(z) = (z + s)^{-1}$ Step 2 is the kernel identity at $t = s$ alone ($\varsigma(z) =
(z + s)^{-1}/\prod_\theta(\theta + s)$, no integral), Step 4 is `rpow_mul_add_le` at $t = s$, and
Steps 0, 1, 3, 5 are unchanged. The result is *new*
`Matrix.IsHermitian.re_quadForm_rpow_sub_cgIterate_add_smul_one_le`, the near-optimality of CG on
shifted systems in every $\mathbf{A}^\alpha$-norm, stated through
`Matrix.IsHermitian.lanczosFA_inv_add_eq_cgIterate`; its $s = 0$ cases
(`re_quadForm_rpow_sub_cgIterate_le`, `norm_sub_cgIterate_le_mul_norm_sub`) come with it. This
checkpoint contains the whole matrix argument; the Stieltjes stage after it is scalar analysis
plus 120 lines of assembly. Its proof imports only `inv_add_sub_eval_interpolate` and
`rpow_mul_add_le`, which sit in the Stieltjes files but use no measure; a proof agent may prove
those two first.

**Size and difficulty.** About 2050 lines for the upper bound and Lanczos-FA, in the table of §7.
The hard parts, honestly: Step 2's integrability and the Lagrange interchange (the largest
scalar piece, but routine measure theory); Step 4's real-power case analysis (fiddly, short);
Step 5's `cfc` bookkeeping; the partial-isometry frame form behind `lanczosFA_eq_arnoldiMatrix`
(an interpolating polynomial on the union of two finite spectra); and `isStieltjes_rpow_neg`
(measure restriction and density; not needed by any theorem of the stage, only by users who want
$z^{\pm 1/2}$, so it may slip to the end). Nothing needs a new interface or a Mathlib gap
filled.

**Infrastructure that was expected and is not needed.** Matrix-valued integrals and their
interaction with `cfc` (§1); the $\mathbf{A}$-norm of an integral; CG on $\mathbf{A} + t\mathbf{I}$
for a family of $t$ (only one shift, in checkpoint 1, and there through the frame form); the
distinctness of the Ritz values (the nodal polynomial is over the set of Ritz values); the grade
hypothesis $m < M$. **Needed and missing**, all listed in §4: the five HermitianCalculus
additions, `aeval_nodal_eq_zero`, shift invariance, the compression lemmas, and the scalar
inequalities ($\lvert g - \hat g\rvert \le \tau g$, the completed square, the kernel inequality),
the first two private to `NearOptimality.lean`.

## 6. The optimality of the constant (Theorem 2): stage K2b

Decided (2026-10-17, relayed by the coordinator): Theorem 2 is a stage K2b right after K2; its
statement is fixed now.

K2b also holds Greenbaum's worst-case theorem for CG and MINRES (maintainer, 2026-10-17): for
every positive definite $\mathbf{A}$ and every $q$ there is a $\mathbf{b}$ whose CG error
(resp. MINRES residual) attains the spectrum-minimax bound, the minimum over residual
polynomials of degree at most $q$ of the maximum over the spectrum, relative to the initial
error (resp. residual). It shares the machinery of Theorem 2: explicit CG and Lanczos on a
matrix with few distinct eigenvalues, and discrete minimax duality. Shared lemmas foreseen:
the Ritz polynomial of a prescribed weighting (given weights $w_i > 0$ on $q + 1$ eigenvalues,
the $\mathbf{b}$ with $\lvert\mathbf{u}_i^{\mathsf{H}}\mathbf{b}vert^2 = w_i$ and its nodal
polynomial, the paper's Lemma 8, with uniqueness of the monic degree-$q$ polynomial
orthogonal to $\mathcal{K}_q$); Ritz values as Gauss quadrature nodes and weights for the
discrete spectral measure; divided differences on $q + 1$ nodes and the weighted
least-squares minimum on them (the paper's Lemma 9); the reduction of $\mathbf{b}$ to the
eigenvectors of $q + 1$ chosen eigenvalues; and discrete minimax duality (equioscillation, or
the dual characterisation of the best residual polynomial on a finite set through weights on
$q + 1$ points), which turns a minimax polynomial into the weights of the worst $\mathbf{b}$.

Statement, in the skeleton as
`Matrix.PosDef.exists_inv_add_le_re_quadForm_rpow_cfc_mulVec_sub_lanczosFA`: for positive
definite $\mathbf{A}$ with at least $q + 1 \ge 2$ distinct eigenvalues
(`q + 1 ≤ (spectrum ℝ A).ncard`), real $\alpha$ and $0 < \eta \le 1$, there are $\mathbf{b}$,
$s \ge 0$ and $\mathbf{y} \in \mathcal{K}_q$ with positive Lanczos-FA error for
$f(z) = (z + s)^{-1}$ and $(1 - \eta)^2 c^2\|f(\mathbf{A})\mathbf{b} - \mathbf{y}\|^2_{\mathbf{A}^\alpha}
\le$ the squared error, $c$ the factor of Theorem 1 in $\kappa(\mathbf{A})$. The positive error
excludes the trivial instances; "$\exists \mathbf{y}$" is the bound against the minimum. The
paper's $\kappa > 1$ follows from two distinct positive eigenvalues and is not a hypothesis.

Plan: restrict $\mathbf{b}$ to $q + 1$ eigenvectors including the extreme ones; Lemma 8 (the
weights (14) prescribe $\pi(\lambda_i) = g_i\omega_i/G$; needs uniqueness of the monic degree-$q$
polynomial with $\pi(\mathbf{A})\mathbf{b} \perp \mathcal{K}_q$, from the grade, and divided
differences, which Mathlib has only through `Lagrange` sums); Lemma 9 (weighted least squares on
$q + 1$ nodes); the exact ratio (15); and two limits ($s \to \infty$ when $\alpha > 1/2$, and the
interior weights $\delta \to 0$), each turned into an explicit choice to avoid filters. Estimate
700 to 1000 lines, hard (the limits and Lemma 8). Recommendation: a stage K2b after the upper
bound lands, in `NearOptimality.lean` if it fits the 1000-line budget; otherwise the file splits
by statement into `NearOptimality.lean` (the bounds) and `Krylov/Functions/Optimality.lean` (the
factor is optimal), not into a "part 2".

## 7. Files, imports, placement, order

Import diagram ("uses" is a direct import):

- `Polynomial/Approximation/Stieltjes.lean` uses Mathlib only (`Pow.Real`, `Measure.Dirac`,
  `Measure.ResolventTransform`; `Rpow.IntegralRepresentation` as a private import for the proof
  of `isStieltjes_rpow_neg`).
- `Polynomial/Interpolation/Stieltjes.lean` uses Approximation/Stieltjes, Mathlib `Lagrange`,
  `WithDensity`.
- `Matrix/Functions/HermitianCalculus.lean` gains `Matrix/Pseudoinverse/Pinv` as an import
  (checked: no cycle; Pinv's closure does not contain HermitianCalculus).
- `Krylov/Basic/Compression.lean` uses Space, `Matrix/Functions/Polynomial`.
- `Krylov/Functions/LanczosFA.lean` uses Compression, `Krylov/LinearSystems/CGLanczos` (hence CG,
  Galerkin and the Lanczos recurrence), ForMathlib `UniformApproximation`.
- `Krylov/Functions/NearOptimality.lean` uses LanczosFA, Interpolation/Stieltjes.
- `Krylov/Functions/Quadrature.lean` uses LanczosFA.

So `Krylov/Functions/` sits above `LinearSystems/` and `Processes/`, which is why the CG and
Lanczos corollaries of Lanczos-FA live in LanczosFA.lean, not in a separate file as K0's
CGLanczos had to.

| File | Defs + theorems | Skeleton lines | Expected when proved |
|---|---|---|---|
| `Matrix/Functions/HermitianCalculus.lean` (additions) | 0 + 5 | 91 | +200 |
| `Matrix/Functions/Polynomial.lean` (addition) | 0 + 1 | 34 | +15 |
| `Krylov/Basic/Space.lean` (addition) | 0 + 1 | 34 | +40 |
| `Polynomial/Approximation/Stieltjes.lean` | 2 + 16 | 183 | 400 |
| `Polynomial/Interpolation/Stieltjes.lean` | 0 + 6 | 129 | 300 |
| `Krylov/Basic/Compression.lean` | 0 + 3 | 87 | 130 |
| `Krylov/Functions/LanczosFA.lean` | 2 + 17 | 273 | 450 |
| `Krylov/Functions/NearOptimality.lean` (upper bound) | 0 + 9 | 301 | 420 |
| `Krylov/Functions/Quadrature.lean` | 0 + 2 | 62 | 120 |
| **K2** | **4 + 60** | | **about 2070** |
| K2b: Theorem 2 | 0 + 1 | (in NearOptimality) | 700 to 1000 |

**Placement decision for the scalar files** (to be confirmed by the maintainer; cheap to move).
The Stieltjes class goes to `Polynomial/Approximation/Stieltjes.lean`, beside the other scalar
function classes whose approximation the layer studies (`BernsteinEllipse`,
`AnalyticApproximation`), and its interpolation error to
`Polynomial/Interpolation/Stieltjes.lean`, in the `Polynomial/Interpolation/` directory that
`docs/PORT_POLYNOMIAL.md` plans for interpolation error. No new `Polynomial/Stieltjes/`
directory: a directory per function class would scatter the layer. The alternative is a future
`Analysis/` layer for scalar function classes (Stieltjes, Bernstein, completely monotone,
operator monotone representations), a layout change worth making only when several such classes
exist. Confirmed by the maintainer (2026-10-17, "this is fine for stieltjes"); CONTRIBUTING §2's
line for `Polynomial/` is amended to "scalar approximation theory and the function classes it
approximates".

**Placement** (CONTRIBUTING §8 item 5), every addition outside the new files with its home:

| Declaration | Home | Reason |
|---|---|---|
| `IsStieltjes`, `HasStieltjesMeasure` and their API | `Polynomial/Approximation/Stieltjes.lean` (new) | a scalar function class; layer 0 holds scalar approximation theory and Krylov may import it (D12); not ForMathlib, whose files are Mathlib-ready facts named after a Mathlib file, while this is a library modelling choice |
| `rpow_mul_add_le` | Approximation/Stieltjes | a plain real inequality, but its only topic is the weighted Stieltjes kernel; it sits next to its integrated form |
| interpolation error of Stieltjes functions | `Polynomial/Interpolation/Stieltjes.lean` (new) | polynomial interpolation of a scalar function class |
| `HasOrthonormalCols.cfc_mul_mul_conjTranspose` | `Matrix/Functions/HermitianCalculus.lean` | functional calculus of a compression, beside the square case |
| `Matrix.IsHermitian.spectrum_conjTranspose_mul_mul_subset_Icc` | HermitianCalculus | the spectral-location API (`spectrum_subset_Icc_of_le`, `spectrum_subset_iff`) is there; `Matrix/Spectral/Interlacing.lean` has the eigenvalue form but not the `spectrum` vocabulary |
| `Matrix.IsHermitian.cfc_inv_eq_pinv` | HermitianCalculus | brief D12, beside `Matrix.PosDef.inv_eq_cfc` |
| `norm_toLp_cfc_mulVec_sq`, `norm_star_dotProduct_cfc_mulVec_le` | HermitianCalculus | quadratic forms of functions of one Hermitian matrix, beside `re_quadForm_cfc_eq_sum` |
| `Matrix.IsHermitian.aeval_nodal_eq_zero` | `Matrix/Functions/Polynomial.lean` | polynomials in a matrix |
| `krylovSpace_add_smul_one` | `Krylov/Basic/Space.lean` | a Krylov-space fact |
| compression lemmas, Ritz-polynomial orthogonality | `Krylov/Basic/Compression.lean` (new, D12) | compressions to a Krylov space; consumed by LanczosFA, Quadrature, and later Ritz values (K4) and SLQ (K7) |
| `compressedCfc` | LanczosFA.lean | its only consumers are Lanczos-FA and quadrature; `galerkinInverse` got its own file because CG, PCG, CGLS and block CG share it; split off if a second consumer appears |
| CG and shifted-CG near-optimality | NearOptimality.lean | corollaries of the topic theorem, which a CG file cannot import; CG.lean's module docstring will point to them |

No placement flag is open.

**Order and commit checkpoints.** One proof agent per file, at most two at once (§11).

1. *C1, infrastructure*: the Matrix additions, `krylovSpace_add_smul_one`, Compression. One agent;
   the HermitianCalculus additions are independent of Compression and may go to a second agent.
2. *C2, Lanczos-FA*: LanczosFA.lean. Commit: the definition and its API, with the CG identity.
3. *C3, checkpoint 1*: `inv_add_sub_eval_interpolate`, `rpow_mul_add_le` (in the Stieltjes
   files, measure-free), the abstract step and the three CG theorems of NearOptimality. Commit;
   the maintainer can review the matrix argument here.
4. *C4, Stieltjes*: the rest of the two Stieltjes files (`isStieltjes_rpow_neg` last).
   Independent of C2 and C3; may run in parallel with them.
5. *C5, the theorem*: Theorem 5, Theorem 1, $\kappa$ and Euclidean forms. Commit.
6. *C6*: Quadrature (independent after C2).
7. *K2b*: Theorem 2, after review.

## 8. Mathlib search and records

What matters from the search (grep in `.lake/packages/mathlib/Mathlib`). Bridges: Mathlib's
`MeasureTheory.resolventTransform` is the Stieltjes transform of a measure
(`HasStieltjesMeasure.apply_eq_resolventTransform`), and
`Real.exists_measure_rpow_eq_integral_rpowIntegrand₀₁` gives the instance $z^{-\gamma}$.
Searched, none: Pick or Nevanlinna functions; Stieltjes functions of operators or matrices;
Krylov spaces or Lanczos-FA; divided differences beyond `Lagrange` sums (matters for K2b); the
cardinality of the spectrum of a Hermitian matrix (a private lemma from
`Matrix.IsHermitian.spectrum_eq_image_eigenvalue`). Mathlib's `StieltjesFunction` is unrelated
(§2.1). The other Mathlib names the proofs use are cited where they are used (§5).

`docs/design/Mathlib-deviations.md`: additions with bridges, no numbered deviation:
`IsStieltjes`/`HasStieltjesMeasure` (bridge `apply_eq_resolventTransform`), `compressedCfc`,
`lanczosFA`. CONTRIBUTING §5.3 gains the two rows of §2. `docs/constants.toml`: nothing (the
constants are inline).

## 9. Literature and bibliography

New keys, added before citing (CONTRIBUTING §6):

```bibtex
@misc{ChenPersson2026,
  author = {Chen, Tyler and Persson, David},
  title = {Optimal near-optimality bounds for the {L}anczos method for matrix functions},
  year = {2026},
  eprint = {2608.07160v1},
  archivePrefix = {arXiv},
  primaryClass = {math.NA},
  url = {https://arxiv.org/abs/2608.07160v1},
  note = {Version 1, 7 August 2026}
}
@article{Schweitzer2025,
  author = {Schweitzer, Marcel},
  title = {Near instance optimality of the {L}anczos method for {S}tieltjes and related
           matrix functions},
  journal = {SIAM Journal on Matrix Analysis and Applications},
  volume = {46}, number = {3}, pages = {1846--1865}, year = {2025}
}
@article{FrommerGuttelSchweitzer2014,
  author = {Frommer, Andreas and G{\"u}ttel, Stefan and Schweitzer, Marcel},
  title = {Efficient and stable {A}rnoldi restarts for matrix functions based on quadrature},
  journal = {SIAM Journal on Matrix Analysis and Applications},
  volume = {35}, number = {2}, pages = {661--683}, year = {2014}
}
@article{Saad1992,
  author = {Saad, Yousef},
  title = {Analysis of some {K}rylov subspace approximations to the matrix exponential
           operator},
  journal = {SIAM Journal on Numerical Analysis},
  volume = {29}, number = {1}, pages = {209--228}, year = {1992}
}
```

The arXiv data of `ChenPersson2026` are from the PDF's margin stamp. The other three are copied
from the paper's reference list; DOIs and the locators below are to be verified against the
articles before the PR: `Saad1992` Lemma 3.1 (polynomial exactness) and §3.2 (exactness past the
grade, as the paper cites it); `FrommerGuttelSchweitzer2014` (3.9) (the paper's citation for
Lemma 4); `Schweitzer2025` Theorems 3.1 and 4.1; `GolubMeurant2010` §4 (orthogonality (11), as
the paper cites it) and Chapter 7 (Gauss quadrature for $\mathbf{b}^{\mathsf{H}}f(\mathbf{A})\mathbf{b}$).
`Matrix.IsHermitian.lanczosFA_eval` cites `Saad1992` alone. The paper's [Che24] (the maintainer's handbook,
for (9)) is not cited: only `ChenPersson2026` is cleared (brief §9 and question 3).
`ChenPersson2026` locators used: (1), (2), (5), (6), (9), (11), (14), (15), §1.1, §1.4,
Lemma 4 (parts 1 and 2), Theorem 5, Lemma 6, Theorem 1, Remark 3, Theorem 2, Lemmas 8 and 9.
No passage of the paper is quoted in a repository file.

Result ids: `lanczos-fa-formula`, `lanczos-fa-uniform-bound`, `lanczos-fa-recurrence`,
`lanczos-fa-near-optimality` (Theorem 1 and its Euclidean form), and for K2b
`lanczos-fa-near-optimality-lower-bound` (not "sharp": ids, like names, do not grade a bound).

## 10. Consumers

`lanczosFA`: SLQ and Hutch++ with Lanczos (K7) through Quadrature; random-start Lanczos (K5)
does not need it. The frame form and the compression lemmas: Ritz values and Kaniel–Paige–Saad
(K4). `compressedCfc`: block Lanczos-FA in the block round (`compressedCfc A f
(blockKrylovMatrix A B q) * B`, no new definition, as for `galerkinInverse`). `IsStieltjes`:
the near-optimality theorems; a later rational-function near-optimality (brief §4) and Nyström
PCG (K8) only through shifted CG. The abstract step: any later near-optimality proof with a
factored error (the rational case of [Ams+24] in the paper's list). The CG corollaries: K1's
Euclidean-norm statements for CG may cite `norm_sub_cgIterate_le_mul_norm_sub`, beside K1's
Chebyshev rate `Matrix.IsHermitian.re_quadForm_sub_cgIterate_le_four_mul_pow` (K1's rename of
K0's `re_quadForm_sub_cgIterate_le_two_mul_pow`, the $\kappa = a'/a$ form).

## 11. Decisions

Decided (2026-10-17, relayed by the coordinator after an independent review): Theorem 2 is
stage K2b, right after K2 (§6); Theorem 5 is public, with the measure as data and the kernel
bound almost everywhere, and the `IsStieltjes` all-$t$ form as a corollary (§3).

Settled (2026-10-17, maintainer: "this is fine for stieltjes"): **the home and shape of
Stieltjes functions**, `Polynomial/Approximation/Stieltjes.lean` and
`Polynomial/Interpolation/Stieltjes.lean` (§7), with the measure a `Measure ℝ` null on
$(-\infty, 0)$ and the values constrained on $(0, \infty)$ only; CONTRIBUTING §2 amended.
No question is open.
