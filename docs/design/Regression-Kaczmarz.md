# Design note: randomized Kaczmarz and sketch-and-project

Draft of 2026-10-19, revised the same day after a bounded Fable review (verdict: approve after two
blocking fixes and the should-fixes; all are folded in, see the revision log at the end). Branch
`regression/sketch-precondition` (worktree `nlalib-block`, head `bc72b8d`). Approved 2026-10-19.
Maintainer request (2026-10-19): "Let's do sketch and precondition and Randomized kaczmarz." This
note covers randomized Kaczmarz with its convergence guarantees, framed as an instance of
sketch-and-project. Sketch-and-precondition and iterative sketching are in the concurrent note
`docs/design/Regression-SketchPrecondition.md` (§10 lists what the two share). The file name follows
the request; §7 argues that the Lean files belong in `Solvers/`, as `docs/PORT_KRYLOV.md` D12
(approved 2026-10-17) already decided.

Maintainer decision (2026-10-19), applied to the whole round: "for sketch and precondition, dont
worry about rates now". No explorer Rates rows are proposed; the `exists_forall_` forms that
CONTRIBUTING §5.2 rule 3 requires stay.

**Approved by the maintainer, 2026-10-19** ("good to all, except frobConditionNumber add pseudo
since it is A^+"): D1 (sketch-and-project as the definition, Kaczmarz as its instance), D2 (the
i.i.d.-sequence idiom `HasLaw ξ (Measure.infinitePi fun _ : ℕ => ν) μ`, a new §5.3 row) and D3 (a
named Frobenius condition number, which reverses a remark in `Matrix-Pseudoinverse.md` §8), with D3's
name changed to `frobPseudoConditionNumber`, since it is built from $\mathbf{A}^{+}$, in line with
`pseudoConditionNumber`. Everything else in §11 proceeds as recommended. The skeleton waits for the
library-wide naming audit (maintainer: "just wait for audit"), and names here follow its grammar
once adopted.

**Scope recommendation.** This round:
* the sketch-and-project step and iterate (Euclidean metric) and their deterministic geometry;
* Gower–Richtárik's two expectation theorems for consistent systems under a Loewner bound on the
  expected projector, extended to rank-deficient systems;
* randomized Kaczmarz over `RCLike` with squared-row-norm sampling: the one-step expectation
  inequality for any right-hand side (an identity when no row is zero); one primary bound covering
  consistent and inconsistent systems with no rank assumption (Strohmer–Vershynin's rate,
  Zouzias–Freris's horizon); the any-right-hand-side bound about the least-squares solution nearest
  $\mathbf{x}_0$; the consistent corollaries; Kaczmarz with any row probabilities through
  sketch-and-project; the mean iterate as a Richardson (Landweber) iterate; iteration counts and their
  `exists_forall_` forms.

Deferred: randomized extended Kaczmarz, block Kaczmarz with pavings, a general metric
$\mathbf{B}$, almost-sure convergence, adaptive (greedy) row selection, Rates rows (§6). About
1,300 lines: two new Solvers files, one new ForMathlib file, and small additions to four existing
files.

## 0. Sources read

PDFs fetched into the session scratchpad and read for the parts cited:

* [StrohmerVershynin2009] T. Strohmer, R. Vershynin, *A randomized Kaczmarz algorithm with
  exponential convergence*, J. Fourier Anal. Appl. 15 (2009); arXiv:math/0702226. Algorithm 1 (row
  $i$ with probability $\|\mathbf{a}_i\|^2/\|\mathbf{A}\|_{\mathsf{F}}^2$), Theorem 2 (rate
  $1 - \kappa(\mathbf{A})^{-2}$, $\kappa(\mathbf{A}) = \|\mathbf{A}\|_{\mathsf{F}}\|\mathbf{A}^{-1}\|_2$
  for a left inverse; stated over $\mathbb{C}^n$), §2.1 (11) (iterations
  $\approx 2\kappa^2\log(1/\varepsilon)$ for error $\varepsilon\|\mathbf{e}_0\|$), Theorem 3 (lower bound).
* [Needell2010] D. Needell, *Randomized Kaczmarz solver for noisy linear systems*, BIT 50 (2010);
  arXiv:0902.0958v2. Theorem 2.1: full column rank, consistent $\mathbf{A}\mathbf{x} = \mathbf{b}$ run
  with $\mathbf{b} + \mathbf{r}$; $\mathbb{E}\|\mathbf{x}_k - \mathbf{x}\| \le (1 - 1/R)^{k/2}\|\mathbf{x}_0 - \mathbf{x}\|
  + \sqrt{R}\,\gamma$, $R = \|\mathbf{A}^{-1}\|^2\|\mathbf{A}\|_{\mathsf{F}}^2$, $\gamma = \max_i |r_i|/\|\mathbf{a}_i\|$.
* [ZouziasFreris2013] A. Zouzias, N. M. Freris, *Randomized extended Kaczmarz for solving least
  squares*, SIAM J. Matrix Anal. Appl. 34 (2013); arXiv:1205.5770v3. (2) $\kappa_{\mathsf{F}}^2 :=
  \|\mathbf{A}\|_{\mathsf{F}}^2\|\mathbf{A}^{+}\|_2^2$; Theorem 4 (rank-deficient consistent, limit
  $\mathbf{A}^{+}\mathbf{b}$, Lemma 6 assumes iterates in the row space); Theorem 7 and (5) (any
  $\mathbf{w}$, horizon $\|\mathbf{w}\|^2/\sigma_{\min}^2$, Needell's $\gamma$ improved, rank assumption
  dropped); Theorem 2 (column projections); Algorithm 3 and Theorem 8 (REK).
* [GowerRichtarik2015] R. M. Gower, P. Richtárik, *Randomized iterative methods for linear systems*,
  SIAM J. Matrix Anal. Appl. 36 (2015); arXiv:1506.03296v5. (2.2) sketch-and-project, (2.7)
  update, Theorem 2.1 (six viewpoints), §3.5 block Kaczmarz, Theorem 4.4 (4.6) (mean error
  $(\mathbf{I} - \mathbf{B}^{-1}\mathbb{E}\mathbf{Z})^k$), Lemma 4.5, Theorem 4.6 (mean-square error,
  $\mathbb{E}\mathbf{Z}$ positive definite). Their sketch $\mathbf{S} \in \mathbb{R}^{m \times q}$
  enters as $\mathbf{S}^{\mathsf{T}}\mathbf{A}$; ours is the library's left factor $\mathbf{S}\mathbf{A}$.
* [NeedellTropp2014] D. Needell, J. A. Tropp, *Paved with good intentions: analysis of a randomized
  block Kaczmarz method*, Linear Algebra Appl. 441 (2014); arXiv:1208.3805v3. Definition 1.1 (row
  paving), Theorem 1.2 (rate $1 - \sigma_{\min}^2/(\beta m)$, horizon $(\beta/\alpha)\|\mathbf{e}\|^2/\sigma_{\min}^2$).
* [LeventhalLewis2010] D. Leventhal, A. S. Lewis, *Randomized methods for linear constraints:
  convergence rates and conditioning*, Math. Oper. Res. 35 (2010); arXiv:0806.3015. Theorem 4.7:
  $\mathbb{E}[d(\mathbf{x}_{j+1}, S)^2 \mid \mathbf{x}_j] \le (1 - 1/(L^2\|\mathbf{A}\|_{\mathsf{F}}^2))\,d(\mathbf{x}_j, S)^2$
  with the Hoffman constant $L$ (for equations, $\|\mathbf{A}^{+}\|_2$): convergence to the
  projection of $\mathbf{x}_0$ onto the solution set, any rank.
* [MaNeedellRamdas2015] A. Ma, D. Needell, A. Ramdas, *Convergence properties of the randomized
  extended Gauss–Seidel and Kaczmarz methods*, SIAM J. Matrix Anal. Appl. 36 (2015);
  arXiv:1503.08235v3. (2.1) the complex update with $(\mathbf{X}^i)^*$, (2.2), Table 1.1 (which method
  converges to which solution in the four regimes).

Not read, cited nowhere: Dereziński–Rebrova (sharp sketch-and-project via RSVD), Steinerberger,
Gower–Richtárik's stochastic dual ascent. The Chen–Persson manuscript is not used. None of the seven
keys above is in `docs/references.bib` (§9).

## 1. The quarry

Modules `NLAlib.Solvers.Kaczmarz.{Core, KaczmarzExtensions, KaczmarzProbability, KaczmarzRowSpace}`
(884 lines, 33 declarations, none `sorry`) and `NLAlib.Solvers.SketchAndProject.{Core, Probability}`
(569 lines, 36 declarations), read from the sources and `atlas/declarations.json`.

How they model the algorithm. Real only, `⬝ᵥ` for norms, `frobSq`. `Kaczmarz.step A b x i` is the
explicit row update; `Kaczmarz.prob A i = ‖A i‖² / frobSq A`. The expectation is **not** a
probability integral: `expErr A b xs x k` is defined by first-step recursion
(`expErr (k+1) x = ∑ i, prob A i * expErr k (step A b x i)`), `run` executes a path
`Fin k → m`, `expErr_eq_sum_paths` identifies the recursion with a weighted path sum, and
`kaczmarzRowPathPMF A hA k : PMF (Fin k → m)` (a proof term in the definition) turns it into an
integral after the fact. The smallest singular value enters as the raw hypothesis
`hσ : ∀ v, σ ^ 2 * (v ⬝ᵥ v) ≤ (A *ᵥ v) ⬝ᵥ (A *ᵥ v)` (or its row-space restriction), repeated in
every theorem. The inconsistent results come in six near-copies (`expErr_le_add`,
`_add_div_sq`, each again `_of_sub_mem_range`, each again as an integral). Sketch-and-project is a
separate development over a finite family of sketches with its own `expErr`, `pathPMF`,
`iidPathPMF`, `iidPathLaw`, `sketchLaw`, `meanProjector`, `expectedProjector`; Kaczmarz is never
derived from it (the module docstring says so). `docs/port/inventory-sketching.md` §8 lists these
"finite path laws (five times)" and "Kaczmarz developed apart from sketch-and-project" as defects.

The quarry's one-step statements for inconsistent systems (`expected_sqErr_step_le_add` and its
row-space twin) are inequalities, and rightly: the expected residual term is a sum over the
*nonzero* rows only, since a zero row has weight $0$ and leaves the iterate unchanged. The new
library keeps that: the one-step statement is an inequality for every $\mathbf{A}$ and an identity
only when no row is zero (§5.2).

What is reused, as mathematics and proof material:
* the Pythagoras step (`sqErr_step`, `sqErr_step_eq_add`) and its residual term, which becomes the
  general identity `norm_sub_sketchAndProject_sq` (§3.2);
* the row-space invariance (`step_sub_mem_range_of_sub_mem_range`, `SketchProject.step_sub_mem_range`,
  whose `hB` transpose trick is replaced by `range_mulVecLin_pinv`);
* the recurrence-solving induction of `expErr_le_add`;
* the observation of `KaczmarzExtensions.expErr_zero_le_moorePenroseInverse` that from
  $\mathbf{x}_0 = \mathbf{0}$ the limit is $\mathbf{A}^{+}\mathbf{b}$, generalised to the least-squares
  solution nearest $\mathbf{x}_0$, for any right-hand side.

What is deliberately not reproduced: the first-step recursion and path sums as the definition of
expectation (replaced by `HasLaw` on an i.i.d. sequence, D2); `PMF`s with proof-term arguments;
the raw `hσ` hypotheses (replaced by `specNorm (pinv A)`, which needs none, D3); the six
inconsistent-system copies (one theorem, §5.2); the separate Kaczmarz step (an instance, D1); real
scalars and `⬝ᵥ` norms (§5.1 of CONTRIBUTING); finite sketch families (any law).

## 2. Inventory: what exists

Every name below was checked by grep (NLAlib at `bc72b8d`, Mathlib in `.lake/packages/mathlib`).
The new signatures of §§3–5 were elaborated, with `sorry` bodies, against the current build in two
scratch files in the session scratchpad (one Lean process each time); the revised signatures were
re-elaborated after the review, the sibling's `richardsonIterate` stubbed with its rectangular
signature.

**Matrix.** `pinv`, `pinv_mul : pinv A * A = rangeProjector Aᴴ`, `range_mulVecLin_pinv`,
`pinv_smul`, `pinv_of_isUnit`, `pinv_eq_conjTranspose_mul_pinv_mul_conjTranspose_self`,
`isLeastSquaresSolution_pinv_mulVec`, `IsLeastSquaresSolution.norm_pinv_mulVec_le`,
`IsLeastSquaresSolution.eq_pinv_mulVec_of_norm_le` (`Matrix/Pseudoinverse/`);
`norm_le_specNorm_pinv_mul_norm_mulVec_of_mem_range` ($\|\mathbf{x}\| \le \|\mathbf{A}^{+}\|_2\|\mathbf{A}\mathbf{x}\|$
on the row space, any rank), `specNorm_pinv` ($\|\mathbf{A}^{+}\|_2 = \sigma_k(\mathbf{A})^{-1}$ for
$k + 1 = \operatorname{rank}\mathbf{A}$), `smul_one_le_conjTranspose_mul_self_iff_specNorm_pinv_sq_le`
(`NormBounds.lean`); `pseudoConditionNumber` (`ConditionNumber.lean`);
`isStarProjection_rangeProjector`, `IsStarProjection.norm_toLp_sq_eq_add` (Pythagoras),
`rangeProjector_mulVec_eq_self_iff`, `rangeProjector_mono` (`Matrix/Basic/Projector.lean`);
`selectionMatrix`, `conjTranspose_selectionMatrix_mul`, `conjTranspose_selectionMatrix_mulVec`
(`Matrix/Basic/Selection.lean`); `frobNorm_sq_eq_sum_row`, `frobNorm_sq_eq_sum_range_singularValues_sq`;
`leverageScoreDistribution` (the precedent for a weight vector `m → ℝ≥0`).

**Probability.** `samplingMeasure p` (any weights `p : ι → ℝ≥0`, a probability measure when they sum
to one), `integral_samplingMeasure`, `isProbabilityMeasure_samplingMeasure`,
`samplingMeasure_const_inv_card` (`Probability/Distributions/Sampling.lean`); `hasLaw_pi_iff`,
`HasLaw.iIndepFun_eval` (`Probability/Law.lean`, the finite product idiom);
`IndepFun.integral_comp_eq_integral_integral` (`ForMathlib/Probability/Independence/Basic.lean`,
Fubini for an independent pair, from Hutch++); `Matrix.integral_quadForm`
(`Probability/MatrixIntegral.lean`); `measurable_pinv`, `measurable_rangeProjector`
(`Probability/Measurability/Matrix.lean`); `Measurable.matrix_mul`, `Measurable.matrix_mulVec`
(`ForMathlib/MeasureTheory/Matrix.lean`). `Matrix.integral_mulVec` does not exist (checked).

**Mathlib.** `Measure.infinitePi` (total: the zero measure unless every factor is a probability
measure), `measurePreserving_eval_infinitePi`, `Measure.infinitePi_map_pi`, `iIndepFun_infinitePi`,
`iIndepFun_iff_hasLaw_Pi_infinitePi`, `iIndepFun.indepFun_finset₀`, `IndepFun.comp`,
`HasLaw.integral_comp`, `aemeasurable_pi_lambda`, `DependsOn` with `dependsOn_iff_exists_comp`
(`Mathlib/Logic/Function/DependsOn.lean`; `MeasureTheory/Function/FactorsThrough.lean` has only the
converse direction, `Measurable.dependsOn_of_piFinset`), `Finset.coe_range`,
`Matrix.replicateRow`, `Matrix.replicateCol`, `Matrix.conjTranspose_replicateRow`,
`Real.one_sub_le_exp_neg`, `ContinuousLinearMap.integral_comp_comm`. Searched, none: Kaczmarz,
sketch-and-project, any iterated random map.

**How the library handles independent samples today.** Finite families only: a vector of
`|k|` i.i.d. indices has the single hypothesis `HasLaw ι (Measure.pi fun _ : k => samplingMeasure p) μ`
(`hasLaw_samplingSketchMatrix`), and proofs transport to the canonical product
(`samplingSketch_eq_map`, `iIndepFun_pi`). Nothing in the library uses `Measure.infinitePi` or an
ℕ-indexed sequence; `PORT_KRYLOV.md` D12 reserved "i.i.d. iterates on `Measure.infinitePi`" for
`Probability/` and gated Kaczmarz on it (stage K9).

## 3. Definitions

Letters, shared with the sibling note (§10): sketch row type `k`, iteration count `q`, error written
solution minus iterate, `xs - …Iterate …`.

### 3.1 The step and the iterate

```lean
-- NLAlib/Solvers/SketchAndProject.lean
variable {𝕜 : Type*} [RCLike 𝕜] {k m n : Type*} [Fintype k] [Fintype m] [Fintype n]

/-- The **sketch-and-project step**
$\mathsf{sketchAndProject}(\mathbf{A}, \mathbf{S}, \mathbf{b}, \mathbf{x}) := \mathbf{x} +
(\mathbf{S}\mathbf{A})^{+}\mathbf{S}(\mathbf{b} - \mathbf{A}\mathbf{x})$: the point nearest
$\mathbf{x}$ among the least-squares solutions of the sketched system
$\mathbf{S}\mathbf{A}\mathbf{y} = \mathbf{S}\mathbf{b}$, its solutions when that system is consistent
(`NLAlib.isLeastSquaresSolution_sketchAndProject`,
`NLAlib.norm_sketchAndProject_sub_le_of_isLeastSquaresSolution`). Total; the step is the identity
when $\mathbf{S}\mathbf{A} = \mathbf{0}$. Argument order: system, sketch, right-hand side, point, as
in `NLAlib.sketchAndSolve`. [GowerRichtarik2015, (2.2), (2.7)]; there with the metric $\mathbf{B}$
and the sketch $\mathbf{S}^{\mathsf{T}}$, here $\mathbf{B} = \mathbf{I}$. -/
noncomputable def sketchAndProject (A : Matrix m n 𝕜) (S : Matrix k m 𝕜) (b : m → 𝕜)
    (x : n → 𝕜) : n → 𝕜 :=
  x + pinv (S * A) *ᵥ (S *ᵥ (b - A *ᵥ x))

/-- The **sketch-and-project iterate** with sketches $\mathbf{S}_0, \mathbf{S}_1, \ldots$:
$\mathbf{x}_{q+1} = \mathsf{sketchAndProject}(\mathbf{A}, \mathbf{S}_q, \mathbf{b}, \mathbf{x}_q)$. -/
noncomputable def sketchAndProjectIterate (A : Matrix m n 𝕜) (S : ℕ → Matrix k m 𝕜) (b : m → 𝕜)
    (x₀ : n → 𝕜) : ℕ → n → 𝕜
  | 0 => x₀
  | q + 1 => sketchAndProject A (S q) b (sketchAndProjectIterate A S b x₀ q)
```

```lean
-- NLAlib/Solvers/Kaczmarz.lean
variable [DecidableEq m]

/-- The **randomized Kaczmarz iterate** with row choices $\iota_0, \iota_1, \ldots$: the
sketch-and-project iterate whose $q$-th sketch selects row $\iota_q$, so that each step is the
orthogonal projection onto the hyperplane
$\{\mathbf{y} : (\mathbf{A}\mathbf{y})_{\iota_q} = b_{\iota_q}\}$. The row-action formula
$$\mathbf{x}_{q+1} = \mathbf{x}_q + \frac{b_{\iota_q} - (\mathbf{A}\mathbf{x}_q)_{\iota_q}}
{\|\mathbf{a}_{\iota_q}\|^2}\,\overline{\mathbf{a}_{\iota_q}}$$
is `NLAlib.kaczmarzIterate_succ`; a zero row leaves the iterate unchanged.
[StrohmerVershynin2009, Algorithm 1]; [MaNeedellRamdas2015, (2.1)]. -/
noncomputable def kaczmarzIterate (A : Matrix m n 𝕜) (ι : ℕ → m) (b : m → 𝕜) (x₀ : n → 𝕜) :
    ℕ → n → 𝕜 :=
  sketchAndProjectIterate A (fun q => (selectionMatrix fun _ : Unit => ι q)ᴴ) b x₀
```

Notes on the choices (D1, D11):

* **Mathematical definitions, realisation as theorems** (the maintainer's direction of 2026-10-17
  and `Krylov-CG.md` §4). The step is defined as a projection through `pinv`; the familiar row
  update is the theorem `kaczmarzIterate_succ`, proved from the new Matrix lemma
  `pinv_replicateRow` (§7). The "six viewpoints" of [GowerRichtarik2015, Theorem 2.1] are not all
  stated; the two that consumers use are (nearest point, least-squares solution of the sketched
  system).
* **One sketch type per iterate.** The sequence is `ℕ → Matrix k m 𝕜` with fixed `k`. Kaczmarz uses
  `k = Unit` and `(selectionMatrix fun _ : Unit => i)ᴴ`, whose product with $\mathbf{A}$ is the row
  `A.submatrix (fun _ => i) id` (`conjTranspose_selectionMatrix_mul`); block Kaczmarz with blocks of
  one size uses `(selectionMatrix τ)ᴴ` for `τ : k → m`, and blocks of unequal sizes the
  $m \times m$ diagonal mask of the block (zero rows do not change the projection). The precedent for
  `Unit` is `blockKrylovMatrix_replicateCol`.
* **No `kaczmarzStep`.** The single step is `kaczmarzIterate A (fun _ => i) b x 1`, and every
  one-step statement is the case $q = 0$ of an iterate statement from a deterministic start.
* **The iterate is a function of the whole index sequence**, `ι : ℕ → m`, so a random iterate is
  `kaczmarzIterate A (ι ω) b x₀ q` for `ι : Ω → ℕ → m`. It depends only on `ι 0, …, ι (q-1)`
  (`dependsOn_sketchAndProjectIterate`, Mathlib's `DependsOn`).
* **Error order.** Statements write the error as `xs - …Iterate …`, as Krylov does
  (`re_quadForm_sub_cgIterate_le`) and the sibling's `sub_richardsonIterate_eq`, so the mean-error
  identity and the Richardson bridge rewrite without `neg_sub`. Row-space statements keep
  `…Iterate … - x₀ ∈ …`, as `pcgIterate_sub_mem_krylovSpace` does, and the start hypothesis is
  `xs - x₀ ∈ LinearMap.range Aᴴ.mulVecLin`.

### 3.2 Deterministic API (`Solvers/SketchAndProject.lean`)

```lean
theorem isLeastSquaresSolution_sketchAndProject (A : Matrix m n 𝕜) (S : Matrix k m 𝕜) (b : m → 𝕜)
    (x : n → 𝕜) : IsLeastSquaresSolution (S * A) (S *ᵥ b) (sketchAndProject A S b x)
theorem norm_sketchAndProject_sub_le_of_isLeastSquaresSolution {y : n → 𝕜}
    (hy : IsLeastSquaresSolution (S * A) (S *ᵥ b) y) :
    ‖WithLp.toLp 2 (sketchAndProject A S b x - x)‖ ≤ ‖WithLp.toLp 2 (y - x)‖

/-- The error after one step, for any reference point $\mathbf{x}_\star$: the complementary
projection of the error minus the sketched solution for the residual
$\mathbf{r} = \mathbf{b} - \mathbf{A}\mathbf{x}_\star$. -/
theorem sub_sketchAndProject_eq [DecidableEq n] (A : Matrix m n 𝕜) (S : Matrix k m 𝕜) (b : m → 𝕜)
    (x xs : n → 𝕜) :
    xs - sketchAndProject A S b x =
      (1 - rangeProjector (S * A)ᴴ) *ᵥ (xs - x) - pinv (S * A) *ᵥ (S *ᵥ (b - A *ᵥ xs))

/-- **Pythagoras for one step**, any reference point:
$\|\mathbf{x}_\star - \mathbf{x}^{+}\|^2 = \|\mathbf{x}_\star - \mathbf{x}\|^2
- \|\mathbf{P}(\mathbf{x}_\star - \mathbf{x})\|^2 + \|(\mathbf{S}\mathbf{A})^{+}\mathbf{S}\mathbf{r}\|^2$
with $\mathbf{P}$ the projector onto the row space of $\mathbf{S}\mathbf{A}$. -/
theorem norm_sub_sketchAndProject_sq (A : Matrix m n 𝕜) (S : Matrix k m 𝕜) (b : m → 𝕜)
    (x xs : n → 𝕜) :
    ‖WithLp.toLp 2 (xs - sketchAndProject A S b x)‖ ^ 2 =
      ‖WithLp.toLp 2 (xs - x)‖ ^ 2 - ‖WithLp.toLp 2 (rangeProjector (S * A)ᴴ *ᵥ (xs - x))‖ ^ 2 +
        ‖WithLp.toLp 2 (pinv (S * A) *ᵥ (S *ᵥ (b - A *ᵥ xs)))‖ ^ 2

theorem sketchAndProject_sub_mem_range (A : Matrix m n 𝕜) (S : Matrix k m 𝕜) (b : m → 𝕜)
    (x : n → 𝕜) : sketchAndProject A S b x - x ∈ LinearMap.range Aᴴ.mulVecLin
theorem sketchAndProjectIterate_sub_mem_range (A : Matrix m n 𝕜) (S : ℕ → Matrix k m 𝕜)
    (b : m → 𝕜) (x₀ : n → 𝕜) (q : ℕ) :
    sketchAndProjectIterate A S b x₀ q - x₀ ∈ LinearMap.range Aᴴ.mulVecLin
/-- For a consistent system the error never grows. -/
theorem norm_sub_sketchAndProjectIterate_le {A : Matrix m n 𝕜} {b : m → 𝕜} {xs : n → 𝕜}
    (hxs : A *ᵥ xs = b) (S : ℕ → Matrix k m 𝕜) (x₀ : n → 𝕜) (q : ℕ) :
    ‖WithLp.toLp 2 (xs - sketchAndProjectIterate A S b x₀ q)‖ ≤ ‖WithLp.toLp 2 (xs - x₀)‖
theorem dependsOn_sketchAndProjectIterate (A : Matrix m n 𝕜) (b : m → 𝕜) (x₀ : n → 𝕜) (q : ℕ) :
    DependsOn (fun S : ℕ → Matrix k m 𝕜 => sketchAndProjectIterate A S b x₀ q) (Set.Iio q)
theorem measurable_sketchAndProjectIterate (A : Matrix m n 𝕜) (b : m → 𝕜) (x₀ : n → 𝕜) (q : ℕ) :
    Measurable fun S : ℕ → Matrix k m 𝕜 => sketchAndProjectIterate A S b x₀ q
```

Only `sub_sketchAndProject_eq` takes `[DecidableEq n]` (for `1 - rangeProjector …`).

Kaczmarz realisation (`Solvers/Kaczmarz.lean`), `[DecidableEq m]` only:

```lean
@[simp] theorem kaczmarzIterate_zero : kaczmarzIterate A ι b x₀ 0 = x₀
/-- **The row-action formula.** -/
theorem kaczmarzIterate_succ (A : Matrix m n 𝕜) (ι : ℕ → m) (b : m → 𝕜) (x₀ : n → 𝕜) (q : ℕ) :
    kaczmarzIterate A ι b x₀ (q + 1) =
      kaczmarzIterate A ι b x₀ q +
        ((b (ι q) - (A *ᵥ kaczmarzIterate A ι b x₀ q) (ι q)) /
          ((‖WithLp.toLp 2 (A (ι q))‖ ^ 2 : ℝ) : 𝕜)) • star (A (ι q))
/-- Each step solves its equation [MaNeedellRamdas2015, (2.2)]. -/
theorem mulVec_kaczmarzIterate_succ_apply (hA : A (ι q) ≠ 0) :
    (A *ᵥ kaczmarzIterate A ι b x₀ (q + 1)) (ι q) = b (ι q)
/-- The one-step identity, any reference point and every row (for a zero row both fractions are
$0$ and the step is the identity), from `NLAlib.norm_sub_sketchAndProject_sq`. -/
theorem norm_sub_kaczmarzIterate_succ_sq (ι : ℕ → m) (xs : n → 𝕜) (q : ℕ) :
    ‖WithLp.toLp 2 (xs - kaczmarzIterate A ι b x₀ (q + 1))‖ ^ 2 =
      ‖WithLp.toLp 2 (xs - kaczmarzIterate A ι b x₀ q)‖ ^ 2 -
        ‖(A *ᵥ (xs - kaczmarzIterate A ι b x₀ q)) (ι q)‖ ^ 2 / ‖WithLp.toLp 2 (A (ι q))‖ ^ 2 +
        ‖(b - A *ᵥ xs) (ι q)‖ ^ 2 / ‖WithLp.toLp 2 (A (ι q))‖ ^ 2
theorem kaczmarzIterate_sub_mem_range (A : Matrix m n 𝕜) (ι : ℕ → m) (b : m → 𝕜) (x₀ : n → 𝕜)
    (q : ℕ) : kaczmarzIterate A ι b x₀ q - x₀ ∈ LinearMap.range Aᴴ.mulVecLin
```

### 3.3 The sampling law

```lean
-- NLAlib/Matrix/Norms/Frobenius.lean
/-- The **squared-row-norm distribution** $p_i = \|\mathbf{a}_i\|^2/\|\mathbf{A}\|_{\mathsf{F}}^2$
of the rows of $\mathbf{A}$: the weights of length-squared row sampling, for use with
`NLAlib.samplingMeasure` (randomized Kaczmarz) and `NLAlib.samplingSketch` (row sampling). Junk
value: all weights $0$ when $\mathbf{A} = \mathbf{0}$; otherwise they sum to one
(`NLAlib.sum_rowNormSqDistribution`). [StrohmerVershynin2009, Algorithm 1]. -/
noncomputable def rowNormSqDistribution (A : Matrix m n 𝕜) (i : m) : ℝ≥0 :=
  ‖WithLp.toLp 2 (A i)‖₊ ^ 2 / ‖frobNorm A‖₊ ^ 2

theorem coe_rowNormSqDistribution (A : Matrix m n 𝕜) (i : m) :
    (rowNormSqDistribution A i : ℝ) = ‖WithLp.toLp 2 (A i)‖ ^ 2 / frobNorm A ^ 2
theorem sum_rowNormSqDistribution {A : Matrix m n 𝕜} (hA : A ≠ 0) :
    ∑ i, rowNormSqDistribution A i = 1
```

`Sketching/Sampling/` has no inline twin of these weights (checked `RowSampling.lean`,
`MatrixMultiplication.lean`). General probabilities need no definition: any `p : m → ℝ≥0` gives
`samplingMeasure p`, and §5.3 states Kaczmarz for it. Uniform sampling after row normalisation is
the case of rows of equal norm, where `rowNormSqDistribution A` is constant and
`samplingMeasure_const_inv_card` identifies the law with `uniformOn Set.univ` (a two-line later
target, §6).

## 4. Probabilistic modelling

**The idiom (D2).** An i.i.d. sequence with law $\nu$ is `ξ : Ω → ℕ → β` with the single hypothesis
```lean
HasLaw ξ (Measure.infinitePi fun _ : ℕ => ν) μ
```
the ℕ-indexed analogue of the library's finite idiom `HasLaw X (Measure.pi ν) μ`
(`docs/PORT_PROBABILITY.md` D2), stated through Mathlib's product measure. For Kaczmarz,
`ξ = ι : Ω → ℕ → m` and `ν = samplingMeasure (rowNormSqDistribution A)`, which needs
`[MeasurableSpace m] [MeasurableSingletonClass m]` in the statement, as `hasLaw_samplingSketchMatrix`
does. For sketch-and-project, `ξ = S : Ω → ℕ → Matrix k m 𝕜` with any law `ν`, so Gaussian, sparse
and sampling sketches all enter the same way.

Why this and not the alternatives:
* *A finite prefix per statement*, `HasLaw (fun ω (j : Fin q) => ι ω j) (Measure.pi fun _ => ν) μ`:
  slightly more general (a user with exactly $q$ samples), but a $q$-dependent hypothesis in every
  theorem, a `Fin` coercion in every iterate, and an induction that must restrict the prefix at each
  step. The old repo's path laws were this, five times over.
* *`iIndepFun` plus marginals*: two hypotheses where one suffices; the bridge `hasLaw_infinitePi_iff`
  (§7) converts in one step, as `hasLaw_pi_iff` does for finite families.
* *A canonical space* (`∫ … ∂Measure.infinitePi …` directly): excluded by `PORT_PROBABILITY.md` D2.
* *Markov kernels / Ionescu-Tulcea* (`Kernel.traj`): the right tool for *adaptive* sampling (greedy
  Kaczmarz, randomly pivoted Cholesky), not needed for i.i.d. choices; see §6.

**Degenerate cases.** `Measure.infinitePi` of a family that is not a probability measure is $0$, and
`HasLaw ξ 0 μ` forces $\mu = 0$, so every left-hand side (an integral over $\mu$) is $0$. Whether a
statement survives without a probability hypothesis then depends on its right-hand side, and the
two files differ:
* **Sketch-and-project** statements take `[IsProbabilityMeasure ν]`. Without it they are false: for
  $\nu = 2\,\delta_{\mathbf{T}}$ the expected projector doubles, $\lambda = 2$ satisfies the Loewner
  hypothesis, and $(1 - \lambda)^q\|\mathbf{x}_\star - \mathbf{x}_0\|^2 < 0$ for odd $q$. The remark
  "$\lambda \le 1$" of §5.1 also uses $\nu(\mathrm{univ}) = 1$.
* **Kaczmarz** statements take no hypothesis on $\mathbf{A}$, because their law is fixed. If
  $\mathbf{A} \ne \mathbf{0}$ the weights sum to one and the law is a probability measure. If
  $\mathbf{A} = \mathbf{0}$ then $\mu = 0$, and every right-hand side is nonnegative through the
  junk values: `frobPseudoConditionNumber 0 = 0`, so the rate $1 - 1/0^2 = 1$; the horizon terms are
  `… / frobNorm 0 ^ 2 = 0`; and $\varepsilon\|\cdot\|^2 \ge 0$. The exact identity is $0 = 0$. The
  exception is the mean iterate (§5.3), whose right-hand side is a vector: it takes `A ≠ 0`.

**Conditioning on the past, without conditional expectation.** Every expectation step in this note
is one Fubini identity: if $F$ is a measurable function of the first $q$ coordinates, then
$F(\xi)$ is independent of $\xi_q$ and
$$\int f(F(\xi), \xi_q)\,d\mu = \int\!\!\int f(F(\xi), s)\,d\nu(s)\,d\mu\,.$$
It is a statement in Mathlib's vocabulary only, so it goes to `ForMathlib` (§7):

```lean
-- NLAlib/ForMathlib/Probability/Independence/Basic.lean (beside
-- `IndepFun.integral_comp_eq_integral_integral`)
/-- A measurable function of the coordinates in a finite set $s$ of an independent family is
independent of a coordinate outside $s$. Upstream candidate. -/
theorem iIndepFun.indepFun_comp_of_dependsOn {ι γ : Type*} {β : ι → Type*}
    [∀ i, MeasurableSpace (β i)] [MeasurableSpace γ] {X : (i : ι) → Ω → β i}
    (hX : iIndepFun X μ) (hXm : ∀ i, AEMeasurable (X i) μ) {s : Finset ι} {t : ι} (ht : t ∉ s)
    {F : ((i : ι) → β i) → γ} (hF : Measurable F) (hFs : DependsOn F s) :
    IndepFun (fun ω => F fun i => X i ω) (X t) μ

-- NLAlib/ForMathlib/Probability/Independence/InfinitePi.lean (new)
/-- **Conditioning on the past of an i.i.d. sequence** (Fubini). Upstream candidate. -/
theorem HasLaw.integral_comp_eq_integral_integral_of_dependsOn {β α E : Type*}
    [MeasurableSpace β] [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ν : Measure β} [IsProbabilityMeasure ν] {ξ : Ω → ℕ → β}
    (hξ : HasLaw ξ (Measure.infinitePi fun _ : ℕ => ν) μ) {q : ℕ} {F : (ℕ → β) → α}
    (hF : Measurable F) (hFq : DependsOn F (Set.Iio q))
    {f : α × β → E} (hf : Integrable f ((μ.map fun ω => F (ξ ω)).prod ν)) :
    ∫ ω, f (F (ξ ω), ξ ω q) ∂μ = ∫ ω, ∫ s, f (F (ξ ω), s) ∂ν ∂μ
```

The first lemma takes a `Finset` (the shape of `iIndepFun.indepFun_finset₀`); the second passes
`Finset.range q`, meeting `DependsOn F (Set.Iio q)` through `Finset.coe_range`.

No generic "drift lemma" for iterated random maps and no random-iterate definition: each file's
induction is ten lines once the Fubini step exists, and a generic version would need integrability
hypotheses that both consumers discharge differently (bounded in sketch-and-project, finitely valued
in Kaczmarz).

## 5. Headline statements

Common context for §5.1–5.2:
```lean
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
open scoped MatrixOrder                -- the Loewner order in `hlam`
open scoped Matrix.Norms.L2Operator    -- matrix-valued integrals, CONTRIBUTING §5.1
```

### 5.1 Sketch-and-project, consistent systems (`Solvers/SketchAndProject.lean`)

The expected projector is written out, `∫ T, rangeProjector (T * A)ᴴ ∂ν` (no definition), where
`rangeProjector (T * A)ᴴ = pinv (T * A) * (T * A)` is Gower–Richtárik's $\mathbf{Z}$ at
$\mathbf{B} = \mathbf{I}$ (`pinv_mul`). Every statement here integrates an `n × n` matrix, whose
normed structure under `Matrix.Norms.L2Operator` needs `[DecidableEq n]`; that is the minimal set
(checked by elaboration).

```lean
/-- The exact one-step identity in expectation:
$\mathbb{E}\|\mathbf{x}_\star - \mathbf{x}_{q+1}\|^2 = \mathbb{E}\|\mathbf{x}_\star - \mathbf{x}_q\|^2
- \mathbb{E}\,\operatorname{Re}\langle \mathbf{x}_\star - \mathbf{x}_q,
\mathbb{E}[\mathbf{Z}](\mathbf{x}_\star - \mathbf{x}_q)\rangle$.
[GowerRichtarik2015, proof of Theorem 4.6]. -/
theorem integral_norm_sub_sketchAndProjectIterate_succ_sq [DecidableEq n]
    {ν : Measure (Matrix k m 𝕜)} [IsProbabilityMeasure ν] {S : Ω → ℕ → Matrix k m 𝕜}
    (hS : HasLaw S (Measure.infinitePi fun _ : ℕ => ν) μ) {A : Matrix m n 𝕜} {b : m → 𝕜}
    {xs : n → 𝕜} (hxs : A *ᵥ xs = b) (x₀ : n → 𝕜) (q : ℕ) :
    ∫ ω, ‖WithLp.toLp 2 (xs - sketchAndProjectIterate A (S ω) b x₀ (q + 1))‖ ^ 2 ∂μ =
      ∫ ω, ‖WithLp.toLp 2 (xs - sketchAndProjectIterate A (S ω) b x₀ q)‖ ^ 2 ∂μ -
        ∫ ω, RCLike.re (quadForm (∫ T, rangeProjector (T * A)ᴴ ∂ν)
          (xs - sketchAndProjectIterate A (S ω) b x₀ q)) ∂μ

/-- **The mean error** contracts by the expected projector:
$\mathbf{x}_\star - \mathbb{E}[\mathbf{x}_q] = (\mathbf{I} - \mathbb{E}\mathbf{Z})^q(\mathbf{x}_\star - \mathbf{x}_0)$.
[GowerRichtarik2015, Theorem 4.4, (4.6)]. -/
theorem integral_sub_sketchAndProjectIterate [DecidableEq n]
    {ν : Measure (Matrix k m 𝕜)} [IsProbabilityMeasure ν] {S : Ω → ℕ → Matrix k m 𝕜}
    (hS : HasLaw S (Measure.infinitePi fun _ : ℕ => ν) μ) {A : Matrix m n 𝕜} {b : m → 𝕜}
    {xs : n → 𝕜} (hxs : A *ᵥ xs = b) (x₀ : n → 𝕜) (q : ℕ) :
    ∫ ω, (xs - sketchAndProjectIterate A (S ω) b x₀ q) ∂μ =
      (1 - ∫ T, rangeProjector (T * A)ᴴ ∂ν) ^ q *ᵥ (xs - x₀)

/-- **Sketch-and-project converges linearly in expectation.** For a consistent system
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$, a start with $\mathbf{x}_\star - \mathbf{x}_0$ in the row
space of $\mathbf{A}$, i.i.d. sketches with a probability law $\nu$, and
$\lambda\mathbf{P}_{\mathbf{A}^{\mathsf{H}}} \preceq \mathbb{E}_{\nu}\mathbf{Z}$ with
$\mathbf{Z} = (\mathbf{S}\mathbf{A})^{+}\mathbf{S}\mathbf{A}$,
$$\mathbb{E}\|\mathbf{x}_\star - \mathbf{x}_q\|^2 \le (1 - \lambda)^q\|\mathbf{x}_\star - \mathbf{x}_0\|^2\,.$$
[GowerRichtarik2015, Theorem 4.6]; there for $\mathbb{E}\mathbf{Z}$ positive definite (full column
rank) and $\lambda = \lambda_{\min}(\mathbb{E}\mathbf{Z})$, with a general metric; here any rank, any
law, $\mathbf{B} = \mathbf{I}$. Iteration-count form:
`NLAlib.integral_norm_sub_sketchAndProjectIterate_sq_le_mul_of_log_div_le`.
Result: sketch-and-project -/
theorem integral_norm_sub_sketchAndProjectIterate_sq_le [DecidableEq n]
    {ν : Measure (Matrix k m 𝕜)} [IsProbabilityMeasure ν] {S : Ω → ℕ → Matrix k m 𝕜}
    (hS : HasLaw S (Measure.infinitePi fun _ : ℕ => ν) μ) {A : Matrix m n 𝕜} {b : m → 𝕜}
    {xs x₀ : n → 𝕜} (hxs : A *ᵥ xs = b) (hx₀ : xs - x₀ ∈ LinearMap.range Aᴴ.mulVecLin)
    {lam : ℝ} (hlam : lam • rangeProjector Aᴴ ≤ ∫ T, rangeProjector (T * A)ᴴ ∂ν) (q : ℕ) :
    ∫ ω, ‖WithLp.toLp 2 (xs - sketchAndProjectIterate A (S ω) b x₀ q)‖ ^ 2 ∂μ ≤
      (1 - lam) ^ q * ‖WithLp.toLp 2 (xs - x₀)‖ ^ 2
```

The Loewner hypothesis on the row space is the useful form: full column rank gives
`rangeProjector Aᴴ = 1` and the familiar `lam • 1 ≤ ∫ …` (§5.3 row "spectral bound"); block
Kaczmarz with a paving gives it from $\mathbf{P}_{\mathbf{A}_\tau^{\mathsf{H}}} \succeq
\mathbf{A}_\tau^{\mathsf{H}}\mathbf{A}_\tau/\beta$; Kaczmarz gives it from §5.3. Since $\nu$ is a
probability measure and each $\mathbf{Z} \preceq \mathbf{P}_{\mathbf{A}^{\mathsf{H}}}$
(`rangeProjector_mono`), $\lambda \le 1$ whenever $\mathbf{A} \ne \mathbf{0}$, so no side condition.

Iteration count and asymptotic form, both with `[IsProbabilityMeasure ν]`:

```lean
theorem integral_norm_sub_sketchAndProjectIterate_sq_le_mul_of_log_div_le [DecidableEq n]
    {ν : Measure (Matrix k m 𝕜)} [IsProbabilityMeasure ν] {S : Ω → ℕ → Matrix k m 𝕜}
    (hS : HasLaw S (Measure.infinitePi fun _ : ℕ => ν) μ) {A : Matrix m n 𝕜} {b : m → 𝕜}
    {xs x₀ : n → 𝕜} (hxs : A *ᵥ xs = b) (hx₀ : xs - x₀ ∈ LinearMap.range Aᴴ.mulVecLin)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam : lam • rangeProjector Aᴴ ≤ ∫ T, rangeProjector (T * A)ᴴ ∂ν)
    {ε : ℝ} (hε : 0 < ε) {q : ℕ} (hq : Real.log (1 / ε) / lam ≤ q) :
    ∫ ω, ‖WithLp.toLp 2 (xs - sketchAndProjectIterate A (S ω) b x₀ q)‖ ^ 2 ∂μ ≤
      ε * ‖WithLp.toLp 2 (xs - x₀)‖ ^ 2

/-- **$O(\lambda^{-1}\log(1/\varepsilon))$ iterations suffice for sketch-and-project**: there are
absolute constants $C, \varepsilon_0 > 0$ such that for a consistent system
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$, a start with $\mathbf{x}_\star - \mathbf{x}_0$ in the row
space of $\mathbf{A}$, i.i.d. sketches with a probability law $\nu$ satisfying
$\lambda\mathbf{P}_{\mathbf{A}^{\mathsf{H}}} \preceq \mathbb{E}_{\nu}[(\mathbf{S}\mathbf{A})^{+}\mathbf{S}\mathbf{A}]$
with $\lambda > 0$, $0 < \varepsilon \le \varepsilon_0$ and $q \ge C\lambda^{-1}\log(1/\varepsilon)$,
$\mathbb{E}\|\mathbf{x}_\star - \mathbf{x}_q\|^2 \le \varepsilon\|\mathbf{x}_\star - \mathbf{x}_0\|^2$.
The proof takes $C = 1$ and $\varepsilon_0 = 1$. [GowerRichtarik2015, Theorem 4.6].
Asymptotic: NLAlib.integral_norm_sub_sketchAndProjectIterate_sq_le_mul_of_log_div_le
Result: sketch-and-project -/
theorem exists_forall_integral_norm_sub_sketchAndProjectIterate_sq_le_mul :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω 𝕜 k m n : Type} [MeasurableSpace Ω] [RCLike 𝕜] [Fintype k]
      [Fintype m] [Fintype n] [DecidableEq n] (μ : Measure Ω) (ν : Measure (Matrix k m 𝕜))
      [IsProbabilityMeasure ν] (S : Ω → ℕ → Matrix k m 𝕜) (A : Matrix m n 𝕜) (b : m → 𝕜)
      (xs x₀ : n → 𝕜) (lam : ℝ) (q : ℕ) (ε : ℝ),
      HasLaw S (Measure.infinitePi fun _ : ℕ => ν) μ → A *ᵥ xs = b →
      xs - x₀ ∈ LinearMap.range Aᴴ.mulVecLin → 0 < lam →
      lam • rangeProjector Aᴴ ≤ ∫ T, rangeProjector (T * A)ᴴ ∂ν → 0 < ε → ε ≤ ε₀ →
      C * (Real.log (1 / ε) / lam) ≤ q →
      ∫ ω, ‖WithLp.toLp 2 (xs - sketchAndProjectIterate A (S ω) b x₀ q)‖ ^ 2 ∂μ ≤
        ε * ‖WithLp.toLp 2 (xs - x₀)‖ ^ 2
```

### 5.2 Randomized Kaczmarz (`Solvers/Kaczmarz.lean`)

The rate is written with the Frobenius condition number of D3,
`frobPseudoConditionNumber A := frobNorm A * specNorm (pinv A)` (Strohmer–Vershynin's $\kappa(\mathbf{A})$,
Zouzias–Freris's $\kappa_{\mathsf{F}}$; docstrings write it out,
$\|\mathbf{A}\|_{\mathsf{F}}\|\mathbf{A}^{+}\|_2$, never $\kappa$, per CONTRIBUTING §6). It needs no
rank hypothesis: $\|\mathbf{A}^{+}\|_2^{-1}$ is the smallest *nonzero* singular value
(`specNorm_pinv`). For $\mathbf{A} \ne \mathbf{0}$, `one_le_frobPseudoConditionNumber` gives
$\rho = 1 - 1/\|\mathbf{A}\|_{\mathsf{F}}^2\|\mathbf{A}^{+}\|_2^2 \in [0, 1)$.

```lean
variable [DecidableEq m] [MeasurableSpace m] [MeasurableSingletonClass m]
  {A : Matrix m n 𝕜} {b : m → 𝕜} {ι : Ω → ℕ → m} {x₀ : n → 𝕜}
```
(no `[DecidableEq n]`: no statement in this subsection has a projector on `n` or a `1 - …`; checked
by elaboration.)

```lean
/-- **The one-step bound in expectation**, for any right-hand side and reference point
$\mathbf{x}_\star$, with $\mathbf{r} = \mathbf{b} - \mathbf{A}\mathbf{x}_\star$:
$$\mathbb{E}\|\mathbf{x}_\star - \mathbf{x}_{q+1}\|^2 \le \mathbb{E}\|\mathbf{x}_\star - \mathbf{x}_q\|^2
- \frac{\mathbb{E}\|\mathbf{A}(\mathbf{x}_\star - \mathbf{x}_q)\|^2}{\|\mathbf{A}\|_{\mathsf{F}}^2}
+ \frac{\|\mathbf{r}\|^2}{\|\mathbf{A}\|_{\mathsf{F}}^2}\,.$$
The gap is the residual on the zero rows, which are never chosen; with no zero row it is the identity
`NLAlib.integral_norm_sub_kaczmarzIterate_succ_sq`. This is the form the bounds use.
[StrohmerVershynin2009, proof of Theorem 2]; [ZouziasFreris2013, Lemma 6, (5)], there after the
singular-value bound. -/
theorem integral_norm_sub_kaczmarzIterate_succ_sq_le
    (hι : HasLaw ι (Measure.infinitePi fun _ : ℕ => samplingMeasure (rowNormSqDistribution A)) μ)
    (xs : n → 𝕜) (q : ℕ) :
    ∫ ω, ‖WithLp.toLp 2 (xs - kaczmarzIterate A (ι ω) b x₀ (q + 1))‖ ^ 2 ∂μ ≤
      ∫ ω, ‖WithLp.toLp 2 (xs - kaczmarzIterate A (ι ω) b x₀ q)‖ ^ 2 ∂μ -
        (∫ ω, ‖WithLp.toLp 2 (A *ᵥ (xs - kaczmarzIterate A (ι ω) b x₀ q))‖ ^ 2 ∂μ) /
          frobNorm A ^ 2 +
        ‖WithLp.toLp 2 (b - A *ᵥ xs)‖ ^ 2 / frobNorm A ^ 2

/-- **The one-step identity in expectation**, when no row of $\mathbf{A}$ is zero: equality in
`NLAlib.integral_norm_sub_kaczmarzIterate_succ_sq_le`. At $q = 0$ from a deterministic start it is
the conditional identity of the proofs. Without `hA` it fails: for
$\mathbf{A} = \begin{bmatrix} 1 \\ 0 \end{bmatrix}$, $\mathbf{b} = (0, 1)$, $\mathbf{x}_0 = \mathbf{x}_\star = \mathbf{0}$
the left side is $0$ and the right side $1$. [StrohmerVershynin2009, proof of Theorem 2]. -/
theorem integral_norm_sub_kaczmarzIterate_succ_sq (hA : ∀ i, A i ≠ 0)
    (hι : HasLaw ι (Measure.infinitePi fun _ : ℕ => samplingMeasure (rowNormSqDistribution A)) μ)
    (xs : n → 𝕜) (q : ℕ) :
    ∫ ω, ‖WithLp.toLp 2 (xs - kaczmarzIterate A (ι ω) b x₀ (q + 1))‖ ^ 2 ∂μ =
      ∫ ω, ‖WithLp.toLp 2 (xs - kaczmarzIterate A (ι ω) b x₀ q)‖ ^ 2 ∂μ -
        (∫ ω, ‖WithLp.toLp 2 (A *ᵥ (xs - kaczmarzIterate A (ι ω) b x₀ q))‖ ^ 2 ∂μ) /
          frobNorm A ^ 2 +
        ‖WithLp.toLp 2 (b - A *ᵥ xs)‖ ^ 2 / frobNorm A ^ 2

/-- **Randomized Kaczmarz, any right-hand side.** For any $\mathbf{x}_\star$ with
$\mathbf{x}_\star - \mathbf{x}_0$ in the row space of $\mathbf{A}$ and rows drawn i.i.d. with
probability $\|\mathbf{a}_i\|^2/\|\mathbf{A}\|_{\mathsf{F}}^2$, with
$\rho = 1 - \|\mathbf{A}\|_{\mathsf{F}}^{-2}\|\mathbf{A}^{+}\|_2^{-2}$,
$$\mathbb{E}\|\mathbf{x}_\star - \mathbf{x}_q\|^2 \le \rho^q\|\mathbf{x}_\star - \mathbf{x}_0\|^2
+ (1 - \rho^q)\,\|\mathbf{A}^{+}\|_2^2\,\|\mathbf{b} - \mathbf{A}\mathbf{x}_\star\|^2\,.$$
No rank assumption. **The reference point.** For $\mathbf{x}_0 = \mathbf{0}$ take
$\mathbf{x}_\star = \mathbf{A}^{+}\mathbf{b}$; in general take the least-squares solution nearest
$\mathbf{x}_0$, $\mathbf{x}_0 + \mathbf{A}^{+}(\mathbf{b} - \mathbf{A}\mathbf{x}_0)$, which minimises the
horizon (`NLAlib.integral_norm_add_pinv_mulVec_sub_kaczmarzIterate_sq_le`). The choice
$\mathbf{x}_\star = \mathbf{A}^{+}\mathbf{b}$ with a generic $\mathbf{x}_0$ violates the row-space
hypothesis, and the bound then fails. [ZouziasFreris2013, Theorem 7]; the same horizon
$\|\mathbf{w}\|^2/\sigma_{\min}^2$, here with the factor $1 - \rho^q$. [Needell2010, Theorem 2.1];
there for full column rank, in the unsquared norm and with the larger horizon
$R\gamma^2 \ge \|\mathbf{A}^{+}\|_2^2\|\mathbf{r}\|^2$, which this implies by Jensen's inequality. Port
of `NLAlib.Kaczmarz.expErr_le_add_of_sub_mem_range` and five variants. Iteration-count form:
`NLAlib.integral_norm_sub_kaczmarzIterate_sq_le_mul_add_of_mul_log_le`.
Result: kaczmarz-inconsistent -/
theorem integral_norm_sub_kaczmarzIterate_sq_le_add
    (hι : HasLaw ι (Measure.infinitePi fun _ : ℕ => samplingMeasure (rowNormSqDistribution A)) μ)
    {xs : n → 𝕜} (hx₀ : xs - x₀ ∈ LinearMap.range Aᴴ.mulVecLin) (q : ℕ) :
    ∫ ω, ‖WithLp.toLp 2 (xs - kaczmarzIterate A (ι ω) b x₀ q)‖ ^ 2 ∂μ ≤
      (1 - 1 / frobPseudoConditionNumber A ^ 2) ^ q * ‖WithLp.toLp 2 (xs - x₀)‖ ^ 2 +
        (1 - (1 - 1 / frobPseudoConditionNumber A ^ 2) ^ q) * specNorm (pinv A) ^ 2 *
          ‖WithLp.toLp 2 (b - A *ᵥ xs)‖ ^ 2

/-- **From any start, randomized Kaczmarz converges to the least-squares solution nearest the
start, up to the horizon**, for any right-hand side and with no hypothesis: with
$\mathbf{x}_\star = \mathbf{x}_0 + \mathbf{A}^{+}(\mathbf{b} - \mathbf{A}\mathbf{x}_0)$ and $\rho$ as
above,
$$\mathbb{E}\|\mathbf{x}_\star - \mathbf{x}_q\|^2 \le \rho^q\|\mathbf{A}^{+}(\mathbf{b} - \mathbf{A}\mathbf{x}_0)\|^2
+ (1 - \rho^q)\,\|\mathbf{A}^{+}\|_2^2\,\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{b}\|^2\,.$$
From $\mathbf{x}_0 = \mathbf{0}$ the limit is $\mathbf{A}^{+}\mathbf{b}$. [ZouziasFreris2013, Theorem 7],
there from $\mathbf{x}_0 = \mathbf{0}$; [LeventhalLewis2010, Theorem 4.7], there for consistent systems.
Port of `NLAlib.Kaczmarz.expErr_zero_le_moorePenroseInverse`.
Result: kaczmarz-rank-deficient -/
theorem integral_norm_add_pinv_mulVec_sub_kaczmarzIterate_sq_le
    (hι : HasLaw ι (Measure.infinitePi fun _ : ℕ => samplingMeasure (rowNormSqDistribution A)) μ)
    (x₀ : n → 𝕜) (q : ℕ) :
    ∫ ω, ‖WithLp.toLp 2 (x₀ + pinv A *ᵥ (b - A *ᵥ x₀) - kaczmarzIterate A (ι ω) b x₀ q)‖ ^ 2 ∂μ ≤
      (1 - 1 / frobPseudoConditionNumber A ^ 2) ^ q * ‖WithLp.toLp 2 (pinv A *ᵥ (b - A *ᵥ x₀))‖ ^ 2 +
        (1 - (1 - 1 / frobPseudoConditionNumber A ^ 2) ^ q) * specNorm (pinv A) ^ 2 *
          ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ b)‖ ^ 2

/-- Its consistent case, $\mathbf{b} \in \operatorname{range}\mathbf{A}$, where the horizon
vanishes: convergence to the projection of $\mathbf{x}_0$ onto the solution set.
[LeventhalLewis2010, Theorem 4.7]; [ZouziasFreris2013, Theorem 4]. -/
theorem integral_norm_add_pinv_mulVec_sub_kaczmarzIterate_sq_le_of_mem_range
    (hι : HasLaw ι (Measure.infinitePi fun _ : ℕ => samplingMeasure (rowNormSqDistribution A)) μ)
    (hb : b ∈ LinearMap.range A.mulVecLin) (x₀ : n → 𝕜) (q : ℕ) :
    ∫ ω, ‖WithLp.toLp 2 (x₀ + pinv A *ᵥ (b - A *ᵥ x₀) - kaczmarzIterate A (ι ω) b x₀ q)‖ ^ 2 ∂μ ≤
      (1 - 1 / frobPseudoConditionNumber A ^ 2) ^ q * ‖WithLp.toLp 2 (pinv A *ᵥ (b - A *ᵥ x₀))‖ ^ 2

/-- **Randomized Kaczmarz converges linearly in expectation** (Strohmer–Vershynin), any rank: for
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$, $\mathbf{x}_\star - \mathbf{x}_0$ in the row space of
$\mathbf{A}$ and rows drawn i.i.d. with probability $\|\mathbf{a}_i\|^2/\|\mathbf{A}\|_{\mathsf{F}}^2$,
$$\mathbb{E}\|\mathbf{x}_\star - \mathbf{x}_q\|^2 \le
\Bigl(1 - \frac{1}{\|\mathbf{A}\|_{\mathsf{F}}^2\|\mathbf{A}^{+}\|_2^2}\Bigr)^q
\|\mathbf{x}_\star - \mathbf{x}_0\|^2\,,$$
the rate in $[0, 1)$ for $\mathbf{A} \ne \mathbf{0}$. [StrohmerVershynin2009, Theorem 2]; there for
full column rank, where the row-space hypothesis is empty. [ZouziasFreris2013, Theorem 4]. Port of
`NLAlib.integral_sqErr_kaczmarz_le_frobPseudoConditionNumber`. Iteration-count form:
`NLAlib.integral_norm_sub_kaczmarzIterate_sq_le_mul_of_mul_log_le`.
Result: randomized-kaczmarz -/
theorem integral_norm_sub_kaczmarzIterate_sq_le
    (hι : HasLaw ι (Measure.infinitePi fun _ : ℕ => samplingMeasure (rowNormSqDistribution A)) μ)
    {xs : n → 𝕜} (hxs : A *ᵥ xs = b) (hx₀ : xs - x₀ ∈ LinearMap.range Aᴴ.mulVecLin) (q : ℕ) :
    ∫ ω, ‖WithLp.toLp 2 (xs - kaczmarzIterate A (ι ω) b x₀ q)‖ ^ 2 ∂μ ≤
      (1 - 1 / frobPseudoConditionNumber A ^ 2) ^ q * ‖WithLp.toLp 2 (xs - x₀)‖ ^ 2
```

**Iteration counts** (CONTRIBUTING §5.2 rule 3). From
$(1 - \kappa_{\mathsf{F}}^{-2})^q \le e^{-q/\kappa_{\mathsf{F}}^2}$:
```lean
theorem integral_norm_sub_kaczmarzIterate_sq_le_mul_of_mul_log_le
    (hι : HasLaw ι (Measure.infinitePi fun _ : ℕ => samplingMeasure (rowNormSqDistribution A)) μ)
    {xs : n → 𝕜} (hxs : A *ᵥ xs = b) (hx₀ : xs - x₀ ∈ LinearMap.range Aᴴ.mulVecLin)
    {ε : ℝ} (hε : 0 < ε) {q : ℕ} (hq : frobPseudoConditionNumber A ^ 2 * Real.log (1 / ε) ≤ q) :
    ∫ ω, ‖WithLp.toLp 2 (xs - kaczmarzIterate A (ι ω) b x₀ q)‖ ^ 2 ∂μ ≤
      ε * ‖WithLp.toLp 2 (xs - x₀)‖ ^ 2

/-- **$O(\|\mathbf{A}\|_{\mathsf{F}}^2\|\mathbf{A}^{+}\|_2^2\log(1/\varepsilon))$ iterations suffice
for randomized Kaczmarz**: there are absolute constants $C, \varepsilon_0 > 0$ such that for
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$, $\mathbf{x}_\star - \mathbf{x}_0$ in the row space of
$\mathbf{A}$, rows drawn i.i.d. with probability $\|\mathbf{a}_i\|^2/\|\mathbf{A}\|_{\mathsf{F}}^2$,
$0 < \varepsilon \le \varepsilon_0$ and
$q \ge C\|\mathbf{A}\|_{\mathsf{F}}^2\|\mathbf{A}^{+}\|_2^2\log(1/\varepsilon)$,
$\mathbb{E}\|\mathbf{x}_\star - \mathbf{x}_q\|^2 \le \varepsilon\|\mathbf{x}_\star - \mathbf{x}_0\|^2$.
The proof takes $C = 1$, $\varepsilon_0 = 1$. [StrohmerVershynin2009, §2.1, (11)], which counts
$2\kappa^2\log(1/\varepsilon)$ for the unsquared error.
Asymptotic: NLAlib.integral_norm_sub_kaczmarzIterate_sq_le_mul_of_mul_log_le
Result: randomized-kaczmarz -/
theorem exists_forall_integral_norm_sub_kaczmarzIterate_sq_le_mul :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω 𝕜 m n : Type} [MeasurableSpace Ω] [RCLike 𝕜] [Fintype m]
      [Fintype n] [DecidableEq m] [MeasurableSpace m] [MeasurableSingletonClass m]
      (μ : Measure Ω) (A : Matrix m n 𝕜) (b : m → 𝕜) (ι : Ω → ℕ → m) (xs x₀ : n → 𝕜) (q : ℕ) (ε : ℝ),
      HasLaw ι (Measure.infinitePi fun _ : ℕ => samplingMeasure (rowNormSqDistribution A)) μ →
      A *ᵥ xs = b → xs - x₀ ∈ LinearMap.range Aᴴ.mulVecLin → 0 < ε → ε ≤ ε₀ →
      C * (frobPseudoConditionNumber A ^ 2 * Real.log (1 / ε)) ≤ q →
      ∫ ω, ‖WithLp.toLp 2 (xs - kaczmarzIterate A (ι ω) b x₀ q)‖ ^ 2 ∂μ ≤
        ε * ‖WithLp.toLp 2 (xs - x₀)‖ ^ 2
```

The same pair for the inconsistent bound, conclusion
`≤ ε * ‖WithLp.toLp 2 (xs - x₀)‖ ^ 2 + specNorm (pinv A) ^ 2 * ‖WithLp.toLp 2 (b - A *ᵥ xs)‖ ^ 2`
and no `hxs`: `integral_norm_sub_kaczmarzIterate_sq_le_mul_add_of_mul_log_le` and
`exists_forall_integral_norm_sub_kaczmarzIterate_sq_le_mul_add`, whose docstrings follow the pattern
above (hypotheses and conclusion in full, `Asymptotic:` line before `Result: kaczmarz-inconsistent`).

### 5.3 Kaczmarz as a sketch-and-project instance; the mean iterate

```lean
/-- The expected projector of a random row: $\sum_i p_i \mathbf{P}_{\overline{\mathbf{a}_i}}$. -/
theorem integral_rangeProjector_conjTranspose_selectionMatrix_mul [DecidableEq n]
    (A : Matrix m n 𝕜) (p : m → ℝ≥0) :
    ∫ i, rangeProjector ((selectionMatrix fun _ : Unit => i)ᴴ * A)ᴴ ∂samplingMeasure p =
      ∑ i, (p i : ℝ) • rangeProjector (Matrix.replicateCol Unit (star (A i)))
/-- At squared-row-norm weights it is $\mathbf{A}^{\mathsf{H}}\mathbf{A}/\|\mathbf{A}\|_{\mathsf{F}}^2$
[StrohmerVershynin2009, (7)–(9)]. -/
theorem integral_rangeProjector_conjTranspose_selectionMatrix_mul_rowNormSqDistribution
    [DecidableEq n] (A : Matrix m n 𝕜) :
    ∫ i, rangeProjector ((selectionMatrix fun _ : Unit => i)ᴴ * A)ᴴ
        ∂samplingMeasure (rowNormSqDistribution A) = (frobNorm A ^ 2)⁻¹ • (Aᴴ * A)

/-- **Randomized Kaczmarz with any row probabilities**, consistent systems: rows drawn i.i.d. with
probabilities $p_i$ summing to one, and
$\lambda\mathbf{P}_{\mathbf{A}^{\mathsf{H}}} \preceq \sum_i p_i \mathbf{P}_{\overline{\mathbf{a}_i}}$, give
$\mathbb{E}\|\mathbf{x}_\star - \mathbf{x}_q\|^2 \le (1 - \lambda)^q\|\mathbf{x}_\star - \mathbf{x}_0\|^2$.
Uniform sampling is $p_i = 1/\lvert m \rvert$. From
`NLAlib.integral_norm_sub_sketchAndProjectIterate_sq_le` and the bridge above.
[GowerRichtarik2015, §3.3]. -/
theorem integral_norm_sub_kaczmarzIterate_sq_le_of_hasLaw_samplingMeasure [DecidableEq n]
    {p : m → ℝ≥0} (hp : ∑ i, p i = 1)
    (hι : HasLaw ι (Measure.infinitePi fun _ : ℕ => samplingMeasure p) μ)
    {xs : n → 𝕜} (hxs : A *ᵥ xs = b) (hx₀ : xs - x₀ ∈ LinearMap.range Aᴴ.mulVecLin) {lam : ℝ}
    (hlam : lam • rangeProjector Aᴴ ≤
      ∑ i, (p i : ℝ) • rangeProjector (Matrix.replicateCol Unit (star (A i)))) (q : ℕ) :
    ∫ ω, ‖WithLp.toLp 2 (xs - kaczmarzIterate A (ι ω) b x₀ q)‖ ^ 2 ∂μ ≤
      (1 - lam) ^ q * ‖WithLp.toLp 2 (xs - x₀)‖ ^ 2
```

(`[DecidableEq n]` here for the `n × n` matrix integral and the Loewner order on `Matrix n n 𝕜`
through `MatrixOrder`; the version in the scratch file elaborated with it.)

**The mean iterate is a Richardson (Landweber) iterate**, for any $\mathbf{b}$:
$\mathbb{E}[\mathbf{x}_{q+1}] = \mathbb{E}[\mathbf{x}_q] + \|\mathbf{A}\|_{\mathsf{F}}^{-2}
\mathbf{A}^{\mathsf{H}}(\mathbf{b} - \mathbf{A}\mathbb{E}[\mathbf{x}_q])$, by linearity and the §5.3
bridge (zero rows contribute $\mathbf{0}$ on both sides). It is stated with the sibling note's
`richardsonIterate`, whose signature is pending with the maintainer (sibling D3: square
`A M : Matrix n n 𝕜`, or rectangular `A : Matrix m n 𝕜`, `M : Matrix n m 𝕜`, `b : m → 𝕜`). The
normal-equations form is valid under **either** signature, since it is the square case of the
rectangular one; the Landweber form exists only under the rectangular one:

```lean
/-- **The mean Kaczmarz iterate is Richardson's iteration on the normal equations** with step
$\|\mathbf{A}\|_{\mathsf{F}}^{-2}$, for any right-hand side.
The averaged form of the observation that randomized Kaczmarz is stochastic gradient descent on
the least-squares objective [MaNeedellRamdas2015, §2.1]. -/
theorem integral_kaczmarzIterate [DecidableEq n] (hA : A ≠ 0)
    (hι : HasLaw ι (Measure.infinitePi fun _ : ℕ => samplingMeasure (rowNormSqDistribution A)) μ)
    (x₀ : n → 𝕜) (q : ℕ) :
    ∫ ω, kaczmarzIterate A (ι ω) b x₀ q ∂μ =
      richardsonIterate (Aᴴ * A) ((frobNorm A ^ 2)⁻¹ • (1 : Matrix n n 𝕜)) (Aᴴ *ᵥ b) x₀ q

-- only if the rectangular signature is adopted; equal to the above by the sibling's
-- `richardsonIterate_mul_conjTranspose`, `smul_mul`, `Matrix.one_mul`; needs no `[DecidableEq n]`
theorem integral_kaczmarzIterate_eq_richardsonIterate_conjTranspose (hA : A ≠ 0)
    (hι : HasLaw ι (Measure.infinitePi fun _ : ℕ => samplingMeasure (rowNormSqDistribution A)) μ)
    (x₀ : n → 𝕜) (q : ℕ) :
    ∫ ω, kaczmarzIterate A (ι ω) b x₀ q ∂μ =
      richardsonIterate A ((frobNorm A ^ 2)⁻¹ • Aᴴ) b x₀ q
```

If the rectangular signature is adopted, the Landweber form is the primary statement (it avoids
forming $\mathbf{A}^{\mathsf{H}}\mathbf{A}$ and needs no `[DecidableEq n]`) and the normal-equations
form its one-line corollary; under the square signature only the first exists. Both elaborated
against a stub with the rectangular signature. `hA` is needed: for $\mathbf{A} = \mathbf{0}$,
$\mu = 0$ and the left side is $\mathbf{0}$, the right side $\mathbf{x}_0$. The consistent case
gives, with the sibling's `sub_richardsonIterate_eq`,
$\mathbf{x}_\star - \mathbb{E}[\mathbf{x}_q] = (\mathbf{I} - \mathbf{A}^{\mathsf{H}}\mathbf{A}/\|\mathbf{A}\|_{\mathsf{F}}^2)^q(\mathbf{x}_\star - \mathbf{x}_0)$,
which §5.1's `integral_sub_sketchAndProjectIterate` also gives through the bridge. The mean
identity lands after the sibling's `Krylov/LinearSystems/Richardson.lean`; if that slips, it waits,
and nothing else depends on it.

The headline Kaczmarz bounds do not go through the sketch-and-project bridge: §5.2's direct proof is
shorter and covers inconsistent systems, which sketch-and-project with a general law does not (its
residual term need not be integrable).

## 6. In this round, and deferred

**In**: §§3–5, the lower-layer additions of §7.

**Deferred**, each with its reason ("defer very complex material"; none blocks the headlines):
* **Randomized extended Kaczmarz** [ZouziasFreris2013, Algorithm 3, Theorem 8]. Moderate once this
  round lands: its column half (Theorem 2) is the consistent Kaczmarz theorem applied to
  $\mathbf{A}^{\mathsf{H}}\mathbf{z} = \mathbf{0}$, and its row half is the §5.2 bound with a
  moving right-hand side. It needs two coupled streams (an i.i.d. sequence of pairs with law
  $\nu_{\mathrm{row}} \otimes \nu_{\mathrm{col}}$, which D2 covers) and a statement-shape decision of its
  own (the $\lfloor T/2\rfloor$ split of Theorem 8 against a $q\rho^q$ form). Recommended as the next
  stage.
* **Block Kaczmarz with a row paving** [NeedellTropp2014, Theorem 1.2]. The consistent half is a
  corollary of §5.1 given a paving; a paving predicate `IsRowPaving A T α β` is a new interface (§5.4
  of CONTRIBUTING), and the existence of good pavings (random pavings by matrix Chernoff) is the hard
  part. Deferred with REK; the general theorem already accepts any block law.
* **General metric $\mathbf{B}$** (Gower–Richtárik's $\|\cdot\|_{\mathbf{B}}$, randomized Newton and
  coordinate descent): needs a weighted-norm spelling (`quadForm B`) through every statement.
* **Almost-sure convergence** (summable $\mathbb{E}\|\mathbf{e}_q\|^2$ and Borel–Cantelli) and **tails**
  by Markov: easy corollaries without a consumer yet.
* **Adaptive row selection** (greedy, maximal-residual, Motzkin; also randomly pivoted Cholesky,
  `PORT_KRYLOV.md` question 2): needs adapted, non-i.i.d. sequences, that is Markov kernels
  (`Kernel.traj`). The K9 gate is therefore only half opened by D2: i.i.d. yes, adaptive no.
* **Strohmer–Vershynin's lower bound** (Theorem 3), relaxation parameters, and the uniform-weights
  identification for equal row norms: small later targets.
* **Explorer Rates rows**: not this round (maintainer, 2026-10-19).

## 7. Files, placement and imports

**Placement of the topic.** Randomized Kaczmarz and sketch-and-project solve linear systems
$\mathbf{A}\mathbf{x} = \mathbf{b}$ by row action; on an inconsistent system Kaczmarz does not converge
to the least-squares solution (it stops at a horizon, §5.2). Regression's topic is "sketched least
squares and preconditioning" (CONTRIBUTING §2). A reader looking for Kaczmarz looks under solvers, and
`PORT_KRYLOV.md` D12 (approved 2026-10-17) put "sketched GMRES and Rayleigh–Ritz, Nyström PCG, Kaczmarz,
sketch-and-project" in `Solvers/` (layer 5) and sketch-and-precondition in `Regression/`. The sibling
note follows D12 for its part; this note follows it for ours, so the two are consistent with the
approved table. Recommendation: `NLAlib/Solvers/`, flat for now (later Solvers notes may add
subdirectories). Both files import only Matrix and Probability (layer ≤ 1, plus Krylov for the mean
identity), so layer 5 is a placement by topic, not by dependency, as CONTRIBUTING §8 item 5 asks.
`Regression/Kaczmarz.lean` would also compile; if the maintainer prefers to keep the request's two
topics together, that is a two-file move (D4, reversible). The design note keeps the requested file
name.

| File | New/grows | Content, in order | Lines | Imports |
|---|---|---|---|---|
| `ForMathlib/Probability/Independence/Basic.lean` | grows | `iIndepFun.indepFun_comp_of_dependsOn` | +40 | `Mathlib.Logic.Function.DependsOn` |
| `ForMathlib/Probability/Independence/InfinitePi.lean` | new | `HasLaw.integral_comp_eq_integral_integral_of_dependsOn` | ~80 | the above, `Mathlib.Probability.Independence.InfinitePi` |
| `Probability/Law.lean` | grows (171) | `hasLaw_infinitePi_iff` | +25 | `Mathlib.Probability.Independence.InfinitePi` |
| `Matrix/Pseudoinverse/Pinv.lean` | grows | `pinv_replicateRow` | +20 | — |
| `Matrix/Pseudoinverse/ConditionNumber.lean` | grows | `frobPseudoConditionNumber` and API (D3) | +70 | `Matrix.Norms.Frobenius` |
| `Matrix/Norms/Frobenius.lean` | grows (~460) | `rowNormSqDistribution`, `coe_…`, `sum_…` | +30 | — |
| `Solvers/SketchAndProject.lean` | new | §3.1 definitions, §3.2, §5.1 | ~450 | Pseudoinverse, Projector, Selection, MatrixIntegral, Measurability.Matrix, the ForMathlib file |
| `Solvers/Kaczmarz.lean` | new | §3.1 `kaczmarzIterate`, realisation, §5.2, §5.3 | ~550 | SketchAndProject, Sampling, ConditionNumber, `Krylov.LinearSystems.Richardson` (sibling) for the mean identity |

**Placement of every addition outside the new Solvers files:**
* `iIndepFun.indepFun_comp_of_dependsOn` → `ForMathlib/Probability/Independence/Basic.lean`: Mathlib
  vocabulary only, would join `Mathlib/Probability/Independence/Basic.lean` beside
  `iIndepFun.indepFun_finset`.
* `HasLaw.integral_comp_eq_integral_integral_of_dependsOn` → new
  `ForMathlib/Probability/Independence/InfinitePi.lean`, named after the Mathlib file it would join.
  `PORT_KRYLOV.md` D12 said "`Probability/`"; ForMathlib is the stricter reading of CONTRIBUTING §2
  for a statement without NLAlib vocabulary.
* `hasLaw_infinitePi_iff` → `Probability/Law.lean`, beside its finite twin `hasLaw_pi_iff` (which
  sits there, not in ForMathlib, by the same file's precedent). Like `hasLaw_pi_iff` it takes
  `[IsProbabilityMeasure μ]` and `[∀ i, IsProbabilityMeasure (ν i)]`.
* `pinv_replicateRow` (the pseudoinverse of a one-row matrix,
  $(\mathbf{a}^{\mathsf{T}})^{+} = \overline{\mathbf{a}}/\|\mathbf{a}\|^2$, and $\mathbf{0}$ for
  $\mathbf{a} = \mathbf{0}$) → `Pinv.lean`: a pseudoinverse fact.
* `frobPseudoConditionNumber` → `ConditionNumber.lean`, beside `pseudoConditionNumber`.
* `rowNormSqDistribution` → `Frobenius.lean`, beside `frobNorm_sq_eq_sum_row`, which is its
  normalisation. Row norms are a Frobenius quantity; `leverageScoreDistribution` lives in
  `Matrix/Subspaces/` because leverage is a subspace quantity (the review's reading, adopted).
* `Matrix.integral_mulVec`, if the mean-error proof needs it (it does not exist; checked) →
  `Probability/MatrixIntegral.lean`, a matrix-integral fact; recorded as a placement amendment when
  it happens.
* Measurability and `DependsOn` of the iterate → `Solvers/SketchAndProject.lean`, about the iterate.
  (Krylov's measurability went to `Probability/Measurability/Krylov.lean` only because Krylov is
  layer 1 and imports no probability; Solvers is layer 5.)

No `Mathlib-deviations.md` entry: every Mathlib object (`Measure.infinitePi`, `HasLaw`, `DependsOn`,
`iIndepFun`) is used as is.

**§5.3 vocabulary rows** (added with the PRs that introduce them):

| Concept | Spelling | Mathlib bridge |
|---|---|---|
| i.i.d. sequence | `HasLaw ξ (Measure.infinitePi fun _ : ℕ => ν) μ` for `ξ : Ω → ℕ → β`; a function of the first `q` terms is `DependsOn F (Set.Iio q)`; conditioning on the past is `HasLaw.integral_comp_eq_integral_integral_of_dependsOn` | `hasLaw_infinitePi_iff`; Mathlib's `iIndepFun_iff_hasLaw_Pi_infinitePi` |
| sketch-and-project | `sketchAndProject A S b x := x + pinv (S * A) *ᵥ (S *ᵥ (b - A *ᵥ x))`, iterate `sketchAndProjectIterate A S b x₀ q` for `S : ℕ → Matrix k m 𝕜`; expected projector `∫ T, rangeProjector (T * A)ᴴ ∂ν`, no definition; error `xs - …` | `isLeastSquaresSolution_sketchAndProject`; Mathlib has none |
| randomized Kaczmarz | `kaczmarzIterate A ι b x₀ q`, rows `ι : ℕ → m`, law `samplingMeasure (rowNormSqDistribution A)` | `kaczmarzIterate_succ` (row-action formula); Mathlib has none |
| Frobenius condition number | `frobPseudoConditionNumber A := frobNorm A * specNorm (pinv A)`, any shape and rank; written out in docstrings, $\|\mathbf{A}\|_{\mathsf{F}}\|\mathbf{A}^{+}\|_2$ (CONTRIBUTING §6 keeps $\kappa$ for the classical one) | `frobPseudoConditionNumber_eq_frobNorm_div_singularValues`; Mathlib has none |

**Named constants.** None. Every constant is the source's and the proof reaches it: the rate
$1 - \kappa_{\mathsf{F}}^{-2}$ (Strohmer–Vershynin's), the horizon $\|\mathbf{A}^{+}\|_2^2\|\mathbf{r}\|^2$
(Zouzias–Freris's; only the factor $1 - \rho^q$ is new, and the horizon is smaller than Needell's),
$C = 1$, $\varepsilon_0 = 1$. No `docs/constants.toml` entry.

## 8. Proof plan and difficulty

Easy: under a day and 60 lines; medium: up to a few days or 150 lines.

| Theorem | Uses | Estimate |
|---|---|---|
| `pinv_replicateRow` | `pinv_eq_conjTranspose_mul_pinv_mul_conjTranspose_self`; $\mathbf{R}\mathbf{R}^{\mathsf{H}} = \|\mathbf{a}\|^2 \cdot \mathbf{1}$ on `Unit`; `pinv_smul`, `pinv_of_isUnit isUnit_one`; `Matrix.conjTranspose_replicateRow` | easy, 20 |
| `frobPseudoConditionNumber` API: `frobPseudoConditionNumber_nonneg`, `frobPseudoConditionNumber_zero`, `frobPseudoConditionNumber_eq_frobNorm_div_singularValues` (`k + 1 = rank`), `pseudoConditionNumber_le_frobPseudoConditionNumber`, `rank_le_frobPseudoConditionNumber_sq`, `frobPseudoConditionNumber_sq_le_rank_mul_pseudoConditionNumber_sq`, `one_le_frobPseudoConditionNumber` (`A ≠ 0`, which gives $0 \le \rho$), `frobPseudoConditionNumber_conjTranspose` | `specNorm_pinv`, `frobNorm_sq_eq_sum_range_singularValues_sq`, `singularValues_antitone`, `pseudoConditionNumber_def`, `pinv_conjTranspose` | easy, 60 |
| `rowNormSqDistribution` API | `frobNorm_sq_eq_sum_row`, `frobNorm_eq_zero_iff`, `NNReal` coercions | easy, 25 |
| `hasLaw_infinitePi_iff` | `iIndepFun_iff_hasLaw_Pi_infinitePi`, `measurePreserving_eval_infinitePi` with `fun_comp_hasLaw`, `aemeasurable_pi_lambda` | easy, 25 |
| `iIndepFun.indepFun_comp_of_dependsOn` | `iIndepFun.indepFun_finset₀` with `s` and `{t}`; `dependsOn_iff_exists_comp` to factor $F$ through `s.restrict`, measurably, by extending with a default point. That needs `∀ i, Nonempty (β i)`, which follows from `Nonempty Ω` (each `X i ω` inhabits `β i`); the case `Ω` empty is trivial ($\mu = 0$), so the proof opens with that case split. `IndepFun.comp`. Mathlib's `FactorsThrough.lean` has only the converse, so nothing shortens this | medium, 70 (plumbing) |
| `HasLaw.integral_comp_eq_integral_integral_of_dependsOn` | the above on the canonical space (`iIndepFun_infinitePi`) with `s = Finset.range q` and `Finset.coe_range`; `HasLaw.integral_comp` to transport; `IndepFun.integral_comp_eq_integral_integral`; `measurePreserving_eval_infinitePi` for the law of $\xi_q$ | medium, 50 |
| §3.2 nearest point, error identity, Pythagoras | `isLeastSquaresSolution_pinv_mulVec` on the shifted system, `IsLeastSquaresSolution.norm_pinv_mulVec_le`; `pinv_mul`, `mul_pinv_mul_self`; `isStarProjection_rangeProjector`, `IsStarProjection.norm_toLp_sq_eq_add`, `range_mulVecLin_pinv`, `rangeProjector_mulVec_eq_self_iff`; `classical` for the `1 - P` inside the Pythagoras proof | easy, 3 × 30 |
| §3.2 invariance, contraction, `DependsOn`, measurability | `range_mulVecLin_pinv` with `(S * A)ᴴ = Aᴴ * Sᴴ` (range of a product ≤ range of the left factor); `IsStarProjection.norm_toLp_mulVec_le`; induction; `measurable_pinv`, `Measurable.matrix_mul`, `Measurable.matrix_mulVec`, `measurable_pi_apply` | easy, 4 × 15 |
| `kaczmarzIterate_succ`, `mulVec_…_apply`, `norm_sub_kaczmarzIterate_succ_sq` | `conjTranspose_selectionMatrix_mul`, `conjTranspose_selectionMatrix_mulVec`, `pinv_replicateRow`; the rank-one projector $\mathbf{u}\mathbf{u}^{\mathsf{H}}/\|\mathbf{u}\|^2$; `norm_sub_sketchAndProject_sq` | easy, 50 total |
| §5.1 exact identity and bound | the ForMathlib lemma with $F$ = the iterate; `integral_map`; `Matrix.integral_quadForm` under the Loewner order (`Matrix.le_iff`, the `Matrix.PosSemidef` quadratic form); integrability from `norm_sub_sketchAndProjectIterate_le` (bounded) and boundedness of projectors; `rangeProjector_mono` and $\nu(\mathrm{univ}) = 1$ for $\lambda \le 1$; induction | medium, 100 |
| §5.1 mean error | the same Fubini step for a vector-valued $f$; Bochner integral commuting with `mulVec` (`ContinuousLinearMap.integral_comp_comm`, or `Matrix.integral_mulVec` added to `MatrixIntegral.lean`) | medium, 50 |
| §5.2 one-step inequality and identity | ForMathlib lemma; `integral_samplingMeasure`; `norm_sub_kaczmarzIterate_succ_sq` weighted by $p_i$; `frobNorm_sq_eq_sum_row`, `EuclideanSpace.norm_sq_eq`; the residual sum over rows with `A i ≠ 0` is at most, and under `hA` equal to, $\|\mathbf{r}\|^2$, **cases on `A i = 0` per row**; integrability (finitely valued: the iterate factors through `Fin q → m`); cases on $\mathbf{A} = \mathbf{0}$ (then $\mu = 0$) | medium, 80 |
| §5.2 primary bound and corollaries | the inequality; `sketchAndProjectIterate_sub_mem_range` plus `hx₀`; `norm_le_specNorm_pinv_mul_norm_mulVec_of_mem_range`; `integral_mono`; the recurrence $E_{q+1} \le \rho E_q + (1 - \rho)h$ by induction ($0 \le \rho$ from `one_le_frobPseudoConditionNumber`); consistent: $\mathbf{r} = \mathbf{0}$; nearest least-squares solution: $\mathbf{x}_\star := \mathbf{x}_0 + \mathbf{A}^{+}(\mathbf{b} - \mathbf{A}\mathbf{x}_0)$, its residual $(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{b}$ by `mul_pinv`, `range_mulVecLin_pinv` for the row-space hypothesis; its consistent case by `rangeProjector_mulVec_eq_self_iff` | medium, 60 + 3 × 15 |
| iteration counts, asymptotic forms | `Real.one_sub_le_exp_neg`, `pow_le_pow_left₀`, `Real.exp_log`; $C = 1$ | easy, 6 × 25 |
| §5.3 bridge and any-$p$ Kaczmarz | `integral_samplingMeasure`, `pinv_replicateRow`, `pinv_mul`, `Matrix.conjTranspose_mul_eq_sum_vecMulVec`; the HasLaw of the sketch sequence by `Measure.infinitePi_map_pi`; §5.1 | easy, 40 + 30 |
| mean iterate | the Fubini step, the bridge, linearity of the integral; induction against `richardsonIterate_succ` | easy, 40 |

Nothing needs new Matrix analysis. The only new probability is the Fubini-on-the-past lemma; the
rest reuses `samplingMeasure`, `HasLaw` and Mathlib's product measure. Stage order: **RK-0** lower
layers (ForMathlib, Law, Matrix additions), **RK-1** `SketchAndProject.lean`, **RK-2**
`Kaczmarz.lean`; a statement skeleton in `NLAlibScaffold` first, as for Hutch++. One proof agent at a
time, one file each.

## 9. Bibliography and explorer

**New `docs/references.bib` entries**, each added in the commit that first cites it (DOIs to check
against the publisher when added):
* `StrohmerVershynin2009`: T. Strohmer, R. Vershynin, *A randomized Kaczmarz algorithm with
  exponential convergence*, J. Fourier Anal. Appl. 15(2):262–278, 2009; arXiv:math/0702226.
* `Needell2010`: D. Needell, *Randomized Kaczmarz solver for noisy linear systems*, BIT Numer. Math.
  50(2):395–403, 2010; arXiv:0902.0958.
* `ZouziasFreris2013`: A. Zouzias, N. M. Freris, *Randomized extended Kaczmarz for solving least
  squares*, SIAM J. Matrix Anal. Appl. 34(2):773–793, 2013; arXiv:1205.5770.
* `GowerRichtarik2015`: R. M. Gower, P. Richtárik, *Randomized iterative methods for linear systems*,
  SIAM J. Matrix Anal. Appl. 36(4):1660–1690, 2015; arXiv:1506.03296.
* `LeventhalLewis2010`: D. Leventhal, A. S. Lewis, *Randomized methods for linear constraints:
  convergence rates and conditioning*, Math. Oper. Res. 35(3):641–654, 2010; arXiv:0806.3015.
* `MaNeedellRamdas2015`: A. Ma, D. Needell, A. Ramdas, *Convergence properties of the randomized
  extended Gauss–Seidel and Kaczmarz methods*, SIAM J. Matrix Anal. Appl. 36(4):1590–1604, 2015;
  arXiv:1503.08235.
* `NeedellTropp2014`: D. Needell, J. A. Tropp, *Paved with good intentions: analysis of a randomized
  block Kaczmarz method*, Linear Algebra Appl. 441:199–221, 2014; arXiv:1208.3805 (cited only in the
  deferral remarks of module docstrings until block Kaczmarz lands).

**Explorer.** Results: `randomized-kaczmarz`, `kaczmarz-inconsistent`, `kaczmarz-rank-deficient`
(the quarry atlas's ids, kept for continuity) and `sketch-and-project`. A new topic "Randomized
solvers" after Estimation, with collections "Kaczmarz" (definitions `NLAlib.kaczmarzIterate`,
`NLAlib.rowNormSqDistribution`) and "Sketch-and-project" (definition `NLAlib.sketchAndProject`).
Rates rows are deferred (maintainer, 2026-10-19); the `exists_forall_` forms exist for when they
are wanted. The explorer repository is edited by its own sessions; this note only proposes.

## 10. Coordination with `Regression-SketchPrecondition.md`

Shared conventions, agreed with the sibling note's revision:
* **Letters and argument order.** Both notes: system, sketch, right-hand side, start, count,
  following `sketchAndSolve A S B` and `pcgIterate A M b x₀ q`; sketch row type `k`, count `q`. The
  sibling writes the least-squares right-hand side `y`; this note writes `b` (linear systems, the
  sources' letter). Both iterates are total recursions with the count last (§5.3 row "algorithm").
* **Error order.** Solution minus iterate, `xs - …Iterate …`, in both notes and in Krylov
  (`re_quadForm_sub_cgIterate_le`, the sibling's `sub_richardsonIterate_eq`); row-space and
  Krylov-space memberships keep `…Iterate … - x₀`.
* **`richardsonIterate A M b x₀ q`** (sibling, `Krylov/LinearSystems/Richardson.lean`): the mean
  Kaczmarz iterate (§5.3) is stated with it, in the normal-equations form valid under either
  pending signature, and in the Landweber form if the rectangular one is adopted. This note does not
  define a second Richardson. Gower–Richtárik's mean error (§5.1) is stated with `(1 - E Z) ^ q`
  directly, since for a general law the expected iterate's affine part is not of Richardson's form
  without $\mathbf{x}_\star$.
* **Names kept distinct.** `iterativeSketching` (one fixed sketch, Richardson on the normal equations)
  against `sketchAndProject` / `kaczmarzIterate` (a fresh random sketch or row per step). `sketchAndSolve`
  is the one-shot sketched solution; `sketchAndProject A S b x - x = pinv (S * A) *ᵥ (S *ᵥ (b - A *ᵥ x))`
  is the vector sketch-and-solve correction for the current residual, a remark for the module
  docstring, not a theorem.
* **D2 is the sibling's deferred "fresh sketches per step"** (Pilanci–Wainwright's iterative Hessian
  sketch): that item needs exactly the i.i.d.-sequence idiom and the Fubini-on-the-past lemma of §4.
* **Placement.** Consistent with the approved D12: least squares in `Regression/`, row-action
  solvers in `Solvers/` (§7).
* **Solution interfaces.** Sibling: `IsLeastSquaresSolution A y xs`, energy error. Here:
  `A *ᵥ xs = b` (consistent), any `xs` with the residual `b - A *ᵥ xs` (inconsistent), Euclidean
  error. Both are existing spellings; no new interface either side.
* **Rates**: none in either note this round (maintainer, 2026-10-19).

## 11. Decisions

**For the maintainer (serious, hard to reverse)**

**D1. Sketch-and-project as the definition, Kaczmarz as its instance.** (a) `sketchAndProject` (with
`pinv`) and `sketchAndProjectIterate` are the definitions; `kaczmarzIterate` is the iterate with
single-row selection sketches, and the row-action update is the theorem `kaczmarzIterate_succ`
(§3.1). Block Kaczmarz, Gaussian sketch-and-project and arbitrary row probabilities are then
instances of one theorem (§5.1, §5.3). (b) Kaczmarz standalone with the explicit update as its
definition, sketch-and-project separate (the quarry; listed as a defect in
`inventory-sketching.md` §8). (c) Sketch-and-project only, Kaczmarz statements written with
`sketchAndProjectIterate A (fun q => (selectionMatrix fun _ : Unit => ι q)ᴴ) b x₀` (no name).
Recommendation: **(a)**: it follows the 2026-10-17 direction (methods defined mathematically,
implementations as realisation theorems), keeps a readable name for the method people cite, and
costs one definition. Changing it later renames every Kaczmarz statement.

**D2. The i.i.d.-sequence idiom** (§4). (a) `HasLaw ξ (Measure.infinitePi fun _ : ℕ => ν) μ` for
`ξ : Ω → ℕ → β`, a new §5.3 row with the bridge `hasLaw_infinitePi_iff` and the Fubini-on-the-past
lemma; (b) a finite-prefix law `Measure.pi (fun _ : Fin q => ν)` per statement; (c) `iIndepFun` plus
marginals. Recommendation: **(a)**: one hypothesis for all $q$, Mathlib's product measure, the
ℕ-analogue of the existing finite idiom, and the shape every later i.i.d. iteration (REK, block
Kaczmarz, fresh-sketch iterative sketching, SGD-type analyses) will take. It is library-wide
vocabulary, hence here.

**D3. A named Frobenius condition number.** (a) `frobPseudoConditionNumber A := frobNorm A * specNorm (pinv A)`
in `ConditionNumber.lean` (§7), rate `1 - 1 / frobPseudoConditionNumber A ^ 2`; (b) no definition, the rate
written out `1 - 1 / (frobNorm A * specNorm (pinv A)) ^ 2` in every statement, as
`Matrix-Pseudoinverse.md` §8 recorded ("There is no 'scaled condition number' definition; the
Kaczmarz rate is `1 - singularValues A k ^ 2 / frobNorm A ^ 2` with `k + 1 = card n`"); (c) the
singular-value form with an index hypothesis `k + 1 = A.rank`. Recommendation: **(a)**. The quantity
recurs in about a dozen statements here and in every later row-action method (REK, block Kaczmarz,
randomized Gauss–Seidel), CONTRIBUTING §4 asks for named quantities over repeated inline formulas,
and (c) needs a rank index, junk-free only for $\mathbf{A} \ne \mathbf{0}$. The 2026-10-14 remark predates
this consumer; (a) reverses it, so it is asked.

**Proceeding as recommended**
* **D4. Placement.** `Solvers/SketchAndProject.lean` and `Solvers/Kaczmarz.lean` per D12, flat; the
  alternative `Regression/` is a two-file move (§7).
* **D5. Primary Kaczmarz theorem.** The any-right-hand-side bound with factor $1 - \rho^q$
  (§5.2) is primary; the bound about the least-squares solution nearest $\mathbf{x}_0$ (no
  hypothesis), Strohmer–Vershynin's consistent form and the nearest-solution consistent form are
  corollaries; the quarry's six inconsistent variants become one theorem. The one-step statement is
  an inequality for every $\mathbf{A}$ and an identity under `∀ i, A i ≠ 0`.
* **D6. Rank.** No rank hypothesis anywhere: the row-space hypothesis
  `xs - x₀ ∈ LinearMap.range Aᴴ.mulVecLin` (the §5.3 column-space spelling), empty at full column
  rank, and the pseudoinverse in the rate.
* **D7. Scalars.** `RCLike` throughout; Strohmer–Vershynin already work over $\mathbb{C}$, and the
  complex update carries $\overline{\mathbf{a}_i}$ (Ma–Needell–Ramdas (2.1)).
* **D8. Sketch-and-project scope.** Euclidean metric only, consistent systems only for general laws,
  `[IsProbabilityMeasure ν]` on every expectation statement, the Loewner hypothesis
  `lam • rangeProjector Aᴴ ≤ ∫ T, rangeProjector (T * A)ᴴ ∂ν`, no new interface (instances prove it;
  nothing takes it twice).
* **D9. Sampling weights.** `rowNormSqDistribution A : m → ℝ≥0` as a definition (like
  `leverageScoreDistribution`), in `Frobenius.lean` (§7); general probabilities through
  `samplingMeasure p` with no new definition, and Kaczmarz for them this round (§5.3).
* **D10. Probability infrastructure.** The two ForMathlib lemmas and one Law bridge (§4, §7); no
  random-iterate definition, no generic drift lemma, no kernels.
* **D11. No `kaczmarzStep`**; one-step statements are the $q = 0$ case of iterate statements (§3.1).
  Error order `xs - …`, letters `k` and `q`, minimal instance arguments (`[DecidableEq n]` only where
  an `n × n` integral, Loewner order or `1 - …` occurs), shared with the sibling (§10).
* **D12. Asymptotic forms.** One explicit iteration-count corollary and one `exists_forall_` form
  each for consistent Kaczmarz, inconsistent Kaczmarz and sketch-and-project, $C = 1$,
  $\varepsilon_0 = 1$. No Rates rows this round.
* **D13. Scope** as in §6: REK next (moderate, recommended as the follow-up stage), block Kaczmarz with
  pavings, metric $\mathbf{B}$, almost-sure convergence and adaptive selection deferred with their
  gaps recorded.
* **D14. Mean iterate.** Gower–Richtárik's mean-error identity in (§5.1); the Kaczmarz mean iterate
  as Richardson in both forms (§5.3), landing after the sibling's `richardsonIterate`.

## Revision log (2026-10-19, after the Fable review)

* Blocking 1: the one-step expectation statement is now an inequality for every $\mathbf{A}$
  (`integral_norm_sub_kaczmarzIterate_succ_sq_le`, which the induction uses) and an identity under
  `∀ i, A i ≠ 0`, with the zero-row counterexample in its docstring; §1 and §8 updated.
* Blocking 2: `[IsProbabilityMeasure ν]` on the sketch-and-project bound, its iteration-count and
  `exists_forall_` forms; §4's degenerate-cases paragraph rewritten, with the reason the Kaczmarz
  statements survive $\mathbf{A} = \mathbf{0}$ (junk values make every right-hand side nonnegative).
* Should-fix: the any-$\mathbf{b}$ bound about the least-squares solution nearest $\mathbf{x}_0$
  (`integral_norm_add_pinv_mulVec_sub_kaczmarzIterate_sq_le`) replaces the consistent-only
  `_of_mem_range`, which becomes its corollary, and `_le_add` warns about $\mathbf{x}_\star = \mathbf{A}^{+}\mathbf{b}$;
  error order `xs - …` in every name; `[DecidableEq n]` dropped from the Kaczmarz statements; the
  Rates proposal deleted.
* Minor: the `Nonempty` case split and `Finset.coe_range` in §8; `open scoped MatrixOrder`; letters
  `k`, `q` as in the sibling; full asymptotic docstrings shown; $\rho \in [0, 1)$ in the
  Strohmer–Vershynin docstring; the length-squared remark on `rowNormSqDistribution`; Kaczmarz with
  any row probabilities moved into this round; the placement flag on `rowNormSqDistribution` resolved;
  the `frobPseudoConditionNumber` API names listed.
* Coordination: the mean iterate stated so that it holds under either `richardsonIterate` signature,
  with the Landweber form for the rectangular one.
* All changed signatures re-elaborated (scratch file `Scratch2.lean` in the session scratchpad,
  one Lean process, `sorry` warnings only).
