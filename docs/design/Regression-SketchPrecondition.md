# Design note: sketch-and-precondition and iterative sketching for overdetermined least squares

Draft of 2026-10-19, revised the same day after a bounded review (no blocking findings; the review
is in the session scratchpad), branch `regression/sketch-precondition` (worktree `nlalib-block`,
head `bc72b8d`). Approved 2026-10-19. Maintainer request (2026-10-19): "Let's do sketch and precondition
and Randomized kaczmarz." This note covers sketch-and-precondition as an algorithm with convergence
guarantees, not only the conditioning estimate. Randomized Kaczmarz has its own note,
`docs/design/Regression-Kaczmarz.md`. §9 lists the names the two notes share.

Maintainer decision (2026-10-19): "for sketch and precondition, dont worry about rates now". The
explorer Rates rows are deferred (§7). The `exists_forall_` forms that CONTRIBUTING §5.2 rule 3
requires are still in scope.

**Approved by the maintainer, 2026-10-19** ("good to all"):
* **D1:** what the algorithm is, as a definition.
* **D2:** the new names and §5.3 rows, with the explicit start.
* **D3:** the shape of `richardsonIterate`: rectangular, `A : Matrix m n 𝕜` with
  `M : Matrix n m 𝕜`, because the Kaczmarz note shares the definition.

Everything else in §8 goes ahead as recommended. The skeleton waits for the library-wide naming
audit (maintainer: "just wait for audit"), and names here follow its grammar once adopted.

**Scope recommendation.** In this round:
* sketch-and-precondition (PCG on the normal equations, preconditioned by the sketched Gram matrix)
  from any start and from the sketch-and-solve warm start, with energy, residual and forward-error
  bounds;
* iterative sketching, undamped and damped (rectangular preconditioned Richardson);
* one generic tail theorem for each start of each algorithm;
* Gaussian, sub-Gaussian, SRHT and CountSketch corollaries for sketch-and-precondition, each with
  explicit sizes and an `exists_forall_` form, plus an explicit-start form.

Deferred (§7): LSQR's Golub–Kahan recurrence, momentum, rank-deficient and underdetermined
problems, ridge regularisation, fresh sketches at every step, floating point, cold-start family
corollaries, Haar, and Rates rows. The work is about 1,400 lines in eight files.

**What was elaborated.** Every Lean signature in §3 (definitions, bridges and realisations), §4
(deterministic statements) and §5 (generic tails, all four explicit family theorems, the Gaussian
explicit-start form, all four asymptotic forms) elaborates against the current build. The check was
one `lake env lean` run on `sorry` stubs:
`/tmp/claude-1000/-home-tyler-Documents-NLA-lib/bfb769ef-6d07-45c0-88a2-1c5dcd237c2b/scratchpad/sp/SP2.lean`.
It reported 40 declarations and no errors. Docstrings were not elaborated. They are written in full
here, but `check_latex.mjs` and `check_constants.py` run on them only at the skeleton. The
sub-Gaussian, SRHT and CountSketch explicit-start forms are the Gaussian one with the law
hypothesis changed, so they were not elaborated separately.

Sources read for this note (PDFs fetched into the session scratchpad):

* [MartinssonTropp2020] §§10.1–10.7 (arXiv:2002.01387): §10.4 iterative sketching, §10.5
  sketch-and-precondition ("a reinterpretation of the theory in Rokhlin and Tygert (2008)"), and
  Remark 10.3 for the history (Rokhlin–Tygert, Blendenpik, LSRN). MT's
  $\|\mathbf{A}\mathbf{x}_j - \mathbf{b}\| \le (1 + \varepsilon)\|\mathbf{A}\mathbf{x}_\star - \mathbf{b}\|$
  is unsquared.
* [Epperly2024] E. N. Epperly, *Fast and forward stable randomized algorithms for linear
  least-squares problems*, arXiv:2311.04362v2. Read: Algorithm 1 (sketch-and-precondition with the
  sketch-and-solve start and preconditioned LSQR), Definition 2, Fact 3, Fact 4 (sketch-and-solve),
  (3.2) (iterative sketching as iterative refinement on the normal equations), Theorem 5 and its
  proof §3.6, and Appendix B with Theorem 10 (damping and momentum).
* [EpperlyMeierNakatsukasa2024] arXiv:2406.03468v3. Read: Fact 2.2 (randomized preconditioning for
  any orthogonal factorization $\mathbf{S}\mathbf{A} = \mathbf{Q}\mathbf{R}$), §2.1 ("CG and MINRES
  on the normal equations are mathematically equivalent to LSQR and LSMR"), and §3.1 (the variants
  side by side).
* [PilanciWainwright2016] arXiv:1411.0347: the iterative Hessian sketch, with a fresh sketch per
  step and a convex constraint. Read for scope only (§7).
* Not fetched, cited from the surveys: [RokhlinTygert2008], [AvronMaymounkovToledo2010],
  [MengSaundersMahoney2014], [PaigeSaunders1982]. Their locators are marked "to verify".

**Convention, and its translation (every docstring of §§4–5 states it).** The library's subspace
embedding has squared constants:
$a\|\mathbf{v}\|^2 \le \|\mathbf{S}\mathbf{v}\|^2 \le b\|\mathbf{v}\|^2$ (`IsSubspaceEmbedding`).
Its $\varepsilon$ form is $a = 1 - \varepsilon$, $b = 1 + \varepsilon$.
1. Epperly and EMN use the unsquared distortion
   $(1 - \eta)\|\mathbf{v}\| \le \|\mathbf{S}\mathbf{v}\| \le (1 + \eta)\|\mathbf{v}\|$. Their
   formulas are the general $(a, b)$ theorems at $a = (1 - \eta)^2$, $b = (1 + \eta)^2$, not the
   $1 \mp \varepsilon$ corollaries.
2. At those values the PCG rate $(\sqrt{b/a} - 1)/(\sqrt{b/a} + 1)$ is exactly $\eta$, and the
   warm-start factor is $4(b/a - 1) = 16\eta/(1 - \eta)^2$.
3. The library's residual bounds are squared, $(1 + \tau)\,\mathrm{OPT}^2$, against MT's unsquared
   $(1 + \varepsilon)$.

## 1. What exists, and what is missing

Verified by grep in this worktree. Every name below exists, and the review read each statement.

**Deterministic conditioning (Regression).** `NLAlib/Regression/Embedding.lean` has
sketch-and-precondition only as a conditioning estimate:
* the Loewner halves `IsSubspaceEmbedding.inv_smul_one_le_conjTranspose_mul_self` and
  `IsSubspaceEmbedding.conjTranspose_mul_self_le_inv_smul_one`;
* `IsSubspaceEmbedding.pseudoConditionNumber_mul_sq_le` (`Result: sketch-and-precondition`) and its
  QR form `IsSubspaceEmbedding.pseudoConditionNumber_mul_inv_sq_le_of_isQR`.

Sketch-and-solve is `IsSubspaceEmbedding.norm_sub_mulVec_sq_le` (any minimizer, any $\mathbf{U}$
whose range contains $\operatorname{range}\mathbf{A}$ and $\mathbf{y}$), with
`IsSubspaceEmbedding.norm_sub_mulVec_le` and `IsSubspaceEmbedding.norm_sub_mulVec_sq_le_of_fromCols`.

**Least squares, Gram matrices and factorizations (Matrix).**
* Least squares: `IsLeastSquaresSolution`, `isLeastSquaresSolution_iff_normal_equations`,
  `IsLeastSquaresSolution.norm_sub_mulVec_sq_eq_add` (Pythagoras),
  `IsLeastSquaresSolution.sub_mulVec_eq`, `exists_isLeastSquaresSolution`,
  `isLeastSquaresSolution_pinv_mulVec`, `sketchAndSolve` (matrix right-hand side).
* Gram matrices and the pseudoinverse: `posDef_conjTranspose_mul_self_iff`,
  `pinv_conjTranspose_mul_self`, `pinv_of_isUnit`, `quadForm_conjTranspose_mul_self`,
  `quadForm_conjTranspose_mul_mul`.
* Factorizations: `IsQR` (field `hasOrthonormalCols`), `IsSVD` (fields `hasOrthonormalCols_left`,
  `hasOrthonormalCols_right`, `eq`).
* The smallest singular value: `singularValues_last_mul_norm_le`
  ($\sigma_j(\mathbf{A})\|\mathbf{x}\| \le \|\mathbf{A}\mathbf{x}\|$ for $j + 1 = \lvert n\rvert$).

**Krylov (layer 1).**
* Iterates: `cgIterate` and `pcgIterate`, Galerkin definitions, basis-free.
* PCG bounds: `Matrix.IsHermitian.re_quadForm_sub_pcgIterate_le_four_mul_pow`,
  `Matrix.PosDef.re_quadForm_sub_pcgIterate_le`,
  `Matrix.PosDef.re_quadForm_sub_pcgIterate_le_residualMinimax_sq_mul`.
* Structure: `Matrix.PosDef.isMinOn_pcgIterate`, the split form
  `Matrix.PosDef.pcgIterate_eq_mulVec_cgIterate`, the recurrence `Matrix.PosDef.pcgState_x_eq`, and
  `pcgIterate_sub_mem_krylovSpace`.
* CGLS: `cgIterate (Aᴴ * A) (Aᴴ *ᵥ b) x₀ q`, unnamed, with
  `re_quadForm_sub_cgIterate_conjTranspose_mul_le_four_mul_pow`.
* Spectral equivalence: `Matrix.PosDef.spectrum_mul_subset_Icc_of_le` and
  `Matrix.PosDef.smul_le_and_le_smul_iff_spectrum_subset`.
* The polynomial bound behind every Krylov estimate: `Matrix.IsHermitian.re_quadForm_aeval_aeval_mulVec_le`.
* The factor and similarity behind every PCG bound:
  `Matrix.PosDef.exists_eq_mul_conjTranspose_and_eq_mul_diagonal_mul_conjTranspose` and
  `spectrum_mul_conjTranspose_mul`. `PCG.lean`'s helper `exists_split` is private.

There is no Richardson iteration. `docs/design/Krylov-LinearSystems.md` L12 deferred it for want of
a consumer, and iterative sketching is that consumer. `docs/PORT_KRYLOV.md` D12 planned
`Krylov/LinearSystems/PolynomialIteration`. It placed sketch-and-precondition and iterative
sketching in `Regression/`, and Kaczmarz and sketch-and-project in `Solvers/`.

**Probabilistic embeddings (Sketching).**
* Interfaces: `HasSubspaceEmbedding S U a b δ μ` and `IsObliviousSubspaceEmbedding S d a b δ μ`.
* `IsObliviousSubspaceEmbedding.hasSubspaceEmbedding` applies to any $\mathbf{U}$ of rank at most
  $d$, of any shape.
* Size forms concluding `IsObliviousSubspaceEmbedding … d (1 - ε) (1 + ε) δ μ`:

| Family | Size theorem | Named size | Field | Asymptotic form |
|---|---|---|---|---|
| Gaussian, $\lvert k\rvert^{-1/2}\mathbf{G}$ | `isObliviousSubspaceEmbedding_of_hasLaw_gaussianMatrix_of_gaussianEmbeddingDim_le` | `gaussianEmbeddingDim d ε δ` | ℝ | `exists_forall_isObliviousSubspaceEmbedding_of_hasLaw_gaussianMatrix` ($C = 72$) |
| sub-Gaussian rows, $\lvert k\rvert^{-1/2}\mathbf{X}$ | `isObliviousSubspaceEmbedding_of_isSubgaussianVector_of_subgaussianEmbeddingDim_le` | `subgaussianEmbeddingDim c d ε δ` | ℝ | `exists_forall_isObliviousSubspaceEmbedding_of_isSubgaussianVector` ($C = 1152$) |
| SRHT | `isObliviousSubspaceEmbedding_of_hasLaw_srht_of_samplingSize_le` | `samplingSize d (β * srhtRowBound (card n) d (δ/2)) ε (δ/2)` | `RCLike` | `exists_forall_isObliviousSubspaceEmbedding_of_hasLaw_srht` ($C = 72$) |
| CountSketch | `isObliviousSubspaceEmbedding_of_hasLaw_countSketch_of_countSketchRows_le` | `countSketchRows d ε δ` | `RCLike` | `exists_forall_isObliviousSubspaceEmbedding_of_hasLaw_countSketch` ($C = 2$, no `δ ≤ 1/2`) |

The Haar embedding `isObliviousSubspaceEmbedding_of_hasLaw_haarFrame` exists only in tail form,
with constants depending on two tail parameters and no $1 \mp \varepsilon$ size form. Its
corollary is therefore not a one-liner (§7).

**Mathlib.** Searched `Mathlib/LinearAlgebra/Matrix` and `Mathlib/Analysis` for Richardson,
stationary iteration, preconditioned least squares and LSQR: none. No bridge is needed and no
deviation arises.

**Quarry.**
* `NLAlib.Krylov.Solvers.Preconditioned` (`IsPCGIterate`, `IsCGLSIterate`,
  `isPCGIterate_iff_isCGIterate`, `quadForm_sub_le_of_isPCGIterate`): superseded by `pcgIterate`.
  Nothing to port.
* `NLAlib.Krylov.Solvers.PolynomialMethods` (`polyIterate`, `richardsonIterate ω A c x₀ q`,
  `richardsonIterate_succ`, `quadForm_richardsonIterate_sub_le`,
  `quadForm_richardsonIterate_sub_le_of_optimal`, `chebyshevIterate`): real and unpreconditioned.
  Reused as mathematics: the residual polynomial $(1 - x)^q$ and the scalar bound
  $\lvert(1 - x)^q\rvert \le \max(\lvert 1 - a\rvert, \lvert 1 - a'\rvert)^q$ on $[a, a']$ (its
  private `abs_eval_richardson_le`). Not reproduced: the polynomial-method definition and the
  separate step argument (D3).

## 2. The mathematics in one page

Let $\mathbf{A} \in \Bbbk^{m \times n}$ have full column rank, $\mathbf{y} \in \Bbbk^m$,
$\mathbf{S} \in \Bbbk^{k \times m}$, and let $\mathbf{x}_\star$ be the least-squares solution.
Write $\mathbf{G} = (\mathbf{S}\mathbf{A})^{\mathsf{H}}\mathbf{S}\mathbf{A}$ and
$\mathrm{OPT} = \|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{y}\|$. A subspace embedding of
$\operatorname{range}\mathbf{A}$ is the sandwich
$a\,\mathbf{A}^{\mathsf{H}}\mathbf{A} \preceq \mathbf{G} \preceq b\,\mathbf{A}^{\mathsf{H}}\mathbf{A}$.
With $a > 0$, $\mathbf{G}$ is positive definite. With $\mathbf{M} = \mathbf{G}^{-1}$ the sandwich
gives $\sigma(\mathbf{M}\mathbf{A}^{\mathsf{H}}\mathbf{A}) \subseteq [b^{-1}, a^{-1}]$, an
interval of ratio $b/a$.

1. **Sketch-and-precondition** is PCG on the normal equations with preconditioner $\mathbf{G}^{+}$.
   * **Realisations.** Take any factor $\mathbf{M}$ with $\mathbf{S}\mathbf{A}\mathbf{M}$
     orthonormal: QR's $\mathbf{R}^{-1}$, or LSRN's $\mathbf{V}\mathbf{\Sigma}^{-1}$. Then
     $\mathbf{G}^{+} = \mathbf{M}\mathbf{M}^{\mathsf{H}}$, so the iterate is $\mathbf{M}$ times
     CGLS on $\mathbf{A}\mathbf{M}$. That is preconditioned LSQR in exact arithmetic
     [EpperlyMeierNakatsukasa2024, §2.1].
   * **Rate.** The $\mathbf{A}^{\mathsf{H}}\mathbf{A}$-norm is $\|\mathbf{A}\cdot\|$, so the PCG
     bound gives
     $\|\mathbf{A}(\mathbf{x}_\star - \mathbf{x}_q)\|^2 \le 4\rho^{2q}\|\mathbf{A}(\mathbf{x}_\star - \mathbf{x}_0)\|^2$
     with $\rho = (\sqrt{b/a} - 1)/(\sqrt{b/a} + 1)$.
   * **Rate at $1 \mp \varepsilon$.** $\rho = \varepsilon/(1 + \sqrt{1 - \varepsilon^2}) \le \varepsilon$.
     With $s = \sqrt{b/a} \ge 1$, $\rho \le \varepsilon$ is $s(1 - \varepsilon) \le 1 + \varepsilon$,
     which holds because $s \le s^2$.
   * **Rate in $\eta$.** $\rho = \eta$.
2. **Warm start.** Let $\mathbf{S}$ embed a subspace containing $\operatorname{range}\mathbf{A}$
   and $\mathbf{y}$, and let $\mathbf{x}_0$ minimize $\|\mathbf{S}(\mathbf{A}\mathbf{x} - \mathbf{y})\|$.
   * Pythagoras and sketch-and-solve give
     $\|\mathbf{A}(\mathbf{x}_\star - \mathbf{x}_0)\|^2 \le (b/a - 1)\,\mathrm{OPT}^2$, hence
     $\|\mathbf{y} - \mathbf{A}\mathbf{x}_q\|^2 \le (1 + 4(b/a - 1)\rho^{2q})\,\mathrm{OPT}^2$.
   * At $1 \mp \varepsilon$ this is $(1 + 8\varepsilon^{2q+1}/(1 - \varepsilon))\,\mathrm{OPT}^2$.
     In $\eta$ it is $(1 + 16\eta^{2q+1}/(1 - \eta)^2)\,\mathrm{OPT}^2$.
   * The forward error follows from
     $\sigma_{\min}(\mathbf{A})^2\|\mathbf{x}_\star - \mathbf{x}_q\|^2 \le \|\mathbf{A}(\mathbf{x}_\star - \mathbf{x}_q)\|^2$,
     the form Epperly's theorems state.
3. **Iterative sketching** is $\mathbf{x}_{i+1} = \mathbf{x}_i + \omega\mathbf{G}^{+}\mathbf{A}^{\mathsf{H}}(\mathbf{y} - \mathbf{A}\mathbf{x}_i)$
   [Epperly2024, (3.2)]. This is Richardson on the rectangular system with
   $\mathbf{M} = \omega\mathbf{G}^{+}\mathbf{A}^{\mathsf{H}}$, and equally Richardson on the normal
   equations with $\omega\mathbf{G}^{+}$.
   * **Rate.** The error is $(\mathbf{I} - \omega\mathbf{G}^{+}\mathbf{A}^{\mathsf{H}}\mathbf{A})^q$
     applied to the initial error. That matrix is self-adjoint in the $\mathbf{A}^{\mathsf{H}}\mathbf{A}$
     inner product, so
     $\|\mathbf{A}(\mathbf{x}_\star - \mathbf{x}_q)\|^2 \le \max(\lvert 1 - \omega/b\rvert, \lvert 1 - \omega/a\rvert)^{2q}\|\mathbf{A}(\mathbf{x}_\star - \mathbf{x}_0)\|^2$.
     There is no prefactor: Epperly's proof (§3.6) goes through $\|\mathbf{S}\mathbf{A}\cdot\|$ and
     pays $(1 + \eta)/(1 - \eta)$.
   * **At $1 \mp \varepsilon$.** The rate is $\varepsilon/(1 - \varepsilon)$ at $\omega = 1$, and
     $\varepsilon$ at $\omega = 1 - \varepsilon^2$.
   * **In $\eta$** (the general theorem at $a = (1 - \eta)^2$, $b = (1 + \eta)^2$). At
     $\omega = 1$ the rate is Epperly's $g_{\mathrm{IS}} = (2 - \eta)\eta/(1 - \eta)^2$ (Theorem 5).
     At $\omega = 2ab/(a + b) = (1 - \eta^2)^2/(1 + \eta^2)$ it is
     $g_{\mathrm{damp}} = 2\eta/(1 + \eta^2)$ ((B.2), Theorem 10).
4. **PCG beats Richardson** with the same square preconditioner, from every start. The Richardson
   iterate lies in $\mathbf{x}_0 + \mathcal{K}_q(\mathbf{M}\mathbf{A}, \mathbf{M}\mathbf{r}_0)$,
   where PCG minimizes the energy error.
5. **Probability.** Every conclusion is deterministic given `IsSubspaceEmbedding`, so each tail is
   one `measureReal_mono` from `HasSubspaceEmbedding`.
   * The cold start needs $d = \lvert n\rvert$.
   * The warm start needs $d = \lvert n\rvert + 1$, the range of $[\mathbf{A}\ \mathbf{y}]$. Its
     rank bound is `Matrix.rank_le_card_width` with `Fintype.card_sum` and `Fintype.card_unit`.

## 3. Definitions

### 3.1 Rectangular preconditioned Richardson (Krylov layer; D3)

```lean
-- NLAlib/Krylov/LinearSystems/Richardson.lean
variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- The **preconditioned Richardson iterate** for $\mathbf{A} \in \Bbbk^{m \times n}$ with an
approximate inverse $\mathbf{M} \in \Bbbk^{n \times m}$:
$\mathsf{richardsonIterate}(\mathbf{A}, \mathbf{M}, \mathbf{b}, \mathbf{x}_0, 0) := \mathbf{x}_0$
and $\mathsf{richardsonIterate}(\mathbf{A}, \mathbf{M}, \mathbf{b}, \mathbf{x}_0, q + 1) :=
\mathbf{x}_q + \mathbf{M}(\mathbf{b} - \mathbf{A}\mathbf{x}_q)$. A step size $\omega$ is the
preconditioner $\omega\mathbf{M}$. Square with $\mathbf{M} = \mathbf{I}$, it is Richardson's
method with unit step; with an approximate inverse, iterative refinement; with
$\mathbf{M} = \omega\mathbf{A}^{\mathsf{H}}$, Landweber's iteration; with
$\mathbf{M} = \mathbf{N}\mathbf{A}^{\mathsf{H}}$, Richardson on the normal equations
(`NLAlib.richardsonIterate_mul_conjTranspose`). Total, no hypothesis.
[Saad2003, §4.2]; [Greenbaum1997, §2.1]; locators to verify. -/
noncomputable def richardsonIterate (A : Matrix m n 𝕜) (M : Matrix n m 𝕜) (b : m → 𝕜)
    (x₀ : n → 𝕜) : ℕ → n → 𝕜
  | 0 => x₀
  | q + 1 => richardsonIterate A M b x₀ q + M *ᵥ (b - A *ᵥ richardsonIterate A M b x₀ q)
```

The argument order matches `pcgIterate A M b x₀ q`. API: `@[simp] richardsonIterate_zero`,
`richardsonIterate_succ` (rfl), and the three lemmas below.

```lean
/-- **The error of Richardson's iteration**: if $\mathbf{x}_\star$ is a fixed point,
$\mathbf{M}(\mathbf{b} - \mathbf{A}\mathbf{x}_\star) = \mathbf{0}$, then
$\mathbf{x}_\star - \mathbf{x}_q = (\mathbf{I} - \mathbf{M}\mathbf{A})^q(\mathbf{x}_\star - \mathbf{x}_0)$.
The fixed-point hypothesis covers a solution of a consistent system
($\mathbf{A}\mathbf{x}_\star = \mathbf{b}$) and, for $\mathbf{M} = \mathbf{N}\mathbf{A}^{\mathsf{H}}$, a
least-squares solution (`isLeastSquaresSolution_iff_conjTranspose_mulVec_sub_eq_zero`). -/
theorem sub_richardsonIterate_eq {A : Matrix m n 𝕜} {M : Matrix n m 𝕜} {b : m → 𝕜}
    {xs : n → 𝕜} (hxs : M *ᵥ (b - A *ᵥ xs) = 0) (x₀ : n → 𝕜) (q : ℕ) :
    xs - richardsonIterate A M b x₀ q = ((1 - M * A) ^ q) *ᵥ (xs - x₀)

/-- The correction lies in the preconditioned Krylov space
$\mathcal{K}_q(\mathbf{M}\mathbf{A}, \mathbf{M}\mathbf{r}_0)$, for every $\mathbf{A}$, $\mathbf{M}$. -/
theorem richardsonIterate_sub_mem_krylovSpace (A : Matrix m n 𝕜) (M : Matrix n m 𝕜)
    (b : m → 𝕜) (x₀ : n → 𝕜) (q : ℕ) :
    richardsonIterate A M b x₀ q - x₀ ∈ krylovSpace (M * A) (M *ᵥ (b - A *ᵥ x₀)) q

/-- **Richardson through $\mathbf{A}^{\mathsf{H}}$ is Richardson on the normal equations**:
$\mathsf{richardsonIterate}(\mathbf{A}, \mathbf{M}\mathbf{A}^{\mathsf{H}}, \mathbf{y}, \mathbf{x}_0, q)
= \mathsf{richardsonIterate}(\mathbf{A}^{\mathsf{H}}\mathbf{A}, \mathbf{M}, \mathbf{A}^{\mathsf{H}}\mathbf{y},
\mathbf{x}_0, q)$. Five-line induction. -/
theorem richardsonIterate_mul_conjTranspose (A : Matrix m n 𝕜) (M : Matrix n n 𝕜) (y : m → 𝕜)
    (x₀ : n → 𝕜) (q : ℕ) :
    richardsonIterate A (M * Aᴴ) y x₀ q = richardsonIterate (Aᴴ * A) M (Aᴴ *ᵥ y) x₀ q
```

**The Kaczmarz note's call fits.** `Regression-Kaczmarz.md` §5.3 writes the mean Kaczmarz
iterate as `richardsonIterate (Aᴴ * A) ((frobNorm A ^ 2)⁻¹ • 1) (Aᴴ *ᵥ b) x₀ k`. This is the
rectangular signature at `m := n`, with `Aᴴ * A : Matrix n n 𝕜` and `M : Matrix n n 𝕜`, so it
elaborates unchanged (checked). Its rectangular equivalent is the Landweber form
`richardsonIterate A ((frobNorm A ^ 2)⁻¹ • Aᴴ) b x₀ k`. The two are equal by
`richardsonIterate_mul_conjTranspose` with `smul_mul` and `Matrix.one_mul`; this equation was also
elaborated. The Kaczmarz note may use either spelling; the Landweber one avoids forming
$\mathbf{A}^{\mathsf{H}}\mathbf{A}$.

### 3.2 The two least-squares algorithms (Regression layer)

```lean
-- NLAlib/Regression/SketchAndPrecondition.lean
variable {𝕜 : Type*} [RCLike 𝕜] {k m n : Type*} [Fintype k] [Fintype m] [Fintype n]
  [DecidableEq n]

/-- The **sketch-and-precondition iterate** after $q$ steps from $\mathbf{x}_0$:
$\mathsf{sketchAndPrecondition}(\mathbf{A}, \mathbf{S}, \mathbf{y}, \mathbf{x}_0, q) :=
\mathsf{pcgIterate}(\mathbf{A}^{\mathsf{H}}\mathbf{A}, \mathbf{G}^{+}, \mathbf{A}^{\mathsf{H}}\mathbf{y},
\mathbf{x}_0, q)$ with $\mathbf{G} = (\mathbf{S}\mathbf{A})^{\mathsf{H}}\mathbf{S}\mathbf{A}$: PCG
on the normal equations, preconditioned by the sketched Gram matrix. Basis-free. For a QR
factorization $\mathbf{S}\mathbf{A} = \mathbf{Q}\mathbf{R}$ it is $\mathbf{R}^{-1}$ times CGLS on
$\mathbf{A}\mathbf{R}^{-1}$ (`NLAlib.IsQR.sketchAndPrecondition_eq_mulVec_cgIterate`), which is
preconditioned LSQR in exact arithmetic. For an SVD it is LSRN's preconditioner
(`NLAlib.IsSVD.sketchAndPrecondition_eq_mulVec_cgIterate`). The preconditioned Hestenes–Stiefel
recurrence computes it (`NLAlib.pcgState_x_eq_sketchAndPrecondition`). The warm start is
$\mathbf{x}_0 = (\mathbf{S}\mathbf{A})^{+}\mathbf{S}\mathbf{y}$. Junk value: that of
`pcgIterate` when $\mathbf{A}$ is rank deficient.
[RokhlinTygert2008]; [AvronMaymounkovToledo2010]; [MartinssonTropp2020, §10.5];
[Epperly2024, Algorithm 1]. -/
noncomputable def sketchAndPrecondition (A : Matrix m n 𝕜) (S : Matrix k m 𝕜) (y : m → 𝕜)
    (x₀ : n → 𝕜) (q : ℕ) : n → 𝕜 :=
  pcgIterate (Aᴴ * A) (pinv ((S * A)ᴴ * (S * A))) (Aᴴ *ᵥ y) x₀ q

-- NLAlib/Regression/IterativeSketching.lean
/-- The **iterative sketching iterate** with step $\omega$:
$\mathsf{iterativeSketching}(\mathbf{A}, \mathbf{S}, \omega, \mathbf{y}, \mathbf{x}_0, q) :=
\mathsf{richardsonIterate}(\mathbf{A}, \omega\mathbf{G}^{+}\mathbf{A}^{\mathsf{H}}, \mathbf{y},
\mathbf{x}_0, q)$, that is
$\mathbf{x}_{i+1} = \mathbf{x}_i + \omega\mathbf{G}^{+}\mathbf{A}^{\mathsf{H}}(\mathbf{y} - \mathbf{A}\mathbf{x}_i)$
with $\mathbf{G} = (\mathbf{S}\mathbf{A})^{\mathsf{H}}\mathbf{S}\mathbf{A}$. One sketch, fixed for
all steps. $\omega = 1$ is Epperly's iterative sketching. His damped variant is
$\omega = (1 - \eta^2)^2/(1 + \eta^2)$, which is $1 - \varepsilon^2$ in the library's squared
convention. [Epperly2024, (3.2), (B.2)]; [PilanciWainwright2016] with a fresh sketch per step. -/
noncomputable def iterativeSketching (A : Matrix m n 𝕜) (S : Matrix k m 𝕜) (ω : ℝ) (y : m → 𝕜)
    (x₀ : n → 𝕜) (q : ℕ) : n → 𝕜 :=
  richardsonIterate A (ω • (pinv ((S * A)ᴴ * (S * A)) * Aᴴ)) y x₀ q

/-- Iterative sketching is Richardson on the normal equations with $\omega\mathbf{G}^{+}$. -/
theorem iterativeSketching_eq (A : Matrix m n 𝕜) (S : Matrix k m 𝕜) (ω : ℝ) (y : m → 𝕜)
    (x₀ : n → 𝕜) (q : ℕ) :
    iterativeSketching A S ω y x₀ q =
      richardsonIterate (Aᴴ * A) (ω • pinv ((S * A)ᴴ * (S * A))) (Aᴴ *ᵥ y) x₀ q
```

`iterativeSketching_eq` is `richardsonIterate_mul_conjTranspose` after `Matrix.smul_mul`. Every
bound of §4.4 goes through it to the square theorems of §4.1.

Argument order: system, sketch, step, right-hand side, start, count, following `sketchAndSolve A S B`
and `pcgIterate A M b x₀ q`. The start is explicit. The warm start is the hypothesis
`IsLeastSquaresSolution (S * A) (S *ᵥ y) x₀` (any sketched minimizer), which
`pinv (S * A) *ᵥ (S *ᵥ y)` satisfies by `isLeastSquaresSolution_pinv_mulVec`. A vector-valued
`sketchAndSolve` does not exist, so that is the spelling.

### 3.3 Realisation theorems

The redundant hypotheses are gone. Orthonormal columns of $\mathbf{B}\mathbf{M}$, or of
$\mathbf{S}\mathbf{A}\mathbf{M}$, already make $\mathbf{M}$ injective and so invertible, being
square. They also make $\mathbf{A}$ injective, because $\mathbf{M}$ is surjective. The proofs derive
`IsUnit M` through `Matrix.mulVec_injective_iff_isUnit`. `hR : IsUnit R` stays in the `IsQR` form,
where it does not follow (`IsQR` allows a singular `R`).

```lean
-- Matrix/Pseudoinverse/Pinv.lean (outside the stage, §6)
/-- If $\mathbf{B}\mathbf{M}$ has orthonormal columns for square $\mathbf{M}$, then
$(\mathbf{B}^{\mathsf{H}}\mathbf{B})^{+} = \mathbf{M}\mathbf{M}^{\mathsf{H}}$: every orthogonal
factorization gives the same preconditioner (QR's $\mathbf{R}^{-1}$, SVD's
$\mathbf{V}\mathbf{\Sigma}^{-1}$). [EpperlyMeierNakatsukasa2024, Fact 2.2 context]. -/
theorem pinv_conjTranspose_mul_self_eq_mul_conjTranspose {B : Matrix k n 𝕜} {M : Matrix n n 𝕜}
    (hBM : HasOrthonormalCols (B * M)) : pinv (Bᴴ * B) = M * Mᴴ

-- Regression/SketchAndPrecondition.lean
/-- **Sketch-and-precondition is CGLS on $\mathbf{A}\mathbf{M}$**: for square $\mathbf{M}$ with
$\mathbf{S}\mathbf{A}\mathbf{M}$ orthonormal and $\mathbf{M}\mathbf{z}_0 = \mathbf{x}_0$,
$\mathsf{sketchAndPrecondition}(\mathbf{A}, \mathbf{S}, \mathbf{y}, \mathbf{x}_0, q) =
\mathbf{M}\,\mathsf{cgIterate}((\mathbf{A}\mathbf{M})^{\mathsf{H}}\mathbf{A}\mathbf{M},
(\mathbf{A}\mathbf{M})^{\mathsf{H}}\mathbf{y}, \mathbf{z}_0, q)$.
[RokhlinTygert2008]; [AvronMaymounkovToledo2010]; [EpperlyMeierNakatsukasa2024, §2.1].
Result: sketch-and-precondition-realisation -/
theorem sketchAndPrecondition_eq_mulVec_cgIterate {S : Matrix k m 𝕜} {A : Matrix m n 𝕜}
    {M : Matrix n n 𝕜} (hSAM : HasOrthonormalCols (S * A * M)) (y : m → 𝕜) {x₀ z₀ : n → 𝕜}
    (hz₀ : M *ᵥ z₀ = x₀) (q : ℕ) :
    sketchAndPrecondition A S y x₀ q =
      M *ᵥ cgIterate ((A * M)ᴴ * (A * M)) ((A * M)ᴴ *ᵥ y) z₀ q

/-- **QR form** (Blendenpik): for a thin QR factorization $\mathbf{S}\mathbf{A} = \mathbf{Q}\mathbf{R}$
with $\mathbf{R}$ invertible, the iterate is $\mathbf{R}^{-1}$ times CGLS on
$\mathbf{A}\mathbf{R}^{-1}$ from $\mathbf{R}\mathbf{x}_0$. [AvronMaymounkovToledo2010]. -/
theorem IsQR.sketchAndPrecondition_eq_mulVec_cgIterate [LinearOrder n] {Q : Matrix k n 𝕜}
    {R : Matrix n n 𝕜} (hQR : IsQR (S * A) Q R) (hR : IsUnit R) (y : m → 𝕜) (q : ℕ) :
    sketchAndPrecondition A S y x₀ q =
      R⁻¹ *ᵥ cgIterate ((A * R⁻¹)ᴴ * (A * R⁻¹)) ((A * R⁻¹)ᴴ *ᵥ y) (R *ᵥ x₀) q

/-- **SVD form** (LSRN): for $\mathbf{S}\mathbf{A} = \mathbf{U}\mathbf{\Sigma}\mathbf{V}^{\mathsf{H}}$
with square $\mathbf{V}$ and every $\sigma_i > 0$, the iterate is $\mathbf{V}\mathbf{\Sigma}^{-1}$
times CGLS on $\mathbf{A}\mathbf{V}\mathbf{\Sigma}^{-1}$ from $\mathbf{\Sigma}\mathbf{V}^{\mathsf{H}}\mathbf{x}_0$
($\mathbf{S}\mathbf{A}\mathbf{V}\mathbf{\Sigma}^{-1} = \mathbf{U}$). [MengSaundersMahoney2014, §3, to verify]. -/
theorem IsSVD.sketchAndPrecondition_eq_mulVec_cgIterate {U : Matrix k n 𝕜} {σ : n → ℝ}
    {V : Matrix n n 𝕜} (hSVD : IsSVD (S * A) U σ V) (hσ : ∀ i, 0 < σ i) (y : m → 𝕜) (q : ℕ) :
    sketchAndPrecondition A S y x₀ q =
      (V * Matrix.diagonal fun i => ((σ i)⁻¹ : 𝕜)) *ᵥ
        cgIterate ((A * (V * Matrix.diagonal fun i => ((σ i)⁻¹ : 𝕜)))ᴴ *
            (A * (V * Matrix.diagonal fun i => ((σ i)⁻¹ : 𝕜))))
          ((A * (V * Matrix.diagonal fun i => ((σ i)⁻¹ : 𝕜)))ᴴ *ᵥ y)
          ((Matrix.diagonal fun i => ((σ i : ℝ) : 𝕜)) *ᵥ (Vᴴ *ᵥ x₀)) q

/-- **The preconditioned Hestenes–Stiefel recurrence computes it**, when $\mathbf{S}\mathbf{A}$ has
full column rank (which implies that $\mathbf{A}$ does).
Result: sketch-and-precondition-realisation -/
theorem pcgState_x_eq_sketchAndPrecondition {S : Matrix k m 𝕜} {A : Matrix m n 𝕜}
    (hSA : Function.Injective (S * A).mulVec) (y : m → 𝕜) (x₀ : n → 𝕜) (q : ℕ) :
    (pcgState (Aᴴ * A) (pinv ((S * A)ᴴ * (S * A))) (Aᴴ *ᵥ y) x₀ q).x =
      sketchAndPrecondition A S y x₀ q

-- Regression/IterativeSketching.lean
/-- QR step: $\mathbf{x}_{q+1} = \mathbf{x}_q + \omega\mathbf{R}^{-1}\mathbf{R}^{-\mathsf{H}}
\mathbf{A}^{\mathsf{H}}(\mathbf{y} - \mathbf{A}\mathbf{x}_q)$ [Epperly2024, Algorithm 2]. -/
theorem IsQR.iterativeSketching_succ [LinearOrder n] {Q : Matrix k n 𝕜} {R : Matrix n n 𝕜}
    (hQR : IsQR (S * A) Q R) (hR : IsUnit R) (ω : ℝ) (y : m → 𝕜) (x₀ : n → 𝕜) (q : ℕ) :
    iterativeSketching A S ω y x₀ (q + 1) = iterativeSketching A S ω y x₀ q +
      ω • (R⁻¹ *ᵥ ((R⁻¹)ᴴ *ᵥ (Aᴴ *ᵥ (y - A *ᵥ iterativeSketching A S ω y x₀ q))))

/-- SVD step: $\mathbf{x}_{q+1} = \mathbf{x}_q + \omega\mathbf{V}\mathbf{\Sigma}^{-2}\mathbf{V}^{\mathsf{H}}
\mathbf{A}^{\mathsf{H}}(\mathbf{y} - \mathbf{A}\mathbf{x}_q)$. -/
theorem IsSVD.iterativeSketching_succ {U : Matrix k n 𝕜} {σ : n → ℝ} {V : Matrix n n 𝕜}
    (hSVD : IsSVD (S * A) U σ V) (hσ : ∀ i, 0 < σ i) (ω : ℝ) (y : m → 𝕜) (x₀ : n → 𝕜)
    (q : ℕ) :
    iterativeSketching A S ω y x₀ (q + 1) = iterativeSketching A S ω y x₀ q +
      ω • ((V * Matrix.diagonal (fun i => (((σ i) ^ 2)⁻¹ : 𝕜)) * Vᴴ) *ᵥ
        (Aᴴ *ᵥ (y - A *ᵥ iterativeSketching A S ω y x₀ q)))
```

## 4. Deterministic headline statements

Shared context: `S : Matrix k m 𝕜`, `A : Matrix m n 𝕜`, `y : m → 𝕜`, `xs x₀ : n → 𝕜`,
`a b ε : ℝ`, with `[DecidableEq m]` where `rangeProjector` appears.
* Errors are the energy error `‖WithLp.toLp 2 (A *ᵥ (xs - x))‖ ^ 2` (equal to the excess squared
  residual), the residual `‖WithLp.toLp 2 (y - A *ᵥ x)‖ ^ 2` against
  `‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2`, and the forward error through
  `singularValues A j`, $j + 1 = \lvert n\rvert$.
* Rates are inline (§5.2 rule 2: small constants the proof reaches). There are no new named bounds.

In the docstrings, $\mathbf{G}$ is written out once per docstring and
$\mathrm{OPT}$ is written $\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{y}\|$, so each docstring
stands alone.

### 4.1 Krylov: Richardson (square instance)

```lean
/-- **Preconditioned Richardson converges at the rate of the spectrum of $\mathbf{M}\mathbf{A}$**:
for positive definite $\mathbf{A}$ and $\mathbf{M}$ with the real spectrum of $\mathbf{M}\mathbf{A}$
in $[a, a']$ and $\mathbf{A}\mathbf{x}_\star = \mathbf{b}$,
$$\|\mathbf{x}_\star - \mathsf{richardsonIterate}(\mathbf{A}, \mathbf{M}, \mathbf{b}, \mathbf{x}_0, q)\|_{\mathbf{A}}^2
\le \bigl(\max(\lvert 1 - a\rvert, \lvert 1 - a'\rvert)\bigr)^{2q}\,\|\mathbf{x}_\star - \mathbf{x}_0\|_{\mathbf{A}}^2 \,,$$
the $\mathbf{A}$-norm squared written $\operatorname{Re}(\mathbf{z}^{\mathsf{H}}\mathbf{A}\mathbf{z})$.
[Saad2003, §4.2]; [Greenbaum1997, §2.1]; locators to verify; there unpreconditioned.
Result: richardson-iteration -/
theorem _root_.Matrix.PosDef.re_quadForm_sub_richardsonIterate_le {A M : Matrix n n 𝕜}
    (hA : A.PosDef) (hM : M.PosDef) {a a' : ℝ} (hs : spectrum ℝ (M * A) ⊆ Set.Icc a a')
    {b xs : n → 𝕜} (hxs : A *ᵥ xs = b) (x₀ : n → 𝕜) (q : ℕ) :
    RCLike.re (quadForm A (xs - richardsonIterate A M b x₀ q)) ≤
      (max |1 - a| |1 - a'|) ^ (2 * q) * RCLike.re (quadForm A (xs - x₀))

/-- **The optimal step**: for positive definite $\mathbf{A}$, $\mathbf{M}$ with the spectrum of
$\mathbf{M}\mathbf{A}$ in $[a, a']$, $0 < a \le a'$, and $\mathbf{A}\mathbf{x}_\star = \mathbf{b}$,
Richardson with $\frac{2}{a + a'}\mathbf{M}$ satisfies
$$\|\mathbf{x}_\star - \mathbf{x}_q\|_{\mathbf{A}}^2 \le
\Bigl(\frac{a' - a}{a' + a}\Bigr)^{2q}\|\mathbf{x}_\star - \mathbf{x}_0\|_{\mathbf{A}}^2 .$$
[Saad2003, §4.2.1]; locator to verify. -/
theorem _root_.Matrix.PosDef.re_quadForm_sub_richardsonIterate_smul_le {A M : Matrix n n 𝕜}
    (hA : A.PosDef) (hM : M.PosDef) {a a' : ℝ} (ha : 0 < a) (haa : a ≤ a')
    (hs : spectrum ℝ (M * A) ⊆ Set.Icc a a') {b xs : n → 𝕜} (hxs : A *ᵥ xs = b) (x₀ : n → 𝕜)
    (q : ℕ) :
    RCLike.re (quadForm A (xs - richardsonIterate A ((2 / (a + a')) • M) b x₀ q)) ≤
      ((a' - a) / (a' + a)) ^ (2 * q) * RCLike.re (quadForm A (xs - x₀))

/-- **PCG is at least as good as Richardson** with the same preconditioner: for positive definite
$\mathbf{A}$, any $\mathbf{M}$ and $\mathbf{A}\mathbf{x}_\star = \mathbf{b}$,
$\|\mathbf{x}_\star - \mathsf{pcgIterate}(\mathbf{A}, \mathbf{M}, \mathbf{b}, \mathbf{x}_0, q)\|_{\mathbf{A}}
\le \|\mathbf{x}_\star - \mathsf{richardsonIterate}(\mathbf{A}, \mathbf{M}, \mathbf{b}, \mathbf{x}_0, q)\|_{\mathbf{A}}$,
squared. -/
theorem _root_.Matrix.PosDef.re_quadForm_sub_pcgIterate_le_re_quadForm_sub_richardsonIterate
    {A : Matrix n n 𝕜} (hA : A.PosDef) (M : Matrix n n 𝕜) {b xs : n → 𝕜} (hxs : A *ᵥ xs = b)
    (x₀ : n → 𝕜) (q : ℕ) :
    RCLike.re (quadForm A (xs - pcgIterate A M b x₀ q)) ≤
      RCLike.re (quadForm A (xs - richardsonIterate A M b x₀ q))
```

### 4.2 Spectral equivalence (added to `Regression/Embedding.lean`)

```lean
/-- A subspace embedding of the range of a matrix of full column rank with a positive lower
constant $a$ has a positive upper constant $b$, when there is a column. The helper used by every
bound of §§4.3–4.4, extracted from the proof of
`IsSubspaceEmbedding.pseudoConditionNumber_mul_sq_le`. -/
theorem IsSubspaceEmbedding.pos_right_of_injective [Nonempty n] (h : IsSubspaceEmbedding S A a b)
    (ha : 0 < a) (hA : Function.Injective A.mulVec) : 0 < b

/-- **Sketch-and-precondition, spectral form**: if $\mathbf{S}$ embeds $\operatorname{range}\mathbf{A}$
with constants $a > 0$, $b$ and $\mathbf{A}$ has full column rank, the real spectrum of
$((\mathbf{S}\mathbf{A})^{\mathsf{H}}\mathbf{S}\mathbf{A})^{+}\mathbf{A}^{\mathsf{H}}\mathbf{A}$ lies
in $[b^{-1}, a^{-1}]$. [RokhlinTygert2008]; [Epperly2024, Fact 3], there as singular values of
$\mathbf{A}\mathbf{R}^{-1}$ in the unsquared convention. -/
theorem IsSubspaceEmbedding.spectrum_pinv_mul_subset_Icc (h : IsSubspaceEmbedding S A a b)
    (ha : 0 < a) (hA : Function.Injective A.mulVec) :
    spectrum ℝ (pinv ((S * A)ᴴ * (S * A)) * (Aᴴ * A)) ⊆ Set.Icc b⁻¹ a⁻¹
```

### 4.3 Sketch-and-precondition (`Regression/SketchAndPrecondition.lean`)

Names follow the CG/PCG precedent: the general Chebyshev-type bound carries `four_mul_pow`, and an
$\varepsilon$ form is distinguished by its hypothesis, `_of_one_sub_one_add`.

```lean
/-- **Sketch-and-precondition converges geometrically**: if $\mathbf{S}$ is a subspace embedding of
$\operatorname{range}\mathbf{A}$ with constants $a > 0$, $b$ (squared norms), $\mathbf{A}$ has full
column rank and $\mathbf{x}_\star$ is a least-squares solution of
$\mathbf{A}\mathbf{x} \approx \mathbf{y}$, then for every start $\mathbf{x}_0$ and every $q$
$$\|\mathbf{A}(\mathbf{x}_\star - \mathsf{sketchAndPrecondition}(\mathbf{A}, \mathbf{S}, \mathbf{y}, \mathbf{x}_0, q))\|^2
\le 4\Bigl(\frac{\sqrt{b/a} - 1}{\sqrt{b/a} + 1}\Bigr)^{2q}\|\mathbf{A}(\mathbf{x}_\star - \mathbf{x}_0)\|^2 .$$
In the unsquared distortion $\eta$ of Epperly and EMN ($a = (1 - \eta)^2$, $b = (1 + \eta)^2$) the
rate is exactly $\eta$. [RokhlinTygert2008]; [MartinssonTropp2020, §10.5]; [Epperly2024, Algorithm 1].
Result: sketch-and-precondition-convergence -/
theorem IsSubspaceEmbedding.norm_mulVec_sub_sketchAndPrecondition_sq_le_four_mul_pow
    (h : IsSubspaceEmbedding S A a b) (ha : 0 < a) (hA : Function.Injective A.mulVec)
    (hxs : IsLeastSquaresSolution A y xs) (x₀ : n → 𝕜) (q : ℕ) :
    ‖WithLp.toLp 2 (A *ᵥ (xs - sketchAndPrecondition A S y x₀ q))‖ ^ 2 ≤
      4 * ((√(b / a) - 1) / (√(b / a) + 1)) ^ (2 * q) * ‖WithLp.toLp 2 (A *ᵥ (xs - x₀))‖ ^ 2

/-- **Sketch-and-precondition, $\varepsilon$ form**: if $\mathbf{S}$ is a subspace embedding of
$\operatorname{range}\mathbf{A}$ with constants $1 \mp \varepsilon$ (squared norms),
$0 < \varepsilon < 1$, $\mathbf{A}$ has full column rank and $\mathbf{x}_\star$ is a least-squares
solution, then
$$\|\mathbf{A}(\mathbf{x}_\star - \mathsf{sketchAndPrecondition}(\mathbf{A}, \mathbf{S}, \mathbf{y}, \mathbf{x}_0, q))\|^2
\le 4\varepsilon^{2q}\|\mathbf{A}(\mathbf{x}_\star - \mathbf{x}_0)\|^2 .$$
The exact rate is $\varepsilon/(1 + \sqrt{1 - \varepsilon^2}) \le \varepsilon$. Here $\varepsilon$
is the squared-norm distortion, not Epperly's unsquared $\eta$ (for which the general theorem gives
rate $\eta$). -/
theorem IsSubspaceEmbedding.norm_mulVec_sub_sketchAndPrecondition_sq_le_four_mul_pow_of_one_sub_one_add
    (h : IsSubspaceEmbedding S A (1 - ε) (1 + ε)) (hε : 0 < ε) (hε1 : ε < 1)
    (hA : Function.Injective A.mulVec) (hxs : IsLeastSquaresSolution A y xs) (x₀ : n → 𝕜)
    (q : ℕ) :
    ‖WithLp.toLp 2 (A *ᵥ (xs - sketchAndPrecondition A S y x₀ q))‖ ^ 2 ≤
      4 * ε ^ (2 * q) * ‖WithLp.toLp 2 (A *ᵥ (xs - x₀))‖ ^ 2

/-- **Sketch-and-precondition from the sketch-and-solve start**: if $\mathbf{S}$ is a subspace
embedding with constants $a > 0$, $b$ (squared norms) of a subspace $\operatorname{range}\mathbf{U}$
containing $\operatorname{range}\mathbf{A}$ and $\mathbf{y}$, $\mathbf{A}$ has full column rank and
$\mathbf{x}_0$ is any minimizer of $\|\mathbf{S}(\mathbf{A}\mathbf{x} - \mathbf{y})\|$, then
$$\|\mathbf{y} - \mathbf{A}\,\mathsf{sketchAndPrecondition}(\mathbf{A}, \mathbf{S}, \mathbf{y}, \mathbf{x}_0, q)\|^2
\le \Bigl(1 + 4\Bigl(\frac{b}{a} - 1\Bigr)\Bigl(\frac{\sqrt{b/a} - 1}{\sqrt{b/a} + 1}\Bigr)^{2q}\Bigr)
\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{y}\|^2 ,$$
the last factor being the optimal squared residual. In Epperly's unsquared $\eta$
($a = (1 - \eta)^2$, $b = (1 + \eta)^2$) the factor is
$1 + 16\eta^{2q+1}/(1 - \eta)^2$. The bound is squared; [MartinssonTropp2020, §10.5] states an
unsquared $(1 + \varepsilon)$ after $j \sim \log(1/\varepsilon)$ steps. [Epperly2024, Algorithm 1
and Fact 4].
Result: sketch-and-precondition-ls -/
theorem IsSubspaceEmbedding.norm_sub_mulVec_sketchAndPrecondition_sq_le [Fintype r]
    {U : Matrix m r 𝕜} (h : IsSubspaceEmbedding S U a b) (ha : 0 < a)
    (hAU : LinearMap.range A.mulVecLin ≤ LinearMap.range U.mulVecLin)
    (hy : y ∈ LinearMap.range U.mulVecLin) (hA : Function.Injective A.mulVec)
    (hx₀ : IsLeastSquaresSolution (S * A) (S *ᵥ y) x₀) (q : ℕ) :
    ‖WithLp.toLp 2 (y - A *ᵥ sketchAndPrecondition A S y x₀ q)‖ ^ 2 ≤
      (1 + 4 * (b / a - 1) * ((√(b / a) - 1) / (√(b / a) + 1)) ^ (2 * q)) *
        ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2

/-- **Sketch-and-precondition from the sketch-and-solve start, $\varepsilon$ form**: if
$\mathbf{S}$ is a subspace embedding of $\operatorname{range}[\mathbf{A}\ \mathbf{y}]$ with constants
$1 \mp \varepsilon$ (squared norms), $0 < \varepsilon < 1$, $\mathbf{A}$ has full column rank and
$\mathbf{x}_0$ minimizes $\|\mathbf{S}(\mathbf{A}\mathbf{x} - \mathbf{y})\|$, then
$$\|\mathbf{y} - \mathbf{A}\,\mathsf{sketchAndPrecondition}(\mathbf{A}, \mathbf{S}, \mathbf{y}, \mathbf{x}_0, q)\|^2
\le \Bigl(1 + \frac{8\varepsilon^{2q+1}}{1 - \varepsilon}\Bigr)\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{y}\|^2 .$$
-/
theorem IsSubspaceEmbedding.norm_sub_mulVec_sketchAndPrecondition_sq_le_of_one_sub_one_add
    (h : IsSubspaceEmbedding S (Matrix.fromCols A (Matrix.replicateCol Unit y)) (1 - ε) (1 + ε))
    (hε : 0 < ε) (hε1 : ε < 1) (hA : Function.Injective A.mulVec)
    (hx₀ : IsLeastSquaresSolution (S * A) (S *ᵥ y) x₀) (q : ℕ) :
    ‖WithLp.toLp 2 (y - A *ᵥ sketchAndPrecondition A S y x₀ q)‖ ^ 2 ≤
      (1 + 8 * ε ^ (2 * q + 1) / (1 - ε)) * ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2

/-- **Iteration count** (PORT_KRYLOV O6: deterministic counts get explicit corollaries only): if
$\mathbf{S}$ embeds $\operatorname{range}[\mathbf{A}\ \mathbf{y}]$ with constants $1 \mp \varepsilon$,
$0 < \varepsilon \le 1/2$, $\mathbf{A}$ has full column rank, $\mathbf{x}_0$ minimizes
$\|\mathbf{S}(\mathbf{A}\mathbf{x} - \mathbf{y})\|$ and $16\varepsilon^{2q+1} \le \tau$, then
$$\|\mathbf{y} - \mathbf{A}\,\mathsf{sketchAndPrecondition}(\mathbf{A}, \mathbf{S}, \mathbf{y}, \mathbf{x}_0, q)\|^2
\le (1 + \tau)\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{y}\|^2 .$$
At $\varepsilon = 1/2$, $q \ge \log(8/\tau)/\log 4$ steps suffice. -/
theorem IsSubspaceEmbedding.norm_sub_mulVec_sketchAndPrecondition_sq_le_one_add_mul
    (h : IsSubspaceEmbedding S (Matrix.fromCols A (Matrix.replicateCol Unit y)) (1 - ε) (1 + ε))
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (hA : Function.Injective A.mulVec)
    (hx₀ : IsLeastSquaresSolution (S * A) (S *ᵥ y) x₀) {q : ℕ} {τ : ℝ}
    (hq : 16 * ε ^ (2 * q + 1) ≤ τ) :
    ‖WithLp.toLp 2 (y - A *ᵥ sketchAndPrecondition A S y x₀ q)‖ ^ 2 ≤
      (1 + τ) * ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2

/-- **Forward error from the sketch-and-solve start**: under the hypotheses of
`IsSubspaceEmbedding.norm_sub_mulVec_sketchAndPrecondition_sq_le`, with $\mathbf{x}_\star$ the
least-squares solution and $\sigma_{\min}(\mathbf{A}) = \sigma_j(\mathbf{A})$, $j + 1 = \lvert n\rvert$,
$$\sigma_{\min}(\mathbf{A})^2\,\|\mathbf{x}_\star - \mathsf{sketchAndPrecondition}(\mathbf{A}, \mathbf{S}, \mathbf{y}, \mathbf{x}_0, q)\|^2
\le 4\Bigl(\frac{b}{a} - 1\Bigr)\Bigl(\frac{\sqrt{b/a} - 1}{\sqrt{b/a} + 1}\Bigr)^{2q}
\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{y}\|^2 .$$
Epperly's forward-error form ($\|\mathbf{x} - \mathbf{x}_i\| \lesssim \kappa\,\|\mathbf{r}(\mathbf{x})\|/\|\mathbf{A}\|$),
with no division. [Epperly2024, Theorem 5 form]. -/
theorem IsSubspaceEmbedding.singularValues_sq_mul_norm_sub_sketchAndPrecondition_sq_le
    [Fintype r] {U : Matrix m r 𝕜} (h : IsSubspaceEmbedding S U a b) (ha : 0 < a)
    (hAU : LinearMap.range A.mulVecLin ≤ LinearMap.range U.mulVecLin)
    (hy : y ∈ LinearMap.range U.mulVecLin) (hA : Function.Injective A.mulVec)
    (hxs : IsLeastSquaresSolution A y xs)
    (hx₀ : IsLeastSquaresSolution (S * A) (S *ᵥ y) x₀) {j : ℕ} (hj : j + 1 = Fintype.card n)
    (q : ℕ) :
    singularValues A j ^ 2 * ‖WithLp.toLp 2 (xs - sketchAndPrecondition A S y x₀ q)‖ ^ 2 ≤
      4 * (b / a - 1) * ((√(b / a) - 1) / (√(b / a) + 1)) ^ (2 * q) *
        ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2
```

`IsSubspaceEmbedding.pseudoConditionNumber_mul_sq_le` keeps `Result: sketch-and-precondition`. The
new ids are `sketch-and-precondition-convergence`, `sketch-and-precondition-ls`,
`sketch-and-precondition-realisation`, `iterative-sketching-convergence` and `richardson-iteration`.

### 4.4 Iterative sketching (`Regression/IterativeSketching.lean`)

```lean
/-- **Iterative sketching converges geometrically**: if $\mathbf{S}$ is a subspace embedding of
$\operatorname{range}\mathbf{A}$ with constants $a > 0$, $b$ (squared norms), $\mathbf{A}$ has full
column rank, $\mathbf{x}_\star$ is a least-squares solution and $\omega > 0$, then
$$\|\mathbf{A}(\mathbf{x}_\star - \mathsf{iterativeSketching}(\mathbf{A}, \mathbf{S}, \omega, \mathbf{y}, \mathbf{x}_0, q))\|^2
\le \bigl(\max(\lvert 1 - \omega/b\rvert, \lvert 1 - \omega/a\rvert)\bigr)^{2q}\|\mathbf{A}(\mathbf{x}_\star - \mathbf{x}_0)\|^2 .$$
In Epperly's unsquared $\eta$ ($a = (1 - \eta)^2$, $b = (1 + \eta)^2$) the rate at $\omega = 1$
is his $g_{\mathrm{IS}} = (2 - \eta)\eta/(1 - \eta)^2$, and at
$\omega = (1 - \eta^2)^2/(1 + \eta^2)$ it is $g_{\mathrm{damp}} = 2\eta/(1 + \eta^2)$.
[Epperly2024, Theorem 5 and Theorem 10]; there through $\|\mathbf{S}\mathbf{A}\cdot\|$ with the
prefactor $(1 + \eta)/(1 - \eta)$, here in the energy norm without one.
Result: iterative-sketching-convergence -/
theorem IsSubspaceEmbedding.norm_mulVec_sub_iterativeSketching_sq_le
    (h : IsSubspaceEmbedding S A a b) (ha : 0 < a) (hA : Function.Injective A.mulVec)
    {ω : ℝ} (hω : 0 < ω) (hxs : IsLeastSquaresSolution A y xs) (x₀ : n → 𝕜) (q : ℕ) :
    ‖WithLp.toLp 2 (A *ᵥ (xs - iterativeSketching A S ω y x₀ q))‖ ^ 2 ≤
      (max |1 - ω / b| |1 - ω / a|) ^ (2 * q) * ‖WithLp.toLp 2 (A *ᵥ (xs - x₀))‖ ^ 2

/-- **Undamped iterative sketching, $\varepsilon$ form**: for a subspace embedding of
$\operatorname{range}\mathbf{A}$ with constants $1 \mp \varepsilon$ (squared norms),
$0 < \varepsilon < 1$, $\mathbf{A}$ of full column rank and a least-squares solution $\mathbf{x}_\star$,
$$\|\mathbf{A}(\mathbf{x}_\star - \mathsf{iterativeSketching}(\mathbf{A}, \mathbf{S}, 1, \mathbf{y}, \mathbf{x}_0, q))\|^2
\le \Bigl(\frac{\varepsilon}{1 - \varepsilon}\Bigr)^{2q}\|\mathbf{A}(\mathbf{x}_\star - \mathbf{x}_0)\|^2 ,$$
a contraction for $\varepsilon < 1/2$. -/
theorem IsSubspaceEmbedding.norm_mulVec_sub_iterativeSketching_one_sq_le
    (h : IsSubspaceEmbedding S A (1 - ε) (1 + ε)) (hε : 0 < ε) (hε1 : ε < 1)
    (hA : Function.Injective A.mulVec) (hxs : IsLeastSquaresSolution A y xs) (x₀ : n → 𝕜)
    (q : ℕ) :
    ‖WithLp.toLp 2 (A *ᵥ (xs - iterativeSketching A S 1 y x₀ q))‖ ^ 2 ≤
      (ε / (1 - ε)) ^ (2 * q) * ‖WithLp.toLp 2 (A *ᵥ (xs - x₀))‖ ^ 2

/-- **Optimally damped iterative sketching, $\varepsilon$ form**: under the same hypotheses, with
step $\omega = 1 - \varepsilon^2$,
$$\|\mathbf{A}(\mathbf{x}_\star - \mathsf{iterativeSketching}(\mathbf{A}, \mathbf{S}, 1 - \varepsilon^2, \mathbf{y}, \mathbf{x}_0, q))\|^2
\le \varepsilon^{2q}\|\mathbf{A}(\mathbf{x}_\star - \mathbf{x}_0)\|^2 ,$$
a contraction for every $\varepsilon < 1$. Sketch-and-precondition is never worse
(`Matrix.PosDef.re_quadForm_sub_pcgIterate_le_re_quadForm_sub_richardsonIterate`). -/
theorem IsSubspaceEmbedding.norm_mulVec_sub_iterativeSketching_one_sub_sq_sq_le
    (h : IsSubspaceEmbedding S A (1 - ε) (1 + ε)) (hε : 0 < ε) (hε1 : ε < 1)
    (hA : Function.Injective A.mulVec) (hxs : IsLeastSquaresSolution A y xs) (x₀ : n → 𝕜)
    (q : ℕ) :
    ‖WithLp.toLp 2 (A *ᵥ (xs - iterativeSketching A S (1 - ε ^ 2) y x₀ q))‖ ^ 2 ≤
      ε ^ (2 * q) * ‖WithLp.toLp 2 (A *ᵥ (xs - x₀))‖ ^ 2

/-- **Damped iterative sketching from the sketch-and-solve start**: if $\mathbf{S}$ embeds
$\operatorname{range}[\mathbf{A}\ \mathbf{y}]$ with constants $1 \mp \varepsilon$ (squared norms),
$0 < \varepsilon < 1$, $\mathbf{A}$ has full column rank and $\mathbf{x}_0$ minimizes
$\|\mathbf{S}(\mathbf{A}\mathbf{x} - \mathbf{y})\|$, then
$$\|\mathbf{y} - \mathbf{A}\,\mathsf{iterativeSketching}(\mathbf{A}, \mathbf{S}, 1 - \varepsilon^2, \mathbf{y}, \mathbf{x}_0, q)\|^2
\le \Bigl(1 + \frac{2\varepsilon^{2q+1}}{1 - \varepsilon}\Bigr)\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{y}\|^2 .$$
[Epperly2024, Theorem 10 (B.4)], there unsquared with a prefactor. -/
theorem IsSubspaceEmbedding.norm_sub_mulVec_iterativeSketching_one_sub_sq_sq_le
    (h : IsSubspaceEmbedding S (Matrix.fromCols A (Matrix.replicateCol Unit y)) (1 - ε) (1 + ε))
    (hε : 0 < ε) (hε1 : ε < 1) (hA : Function.Injective A.mulVec)
    (hx₀ : IsLeastSquaresSolution (S * A) (S *ᵥ y) x₀) (q : ℕ) :
    ‖WithLp.toLp 2 (y - A *ᵥ iterativeSketching A S (1 - ε ^ 2) y x₀ q)‖ ^ 2 ≤
      (1 + 2 * ε ^ (2 * q + 1) / (1 - ε)) * ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2
```

The damped rate $\varepsilon$ matches the bound proved for sketch-and-precondition, whose exact
rate $\varepsilon/(1 + \sqrt{1 - \varepsilon^2})$ is smaller but which carries the factor 4.
Momentum is deferred (§7).

## 5. Probabilistic statements

### 5.1 Generic tails (end of each algorithm file)

In the namespace of the interface, so the prefix is `measure_` (CONTRIBUTING §4; precedent
`HasSubspaceInjection.measure_norm_sub_mulVec_sq_gt_le`). The warm start is a hypothesis that holds
almost surely, as in that precedent. Measurability is not needed: each proof is `measure_mono_ae`
then `measureReal_mono`, onto the failure event of the embedding.

```lean
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Sketch-and-precondition with a random embedding, any start**: if $\mathbf{S}$ is a subspace
embedding of $\operatorname{range}\mathbf{A}$ with constants $a > 0$, $b$ (squared norms) except
with probability $\delta$, $\mathbf{A}$ has full column rank and $\mathbf{x}_\star$ is a
least-squares solution, then for a fixed start $\mathbf{x}_0$
$$\mathbb{P}\Bigl[\|\mathbf{A}(\mathbf{x}_\star - \mathsf{sketchAndPrecondition}(\mathbf{A}, \mathbf{S}, \mathbf{y}, \mathbf{x}_0, q))\|^2
> 4\Bigl(\frac{\sqrt{b/a} - 1}{\sqrt{b/a} + 1}\Bigr)^{2q}\|\mathbf{A}(\mathbf{x}_\star - \mathbf{x}_0)\|^2\Bigr] \le \delta .$$
-/
theorem HasSubspaceEmbedding.measure_norm_mulVec_sub_sketchAndPrecondition_sq_gt_le
    [IsFiniteMeasure μ] {S : Ω → Matrix k m 𝕜} (h : HasSubspaceEmbedding S A a b δ μ)
    (ha : 0 < a) (hA : Function.Injective A.mulVec) {xs : n → 𝕜}
    (hxs : IsLeastSquaresSolution A y xs) (x₀ : n → 𝕜) (q : ℕ) :
    μ.real {ω | 4 * ((√(b / a) - 1) / (√(b / a) + 1)) ^ (2 * q) *
        ‖WithLp.toLp 2 (A *ᵥ (xs - x₀))‖ ^ 2 <
      ‖WithLp.toLp 2 (A *ᵥ (xs - sketchAndPrecondition A (S ω) y x₀ q))‖ ^ 2} ≤ δ

/-- **Sketch-and-precondition with a random embedding, sketch-and-solve start**: if $\mathbf{S}$ is
a subspace embedding of $\operatorname{range}[\mathbf{A}\ \mathbf{y}]$ with constants $a > 0$, $b$
(squared norms) except with probability $\delta$, $\mathbf{A}$ has full column rank and almost
surely $\mathbf{x}_0$ minimizes $\|\mathbf{S}(\mathbf{A}\mathbf{x} - \mathbf{y})\|$, then
$$\mathbb{P}\Bigl[\|\mathbf{y} - \mathbf{A}\,\mathsf{sketchAndPrecondition}(\mathbf{A}, \mathbf{S}, \mathbf{y}, \mathbf{x}_0, q)\|^2 >
\Bigl(1 + 4\Bigl(\frac{b}{a} - 1\Bigr)\Bigl(\frac{\sqrt{b/a} - 1}{\sqrt{b/a} + 1}\Bigr)^{2q}\Bigr)
\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{y}\|^2\Bigr] \le \delta .$$
Squared residuals; MT's $(1 + \varepsilon)$ is unsquared.
Result: sketch-and-precondition-ls -/
theorem HasSubspaceEmbedding.measure_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le
    [DecidableEq m] [IsFiniteMeasure μ] {S : Ω → Matrix k m 𝕜}
    (h : HasSubspaceEmbedding S (Matrix.fromCols A (Matrix.replicateCol Unit y)) a b δ μ)
    (ha : 0 < a) (hA : Function.Injective A.mulVec) {x₀ : Ω → n → 𝕜}
    (hx₀ : ∀ᵐ ω ∂μ, IsLeastSquaresSolution (S ω * A) (S ω *ᵥ y) (x₀ ω)) (q : ℕ) :
    μ.real {ω | (1 + 4 * (b / a - 1) * ((√(b / a) - 1) / (√(b / a) + 1)) ^ (2 * q)) *
        ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2 <
      ‖WithLp.toLp 2 (y - A *ᵥ sketchAndPrecondition A (S ω) y (x₀ ω) q)‖ ^ 2} ≤ δ

/-- **Iterative sketching with a random embedding, any start**: under the embedding hypothesis of
the cold-start tail above and $\omega > 0$,
$$\mathbb{P}\Bigl[\|\mathbf{A}(\mathbf{x}_\star - \mathsf{iterativeSketching}(\mathbf{A}, \mathbf{S}, \omega, \mathbf{y}, \mathbf{x}_0, q))\|^2 >
\bigl(\max(\lvert 1 - \omega/b\rvert, \lvert 1 - \omega/a\rvert)\bigr)^{2q}\|\mathbf{A}(\mathbf{x}_\star - \mathbf{x}_0)\|^2\Bigr] \le \delta .$$
(The docstring restates the hypotheses in full.) -/
theorem HasSubspaceEmbedding.measure_norm_mulVec_sub_iterativeSketching_sq_gt_le
    [IsFiniteMeasure μ] {S : Ω → Matrix k m 𝕜} (h : HasSubspaceEmbedding S A a b δ μ)
    (ha : 0 < a) (hA : Function.Injective A.mulVec) {ω' : ℝ} (hω : 0 < ω') {xs : n → 𝕜}
    (hxs : IsLeastSquaresSolution A y xs) (x₀ : n → 𝕜) (q : ℕ) :
    μ.real {ω | (max |1 - ω' / b| |1 - ω' / a|) ^ (2 * q) *
        ‖WithLp.toLp 2 (A *ᵥ (xs - x₀))‖ ^ 2 <
      ‖WithLp.toLp 2 (A *ᵥ (xs - iterativeSketching A (S ω) ω' y x₀ q))‖ ^ 2} ≤ δ

/-- **Damped iterative sketching with a random embedding, sketch-and-solve start**: if $\mathbf{S}$
embeds $\operatorname{range}[\mathbf{A}\ \mathbf{y}]$ with constants $1 \mp \varepsilon$,
$0 < \varepsilon < 1$, except with probability $\delta$, $\mathbf{A}$ has full column rank and
almost surely $\mathbf{x}_0$ is a sketched minimizer, then
$$\mathbb{P}\Bigl[\|\mathbf{y} - \mathbf{A}\,\mathsf{iterativeSketching}(\mathbf{A}, \mathbf{S}, 1 - \varepsilon^2, \mathbf{y}, \mathbf{x}_0, q)\|^2 >
\Bigl(1 + \frac{2\varepsilon^{2q+1}}{1 - \varepsilon}\Bigr)\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{y}\|^2\Bigr] \le \delta .$$
-/
theorem HasSubspaceEmbedding.measure_norm_sub_mulVec_iterativeSketching_one_sub_sq_sq_gt_le
    [DecidableEq m] [IsFiniteMeasure μ] {S : Ω → Matrix k m 𝕜}
    (h : HasSubspaceEmbedding S (Matrix.fromCols A (Matrix.replicateCol Unit y))
      (1 - ε) (1 + ε) δ μ)
    (hε : 0 < ε) (hε1 : ε < 1) (hA : Function.Injective A.mulVec) {x₀ : Ω → n → 𝕜}
    (hx₀ : ∀ᵐ ω ∂μ, IsLeastSquaresSolution (S ω * A) (S ω *ᵥ y) (x₀ ω)) (q : ℕ) :
    μ.real {ω | (1 + 2 * ε ^ (2 * q + 1) / (1 - ε)) *
        ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2 <
      ‖WithLp.toLp 2 (y - A *ᵥ iterativeSketching A (S ω) (1 - ε ^ 2) y (x₀ ω) q)‖ ^ 2} ≤ δ
```

The step variable is `ω'` in the iterative-sketching tail, because `ω` is the sample point.
The skeleton may rename the sample point instead.

### 5.2 Family corollaries (sketch-and-precondition, warm start)

The explicit form leaves the distortion $\varepsilon \le 1/2$ free, so a user can trade sketch size
against iterations, and takes the target $\tau$ through $16\varepsilon^{2q+1} \le \tau$. The family
theorems are root-level, so they keep `measureReal_`. Each explicit theorem carries
`Result: sketch-and-precondition-ls`, as `Regression/Gaussian.lean` does with `sketch-and-solve-ls`.

```lean
/-- **Gaussian sketch-and-precondition**: for a standard Gaussian $\mathbf{G} \in \mathbb{R}^{k \times m}$,
$\mathbf{S} = \lvert k\rvert^{-1/2}\mathbf{G}$, $\mathbf{A}$ of full column rank, $\mathbf{x}_0$
almost surely a minimizer of $\|\mathbf{S}(\mathbf{A}\mathbf{x} - \mathbf{y})\|$,
$0 < \varepsilon \le 1/2$, $\delta > 0$, at least
<!-- value gaussianEmbeddingDim {\lvert n \rvert + 1} \varepsilon \delta -->
$9(\sqrt{\lvert n \rvert + 1} + \sqrt{2\log(2/\delta)})^2/\varepsilon^2$ rows
(`gaussianEmbeddingDim (card n + 1) ε δ`) and $16\varepsilon^{2q+1} \le \tau$,
$$\mathbb{P}\Bigl[\|\mathbf{y} - \mathbf{A}\,\mathsf{sketchAndPrecondition}(\mathbf{A}, \mathbf{S}, \mathbf{y}, \mathbf{x}_0, q)\|^2
> (1 + \tau)\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{y}\|^2\Bigr] \le \delta .$$
Squared residuals, and $\varepsilon$ is the squared-norm distortion. [RokhlinTygert2008];
[MartinssonTropp2020, §10.5], there unsquared with $j \sim \log(1/\varepsilon)$ and no constants.
Asymptotic form: `NLAlib.exists_forall_measureReal_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le_of_hasLaw_gaussianMatrix`.
Result: sketch-and-precondition-ls -/
theorem measureReal_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le_of_hasLaw_gaussianMatrix
    [DecidableEq m] {G : Ω → Matrix k m ℝ} (hG : HasLaw G (gaussianMatrix k m) μ)
    {A : Matrix m n ℝ} (hA : Function.Injective A.mulVec) (y : m → ℝ) {x₀ : Ω → n → ℝ}
    (hx₀ : ∀ᵐ ω ∂μ, IsLeastSquaresSolution ((√(Fintype.card k : ℝ))⁻¹ • G ω * A)
      ((√(Fintype.card k : ℝ))⁻¹ • G ω *ᵥ y) (x₀ ω))
    {ε δ τ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (hδ : 0 < δ)
    (hk : gaussianEmbeddingDim (Fintype.card n + 1) ε δ ≤ Fintype.card k)
    {q : ℕ} (hq : 16 * ε ^ (2 * q + 1) ≤ τ) :
    μ.real {ω | (1 + τ) * ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2 <
      ‖WithLp.toLp 2 (y - A *ᵥ sketchAndPrecondition A ((√(Fintype.card k : ℝ))⁻¹ • G ω) y
        (x₀ ω) q)‖ ^ 2} ≤ δ

/-- **Gaussian sketch-and-precondition from $(\mathbf{S}\mathbf{A})^{+}\mathbf{S}\mathbf{y}$**, the
algorithm as run [Epperly2024, Algorithm 1]: the same bound with the start fixed to the
minimum-norm sketched solution. Two lines through `isLeastSquaresSolution_pinv_mulVec`. Explicit
only: it specialises the start, not the sample size. -/
theorem measureReal_norm_sub_mulVec_sketchAndPrecondition_pinv_mulVec_sq_gt_le_of_hasLaw_gaussianMatrix
    [DecidableEq m] {G : Ω → Matrix k m ℝ} (hG : HasLaw G (gaussianMatrix k m) μ)
    {A : Matrix m n ℝ} (hA : Function.Injective A.mulVec) (y : m → ℝ)
    {ε δ τ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (hδ : 0 < δ)
    (hk : gaussianEmbeddingDim (Fintype.card n + 1) ε δ ≤ Fintype.card k)
    {q : ℕ} (hq : 16 * ε ^ (2 * q + 1) ≤ τ) :
    μ.real {ω | (1 + τ) * ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2 <
      ‖WithLp.toLp 2 (y - A *ᵥ sketchAndPrecondition A ((√(Fintype.card k : ℝ))⁻¹ • G ω) y
        (pinv ((√(Fintype.card k : ℝ))⁻¹ • G ω * A) *ᵥ ((√(Fintype.card k : ℝ))⁻¹ • G ω *ᵥ y))
        q)‖ ^ 2} ≤ δ
```

The other three families change only the law hypothesis, the field and `hk`. Each also gets its
`…_pinv_mulVec_…` start form.

| Family | File | Field | `hk` | Extra hypotheses |
|---|---|---|---|---|
| Gaussian, normalised | `Regression/Gaussian.lean` | ℝ | `gaussianEmbeddingDim (card n + 1) ε δ ≤ card k` | none |
| sub-Gaussian rows, normalised | `Regression/SubGaussian.lean` (new) | ℝ | `subgaussianEmbeddingDim c (card n + 1) ε δ ≤ card k` | `iIndepFun` rows, `IsSubgaussianVector … c`, `IsIsotropic`, `ε ≤ 2 * c` |
| SRHT | `Regression/SRHT.lean` (new) | `RCLike` | `samplingSize (card n + 1) (β * srhtRowBound (card m) (card n + 1) (δ / 2)) ε (δ / 2) ≤ card k` | `IsBoundedOrthonormal F β`, `HasLaw S (srht k F) μ` |
| CountSketch | `Regression/CountSketch.lean` | `RCLike` | `countSketchRows (card n + 1) ε δ ≤ card k` | `[DecidableEq k]`, `HasLaw S (countSketch k m) μ` |

Each docstring shows its size with a value marker (`subgaussianEmbeddingDim`, `samplingSize` and
`srhtRowBound`, `countSketchRows`; all registered in `docs/constants.toml`) and states the whole
bound, as the Gaussian one does.

Sketch-and-precondition is invariant under scaling the sketch; iterative sketching is not. The
corollaries keep the normalised sketch of the embedding theorem. `sketchAndPrecondition_smul_sketch`
needs Krylov-space scaling lemmas that do not exist yet (§7).

### 5.3 Asymptotic forms (CONTRIBUTING §5.2 rule 3)

The distortion is fixed at $\varepsilon = 1/2$; $\tau$ is the accuracy parameter, under
$\varepsilon_0$. One constant bounds both resources:

```lean
/-- **Gaussian sketch-and-precondition, asymptotic form**: $O(\lvert n\rvert + 1 + \log(1/\delta))$
rows and $O(\log(1/\tau))$ iterations suffice for the sketch-and-precondition iterate, from almost
surely a sketched minimizer, with $\mathbf{A}$ of full column rank and the normalised Gaussian
sketch $\lvert k\rvert^{-1/2}\mathbf{G}$, to satisfy
$\|\mathbf{y} - \mathbf{A}\mathbf{x}_q\|^2 \le (1 + \tau)\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{y}\|^2$
except with probability $\delta$, for $\tau$ below an absolute constant and $\delta \le 1/2$; the
constants come before every dimension. Squared residuals.
Asymptotic: NLAlib.measureReal_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le_of_hasLaw_gaussianMatrix -/
theorem exists_forall_measureReal_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω k m n : Type} [MeasurableSpace Ω] [Fintype k] [Fintype m]
      [Fintype n] [DecidableEq m] [DecidableEq n] (μ : Measure Ω) (G : Ω → Matrix k m ℝ)
      (A : Matrix m n ℝ) (y : m → ℝ) (x₀ : Ω → n → ℝ) (τ δ : ℝ) (q : ℕ),
      HasLaw G (gaussianMatrix k m) μ → Function.Injective A.mulVec →
      (∀ᵐ ω ∂μ, IsLeastSquaresSolution ((√(Fintype.card k : ℝ))⁻¹ • G ω * A)
        ((√(Fintype.card k : ℝ))⁻¹ • G ω *ᵥ y) (x₀ ω)) →
      0 < τ → τ ≤ ε₀ → 0 < δ → δ ≤ 1 / 2 →
      C * (Fintype.card n + 1 + Real.log (1 / δ)) ≤ Fintype.card k →
      C * Real.log (1 / τ) ≤ q →
      μ.real {ω | (1 + τ) * ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2 <
        ‖WithLp.toLp 2 (y - A *ᵥ sketchAndPrecondition A ((√(Fintype.card k : ℝ))⁻¹ • G ω) y
          (x₀ ω) q)‖ ^ 2} ≤ δ
```

The sub-Gaussian, SRHT and CountSketch forms differ in their binders and thresholds, given in the
table below. All four were elaborated:
* sub-Gaussian adds `[Nonempty k]` and `(X) (c : ℝ≥0)` with its three row hypotheses;
* SRHT adds `{𝕜} [RCLike 𝕜] (S) (F) (β)` with `IsBoundedOrthonormal F β` and `HasLaw S (srht k F) μ`;
* CountSketch adds `{𝕜} [RCLike 𝕜] [DecidableEq k]` and `HasLaw S (countSketch k m) μ`, and has
  no `δ ≤ 1/2` (review item 8; the library's CountSketch form needs none).

| Family | Rows threshold | $C$ | $\varepsilon_0$ | `δ ≤ 1/2` |
|---|---|---|---|---|
| Gaussian | $C(\lvert n\rvert + 1 + \log(1/\delta))$, from `gaussianEmbeddingDim_le`, $72(d + 4\log(1/\delta))$ at $\varepsilon = 1/2$ | 288 | 1/2 | yes |
| sub-Gaussian | $C c^2(\lvert n\rvert + 1 + \log(1/\delta))$, from `subgaussianEmbeddingDim_le` | 4608 | 1/2 | yes |
| SRHT | $C\beta(\lvert n\rvert + 1 + \log(\lvert m\rvert/\delta))\log((\lvert n\rvert + 1)/\delta)$, from `samplingSize_le` | 288 | 1/2 | yes |
| CountSketch | $C(\lvert n\rvert + 1)^2/\delta$, from `countSketchRows_le` | 8 | 1/2 | no |

The iteration threshold: $16(1/2)^{2q+1} = 8\cdot 4^{-q} \le \tau$ once
$q \ge \log(8/\tau)/\log 4$. For $\tau \le 1/2$, $\log 8 \le 3\log(1/\tau)$, so
$q \ge 3\log(1/\tau)$ suffices. That is within the $C$ of every row; the review checked
$\tau = 1/2, 10^{-1}, 10^{-3}, 10^{-8}$. The constants are the review's checked values from the
existing comparisons.

## 6. Files, placement and imports

| File | New/grows | Content (in order) | Lines | Imports |
|---|---|---|---|---|
| `Krylov/LinearSystems/Richardson.lean` | new | `richardsonIterate` (rectangular); zero/succ; `sub_richardsonIterate_eq`; `richardsonIterate_sub_mem_krylovSpace`; `richardsonIterate_mul_conjTranspose`; the square bounds of §4.1 | ~250 | `Krylov.LinearSystems.PCG` |
| `Matrix/Pseudoinverse/Pinv.lean` | grows | `pinv_conjTranspose_mul_self_eq_mul_conjTranspose` | +25 | none |
| `Regression/Embedding.lean` | grows | `IsSubspaceEmbedding.pos_right_of_injective`, `IsSubspaceEmbedding.spectrum_pinv_mul_subset_Icc` | +40 | `Matrix.Inequalities.Order` |
| `Regression/SketchAndPrecondition.lean` | new | definition; realisations (general, `IsQR`, `IsSVD`, recurrence); §4.3; tails of §5.1 | ~420 | Embedding, PCG, PCGRecurrence, SVD, FixedSubspace |
| `Regression/IterativeSketching.lean` | new | definition; `iterativeSketching_eq`; `IsQR`/`IsSVD` steps; §4.4; tails | ~280 | Embedding, Richardson, SVD, FixedSubspace |
| `Regression/Gaussian.lean` | grows (151) | explicit, `pinv_mulVec` and asymptotic Gaussian forms | +130 | SketchAndPrecondition |
| `Regression/CountSketch.lean` | grows (160) | CountSketch forms | +110 | SketchAndPrecondition, CountSketchEmbedding |
| `Regression/SRHT.lean`, `Regression/SubGaussian.lean` | new | the three forms each | ~140 each | SketchAndPrecondition, SRHT / SubGaussian |

**Placement, for every addition outside the new files:**
* `pinv_conjTranspose_mul_self_eq_mul_conjTranspose` goes to `Matrix/Pseudoinverse/Pinv.lean`,
  beside `pinv_conjTranspose_mul_self`. It is a fact about the pseudoinverse of a Gram matrix,
  with no sketch in it.
* The two `IsSubspaceEmbedding` lemmas go to `Regression/Embedding.lean`, section
  "Sketch-and-precondition". They are the spectral restatement of the Loewner halves already there,
  and the positivity helper that their proof already uses inline.
* The Gaussian and CountSketch forms go to the existing family files. Their topic becomes
  "regression with this sketch", and their module docstrings are retitled. **Flag (uncertain):**
  the alternative is a cross-family block at the end of `SketchAndPrecondition.lean`, which
  `Regression-Rates.md` rejected as a "Rates dump". Recommendation: the family files.
* `richardsonIterate` goes to `Krylov/LinearSystems/Richardson.lean`, not PORT_KRYLOV D12's
  `PolynomialIteration.lean`, because the file holds one recursion, not polynomial methods. The
  commit that creates the file records this as a dated amendment to PORT_KRYLOV D12.

Regression imports Krylov (layer 1) and Sketching (layer 3), and Krylov imports neither, so there
is no cycle. Root imports are regenerated with `mk_all`.

## 7. In this round, and deferred

**In:** §§3–5 as written, including the forward-error corollary (a real one-liner through
`singularValues_last_mul_norm_le`) and the `…_pinv_mulVec` start forms.

**Deferred**, each with its gap:
* **Rates rows.** Maintainer, 2026-10-19: "for sketch and precondition, dont worry about rates now".
* **Cold-start family corollaries**, at $d = \lvert n\rvert$ with energy error $4\varepsilon^{2q}$.
  The explicit forms are short, but CONTRIBUTING §5.2 rule 3 gives each its own `exists_forall_`
  pair, about 4 × 70 lines, so they are not one-liners. A user gets them from the generic cold tail
  with `IsObliviousSubspaceEmbedding.hasSubspaceEmbedding` in two lines.
* **Haar corollary.** `isObliviousSubspaceEmbedding_of_hasLaw_haarFrame` has no
  $1 \mp \varepsilon$ size form, only constants in two tail parameters. A size corollary needs that
  inversion first, in Sketching, so it is not a one-liner.
* **LSQR proper** (Golub–Kahan bidiagonalisation and the LSQR recurrence realising CGLS). The
  library has no bidiagonalisation (grep: none), and CGLS = LSQR in exact arithmetic adds no
  theorem.
* **Momentum / heavy ball** [Epperly2024, Theorem 10 (B.5)] and FOSSILS
  [EpperlyMeierNakatsukasa2024]. This is a two-step recursion analysed through a $2\times 2$ block
  companion matrix with an $(i - 1)\varepsilon^i$ factor. PCG already has rate $\le \varepsilon$.
* **Chebyshev semi-iteration** (LSRN's solver): Krylov-LinearSystems L12's deferred
  `chebyshevIterate`. Its bound follows from PCG's comparison once Chebyshev iteration exists.
* **Rank-deficient $\mathbf{A}$** and **underdetermined / minimum-norm** problems. PCG theory needs
  `A.PosDef`, and CG on singular consistent systems is not in the library.
* **Ridge regression**, through $[\mathbf{A}; \sqrt\mu\,\mathbf{I}]$ with a partial sketch
  $\operatorname{diag}(\mathbf{S}, \mathbf{I})$. The embedding property of that partial sketch is
  not in Sketching.
* **Fresh sketches per step** [PilanciWainwright2016] and constrained least squares. These need
  i.i.d. sketch sequences, which the Kaczmarz note introduces, and convex constraints.
* **Blendenpik's coherence analysis**. In exact arithmetic it is covered by the SRHT corollary.
* **Floating point**: [Epperly2024, Theorem 6] and [EpperlyMeierNakatsukasa2024, Theorems 6.1, 8.2].
  The library has no rounding model.
* **Small later targets**: `sketchAndPrecondition_smul_sketch` (with `krylovSpace_smul`); the
  trade-off asymptotic form ($C(\lvert n\rvert + \log(1/\delta))/\varepsilon^2$ rows against
  $C\log(1/\tau)/\log(1/\varepsilon)$ iterations).
* **Explorer follow-up** (explorer sessions own it; hands-off). The collection
  `sketch-and-precondition` in `collections.toml` has
  `results = ["sketch-and-precondition"]`. The five new result ids of §4.3 need adding there, with
  titles in `results.toml`.

## 8. Decisions

**For the maintainer (serious, hard to reverse)**

**D1. What sketch-and-precondition is, as a definition.**
* (a) Basis-free: PCG on the normal equations with preconditioner
  $((\mathbf{S}\mathbf{A})^{\mathsf{H}}\mathbf{S}\mathbf{A})^{+}$ (§3.2). QR, SVD and any
  orthogonal factorization are realisation theorems, and the PCG recurrence computes it.
* (b) Basis-dependent: CGLS on $\mathbf{A}\mathbf{R}^{-1}$ for a supplied $\mathbf{R}$, which is
  Blendenpik's literal form. Every bound would then carry an `IsQR` hypothesis.
* (c) No definition, as for CGLS. Docstrings would show the composition with its three derived
  arguments.

Recommendation: **(a)**, like `rangeProjector` and `rsvd`; the review agrees.

**D2. New names, §5.3 rows, explicit start.**
* Names: `sketchAndPrecondition A S y x₀ q`, `iterativeSketching A S ω y x₀ q` and
  `richardsonIterate A M b x₀ q`.
* §5.3 rows, each naming its bridges:
  * "sketch-and-precondition": `IsQR.sketchAndPrecondition_eq_mulVec_cgIterate`,
    `IsSVD.sketchAndPrecondition_eq_mulVec_cgIterate`, `pcgState_x_eq_sketchAndPrecondition`;
  * "iterative sketching": `iterativeSketching_eq`, `IsQR.iterativeSketching_succ`;
  * "preconditioned Richardson": `richardsonIterate_mul_conjTranspose`.
* Options: (i) all three names; (ii) only `richardsonIterate`, with the two outputs as unnamed
  compositions (the CGLS precedent); (iii) only the two Regression names.
* The start is an explicit argument, and the warm start is a hypothesis. Changing that later renames
  every statement.

Recommendation: **(i)**, with the explicit start; the review agrees.

**D3 (amended after review). The shape of `richardsonIterate`.**
* (a) Rectangular, `(A : Matrix m n 𝕜) (M : Matrix n m 𝕜) (b : m → 𝕜) (x₀ : n → 𝕜)`, with the
  step folded into $\mathbf{M}$ (§3.1). `sub_richardsonIterate_eq` takes a fixed-point hypothesis,
  so it covers consistent systems and least squares. `richardsonIterate_mul_conjTranspose` reduces
  the rectangular form to the normal equations, so the energy bounds stay square.
* (b) Square only, `A M : Matrix n n 𝕜` (the first draft).
* (c) A step argument $\omega$, as in the quarry.

Recommendation: **(a)**.
* It is the definition shared with `Regression-Kaczmarz.md`. Its mean iterate
  `richardsonIterate (Aᴴ * A) ((frobNorm A ^ 2)⁻¹ • 1) (Aᴴ *ᵥ b) x₀ k` is the square instance and
  fits unchanged (checked). The rectangular equivalent is the Landweber form
  `richardsonIterate A ((frobNorm A ^ 2)⁻¹ • Aᴴ) b x₀ k`.
* Iterative sketching becomes Epperly's (3.2) literally.
* It is hard to reverse, because the shape fixes every statement in two notes.

**Proceeding as recommended**

* **D4. Scope:** §7.
* **D5. Error measures:**
  * energy error from any start;
  * residual against $\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{y}\|^2$ from the warm start;
  * forward error as $\sigma_{\min}(\mathbf{A})^2\|\mathbf{x}_\star - \mathbf{x}_q\|^2$, with no
    division.
* **D6. Hypotheses:**
  * `IsSubspaceEmbedding S A a b` with `0 < a` and `Function.Injective A.mulVec`;
  * $\varepsilon$ corollaries at $1 \mp \varepsilon$, named `_of_one_sub_one_add`;
  * every docstring translates to Epperly's unsquared $\eta$ and flags squared against unsquared
    residuals.
* **D7. Warm-start hypothesis:**
  * an embedding of a subspace containing $\operatorname{range}\mathbf{A}$ and $\mathbf{y}$, with
    a `fromCols` corollary;
  * the random families at $d = \lvert n\rvert + 1$;
  * an almost-sure sketched-minimizer hypothesis, plus `…_pinv_mulVec` forms with the start fixed.
* **D8. Families:** Gaussian, sub-Gaussian, SRHT and CountSketch for sketch-and-precondition.
  Iterative sketching gets the generic tails only, because PCG dominates it with the same
  preconditioner.
* **D9. Asymptotic forms:**
  * one `exists_forall_` per family at distortion $1/2$, with $\varepsilon_0$ on $\tau$;
  * CountSketch without `δ ≤ 1/2`;
  * the `+1` in $\lvert n\rvert + 1$ is kept. It matches `Regression-Rates.md` (rank plus one),
    keeps the SRHT logarithm away from $\log 0$, and is uniform across families. Absorbing it would
    need `δ ≤ 1/2`, which CountSketch does not have, and a constant of about 720 for Gaussian.
  * No Rates rows (maintainer, 2026-10-19).
* **D10. Files and placement:** as in §6. Iterative sketching gets its own file. The family-file
  placement is flagged.
* **D11. Sketch normalisation:** the family corollaries use normalised sketches; the scaling lemma
  is later.

## 9. Coordination with the Kaczmarz note

`docs/design/Regression-Kaczmarz.md` now exists. Its §10 reads this note's first draft. Shared
items:
* **`richardsonIterate`.**
  * The mean Kaczmarz iterate (its §5.3, D14) is
    `richardsonIterate (Aᴴ * A) ((frobNorm A ^ 2)⁻¹ • 1) (Aᴴ *ᵥ b) x₀ k`. This is valid for the
    rectangular signature at `m := n` and elaborates unchanged.
  * The Landweber spelling `richardsonIterate A ((frobNorm A ^ 2)⁻¹ • Aᴴ) b x₀ k` is equal through
    `richardsonIterate_mul_conjTranspose`, and is the natural form for an inconsistent $\mathbf{b}$.
  * For sketch-and-project, the expected step $\mathbb{E}[\mathbf{A}^{\mathsf{H}}\mathbf{S}^{\mathsf{H}}(\cdots)^{+}\mathbf{S}] \in \Bbbk^{n\times m}$
    fits the rectangular `M` directly. `sub_richardsonIterate_eq` needs only
    $\mathbf{M}(\mathbf{b} - \mathbf{A}\mathbf{x}_\star) = \mathbf{0}$.
  * The Kaczmarz note should not define a second Richardson iteration, and it already says it will
    not.
* **Error measures and solution interfaces**, both existing spellings: here
  `IsLeastSquaresSolution A y xs` and the energy error; there `A *ᵥ xs = b` and the Euclidean error.
* **Letters.** Here the count is `q` and the least-squares right-hand side is `y`; the Kaczmarz note
  uses `k` and `b`. Both iterates are total recursions with the count last.
* **Placement.** Both notes follow PORT_KRYLOV D12: least squares in `Regression/`, row-action
  solvers in `Solvers/`. `Richardson.lean` is in Krylov, below both.
* **Names kept distinct.** `iterativeSketching` uses one fixed sketch (Richardson);
  `sketchAndProject` and `kaczmarzIterate` use a fresh random sketch or row per step. The i.i.d.
  idiom of the Kaczmarz note is the prerequisite of the deferred fresh-sketch item of §7.

## 10. Proof difficulty

| Theorem | Uses | Estimate |
|---|---|---|
| `sub_richardsonIterate_eq`, `richardsonIterate_sub_mem_krylovSpace`, `richardsonIterate_mul_conjTranspose` | induction; `Matrix.mulVec_mulVec`, `Matrix.mulVec_sub`; `mulVec_mem_krylovSpace_succ`, `krylovSpace_mono` | easy; 20, 25, 10 lines |
| `Matrix.PosDef.re_quadForm_sub_richardsonIterate_le` | the factor `Matrix.PosDef.exists_eq_mul_conjTranspose_and_eq_mul_diagonal_mul_conjTranspose`; `spectrum_mul_conjTranspose_mul`; conjugating $(1 - \mathbf{C}\mathbf{C}^{\mathsf{H}}\mathbf{A})^q$ to $\mathbf{C}(1 - \mathbf{C}^{\mathsf{H}}\mathbf{A}\mathbf{C})^q\mathbf{C}^{-1}$; `quadForm_conjTranspose_mul_mul`; `Matrix.IsHermitian.re_quadForm_aeval_aeval_mulVec_le` at $g = X$, $p = (1 - X)^q$; the quarry's scalar bound | medium, about 80 lines |
| optimal step | the spectrum of $(c\mathbf{M})\mathbf{A}$ for real $c > 0$. Mathlib's `spectrum.smul_eq_smul` is over the scalar field, so go through `Matrix.PosDef.smul_le_and_le_smul_iff_spectrum_subset`: back to the Loewner sandwich, scale it, return to the spectrum. Also `(c • M).PosDef` with real `c`, by `RCLike.real_smul_eq_coe_smul` and Mathlib's `Matrix.PosDef.smul` | easy-medium, 45 lines |
| PCG comparison | `Matrix.PosDef.isMinOn_pcgIterate`, `richardsonIterate_sub_mem_krylovSpace` | easy, 15 lines |
| `pinv_conjTranspose_mul_self_eq_mul_conjTranspose` | `IsUnit M` from the injectivity of $\mathbf{B}\mathbf{M}$ (`Matrix.mulVec_injective_iff_isUnit`); $\mathbf{B}^{\mathsf{H}}\mathbf{B} = \mathbf{M}^{-\mathsf{H}}\mathbf{M}^{-1}$; `pinv_of_isUnit` | easy, 25 lines |
| `IsSubspaceEmbedding.pos_right_of_injective` | the `upper` field at a nonzero column, as in the proof of `pseudoConditionNumber_mul_sq_le` | easy, 15 lines |
| `IsSubspaceEmbedding.spectrum_pinv_mul_subset_Icc` | `IsSubspaceInjection.injective_mulVec`, `posDef_conjTranspose_mul_self_iff`, `pinv_of_isUnit`, the `lower`/`upper` fields scaled, `Matrix.PosDef.spectrum_mul_subset_Icc_of_le` | easy, 25 lines |
| realisations (§3.3) | `Matrix.PosDef.pcgIterate_eq_mulVec_cgIterate` at $\mathbf{C} = \mathbf{M}$ (with `IsUnit M` and the injectivity of $\mathbf{A}$ derived); `IsQR.eq_mul` and `IsQR.hasOrthonormalCols`; `IsSVD.eq` with $\mathbf{V}$ unitary (`hasOrthonormalCols_iff_mem_unitaryGroup`); `Matrix.PosDef.pcgState_x_eq` with Mathlib's `Matrix.PosDef.inv`; the steps by `iterativeSketching_eq` and the Pinv lemma | easy, 70 lines total |
| §4.3 general | the spectrum lemma, `pos_right_of_injective` (empty-`n` split), `Matrix.IsHermitian.re_quadForm_sub_pcgIterate_le_four_mul_pow` at $[b^{-1}, a^{-1}]$, `isLeastSquaresSolution_iff_normal_equations`, `quadForm_conjTranspose_mul_self` | easy, 45 lines |
| $\varepsilon$ rate step | $s = \sqrt{b/a} \ge 1$, $s \le s^2$ | easy, 20 lines |
| warm start, forward error | `IsSubspaceEmbedding.of_range_le`, `IsSubspaceEmbedding.norm_sub_mulVec_sq_le`, `IsLeastSquaresSolution.norm_sub_mulVec_sq_eq_add`, `IsLeastSquaresSolution.sub_mulVec_eq`, `Matrix.range_mulVecLin_le_range_fromCols_left`, `Matrix.mem_range_mulVecLin_fromCols_replicateCol`; `singularValues_last_mul_norm_le` | easy; 40, 20, 15 lines |
| iterative sketching (§4.4) | `iterativeSketching_eq`, the Richardson bound with $\omega\mathbf{G}^{+}$ (spectrum in $[\omega/b, \omega/a]$ by the same Loewner route), `(ω • pinv G).PosDef`; scalar max computations | easy, 40 + 3 × 20 lines |
| generic tails (§5.1) | `measure_mono_ae`, `measureReal_mono` | easy, 15 lines each |
| family explicit (§5.2) | `IsObliviousSubspaceEmbedding.hasSubspaceEmbedding` at $d = \lvert n\rvert + 1$ (`Matrix.rank_le_card_width`, `Fintype.card_sum`, `Fintype.card_unit`); the size theorem; `IsSubspaceEmbedding.mono`; `pinv_mulVec` forms by `isLeastSquaresSolution_pinv_mulVec` | easy, 35 + 5 lines each |
| family asymptotic (§5.3) | the family's `…_le` comparison, threshold arithmetic as in the existing `exists_forall_` proofs, $\log 8 \le 3\log(1/\tau)$ | medium (arithmetic), 50 lines each |

Nothing needs new probability or new Krylov theory beyond Richardson. The hardest proof is the
Richardson bound, which follows the private `exists_split` pattern of `PCG.lean`. If that split is
needed a second time, it becomes public API in `PCG.lean` rather than being copied, recorded as a
placement amendment.

## 11. Bibliography

New `docs/references.bib` entries, each added in the commit that first cites it:

* `RokhlinTygert2008`: V. Rokhlin, M. Tygert, *A fast randomized algorithm for overdetermined linear
  least-squares regression*, PNAS 105(36):13212–13217, 2008.
* `AvronMaymounkovToledo2010`: H. Avron, P. Maymounkov, S. Toledo, *Blendenpik: Supercharging
  LAPACK's least-squares solver*, SISC 32(3):1217–1236, 2010.
* `MengSaundersMahoney2014`: X. Meng, M. A. Saunders, M. W. Mahoney, *LSRN: A parallel iterative
  solver for strongly over- or underdetermined systems*, SISC 36(2):C95–C118, 2014.
* `Epperly2024`: E. N. Epperly, *Fast and forward stable randomized algorithms for linear
  least-squares problems*, SIAM J. Matrix Anal. Appl. 45(4):1782–1804, 2024 (likely locator, to
  verify); arXiv:2311.04362v2, whose numbering the locators follow. Distinct from the existing
  `Epperly2023` (blog post).
* `EpperlyMeierNakatsukasa2024`: E. N. Epperly, M. Meier, Y. Nakatsukasa, *Fast randomized
  least-squares solvers can be just as accurate and stable as classical direct solvers*,
  arXiv:2406.03468v3 (20 August 2025); `@misc` until the journal version is confirmed.
* `PilanciWainwright2016`: M. Pilanci, M. J. Wainwright, *Iterative Hessian sketch: Fast and
  accurate solution approximation for constrained least-squares*, JMLR 17(53):1–38, 2016;
  arXiv:1411.0347.
* `PaigeSaunders1982`: C. C. Paige, M. A. Saunders, *LSQR: An algorithm for sparse linear equations
  and sparse least squares*, ACM TOMS 8(1):43–71, 1982. Cited only in docstrings that mention LSQR.

Existing keys used: `MartinssonTropp2020`, `Saad2003`, `Greenbaum1997`, `Woodruff2014`,
`GolubVanLoan2013`.
