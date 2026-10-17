# Design note: Krylov stage K0, the conjugate gradient slice

Status: 2026-10-17. Drafted from the brief `docs/PORT_KRYLOV.md` (D3, D4, D5, D7, D8, D10, §7,
§8), reviewed by an independent agent (no false statement found; the hypothesis-free Lanczos and
Hestenes–Stiefel realisations were checked, complex phases included), and revised with its fixes.
The maintainer's decisions of 2026-10-17 apply: D1 to D7 and D9 to D12 as recommended, D8 amended
to `spectrum ℝ A ⊆ s` for every spectral location with polynomial bounds `∀ x ∈ s, |p.eval x| ≤ M`.
The statements live in the library files of §6 (not yet in `NLAlib.lean`), each with its module
docstring, LaTeX docstrings, citations and `sorry` proofs; they build with only `sorry` warnings.
Signatures are not repeated here: the files are the specification.

The maintainer's directions, verbatim: "I dont want to define algorithms by formulas that are
computable (in the NLA sense of this word). So for instance, CG can be defined as
Q(Q'AQ)^{-1}Q'b where Q is any onb. This will, in particular, show that the "Lanczos basis"
yields CG. I also want to show that the standard implementations yield the algorithm, although
I'm not so clear how this works. Do we have something similar for gram-schmidt and householder?
... we should think about how we are going to generalize this to block methods. Does it make
sense to have a single definition? Or to later show the regular one is a special case." And:
"let's focus first on just getting the CG infrastructure so that we don't expend too much effort.
I want to see how everything fits together".

## 1. Overview

The slice has three layers, kept apart on purpose.

1. **Objects that are mathematics.** The Krylov matrix and space, the grade, the Galerkin inverse
   on a subspace, the CG iterate, the canonical Krylov basis. None is an algorithm: each is a
   formula that depends on the subspace only, total, with documented junk values.
2. **Theorems about the objects.** The frame form (the maintainer's
   $\mathbf{Q}(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})^{-1}\mathbf{Q}^{\mathsf{H}}\mathbf{b}$
   for every orthonormal basis), optimality, the Galerkin condition, the error polynomial, the
   Chebyshev rate, finite termination, and the structure of the canonical basis.
3. **Algorithms and their realisation theorems.** The Lanczos three-term recurrence and the
   Hestenes–Stiefel recurrence, as total recursions on a state record, each with a theorem that
   what it computes is the object of layer 1. This is the library's existing pattern for
   Gram–Schmidt, Householder and Gaussian elimination (§4).

Dependency list ("X uses Y": the statement or definition of X mentions Y).

- `krylovMatrix A b q` uses matrix powers only; columns `Fin q`, column `j` is $\mathbf{A}^j\mathbf{b}$.
- `krylovSpace A b q` uses `krylovMatrix` (its column space). The polynomial description
  `mem_krylovSpace_iff` uses `Polynomial.aeval`; real polynomials reach it through
  `aeval_mulVec_mem_krylovSpace`, whose proof uses `Polynomial.aeval_map_algebraMap`.
- `krylovGrade A b` uses `krylovMatrix` (rank with $\lvert n \rvert$ columns); the rank formula,
  injectivity below the grade, `krylovGrade_le_iff`, stabilisation and invariance use the grade.
- `galerkinInverse A X` uses `rangeProjector X` and `pinv`, nothing about Krylov spaces: any basis
  matrix, any column type.
- `cgIterate A b q` uses `galerkinInverse` and `krylovMatrix`.
  - The frame form uses `HasOrthonormalCols Q` and a range equality with `krylovSpace`.
  - Optimality uses Mathlib's `IsMinOn` and `quadForm`; the Galerkin condition is
    `(krylovMatrix A b q)ᴴ *ᵥ (b - A *ᵥ cgIterate A b q) = 0`.
  - The error polynomial uses `mem_krylovSpace_iff`; the comparison with any residual polynomial
    uses optimality and `Polynomial.exists_degree_lt_one_sub_eq_X_mul_of_eval_zero_eq_one`.
  - The spectral bound (`spectrum ℝ A ⊆ s`) uses
    `Matrix.IsHermitian.re_quadForm_aeval_aeval_mulVec_le`; the Chebyshev rate uses
    `chebyshevResidual`, `degree_chebyshevResidual_le`, `eval_chebyshevResidual_zero` and
    `isUniformApproxOn_chebyshevResidual_two_mul_pow`; the $\kappa$ form uses
    `pseudoConditionNumber` and `Matrix.PosDef.pseudoConditionNumber_eq`.
  - Finite termination uses `mem_krylovSpace_of_krylovGrade_le` and the exactness of
    `galerkinInverse`.
- `IsGradedKrylovBasis A b Q` uses `HasOrthonormalCols` and `krylovSpace`; its structure theorems
  conclude `IsUpperHessenberg` and `IsTridiagonal`.
- `arnoldiMatrix A b q` (the canonical Lanczos basis for Hermitian $\mathbf{A}$) uses
  `gramSchmidtQ` of `krylovMatrix`.
- `lanczosState A b j` uses matrix-vector products, inner products and norms only. Its realisation
  uses `arnoldiMatrix`, `isGradedKrylovBasis_of_forall_col_mem` and
  `IsGradedKrylovBasis.eq_arnoldiMatrix` (which uses `IsQR.unique` and `isQR_gramSchmidt`).
- `cgState A b x₀ k` likewise; its realisation uses `cgIterate` through the Galerkin
  characterisation.
- "The Lanczos basis yields CG" and "the Lanczos recurrence yields CG" use `cgIterate`,
  `arnoldiMatrix` and the Lanczos realisation, and sit in their own file above both.
- (Block round) `blockKrylovMatrix A B q` with columns `Fin q × s`; block CG is
  `galerkinInverse A (blockKrylovMatrix A B q) * B`, no new definition.

Totals: 16 definitions and 67 theorems in the slice, of which five theorems are Matrix-layer
additions; the block round adds one definition and four theorems (§5).

## 2. Definitions

Common context `{𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]`; `DecidableEq n`
is needed by `A ^ j`, by `1` and by `⁻¹`, and is omitted where the linter says it is unused.
Vectors are `n → 𝕜` with `⬝ᵥ` and `‖WithLp.toLp 2 v‖` (CONTRIBUTING §5.1).

### 2.1 `krylovMatrix`, `krylovSpace` (`Krylov/Basic/Space.lean`)

`krylovMatrix A b q : Matrix n (Fin q) 𝕜`, column `j` equal to `A ^ (j : ℕ) *ᵥ b`; `krylovSpace A b q`
is `LinearMap.range (krylovMatrix A b q).mulVecLin`. The matrix is primary (brief D2(c)): it plugs
the space into `rangeProjector`, `rank`, `pinv`, `gramSchmidtQ` and their measurability lemmas,
and later into `rsvd` for block Krylov; the named `Submodule` keeps statements readable and is
definitionally the §5.3 "column space" spelling. `Fin q` because the column order carries content.
No junk values: `q` counts generators, $\mathcal{K}_0 = \{\mathbf{0}\}$, and "$q$ matrix-vector
products" means $\mathcal{K}_{q+1}$. Polynomials (brief D1(c)): membership and existence produce
`p : 𝕜[X]`; bounds take a supplied `p : ℝ[X]` acting through the ℝ-algebra structure, as in
`Matrix/Functions/Polynomial.lean`. One membership lemma covers both, over any coefficient ring
`R` with `[Algebra R 𝕜]`. Mathlib's nearest object, the cyclic submodule in `Module.AEval'`,
cannot be stated about `n → 𝕜` without transport (an addition, recorded in
`docs/design/Mathlib-deviations.md`).

### 2.2 `krylovGrade` (`Krylov/Basic/Grade.lean`)

`krylovGrade A b := (krylovMatrix A b (Fintype.card n)).rank`, the grade $\nu$. A rank, so that
measurability in $\mathbf{b}$ comes from `measurable_rank`, and one number for every breakdown in
the layer (brief D7). The basic characterisation is
`krylovGrade_le_iff : krylovGrade A b ≤ q ↔ A ^ q *ᵥ b ∈ krylovSpace A b q`, from which the rank
formula, stabilisation and invariance follow. A bridge to `minpoly` is left to the stage that
needs it.

### 2.3 `galerkinInverse` (`Krylov/LinearSystems/Galerkin.lean`)

`galerkinInverse A X := pinv (rangeProjector X * A * rangeProjector X)` (brief D3). Its range and
corange already lie in the column space of `X`, since the pseudoinverse of
$\mathbf{P}\mathbf{A}\mathbf{P}$ has the range of its adjoint. Junk value: when
$\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$ is singular for a frame $\mathbf{Q}$ of the space,
the pseudoinverse is returned, which is not a Galerkin solution. Candidates considered:

| Candidate | Verdict |
|---|---|
| $\mathbf{K}(\mathbf{K}^{\mathsf{H}}\mathbf{A}\mathbf{K})^{+}\mathbf{K}^{\mathsf{H}}\mathbf{b}$, $\mathbf{K}$ the Krylov matrix | total, but basis-dependent when the compression is singular, basis independence only for positive definite $\mathbf{A}$; with $^{-1}$ it is $\mathbf{0}$ past the grade |
| $\mathbf{A}$-orthogonal projection of $\mathbf{A}^{-1}\mathbf{b}$ | needs an inner-product type synonym carrying $\mathbf{A}$; recovered as `Matrix.PosDef.isMinOn_galerkinInverse_mulVec` |
| an `IsMinOn` predicate (`IsCGIterate`) | not a function, so consumers need choice; the library has no constrained least-squares predicate either; recovered as a theorem |
| a `Submodule`-based operator | forces `EuclideanSpace` transport; all spaces here are column spaces |
| $(\mathbf{P}\mathbf{A}\mathbf{P})^{+}$, $\mathbf{P}$ = `rangeProjector X` (adopted) | depends on the subspace only (`rangeProjector_inj`), frame form for every $\mathbf{A}$, measurable through `measurable_rangeProjector`, `measurable_pinv`, block-ready |

`X : Matrix n p 𝕜` needs only `[Fintype p]`; frames `Q : Matrix n r 𝕜` need `[DecidableEq r]`.
"Residual orthogonal to the space" has one spelling, `Xᴴ *ᵥ (b - A *ᵥ y) = 0`, with the bridge
`forall_mem_range_star_dotProduct_eq_zero_iff` (Matrix layer, `Matrix/Basic/Projector.lean`,
proved). Downstream, CG, block CG, PCG, CGLS and deflated CG are `galerkinInverse A X` for
different `X`; K1 and K2 add `minResidualInverse` and `compressedCfc` in the same shape.

### 2.4 `cgIterate` (`Krylov/LinearSystems/CG.lean`)

`cgIterate A b q := galerkinInverse A (krylovMatrix A b q) *ᵥ b`, written
$\mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, q)$ in other docstrings. Zero start: a start
$\mathbf{x}_0$ is `x₀ + cgIterate A (b - A *ᵥ x₀) q`, and only the algorithm `cgState` takes `x₀`.
Errors are target minus output, `xs - cgIterate A b q` with `hxs : A *ᵥ xs = b`, in the squared
$\mathbf{A}$-norm `RCLike.re (quadForm A _)`. Junk values: $q = 0$ and $\mathbf{b} = \mathbf{0}$
give $\mathbf{0}$; past the grade a positive definite $\mathbf{A}$ gives the solution.

### 2.5 `IsGradedKrylovBasis`, `arnoldiMatrix` (`Krylov/Processes/Lanczos.lean`)

`IsGradedKrylovBasis A b Q` (a structure: `HasOrthonormalCols Q` and, for each `j : Fin q`, the
first `j + 1` columns span `krylovSpace A b (j + 1)`), with constructor
`isGradedKrylovBasis_of_forall_col_mem` (CONTRIBUTING §5.4); the compression stays the expression
`Qᴴ * A * Q` (brief D5). `arnoldiMatrix A b q := gramSchmidtQ (krylovMatrix A b q)`, one name for
Arnoldi and Lanczos, zero columns past the grade (D7).

The zero-column caution, in two sentences: past the grade $\mathbf{T} =
\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$ is singular, so `T⁻¹ = 0` and `spectrum ℝ T ⊆ Set.Icc a a'`
fails for $a > 0$ (the frame value $\mathbf{Q}f(\mathbf{T})\mathbf{Q}^{\mathsf{H}}\mathbf{b}$ itself is
unchanged, since a matrix spectrum is finite, `Matrix.finite_real_spectrum`, and `cfc_blockDiagonal`
splits the padding off). Hence frame forms on genuine frames are primary, and every statement on
the canonical basis that inverts $\mathbf{T}$ carries `q + 1 ≤ krylovGrade A b`.

### 2.6 The recurrences

`Krylov/Processes/LanczosRecurrence.lean`: `structure LanczosState (𝕜 n)` with fields `prev`,
`cur : n → 𝕜` and `beta : ℝ` (the state before step $j$ is $(\mathbf{q}_{j-1}, \mathbf{q}_j,
\beta_j)$); `lanczosAlpha A s`; `lanczosStep A s` in Paige's order
($\mathbf{w} = \mathbf{A}\mathbf{q}_j - \beta_j\mathbf{q}_{j-1} - \alpha_j\mathbf{q}_j$,
$\beta_{j+1} = \|\mathbf{w}\|$, $\mathbf{q}_{j+1} = \beta_{j+1}^{-1}\mathbf{w}$); `lanczosState A b`
by pattern matching on ℕ; `lanczosMatrix A b q` and `lanczosTridiagonal A b q`, what the
implementation outputs. At breakdown ($\beta_\nu = 0$) the state is $(\mathbf{q}_{\nu-1},
\mathbf{0}, 0)$ and it is zero from the following step.

`Krylov/LinearSystems/CGRecurrence.lean`: `structure CGState (𝕜 n)` with `x r p : n → 𝕜`;
`cgStep A s` (real step sizes $\alpha_k = \|\mathbf{r}_k\|^2 /
\operatorname{Re}(\mathbf{p}_k^{\mathsf{H}}\mathbf{A}\mathbf{p}_k)$,
$\beta_k = \|\mathbf{r}_{k+1}\|^2/\|\mathbf{r}_k\|^2$, updated residual stored); `cgState A b x₀`.
A zero residual gives $\alpha_k = \beta_k = 0$ and the state stays at the solution.

## 3. Theorems

Names, one-line claims and proof plans; statements are in the files. `Result:` ids:
`cg-galerkin-formula`, `cg-optimality`, `cg-chebyshev-bound`, `lanczos-recurrence`,
`cg-recurrence`; `scripts/Reuse.lean` will be run on these five theorems to check that they are
proved from the library's API.

### 3.1 Matrix additions

- `forall_mem_range_star_dotProduct_eq_zero_iff` (`Matrix/Basic/Projector.lean`): orthogonality to
  a column space iff `Xᴴ *ᵥ w = 0`. Proved.
- `range_gramSchmidtQ` (`Matrix/Factorizations/GramSchmidt.lean`): the Gram–Schmidt matrix spans
  the column space, no rank assumption. Proved.
- `gramSchmidtQ_mul_conjTranspose`: $\mathbf{Q}\mathbf{Q}^{\mathsf{H}} = \mathbf{P}_{\mathbf{A}}$.
  Plan: `conjTranspose_gramSchmidtQ_mul_self` (a zero `gramSchmidtR j j` is a zero column, read
  off that diagonal), `IsStarProjection.eq_rangeProjector`, `range_gramSchmidtQ`.
- `gramSchmidtQ_submatrix`: restriction to an initial segment (an order embedding onto a lower
  set); Mathlib has nothing. Plan: `gramSchmidt` at $j$ depends on indices $\le j$ only, induction
  through `InnerProductSpace.gramSchmidt_def`. `gramSchmidtQ_submatrix_castLE` follows (proved).

These two sorried lemmas are in a file `NLAlib.lean` imports, so `import NLAlib` is not sorry-free
until they are proved; they are the first proof task (§6).

### 3.2 Space and grade

Space: `krylovMatrix_apply`, `krylovMatrix_submatrix_castLE` (both `rfl`); `mem_krylovSpace_iff`
(plan: $\mathbf{K}\mathbf{c} = \sum_j c_j\mathbf{A}^j\mathbf{b}$, `Polynomial.aeval_eq_sum_range'`,
`Polynomial.degreeLTEquiv`); `aeval_mulVec_mem_krylovSpace` (`Polynomial.aeval_map_algebraMap`,
`Polynomial.degree_map_le`); `krylovSpace_mono`, `krylovSpace_zero`, `self_mem_krylovSpace`,
`mulVec_mem_krylovSpace_succ` (from membership and `X * p`).

Grade: `krylovGrade_le_iff` (the core: once $\mathbf{A}^q\mathbf{b} \in \mathcal{K}_q$ the space is
invariant; before, each step adds a dimension, `Submodule.finrank_lt_finrank_of_lt`);
`rank_krylovMatrix`, `finrank_krylovSpace` ($\min(q, \nu)$); `krylovGrade_le_card`
(Cayley–Hamilton, `Matrix.aeval_self_charpoly`); `krylovMatrix_mulVec_injective_iff`;
`krylovSpace_eq_of_krylovGrade_le`; `mulVec_mem_krylovSpace_of_krylovGrade_le`;
`mem_krylovSpace_of_krylovGrade_le` ($\mathbf{A}$ maps the invariant space injectively onto
itself and $\mathbf{b}$ lies in it).

### 3.3 Galerkin inverse

- `galerkinInverse_eq_of_range_eq`: depends on the column space only. Proved (`rangeProjector_inj`).
- `HasOrthonormalCols.galerkinInverse_eq`: $\mathbf{Q}(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})^{+}
  \mathbf{Q}^{\mathsf{H}}$ for every $\mathbf{A}$. Plan: `HasOrthonormalCols.rangeProjector_eq`,
  `HasOrthonormalCols.pinv_mul_left`, `HasOrthonormalCols.pinv_mul_conjTranspose_right`.
- `Matrix.PosDef.galerkinInverse_eq`: the same with $^{-1}$. Plan: add
  `Matrix.PosDef.conjTranspose_mul_mul_same`, `Matrix.PosDef.isUnit`, `pinv_of_isUnit`.
- `galerkinInverse_mulVec_mem`: the output lies in the space (`isPinv_pinv`,
  `range_mulVecLin_rangeProjector`).
- `Matrix.PosDef.conjTranspose_mul_one_sub_mul_galerkinInverse`: the block Galerkin condition
  `Xᴴ * (1 - A * galerkinInverse A X) = 0`. Plan: a frame of the space
  (`exists_hasOrthonormalCols_range_eq`), where it is
  $\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})^{-1} = \mathbf{I}$.
- `Matrix.PosDef.eq_galerkinInverse_mulVec_of_conjTranspose_mulVec_sub_eq_zero`: the Galerkin
  condition determines the vector (the difference $\mathbf{d}$ has
  $\mathbf{d}^{\mathsf{H}}\mathbf{A}\mathbf{d} = 0$).
- `Matrix.PosDef.isMinOn_galerkinInverse_mulVec`: $\mathbf{A}$-norm optimality (Pythagoras, cross
  term killed by the Galerkin condition).
- `Matrix.PosDef.galerkinInverse_mulVec_eq_of_mem`: exact when the solution is in the space.

### 3.4 CG

- `cgIterate_mem_krylovSpace` (proved), `cgIterate_zero`.
- `HasOrthonormalCols.cgIterate_eq`: the pinv frame form, every $\mathbf{A}$.
- `Matrix.PosDef.cgIterate_eq`: **CG is $\mathbf{Q}(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})^{-1}
  \mathbf{Q}^{\mathsf{H}}\mathbf{b}$ for any orthonormal basis of the Krylov space**, the
  maintainer's definition as the first theorem. Plan: §3.3 and `Matrix.mulVec_mulVec`.
- `Matrix.PosDef.conjTranspose_krylovMatrix_mulVec_sub_mulVec_cgIterate_eq_zero`: the Galerkin
  condition; `Matrix.PosDef.eq_cgIterate_of_conjTranspose_krylovMatrix_mulVec_sub_eq_zero`: it
  characterises CG (proved from §3.3).
- `Matrix.PosDef.isMinOn_cgIterate`: $\mathbf{A}$-norm optimality (proved from §3.3).
- `exists_sub_cgIterate_eq_aeval`: the error polynomial $p \in \Bbbk[X]$, $\deg p \le q$,
  $p(0) = 1$, with no hypothesis on $\mathbf{A}$ ($p = 1 - Xs$ from membership).
- `Matrix.PosDef.re_quadForm_sub_cgIterate_le_re_quadForm_aeval`: CG beats every real residual
  polynomial ($1 - p = Xs$ puts $\mathbf{x}_\star - p(\mathbf{A})\mathbf{x}_\star = s(\mathbf{A})\mathbf{b}$
  in $\mathcal{K}_q$, then optimality).
- `Matrix.PosDef.re_quadForm_sub_cgIterate_le`: with `spectrum ℝ A ⊆ s` and $\lvert p \rvert \le M$
  on $s$, error at most $M^2\|\mathbf{x}_\star\|_{\mathbf{A}}^2$ (the comparison, then
  `Matrix.IsHermitian.re_quadForm_aeval_aeval_mulVec_le` with weight $X$ on the spectrum).
- `Matrix.IsHermitian.re_quadForm_sub_cgIterate_le_two_mul_pow`: **the Chebyshev rate** for
  Hermitian $\mathbf{A}$ with spectrum in `Set.Icc a a'`, $0 < a$ (so positive definite, no
  separate hypothesis). Cases: $a < a'$ at `chebyshevResidual a a' q`, converted by
  `Metric.isUniformApproxOn_iff` and `Real.dist_0_eq_abs`; $a = a'$ at $1 - X/a$; $a' < a$ empty
  index type. A Loewner sandwich reaches the hypotheses through `isHermitian_of_le_smul_one` and
  `spectrum_subset_Icc_of_le`; no Loewner corollary is stated (no consumer in the slice).
- `Matrix.PosDef.re_quadForm_sub_cgIterate_le_two_mul_pow_pseudoConditionNumber`: the $\kappa$ form
  (the rate at the extreme eigenvalues, `Matrix.IsHermitian.spectrum_subset_iff`,
  `Matrix.PosDef.pseudoConditionNumber_eq`).
- `Matrix.PosDef.cgIterate_eq_of_krylovGrade_le`: finite termination (proved from Grade and §3.3).

### 3.5 Lanczos basis

- `isGradedKrylovBasis_of_forall_col_mem`: the constructor (independent columns in a space of
  dimension at most $j + 1$).
- `IsGradedKrylovBasis.range_eq`, `.le_krylovGrade`, `.isUpperHessenberg`
  ($\mathbf{A}\mathbf{q}_j \in \mathcal{K}_{j+2}$, orthogonal to later columns), `.isTridiagonal`
  (proved, `IsUpperHessenberg.isTridiagonal`), `.eq_arnoldiMatrix` (an `IsQR` of the Krylov matrix
  with real positive diagonal, then `IsQR.unique` against `isQR_gramSchmidt`).
- `range_arnoldiMatrix` (proved), `arnoldiMatrix_submatrix_castLE` (proved from
  `gramSchmidtQ_submatrix_castLE`), `hasOrthonormalCols_arnoldiMatrix_iff`,
  `isGradedKrylovBasis_arnoldiMatrix`, `conjTranspose_arnoldiMatrix_mulVec_self`
  ($\mathbf{Q}^{\mathsf{H}}\mathbf{b} = \|\mathbf{b}\|\mathbf{e}_0$, every $q$), `mul_arnoldiMatrix`
  (the Arnoldi relation for every $q$, through `gramSchmidtQ_mul_conjTranspose`).

### 3.6 Recurrences and the CG corollaries

- `Matrix.IsHermitian.lanczosMatrix_eq_arnoldiMatrix`, `Matrix.IsHermitian.lanczosTridiagonal_eq`:
  the recurrence computes the Lanczos basis and its compression, every $q$, no breakdown
  hypothesis; `Matrix.IsHermitian.lanczosState_beta_eq_zero_iff`: breakdown exactly at the grade.
- `cgState_r_eq`, `cgState_x_sub_mem_krylovSpace` (every $\mathbf{A}$);
  `Matrix.PosDef.conjTranspose_krylovMatrix_mulVec_cgState_r_eq_zero` ($\mathbf{r}_k \perp
  \mathcal{K}_k$), `Matrix.PosDef.span_cgState_p`, `Matrix.PosDef.star_cgState_r_dotProduct_eq_zero`,
  `Matrix.PosDef.star_cgState_p_dotProduct_mulVec_eq_zero`; `Matrix.PosDef.cgState_x_eq`: **the
  Hestenes–Stiefel iterates are CG**, every $k$; `Matrix.PosDef.cgState_r_eq_zero_iff`.
- `Krylov/LinearSystems/CGLanczos.lean`: `Matrix.PosDef.cgIterate_eq_arnoldiMatrix`, **the Lanczos
  basis yields CG**, $\mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, q+1) =
  \|\mathbf{b}\|\mathbf{Q}\mathbf{T}^{-1}\mathbf{e}_0$ under `q + 1 ≤ krylovGrade A b` (plan:
  `Matrix.PosDef.cgIterate_eq`, `conjTranspose_arnoldiMatrix_mulVec_self`); and
  `Matrix.PosDef.cgIterate_eq_lanczosMatrix`, **the Lanczos recurrence yields CG** (proved by
  rewriting with the two realisations).

## 4. How the realisation theorems work

Yes, the library has this for Gram–Schmidt and Householder. It separates the object from the
algorithm in four ingredients (`docs/design/Matrix-Factorizations.md` §2): the object
(`IsQR A Q R`, unique with positive diagonal); a total recursion on a state indexed by the step
(`householderState`, `gaussState`); breakdown as a value through $0^{-1} = 0$; invariants by
induction and a realisation theorem concluding the object (`isQR_householder`,
`isLU_luLower_luUpper`, whose hypothesis on computed pivots is then characterised by
`forall_luUpper_apply_self_ne_zero_iff`). The Krylov recurrences follow the same pattern, with step
functions `lanczosStep (A : Matrix n n 𝕜) (s : LanczosState 𝕜 n) : LanczosState 𝕜 n` and
`cgStep (A : Matrix n n 𝕜) (s : CGState 𝕜 n) : CGState 𝕜 n`, sequences
`lanczosState A b : ℕ → LanczosState 𝕜 n` and `cgState A b x₀ : ℕ → CGState 𝕜 n`. In both, the
frozen state after breakdown already equals the definition, so the no-breakdown hypothesis leaves
the statement and becomes a separate characterisation of when breakdown happens (brief O7).

**Lanczos** (Hermitian $\mathbf{A}$). Invariant by strong induction for $j < \nu$: the computed
$\mathbf{q}_0, \dots, \mathbf{q}_j$ are orthonormal, $\mathbf{q}_j \in c_j\mathbf{A}^j\mathbf{b} +
\mathcal{K}_j$ with $c_j > 0$, $\beta_j = \mathbf{q}_j^{\mathsf{H}}\mathbf{A}\mathbf{q}_{j-1} > 0$
and $\alpha_j = \mathbf{q}_j^{\mathsf{H}}\mathbf{A}\mathbf{q}_j$. Hermitian symmetry gives
$\mathbf{q}_i^{\mathsf{H}}\mathbf{A}\mathbf{q}_j = 0$ for $i + 1 < j$ (since
$\mathbf{A}\mathbf{q}_i \in \mathcal{K}_{i+2} \subseteq \mathcal{K}_j$), which is why three terms
suffice: $\mathbf{w}$ is the Gram–Schmidt remainder of $\mathbf{A}\mathbf{q}_j$, a positive multiple
of that of $\mathbf{A}^{j+1}\mathbf{b}$. Below the grade, `isGradedKrylovBasis_of_forall_col_mem`
and `IsGradedKrylovBasis.eq_arnoldiMatrix` give equality with the canonical basis. At the grade
$\mathbf{w} = \mathbf{0}$ (`krylovGrade_le_iff`), and from there both sides are zero (a zero
`gramSchmidtR j j` is a zero column of `gramSchmidtQ`, read off the diagonal of
`conjTranspose_gramSchmidtQ_mul_self`); `arnoldiMatrix_submatrix_castLE` handles nesting.
Estimate: 500 to 700 lines for the three Lanczos theorems.

**Hestenes–Stiefel** (positive definite $\mathbf{A}$, $\mathbf{r}_0 = \mathbf{b} -
\mathbf{A}\mathbf{x}_0$). Prove first, by one joint induction, `span_cgState_p` and
$\mathbf{r}_k \perp \mathcal{K}_k$ (`conjTranspose_krylovMatrix_mulVec_cgState_r_eq_zero`), with
$\mathbf{p}_k$ $\mathbf{A}$-conjugate to $\mathcal{K}_k$ and $\mathbf{p}_k = \mathbf{0}$ only when
$\mathbf{r}_k = \mathbf{0}$ (so $\alpha_k$ divides by $\mathbf{p}_k^{\mathsf{H}}\mathbf{A}\mathbf{p}_k >
0$ unless frozen). Then `cgState_x_eq` needs no further induction: $\mathbf{x}_k - \mathbf{x}_0 \in
\mathcal{K}_k$, its residual for the right-hand side $\mathbf{r}_0$ is $\mathbf{r}_k$, orthogonal
to $\mathcal{K}_k$, and the Galerkin characterisation identifies it, for every $k$ (past the grade
$\mathbf{r}_k = \mathbf{0}$). The pairwise forms (residuals orthogonal, directions conjugate)
follow and may land later without blocking the realisation. `cgState_r_eq_zero_iff`: a zero
residual puts $\mathbf{x}_\star - \mathbf{x}_0$ in $\mathcal{K}_k$, hence $\nu \le k$. Estimate:
at least 400 lines.

What the maintainer gets: "the standard implementations yield the algorithm" is
`Matrix.IsHermitian.lanczosMatrix_eq_arnoldiMatrix`, `Matrix.IsHermitian.lanczosTridiagonal_eq`
and `Matrix.PosDef.cgState_x_eq`, each an equality between what code computes and a formula with
no hypothesis beyond the class of matrices, plus `Matrix.PosDef.cgIterate_eq_lanczosMatrix`.

## 5. Block generalisation

**Block-ready now.** All of `Galerkin.lean`: `galerkinInverse A X` takes any `X` with any
`Fintype` column type, the frame forms take any frame, and the Galerkin condition is in block
form, so block CG is `galerkinInverse A (blockKrylovMatrix A B q) * B` with no new definition, and
the same theorems serve PCG and CGLS.

**Vector-specific.** `krylovMatrix` (one start vector); scalar-polynomial membership (blocks need a
polynomial per column, or matrix coefficients); the grade (blocks need deflation); the error
polynomial and residual comparison; the Chebyshev rate (it transfers to block CG columnwise,
since $\mathcal{K}_q(\mathbf{A}, \mathbf{b}_j) \subseteq \mathcal{K}_q(\mathbf{A}, \mathbf{B})$);
`arnoldiMatrix` (`gramSchmidtQ` needs a linear order on the columns, which `Fin q × s` lacks, so the
block basis goes through `finProdFinEquiv` or a block QR); both recurrences (block Lanczos has
$s \times s$ coefficient blocks and rank-deficient breakdown; block CG has matrix step sizes).

**Recommendation** (D10(c)): vector definitions now; in the block round
`blockKrylovMatrix A B q : Matrix n (Fin q × s) 𝕜`, column $(j, i)$ equal to
$(\mathbf{A}^j\mathbf{B})_{:,i}$, with these bridges (checked to elaborate in the scratch sketch
`BlockKrylov.lean`, not a library file):

```lean
theorem range_blockKrylovMatrix_replicateCol (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) :
    LinearMap.range (blockKrylovMatrix A (Matrix.replicateCol Unit b) q).mulVecLin =
      krylovSpace A b q
theorem krylovSpace_col_le_range_blockKrylovMatrix (A : Matrix n n 𝕜) (B : Matrix n s 𝕜)
    (q : ℕ) (j : s) :
    krylovSpace A (B.col j) q ≤ LinearMap.range (blockKrylovMatrix A B q).mulVecLin
theorem galerkinInverse_blockKrylovMatrix_replicateCol (A : Matrix n n 𝕜) (b : n → 𝕜)
    (q : ℕ) :
    galerkinInverse A (blockKrylovMatrix A (Matrix.replicateCol Unit b) q) =
      galerkinInverse A (krylovMatrix A b q)
```

The third is `galerkinInverse_eq_of_range_eq` at the first; "block CG with one column is CG",
`galerkinInverse A (blockKrylovMatrix A (replicateCol Unit b) q) * replicateCol Unit b =
replicateCol Unit (cgIterate A b q)`, is its corollary. The second transfers every vector bound.

**The alternative, one block definition with the vector case at `s = Unit`**, would put
`replicateCol Unit b` and `Fin q × Unit` into every vector statement, state scalar results through
matrix polynomials and `Matrix Unit Unit` Lanczos coefficients, and still not specialise the
block algorithms for free (rank-deficient blocks). Its only gain is in the methods, which
`galerkinInverse` already shares.

## 6. Files, imports and placement

Import diagram ("uses" is a direct import; arrows avoided):

- `Matrix/Basic/Projector.lean` (addition: `forall_mem_range_star_dotProduct_eq_zero_iff`) and
  `Matrix/Factorizations/GramSchmidt.lean` (additions: `range_gramSchmidtQ`,
  `gramSchmidtQ_mul_conjTranspose`, `gramSchmidtQ_submatrix`, `gramSchmidtQ_submatrix_castLE`).
- `Krylov/Basic/Space.lean` uses Mathlib only.
- `Krylov/Basic/Grade.lean` uses Space.
- `Krylov/LinearSystems/Galerkin.lean` uses the Matrix layer only (`Pinv`, `QuadForm`, through them
  `Projector`).
- `Krylov/LinearSystems/CG.lean` uses Grade, Galerkin, `Matrix/Functions/Polynomial`,
  `Matrix/Pseudoinverse/ConditionNumber`, `Polynomial/Chebyshev/Residual`, ForMathlib `Div`.
- `Krylov/Processes/Lanczos.lean` uses Grade, `GramSchmidt`, `Hessenberg` (Processes import only
  Krylov/Basic and the Matrix layer).
- `Krylov/Processes/LanczosRecurrence.lean` uses Lanczos.
- `Krylov/LinearSystems/CGRecurrence.lean` uses CG.
- `Krylov/LinearSystems/CGLanczos.lean` uses CG and LanczosRecurrence.

| File | Definitions + theorems | Built lines | Expected when proved |
|---|---|---|---|
| `Matrix/Basic/Projector.lean` (addition) | 0 + 1 | +19 | proved |
| `Matrix/Factorizations/GramSchmidt.lean` (additions) | 0 + 4 | +49 | +150 |
| `Krylov/Basic/Space.lean` | 2 + 8 | 110 | 250 |
| `Krylov/Basic/Grade.lean` | 1 + 8 | 97 | 300 |
| `Krylov/LinearSystems/Galerkin.lean` | 1 + 8 | 153 | 300 |
| `Krylov/LinearSystems/CG.lean` | 1 + 13 | 225 | 400 |
| `Krylov/Processes/Lanczos.lean` | 2 + 12 | 153 | 450 |
| `Krylov/Processes/LanczosRecurrence.lean` | 6 + 3 | 119 | 500 to 700 |
| `Krylov/LinearSystems/CGRecurrence.lean` | 3 + 8 | 141 | at least 400 |
| `Krylov/LinearSystems/CGLanczos.lean` | 0 + 2 | 62 | 80 |

Placement. `galerkinInverse` has no Krylov vocabulary but its topic is projection methods for
linear systems, looked for beside CG and GMRES; alternative home `Matrix/Pseudoinverse/`, not
taken because every consumer is an iterative method. The bridge lemma is a column-space fact and
goes beside `rangeProjector_mulVec_eq_zero_iff`; the Gram–Schmidt lemmas go to Gram–Schmidt. The
CG corollaries of the Lanczos basis get their own file so that Processes stays below
LinearSystems. No placement flag is open. Smaller than the brief's K0 estimate: shift
invariance, compression lemmas and $\nu \le \deg\mu_{\mathbf{A}}$ wait for K1 and K4.

Parallel proving. Space and Grade first (small; Galerkin can run beside them). Then two agents on
disjoint files: agent A on Galerkin, CG, CGRecurrence; agent B on the GramSchmidt additions,
Lanczos, LanczosRecurrence. CGLanczos last, a few lines once both chains are done.

Records. `docs/design/Mathlib-deviations.md` lists the additions (Krylov space beside
`Module.AEval'`, the grade, the methods, the recurrences; no numbered deviation). CONTRIBUTING
§5.3 "location of the spectrum" is amended to the maintainer's decision of 2026-10-17. Rows for the
Krylov objects join §5.3 in the PR that proves them. Bibliography: `HestenesStiefel1952` and
`Paige1972` added; `Saad2003`, `Saad2011` and `TrefethenBau1997` locators are from the prototype
and the brief, to verify against the books before the PR. Prototype material reused as
mathematics: `Spaces.Polynomial`, `Spaces.Grade`, `Solvers.Minimizer`, `Solvers.CG`,
`Processes.Arnoldi`, the proved halves of `CGRecurrence` and `LanczosRecurrence`; not reproduced:
`IsAffineMinimizer`, `IsCGIterate`, `cgObjective`, `ArnoldiDecomp`, `LanczosDecomp`, `krylovSeq`,
`arnoldiBasis`, `stoppedArnoldiMatrix`, raw eigenvalue hypotheses, `Nat.iterate`.

## 7. Open questions for the maintainer

1. **Hypothesis-free realisation theorems.** The Lanczos realisation holds for every $q$ because
   the frozen recurrence and the zero-padded basis agree past the grade; the textbook form carries
   `q ≤ krylovGrade A b`. The free form implies the other at once but commits the library to the
   zero padding of D7. [Hypothesis free.]
2. **Paige's order in `lanczosStep`.** The stable variant, which a later finite-precision round
   would analyse as is. [Keep it.]
3. **Error spelling.** Squared `RCLike.re (quadForm A (xs - y))`, as
   `Matrix.IsHermitian.re_quadForm_aeval_aeval_mulVec_le`, rather than a new `energyNorm` row.
   [Squared `quadForm`.]

## 8. Consumers

`galerkinInverse`: CG; PCG, CGLS, block and deflated CG later; Nyström PCG through PCG.
`cgIterate` and its rate: PCG (K2), sketch-and-precondition (K6) through CGLS, Lanczos-FA for
$1/x$ (K1). The error polynomial and the comparison: MINRES and polynomial iterations (K2).
`IsGradedKrylovBasis`, `arnoldiMatrix`, `mul_arnoldiMatrix`: Arnoldi and GMRES (K3), Ritz values
(K4), SLQ (K7). `lanczosState`: SLQ's implementation statement and a finite-precision round.
`cgState`: the exhibited algorithm, needed by no later theorem by design.

## Implementation (2026-10-17)

All files of §6 are proved and registered in `NLAlib.lean`. No statement of this note changed;
the amendments are additions and placement.

- **Space** (`Krylov/Basic/Space.lean`): three public lemmas beyond §3.2,
  `krylovSpace_eq_span` (the span of $\mathbf{A}^j\mathbf{b}$, $j < q$),
  `pow_mulVec_mem_krylovSpace` ($\mathbf{A}^j\mathbf{b} \in \mathcal{K}_q$ for $j < q$) and
  `krylovSpace_succ` ($\mathcal{K}_{q+1} = \mathcal{K}_q + \operatorname{span}\{\mathbf{A}^q\mathbf{b}\}$),
  used by Grade, Lanczos and CGRecurrence.
- **Gram–Schmidt** (`Matrix/Factorizations/GramSchmidt.lean`): three public lemmas beyond §3.1,
  `gramSchmidtQ_col_eq_zero_iff` (a column vanishes iff its `gramSchmidtR` diagonal entry does),
  `gramSchmidtQ_mul_conjTranspose_gramSchmidtQ_mul_self`
  ($\mathbf{Q}\mathbf{Q}^{\mathsf{H}}\mathbf{Q} = \mathbf{Q}$, no rank assumption) and
  `gramSchmidtQ_col_bot` (the first column is the normalised first column).
- **Placement of the constructor.** `isGradedKrylovBasis_of_forall_col_mem` lives in
  `Krylov/Processes/Lanczos.lean`, beside `IsGradedKrylovBasis`, not in Grade.
- **Lanczos realisation.** Proved directly, not through `IsGradedKrylovBasis.eq_arnoldiMatrix`:
  an induction shows that the recurrence state equals a canonical state built from the columns
  $\mathbf{q}_j$ of `arnoldiMatrix` and their Gram–Schmidt coefficients $r_j \ge 0$. The step
  works because $r_j\mathbf{w} - r_{j+1}\mathbf{q}_{j+1}$ lies in $\mathcal{K}_{j+1}$ and is
  orthogonal to $\mathbf{q}_0, \dots, \mathbf{q}_j$, hence is zero; this covers the steps past
  the grade, where both sides are zero, with no case split on breakdown.
- **Hestenes–Stiefel route.** Two hypothesis-free invariants, for every $\mathbf{A}$:
  $\mathbf{x}_k - \mathbf{x}_0 \in \mathcal{K}_k$ and $\mathbf{p}_k - \mathbf{r}_k \in \mathcal{K}_k$.
  Then one joint induction for positive definite $\mathbf{A}$: $\mathbf{r}_k \perp \mathcal{K}_k$
  and $\mathbf{A}\mathbf{p}_k \perp \mathcal{K}_k$. `cgState_x_eq` follows with no further
  induction from the Galerkin characterisation
  `Matrix.PosDef.eq_cgIterate_of_conjTranspose_krylovMatrix_mulVec_sub_eq_zero`.
- **Moves to the Matrix layer** (placement, CONTRIBUTING §8 item 5): private helpers of the Krylov
  files became public lemmas where their topic lives.
  `conjTranspose_mul_apply` ($(\mathbf{A}^{\mathsf{H}}\mathbf{B})_{i,j} =
  \mathbf{a}_i^{\mathsf{H}}\mathbf{b}_j$; it was private twice, in Lanczos and LanczosRecurrence;
  `conjTranspose_mul_self_apply` is now its specialisation) and `conjTranspose_mul_mul_apply`
  (the compression entry $\mathbf{q}_i^{\mathsf{H}}\mathbf{A}\mathbf{q}_j$) go to
  `Matrix/Basic/Gram.lean`. Mathlib has only `Matrix.mul_apply'` (a row against a column)
  and the square `Matrix.mul_mul_apply`. `HasOrthonormalCols.star_col_dotProduct_eq_zero_of_mem_span`
  (a column is orthogonal to the span of the others) goes to `Matrix/Basic/Orthonormal.lean`;
  searched, none. `krylovGrade_le_of_mem_of_mulVec_eq` ($\nu \le k$ when
  $\mathbf{c} = \mathbf{A}\mathbf{y}$, $\mathbf{y} \in \mathcal{K}_k(\mathbf{A}, \mathbf{c})$) moves
  from CGRecurrence to `Krylov/Basic/Grade.lean`. The public name `conjTranspose_mul_mul_apply`
  clashed with a private helper of `Sketching/Properties/Isotropic.lean` stating the entry as a
  double sum; that helper is renamed `conjTranspose_mul_mul_apply_eq_sum`, statement unchanged.
  No placement flag is open.

Final counts (public definitions + public theorems; lines):

| File | Definitions + theorems | Lines (whole file) |
|---|---|---|
| `Matrix/Basic/Gram.lean` (additions) | 0 + 2 | 178 |
| `Matrix/Basic/Orthonormal.lean` (addition) | 0 + 1 | 342 |
| `Matrix/Factorizations/GramSchmidt.lean` (additions) | 0 + 7 | 440 |
| `Krylov/Basic/Space.lean` | 2 + 11 | 169 |
| `Krylov/Basic/Grade.lean` | 1 + 9 | 242 |
| `Krylov/LinearSystems/Galerkin.lean` | 1 + 8 | 197 |
| `Krylov/LinearSystems/CG.lean` | 1 + 13 | 288 |
| `Krylov/Processes/Lanczos.lean` | 2 + 12 | 236 |
| `Krylov/Processes/LanczosRecurrence.lean` | 6 + 3 | 466 |
| `Krylov/LinearSystems/CGRecurrence.lean` | 3 + 8 | 367 |
| `Krylov/LinearSystems/CGLanczos.lean` | 0 + 2 | 58 |
