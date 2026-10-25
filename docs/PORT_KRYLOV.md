# Port brief: the Krylov round

For the orchestrating agent building `NLAlib/Krylov/` and the single-vector randomized and iterative
material that lands in `Estimation/`, `Regression/` and `Solvers/`. Read `CONTRIBUTING.md` in full
first (§5.2 "Numerical bounds" and "Asymptotic forms", §5.3, §5.4, §8), then
`docs/PORT_LOWRANK.md` (its D1, D2, D11 and §8), `docs/PORT_POLYNOMIAL.md` (§3, §5),
`docs/design/Polynomial-Jackson-Moments.md` and `docs/design/Mathlib-deviations.md`.

Status: **draft, 2026-10-17, revised the same day** after an independent review and the
maintainer's directions below. §2 holds the decisions for the maintainer, cited "D1" to "D12";
some are already settled by his directions and say so. §3 is decided by the orchestrator and open
to correction (cited "O1" to "O10"). Stage K0, the CG slice, is the plan in detail and the design
checkpoint for the whole round; stages K1 to K9 are a roadmap, sized roughly.

## Maintainer directions (2026-10-17)

Verbatim: "I dont want to define algorithms by formulas that are computable (in the NLA sense of
this word). So for instance, CG can be defined as Q(Q'AQ)^{-1}Q'b where Q is any onb. This will, in
particular, show that the "Lanczos basis" yields CG. I also want to show that the standard
implementations yield the algorithm, although I'm not so clear how this works. Do we have something
similar for gram-schmidt and householder? Do not do the randomized stuff that requires block
methods yet. But we should think about how we are going to generalize this to block methods. Does
it make sense to have a single definition? Or to later show the regular one is a special case."

Then: "let's focus first on just getting the CG infrastructure so that we don't expend too much
effort. I want to see how everything fits together, since I think this will be one of the bigger
design choices in the project".

Read as: methods are defined mathematically, not as computable procedures; CG is
$\mathbf{Q}(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})^{-1}\mathbf{Q}^{\mathsf{H}}\mathbf{b}$ for any
orthonormal basis $\mathbf{Q}$ of the Krylov space. What changed in the brief:
- D3 (methods are basis-free definitions, frame form as the first theorem) is **confirmed**;
- D4: realisation theorems for the standard implementations are **in this round**; the Lanczos
  and Hestenes–Stiefel ones are in the CG slice. D4 answers the Gram–Schmidt and Householder
  question from the library's own precedent and explains how a realisation theorem works;
- the first stage is the **CG slice only** (stage K0, §8), the design checkpoint for the round;
  everything after it is a roadmap, kept brief;
- randomized methods that need block Krylov or block subspace iteration are **out of this round**
  (D11); the `rsvd` unification is kept as the design for that later round (§4);
- D10 answers the block-generalisation question.

Inputs: two read-only surveys of this session (the prototype's Krylov layer; the library, Mathlib
and the scope), `~/Documents/prove2me/lean/docs/KRYLOV_DEFINITIONS.md`, the local PDFs of
Martinsson–Tropp and Tropp–Webber, and the tree at `b0f4a2c` (origin/main). Every library and
Mathlib name below was checked by grep; names marked *new* do not exist yet.


**Decisions (2026-10-17).** The maintainer: "D8: I think the interval and union should be the same
format. For the others the default is fine. Let's just proceed with the CG stuff and then I will
examine". So D1 to D7 and D9 to D12 are approved as recommended, and D8 is amended: every spectral
location hypothesis of the round, interval or union, is `spectrum ℝ A ⊆ s` for Hermitian
$\mathbf{A}$, with `s = Set.Icc a b` for an interval and a union of intervals for the indefinite
case; polynomial bounds are `∀ x ∈ s, |p.eval x| ≤ M`, the form of
`Matrix.IsHermitian.specNorm_aeval_le` in `Matrix/Functions/Polynomial.lean` (whose `Icc` corollary
`specNorm_aeval_le_of_forall_mem_Icc` takes the Loewner form). The
Loewner sandwich `a • 1 ≤ A`, `A ≤ b • 1` is reached by a bridge lemma
(`spectrum_subset_Icc_of_le`, and Mathlib's `le_algebraMap_iff_spectrum_le`,
`algebraMap_le_iff_le_spectrum` for the converse), so callers holding Loewner bounds still apply the
theorems in one step. `A.PosDef`, ranged `eigenvalue A k` and the eigenvector form are unchanged.

## Maintainer directions (2026-10-18, block round)

The block round (`docs/design/Krylov-Block.md`, branch `krylov/block`) reopened D11 at the
maintainer's request. His directions, in order:
- "let's build block krylov and then work towards formalizing the bounds in Tropp Webber": block
  Krylov spaces first (one block definition beside the vector one, D10(c), BD1 (b)), then Tropp and
  Webber's Theorems 9.1 and 9.2 for RBKI and RSI;
- the bounds should also hold for the truncated outputs, borrowing from Musco and Musco where
  needed (late truncation `truncatedSVD (alg …) r`; early truncation if natural, deferred as BD6);
- on the design note: "the gapless bounds are more important, but it is okay to defer them if its
  a big task. other stuff looks good" (BD1 to BD9 approved as recommended; gapless bounds
  prioritised, both the Tropp–Webber form and the Musco–Musco $(1 + \varepsilon)$ form proved);
- next: the upper bound of Bakshi, Clarkson and Woodruff (arXiv:2202.05120), Theorem 5.1 only; the
  lower bounds are a separate later project, from a newer paper.

## Progress (2026-10-18)

The stages were renumbered when designed: the roadmap's "K2 GMRES, MINRES, CGLS, PCG" and "K3
Arnoldi" became stage K1 (`docs/design/Krylov-LinearSystems.md`), its "K1 Lanczos-FA" became K2
(`Krylov-Functions.md`), and K2b (`Krylov-Sharpness.md`) was added for sharpness.

Done, all proved, branch `krylov/block` (2026-10-18; `Krylov-Block.md`, Implementation):
- **Block round B0 to B7**: `blockKrylovMatrix`, `blockKrylovSpace` and their one-column, CG,
  shift, change-of-variables and polynomial bridges (`Krylov/Basic/BlockSpace.lean`); `rbki` and
  `nystromBKI` (`LowRank/Structural/BlockKrylov.lean`); Tropp–Webber Lemma 9.5, the filtered range
  finder, deterministic and in expectation; TW Theorem 9.2 (gapped) for RBKI and RSI in the spectral,
  Frobenius and every quadratic unitarily invariant norm, with the late-truncated spectral and
  Frobenius lines; the gapless bounds in TW's Theorem 9.1 form and in the Musco–Musco
  $(1 + \varepsilon)$ form (truncated and untruncated, with the asymptotic depth
  $O(\log(\lvert n \rvert/\varepsilon)/\sqrt{\varepsilon})$); the Nyström variants through the Gram
  correspondence. Later targets, among them MM Theorems 1 and 11 to 13 and BCW Theorem 5.1, are listed
  in the note.

Done, all proved, branch `krylov/brief`:
- **K0**, the CG slice (`Krylov-CG.md`): Krylov space and grade, `galerkinInverse`, `cgIterate`,
  the canonical Arnoldi/Lanczos basis, the Lanczos and Hestenes–Stiefel realisations.
- **K1**, checkpoints 1 to 5: CG with a start, PCG and its recurrence, CGLS, the rates in
  $\kappa$, outliers and the spectrum-optimal bounds through `residualMinimax`; GMRES, MINRES and
  preconditioned MINRES; MGS Arnoldi, preconditioned Lanczos, GMRES through Givens QR and back
  substitution, the Paige–Saunders recurrence; the Chebyshev worst cases on one and two intervals.
- **K2**, checkpoints C1 to C5: compressions, `lanczosFA`, Stieltjes functions, Chen–Persson
  Theorems 5 and 1 with their $\kappa$, Euclidean and CG forms.
- **K2b**: Greenbaum's theorem for CG and MINRES on every spectrum (discrete minimax duality),
  and Chen–Persson Theorem 2 (the near-optimality factor is optimal) with its CG case.

Remaining: K2 C6 (Gauss quadrature for $\mathbf{b}^{\mathsf{H}}\,\mathsf{lanczosFA}$); K1's
deferred items (L12: MINRES-QLP, the general two-interval bound, real GMRES with complex
eigenvalues, Richardson and Chebyshev iterations); Greenbaum–Gurvits for GMRES with normal
matrices (`Krylov-Sharpness.md` question 2); and the roadmap of §8 from K4 on (Ritz values and
eigenvalue bounds, random-start power and Lanczos, sketched solvers, Hutch++ and SLQ, Nyström PCG,
Kaczmarz and sketch-and-project). Block methods beyond the block round (block Lanczos, CG and
GMRES, BD2) stay deferred.

## Maintainer decisions

Only the directions above so far. Answers to §2 and §10 are recorded here, dated, before any
skeleton depends on them.

## 0. The request and how this brief reads it

The request, verbatim: "I think a good next step is to work on Krylov. Look at the prototype and
decide if the way it defines stuff is reasonable or not. We will need stuff for not only classical
iterative methods but also randomized methods. Make a plan. I will review".

Standing context: usefulness over transcription (statements downstream proofs can apply, unified
interfaces); every departure from Mathlib gets a justified entry in
`docs/design/Mathlib-deviations.md`; very complex material waits when lower layers lack
infrastructure; the LowRank round left power and subspace iteration, randomized block Krylov
(RBKI) and randomly pivoted Cholesky for later (`PORT_LOWRANK.md` §8).

**Verdict in one paragraph.** The prototype's philosophy is right and is kept: methods are
optimality statements over a Krylov space; processes are an orthonormal basis graded by the Krylov
spaces; breakdown is measured by one number, the grade; downstream theorems take "any `Q` with
orthonormal columns whose range contains the Krylov space"; recurrences are secondary. Its
execution is not kept: everything except the spaces is real and transpose-based; there is no Krylov
*matrix*, so nothing connects to `rangeProjector`, `rank`, `gramSchmidtQ`, `pinv` or the
measurability lemmas; bases, compressions, Ritz values and angles exist in parallel spellings;
spectral hypotheses are raw eigenvalue conditions; and every theorem saying "this recurrence
computes that iterate" is unproved. The most useful change is a Krylov matrix `krylovMatrix A b q`,
through which the space, the grade, the projector, the method definitions and the Arnoldi basis
are all expressed in the existing Matrix vocabulary.

## 1. The prototype's definitions: what to keep, change, drop

The prototype's `NLAlib.Krylov` has 470 declarations in 33 files (8390 lines), sorry-free except
for 8 direct scaffolds and 17 declarations flagged through them: the realisations of the CG,
Lanczos and Golub–Kahan recurrences, one QR-algorithm bridge and one angle bridge. Each table gives
the prototype spelling, the problem, the new spelling and the reason. "Keep" means keep the
mathematics and the interface; the spelling always moves to `𝕜`, `ᴴ` and the §5.3 vocabulary.

### 1.1 Krylov space and grade: keep the concept, change the definition

| Prototype | Problem | New | Reason |
|---|---|---|---|
| `krylovSpace A b q`, the `Submodule.span` of $\mathbf{A}^i\mathbf{b}$, $i < q$, any field | no matrix whose range it is, so no projector, rank, Gram–Schmidt, pseudoinverse or measurability lemma applies | *new* `krylovMatrix A b q : Matrix n (Fin q) 𝕜` with column $j$ equal to $\mathbf{A}^j\mathbf{b}$; `krylovSpace A b q` defined as its column space; the span form a lemma | D2 |
| `mem_krylovSpace_iff`: $\mathbf{x} = p(\mathbf{A})\mathbf{b}$, `p.degree < q`, same field | spectral bounds want real polynomials | `mem_krylovSpace_iff` over `𝕜[X]`, plus a corollary for `p : ℝ[X]` | D1 |
| `q` counts generators, $\mathcal{K}_0 = \{0\}$ | none | kept | every consumer uses it |
| `krylovGrade A b`, `finrank ℝ` of the span of all powers; full API | real only; $\{q \le \nu\}$ not visibly measurable | `krylovGrade A b := (krylovMatrix A b (Fintype.card n)).rank`; the API ported over `𝕜` | `measurable_rank` gives measurability (D7) |

### 1.2 Block Krylov space: keep for the block round

| Prototype | Problem | New | Reason |
|---|---|---|---|
| `blockKrylovSpace A Ω q`, `range_aeval_mul_le_blockKrylovSpace` | no matrix, so it cannot be a test matrix | later: *new* `blockKrylovMatrix A B q : Matrix n (Fin q × s) 𝕜` with a bridge to `krylovMatrix` at one column | D10; block methods are out of this round |
| `subspaceIterate A Ω k := range (A ^ k * Ω)` | a name for a column space | no definition: `LinearMap.range (A ^ k * Ω).mulVecLin` | §5.3 "column space" row |

### 1.3 Krylov bases and matrices: one canonical matrix, drop four objects

| Prototype | Problem | New | Reason |
|---|---|---|---|
| `krylovSeq` in `EuclideanSpace` | transport in statements | dropped | §5.1 vectors |
| `arnoldiBasis A b j`, Mathlib Gram–Schmidt over ℕ, zero from the grade on | reimplements the Matrix layer | *new* `arnoldiMatrix A b q := gramSchmidtQ (krylovMatrix A b q)`; column $j$ is the same for every $q > j$ | `gramSchmidtQ` is over `𝕜`, zero at dependencies, measurable |
| `stoppedArnoldiMatrix`, `Fin (min q (krylovGrade A b))` columns | column type depends on $\mathbf{b}$ | dropped | D7 |
| `orthonormalBasisMatrix (krylovSpace A b q)` | arbitrary, not measurable | dropped; definitions are basis-free and frames are hypotheses | D3 |
| `krylovCoefficientVector A b c` | stand-in for a missing matrix | `krylovMatrix A b q *ᵥ c` | one spelling |

### 1.4 Arnoldi and Lanczos decompositions, relations and recurrences: change

| Prototype | Problem | New | Reason |
|---|---|---|---|
| structure `ArnoldiDecomp A b q` (fields `Q`, `graded`), `D.H`, `D.restrict`, `D.Hbar`, `LanczosDecomp := ArnoldiDecomp`, witness `arnoldiDecomp A b q h` | `Fin.castLE` and `restrict` in every relation; the alias breaks dot notation; existence needs a grade hypothesis | the prototype's predicate `IsGradedKrylovBasis A b Q`, kept with its name and the wrapper dropped; canonical `arnoldiMatrix`; compression written `Qᴴ * A * Q` | D5 (reverses a prototype decision of the maintainer) |
| Hessenberg in three spellings, tridiagonal in two | parallel; none concludes a predicate | `hQ.isUpperHessenberg : IsUpperHessenberg (Qᴴ * A * Q)`; `IsTridiagonal` for Hermitian $\mathbf{A}$ | the Matrix layer has both |
| relation $\mathbf{A}\mathbf{Q}_q = \mathbf{Q}_{q+1}\underline{\mathbf{H}}_q$ only up to the grade | needs a decomposition of size $q+1$ | for every $q$: `A * arnoldiMatrix A b q = arnoldiMatrix A b (q + 1) * ((arnoldiMatrix A b (q + 1))ᴴ * A * arnoldiMatrix A b q)` | $\operatorname{range}(\mathbf{A}\mathbf{Q}_q) \subseteq \mathcal{K}_{q+1}$, and $\mathbf{Q}_{q+1}\mathbf{Q}_{q+1}^{\mathsf{H}}$ is the projector onto $\mathcal{K}_{q+1}$ (its nonzero columns are orthonormal); at and past the grade $\mathcal{K}_{q+1} = \mathcal{K}_q$ is $\mathbf{A}$-invariant, so nothing is lost |
| `exists_sign`, `Q_eq_of_pos` | real signs | unimodular scalars, `HasOrthonormalCols.exists_eq_mul_diagonal_of_isUpperHessenberg`; positive normalisation through `IsQR.unique` | exists in the Matrix layer |
| coefficients twice (`LanczosDecomp.alpha/beta`, `lanczosAlpha/lanczosBeta`), bridged by a scaffold | two vocabularies | entries of `Qᴴ * A * Q`; for the canonical matrix $\alpha_j$ real, $\beta_j > 0$ below the grade | one vocabulary |
| `LanczosState`, `lanczosStep`, `lanczosRecurrence`; realisation a scaffold | unproved | recurrences with proved realisation theorems: Lanczos in stage K0, Arnoldi in K3 | D4 |

### 1.5 Golub–Kahan bidiagonalisation: defer

| Prototype | Problem | New | Reason |
|---|---|---|---|
| `GolubKahanDecomp A b k` (two graded bases, two grade hypotheses); `golubKahanRecurrence` (three scaffolds) | no consumer; bundling artefact | later: `arnoldiMatrix (A * Aᴴ) b (k + 1)` and `arnoldiMatrix (Aᴴ * A) (Aᴴ *ᵥ b) k`; its recurrence realised as in D4 | CGLS needs only CG on the normal equations |

### 1.6 CG: keep the design, change the definition

| Prototype | Problem | New | Reason |
|---|---|---|---|
| local predicate `IsAffineMinimizer E x₀ S x` with an `IsMinOn` bridge | a local interface where the library decided against one (`isLeastSquaresSolution_iff_isMinOn`: "no separate predicate") | none; `IsMinOn` is a theorem about the defined iterate | D3 |
| `IsCGIterate A c x₀ q x` with `cgObjective`; `exists_isCGIterate` | an iterate exists by choice; none is canonical or measurable | *new* `cgIterate A b q`, basis-free; error spelled `xs - cgIterate A b q` | D3 |
| bound with `∀ i, |p.eval (hA.eigenvalues i)| ≤ M` | raw spectral hypotheses | Loewner sandwich and `∀ x ∈ Set.Icc a b, |p.eval x| ≤ M`, as `re_quadForm_aeval_mulVec_le` | D8 |
| `CGState`, `cgStep`, `cgRecurrence`; `isCGIterate_cgRecurrence` unproved | unproved | Hestenes–Stiefel with its realisation, stage K0 | D4 |

### 1.7 GMRES, MINRES, FOM, CGLS: keep the content, respell

| Prototype | Problem | New | Reason |
|---|---|---|---|
| `IsGMRESIterate` (residual form, every $\mathbf{A}$), Petrov–Galerkin iff | choice of iterate; real | *new* `gmresIterate A b q`, basis-free; residual `(1 - rangeProjector (A * krylovMatrix A b q)) *ᵥ b` | D3 |
| MINRES as GMRES with `A.IsHermitian` | none | kept: Hermitian theorems about `gmresIterate` | one spelling |
| `dotProduct_le_of_eq_mul_diagonal_mul` (real diagonalisable) | excludes complex eigenvalues | `IsDiagonalizable` over ℂ through `complexify` | `IsDiagonalizable` exists |
| `GMRESArnoldi` through `ArnoldiDecomp` and `Hbar` | bundled | a frame-form lemma on `arnoldiMatrix` (stage K3) | D5 |
| `IsCGLSIterate` | a second predicate | `cgIterate (Aᴴ * A) (Aᴴ *ᵥ b) q` | one spelling |
| FOM breakdown is non-existence of an iterate | no total value | the Galerkin definition returns its junk value through `pinv` (D3) | CONTRIBUTING §5.2 totality |
| Petrov–Galerkin predicates planned, never introduced | no consumer | nothing this round | CONTRIBUTING §8 item 4 |

### 1.8 The polynomial characterisation: keep

| Prototype | Problem | New | Reason |
|---|---|---|---|
| residual algebra, `IsAffineMinimizer.le_aeval`, the weighted class theorem | real only | over `𝕜`; the spectral step is `Matrix.IsHermitian.re_quadForm_aeval_aeval_mulVec_le`, already ported | D1 |
| `polyIterate`, `richardsonIterate`, `chebyshevIterate` (polynomial definition, recurrence theorem) | none | kept; `chebyshevIterate` from `chebyshevResidual` | the same pattern as D4 |
| degrees `< q` (membership), `≤ q` with `eval 0 = 1` (residuals), `< 2 * q` (Gauss); one `natDegree` | the exception | kept, exception removed | one convention |

### 1.9 Ritz values and measurability: change

| Prototype | Problem | New | Reason |
|---|---|---|---|
| `(Matrix.isHermitian_transpose_mul_mul Q hA).eigenvalues j` in statements | proof term in a statement (§5.2) | `eigenvalue (Qᴴ * A * Q) k` | §5.3 eigenvalue row |
| `ritzValues hA Q hQ` with an unused proof argument | proof-carrying definition | dropped | same |
| `lanczosRitzValue A b q`, top only, measurable by a rational supremum | arbitrary basis; does not extend to interior values | projector form `eigenvalue (rangeProjector K * A * rangeProjector K) k`, `K = krylovMatrix A b q` | D9 |
| "the largest" through `hj₁ : ∀ j, θ j ≤ θ j₁` | index hypothesis | index `0` | §5.3 |
| Ritz vectors never defined | none | only with a consumer | §5.2 eigenvector rule |

### 1.10 Gauss quadrature, Lanczos-FA, spectral measure, Jacobi layer

| Prototype | Problem | New | Reason |
|---|---|---|---|
| `krylovFunApprox A f b Q` on any frame, exactness, `krylovFunApprox_congr` | real; depends on a frame argument | *new* `lanczosFA A f b q`, basis-free; the frame form as its first theorem | D3 |
| basis-free quadrature, exactness for degree $< 2q$, error $2\varepsilon\|\mathbf{b}\|^2$ | real | `RCLike.re (star b ⬝ᵥ lanczosFA A f b q)`, frame form a lemma | one functional |
| `spectralMeasure hA v` from `eigenvectorBasis` | arbitrary eigenbasis, no uniqueness lemma | `Matrix/Spectral`, characterised by its integrals | D6 |
| Jacobi layer (Lanczos polynomials, Christoffel–Darboux, Golub–Welsch, `jacobiMatrix`), outside the default import by accident | `eigenvectorBasis` in statements | D6 | D6 |

### 1.11 Power method, subspace iteration, QR algorithm

| Prototype | Problem | New | Reason |
|---|---|---|---|
| `powerIterate A x₀ k := Aᵏ x₀`, `powerStep`, `inverseIterate` | names for powers | `A ^ k *ᵥ x₀` | nothing to name |
| seven tangent functions, two `Complex*` twins | parallel spellings | subspaces: `tangentMatrix U Y`; a vector against an eigenvector: the overlap ratio $\|\mathbf{b}\|^2/\lvert\langle\mathbf{u},\mathbf{b}\rangle\rvert^2$ written out | §5.3; `GaussianLogOverlap.lean` |
| HMT 9.2, HMT 10.7, `SubspaceConvergence` twins | block subspace iteration | later (block round), as `rsvd A ((Aᴴ * A) ^ q * Ω)` | maintainer's directions; §4 |
| `qrAlgorithm qr μ A` | a dense eigensolver | later, `Matrix/Factorizations` | placement |

### 1.12 Preconditioned CG: keep

| Prototype | Problem | New | Reason |
|---|---|---|---|
| `IsPCGIterate`, `isPCGIterate_iff_isCGIterate` (any `W`), sandwich bound | real; a third predicate | the Galerkin definition on `krylovMatrix (M⁻¹ * A) (M⁻¹ *ᵥ b) q`; split form a lemma; bound from the §5.3 "spectral equivalence" row | D3 |
| `exists_isSymm_transpose_mul_mul_eq_one` | duplicates Mathlib | `(CFC.sqrt M)⁻¹`, `Matrix.PosDef.inv_sqrt_eq_cfc` | Mathlib first |
| `krylovSpace_mul_mulVec_eq_map` | none | kept (stage K2, with PCG) | a Krylov-space fact |

### 1.13 Sketch-and-project: move and redesign

| Prototype | Problem | New | Reason |
|---|---|---|---|
| `SketchProject.step` with `moorePenroseInverse`; `expErr`; `pathPMF`, `pathLaw`, `iidPathPMF`, `iidPathLaw`, `sketchLaw`, `meanProjector` | not Krylov; two presentations; expectation hidden in a recurrence | `Solvers/`: the step with `pinv`; i.i.d. sketches on `Measure.infinitePi`; Bochner integral; Loewner hypothesis on the expected projector | stage K9 |

**Proof material worth reusing:** the grade API; residual algebra and GMRES uniqueness; CG existence
and uniqueness; the compression lemmas (`transpose_mulVec_aeval_mulVec_eq`, Gauss exactness,
interpolation at Ritz values); graded-basis structure theory; the recurrence step lemmas of
`LanczosRecurrence` and `CGRecurrence` (the proved halves); Kaniel–Paige–Saad and gap-free Ritz
bounds; the PCG reduction; the Kuczyński–Woźniakowski analysis. Not ported as is: `restrict`
plumbing, `stoppedArnoldiMatrix`, `ritzValues`, `lanczosRitzValue`, the angle functions, the
`eigenvectorBasis` coordinate helpers, the `Complex*` files, the path laws.

## 2. Decisions for the maintainer

Each gives options, a recommendation and the cost of reversing it later.

**D1. Scalars and polynomials.**
- Options: (a) ℝ throughout (prototype); (b) `𝕜` with `𝕜[X]` everywhere; (c) `𝕜` for every
  deterministic statement, `𝕜[X]` where a polynomial is produced (membership, the GMRES optimal
  polynomial), `ℝ[X]` where one is supplied to a Hermitian spectral bound (as
  `Matrix/Functions/Polynomial.lean` does), bridged by `Polynomial.aeval_map_algebraMap`; random
  starts real, because `gaussianVector` is.
- Recommendation: (c). Non-normal GMRES bounds go through `complexify` and `IsDiagonalizable`.
- Rework: (a) to `𝕜` later rewrites every statement; (c) to (b) is mechanical.

**D2. The Krylov matrix as the primary object.**
- Options: (a) the space as a `Submodule.span` with a matrix bridge; (b) the matrix only, the space
  always written as a range; (c) the matrix as the definition and `krylovSpace A b q` a named `def`
  equal to its column space, with the span and polynomial forms as lemmas; the §5.3 row reads
  "Krylov space: `krylovSpace A b q`, the column space of `krylovMatrix A b q`".
- Recommendation: (c). The matrix plugs the space into `rangeProjector`, `rank`, `pinv`,
  `gramSchmidtQ` and the measurability lemmas; the name keeps statements readable. Mathlib has no
  Krylov space; its nearest notion, the cyclic submodule in the type synonym `Module.AEval'`, is
  unusable in statements about vectors (deviation entry 5's reasoning). An addition, not a
  deviation (O8).
- Rework: low between (a) and (c). Sticky: `q` counting generators and the column type `Fin q`.

**D3. Methods are defined mathematically, basis-free (confirmed by the maintainer's directions).**
- The definitions depend only on the subspace, through `P = rangeProjector X` for a basis matrix
  `X`, so no basis is chosen and nothing is an algorithm:
  - *new* `galerkinInverse A X := pinv (P * A * P)`; for any `Q` with orthonormal columns and
    range equal to that of `X`, it equals $\mathbf{Q}\,(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})^{+}\mathbf{Q}^{\mathsf{H}}$
    (`HasOrthonormalCols.pinv_mul_left`, `HasOrthonormalCols.pinv_mul_conjTranspose_right`);
  - *new* `minResidualInverse A X := pinv (A * P)`: `minResidualInverse A X *ᵥ b` is the
    minimum-norm minimiser of $\|\mathbf{b} - \mathbf{A}\mathbf{y}\|$ over $\mathbf{y} \in \operatorname{range}\mathbf{X}$;
  - *new* `compressedCfc A f X := P * cfc f (P * A * P) * P` for Hermitian $\mathbf{A}$;
  - instances, with `K = krylovMatrix A b q`: `cgIterate A b q := galerkinInverse A K *ᵥ b`,
    `gmresIterate A b q := minResidualInverse A K *ᵥ b`, `lanczosFA A f b q := compressedCfc A f K *ᵥ b`;
    Gauss quadrature is `RCLike.re (star b ⬝ᵥ lanczosFA A f b q)`. A start `x₀` is
    `x₀ + cgIterate A (b - A *ᵥ x₀) q`, no second name. PCG, CGLS and (later) block CG are other
    choices of `X`; sketched GMRES replaces the projection by the existing `sketchAndSolve`.
- The CG slice (stage K0) introduces only `galerkinInverse` and `cgIterate`; the others arrive with
  stages K1 and K2, but the slice's design note fixes the shared shape for all of them.
- First theorems, in this order: the **frame form** (for every `Q` with `HasOrthonormalCols Q`
  whose range is the Krylov space, `cgIterate A b q = Q *ᵥ ((Qᴴ * A * Q)⁻¹ *ᵥ (Qᴴ *ᵥ b))` for
  positive definite $\mathbf{A}$, and `lanczosFA A f b q = Q *ᵥ (cfc f (Qᴴ * A * Q) *ᵥ (Qᴴ *ᵥ b))`);
  then the `IsMinOn` optimality (CG minimises the $\mathbf{A}$-norm error, GMRES the residual);
  then the corollaries "the Lanczos basis yields CG" (`arnoldiMatrix A b q` below the grade, and
  the Lanczos recurrence's vectors, both in stage K0) and "CG is Lanczos-FA for $1/x$" (stage K1; a new
  Matrix lemma: for Hermitian $\mathbf{M}$, `cfc (·⁻¹) M = pinv M`).
- Junk values, stated in the docstrings: when $\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$ is
  singular (indefinite or non-Hermitian $\mathbf{A}$, the FOM breakdown), `galerkinInverse` returns
  $\mathbf{Q}(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})^{+}\mathbf{Q}^{\mathsf{H}}$, which is not
  a Galerkin solution; the prototype treated this case as non-existence.
- Why this spelling (the maintainer asked for a basis-free definition and left the spelling open):
  the projector form is canonical (depends on the space only), total, measurable in $\mathbf{b}$
  through `measurable_rangeProjector` and `measurable_pinv`, uniform across CG, GMRES and Lanczos-FA,
  and block-ready (D10). The error is `xs - cgIterate A b q`, LowRank's "target minus named output".
  It needs no zero-column invariance: the frame form takes a genuine frame, and the bounds of stages
  K0 and K1 are proved there, where the Loewner sandwich holds for $\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$.
- Rework: low; the `IsMinOn` lemmas make predicates a rename.

**D4. Realisation theorems for the standard implementations (in this round, by the maintainer's
directions).**
- The precedent, which answers "do we have something similar for Gram–Schmidt and Householder?":
  yes. The library separates the mathematical object from the algorithm and links them by a
  theorem:
  - QR is the predicate `IsQR A Q R` (`Matrix/Factorizations/QR.lean`), unique with positive
    diagonal (`IsQR.unique`);
  - Gram–Schmidt is `gramSchmidtQ` (Mathlib's `gramSchmidtNormed`) with `isQR_gramSchmidt` under
    full column rank, and the classical recursion as a theorem, `gramSchmidtR_apply_self_smul_col`;
  - Householder is a total recursion `householderState` (`Matrix/Factorizations/Householder.lean`)
    whose realisation theorem `isQR_householder` concludes `IsQR`;
  - Gaussian elimination is `gaussState` with `isLU_luLower_luUpper`, under a hypothesis on the
    computed pivots;
  - CONTRIBUTING §5.3 "algorithm" row: a total recursion indexed by the step, breakdown as a value,
    a realisation theorem under a hypothesis on the computed quantities.
- How a realisation theorem works, for the maintainer's "not so clear how this works":
  1. the algorithm is a total recursion on a state indexed by the step (Lanczos: previous vector,
     current vector, current $\beta$; CG: iterate, residual, search direction), with Lean's
     $0^{-1} = 0$ making a step after breakdown well defined (the state freezes);
  2. invariants are proved by induction on the step: for Lanczos, the computed vectors are
     orthonormal and the first $j+1$ span $\mathcal{K}_{j+1}$, and Hermitian symmetry makes the
     projections onto all but the last two vectors vanish, which is why three terms suffice; for CG,
     $\mathbf{r}_k = \mathbf{b} - \mathbf{A}\mathbf{x}_k$, the residuals and directions span
     $\mathcal{K}_k$, the residuals are orthogonal and the directions $\mathbf{A}$-conjugate;
  3. the hypothesis is that breakdown has not occurred ($\beta_j \ne 0$ for $j$ below the step, which
     is $j <$ the grade), or none where the frozen state already equals the definition (CG past the
     grade sits at the solution);
  4. the conclusion is equality with the mathematical definition: the Lanczos vectors are
     `(arnoldiMatrix A b q).col j` and $\alpha_j, \beta_j$ are the entries of `Qᴴ * A * Q`, proved by
     exhibiting `IsQR (krylovMatrix A b q) Q R` with positive diagonal and applying `IsQR.unique`
     against `isQR_gramSchmidt`; the CG iterate equals `cgIterate A b k`, proved from the frame form
     and the invariants.
- Plan: in the CG slice (stage K0), the Lanczos three-term recurrence realising the Lanczos basis
  and $\mathbf{T}$, and Hestenes–Stiefel CG realising `cgIterate` for every $k$ under `A.PosDef`
  (the cheapest: a joint induction, the prototype's two scaffolds); later, Arnoldi in modified
  Gram–Schmidt form realising `arnoldiMatrix` (stage K3) and Golub–Kahan.
- Options: (a) the plan; (b) only Lanczos and CG; (c) defer all (the brief's first draft).
  Recommendation: (a). Rework: none; additive.

**D5. Arnoldi and Lanczos: a bundled structure or a predicate. This reverses a decision you took in
the prototype** (`KRYLOV_DEFINITIONS.md` §3.12, "the bundled decomposition (maintainer's proposal,
adopted)"; its purpose: $\mathbf{T} = \mathbf{Q}^{\mathsf{T}}\mathbf{A}\mathbf{Q}$ "is a definition,
never a hypothesis").
- Options: (a) keep `ArnoldiDecomp` and `LanczosDecomp` over `𝕜`; (b) the prototype's own
  predicate `IsGradedKrylovBasis A b Q` (orthonormal columns, the first $j+1$ spanning
  $\mathcal{K}_{j+1}$), kept with its name, which is accurate since unimodular column scalars are
  free, and the wrapper dropped; the canonical `arnoldiMatrix` for relations; the compression
  written `Qᴴ * A * Q`, so $\mathbf{T}$ stays an expression and never a hypothesis; (c) the canonical
  matrix only.
- Recommendation: (b).
- Why: the structure's cost was in every signature (`D.restrict`, `Fin.castLE`, the alias breaking
  dot notation) and it forced a grade hypothesis for existence. The prototype's other reasons are
  answered: (ii) "$\mathbf{T}_q$ is the leading section of $\mathbf{T}_{q+1}$": for `arnoldiMatrix`
  it is a nesting lemma (`arnoldiMatrix A b q` is the first $q$ columns of `arnoldiMatrix A b (q + 1)`);
  for any graded basis it holds up to unimodular scalars; (iii) the Jacobi-matrix identities: they
  take the predicate, and this round has no consumer for the bundle partly because D6 defers that
  layer. Most consumers need only a frame (CONTRIBUTING §5.4's example).
- Rework: if you keep (a), a structure wrapping the predicate is added in stage K0 at low cost.

**D6. The Jacobi-matrix, orthogonal-polynomial and spectral-measure layer.** The prototype's
`KRYLOV_DEFINITIONS.md` §3.11 records it as "a layer the maintainer wants explicitly": Lanczos
polynomials orthonormal for $\mu_{\mathbf{b}}$, Gauss nodes and weights from $\mathbf{T}$,
Christoffel–Darboux, the continued fraction, interlacing of $\mathbf{T}_q$ in $\mathbf{T}_{q+1}$.
- Options: (a) defer to a later round, after the Polynomial OP stages; (b) schedule Polynomial OP0
  to OP3 (finite scalar orthogonality, recurrence, Christoffel–Darboux, Gauss exactness;
  `Polynomial-Jackson-Moments.md` §5) and the spectral measure in `Matrix/Spectral` before a
  Jacobi stage after K1, adding about 1500 lines.
- Recommendation: (a), honestly because the scalar OP layer does not exist yet and its design
  checkpoints are pending; matrix-level quadrature (stage K1) and the Lanczos recurrence (K0) do
  not need it. Choose (b) if you want the layer now; it then follows stage K1.
- Rework: none; (a) is additive.

**D7. Breakdown.** (a) The prototype's three devices; (b) `q ≤ krylovGrade A b` everywhere; (c) the
grade as the only vocabulary, zero columns of `arnoldiMatrix` past the grade, no index type
depending on $\mathbf{b}$, and the grade hypothesis only where orthonormality is used (*new*
`hasOrthonormalCols_arnoldiMatrix_iff`). The basis-free definitions of D3 need no hypothesis at all.
Recommendation: (c). Rework: medium (index types).

**D8. Spectral hypotheses (amended by the maintainer 2026-10-17: interval and union both as `spectrum ℝ A ⊆ s`; see Maintainer directions).** (a) The prototype's raw conditions; (b) the §5.3 rows:
an interval is `a • 1 ≤ A`, `A ≤ b • 1`; a union (MINRES, indefinite) is `spectrum ℝ A ⊆ s`;
`A.PosDef`, `A.PosSemidef`; `eigenvalue A k` with ranged indices; eigenvectors as hypotheses
`A *ᵥ u = eigenvalue A 0 • u` with unit norm; polynomial bounds `∀ x ∈ Set.Icc a b, |p.eval x| ≤ M`,
the form of `specNorm_aeval_le_of_forall_mem_Icc`. $\kappa$ forms are corollaries through
`pseudoConditionNumber`. Recommendation: (b), the contract. Rework: high (every statement).

**D9. Ritz values and measurability.**
- Options: (a) the prototype's three forms; (b) statements in frame form,
  `eigenvalue (Qᴴ * A * Q) k`, with basis independence and no new definition; functions of a random
  start in projector form, `eigenvalue (P * A * P) k` with `P = rangeProjector (krylovMatrix A b q)`,
  measurable from `measurable_rangeProjector` and `measurable_eigenvalue`; (c) a named
  `ritzValue A S k` through `svdU` on rank events.
- The bridge is honest only for positive semidefinite $\mathbf{A}$: $\mathbf{P}\mathbf{A}\mathbf{P}$
  has the $r$ Ritz values and $n - r$ zeros, which sort after them, so the two forms agree for
  $k < r = \operatorname{rank}$. For Hermitian $\mathbf{A}$ with $a\mathbf{I} \preceq \mathbf{A}$
  the statement uses the shifted form `eigenvalue (P * (A - a • 1) * P) k + a`, again for $k < r$,
  by shift invariance of the Krylov space. The random-start consumers (MT Theorems 6.1, 6.2)
  assume positive semidefinite $\mathbf{A}$.
- Recommendation: (b); (c) only if a consumer needs interior Ritz values of indefinite matrices as
  random variables. Rework: low.

**D10. Generalising to block methods (the maintainer's question).**
- Options:
  - (a) a single block definition, the vector case as $s$ = `Unit`;
  - (b) vector definitions now, block definitions later, with a bridge lemma that the vector case is
    the one-column case;
  - (c) a split by kind of object: the method definitions of D3 already take a basis matrix `X`
    with any column type and apply to a matrix right-hand side, so they are block-ready and need no
    second definition (block CG is `galerkinInverse A (blockKrylovMatrix A B q) * B`);
    `krylovMatrix A b q` stays a vector definition with `Fin q` columns; `blockKrylovMatrix A B q`
    (columns `Fin q × s`) comes with the block round, with a bridge lemma that for the one-column
    `B` built from $\mathbf{b}$ its range equals that of `krylovMatrix A b q`; scalar-polynomial
    theorems (three-term recurrence, Chebyshev rates, polynomial optimality, grade) are
    vector-specific, and their block analogues (block tridiagonal $\mathbf{T}$ with matrix
    coefficients, matrix polynomials, block grade with deflation) are separate theorems later with
    specialisation lemmas.
- Recommendation: (c); I checked it against the alternatives and agree with it.
- Trade-off: (a) gives one spelling per concept but puts `Fin q × Unit` index types and
  `Matrix.replicateCol` into every vector statement, and the vector theorems would be stated
  through matrix polynomials they do not need; block Lanczos also differs in structure (block
  tridiagonal, rank-deficient blocks, block grade), so a block definition does not specialise for
  free anyway. (b) duplicates the method definitions. (c) unifies exactly where the mathematics is
  the same (projection onto a subspace) and separates where it is not.
- Rework: low for the method definitions; the Krylov matrices are separate by design.

**D11. Scope of the randomized methods (block methods out, by the maintainer's directions).**
- In this round, all single-vector or block-sketch without block Krylov iteration:
  1. random-start power and Lanczos for the largest eigenvalue: gap-dependent and $\log n$ forms
     through the existing log-overlap moments, Kuczyński–Woźniakowski's constants as source
     values of named bounds, the gap-free form with the Chebyshev amplifier;
  2. sketched GMRES and sketched Rayleigh–Ritz on single-vector Krylov bases; sketch-and-precondition
     and iterative sketching (a sketch $\mathbf{S}\mathbf{A}$, no block Krylov);
  3. Hutch++ in expectation (a block sketch $\mathbf{A}\mathbf{S}$ through `rsvd`, one pass, no
     block Krylov iteration) and SLQ (one Lanczos run per probe vector);
  4. Nyström PCG (one Nyström sketch $\mathbf{A}\mathbf{\Omega}$, no iteration);
  5. randomized Kaczmarz and sketch-and-project, last, gated (stage K9).
- Later (the block round): randomized subspace iteration and RBKI for low rank, their Nyström
  variants, random-start block Lanczos, HMT Proposition 8.6 and Theorem 9.2, Krylov-aware trace
  estimation; then TW's gapless bounds (Lemma 9.4), adaptive rank, randomly pivoted Cholesky
  (question 2). The design for that round is in §4.
- Recommendation: as listed. Rework: none.

**D12. Placement.**
- `Krylov/` (layer 1) is deterministic and imports Matrix, Polynomial and ForMathlib only.
  Subdirectories: `Krylov/Basic/` (Space, Grade, Compression), `Krylov/LinearSystems/`
  (Projection, CG, PolynomialIteration, Preconditioned, GMRES), `Krylov/Functions/`
  (FunctionApprox, Quadrature), `Krylov/Processes/` (Arnoldi, Lanczos, Recurrences),
  `Krylov/Eigenvalues/` (Ritz, PowerIteration).
- Outside `Krylov/`:

  | Addition | Home | Reason |
  |---|---|---|
  | `gramSchmidtQ A * (gramSchmidtQ A)ᴴ = rangeProjector A` (partial isometry) | `Matrix/Factorizations/GramSchmidt.lean` | a Gram–Schmidt fact |
  | `cfc (·⁻¹) M = pinv M` for Hermitian $\mathbf{M}$ | `Matrix/Functions/HermitianCalculus.lean` | a functional-calculus fact |
  | $\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}} \le \operatorname{tr}\mathbf{A}/\sqrt{k}$, PSD | `Matrix/Spectral/LowRank.lean` | best approximation (Hutch++) |
  | Chebyshev amplifier (Poly8), two-interval MINRES polynomial | `Polynomial/Chebyshev/` | scalar polynomials; Poly8's named consumer |
  | `measurable_krylovMatrix`, `measurable_arnoldiMatrix`, measurability of the D3 outputs and of projector-form Ritz values in $\mathbf{b}$ | *new* `Probability/Measurability/Krylov.lean` | measurability lives beside `Probability/Measurability/Matrix.lean`; Krylov imports no Probability (the file imports Krylov within layer 1) |
  | random-start eigenvalue estimation, Hutch++, SLQ | `Estimation/Spectral/`, `Estimation/Trace/` (new, layer 4) | estimation |
  | sketch-and-precondition, iterative sketching | `Regression/` | sketched least squares and preconditioning |
  | sketched GMRES and Rayleigh–Ritz, Nyström PCG, Kaczmarz, sketch-and-project | `Solvers/` (new, layer 5) | randomized solvers |
  | i.i.d. iterates on `Measure.infinitePi` | `Probability/` | a probability fact |

- Not this round: the QR algorithm, `jacobiMatrix`, the spectral measure (D6). Rework: import paths.
- Amendment (2026-10-20, sketch-and-precondition skeleton): Richardson's iteration lives in
  `Krylov/LinearSystems/Richardson.lean`, not `PolynomialIteration.lean`: the file holds one
  recursion (`NLAlib.richardsonIterate`, rectangular), not polynomial methods
  (`docs/design/Regression-SketchPrecondition.md` §6). The i.i.d.-iterate lemma went to
  `ForMathlib/Probability/Independence/InfinitePi.lean` and `Probability/Law.lean`
  (`docs/design/Regression-Kaczmarz.md` §7).
- Amendment (2026-10-25, maintainer decision on library organization): `Solvers/` is merged into
  `Regression/` (Kaczmarz and sketch-and-project are `Regression/{Kaczmarz, SketchAndProject}.lean`);
  later randomized solvers (sketched GMRES, Nyström PCG) go to `Regression/` too, or stay in Krylov
  when deterministic. Layers now follow the imports (CONTRIBUTING §2): Krylov 1, Probability 1.5,
  so `Probability/Measurability/Krylov.lean` imports Krylov and Krylov never imports Probability.

## 3. Decisions the orchestrator takes

**O1. Conventions.** `q` counts generators; degrees `p.degree < q` (membership), `p.degree ≤ q` with
`p.eval 0 = 1` (residuals), `p.degree < 2 * q` (Gauss); "`q` matrix-vector products" theorems are
about $\mathcal{K}_{q+1}$ and say so.

**O2. Names and argument order.** Matrix first, then function or right-hand side, then the basis or
depth: `cgIterate A b q`, `lanczosFA A f b q`, `galerkinInverse A X`, `polyIterate A b x₀ s`.
Docstrings show outputs in `\mathsf`; only the definition's docstring shows the formula. The core
names of D3 are provisional until the stage K0 note.

**O3. Angles and overlaps.** `tangentMatrix` and `principalAngle` for subspaces; the overlap ratio
written out for a vector against an eigenvector; no Krylov-local angle definition.

**O4. Quadrature.** Matrix-level Gauss exactness and error in stage K1; the OP reading under D6.

**O5. Random results are real**, because the Gaussian laws are (LowRank D3).

**O6. Constants and asymptotic forms.** Small source constants the proof reaches are written in the
statement (CG's $2(\frac{\sqrt b - \sqrt a}{\sqrt b + \sqrt a})^q$). Kuczyński–Woźniakowski's
(0.871, 1.254, 2.575, 2.589) and Hutch++'s are `irreducible_def` bounds with `docs/constants.toml`
entries and inline values (§5.2 rule 2). Randomized sample-size results get `exists_forall_`
corollaries (§5.2 rule 3); deterministic iteration counts get explicit corollaries only.

**O7. Realisation statements** follow `isQR_householder` and `isLU_luLower_luUpper`: the recursion is
a `def` by structural recursion on ℕ, step lemmas are private unless a second file needs them, and
the realisation theorem's hypothesis is on computed quantities (no breakdown), never on the grade
when the computed form is available.

**O8. Mathlib search and deviations.** Each note records the search (`Polynomial.degreeLT`,
`Matrix.range_mulVecLin`, `InnerProductSpace.gramSchmidt`, `span_gramSchmidt_Iic`, `Module.AEval'`,
`minpoly`, `Lagrange.interpolate`, `IsMinOn`, `AffineSubspace.mk'`). Mathlib has no Krylov space,
grade, Arnoldi basis or CG, so the new definitions are additions. One candidate deviation: the
grade is the finite rank of Mathlib's cyclic submodule in `Module.AEval'`; without a bridge it
gets a numbered entry with its reason.

**O9. Degenerate cases** for every statement: $q = 0$; $\mathbf{b} = \mathbf{0}$; $\mathbf{b}$ an
eigenvector; $q$ above the grade; singular or indefinite $\mathbf{A}$ (junk values of D3);
an empty index type; a recurrence step after breakdown.

**O10. Ledger.** The prototype's 470 `Krylov` declarations and their consumers are accounted for:
ported, cut with the reason from §1, or deferred with §4 as the reason.

## 4. Scope

**This round.** First the CG slice (stage K0), in detail. Then, as a roadmap: Lanczos-FA and
Gauss quadrature; GMRES, MINRES, CGLS, PCG and polynomial iterations; the Arnoldi basis and its
recurrence for general $\mathbf{A}$; Ritz values and eigenvalue bounds with the Chebyshev
amplifier; and the single-vector randomized items of D11 (random-start power and Lanczos, sketched
GMRES and Rayleigh–Ritz, sketch-and-precondition, iterative sketching, Hutch++, SLQ, Nyström PCG,
Kaczmarz and sketch-and-project).

**Later rounds**, each with its reason:
- *The block round* (maintainer's directions). Design, kept from the review draft:
  `blockKrylovMatrix` (D10); RSI is `rsvd A ((Aᴴ * A) ^ q * Ω)` and RBKI is
  `rsvd A (blockKrylovMatrix (Aᴴ * A) Ω q)`, with no new names and the test matrix on the right.
  Unifying them through `rsvd` simplifies the object and the deterministic reduction and does not
  try to unify the rest. Shared, proved once: for `p.degree < q`, `aeval (Aᴴ * A) p * Ω` is the
  block Krylov matrix times a coefficient matrix, so `singularValues_sub_rsvd_le_sub_mul` gives
  $\sigma_i(\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{K})) \le \sigma_i(\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, p(\mathbf{A}^{\mathsf{H}}\mathbf{A})\mathbf{\Omega}))$
  in one lemma; and $\mathsf{rsvd}(\mathbf{A}, p(\mathbf{A}^{\mathsf{H}}\mathbf{A})\mathbf{\Omega}) = \mathbf{P}_{\mathbf{B}\mathbf{\Omega}}\mathbf{A}$
  with $\mathbf{B} = \mathbf{A}p(\mathbf{A}^{\mathsf{H}}\mathbf{A})$, so every LowRank theorem applies
  to $\mathbf{B}$ with $\mathbf{\Omega}$ untouched. `IsSVD.mul_aeval_conjTranspose_mul_self` gives
  the signed values $\sigma_i p(\sigma_i^2)$; the singular values of $\mathbf{B}$ are their absolute
  values re-sorted, a small re-sorting lemma to add then. Diverging, not abstracted: the polynomial
  (power, Chebyshev, amplifier) and the probability. Citations: the four gapped lines (RSI, RBKI,
  NysSI, NysBKI) of `TroppWebber2023` Theorem 9.2, through its Lemma 9.5 and Proposition 8.6 (in
  the library as `measureReal_frobNorm_mul_mul_pinv_sq_gt_le_of_hasLaw_gaussianMatrix`,
  `RandomMatrix/Gaussian/BlockTail.lean`); its Theorem 9.1 is the gapless theorem (Lemma 9.4). MT
  Theorem 11.11 is stated in MT without proof ("adapted from Tropp"); the proof must be
  reconstructed, citing Musco and Musco 2015 Theorem 1 as its source, with the constant an
  `irreducible_def` expected to differ from MT's and depth $q = O(\log(n/\varepsilon)/\sqrt{\varepsilon})$.
  Also in that round: HMT Proposition 8.6 and Theorem 9.2, random-start block Lanczos, Krylov-aware
  trace estimation, block CG, block GMRES, deterministic block Lanczos and block Arnoldi (block
  grade, deflation of rank-deficient blocks).
- Deflation (deflated CG, GMRES, Lanczos): D3 with an augmented `X`, but the analyses need
  perturbation of the deflated spectrum.
- Two-sided Lanczos, BiCG, Petrov–Galerkin with test space different from the search space: no
  consumer, and they need an oblique-projection definition beside D3.
- Arnoldi-FA for non-Hermitian $f(\mathbf{A})\mathbf{b}$: needs a holomorphic functional calculus for
  non-normal matrices, which the Matrix layer lacks.
- The Jacobi, orthogonal-polynomial and spectral-measure layer (D6); Golub–Kahan and LSQR (no
  consumer); Lanczos-FA near-optimality for rational functions (rational-function infrastructure).
- Steepest descent: no Krylov optimality characterisation, so it does not fit D3; with stationary
  splittings, Gauss–Seidel and SOR in a Solvers round.
- Restarted GMRES, Crouzeix–Palencia bounds, the QR algorithm, randomly pivoted Cholesky
  (question 2), sharp Kuczyński–Woźniakowski constants.

**Out.** Finite precision: Paige- and Greenbaum-style analyses are large; the cheap perturbed
relation $\mathbf{A}\mathbf{Q} = \mathbf{Q}\mathbf{T} + \beta\mathbf{q}\mathbf{e}^{\mathsf{H}} + \mathbf{F}$
as a hypothesis is left out unless you want it (question 4); the maintainer's LAA paper on Lanczos
stability (§9) is the reference for the exclusion. Streaming, cost and query models (question 5).

## 5. Process

As in `PORT_LOWRANK.md` §1, with these points:
- **Approval.** The maintainer confirms or decides §2 before any skeleton depends on it.
- **The CG slice first.** Stage K0 gets one design note, `docs/design/Krylov-CG.md`, with exact
  signatures for all its files, reviewed by a `fable` agent and then by the maintainer before any
  proof. After it is implemented, the maintainer reviews how the pieces fit (the design checkpoint
  for the round); the roadmap stages are designed only after that, and may change.
- **Notes** are drafted by an Opus agent; consumers first; the placement list (CONTRIBUTING §8
  item 5); the Mathlib search of O8. File budget about 1000 lines; proof agents one file at a time,
  at most two at once.
- **Hands off the prototype.** `~/Documents/prove2me` is read, never edited or built.

## 6. What the library has (checked against the tree)

- **For the CG slice**: `rangeProjector`, `pinv`, `HasOrthonormalCols.pinv_mul_left`,
  `HasOrthonormalCols.pinv_mul_conjTranspose_right`, `measurable_rank`; `IsQR`, `IsQR.unique`,
  `gramSchmidtQ`, `isQR_gramSchmidt`, `hasOrthonormalCols_gramSchmidtQ`,
  `span_gramSchmidtQ_col_image_Iic`, `gramSchmidtR_apply_self_smul_col`; `IsUpperHessenberg`,
  `IsTridiagonal`, `HasOrthonormalCols.exists_eq_mul_diagonal_of_isUpperHessenberg`; `quadForm`,
  `isLeastSquaresSolution_iff_isMinOn`; `Matrix.IsHermitian.re_quadForm_aeval_aeval_mulVec_le` and
  `re_quadForm_aeval_mulVec_le` (the spectral step, CG at weight $g = X$);
  `exists_degree_lt_one_sub_eq_X_mul_of_eval_zero_eq_one` (residual algebra); `chebyshevResidual`
  with `isUniformApproxOn_chebyshevResidual_two_mul_pow` (the rate); `pseudoConditionNumber`,
  `Matrix.PosDef.smul_le_and_le_smul_iff_spectrum_subset` ($\kappa$ form).
- **Algorithm precedent** (D4): `householderState`, `isQR_householder`, `gaussState`,
  `isLU_luLower_luUpper`.
- **For the roadmap**: `specNorm_cfc_sub_aeval_le`, `cfc_blockDiagonal`, `Matrix.PosDef.inv_eq_cfc`,
  `Matrix.PosDef.inv_sqrt_eq_cfc`, `exists_degree_le_isUniformApproxOn_of_open_ellipse_interval`,
  `jacksonApprox`, `exists_degree_lt_isUniformApproxOn_inv`; `eigenvalue`,
  `eigenvalue_conjTranspose_mul_mul_le` (Ritz values never exceed eigenvalues),
  `le_eigenvalue_of_forall_mem`, `sqrt_add_div_sqrt_sub_pow_div_two_le_eval_T_real`,
  `tangentMatrix`, `IsDiagonalizable`, `complexify`; `sketchAndSolve`,
  `IsSubspaceEmbedding.norm_sub_mulVec_sq_le_of_fromCols`,
  `IsSubspaceEmbedding.pseudoConditionNumber_mul_sq_le`; `rsvd`, `nystrom`,
  `singularValues_sub_rsvd_le_sub_mul`; `gaussianVector`, `IsIsotropic.integral_quadForm`,
  `integral_log_norm_sq_div_sq_le_of_hasLaw_gaussianVector`, `ae_eval_ne_zero_of_ne_zero`,
  `measurable_rangeProjector`, `measurable_eigenvalue`, `measurable_gramSchmidtQ`.
- **Mathlib**: no Krylov space, grade, Arnoldi, Lanczos, CG, matrix quadrature or spectral measure.
  Used: `Polynomial.degreeLT`, `Matrix.range_mulVecLin`, `Polynomial.aeval_map_algebraMap`,
  `InnerProductSpace.gramSchmidtNormed`, `minpoly`, `IsMinOn`, `AffineSubspace.mk'`,
  `MeasureTheory.Measure.infinitePi`. The spectrum of a matrix is finite
  (`Matrix.IsHermitian.finite_real_spectrum`), so `cfc f` of a Hermitian matrix is defined by its
  eigenvalues for every `f`, never the junk value of `cfc_apply_of_not_continuousOn`.

## 7. The mathematics of the CG slice

Provisional; exact signatures are the K0 note's.

```lean
noncomputable def krylovMatrix (A : Matrix n n 𝕜) (b) (q : ℕ) : Matrix n (Fin q) 𝕜
theorem krylovMatrix_apply (i : n) (j : Fin q) : krylovMatrix A b q i j = (A ^ (j : ℕ) *ᵥ b) i
def krylovSpace (A : Matrix n n 𝕜) (b) (q : ℕ) := LinearMap.range (krylovMatrix A b q).mulVecLin
theorem mem_krylovSpace_iff : x ∈ krylovSpace A b q ↔ ∃ p : 𝕜[X], p.degree < q ∧ x = aeval A p *ᵥ b
noncomputable def krylovGrade (A : Matrix n n 𝕜) (b) : ℕ := (krylovMatrix A b (Fintype.card n)).rank
theorem rank_krylovMatrix : (krylovMatrix A b q).rank = min q (krylovGrade A b)
noncomputable def galerkinInverse (A : Matrix n n 𝕜) (X : Matrix n p 𝕜) : Matrix n n 𝕜 :=
  pinv (rangeProjector X * A * rangeProjector X)
noncomputable def cgIterate (A : Matrix n n 𝕜) (b) (q : ℕ) := galerkinInverse A (krylovMatrix A b q) *ᵥ b
noncomputable def arnoldiMatrix (A : Matrix n n 𝕜) (b) (q : ℕ) : Matrix n (Fin q) 𝕜 :=
  gramSchmidtQ (krylovMatrix A b q)
```

1. **Frame form.** For `hA : A.PosDef`, `hQ : HasOrthonormalCols Q` and
   `hK : LinearMap.range Q.mulVecLin = krylovSpace A b q`:
   `cgIterate A b q = Q *ᵥ ((Qᴴ * A * Q)⁻¹ *ᵥ (Qᴴ *ᵥ b))`, which is
   $\mathbf{Q}(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})^{-1}\mathbf{Q}^{\mathsf{H}}\mathbf{b}$.
2. **Optimality.** With `A *ᵥ xs = b`, `cgIterate A b q` minimises `RCLike.re (quadForm A (y - xs))`
   over the Krylov space (Mathlib's `IsMinOn`); Galerkin form `Qᴴ *ᵥ (b - A *ᵥ cgIterate A b q) = 0`.
3. **The Lanczos basis yields CG.** For Hermitian positive definite $\mathbf{A}$ and $q \le \nu$,
   `arnoldiMatrix A b q` satisfies `IsGradedKrylovBasis`, $\mathbf{T} = \mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$
   is tridiagonal with real $\alpha_j$ and $\beta_j > 0$, $\mathbf{Q}^{\mathsf{H}}\mathbf{b} = \|\mathbf{b}\|\mathbf{e}_0$
   for $0 < q$, and so `cgIterate A b q = ‖b‖ • Q *ᵥ (T⁻¹ *ᵥ e₀)`; the relation
   `A * arnoldiMatrix A b q = arnoldiMatrix A b (q + 1) * (…)` holds for every $q$.
4. **Polynomial characterisation and rate.**
   ```lean
   theorem re_quadForm_sub_cgIterate_le (ha : 0 < a) (h₁ : a • (1 : Matrix n n 𝕜) ≤ A)
       (h₂ : A ≤ a' • (1 : Matrix n n 𝕜)) (hxs : A *ᵥ xs = b) (p : ℝ[X]) (hp : p.degree ≤ q)
       (hp₀ : p.eval 0 = 1) (hM : ∀ x ∈ Set.Icc a a', |p.eval x| ≤ M) :
       RCLike.re (quadForm A (xs - cgIterate A b q)) ≤ M ^ 2 * RCLike.re (quadForm A xs)
   ```
   with the error equal to the minimum over residual polynomials, the rate
   $\|\mathbf{x}_\star - \mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, q)\|_{\mathbf{A}} \le 2\bigl(\frac{\sqrt{a'} - \sqrt a}{\sqrt{a'} + \sqrt a}\bigr)^q\|\mathbf{x}_\star\|_{\mathbf{A}}$
   at `chebyshevResidual a a' q`, the $\kappa$ form, and finite termination once
   `krylovGrade A b ≤ q`.
5. **Lanczos recurrence, realised.** *new* `lanczosState A b k`: previous vector, current vector,
   current $\beta$; one step forms $\mathbf{w} = \mathbf{A}\mathbf{q}_j - \beta_j\mathbf{q}_{j-1}$,
   $\alpha_j = \operatorname{Re}\langle\mathbf{q}_j, \mathbf{w}\rangle$,
   then subtracts $\alpha_j\mathbf{q}_j$ from $\mathbf{w}$,
   $\beta_{j+1} = \|\mathbf{w}\|$, $\mathbf{q}_{j+1} = \mathbf{w}/\beta_{j+1}$ (zero when $\beta_{j+1} = 0$,
   after which the state is frozen). Realisation: for Hermitian $\mathbf{A}$ and $j < \nu$ the
   $j$-th vector is `(arnoldiMatrix A b q).col j` for every $q > j$, and $\alpha_j$, $\beta_j$ are the
   entries of $\mathbf{T}$; past the grade the vectors are zero.
6. **Hestenes–Stiefel, realised.** *new* `cgState A b k`: iterate, residual, direction, with
   $\alpha_k = \|\mathbf{r}_k\|^2/\mathbf{p}_k^{\mathsf{H}}\mathbf{A}\mathbf{p}_k$ and
   $\beta_k = \|\mathbf{r}_{k+1}\|^2/\|\mathbf{r}_k\|^2$. Realisation: for `A.PosDef` and every $k$,
   the computed iterate equals `cgIterate A b k`.

## 8. Stages

**Stage K0, the CG slice** (the design checkpoint for the round). Uses only existing lower layers,
plus two Matrix lemmas listed in D12 (the Gram–Schmidt partial isometry; the `cfc` inverse lemma is
not needed until K1). In order, one file at a time:

| Step | Content (§7 items) | File | Lines | Decls |
|---|---|---|---|---|
| K0a | `krylovMatrix`, `krylovSpace`, membership over `𝕜[X]` and `ℝ[X]`, monotonicity, $\mathbf{A}\mathcal{K}_q \subseteq \mathcal{K}_{q+1}$, shift invariance, compression lemmas | `Krylov/Basic/Space.lean` | 400 | 20 |
| K0b | `krylovGrade`: rank $\min(q,\nu)$, stabilisation, invariance, $\nu \le \deg\mu_{\mathbf{A}}$, finite termination | `Krylov/Basic/Grade.lean` | 300 | 13 |
| K0c | `galerkinInverse`, `cgIterate`: range independence, frame form, optimality, Galerkin form, residual algebra, polynomial characterisation, Chebyshev rate, $\kappa$ form, finite termination (items 1, 2, 4) | `Krylov/LinearSystems/Projection.lean`, `CG.lean` | 650 | 30 |
| K0d | `arnoldiMatrix`, `IsGradedKrylovBasis`, relation, Hessenberg and tridiagonal structure, uniqueness, the Lanczos basis yields CG (item 3) | `Krylov/Processes/Lanczos.lean`, Matrix addition | 500 | 23 |
| K0e | `lanczosState` and `cgState` with their realisation theorems (items 5, 6) | `Krylov/Processes/LanczosRecurrence.lean`, `Krylov/LinearSystems/CGRecurrence.lean` | 850 | 38 |
| **K0** | | | **about 2700** | **about 125** |

Consumers inside the slice: K0c uses K0a and K0b; K0d uses K0c (the Lanczos-basis corollary);
K0e uses K0d and K0c. Outside it: every roadmap stage. The prototype material is `Spaces`,
`Solvers.Minimizer`, `Solvers.CG`, `Processes.Arnoldi`, `Processes.Lanczos`, and the proved halves
of `LanczosRecurrence` and `CGRecurrence`.

**Roadmap** (each designed after the K0 checkpoint; sizes approximate):
- **K1 Lanczos-FA and Gauss quadrature** (about 550 lines): `compressedCfc`, `lanczosFA`, frame form,
  the $2\varepsilon\|\mathbf{b}\|$ and $2\varepsilon\|\mathbf{b}\|^2$ bounds and instances, CG as
  Lanczos-FA for $1/x$. Needs K0.
- **K2 GMRES, MINRES, CGLS, PCG, polynomial iterations** (about 1100): `minResidualInverse`,
  `gmresIterate`, residual-polynomial bounds, MINRES two-interval rate (Polynomial addition), CGLS,
  PCG under spectral equivalence, Richardson and Chebyshev iteration. Needs K0.
- **K3 Arnoldi for general $\mathbf{A}$** (about 600): Hessenberg structure, GMRES as a small
  least-squares problem, `arnoldiState` (modified Gram–Schmidt) realised. Needs K0, K2.
- **K4 Ritz values and eigenvalue bounds** (about 850): Chebyshev amplifier (Poly8), D9 forms,
  Kaniel–Paige–Saad, gap-free bound, power and inverse iteration. Needs K0.
- **K5 Random-start power and Lanczos** (about 800): `Probability/Measurability/Krylov.lean`, the
  almost-sure grade (the degree of the minimal polynomial of $\mathbf{A}$, not $n$; from
  `ae_eval_ne_zero_of_ne_zero` on a minor of the Krylov matrix), gap-dependent and $\log n$
  expectations, named bounds. Needs K4.
- **K6 Sketched solvers** (about 600): sketched GMRES and Rayleigh–Ritz, sketch-and-precondition,
  iterative sketching. Needs K2, K4.
- **K7 Hutch++ and SLQ** (about 700). Needs K1, LowRank.
- **K8 Nyström PCG** (about 450). Needs K2, LowRank.
- **K9 Kaczmarz and sketch-and-project** (about 750), gated on the i.i.d.-iterate addition.

Total: about 2700 lines for the slice and about 6400 for the roadmap.

## 9. Literature

**Verified against local PDFs:**
- `HalkoMartinssonTropp2011`: Algorithms 4.3, 4.4; Proposition 8.6; Theorem 9.2 (printed
  $(\mathbf{A}^*\mathbf{A})^q\mathbf{A}$ is a typo for $(\mathbf{A}\mathbf{A}^*)^q\mathbf{A}$);
  Corollary 10.10 (block round).
- `MartinssonTropp2020`: §4 (Example 4.2, Theorem 4.5; headings); §6.2, §6.3, Theorems 6.1, 6.2
  (Kuczyński–Woźniakowski as source, PSD); §6.6 and Algorithm 6 (SLQ); §10.4, §10.5, §17.3, §17.4
  (headings); §11.6 to §11.7, Lemma 11.8, Corollary 11.9, Theorem 11.11 (stated without proof,
  "adapted from Tropp"; block round).
- `TroppWebber2023` (arXiv v3): Theorem 9.1 (gapless), Theorem 9.2 (gapped, four lines), Lemmas
  5.1, 5.2, 8.3, 9.3, 9.4, 9.5, Proposition 8.6 (block round).
- Gautschi, *Orthogonal Polynomials: Computation and Approximation*, 2004: Theorems 1.31, 1.45,
  1.46, 3.1 (new key `Gautschi2004`; D6).
- `Trefethen2019`: Theorem 19.3. `Saad2003`: Theorem 6.29, (6.128) (already cited).
- Chen, Trogdon and Ubaru, "Randomized matrix-free quadrature: unified and uniform bounds for
  stochastic Lanczos quadrature and the kernel polynomial method", SIAM J. Sci. Comput., 2025,
  DOI 10.1137/23M1600414 (from the SIAM author proof). The key `ChenTrogdonUbaru2022` is arXiv v1;
  question 3. Stage K7.
- "Stability of the Lanczos algorithm on matrices with regular spectral distributions", Linear
  Algebra Appl., DOI 10.1016/j.laa.2023.11.006 (the maintainer's paper; authors and pages copied
  from the article PDF when the key is added). Provenance for the finite-precision exclusion only.

**In `references.bib`, locators to verify:** `Saad2003` (§6.2, §6.5, Proposition 6.32, §9.2);
`Saad2011` (§6.1 to §6.6, Theorem 6.4); `TrefethenBau1997` (Lectures 7, 10, 33, 35, 36, 37, 38, 40);
`GolubVanLoan2013` (§10.1, §11.5); `Parlett1998` (§12.4, Ch. 13); `GolubMeurant2010` (Ch. 4, 6);
`KuczynskiWozniakowski1992` (Theorems 4.1, 4.2 per the prototype); `Higham2008` (§13.2);
`ChenEtAl2025` (question 2).

**New keys, locators to verify:** Greenbaum 1997 (Theorem 3.1.1, §3.1, §3.2); Hestenes and Stiefel
1952 and Lanczos 1950, with Paige 1971 (the recurrences of stage K0e); Saad 1980 (SINUM 17);
Saad 1992 (SINUM 29); Musco and Musco 2015 (NeurIPS, Theorem 1, Lemma 4; K4 and the block round);
Musco, Musco and Sidford 2018 (SODA); Meyer, Musco, Musco and Woodruff 2021 (SOSA, Theorem 1);
Ubaru, Chen and Saad 2017 (SIMAX 38(4)); Frangella, Tropp and Udell 2023 (SIMAX 44(2), Proposition
5.3, Theorem 5.1); Nakatsukasa and Tropp 2024 (SIMAX 45(2), §3, §5); Strohmer and Vershynin 2009;
Gower and Richtárik 2015 (Theorem 4.6); Rokhlin and Tygert 2008; Avron, Maymounkov and Toledo 2010;
Meng, Saunders and Mahoney 2014; Pilanci and Wainwright 2016; Paige and Saunders 1975, 1982; Kaniel
1966. Each key is added before it is cited (CONTRIBUTING §6).

**The maintainer's own papers.** Only the two above are cited. No other is cited, used as a source
or summarised until question 3 is answered.

## 10. Questions for the maintainer

Only questions whose answer changes the plan. Recommendations in brackets.

1. **The slice's edges.** The CG slice (about 2700 lines) contains the realisation theorems, as
   directed. Should a second method (PCG or Lanczos-FA) join it, to test the D3 core before the
   checkpoint? [No: the K0 note writes the K1 and K2 signatures on paper instead, so the checkpoint
   can judge the shared shape at no proof cost.]
2. **Randomly pivoted Cholesky.** Not a Krylov method; its analysis needs adaptive random sampling,
   the infrastructure K9 builds. LowRank follow-up, or this round? [LowRank follow-up.]
3. **Citations.** Several of your other papers in `~/Documents/Papers` bear on this round's later
   items; in particular, two later-round topics of §4, Krylov-aware trace estimation and Lanczos-FA
   near-optimality for rational functions, are subjects of your papers. Which are published and
   citable? Until then none is cited or used as a source. And the SISC version of Chen, Trogdon and
   Ubaru: a new key beside `ChenTrogdonUbaru2022`, or update it? [A new key; the v1 key stays for
   the Jackson round's citations of its Appendix C.]
4. **Finite precision.** With the recurrences now in (D4), do you want the cheap perturbed-relation
   hypothesis of §4 as a stage after K0? [No, a later round.]
5. **The matvec query model.** The prototype's `KRYLOV_DEFINITIONS.md` §3.10 proposed a query model
   (`MatvecAlg`, `run`, `cost`) for exhibiting algorithms and for matrix-vector lower bounds,
   which is where randomized lower bounds live. Does it stay out of this round? [Out; D4's
   realisation theorems exhibit the standard algorithms without a cost model.]

## 11. Done

The round is done when:
- the stages the maintainer keeps are implemented, each with its design note, review and report;
- `NLAlib` and `NLAlibScaffold` build with no warnings, and the CONTRIBUTING §9 checks pass;
- every new definition is in `docs/design/Mathlib-deviations.md` (an addition or a numbered
  deviation with its bridge), and every §5.3 row added (Krylov space and matrix, grade, Arnoldi
  matrix, the D3 definitions, the recurrences) is in CONTRIBUTING with its bridge;
- the ledger accounts for the prototype's 470 `Krylov` declarations and their consumers;
- `docs/design/Krylov-REPORT.md` reports as `Sketching-REPORT.md` did, listing open placement flags.
