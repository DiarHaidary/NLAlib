# Design note: block Krylov spaces and the Tropp–Webber bounds for RBKI and RSI

Status: approved and implemented, 2026-10-18 (Decisions; Implementation, with "What was proved",
"Wrap-up amendments" and "Later targets"). Drafted 2026-10-18, branch `krylov/block` (off
`origin/main` at `f4e1255`). Written from the orchestrator's brief, read against the tree, the prototype atlas and the two papers; revised the
same day after an independent review (`review-1`: no false statement found; the depth translation,
Chebyshev degrees and exponents checked against the PDF; findings on BD3, the B0 bridges, the §6.1
statement shapes and the stage sizes adopted below). No Lean file exists yet; the signatures below
are sketches for the skeleton, not the specification. The questions marked BD1 to BD9 (§13, BD3 in
two parts) are for the maintainer; everything else proceeds as recommended unless he objects.

The maintainer's request, verbatim: "let's build block krylov and then work towards formalizing the
bounds in Tropp Webber." Scope addition relayed by the coordinator: the bounds should ideally also
hold for the truncated variants (late truncation `truncatedSVD (alg …) r`, and early truncation if
natural), "so we might need to borrow ideas from Musco Musco".

Earlier direction on the block question (PORT_KRYLOV.md:22): "we should think about how we are
going to generalize this to block methods. Does it make sense to have a single definition? Or to
later show the regular one is a special case." It was answered by D10(c) (PORT_KRYLOV.md:405–427,
Krylov-CG.md §5), which the maintainer approved with D1 to D7 and D9 to D12 on 2026-10-17
(PORT_KRYLOV.md:48). §2 reopens it only because the orchestrator now recommends the other option.

Sources: Tropp and Webber, arXiv:2306.12418v3 (`TroppWebber2023`, cited "TW"); Musco and Musco,
arXiv:1504.05477v4 (new key `MuscoMusco2015`, cited "MM"); Gu 2015 (`Gu2015`, TW's [50]).

## 1. Overview and main findings

1. **The analysis needs almost nothing from Krylov theory.** Every bound in TW §9 goes through one
   fact: for a polynomial $f$ of degree less than $q$, the sketch
   $\mathbf{A}f(\mathbf{A}^{\mathsf{H}}\mathbf{A})\mathbf{\Omega}$ has its range inside the block
   Krylov space $\mathbf{A}\,\mathcal{K}_q(\mathbf{A}^{\mathsf{H}}\mathbf{A}, \mathbf{\Omega}) =
   \mathcal{K}_q(\mathbf{A}\mathbf{A}^{\mathsf{H}}, \mathbf{A}\mathbf{\Omega})$, so "bigger
   projection, smaller error" (TW Lemma 5.1) bounds the RBKI error by the error of the range finder
   on the filtered sketch. No block grade, block Lanczos, block tridiagonality or recurrence is
   used. The block Krylov work of this round is therefore one block space file, with the bridges
   and structural lemmas later block algorithms will need so that it is not reopened (§3).
2. **RBKI and RSI are randomized SVDs with special test matrices.** With the library's
   `rsvd A Ω := rangeProjector (A * Ω) * A` (`Matrix/Factorizations/SketchedLowRank.lean:93`),
   RBKI is `rsvd A (blockKrylovMatrix (Aᴴ * A) Ω q)` and RSI with $p$ power steps is
   `rsvd A ((Aᴴ * A) ^ p * Ω)` (the approved plan of PORT_KRYLOV.md:520–540; BD3a proposes a name
   for RBKI only). Every existing deterministic `rsvd` lemma, in particular the whole late-truncation API of `LowRank/Structural/Truncation.lean` (Gu's projected form,
   reverse Eckart–Young), applies to them with no new work. This is what makes the truncated
   variants cheap.
3. **Most of TW §8 is already in the library**, in general (non-diagonal) form: the structural bound
   (TW Proposition 8.5, (8.2)) for any frame, `SymmetricGauge.matrixNorm_conjTranspose_mul_self_sub_rsvd_le`
   (`LowRank/Structural/RangeFinder.lean:200`); TW Proposition 8.6, both the expectation
   `integral_frobNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix` (`RandomMatrix/Gaussian/BlockMoments.lean:155`)
   and the tail `measureReal_not_frobNorm_mul_mul_pinv_sq_le_le_of_hasLaw_gaussianMatrix`
   (`RandomMatrix/Gaussian/BlockTail.lean:543`); TW Theorem 8.1 (`LowRank/Gaussian/RangeFinder.lean:135–327`,
   `LowRank/Gaussian/RangeFinderTail.lean:188–365`); TW Corollary 8.2 (`LowRank/Gaussian/Nystrom.lean`,
   `NystromTail.lean`); reverse Eckart–Young (`Matrix/Spectral/BestRankApprox.lean:624`).
4. **Two items of TW §8 are not needed for §9**: the diagonal psd reduction (Lemma 8.3) and parallel
   sums (Lemma 8.4). The library already proves TW 8.1 without them (any-frame structural bounds;
   layer-cake in place of parallel sums, `BlockTail.lean:25`). Parallel sums only serve the sharper
   (8.1) and the $k \in \{r, r+1\}$ cases of Theorem 8.7. Both are deferred (BD5).
5. **New mathematics on the path to Theorem 9.2 is small**: the filtered structural bound (Lemma 9.5,
   deterministic part, in general form), three Chebyshev growth facts (Lemma 9.3 parts 2 and 3),
   and the Gaussian glue. Theorem 9.1 adds TW's "almost convex" Jensen lemma (Lemma 9.4) and two
   further Chebyshev facts (Lemma 9.3 parts 4 and 5), the only real-analysis work of the round.
6. **Musco–Musco's case split gives gapless bounds from gapped ones**, for the truncated and the
   untruncated output alike, in the form "$(1+\varepsilon)^2\sigma_{r}^2$ plus an exponentially
   small term", with the asymptotic depth $q = O(\log(n/\varepsilon)/\sqrt{\varepsilon})$. It needs
   only the gapped theorem, reverse Eckart–Young and one new monotonicity lemma for late truncation.
   This is a cheap gapless result before TW's exact Theorem 9.1 constants (BD4).

## 2. Block generalisation: one definition or two (decision BD1)

### 2.1 What exists

The vector Krylov layer is 23 files, about 8,200 lines, about 260 public declarations, all proved,
on `origin/main`. The objects:

- `krylovMatrix A b q : Matrix n (Fin q) 𝕜` (`Krylov/Basic/Space.lean:60`), `krylovSpace`
  (`:78`), `mem_krylovSpace_iff` (`:102`, scalar polynomials), `krylovMatrix_mul_mulVec` (`:208`,
  change of variables);
- `krylovGrade A b` (`Krylov/Basic/Grade.lean:52`) with `rank_krylovMatrix` (`:172`,
  rank $= \min(q, \nu)$) and `krylovGrade_le_iff` (`:154`);
- `IsGradedKrylovBasis`, `arnoldiMatrix A b q := gramSchmidtQ (krylovMatrix A b q)`
  (`Krylov/Processes/Lanczos.lean:67`, a `structure`, and `:143`), tridiagonality (`:135`, the Matrix layer's
  `IsTridiagonal` on `Fin n`, `Matrix/Factorizations/Hessenberg.lean:57`);
- the basis-free methods `galerkinInverse`, `minResidualInverse`, `compressedCfc`, which already
  take a basis matrix `X` with any `Fintype` column type (`Krylov/LinearSystems/Galerkin.lean:66`);
- realisation theorems: Lanczos, Hestenes–Stiefel CG, PCG, MGS Arnoldi, GMRES by Givens,
  Paige–Saunders MINRES (`Krylov/Processes/*Recurrence.lean`, `Krylov/LinearSystems/*Recurrence.lean`,
  `GMRESArnoldi.lean`).

Uses: `krylovMatrix` 98 lines in 15 files, `krylovSpace` 144 lines in 16 files, `krylovGrade` 54
lines in 14 files, `arnoldiMatrix` 162 lines in 7 files, `cgIterate` 87 lines, `gmresIterate` 74,
`lanczosFA` 60. None outside `NLAlib/Krylov/` (grep, 2026-10-18).

### 2.2 The vector-specific facts and how they would read with blocks

| Vector fact | Block analogue | Same statement? |
|---|---|---|
| grade $\nu$, one number; rank $\mathbf{K}_q = \min(q,\nu)$; strict growth then constant | block grade is a sequence of block ranks with deflation; rank is not $\min(q \cdot p, \cdot)$ in general | no |
| $\mathbf{x} \in \mathcal{K}_q \iff \mathbf{x} = p(\mathbf{A})\mathbf{b}$, $\deg p < q$ | $\mathbf{x} = \sum_j \mathbf{A}^j\mathbf{B}\mathbf{c}_j$, or one polynomial per column of $\mathbf{B}$ | no; scalar form is the $p = 1$ corollary |
| `arnoldiMatrix := gramSchmidtQ (krylovMatrix …)` | `gramSchmidtQ` (`Matrix/Factorizations/GramSchmidt.lean:156`) needs `[LinearOrder n] [LocallyFiniteOrderBot n]` on the column type (the variable line `:51`); `Fin q × p` has none, so a block basis goes through `Prod.Lex`, `finProdFinEquiv` or a block QR | no |
| $\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$ tridiagonal (`IsTridiagonal`, `Fin` indexed) | block tridiagonal with $p \times p$ blocks; a new predicate | no |
| three-term Lanczos, CG, MINRES, Arnoldi recurrences and their realisations | block recurrences with matrix coefficients and rank-deficient breakdown | no |
| CG, GMRES, Lanczos-FA as projections onto a subspace | the same definitions with `blockKrylovMatrix` as `X` (block CG is `galerkinInverse A (blockKrylovMatrix A B q) * B`) | yes, already shared |

The mathematics coincides exactly where the library already shares it (projection onto a subspace,
D3) and differs everywhere else.

### 2.3 Options

- **(a) One block definition, vector API refactored** (the orchestrator's recommendation).
  `krylovMatrix A B q : Matrix n (Fin q × p) 𝕜` for `B : Matrix n p 𝕜`; the vector case is
  `p = Unit`, `B = Matrix.replicateCol Unit b`. Cost: every statement of the 15 to 16 files above
  changes; `cgIterate A b q` either keeps its vector signature and wraps `replicateCol` inside (then
  every unfolding lemma carries it) or changes to a matrix right-hand side; the grade file (22
  declarations) and the five recurrence files are vector theorems that must still be stated through
  the `Unit` specialisation, so they gain `replicateCol` and `Fin q × Unit` index types without
  gaining generality; `arnoldiMatrix` needs a linear order on `Fin q × Unit` (`Prod.Lex`) or an
  `Equiv` to `Fin q`. Estimate: 2,000 to 3,000 lines touched, several proofs reworked
  (`rfl`-based apply lemmas, `Fin.castLE` nesting, `Fin.last` arguments in Grade and Lanczos), no
  new theorem. Gain: one definition.
- **(b) Two definitions with bridges** (D10(c), approved 2026-10-17). `krylovMatrix` unchanged;
  new `blockKrylovMatrix A B q : Matrix n (Fin q × p) 𝕜` and `blockKrylovSpace`, with bridges at
  the matrix level (`blockKrylovMatrix_replicateCol`: the one-column block Krylov matrix is the
  vector one reindexed), at the space level (`blockKrylovSpace_replicateCol`, and
  `blockKrylovSpace_eq_iSup_krylovSpace`, the columnwise supremum that transfers every vector bound
  to block methods) and at the method level (`galerkinInverse_blockKrylovMatrix_replicateCol` and
  "block CG with one column is CG", the bridges Krylov-CG.md §5 wrote down and checked to elaborate).
  The block file also carries the block analogues of the vector file's structural lemmas (prefix,
  successor, $\mathbf{A}\mathcal{K}_q \subseteq \mathcal{K}_{q+1}$, shift, change of variables), so
  later block algorithms do not reopen it (§3). This mirrors Mathlib's `mulVec`/`mul` split and
  CONTRIBUTING §5.1 (vectors are `n → 𝕜`). Cost: about 350 lines, plus about 30 lines appended to
  `Krylov/LinearSystems/CG.lean`; no existing statement changes.
- **(c) One definition, vector API as a definitional specialisation.** `blockKrylovMatrix` is the
  definition and `krylovMatrix A b q := (blockKrylovMatrix A (replicateCol Unit b) q).submatrix id
  (fun j => (j, ()))`, keeping the vector type `Matrix n (Fin q) 𝕜` and every vector statement.
  `krylovMatrix_apply` and `krylovMatrix_submatrix_castLE` stop being `rfl` at reducible
  transparency and need a `simp` proof; a dozen proofs that unfold `krylovMatrix` may need touching.
  The bridge becomes definitional. Gain over (b): "a single definition" in the literal sense; cost:
  one import edge (`Space.lean` would import the block file) and small proof churn.

**Recommendation: (b).** The maintainer approved it, the Tropp–Webber path uses none of the
vector-specific facts, and the facts that would be unified by (a) are exactly those that do not
generalise without changing their statements. The test applied: a later block algorithm (block
Arnoldi/Lanczos, block CG/GMRES theory) must not need a second pass on the block file or any
change to the vector files; the B0 list of §3 is built to pass it, and the method-level bridge
answers the maintainer's "later show the regular one is a special case" in Lean. Option (c) is the fallback if the maintainer wants a
single definition: it costs little and can be done later from (b) without touching any statement.
Option (a) is not recommended: its cost is concentrated in the most delicate proved files (Grade,
Lanczos, the recurrences) and it buys no theorem.

## 3. Scope of "build block Krylov" (decision BD2)

**This round (stage B0: `Krylov/Basic/BlockSpace.lean`, about 350 lines, and a section of
`Krylov/LinearSystems/CG.lean`, about 30 lines):**

```lean
variable {𝕜 : Type*} [RCLike 𝕜] {m n p : Type*} [Fintype m] [Fintype n] [Fintype p] [DecidableEq n]

def blockKrylovMatrix (A : Matrix n n 𝕜) (B : Matrix n p 𝕜) (q : ℕ) : Matrix n (Fin q × p) 𝕜 :=
  Matrix.of fun i jc => (A ^ (jc.1 : ℕ) * B) i jc.2
@[simp] theorem blockKrylovMatrix_apply : blockKrylovMatrix A B q i (j, c) = (A ^ (j : ℕ) * B) i c
def blockKrylovSpace (A : Matrix n n 𝕜) (B : Matrix n p 𝕜) (q : ℕ) : Submodule 𝕜 (n → 𝕜) :=
  LinearMap.range (blockKrylovMatrix A B q).mulVecLin

-- bridges to the vector API (BD1(b)); the first makes BD1(c) free later
theorem blockKrylovMatrix_replicateCol (b : n → 𝕜) :
    blockKrylovMatrix A (Matrix.replicateCol Unit b) q = (krylovMatrix A b q).submatrix id Prod.fst
theorem blockKrylovSpace_replicateCol (b : n → 𝕜) :
    blockKrylovSpace A (Matrix.replicateCol Unit b) q = krylovSpace A b q
theorem blockKrylovSpace_eq_iSup_krylovSpace :
    blockKrylovSpace A B q = ⨆ c, krylovSpace A (B.col c) q
theorem krylovSpace_col_le_blockKrylovSpace (c : p) :
    krylovSpace A (B.col c) q ≤ blockKrylovSpace A B q

-- structure: block analogues of Space.lean:70, :143, :165, :194, :220
theorem blockKrylovMatrix_submatrix_castLE (h : q ≤ q') :
    (blockKrylovMatrix A B q').submatrix id (Prod.map (Fin.castLE h) id) = blockKrylovMatrix A B q
theorem blockKrylovSpace_mono : Monotone (blockKrylovSpace A B)
@[simp] theorem blockKrylovSpace_zero : blockKrylovSpace A B 0 = ⊥
theorem blockKrylovSpace_one : blockKrylovSpace A B 1 = LinearMap.range B.mulVecLin
theorem blockKrylovSpace_succ :
    blockKrylovSpace A B (q + 1) = blockKrylovSpace A B q ⊔ LinearMap.range (A ^ q * B).mulVecLin
theorem mulVec_mem_blockKrylovSpace_succ (hx : x ∈ blockKrylovSpace A B q) :
    A *ᵥ x ∈ blockKrylovSpace A B (q + 1)
theorem blockKrylovSpace_add_smul_one (s : ℝ) :
    blockKrylovSpace (A + s • (1 : Matrix n n 𝕜)) B q = blockKrylovSpace A B q
theorem blockKrylovMatrix_mul_mul (C : Matrix m n 𝕜) (D : Matrix n m 𝕜) (B : Matrix n p 𝕜) (q : ℕ) :
    blockKrylovMatrix (C * D) (C * B) q = C * blockKrylovMatrix (D * C) B q
theorem blockKrylovSpace_mul_mul (C : Matrix m n 𝕜) (D : Matrix n m 𝕜) (B : Matrix n p 𝕜) (q : ℕ) :
    blockKrylovSpace (C * D) (C * B) q = (blockKrylovSpace (D * C) B q).map C.mulVecLin
theorem rank_blockKrylovMatrix_le : (blockKrylovMatrix A B q).rank ≤ q * Fintype.card p

-- polynomials
theorem mem_blockKrylovSpace_iff : x ∈ blockKrylovSpace A B q ↔
    ∃ f : p → 𝕜[X], (∀ c, (f c).degree < q) ∧ ∑ c, aeval A (f c) *ᵥ B.col c = x
theorem exists_aeval_mul_eq_blockKrylovMatrix_mul {R : Type*} [CommSemiring R] [Algebra R 𝕜]
    {f : R[X]} (hf : f.degree < q) :
    ∃ C : Matrix (Fin q × p) p 𝕜, aeval A f * B = blockKrylovMatrix A B q * C
theorem range_aeval_mul_le_blockKrylovSpace (hf : f.degree < q) :
    LinearMap.range (aeval A f * B).mulVecLin ≤ blockKrylovSpace A B q

-- in Krylov/LinearSystems/CG.lean, section "One column" (the Krylov-CG.md §5 bridges)
theorem galerkinInverse_blockKrylovMatrix_replicateCol (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) :
    galerkinInverse A (blockKrylovMatrix A (Matrix.replicateCol Unit b) q) =
      galerkinInverse A (krylovMatrix A b q)
theorem galerkinInverse_blockKrylovMatrix_replicateCol_mul (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) :
    galerkinInverse A (blockKrylovMatrix A (Matrix.replicateCol Unit b) q) *
      Matrix.replicateCol Unit b = Matrix.replicateCol Unit (cgIterate A b q)
```

The CG section goes to `CG.lean` (placement: it is a statement about `cgIterate`, and `Krylov/Basic`
does not import `LinearSystems`); its proofs are `galerkinInverse_eq_of_range_eq`
(Galerkin.lean:71) at the space bridge and `Matrix.mul_replicateCol`-style rewriting. The same
one-line pattern gives GMRES and Lanczos-FA twins when a consumer asks; they are not listed.

`blockKrylovMatrix_mul_mul` at `C = A`, `D = Aᴴ` is TW's
$\mathcal{K}_q(\mathbf{A}\mathbf{A}^{\mathsf{H}}, \mathbf{A}\mathbf{\Omega}) =
\mathbf{A}\,\mathcal{K}_q(\mathbf{A}^{\mathsf{H}}\mathbf{A}, \mathbf{\Omega})$ (TW §5.3), the block
form of `krylovMatrix_mul_mulVec`; it needs rectangular `C`, `D` (the vector lemma is square), which
is why it is stated with `m`. `mulVec_mem_blockKrylovSpace_succ` and `blockKrylovSpace_succ` are the
invariance facts a block Arnoldi relation `A * K_q = K_{q+1} * S` needs; the prefix lemma is the
nesting a graded block basis needs. Measurability, `measurable_blockKrylovMatrix` (linear in `B`),
goes to the new `Probability/Measurability/Krylov.lean` that PORT_KRYLOV D12 already names.

Prototype material: `~/Documents/prove2me/lean/NLAlib/Krylov/Spaces/Block.lean` (`blockKrylovSpace`
:42, `blockKrylovSpace_eq_iSup` :69, `mem_blockKrylovSpace_iff` :81,
`range_aeval_mul_le_blockKrylovSpace` :103, `finrank_blockKrylovSpace_le` :142), proved and
generic; the mathematics is ported, the definition moves to the matrix form of D2. Its
`subspaceIterate` (:150) is not reproduced (a name for a column space, PORT_KRYLOV.md:137).

**Later, with a recommendation each:**
- block grade and deflation, block Arnoldi/Lanczos (`IsGradedBlockKrylovBasis`, block QR on
  `Fin q × p` with `Prod.Lex`), block tridiagonality, the block Lanczos recurrence and its
  realisation: later round; no consumer in TW.
- block CG and block GMRES: no new definition is needed (`galerkinInverse A (blockKrylovMatrix A B
  q) * B`, `minResidualInverse …`); the one-column bridge is in B0 (above); their theory (block CG
  rates through `krylovSpace_col_le_blockKrylovSpace`) later.
- random-start block Lanczos for eigenvalues, Krylov-aware trace estimation: later round (they need
  the block basis).

## 4. RBKI, RSI and the Nyström variants (decisions BD3a, BD3b, BD6, BD7)

### 4.1 Definitions

`LowRank/Structural/BlockKrylov.lean` (new). Field `𝕜`, any `Fintype` index types, test matrix on
the right as in LowRank.

**What is already decided.** PORT_KRYLOV.md §4 (lines 520–522), approved with D1 to D12 on
2026-10-17, fixes "RSI is `rsvd A ((Aᴴ * A) ^ q * Ω)` and RBKI is `rsvd A (blockKrylovMatrix (Aᴴ *
A) Ω q)`, with no new names and the test matrix on the right". In that spelling RSI is indexed by
the number of power steps and RBKI by the number of blocks. The first draft of this note departed
from it twice (names for all four outputs, and RSI re-indexed by blocks as
`rsvd A ((Aᴴ * A) ^ (q - 1) * Ω)`, with a junk value at $q = 0$ and `1 ≤ q` in every RSI theorem);
both departures are now explicit decisions, BD3a and BD3b, and the recommendation below keeps the
approved RSI spelling.

**BD3a, names.** Two approved precedents conflict: the Krylov layer names its methods although each
is a composition (`cgIterate := galerkinInverse A (krylovMatrix A b q) *ᵥ b`), and the LowRank round
report states "a name exactly when the output is not a composition of named functions"
(`docs/design/LowRank-REPORT.md` §3, branch `lowrank/s7-s9`). Options: (i) no names (the brief);
(ii) names for all four (first draft); (iii) names for the block Krylov outputs only, `rbki` and
`nystromBKI`, with RSI and NysSI the unnamed compositions `rsvd A ((Aᴴ * A) ^ p * Ω)` and
`nystrom H (H ^ p * Ω)` (the reviewer's proposal). **Recommendation: (iii).** The block Krylov
outputs hide a `Fin q × l` reindexing and the change of variables
$\mathcal{K}_q(\mathbf{A}\mathbf{A}^{\mathsf{H}}, \mathbf{A}\mathbf{\Omega}) =
\mathbf{A}\,\mathcal{K}_q(\mathbf{A}^{\mathsf{H}}\mathbf{A}, \mathbf{\Omega})$, so a name buys
readable statements and searchable theorem names (`integral_specNorm_sub_rbki_sq_le_…`), at the
cost of one rewrite (`rbki_def`) before an `rsvd` lemma applies; an RSI output is a power times the
test matrix, short enough to read, and naming it would add a second spelling of an approved one.

**BD3b, the RSI index.** Options: (i) $p$ = number of power steps, `rsvd A ((Aᴴ * A) ^ p * Ω)` as
approved: no junk value, no hypothesis, bounds in $e^{-8p\gamma}$ and
$R^{1/(2p+1)}$, and the only place the two indices meet is the comparison lemma
`rbki A Ω (p + 1)` against RSI at $p$; (ii) $q$ = blocks, TW's $q$ (RSI with $q = 1$ is RSVD),
which needs $q - 1$ in the definition. **Recommendation: (i)**, subtraction-free and as approved.
The docstrings state TW's count: RBKI with $q$ blocks is TW's $m = 2q$ multiplications, RSI with
$p$ power steps is $m = 2p + 2$, NysBKI with $q$ blocks and NysSI with $p$ power steps are
$m = q$ and $m = p + 1$ products with $\mathbf{H}$.

```lean
/-- \mathsf{rbki}(\mathbf{A}, \mathbf{\Omega}, q) := \mathsf{rsvd}(\mathbf{A},
\mathbf{K}_q(\mathbf{A}^{\mathsf{H}}\mathbf{A}, \mathbf{\Omega}))
= \mathbf{P}_{\mathcal{K}_q(\mathbf{A}\mathbf{A}^{\mathsf{H}}, \mathbf{A}\mathbf{\Omega})}\mathbf{A}. -/
noncomputable def rbki (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) (q : ℕ) : Matrix m n 𝕜 :=
  rsvd A (blockKrylovMatrix (Aᴴ * A) Ω q)
noncomputable def nystromBKI (H : Matrix n n 𝕜) (Ω : Matrix n l 𝕜) (q : ℕ) : Matrix n n 𝕜 :=
  nystrom H (blockKrylovMatrix H Ω q)
-- RSI and NysSI: no definition; `rsvd A ((Aᴴ * A) ^ p * Ω)`, `nystrom H (H ^ p * Ω)`
```

Odd $m$ for RBKI and RSI (Bjarkason's co-range form $\mathbf{A}\mathbf{P}_{\cdots}$, TW (5.3) and
Algorithm 5.5) is deferred (BD6); in the library it would be
`(rsvd Aᴴ (blockKrylovMatrix (A * Aᴴ) (A * Ω) j))ᴴ`, an `rsvd` of $\mathbf{A}^{\mathsf{H}}$ whose test
matrix is not Gaussian, so it needs its own Gaussian step.

Error spelling, as LowRank (PORT_LOWRANK.md:25–31): `A - rbki A Ω q`, `A - rsvd A ((Aᴴ * A) ^ p * Ω)`,
late truncation `A - truncatedSVD (rbki A Ω q) r`. Early truncation is deferred with the odd-count
forms (BD6, BD8): `earlyTruncatedRSVD A K r` (SketchedLowRank.lean:321) on the Krylov basis matrix
`K = blockKrylovMatrix (Aᴴ * A) Ω q` truncates $\mathbf{A}\mathbf{K}$ and so depends on the scaling of
that basis; it is basis-free (up to ties) only on an orthonormal Krylov basis $\mathbf{Q}$, where
$\mathbf{Q} \mapsto \mathbf{Q}\mathbf{V}$ sends $\llbracket\mathbf{A}\mathbf{Q}\rrbracket_r$ to
$\llbracket\mathbf{A}\mathbf{Q}\rrbracket_r\mathbf{V}$, and there its output
$\mathbf{P}_{\llbracket\mathbf{A}\mathbf{P}_{\mathcal{K}}\rrbracket_r}\mathbf{A}$ is the truncation of
the co-range form $\mathbf{A}\mathbf{P}_{\mathcal{K}}$. Musco–Musco's output
$\mathbf{Z} = \mathbf{Q}\bar{\mathbf{U}}_k$ (MM Algorithm 2, steps 4 to 6) is late truncation,
$\mathbf{Z}\mathbf{Z}^{\mathsf{H}}\mathbf{A} = \llbracket\mathbf{P}_{\mathcal{K}}\mathbf{A}\rrbracket_k$
(MM Lemma 2), which is what this round covers.

### 4.2 First theorems (deterministic, same file)

```lean
theorem rbki_def : rbki A Ω q = rsvd A (blockKrylovMatrix (Aᴴ * A) Ω q)
theorem rbki_eq_rangeProjector : rbki A Ω q = rangeProjector (blockKrylovMatrix (A * Aᴴ) (A * Ω) q) * A
theorem rbki_one : rbki A Ω 1 = rsvd A Ω            -- range invariance of rangeProjector
@[simp] theorem rbki_zero : rbki A Ω 0 = 0
theorem singularValues_sub_rbki_le_of_degree_lt (f : ℝ[X]) (hf : f.degree < q) (i : ℕ) :
    singularValues (A - rbki A Ω q) i ≤ singularValues (A - rsvd A (aeval (Aᴴ * A) f * Ω)) i
theorem singularValues_sub_rbki_le_sub_rsvd_pow (p i : ℕ) :
    singularValues (A - rbki A Ω (p + 1)) i ≤ singularValues (A - rsvd A ((Aᴴ * A) ^ p * Ω)) i
theorem singularValues_sub_rbki_le_of_le (h : q ≤ q') (i : ℕ) :
    singularValues (A - rbki A Ω q') i ≤ singularValues (A - rbki A Ω q) i
-- Nyström variants through the Gram correspondence (NystromGram.lean:104, :124, :202)
theorem nystromBKI_conjTranspose_mul_self (F : Matrix m n 𝕜) :
    nystromBKI (Fᴴ * F) Ω q = (rbki F Ω q)ᴴ * rbki F Ω q
theorem conjTranspose_mul_self_sub_nystromBKI (F : Matrix m n 𝕜) :
    Fᴴ * F - nystromBKI (Fᴴ * F) Ω q = (F - rbki F Ω q)ᴴ * (F - rbki F Ω q)
theorem _root_.Matrix.PosSemidef.sub_nystromBKI_eq (hH : H.PosSemidef) :
    H - nystromBKI H Ω q = (CFC.sqrt H - rbki (CFC.sqrt H) Ω q)ᴴ * (CFC.sqrt H - rbki (CFC.sqrt H) Ω q)
-- NysSI needs no new lemma: `Matrix.PosSemidef.sub_nystrom_eq` (NystromGram.lean:202) at the test
-- matrix `H ^ p * Ω`, with `H ^ p = (CFC.sqrt H ᴴ * CFC.sqrt H) ^ p`, is RSI of `CFC.sqrt H`
```

`singularValues_sub_rbki_le_of_degree_lt` is the whole Krylov content of TW §9: the range of
`A * aeval (Aᴴ * A) f * Ω` lies in that of `A * blockKrylovMatrix (Aᴴ * A) Ω q`
(`exists_aeval_mul_eq_blockKrylovMatrix_mul`), then Lemma 5.1 in singular-value form (§5, B1a). The
NysBKI Gram identity says NysBKI of $\mathbf{H}$ with $q$ products is RBKI of
$\mathbf{H}^{1/2}$ with depth $q$, which TW count as $2q$ products with $\mathbf{H}^{1/2}$.

## 5. Inventory: every result TW Theorems 9.1 and 9.2 rest on

"Lib" means on `origin/main`. Difficulty: E easy (under a day for a proof agent), M medium, H hard.

| TW result | Status | Lean name, or proposed statement | Home | Difficulty |
|---|---|---|---|---|
| Lemma 5.1, spectral and Frobenius | Lib | `specNorm_one_sub_rangeProjector_mul_le_of_range_le`, `frobNorm_…` (`Matrix/Norms/Projector.lean:280, :291`) | | |
| Lemma 5.1, singular values and every unitarily invariant norm | new | `singularValues_one_sub_rangeProjector_mul_le_of_range_le (h : range Y ≤ range B) (A) (i) : σᵢ((1 - P_B) A) ≤ σᵢ((1 - P_Y) A)`; gauge corollary `SymmetricGauge.matrixNorm_one_sub_rangeProjector_mul_le_of_range_le`. Proof: `rangeProjector_mono` (`Matrix/Basic/Projector.lean:380`), conjugation, `eigenvalue_le_eigenvalue_of_le` (`Matrix/Spectral/Weyl.lean:62`) | `Matrix/Spectral/SingularValueInequalities.lean` beside `singularValues_one_sub_rangeProjector_mul_le` (:346); gauge form in `Matrix/Norms/Projector.lean` | E |
| Lemma 8.3, diagonal psd reduction | not formalised (BD5) | general-$\mathbf{A}$ statements through frames instead, as the existing structural bounds do | | (M to state, costly to use) |
| Lemma 8.4, parallel sums | deferred (BD5) | if ever: `parallelSum A B := A - A * pinv (A + B) * A`, symmetry, PD formula, monotone and concave, Ando's norm inequality | `Matrix/Inequalities/ParallelSum.lean` (new); Mathlib has none (searched `parallel`, `harmonic`) | M (Ando's (4): H) |
| Prop 8.5, (8.2), any frame, every quadratic gauge | Lib | `SymmetricGauge.matrixNorm_conjTranspose_mul_self_sub_rsvd_le` (`LowRank/Structural/RangeFinder.lean:200`), `HasOrthonormalCols.specNorm_sub_rsvd_sq_le` (:249), competitor identity `HasOrthonormalCols.sub_mul_mul_pinv_mul_conjTranspose_eq` (:127) and Gram identity (:144) | | |
| Prop 8.5, (8.1) with the parallel sum | deferred | not on the path | | |
| Prop 8.6, (8.10) | Lib | `integral_frobNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix` (`RandomMatrix/Gaussian/BlockMoments.lean:155`) | | |
| Prop 8.6, (8.9) | Lib | `measureReal_not_frobNorm_mul_mul_pinv_sq_le_le_of_hasLaw_gaussianMatrix` (`BlockTail.lean:543`); only for tail versions of §9, which TW do not state | | |
| Theorem 8.1 (RSVD2) for a filtered matrix | Lib, as a template | `integral_specNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix` (`LowRank/Gaussian/RangeFinder.lean:300`); TW 9.1 needs it at the rank-$r$ competitor projector instead of $\mathbf{P}_{\mathbf{B}\mathbf{\Omega}}$, which is the same theorem at the test matrix `Ω * pinv (Zᴴ * Ω)` (row "competitor projector" below) | | |
| Theorem 8.7 | partly Lib (Frobenius $k \ge r+2$, spectral, Schatten 4 via FourthMoment) | not on the path | | |
| Lemma B.1, B.2 | Lib | `integral_frobNorm_mul_mul_sq_of_hasLaw_gaussianMatrix` (`Moments.lean:187`), `integral_frobNorm_pinv_sq_of_hasLaw_gaussianMatrix` (`InverseMoments/Frobenius.lean:69`), Chevet `SpectralNorm.lean:274` | | |
| Gaussian invariance and block independence | Lib | `hasLaw_conjTranspose_mul_of_hasLaw_gaussianMatrix` (`Invariance.lean:145`), `indepFun_conjTranspose_mul_of_hasLaw_gaussianMatrix` (:208), `ae_rank_mul_eq_min_…` (`Rank.lean:178`) | | |
| Lemma 9.3 part 1 (parity) | replaced | not needed: $T_{2j}(x) = T_j(2x^2 - 1)$ from Mathlib `Polynomial.Chebyshev.T_mul` (`RingTheory/Polynomial/Chebyshev.lean:1118`) and `T_two` (:137); new one-liner `eval_T_two_mul (j) (x) : (T ℝ (2 * j)).eval x = (T ℝ j).eval (2 * x ^ 2 - 1)` | `ForMathlib/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Growth.lean` | E |
| Lemma 9.3 part 2 | Mathlib | `Polynomial.Chebyshev.abs_eval_T_real_le_one` (`Analysis/SpecialFunctions/Trigonometric/Chebyshev/RootsExtrema.lean:46`) | | |
| Lemma 9.3 part 3, monotone on $[1,\infty)$ | new (prototype `monotoneOn_eval_T_real`, `Polynomial/Chebyshev/Growth.lean:68`) | `monotoneOn_eval_T_real (q : ℕ) : MonotoneOn (fun x => (T ℝ q).eval x) (Set.Ici 1)` | ForMathlib Chebyshev `Growth.lean` | E |
| Lemma 9.3 part 3, growth | new, from Lib | `exp_two_mul_le_one_add_div_one_sub (h₀ : 0 ≤ r) (h₁ : r < 1) : exp (2 * r) ≤ (1 + r) / (1 - r)` (TW (C.1)); `exp_mul_sqrt_div_two_le_eval_T_real (q) (h₀ h₁) : exp (2 * q * √r) / 2 ≤ (T ℝ q).eval ((1 + r) / (1 - r))` from the library's `sqrt_add_div_sqrt_sub_pow_div_two_le_eval_T_real` (ForMathlib Chebyshev `Growth.lean:68`) at $a = r$, $b = 1$, and (C.1) at $\sqrt r$ | ForMathlib `Growth.lean` (the scalar lemma in ForMathlib `Analysis/SpecialFunctions/Exp` or beside it) | E |
| Lemma 9.3 part 4, inverse | new | in implication form, no inverse function: `le_exp_of_eval_T_real_le (hq : 0 < q) (hx : 1 ≤ x) (h : (T ℝ q).eval x ≤ y) : x ≤ exp ((log (2 * y) / q) ^ 2 / 2)`; $1 \le y$ follows from `hx` and `one_le_eval_T_real` and is derived, not assumed. Mathlib has `T_real_cosh` (Chebyshev `Basic.lean:173`), `Real.arcosh` (`Analysis/SpecialFunctions/Arcosh.lean:61`), `Real.cosh_le_exp_half_sq` (`Trigonometric/Series.lean:154`); needs $\operatorname{arcosh} y \le \log 2y$ and strict monotonicity (from the radical form `eval_T_real_eq_of_one_le`, ForMathlib `Growth.lean:41`) | ForMathlib `Growth.lean` | E to M |
| Lemma 9.3 part 5, supporting lines | new | `hasSupportingLineOn_mul_eval_T_sq (j : ℕ) (hx : 1 ≤ x) : HasSupportingLineOn (fun y => y * ((T ℝ j).eval (2 * y - 1)) ^ 2) (Set.Ici 0) x`, which is TW's $x T_{2j}(x^{1/2})^2$ rewritten by part 1. Proof: $\varphi'(t) \le 1 + 4tj^2 \le \varphi'(1)$ on $[0,1]$ by `abs_iterate_derivative_T_real_le` (`RootsExtrema.lean:334`, $\lvert T^{(k)}(x)\rvert \le T^{(k)}(1)$) with $T_j'(1) = j^2$ from `T_derivative_eq_U` (`RingTheory/Polynomial/Chebyshev.lean:853`) and $U_{j-1}(1) = j$, and $\varphi'$ monotone on $[1,\infty)$ (derivatives of $T_j$ nonnegative there), then the mean value inequality. The $x^{1/4}$ case of TW is not needed (§6.5) | `Polynomial/Chebyshev/Filter.lean` (new) | M (the hardest scalar item) |
| `cfc` on an invariant frame | new | `Matrix.IsHermitian.cfc_mul_eq_mul_diagonal_of_mul_eq (hA : A.IsHermitian) (hW : HasOrthonormalCols W) (hAW : A * W = W * Matrix.diagonal fun i => (d i : 𝕜)) (g : ℝ → ℝ) : cfc g A * W = W * Matrix.diagonal fun i => (g (d i) : 𝕜)`; the library has only the full eigendecomposition `cfc_eq_mul_diagonal_mul_conjTranspose` (`Matrix/Functions/HermitianCalculus.lean:112`) and `cfc_diagonal` (:171); the polynomial twin exists, `aeval_mul_eq_mul_aeval_of_mul_eq_mul` (`Matrix/Functions/Polynomial.lean:286`) | `Matrix/Functions/HermitianCalculus.lean` | E |
| supporting line, interface | new (BD9) | `def HasSupportingLineOn (f : ℝ → ℝ) (s : Set ℝ) (x : ℝ) : Prop := ∃ c, ∀ y ∈ s, f x + c * (y - x) ≤ f y`; bridge `ConvexOn.hasSupportingLineOn` for differentiable convex `f` (Mathlib's tangent-line inequality for convex functions, name to verify in `Analysis/Convex/Deriv.lean`); Mathlib has no subgradient for real functions (searched `Subgradient`) | `ForMathlib/Analysis/Convex/SupportingLine.lean` (new) | E |
| Lemma 9.4, scalar half | new | `HasSupportingLineOn.le_integral_comp [IsProbabilityMeasure μ] (h : HasSupportingLineOn φ s (∫ ω, X ω ∂μ)) (hX : ∀ ω, X ω ∈ s) (hi : Integrable X μ) (hφi : Integrable (φ ∘ X) μ) : φ (∫ ω, X ω ∂μ) ≤ ∫ ω, φ (X ω) ∂μ` | `ForMathlib/Analysis/Convex/Integral.lean` (exists, holds `ConcaveOn.le_map_integral_of_integral_mem` :38) | E |
| Lemma 9.4, quadratic-form half | new, generalises Lib | `apply_re_quadForm_le_re_quadForm_cfc_of_hasSupportingLineOn (hA : A.IsHermitian) (hAs : spectrum ℝ A ⊆ s) (hx : ‖toLp 2 x‖ = 1) (hφ : HasSupportingLineOn φ s (re (quadForm A x))) : φ (re (quadForm A x)) ≤ re (quadForm (cfc φ A) x)`; the convex version is `apply_re_quadForm_le_re_quadForm_cfc` (`Matrix/Functions/TraceFunctions.lean:84`) and the private weights lemma there gives the proof | `Matrix/Functions/TraceFunctions.lean` | E |
| Lemma 9.4, projection half | new | `apply_specNorm_mul_sq_le_specNorm_mul_sq_of_hasSupportingLineOn {A : Matrix m n 𝕜} {B : Matrix m p 𝕜} (hB : B * Bᴴ = cfc φ (A * Aᴴ)) (hP : IsStarProjection P) (h₀ : 0 < specNorm (P * A)) (hφ : HasSupportingLineOn φ (Set.Ici 0) (specNorm (P * A) ^ 2)) : φ (specNorm (P * A) ^ 2) ≤ specNorm (P * B) ^ 2` (TW (9.4): top eigenvector of $\mathbf{P}\mathbf{A}\mathbf{A}^{\mathsf{H}}\mathbf{P}$ lies in the range of $\mathbf{P}$) | `Matrix/Functions/TraceFunctions.lean` or `Matrix/Norms/Projector.lean` | E to M |
| Eckart–Young lower bound used in 9.4 | Lib | `singularValues_le_specNorm_sub_of_rank_le` (`Matrix/Spectral/LowRank.lean:591`) | | |
| Lemma 9.5, deterministic, head capture | new | §6.1 `HasOrthonormalCols.matrixNorm_one_sub_rangeProjector_mul_mul_le` | `LowRank/Structural/Filter.lean` (new) | M |
| Lemma 9.5, deterministic, error bound | new | §6.1 `SymmetricGauge.matrixNorm_conjTranspose_mul_self_sub_rsvd_cfc_le`. TW's printed Lemma 9.5 has $\|\mathbf{A}_3\varphi(\mathbf{A}_3)\|_p^2$ in its statement, but its proof (and Theorem 9.2) uses the Frobenius norm; the library version is the proof's | same | M |
| competitor projector (rank-$r$ $\mathbf{Q}$ of TW 9.1) | new, a corollary of Lib | `HasOrthonormalCols.specNorm_sub_rsvd_mul_pinv_sq_le (hZ) (hΩ) (B) : specNorm (B - rsvd B (Ω * pinv (Zᴴ * Ω))) ^ 2 ≤ specNorm (B - B * Z * Zᴴ) ^ 2 + specNorm ((B - B * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω)) ^ 2`. Proof: with $\mathbf{\Omega}' = \mathbf{\Omega}(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^+$ one has $\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega}' = \mathbf{I}$ under `hΩ` (the private `mul_pinv_self_of_rank_eq`, RangeFinder.lean:100, made public), so `(Ω'ᴴ * Z).rank = Z.rank`, `pinv 1 = 1`, and `HasOrthonormalCols.specNorm_sub_rsvd_sq_le` (RangeFinder.lean:249) at $\mathbf{\Omega}'$ is the inequality. Rank at most `card s` from `rank_rsvd_le` (SketchedLowRank.lean:135); range inside that of `B * Ω` from `range_mul_mul_pinv_mul_conjTranspose_le` (RangeFinder.lean:91) | `LowRank/Structural/RangeFinder.lean` | E (20 lines) |
| Lemma 9.5, expectation | new | §6.2, first block | `LowRank/Gaussian/BlockKrylov.lean` (new) | M (glue) |
| relative gap $\gamma$ | new (BD9) | `noncomputable def singularGapRatio (A) (i j : ℕ) : ℝ := (σᵢ - σⱼ) / (σᵢ + σⱼ)` with `singularGapRatio_nonneg`, `_le_one`, `(1 - γ)/(1 + γ) = σⱼ/σᵢ` | `Matrix/Spectral/SingularValueInequalities.lean` beside `singularGap` (:461) | E |
| truncation monotone in rank (MM, Theorem 10) | new | `truncatedSVD_rsvd_eq_rangeProjector_mul : truncatedSVD (rsvd A Ω) k = rangeProjector (truncatedSVD (rsvd A Ω) k) * A` (the left singular vectors of $\mathbf{P}\mathbf{A}$ lie in the range of $\mathbf{P}$) and `range_truncatedSVD_mono` (one `svdU` for every $k$, `Matrix/Spectral/LowRank.lean:79`), then Lemma 5.1 (B1a): `singularValues_sub_truncatedSVD_rsvd_le_of_le (h : k ≤ k') (i) : σᵢ(A - truncatedSVD (rsvd A Ω) k') ≤ σᵢ(A - truncatedSVD (rsvd A Ω) k)`, so every gauge; for the canonical truncation (with ties a statement for every best approximation may fail) | `LowRank/Structural/Truncation.lean` | E to M |
| reverse Eckart–Young (Gu Thm 3.4, MM Lemma 15) | Lib | `specNorm_sub_sq_add_frobNorm_sub_truncatedSVD_sq_le_of_rank_le` (`BestRankApprox.lean:624`), `IsBestRankApprox.specNorm_sub_sq_add_frobNorm_sub_truncatedSVD_sq_le` (`Truncation.lean:154`) | | |
| Gu's projected form | Lib | `frobNorm_sub_truncatedSVD_rsvd_sq_le_frobNorm_sub_truncatedSVD_sq_add` (`Truncation.lean:199`) | | |
| polynomial filter on an SVD | Lib | `IsSVD.mul_aeval_conjTranspose_mul_self` (`Matrix/Functions/Polynomial.lean:310`), `aeval_mul_conjTranspose_self_mul` (:298), `singularValues_pow_mul_conjTranspose_self_mul` (:332), `Matrix.IsHermitian.cfc_eq_aeval_of_forall_eval_eq` (:106) | | |
| HMT Prop 8.6 (RSI gapless) | new from prototype | `IsStarProjection.specNorm_mul_pow_le (hP : IsStarProjection P) (A) (j : ℕ) : specNorm (P * A) ^ (2 * j + 1) ≤ specNorm (P * ((A * Aᴴ) ^ j * A))`; prototype `LowRank/Structural/PowerIteration.lean:155` (`specNorm_residual_pow_le`), or as the convex case of the Lemma 9.4 projection half | `Matrix/Norms/Projector.lean` | E |
| frames | Lib | `exists_isSVD_fromCols` (`Matrix/Spectral/SVD.lean:446`), `exists_hasOrthonormalCols_mul_mul_conjTranspose_eq_truncatedSVD(_completion)` (`Matrix/Spectral/LowRank.lean:516, :546`) | | |
| Theorem 9.1, 9.2 | new | §6 | `LowRank/Gaussian/BlockKrylov.lean`, `BlockKrylovGapless.lean`, `NystromBlockKrylov.lean` | |

**Lemma 8.3 in Lean, and why not.** The algebra is easy: for unitary $\mathbf{U}, \mathbf{V}$,
`blockKrylovMatrix ((U A Vᴴ)ᴴ (U A Vᴴ)) (V Ω) q = V * blockKrylovMatrix (Aᴴ A) Ω q` and
`rangeProjector (U X) = U P_X Uᴴ`, so `rbki (U A Vᴴ) (V Ω) q = U * rbki A Ω q * Vᴴ`, and
`hasLaw_mul_mul_of_hasLaw_gaussianMatrix` (`Invariance.lean:125`) moves the law. The cost is in
using it: every statement would be proved for a diagonal, sorted, square, psd matrix over `Fin`
indices and then transported, and the rectangular case needs padding. The existing LowRank layer
instead states the structural bounds for any frame `Z` and applies them to the top-$k$ singular
frame, with the Gaussian blocks $\mathbf{V}_1^{\mathsf{H}}\mathbf{\Omega}$,
$\mathbf{V}_2^{\mathsf{H}}\mathbf{\Omega}$ independent by `indepFun_conjTranspose_mul_…`. TW's
diagonal proofs translate line by line into that frame language (TW's $\mathbf{A}_1$ is
`A * W * Wᴴ` for the top-$r$ frame `W`, $\mathbf{\Omega}_\alpha$ is `Zᴴ * Ω`). Recommendation (BD5):
no Lemma 8.3; record it as "not needed" in the ledger. The equivariance identity above is a cheap
optional lemma if a consumer appears.

## 6. Headline statements

Deterministic statements over `[RCLike 𝕜]`; random statements over ℝ with
`(hX : HasLaw X (gaussianMatrix n l) μ)`, `X : Ω → Matrix n l ℝ`, as every LowRank Gaussian theorem
(LowRank D3/D4; CONTRIBUTING §5.1). Indices from 0: TW's $\sigma_{r+1}$ is `singularValues A r`,
TW's $\sigma_r$ with $r$ the target rank is `singularValues A h` with `hr : h + 1 = r` (the
CONTRIBUTING index-shift row), TW's $\sigma_s$ is `singularValues A t` with $t = s - 1$, so
TW's $r < s$ is `r ≤ t`, TW's $k \ge s + 1$ is `t + 2 ≤ Fintype.card l`, TW's
$\frac{s-1}{k-s}$ is `t / (card l - t - 1)` and $\lfloor\mathbf{A}\rfloor_{s-1}$ is
`truncatedSVD A t`. RBKI with $q$ blocks is TW's $m = 2q$, so $m - 2 = 2(q - 1)$; RSI with $p$ power steps is $m = 2p + 2$, so $m - 2 = 2p$. The source's small constants (4, 8, 16)
are written in the statements (§5.2 rule 2). Names are provisional; incomparable bounds are named by
what distinguishes them (§5.2 rule 4).

### 6.1 The filtered range finder (TW Lemma 9.5, deterministic; `LowRank/Structural/Filter.lean`)

The filter is a real function $g$ through `cfc` on $\mathbf{A}^{\mathsf{H}}\mathbf{A}$, so that
polynomials (RSI, RBKI) and the non-polynomial filters of TW's printed Nyström shapes
($T_{2m-3}(\sqrt{x/\sigma_s})$, $x^{m-3/2}$; BD7) are both instances; a polynomial corollary in `aeval` form follows by `cfc_eq_aeval_of_forall_eval_eq`.
`W` is an invariant frame for the head (TW's $\mathbf{A}_1$), `Z` a frame containing it (TW's
$\mathbf{\Omega}_\alpha = \mathbf{Z}^{\mathsf{H}}\mathbf{\Omega}$):

```lean
variable {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜} (g : ℝ → ℝ)
  {W : Matrix n r 𝕜} (hW : HasOrthonormalCols W) {d : r → ℝ}
  (hAW : Aᴴ * A * W = W * Matrix.diagonal fun i => (d i : 𝕜))
  {Z : Matrix n s 𝕜} (hZ : HasOrthonormalCols Z) (hΩ : (Ωᴴ * Z).rank = Z.rank)
  (hWZ : LinearMap.range W.mulVecLin ≤ LinearMap.range Z.mulVecLin)
  {c : ℝ} (hc : 0 < c) (hg : ∀ i, c ≤ |g (d i)|)

/-- head capture: (I - P_{A g(AᴴA) Ω}) A W Wᴴ is at most c⁻¹ times the sketch residual -/
theorem HasOrthonormalCols.matrixNorm_one_sub_rangeProjector_mul_mul_le (Φ : SymmetricGauge) :
    Φ.matrixNorm ((1 - rangeProjector (A * cfc g (Aᴴ * A) * Ω)) * (A * W * Wᴴ)) ≤
      c⁻¹ * Φ.matrixNorm ((A * cfc g (Aᴴ * A) - A * cfc g (Aᴴ * A) * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω))
/-- TW Lemma 9.5 deterministic, every quadratic gauge (so Schatten p ≥ 2 squared), in the
`Eᴴ * E` orientation of RangeFinder.lean:200 -/
theorem SymmetricGauge.matrixNorm_conjTranspose_mul_self_sub_rsvd_cfc_le (Φ : SymmetricGauge) :
    Φ.matrixNorm ((A - rsvd A (cfc g (Aᴴ * A) * Ω))ᴴ * (A - rsvd A (cfc g (Aᴴ * A) * Ω))) ≤
      Φ.matrixNorm ((A - A * W * Wᴴ)ᴴ * (A - A * W * Wᴴ)) + c⁻¹ ^ 2 * Φ.matrixNorm (Mᴴ * M)
-- with M the sketch residual of the head-capture lemma; spectral and Frobenius corollaries
```

Proof plan (TW (9.5) to (9.7) in frame language): with $\mathbf{B} = \mathbf{A}g(\mathbf{A}^{\mathsf{H}}\mathbf{A})$,
`hAW` and the invariant-frame lemma `Matrix.IsHermitian.cfc_mul_eq_mul_diagonal_of_mul_eq` (new,
§5, B1a) give $\mathbf{B}\mathbf{W} = \mathbf{A}\mathbf{W}g(\mathbf{D})$, so
$\mathbf{A}\mathbf{W}\mathbf{W}^{\mathsf{H}} = \mathbf{B}\mathbf{W}g(\mathbf{D})^{-1}\mathbf{W}^{\mathsf{H}}$
and $\|g(\mathbf{D})^{-1}\|_2 \le c^{-1}$; $\mathbf{B}\mathbf{W} = \mathbf{B}\mathbf{Z}\mathbf{Z}^{\mathsf{H}}\mathbf{W}$;
the competitor identity (RangeFinder.lean:127) for $\mathbf{B}$ and $\mathbf{Z}$ gives
$(\mathbf{I} - \mathbf{P})\mathbf{B}\mathbf{Z}\mathbf{Z}^{\mathsf{H}} = -(\mathbf{I} - \mathbf{P})\mathbf{M}\mathbf{Z}^{\mathsf{H}}$
with $\mathbf{P} \succeq \mathbf{P}_{\mathbf{B}\mathbf{\Omega}(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^+}$.
The error bound adds the coarse split $(\mathbf{I}-\mathbf{P})\mathbf{A}\mathbf{A}^{\mathsf{H}}(\mathbf{I}-\mathbf{P})
= (\mathbf{I}-\mathbf{P})(\mathbf{E}\mathbf{E}^{\mathsf{H}} + \mathbf{A}\mathbf{W}\mathbf{W}^{\mathsf{H}}\mathbf{A}^{\mathsf{H}})(\mathbf{I}-\mathbf{P})$,
$\mathbf{E} = \mathbf{A} - \mathbf{A}\mathbf{W}\mathbf{W}^{\mathsf{H}}$ (cross terms vanish), the gauge
triangle inequality and contraction by the projector; the split lives on the $m \times m$ side, and
`Φ.matrixNorm_mul_conjTranspose_self` (`Matrix/Norms/UnitarilyInvariant.lean:191`) moves it once to
the statement's `Eᴴ * E` side, so the siblings rewrite into the existing structural bound. The two lemmas are separate because the
truncated theorems use the head capture alone (§7). Prototype: `LowRank/PolynomialMethods/PolynomialFilter.lean`
(`specNorm_residual_sq_le_filterTailMaxAbs_div_filterHeadMinAbs` :310) has the mathematics with
`Fin`-indexed blocks and bundled hypotheses; its shapes are not reused.

### 6.2 Gapped bounds (TW Theorem 9.2; `LowRank/Gaussian/BlockKrylov.lean`)

```lean
/-- Lemma 9.5 in expectation, polynomial filter (head pointwise, tail in the D8 interval form;
the padded indices are covered by `x = 0`) -/
theorem integral_specNorm_sub_rsvd_aeval_sq_le_of_hasLaw_gaussianMatrix (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) (f : ℝ[X]) {r t : ℕ} (hrt : r ≤ t)
    (ht : t + 2 ≤ Fintype.card l) {c a : ℝ} (hc : 0 < c)
    (hhead : ∀ i < r, c ≤ |f.eval (singularValues A i ^ 2)|)
    (htail : ∀ x ∈ Set.Icc 0 (singularValues A t ^ 2), |f.eval x| ≤ a) :
    ∫ ω, specNorm (A - rsvd A (aeval (Aᴴ * A) f * X ω)) ^ 2 ∂μ ≤
      singularValues A r ^ 2 +
        (a / c) ^ 2 * ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) * frobNorm (A - truncatedSVD A t) ^ 2

/-- TW Theorem 9.2, RBKI, spectral -/
theorem integral_specNorm_sub_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {h r t q : ℕ} (hr : h + 1 = r)
    (hrt : r ≤ t) (ht : t + 2 ≤ Fintype.card l) (hq : 1 ≤ q) :
    ∫ ω, specNorm (A - rbki A (X ω) q) ^ 2 ∂μ ≤
      singularValues A r ^ 2 +
        4 * Real.exp (-8 * ((q : ℝ) - 1) * Real.sqrt (singularGapRatio A h t)) *
          ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) * frobNorm (A - truncatedSVD A t) ^ 2
```

The RBKI proof is the first lemma at
$f(y) = T_{q-1}(2y/\sigma_t^2 - 1)$, degree $q - 1$, then `singularValues_sub_rbki_le_of_degree_lt`:
$|f(x)| \le 1$ for $x \in [0, \sigma_t^2]$ (Mathlib part 2 after the affine change), and for $i < r$,
$f(\sigma_i^2) = T_{2q-2}(\sigma_i/\sigma_t) \ge T_{2q-2}(\sigma_h/\sigma_t) =
T_{2q-2}(\tfrac{1+\gamma}{1-\gamma}) \ge \tfrac12 e^{4(q-1)\sqrt\gamma}$ (parts 1 and 3), so
$(a/c)^2 \le 4e^{-8(q-1)\sqrt\gamma}$, which is TW's $4e^{-4(m-2)\sqrt\gamma}$. The case
$\sigma_t = 0$ makes the filter degenerate; there $\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}} = 0$
and the error is zero almost surely (`ae_rsvd_eq_self_of_hasLaw_gaussianMatrix`,
RangeFinder.lean:99, with `rbki_one` and monotonicity in $q$), so the statement needs no positivity
hypothesis; if the proof agent finds this case costly, `0 < singularValues A t` is added and
recorded.

Siblings, same hypotheses:
- **Frobenius**: `frobNorm (A - rbki A (X ω) q) ^ 2 ≤ frobNorm (A - truncatedSVD A r) ^ 2 + …`;
- **every quadratic gauge** (Schatten $p \ge 2$ squared): Gram form, the shape of
  `integral_matrixNorm_conjTranspose_mul_self_sub_rsvd_le_of_hasLaw_gaussianMatrix`
  (RangeFinder.lean:135); TW's statement is for Schatten $2 \le p \le \infty$;
- **RSI** at $p$ power steps: `rsvd A ((Aᴴ * A) ^ p * X ω)`, $f = X^p$, no hypothesis on $p$, term
  `Real.exp (-8 * p * singularGapRatio A h t)` with no factor 4 (TW's $e^{-4(m-2)\gamma}$ at
  $m = 2p + 2$; the ratio is $((1-\gamma)/(1+\gamma))^{4p} \le e^{-8p\gamma}$ by part 3's scalar
  lemma).

Order: spectral first (it is the one MM's argument needs), Frobenius second, gauge third.

### 6.3 Gapless bounds, Musco–Musco form (`LowRank/Gaussian/BlockKrylovGapless.lean`)

```lean
/-- gapless, truncated output, spectral; also for `rbki` without truncation -/
theorem integral_specNorm_sub_truncatedSVD_rbki_sq_le_one_add_sq_mul_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {r q : ℕ}
    (hr : r + 2 ≤ Fintype.card l) (hq : 1 ≤ q) {ε : ℝ} (hε : 0 < ε) :
    ∫ ω, specNorm (A - truncatedSVD (rbki A (X ω) q) r) ^ 2 ∂μ ≤
      (1 + ε) ^ 2 * singularValues A r ^ 2 +
        4 * Real.exp (-8 * ((q : ℝ) - 1) * Real.sqrt (ε / (2 + ε))) *
          ((r : ℝ) / ((Fintype.card l : ℝ) - r - 1)) * frobNorm (A - truncatedSVD A r) ^ 2

/-- O(log(n/ε)/√ε) depth suffices. Asymptotic: <the theorem above> -/
theorem exists_forall_integral_specNorm_sub_truncatedSVD_rbki_sq_le :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l : Type} [Fintype m] [Fintype n] [Fintype l] …
      (μ) (X) (A : Matrix m n ℝ) (r q : ℕ) (ε : ℝ), HasLaw X (gaussianMatrix n l) μ →
      r + 2 ≤ Fintype.card l → 0 < ε → ε ≤ ε₀ →
      C * Real.log (Fintype.card n / ε) / Real.sqrt ε ≤ q →
      ∫ ω, specNorm (A - truncatedSVD (rbki A (X ω) q) r) ^ 2 ∂μ ≤ (1 + ε) * singularValues A r ^ 2
```

The $\log n$ enters through $\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2 \le
\lvert n \rvert\,\sigma_r^2$ and $r/(\ell - r - 1) \le r \le \lvert n \rvert$, absorbed into $C$. When
$r \ge \lvert n \rvert$, $\sigma_r = 0$ and $\operatorname{rank}\mathbf{A} \le \lvert n \rvert \le r \le \ell - 2$, so
the error is zero almost surely (`ae_rsvd_eq_self_of_hasLaw_gaussianMatrix`, `rbki_one`,
monotonicity in $q$); $\log(\lvert n \rvert/\varepsilon)$ suffices. This is MM Theorem 10 in
expectation with explicit constants, and the statement MT Theorem 11.11 makes without proof
(PORT_KRYLOV.md:536–539). The proof is §7.2.

**Constants.** PORT_KRYLOV.md:536–539 expected MT 11.11's constant to be "an `irreducible_def`
expected to differ from MT's". This note departs from that expectation: the ε-form's constants
($4$, $8$, $\varepsilon/(2+\varepsilon)$) are explicit and small, so §5.2 rule 2 writes them in the
statement. They are this note's derivation, not a printed source: $4$ and $8$ come from TW Theorem 9.2
(RBKI line at $m = 2q$), $\varepsilon/(2+\varepsilon)$ from MM Theorem 10's case split (its proof,
with $(1+\varepsilon)$ in place of MM's $(1+\varepsilon/2)$); the docstring cites both, says the
statement is composed here, and gives no `MuscoMusco2015` constant as printed. The asymptotic form's
$C$ is existential, as rule 3 requires.

### 6.4 Gapless bounds, Tropp–Webber form (TW Theorem 9.1; same file)

```lean
/-- TW Theorem 9.1, RBKI -/
theorem integral_specNorm_sub_rbki_sq_le_mul_exp_of_hasLaw_gaussianMatrix (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) {r q : ℕ} (hr : r + 2 ≤ Fintype.card l) (hq : 2 ≤ q)
    (hσ : 0 < singularValues A r) :
    ∫ ω, specNorm (A - rbki A (X ω) q) ^ 2 ∂μ ≤
      singularValues A r ^ 2 *
        Real.exp (Real.log (4 * rangeFinderTailRatio A r (Fintype.card l)) ^ 2 / (16 * ((q : ℝ) - 1) ^ 2))
/-- TW Theorem 9.1, RSI at p power steps (m = 2p + 2) -/
theorem integral_specNorm_sub_rsvd_pow_mul_sq_le_mul_rpow_of_hasLaw_gaussianMatrix … (p : ℕ) (hσ) :
    ∫ ω, specNorm (A - rsvd A ((Aᴴ * A) ^ p * X ω)) ^ 2 ∂μ ≤
      singularValues A r ^ 2 * rangeFinderTailRatio A r (Fintype.card l) ^ (1 / (2 * (p : ℝ) + 1))
```

with the plain definition (one formula in four statements, CONTRIBUTING §4 "named quantities")
`rangeFinderTailRatio A r l := 1 + r / (l - r - 1) * frobNorm (A - truncatedSVD A r) ^ 2 / singularValues A r ^ 2`,
which is TW (RSVD2)'s spectral bound divided by $\sigma_r^2$ and so not Krylov-specific (its home is
`LowRank/Gaussian/RangeFinder.lean`, beside the bound it normalises), so TW's
$\log(4 + \tfrac{4r}{k-r-1}\sum_{i>r}\sigma_i^2/\sigma_{r+1}^2)$ is `log (4 * rangeFinderTailRatio …)` and
$\tfrac{1}{4(m-2)^2} = \tfrac{1}{16(q-1)^2}$. Hypotheses checked minimal: `2 ≤ q` (at $q = 1$ the right
side is $\sigma_r^2$, false), `0 < singularValues A r` (normalisation).

Proof (TW §9.3 in frame language). RBKI: normalise by $\sigma_r$ (or carry it); let `W` be the top-$r$
right singular frame, $\mathbf{B} = \mathbf{A}\,T_{q-1}(2\mathbf{A}^{\mathsf{H}}\mathbf{A}/\sigma_r^2 - \mathbf{I})$,
and $\mathbf{Q}(\omega) = \mathbf{P}_{\mathbf{B}\mathbf{X}(\mathbf{W}^{\mathsf{H}}\mathbf{X})^+}$, of rank at most $r$.
(i) $\|\mathbf{A} - \mathsf{rbki}\|_2 \le \|(\mathbf{I} - \mathbf{Q})\mathbf{A}\|_2$ (range inclusion through B0).
(ii) $\|(\mathbf{I} - \mathbf{Q})\mathbf{A}\|_2 \ge \sigma_r$ (Eckart–Young, LowRank.lean:591).
(iii) $\varphi(y) = y\,T_{q-1}(2y/\sigma_r^2 - 1)^2$ has supporting lines on $[\sigma_r^2, \infty)$
(part 5, scaled) and $\mathbf{B}\mathbf{B}^{\mathsf{H}} = \varphi(\mathbf{A}\mathbf{A}^{\mathsf{H}})$
(`aeval_mul_conjTranspose_self_mul`), so the projection half of Lemma 9.4 gives
$\varphi(\|(\mathbf{I}-\mathbf{Q})\mathbf{A}\|^2) \le \|(\mathbf{I}-\mathbf{Q})\mathbf{B}\|^2$ pointwise and the scalar half
moves $\varphi$ outside the integral. (iv) The competitor-projector corollary, the frame and
almost-sure-rank glue made public in B5a, and BlockMoments:155 give
$\mathbb{E}\|(\mathbf{I}-\mathbf{Q})\mathbf{B}\|^2 \le \sigma_r^2 + \tfrac{r}{\ell-r-1}\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2$,
since $|T_{q-1}| \le 1$ on the tail. (v) $T_{2q-2}(\sqrt{x})^2 \le \varphi(x)$ for $x \ge 1$ and part 4
invert. RSI at $p$ power steps is the same with $\varphi(y) = y^{2p+1}$, convex, so HMT
Proposition 8.6 (`IsStarProjection.specNorm_mul_pow_le`, from the prototype's `specNorm_residual_pow_le`)
replaces Lemma 9.4 and no Chebyshev fact is used.

### 6.5 Nyström variants (BD7; `LowRank/Gaussian/NystromBlockKrylov.lean`)

Through `Matrix.PosSemidef.sub_nystromBKI_eq`, every RBKI bound for $\mathbf{F} = \mathbf{H}^{1/2}$
becomes a NysBKI bound: $\|\mathbf{H} - \mathsf{nystromBKI}(\mathbf{H}, \mathbf{\Omega}, q)\|_{S_p} =
\|\mathbf{F} - \mathsf{rbki}(\mathbf{F}, \mathbf{\Omega}, q)\|_{S_{2p}}^2$, with
$\sigma_i(\mathbf{F})^2 = \lambda_i(\mathbf{H})$, $\|\mathbf{F} - \llbracket\mathbf{F}\rrbracket_t\|_{\mathsf{F}}^2 =
\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_t\|_*$, and gap ratio of $\mathbf{F}$ at least half that of
$\mathbf{H}$ (TW's $\sqrt{(1+\gamma)/(1-\gamma)} \ge (1+\gamma/2)/(1-\gamma/2)$, a scalar lemma). The
resulting gapped NysBKI bound,
$$\mathbb{E}\|\mathbf{H} - \mathsf{nystromBKI}(\mathbf{H}, \mathbf{\Omega}, q)\|_2 \le \lambda_r(\mathbf{H}) +
4e^{-4\sqrt2\,(q-1)\sqrt{\gamma}}\,\frac{t}{\ell - t - 1}\,\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_t\|_*\,,$$
is in the Nyström-native shape of TW Corollary 8.2 (unsquared, nuclear tail). NysSI at $p$ power
steps, `nystrom H (H ^ p * Ω)`, is RSI of $\mathbf{H}^{1/2}$ at $p$ by `Matrix.PosSemidef.sub_nystrom_eq`
and gets $e^{-4p\gamma}$, with $\gamma$ from the eigenvalues of $\mathbf{H}$ directly
($(\lambda_t/\lambda_h)^{2p} = ((1-\gamma)/(1+\gamma))^{2p}$).

**Comparison with TW's printed lines (checked against the PDF, pages 39 and 40).** TW Theorem 9.2
prints, for psd $\mathbf{A} = \mathbf{H}$, NysSI as
$\mathbb{E}\|\mathbf{H} - \hat{\mathbf{H}}\|_p^2 \le \|\mathbf{H} - \lfloor\mathbf{H}\rfloor_r\|_p^2 + e^{-4(m-3/2)\gamma}\tfrac{s-1}{k-s}\|\mathbf{H} - \lfloor\mathbf{H}\rfloor_{s-1}\|_{\mathsf{F}}^2$
and NysBKI with $4e^{-4(m-3/2)\sqrt{2\gamma}}$; Theorem 9.1 prints NysSI with rate $1/(m - 1/2)$ and
NysBKI with $1/(8(m-3/2)^2)$, on $\log(\mathbb{E}\|\mathbf{H} - \hat{\mathbf{H}}\|^2/\sigma_{r+1}(\mathbf{H})^2)$
with $\sum\sigma_i(\mathbf{H})^2/\sigma_{r+1}(\mathbf{H})^2$. All four are squared norms of
$\mathbf{H}$ itself. TW lose half a step as follows: they bound
$\|\mathbf{H} - \mathbf{H}\langle\mathbf{M}\rangle\| = \|(\mathbf{I}-\mathbf{Q})\mathbf{H}^{1/2}\|^2 =
\|(\mathbf{I}-\mathbf{Q})\mathbf{H}(\mathbf{I}-\mathbf{Q})\| \le \|(\mathbf{I}-\mathbf{Q})\mathbf{H}\|$
(proof of 9.2, NysSI paragraph) and then run Lemma 9.5 on $\mathbf{H}$ with the non-polynomial filter
$\varphi(x) = T_{2m-3}(\sqrt{x/\sigma_s})$, so that $\mathbf{H}\varphi(\mathbf{H})$ is an even polynomial of
degree $2m - 2$ in $\mathbf{F} = \mathbf{H}^{1/2}$ inside $\mathbf{F}\,\mathcal{K}_m(\mathbf{F}^2, \mathbf{\Omega})$;
in $\mathbf{F}$-units their filter is $x\,T_{2m-3}(x)$, one Chebyshev degree short of the $T_{2m-2}(x)$
the Gram route uses, and the tail weights are $\sigma_i(\mathbf{H})^2$, which is where their squared
tail comes from. The Gram route keeps the exact identity
$\|\mathbf{H} - \mathsf{nystromBKI}\|_{S_p} = \|\mathbf{F} - \mathsf{rbki}(\mathbf{F})\|_{S_{2p}}^2$ and applies
the RBKI line to $\mathbf{F}$ at depth $q$, with $\gamma_{\mathbf{F}} \ge \gamma_{\mathbf{H}}/2$
(verified: $(1+\gamma)(1-\gamma/2)^2 - (1-\gamma)(1+\gamma/2)^2 = \gamma^3/2 \ge 0$), giving
$4e^{-4\sqrt2(q-1)\sqrt{\gamma}}$ against TW's $4e^{-4\sqrt2(q-3/2)\sqrt{\gamma}}$ in the other shape.
For the gapless lines the Gram route gives rate $1/(16(q-1)^2)$ on
$\log(\mathbb{E}\|\mathbf{H} - \hat{\mathbf{H}}\|/\lambda_{r+1})$ with the nuclear tail ratio, against TW's
$1/(8(q-3/2)^2)$ on the squared quantity with the Frobenius tail ratio. By Jensen each implies a
bound of the other's shape with a worse constant; neither dominates (§5.2 rule 4: they may coexist).
The NysBKI and NysSI docstrings say: "TW Theorem 9.2 (NysBKI) is stated for
$\mathbb{E}\|\mathbf{H} - \hat{\mathbf{H}}\|_p^2$ with a squared Frobenius tail and exponent
$4(m - 3/2)\sqrt{2\gamma}$; this statement is the Nyström-native shape of TW Corollary 8.2, obtained
from the RBKI line at $\mathbf{H}^{1/2}$; the two are incomparable." TW's printed shapes need the
`cfc` filter of §6.1 at $g(y) = \varphi(\sqrt y)$ (non-polynomial) and are optional (BD7).

## 7. Truncated variants and the Musco–Musco argument

### 7.1 What is feasible

| Output | Norm | Gapped (TW 9.2 shape) | Gapless |
|---|---|---|---|
| `truncatedSVD (rbki A Ω q) r` | Frobenius | yes, same right side as untruncated: Gu's projected form `frobNorm_sub_truncatedSVD_rsvd_sq_le_frobNorm_sub_truncatedSVD_sq_add` (Truncation.lean:199) at test matrix `blockKrylovMatrix (Aᴴ * A) Ω q`, then $\|(\mathbf{I}-\mathbf{P})\llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}$ by the head-capture lemma and its expectation | no (MM Theorem 11 needs MM Lemma 9 properties 2 and 3; deferred) |
| same | spectral | yes, same right side: reverse Eckart–Young `IsBestRankApprox.specNorm_sub_sq_add_frobNorm_sub_truncatedSVD_sq_le` (Truncation.lean:154) turns the Frobenius excess into spectral excess | yes, §6.3 (MM case split) |
| same | Schatten $2 < p < \infty$ | only the weaker unsquared form through `SymmetricGauge.matrixNorm_sub_truncatedSVD_rsvd_le` (Truncation.lean:73, HMT 9.3); optional | no |
| `truncatedSVD (rsvd A ((Aᴴ * A) ^ p * Ω)) r` | Frobenius, spectral | yes, as RBKI | spectral ε-form, as RBKI with $\gamma$ in place of $\sqrt\gamma$ |
| `truncatedSVD (nystromBKI …) r` | nuclear, spectral | through the Gram correspondence and `Matrix.PosSemidef.nuclearNorm_sub_truncatedSVD_nystrom` (Truncation.lean:245–291); optional | optional |

The TW §9.1 sentence ("the gapped error bounds remain valid even when we replace $\hat{\mathbf{A}}$
with $\lfloor\hat{\mathbf{A}}\rfloor_r$, due to the reverse Eckart–Young inequality") is the spectral
row, reached through the Frobenius row; the library already holds both tools for `rsvd`, and
`rbki_def` makes them apply.

Statements, beside §6.2: `integral_frobNorm_sub_truncatedSVD_rbki_sq_le_singularGapRatio_…` and
`integral_specNorm_sub_truncatedSVD_rbki_sq_le_singularGapRatio_…`, with exactly the right sides
of §6.2 (Frobenius and spectral). Template: `integral_specNorm_sub_truncatedSVD_rsvd_sq_le_of_hasLaw_gaussianMatrix`
(RangeFinder.lean:560).

### 7.2 The Musco–Musco case split (proof of §6.3)

MM Theorem 10's argument, in the library's terms. Fix $\varepsilon > 0$. Let $h$ be the number of
indices $i$ with $\sigma_i \ge (1+\varepsilon)\sigma_r$ (0-indexed; $h \le r$ when $\sigma_r > 0$;
the case $\sigma_r = 0$ is the exact case of §6.2). It depends on $\mathbf{A}$ only, so the case
split is deterministic and commutes with the expectation.
- $h = 0$: $\|\mathbf{A} - \llbracket\mathsf{rbki}\rrbracket_r\|_2 \le \|\mathbf{A}\|_2 = \sigma_0 < (1+\varepsilon)\sigma_r$,
  since `truncatedSVD_rsvd_eq_rangeProjector_mul` (§5, B4) writes the truncated output as
  $\mathbf{\Pi}_r\mathbf{A}$, with $\mathbf{\Pi}_r$ the projector onto the nonzero left singular vectors of
  $\mathbf{P}\mathbf{A}$ (which lie in the range of $\mathbf{P}$), so the error is a projection residual and
  `singularValues_one_sub_rangeProjector_mul_le` applies.
- $h \ge 1$: the gapped truncated spectral bound at target rank $h$, head index $h - 1$, tail
  index $t = r$: $\gamma = \mathsf{gapRatio}(h-1, r) \ge \varepsilon/(2+\varepsilon)$ because
  $\sigma_{h-1} \ge (1+\varepsilon)\sigma_r$, and $\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_h\|_2 = \sigma_h <
  (1+\varepsilon)\sigma_r$; block size $r + 2 \le \ell$ is the gapless hypothesis. Then
  `singularValues_sub_truncatedSVD_rsvd_le_of_le` (rank $h \le r$, new, B4) moves from rank $h$ to
  rank $r$.
The untruncated twin replaces the last step by Lemma 5.1 alone:
$\|\mathbf{A} - \mathsf{rbki}\|_2 \le \|\mathbf{A} - \llbracket\mathsf{rbki}\rrbracket_h\|_2$ because
the range of $\mathbf{\Pi}_h$ lies in the Krylov range.

### 7.3 What MM needs from the library

| MM | Library |
|---|---|
| Lemma 2 (best rank-$l$ approximation inside a subspace, Frobenius) | `HasOrthonormalCols.frobNorm_sub_mul_truncatedSVD_le_of_rank_le` (`Matrix/Spectral/ProjectedLowRank.lean:76`), `HasOrthonormalCols.frobNorm_sub_truncatedSVD_rsvd` (`Truncation.lean:168`) |
| Lemma 3 (projection is spectrally optimal in a subspace) | `specNorm_one_sub_rangeProjector_mul_le_specNorm_sub_mul` (`Matrix/Norms/Projector.lean:258`) |
| Lemma 15 = Gu Theorem 3.4 (Frobenius excess to spectral excess) | `specNorm_sub_sq_add_frobNorm_sub_truncatedSVD_sq_le_of_rank_le` (`BestRankApprox.lean:624`) |
| Lemma 4 (Gaussian Frobenius sketch, probability 99/100) | replaced by expectations: BlockMoments.lean:155 |
| Lemma 5 (Chebyshev minimizing polynomial) | replaced by TW Lemma 9.3 parts 2 and 3 (B2a); prototype `chebyshevAmplifier` (`Polynomial/Chebyshev/Core.lean:46`) is not ported as a definition: the filter appears only inside proofs |
| Lemma 9 property 1 (head of rank $m$ captured) | head-capture lemma (§6.1) with Gu's projected form |
| Theorem 10 (spectral) | §6.3, §7.2 |
| Lemma 9 properties 2, 3; Theorems 11, 12 (Frobenius, per-vector) | deferred. They need the per-index accumulation of MM's error function; available tools: `IsStarProjection.singularValues_mul_le` (`SingularValueInequalities.lean:338`), Courant–Fischer (`Matrix/Spectral/CourantFischer.lean`), Cauchy interlacing (`Matrix/Spectral/Interlacing.lean:53–105`), low-rank interlacing `singularValues_add_le_of_rank_le` (`SingularValueInequalities.lean:125`), Weyl (`Matrix/Spectral/Weyl.lean:90–185`), Mirsky (`Majorization/TraceInequalities.lean:227`) |
| Theorem 13 (gap-dependent, oversampled block) | its guarantee (2) (spectral) is covered by §6.2 and §7.1 with $t > r$; MM 13 also covers (1) Frobenius-relative and (3) per-vector, which are deferred with Theorems 11 and 12 |

Musco–Musco is cited for the case split (`MuscoMusco2015`, Theorem 10 and its proof) in the
docstrings of §6.3; the bibliography entry is added with the first citing file.

## 8. Files, imports, placement

| File | Content | Lines | Stage |
|---|---|---|---|
| `Krylov/Basic/BlockSpace.lean` (new) | §3 | 350 | B0 |
| `Krylov/LinearSystems/CG.lean` | one-column bridges (§3) | +30 | B0 |
| `Probability/Measurability/Krylov.lean` (new, named in D12) | `measurable_blockKrylovMatrix` | 40 | B0 |
| `Matrix/Spectral/SingularValueInequalities.lean` | Lemma 5.1 singular values; `singularGapRatio` and API | +80 | B1a |
| `Matrix/Norms/Projector.lean` | Lemma 5.1 gauge | +30 | B1a |
| `Matrix/Functions/HermitianCalculus.lean` | `Matrix.IsHermitian.cfc_mul_eq_mul_diagonal_of_mul_eq` (invariant frame) | +30 | B1a |
| `Matrix/Norms/Projector.lean` | HMT 8.6 power lemma `IsStarProjection.specNorm_mul_pow_le` | +40 | B1b (9.1 only) |
| `Matrix/Functions/TraceFunctions.lean` | Lemma 9.4 quadratic-form and projection halves | +80 | B1b (9.1 only) |
| `ForMathlib/Analysis/Convex/SupportingLine.lean` (new) | `HasSupportingLineOn`, convex bridge | 60 | B1b (9.1 only) |
| `ForMathlib/Analysis/Convex/Integral.lean` | Lemma 9.4 scalar half | +30 | B1b (9.1 only) |
| `ForMathlib/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Growth.lean` | parts 1 and 3 (B2a); part 4 (B2b) | +150 | B2a, B2b |
| `Polynomial/Chebyshev/Filter.lean` (new) | part 5 | 150 | B2b (9.1 only) |
| `LowRank/Structural/BlockKrylov.lean` (new) | §4 | 250 | B3 |
| `LowRank/Structural/Filter.lean` (new) | §6.1 | 300 | B4 |
| `LowRank/Structural/RangeFinder.lean` | competitor-projector corollary; `mul_pinv_self_of_rank_eq` made public | +30 | B4 |
| `LowRank/Structural/Truncation.lean` | `truncatedSVD_rsvd_eq_rangeProjector_mul`, monotonicity in rank | +60 | B4 |
| `LowRank/Gaussian/Filter.lean` (new) | Lemma 9.5 in expectation: gauge form, spectral and Frobenius corollaries, `integrable_` companions; frame, complement-frame and almost-sure-rank glue made public | 500 | B5a |
| `LowRank/Gaussian/BlockKrylov.lean` (new) | §6.2 RBKI and RSI instances (spectral, Frobenius, gauge), §7.1 truncated lines, integrability | 550 | B5b |
| `LowRank/Gaussian/RangeFinder.lean` | `rangeFinderTailRatio` and API | +30 | B6b |
| `LowRank/Gaussian/BlockKrylovGapless.lean` (new) | §6.3, §6.4 | 550 | B6a, B6b |
| `LowRank/Gaussian/NystromBlockKrylov.lean` (new) | §6.5 | 400 | B7 |

Placement (CONTRIBUTING §8 item 5): every addition outside the new files sits with its topic:
singular-value inequalities with `singularValues_one_sub_rangeProjector_mul_le`; projector norms
with the spectral and Frobenius range-inclusion lemmas; the invariant-frame `cfc` lemma with the
functional calculus of Hermitian matrices, beside `cfc_eq_mul_diagonal_mul_conjTranspose`;
quadratic-form Jensen with its convex version; the one-column CG bridges with `cgIterate`, since
`Krylov/Basic` does not import `LinearSystems`; `rangeFinderTailRatio` with the RSVD bound it
normalises; Chebyshev growth with the existing growth file (pure facts, no NLAlib vocabulary, so
ForMathlib); the filtered range finder as a LowRank structural topic (its statement is about `rsvd`
of a filtered sketch, not about Krylov spaces; its Gaussian form in `LowRank/Gaussian/Filter.lean`
for the same reason); RBKI and NysBKI in LowRank because a user looks for
low-rank approximation algorithms there, importing Krylov's block space (layer 4 imports layer 1).
One flag: `Polynomial/Chebyshev/Filter.lean` holds a single fact today; if it stays alone at the
end of the round it moves into ForMathlib's growth file. Krylov/ gains no LowRank vocabulary.

Mathlib search (O8 style): no block Krylov space, no parallel sum, no subgradient of a real
function, no monotonicity of $T_n$ on $[1,\infty)$ and no $1+\varepsilon$ growth bound; used:
`Polynomial.Chebyshev.T_mul`, `T_two`, `T_real_cosh`, `abs_eval_T_real_le_one`,
`abs_iterate_derivative_T_real_le`, `T_derivative_eq_U`, `one_le_eval_T_real`, `Real.arcosh`,
`Real.cosh_le_exp_half_sq`, `Matrix.replicateCol`, `Submodule.iSup`, `ConvexOn.map_integral_le`
(locators in §5; all verified at the shared Mathlib revision by the review). Deviations: none (all new
objects are additions; `HasSupportingLineOn` and `singularGapRatio` get §5.3 rows, BD9).

Note: `nlalib-block/.lake/packages/mathlib` is an empty checkout; the search was run in the shared
copy's Mathlib at the same revision.

## 9. Stage plan

Each checkpoint is one proof agent, one file or a short chain, in order.

| Stage | Content | Depends on | Path |
|---|---|---|---|
| **B0** | `blockKrylovMatrix`, `blockKrylovSpace`, matrix-, space- and method-level bridges, prefix, successor, shift, change of variables, polynomial inclusion, measurability | Krylov K0 | 9.2, 9.1 |
| **B1a** | Lemma 5.1 singular-value and gauge forms; `singularGapRatio`; invariant-frame `cfc` lemma | Matrix | 9.2 |
| **B2a** | Chebyshev parts 1 and 3 (composition, monotonicity, growth), scalar $e^{2r} \le (1+r)/(1-r)$ | Mathlib | 9.2 |
| **B3** | `rbki`, `nystromBKI` and the deterministic reductions of §4.2 | B0, B1a | 9.2, 9.1 |
| **B4** | filtered range finder (head capture, Lemma 9.5 deterministic), competitor-projector corollary, truncation as a projection and monotone in rank | B1a, B3 | 9.2, 9.1 |
| **B5a** | Lemma 9.5 in expectation (gauge, spectral, Frobenius, integrability), public Gaussian frame glue | B4 | 9.2, 9.1 |
| **B5b** | **TW Theorem 9.2** for RBKI and RSI: spectral, Frobenius, gauge; truncated spectral and Frobenius | B2a, B5a | 9.2 (headline) |
| **B6a** | gapless ε-form (§6.3), truncated and untruncated, with the asymptotic corollary | B5b | 9.1 (MM form) |
| **B1b** | `HasSupportingLineOn`, Lemma 9.4 (three halves), HMT 8.6 power lemma | Matrix, ForMathlib | 9.1 (TW form) |
| **B2b** | Chebyshev parts 4 and 5 | B2a | 9.1 (TW form) |
| **B6b** | **TW Theorem 9.1** for RBKI and RSI, `rangeFinderTailRatio` | B1b, B2b, B4, B5a | 9.1 (headline) |
| **B7** | Nyström variants by the Gram route (gapped, both gapless forms), and their truncations | B5b, B6a, B6b | Nyström lines |
| later | odd $m$ and early truncation (BD6); TW's printed Nyström shapes; Schatten-$p$ truncated; tail versions from (8.9); Frobenius and per-vector gapless (MM 11, 12); parallel sums and TW 8.7 for $k \in \{r, r+1\}$; Lemma 8.3; block grade, block Lanczos, block CG/GMRES theory | | |

**Critical path.** To Theorem 9.2: B0, B1a, B3, B4, B5a, B5b (B2a runs beside B3 to B5a). To
Theorem 9.1: the 9.2 path plus B6a for the Musco–Musco form; TW's exact constants need B1b, B2b
and B6b, which depend on B5a but not on B5b. Theorem 9.2 comes first although the request lists 9.1
first: TW's proof of 9.1 for RBKI uses the rank-$r$ competitor projector and the Gaussian glue of B4
and B5a anyway, and adds the only real-analysis items of the round (part 5, Lemma 9.4), so doing 9.2
first front-loads the cheap headline and gives the ε-form of 9.1 at once. B1b and B2b are
independent of B3 to B5b and may run in parallel with them (at most two proof agents at once,
CONTRIBUTING §11). Total about 3,800 lines for B0 to B7.

## 10. Risks, and what is deferred

1. **Lemma 9.3 part 5** (supporting lines of $y\,T_j(2y-1)^2$): derivatives of Chebyshev polynomials
   and a mean-value argument; the hardest scalar item. Mitigation: it is off the 9.2 path, and the
   ε-form (B6a) gives a gapless theorem without it. If it stalls, it goes to the scaffold with a
   `Proof:` note and B6b waits.
2. **Index bookkeeping**: `Fin q × l` columns, frames `W ⊆ Z` from `exists_isSVD_fromCols`, the
   almost-sure rank condition `(Xᴴ * Z).rank = Z.rank`, and complement frames for BlockMoments.
   The existing Gaussian RSVD proofs (RangeFinder.lean:135–300) are the template; B5a makes their
   private glue public, since B5b and B6b both need it (CONTRIBUTING §3). B5a is sized for the glue
   (500 lines) so that the corollaries of B5b do not fall to the scaffold.
3. **Degenerate cases**: $\sigma_t = 0$ in the gapped filter, $\sigma_r = 0$ in the gapless forms,
   $q \le 1$, ties among singular values in the truncation monotonicity (stated for the canonical
   `truncatedSVD`; a version for every best approximation may be false with ties).
4. **Nyström shapes**: the Gram route's statements differ in shape from TW's printed lines; the
   comparison is done (§6.5, checked against the PDF) and goes into the docstrings, so no proof
   agent should look for a bug there.
5. **Even multiplication counts only** (BD6): TW's theorems hold for every $m$; ours for even $m$
   for RBKI ($m = 2q$) and RSI ($m = 2p + 2$) and for every $m$ for the Nyström variants.
   Docstrings record the restriction.
6. **Names and index** (BD3a, BD3b): if the maintainer prefers no names at all, `rbki` and
   `nystromBKI` become rewrite lemmas and theorem names lengthen; if he prefers TW's block index for
   RSI, RSI statements gain `1 ≤ q` and `q - 1`; nothing else changes.

Deferred, with the gap recorded: parallel sums (no Matrix-layer object; Ando's Schatten inequality
is hard), Lemma 8.3 (not needed), Frobenius gapless bounds for RBKI (MM Theorem 11; TW call them
recent work [6, 8, 73]), per-vector guarantees (MM Theorem 12), Meyer et al.'s $k < r$ bounds, the
block Lanczos layer.

## 11. Dependence on branch `lowrank/s7-s9`

`git cherry` (read-only) shows three of its four commits already on `origin/main` (S7 and S9 as
`d45b977`, `71b1d63`, `c6435ee`). Only `43ba36f` is missing: `docs/design/LowRank-REPORT.md` (the
round report: 515 public names, the naming rule "a name exactly when the output is not a composition
of named functions" in §3, the deferral list in §9.1 naming "power and subspace iteration, block
Krylov, polynomial filters" and "HMT Proposition 8.6 would join `Structural/RangeFinder`") and
small dated status edits to `PORT_LOWRANK.md`, `LowRank-S0/S2a/S3/S4/S5/S7/S9.md` and
`Mathlib-deviations.md`. This round depends on no Lean from that branch: everything it uses
(truncation API, PCP, oblivious and Gaussian range finders, Nyström) is on main. It depends on the
report as documentation: BD3a is decided with its §3 rule in view, and B4 to B5b close part of its §9.1
deferral list, so the report should be merged before or with this note, and its §9.1 updated when
B5b lands.

## 12. Literature and bibliography

- `TroppWebber2023` (in `docs/references.bib`): Lemmas 5.1, 5.2, 8.3, 8.4, 9.3, 9.4, 9.5;
  Propositions 8.5, 8.6; Theorems 8.1, 8.7, 9.1, 9.2; Appendices B, C; §9.1 remark on truncation.
  Locators checked against the local text and PDF (pages 15, 33 to 46, 47 to 55).
- `Gu2015` (in the bib): Theorem 3.4 (reverse Eckart–Young), already cited by the library.
- `HalkoMartinssonTropp2011` (in the bib): Proposition 8.6 (power lemma, RSI gapless), Theorem 9.1.
- New key `MuscoMusco2015`: C. Musco and C. Musco, "Randomized block Krylov methods for stronger
  and faster approximate singular value decomposition", NeurIPS 2015, arXiv:1504.05477v4; Algorithm 2,
  Lemmas 2, 3, 5, 9, 15, Theorems 1, 10, 13. (PORT_KRYLOV §9 lists it; not yet in the bib.)
- `MartinssonTropp2020`: Theorem 11.11 (stated without proof; §6.3 proves an explicit version).
- Only if parallel sums are scheduled: Anderson and Duffin 1969, Ando 1994 (TW's [4], [5]).
- Result ids (new): `rbki-gapped-error`, `rsi-gapped-error`, `rbki-gapless-error`,
  `rsi-gapless-error`, `nysbki-gapped-error`, `nyssi-gapped-error`, `filtered-range-finder-bound`,
  `chebyshev-growth-gap`; reused: `range-finder-structural-bound` (the filtered bound generalises it).

## 13. Decisions for the maintainer

**BD1. One block definition or two.** (a) a single block definition, vector API refactored;
(b) separate `blockKrylovMatrix` with bridges, vector API untouched (D10(c), approved 2026-10-17);
(c) the block definition primary and `krylovMatrix` its one-column reindexing, all vector statements
unchanged. Recommendation: **(b)**; (c) if you want one definition literally; (a) not recommended
(2,000 to 3,000 lines of churn in proved files for no theorem). Under (b), B0 carries the
matrix-level bridge `blockKrylovMatrix_replicateCol`, the block structural lemmas and the "block CG
with one column is CG" bridge (§3), so later block algorithms do not reopen it and (b) to (c) is
cheap at any time.

**BD2. Block Krylov scope this round.** (a) the block space file B0 with its bridges, no block
algorithm;
(b) also block Lanczos/Arnoldi with a realisation theorem and block grade; (c) also block CG and
GMRES theory. Recommendation: **(a)**; TW needs nothing else. Block CG and GMRES need no new
definition when they come.

**BD3a. Names.** Already decided: PORT_KRYLOV §4 (approved 2026-10-17) spells RSI as
`rsvd A ((Aᴴ * A) ^ q * Ω)` and RBKI as `rsvd A (blockKrylovMatrix (Aᴴ * A) Ω q)` "with no new
names"; the LowRank report's rule agrees, the Krylov layer's `cgIterate` precedent does not. Options:
(i) no names, as approved; (ii) names for all four outputs (`rbki`, `rsi`, `nystromBKI`,
`nystromSI`; this note's first draft); (iii) names for the block Krylov outputs only, `rbki` and
`nystromBKI`, RSI and NysSI as the approved unnamed compositions (the reviewer's proposal).
Recommendation: **(iii)**, adopting the reviewer's proposal over the first draft's (ii): the block
outputs hide a `Fin q × l` reindexing and a change of variables worth a name, the RSI outputs are
short and already spelled by an approved decision. This changes the approved "no new names" for
RBKI and NysBKI only.

**BD3b. The RSI and NysSI index.** Options: (i) $p$ = number of power steps,
`rsvd A ((Aᴴ * A) ^ p * Ω)` and `nystrom H (H ^ p * Ω)`, as approved: no junk value, no hypothesis,
bounds in $e^{-8p\gamma}$ and $R^{1/(2p+1)}$, the two indices meet only in
`singularValues_sub_rbki_le_sub_rsvd_pow` (`rbki … (p + 1)`); (ii) TW's block index $q$ (RSI with
$q = 1$ is RSVD), which puts `q - 1` in a definition, a junk value at $q = 0$ and `1 ≤ q` in every RSI
theorem (the first draft did this without saying it changed an approved spelling). Recommendation:
**(i)**, as approved; docstrings translate to TW's $m$.

**BD4. Which gapless theorem.** (a) TW's exact Theorem 9.1 (Lemma 9.4, Lemma 9.3 parts 4 and 5);
(b) the Musco–Musco ε-form from the gapped theorem (§6.3), which also covers the truncated output and
yields the $O(\log(n/\varepsilon)/\sqrt\varepsilon)$ corollary; (c) both. Recommendation: **(c)**, in
the order 9.2, then (b), then (a).

**BD5. Lemma 8.3 and parallel sums.** (a) formalise both as in TW; (b) neither: general-$\mathbf{A}$
statements through frames, parallel sums deferred until a consumer needs (8.1) or TW 8.7 at
$k \in \{r, r+1\}$. Recommendation: **(b)**.

**BD6. Multiplication counts.** (a) even counts only (RBKI and RSI as range projections);
(b) also odd counts (Bjarkason's co-range forms), together with early truncation on an orthonormal
Krylov basis, which is the truncation of the co-range form (§4.1). Recommendation: **(a)** now, (b)
later as an optional stage.

**BD7. Nyström variants.** (a) the Gram-route statements (Nyström-native shape, from RBKI and RSI at
$\mathbf{H}^{1/2}$, no new analysis, exponents $q - 1$ and $p$); (b) TW's printed shapes (squared norm,
Frobenius tail, exponents $m - 3/2$, needs the non-polynomial `cfc` filter); (c) both. The two are
incomparable (§6.5). Recommendation: **(a)** now, (b) optional.

**BD8. Truncated variants.** (a) spectral and Frobenius gapped bounds for `truncatedSVD (rbki …) r`
and `truncatedSVD (rsvd A ((Aᴴ * A) ^ p * Ω)) r`, and the spectral gapless ε-form (explicit small
constants derived here, not an `irreducible_def` as PORT_KRYLOV §4 expected, §6.3); (b) also Schatten-$p$ truncated,
Frobenius gapless (MM Theorem 11) and per-vector (MM Theorem 12). Recommendation: **(a)**; (b)
deferred (MM Theorem 11 needs machinery the library lacks, and TW call it open-ended recent work).
Early truncation: on the Krylov basis matrix it is not basis-free; on an orthonormal Krylov basis it
is basis-free up to ties and is the truncation of the co-range form, so it is deferred with BD6
(§4.1).

**BD9. New vocabulary.** Two §5.3 rows: the relative gap `singularGapRatio A i j` (TW's $\gamma$),
and the supporting-line predicate `HasSupportingLineOn f s x` (ForMathlib, no Mathlib analogue);
also the plain definition `rangeFinderTailRatio` (§6.4), which needs no row.
Options: (a) both as proposed; (b) write $\gamma$ and the supporting-line condition out in each
statement. Recommendation: **(a)**; each appears in four or more statements.

## Decisions

Maintainer, 2026-10-18: "the gapless bounds are more important, but it is okay to defer them if
its a big task. other stuff looks good". So BD1 to BD9 are approved as recommended (BD1 (b), BD2
(a), BD3a (iii), BD3b (i), BD4 (c), BD5 (b), BD6 (a), BD7 (a), BD8 (a), BD9 (a)). Priority: the
gapless bounds (TW Theorem 9.1 and its truncated forms) are the more important target. The stage
order stays (Theorem 9.2 first, since the Musco–Musco ε-form gapless bound is derived from it), but
B6a and B6b are not optional; a gapless item is deferred only if it proves to be a large task, and
then the gap is recorded here. The deferred truncated Frobenius gapless bound (MM Theorem 11) is
revisited after B6b with the same rule.

## Implementation

Skeleton written 2026-10-18 (all statements of B0 to B7 with `sorry` proofs, stage markers
`-- Stage Bx` above each group, `-- SKELETON-NOTE:` above the statements with a proof caution).

### Skeleton changes

Departures from the signatures of §3 to §8, with the reason; none changes a decision.

1. **CG bridge (§3).** `cgIterate` takes a start, `cgIterate A b x₀ q`; the method-level bridge is
   `galerkinInverse_blockKrylovMatrix_replicateCol_mul … = replicateCol Unit (cgIterate A b 0 q)`
   (zero start). The note's `cgIterate A b q` was ill-typed.
2. **Invariant-frame `cfc` lemma (§5).** `Matrix.IsHermitian.cfc_mul_eq_mul_diagonal_of_mul_eq`
   drops `HasOrthonormalCols W`: each nonzero column of $\mathbf{W}$ is an eigenvector and a zero
   column maps to zero, so the hypothesis is not needed (§5.2, minimal hypotheses).
3. **Gauge form of Lemma 5.1 (§5, §8).** Placed in `Matrix/Norms/UnitarilyInvariant.lean`, beside
   `SymmetricGauge.matrixNorm_mul_le_of_isStarProjection`, not in `Matrix/Norms/Projector.lean`:
   `Projector.lean` is imported by `SingularValueInequalities.lean` and so cannot import the gauge
   file (cycle). The singular-value form is in `SingularValueInequalities.lean` as planned.
4. **Supporting-line Jensen (§5).** `HasSupportingLineOn.le_integral_comp` takes
   `∀ᵐ ω ∂μ, X ω ∈ t` in place of `∀ ω`, which is weaker and what a random variable gives.
5. **Chebyshev composition (§5).** `Polynomial.Chebyshev.eval_T_two_mul` is stated over any
   commutative ring and integer index (`T R (2 * j)`), Mathlib's generality for `T_mul`;
   Mathlib's `T` is `ℤ`-indexed, so the real statements cast `(q : ℤ)`. The scalar
   `Real.exp_two_mul_le_one_add_div_one_sub` sits in the Chebyshev growth file ("or beside it",
   §5), in namespace `Real`, since ForMathlib has no exponential-inequality file.
6. **Polynomial reduction of RBKI (§4.2).** `singularValues_sub_rbki_le_of_degree_lt` takes a
   polynomial over any `R` with `[Algebra R 𝕜]` (as `exists_aeval_mul_eq_blockKrylovMatrix_mul`),
   not only `ℝ[X]`.
7. **Competitor projector (§5).** Stated as `HasOrthonormalCols.specNorm_sub_rsvd_mul_pinv_sq_le` with
   the file's `A` for the note's `B`; the private `mul_pinv_self_of_rank_eq` is now public as
   `HasOrthonormalCols.mul_pinv_self_of_rank_eq` (one call site updated).
8. **Truncation monotone in rank (§5).** The helper "`range_truncatedSVD_mono`" is
   `range_mulVecLin_truncatedSVD_mono` (a `Monotone` statement) in `Matrix/Spectral/LowRank.lean`,
   the home of `truncatedSVD` and of `range_mulVecLin_truncatedSVD_le` (placement by topic).
9. **B5a glue.** The public frame glue is one Matrix-layer lemma,
   `exists_hasOrthonormalCols_conjTranspose_mul_self_mul_eq_mul_diagonal` in
   `Matrix/Spectral/LowRank.lean` (topic: frames of the truncated SVD, beside
   `exists_hasOrthonormalCols_mul_mul_conjTranspose_eq_truncatedSVD_completion`): nested invariant
   frames $\mathbf{Z}$, $\mathbf{V}$ of $\mathbf{A}^{\mathsf{H}}\mathbf{A}$ whose prefixes give every
   $\llbracket\mathbf{A}\rrbracket_r$, $r \le k$. The almost-sure-rank glue already exists
   (`ae_rank_conjTranspose_mul_eq_of_hasLaw_gaussianMatrix`). B5a adds head capture in
   expectation, `integral_frobNorm_one_sub_rangeProjector_mul_truncatedSVD_sq_le_of_hasLaw_gaussianMatrix`,
   which the truncated lines of B5b and the case split of B6a need. No separate `integrable_`
   companions for the filtered range finder: the law-free `integrable_*_sub_rsvd*` lemmas apply at
   the test matrix $f(\mathbf{A}^{\mathsf{H}}\mathbf{A})\mathbf{X}$.
10. **RBKI integrability (B5b).** The five `integrable_*_rbki*` lemmas are in
    `LowRank/Random/RangeFinder.lean`, with the other law-free integrability companions (the
    precedent stated in the module docstring of `LowRank/Gaussian/RangeFinder.lean`), over
    `RCLike 𝕜` for any a.e.-measurable test matrix, not in `LowRank/Gaussian/BlockKrylov.lean`.
11. **Truncated RSI (B5b).** Added the RSI twins of the truncated lines (§7.1 table, BD8 (a)):
    `integral_{spec,frob}Norm_sub_truncatedSVD_rsvd_pow_mul_sq_le_singularGapRatio_…`.
12. **RSI in the $(1 + \varepsilon)$ form (B6a).** Added
    `integral_specNorm_sub_{truncatedSVD_,}rsvd_pow_mul_sq_le_one_add_sq_mul_…` with
    $e^{-8p\varepsilon/(2+\varepsilon)}$ (§7.1 table, BD8 (a)).
13. **`rangeFinderTailRatio` (§6.4).** Over `RCLike 𝕜`; registered in `docs/constants.toml`
    (it is a named quantity used by name in statements, so docstrings show its value).
14. **Nyström (B7).** The Tropp–Webber form uses `rangeFinderTailRatio (CFC.sqrt H) r ℓ` with the
    bridge `Matrix.PosSemidef.rangeFinderTailRatio_sqrt` to the Nyström-native ratio
    $1 + \frac{r}{\ell - r - 1}\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_r\|_*/\sigma_r(\mathbf{H})$
    (no new named quantity). The truncations are the trace-norm gapped lines for NysBKI and NysSI
    (exact through `Matrix.PosSemidef.nuclearNorm_sub_truncatedSVD_nystrom`); spectral truncated
    Nyström and the gapless truncated Nyström lines are not stated (§7.1: optional; the spectral
    error of a truncated Nyström output depends on the tie-break).
15. **Not stated:** a Tropp–Webber-form (exact constant) gapless bound for the *truncated* RBKI
    output; the truncated gapless bound of this round is the $(1 + \varepsilon)$ form (§6.3).
    Revisit with MM Theorem 11 after B6b.
16. **Pointwise head capture (B4).** Added
    `HasOrthonormalCols.singularValues_one_sub_rangeProjector_mul_mul_le` in
    `LowRank/Structural/Filter.lean`, the singular-value form of head capture
    ($\sigma_i((\mathbf{I}-\mathbf{P})\mathbf{A}\mathbf{W}\mathbf{W}^{\mathsf{H}}) \le c^{-1}\sigma_i(\mathbf{M})$),
    as the skeleton review suggested: the Gram form squares it, which the gauge form alone does not
    allow (weak majorization does not survive squaring in the library). The gauge head capture is
    its corollary.
17. **Square-root bridge (B7).** `Matrix.PosSemidef.rangeFinderTailRatio_sqrt` is restated on the
    file's `H : Matrix n n ℝ` instead of a fresh `{k} [Fintype k] {G}` (skeleton review 3.1). The
    review's instance concern does not arise: `CFC.sqrt` on matrices takes the `DecidableEq`
    instance only inside a `Prop`-valued argument (the functional-calculus instance), so the
    classical and section spellings of `CFC.sqrt H` are defeq by proof irrelevance and the
    `Classical` lemmas (`Matrix.PosSemidef.sub_nystrom_eq`,
    `Matrix.PosSemidef.nuclearNorm_sub_truncatedSVD_nystrom`) rewrite section-instance goals
    directly, no `convert`. Lean's `unusedDecidableInType` linter flags a section `[DecidableEq n]`
    on such a statement, so the bridge is stated `open scoped Classical in` before the file's
    `variable [DecidableEq n]` (the variable line is split; the B7 theorems keep the instance).
    The B7 helpers are in `Matrix/Functions/AbsoluteValue.lean` (topic: the square root as a
    factor): `Matrix.PosSemidef.conjTranspose_sqrt_mul_sqrt`, `sq_singularValues_sqrt`,
    `frobNorm_sqrt_sub_truncatedSVD_sq` and the scalar gap bridge
    `singularGapRatio_le_two_mul_singularGapRatio_sqrt` ($\gamma_{\mathbf{H}} \le
    2\gamma_{\mathbf{H}^{1/2}}$).

Result ids used: `rbki-gapped-error`, `rsi-gapped-error`, `rbki-gapless-error`,
`rsi-gapless-error`, `nysbki-gapped-error`, `nyssi-gapped-error`, `filtered-range-finder-bound`,
and the new `nysbki-gapless-error`, `nyssi-gapless-error`; `gram-correspondence` reused.

### What was proved (2026-10-18)

All stages B0 to B7 are proved on branch `krylov/block`; `import NLAlib` has no `sorry`. Per stage,
the files and the headline names (all in namespace `NLAlib` unless written otherwise):

- **B0** (block Krylov spaces). `Krylov/Basic/BlockSpace.lean`: `blockKrylovMatrix`,
  `blockKrylovSpace`, the one-column bridges `blockKrylovMatrix_replicateCol`,
  `blockKrylovSpace_replicateCol`, `blockKrylovSpace_eq_iSup_krylovSpace`, prefix and successor
  (`blockKrylovMatrix_submatrix_castLE`, `blockKrylovSpace_mono`, `blockKrylovSpace_succ`,
  `mulVec_mem_blockKrylovSpace_succ`), shift (`blockKrylovSpace_add_smul_one`), change of variables
  (`blockKrylovMatrix_mul_mul`, `blockKrylovSpace_mul_mul`), `rank_blockKrylovMatrix_le`,
  `mem_blockKrylovSpace_iff`, the polynomial inclusion `exists_aeval_mul_eq_blockKrylovMatrix_mul`,
  `range_aeval_mul_le_blockKrylovSpace`. `Krylov/LinearSystems/CG.lean`: block CG with one column
  is CG, `galerkinInverse_blockKrylovMatrix_replicateCol(_mul)`. `Probability/Measurability/Krylov.lean`:
  `measurable_blockKrylovMatrix`. `Matrix/Functions/Polynomial.lean`: `Matrix.mul_pow_mul`.
- **B1a** (TW Lemma 5.1, the relative gap). `Matrix/Spectral/SingularValueInequalities.lean`:
  `singularValues_one_sub_rangeProjector_mul_le_of_range_le`, `singularGapRatio` with
  `singularGapRatio_nonneg`, `singularGapRatio_le_one`,
  `one_sub_singularGapRatio_div_one_add_singularGapRatio`. `Matrix/Norms/UnitarilyInvariant.lean`:
  `SymmetricGauge.matrixNorm_one_sub_rangeProjector_mul_le_of_range_le`.
  `Matrix/Functions/HermitianCalculus.lean`: `Matrix.IsHermitian.cfc_mul_eq_mul_diagonal_of_mul_eq`.
- **B1b** (supporting lines, TW Lemma 9.4, HMT Proposition 8.6). `ForMathlib/Analysis/Convex/SupportingLine.lean`:
  `HasSupportingLineOn`, `ConvexOn.hasSupportingLineOn`. `ForMathlib/Analysis/Convex/Integral.lean`:
  `HasSupportingLineOn.le_integral_comp`. `Matrix/Functions/TraceFunctions.lean`:
  `apply_re_quadForm_le_re_quadForm_cfc_of_hasSupportingLineOn`,
  `apply_specNorm_mul_sq_le_specNorm_mul_sq_of_hasSupportingLineOn`. `Matrix/Norms/Projector.lean`:
  `IsStarProjection.specNorm_mul_pow_le`.
- **B2a, B2b** (TW Lemma 9.3). `ForMathlib/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Growth.lean`
  (namespace `Polynomial.Chebyshev`): `eval_T_two_mul`, `monotoneOn_eval_T_real`,
  `exp_mul_sqrt_div_two_le_eval_T_real` (parts 1 to 3), `le_exp_of_eval_T_real_le` (part 4),
  `eval_iterate_derivative_T_real_nonneg`, `monotoneOn_eval_iterate_derivative_T_real`,
  `hasSupportingLineOn_mul_eval_T_sq` (part 5). `ForMathlib/Analysis/SpecialFunctions/Log/Deriv.lean`:
  `Real.exp_two_mul_le_one_add_div_one_sub` (TW (C.1)).
- **B3** (RBKI and NysBKI). `LowRank/Structural/BlockKrylov.lean`: `rbki`, `nystromBKI`, `rbki_def`,
  `rbki_eq_rangeProjector`, `rbki_one`, `rbki_zero`, `singularValues_sub_rbki_le_of_degree_lt`,
  `singularValues_sub_rbki_le_sub_rsvd_pow`, `singularValues_sub_rbki_le_of_le`,
  `nystromBKI_conjTranspose_mul_self`, `conjTranspose_mul_self_sub_nystromBKI`,
  `Matrix.PosSemidef.sub_nystromBKI_eq`.
- **B4** (TW Lemma 9.5, deterministic). `LowRank/Structural/Filter.lean`:
  `HasOrthonormalCols.singularValues_one_sub_rangeProjector_mul_mul_le`,
  `HasOrthonormalCols.matrixNorm_one_sub_rangeProjector_mul_mul_le`,
  `SymmetricGauge.matrixNorm_conjTranspose_mul_self_sub_rsvd_cfc_le`,
  `HasOrthonormalCols.specNorm_sub_rsvd_cfc_sq_le`, `HasOrthonormalCols.frobNorm_sub_rsvd_cfc_sq_le`.
  `LowRank/Structural/RangeFinder.lean`: `HasOrthonormalCols.mul_pinv_self_of_rank_eq`,
  `HasOrthonormalCols.specNorm_sub_rsvd_mul_pinv_sq_le`. `LowRank/Structural/Truncation.lean`:
  `truncatedSVD_rsvd_eq_rangeProjector_mul`, `singularValues_sub_truncatedSVD_rsvd_le_of_le`.
  `Matrix/Spectral/LowRank.lean`: `range_mulVecLin_truncatedSVD_mono`.
- **B5a** (TW Lemma 9.5 in expectation). `LowRank/Gaussian/Filter.lean`:
  `integral_matrixNorm_conjTranspose_mul_self_sub_rsvd_aeval_le_of_hasLaw_gaussianMatrix`,
  `integral_specNorm_sub_rsvd_aeval_sq_le_of_hasLaw_gaussianMatrix`,
  `integral_frobNorm_sub_rsvd_aeval_sq_le_of_hasLaw_gaussianMatrix`,
  `integral_frobNorm_one_sub_rangeProjector_mul_truncatedSVD_sq_le_of_hasLaw_gaussianMatrix`.
  `Matrix/Spectral/LowRank.lean`: `exists_hasOrthonormalCols_conjTranspose_mul_self_mul_eq_mul_diagonal`.
- **B5b** (TW Theorem 9.2). `LowRank/Gaussian/BlockKrylov.lean`:
  `integral_{spec,frob}Norm_sub_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix`,
  `integral_{spec,frob}Norm_sub_rsvd_pow_mul_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix`, their
  Gram forms in `SymmetricGauge`, and the truncated lines
  `integral_{spec,frob}Norm_sub_truncatedSVD_rbki_sq_le_singularGapRatio_…` and
  `integral_{spec,frob}Norm_sub_truncatedSVD_rsvd_pow_mul_sq_le_singularGapRatio_…`.
  `LowRank/Random/RangeFinder.lean`: the five `integrable_*_rbki*` companions.
- **B6a** (gapless, Musco–Musco $(1 + \varepsilon)$ form). `LowRank/Gaussian/BlockKrylovGapless.lean`:
  `integral_specNorm_sub_{truncatedSVD_,}rbki_sq_le_one_add_sq_mul_of_hasLaw_gaussianMatrix`,
  `integral_specNorm_sub_{truncatedSVD_,}rsvd_pow_mul_sq_le_one_add_sq_mul_of_hasLaw_gaussianMatrix`,
  and the asymptotic form
  `exists_forall_integral_specNorm_sub_truncatedSVD_rbki_sq_le_of_hasLaw_gaussianMatrix`
  (depth $O(\log(\lvert n \rvert/\varepsilon)/\sqrt{\varepsilon})$).
- **B6b** (TW Theorem 9.1). Same file: `integral_specNorm_sub_rbki_sq_le_mul_exp_of_hasLaw_gaussianMatrix`,
  `integral_specNorm_sub_rsvd_pow_mul_sq_le_mul_rpow_of_hasLaw_gaussianMatrix`.
  `LowRank/Gaussian/RangeFinder.lean`: `rangeFinderTailRatio`, `one_le_rangeFinderTailRatio`,
  `sq_singularValues_mul_rangeFinderTailRatio` (registered in `docs/constants.toml`).
- **B7** (Nyström by the Gram correspondence). `LowRank/Gaussian/NystromBlockKrylov.lean`
  (namespace `Matrix.PosSemidef`): `rangeFinderTailRatio_sqrt`, the gapped
  `integral_specNorm_sub_{nystromBKI,nystrom_pow_mul}_le_singularGapRatio_…`, the gapless
  `…_le_one_add_sq_mul_…` and `…_le_mul_exp_…`, `…_le_mul_rpow_…`, and the trace-norm truncated
  lines `integral_nuclearNorm_sub_truncatedSVD_{nystromBKI,nystrom_pow_mul}_le_singularGapRatio_…`.
  `Matrix/Functions/AbsoluteValue.lean`: `Matrix.PosSemidef.conjTranspose_sqrt_mul_sqrt`,
  `sq_singularValues_sqrt`, `frobNorm_sqrt_sub_truncatedSVD_sq`,
  `singularGapRatio_le_two_mul_singularGapRatio_sqrt`.

Result ids: as listed at the end of Skeleton changes. §5.3 rows for `singularGapRatio` and
`HasSupportingLineOn` added to CONTRIBUTING (BD9); `rangeFinderTailRatio` has none (BD9). Ledger:
eleven prototype entries (stages B0, B1b, B3).

### Wrap-up amendments (2026-10-18)

Placement pass over every new public declaration of the round (CONTRIBUTING §8 item 5):

1. The private top-eigenvector helper of `TraceFunctions.lean` is public as
   `IsStarProjection.exists_mulVec_eq_self_and_re_quadForm_eq_specNorm_mul_sq` in
   `Matrix/Spectral/CourantFischer.lean`, beside
   `Matrix.PosSemidef.exists_norm_eq_one_and_mulVec_eq_specNorm_smul` (spectral-norm attainment);
   it imports `Matrix/Basic/Projector.lean`, no cycle.
2. The private "$\sigma_t = 0$ gives $\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t = \mathbf{0}$" helper of
   `LowRank/Gaussian/BlockKrylov.lean` is replaced by the public
   `truncatedSVD_of_singularValues_eq_zero` in `Matrix/Spectral/LowRank.lean`, beside
   `truncatedSVD_of_rank_le` (no existing public lemma said it).
3. §8's flag closed: `Polynomial/Chebyshev/Filter.lean` held one fact with no NLAlib vocabulary;
   `hasSupportingLineOn_mul_eval_T_sq` moved into ForMathlib's Chebyshev growth file (now in
   namespace `Polynomial.Chebyshev`, beside the derivative monotonicity it uses) and the file is
   deleted.
4. Skeleton change 5's placement: `Real.exp_two_mul_le_one_add_div_one_sub` moved from the
   Chebyshev growth file to `ForMathlib/Analysis/SpecialFunctions/Log/Deriv.lean`, the file of the
   Mathlib series (`Real.hasSum_log_sub_log_of_abs_lt_one`) it is the first term of.
5. `scripts/Duplicates.lean` found three private copies of $0 \le t/(\ell - t - 1)$ for
   $t + 2 \le \ell$ (in `BlockKrylov.lean`, `BlockKrylovGapless.lean`, `NystromBlockKrylov.lean`);
   they are replaced by the public `natCast_div_sub_sub_one_nonneg` in
   `LowRank/Gaussian/RangeFinder.lean`, beside `rangeFinderTailRatio`, whose weight it is.

Checked and left in place, each recorded above: the gauge Lemma 5.1 in `UnitarilyInvariant.lean`
(change 3, import cycle), the integrability companions in `LowRank/Random/RangeFinder.lean` (change
10), the B7 square-root helpers in `AbsoluteValue.lean` (change 17), and
`Matrix.PosSemidef.rangeFinderTailRatio_sqrt` in the Nyström file (change 14; its only content is
the Nyström-native ratio). No flag is open.

### Asymptotic forms for the Rates page (2026-10-18)

Maintainer: "add to the explorer rates page too" (low-rank approximation only; no rates for the
linear-system solvers). Every Rates row resolves to a proved `exists_forall_` corollary paired
with its explicit theorem (CONTRIBUTING §5.2 rule 3), so seventeen corollaries were added, each
in the file of its explicit theorem, whose docstring now names it ("Asymptotic form: …"). All
conclude relative error $1 + \varepsilon$ against the best rank-$r$ error in the theorem's own norm
and power, with $\lvert n \rvert$ the number of columns:

| Explicit family | Corollaries | Sufficient resource | Constants in the proof |
|---|---|---|---|
| gapped RBKI, spectral/Frobenius, untruncated/truncated (`BlockKrylov.lean`) | 4 | $q \ge C\log(\lvert n \rvert/\varepsilon)/\sqrt{\gamma}$ | $C = 3$, $\varepsilon_0 = 1/2$ |
| gapped RSI, same four (`BlockKrylov.lean`) | 4 | $p \ge C\log(\lvert n \rvert/\varepsilon)/\gamma$ | $C = 1$, $\varepsilon_0 = 1/2$ |
| gapped NysBKI spectral and truncated trace (`NystromBlockKrylov.lean`) | 2 | as RBKI | $C = 3$, $\varepsilon_0 = 1/2$ |
| gapped NysSI spectral and truncated trace (same file) | 2 | as RSI | $C = 1$, $\varepsilon_0 = 1/2$ |
| TW gapless RBKI, NysBKI (`BlockKrylovGapless.lean`, Nyström file) | 2 | $q \ge C\log(\lvert n \rvert + 1)/\sqrt{\varepsilon}$ | $C = 4$, $\varepsilon_0 = 1$ |
| TW gapless RSI, NysSI (same files) | 2 | $p \ge C\log(\lvert n \rvert + 1)/\varepsilon$ | $C = 2$, $\varepsilon_0 = 1$ |
| MM gapless truncated RSI (`BlockKrylovGapless.lean`) | 1 | $p \ge C\log(\lvert n \rvert/\varepsilon)/\varepsilon$ | $C = 11$, $\varepsilon_0 = 1/2$ |

The gapped forms carry `0 < singularGapRatio A h t` (at $\gamma = 0$ Lean's $x/0 = 0$ would make
the threshold vacuous) and are named `exists_forall_…_le_of_singularGapRatio_pos_of_hasLaw_gaussianMatrix`,
since their conclusions coincide with the gapless ones. The tail is bounded by dimensions only:
$\frac{t}{\ell-t-1}\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2 \le
\lvert n \rvert^2\sigma_r^2$ and $\le \lvert n \rvert\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2$.
The Tropp–Webber gapless forms bound the tail ratio by $1 + \lvert n \rvert^2$ and so need no
$\log(1/\varepsilon)$; their explicit theorems assume $\sigma_r > 0$, but the corollaries do not:
at $\sigma_r = 0$ the $(1 + \varepsilon)$ form of the same algorithm gives error $0$. The
untruncated Musco–Musco forms got no corollary, being dominated in rate by these; the existing
truncated RBKI corollary ($C = 6$, $\varepsilon_0 = 1/2$) is unchanged.

New supporting declarations, each beside the quantity it bounds: in
`LowRank/Gaussian/RangeFinder.lean` (with `natCast_div_sub_sub_one_nonneg` and
`rangeFinderTailRatio`) the two tail-weight bounds
`natCast_div_sub_sub_one_mul_frobNorm_sub_truncatedSVD_sq_le_card_sq_mul_singularValues_sq`,
`…_le_card_mul_frobNorm_sub_truncatedSVD_sq` and `rangeFinderTailRatio_le_one_add_card_sq`; in
`LowRank/Gaussian/BlockKrylov.lean`, the first file of the round's import chain, the threshold
arithmetic shared by the three files: `one_half_le_log_div`, `le_add_mul_of_le_add_mul_exp`,
`one_le_and_log_div_le_sub_one_mul`; in `BlockKrylovGapless.lean`, the gapless thresholds
`two_le_and_exp_log_four_mul_sq_div_le_one_add`, `rpow_one_div_two_mul_add_one_le_one_add` (and a
private $\varepsilon/2 \le \log(1 + \varepsilon)$). The scalar threshold lemmas are specific to
these thresholds, so they stay with their users rather than in ForMathlib (flag: revisit if a
later round needs them elsewhere).

### Deviations

None from Mathlib (§8: every object is an addition; no `Mathlib-deviations.md` entry). From the
note's signatures: Skeleton changes 1 to 17 above, none of which changes a decision; the largest are
the gauge Lemma 5.1's file (3), the a.e. Jensen hypothesis (4), the Nyström Tropp–Webber form
through `rangeFinderTailRatio (CFC.sqrt H)` with no spectral truncated Nyström line (14), and no
exact-constant gapless bound for the truncated RBKI output (15).

### Later targets

- A Tropp–Webber-constant gapless bound for the truncated RBKI output (Skeleton change 15): the
  skeleton review found that it needs the machinery of MM Theorem 11.
- MM Theorem 11: the Frobenius gapless bound for truncated RBKI.
- MM's per-vector guarantees (Theorems 1 and 12) and the gap-dependent Theorem 13.
- Schatten-$p$ bounds for the truncated outputs (BD8 (b)).
- Odd multiplication counts and early truncation on an orthonormal Krylov basis (BD6 (b)).
- Parallel sums and TW Lemma 8.3, with TW Theorem 8.7 at $k \in \{r, r + 1\}$ (BD5 (a)).
- Block Lanczos and Arnoldi with a realisation theorem and block grade, then block CG and GMRES
  theory (BD2 (b), (c)).
- **Next planned target**: the upper bound of Bakshi, Clarkson and Woodruff, "Low-rank approximation
  with $1/\varepsilon^{1/3}$ matrix-vector products" (STOC 2022, arXiv:2202.05120), Theorem 5.1,
  upper bound only; the lower bounds are a separate later project, from a newer paper (maintainer,
  2026-10-18). It needs: MM's per-vector and gap-dependent guarantees (Theorems 12 and 13 above);
  BCW's Schatten-$p$ projection lemma (their Lemma 5.5) and per-vector-to-Schatten lemma (their
  Lemma 5.7); pinching; and statements about several Krylov subspaces at once.
