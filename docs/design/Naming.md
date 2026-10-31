# Naming: one grammar for the library

Design note, 2026-10-19. A library-wide audit of the names of the 4,105 public declarations
(extraction at a4f8773, the same Lean as `main` at bc72b8d) found the names faithful to their
statements but split between a few competing conventions, mostly in probabilistic statements,
and found CONTRIBUTING's own tail-prefix rule broken 15 times. The maintainer approved its
grammar the same day, with more renames than the audit recommended: "Yes, these are fine. I am
fine with doing more work now if it will make the package more usable. Also, I am fine with
some 'per section' rules if that will help. The CI seems important. It is a big problem that the
contributing rules are broken, because it suggests that the LLMs are not able to keep the rules
in context well."

The grammar itself is CONTRIBUTING §4 (rules N1–N18); this note keeps the evidence, the
decisions and what was renamed. The renames landed in one branch before `v0.1`, with the rename
map `docs/renames/2026-10-naming.json` and no `@[deprecated]` aliases (CONTRIBUTING §4 N12 asks
for aliases only after the `v0.1` tag; no such tag exists). `scripts/check_names.py` enforces
the checkable rules in CI.

## 1. Decisions (maintainer, 2026-10-19)

| # | audit | decision | rule | done |
|---|---|---|---|---|
| 1 | D1 tail prefix | The statement decides: `μ.real {…}` is `measureReal_`, `μ {…}` is `measure_`, in every namespace. Reverses the 2026-10-14 rule (namespaced `measure_`). The audit allowed keeping Mathlib's `measure_` for the 5 names NLAlib adds to `ProbabilityTheory.HasSubgaussianMGF`; **not kept** (see below). | N14 | 64 renames |
| 2 | D2, D3 tail event | A scalar event is written `{ω \| b < err ω}` and named subject first (`err_gt`); `¬` stays only for Loewner, conjunction and predicate events. The §5.3 "tail" row is amended. | N15 | 28 statements, 37 names |
| 3 | D4 subtraction | Errors are `exact − computed` everywhere, trace estimation included (the audit had recommended keeping `estimate − trace` there as an exception). | N10 | 9 statements and names |
| 4 | D5 `sq` | `sq_singularValues` becomes `singularValues_sq`, with all its dependents. | N6 | 17 renames |
| 5 | D6, D7 hypotheses | Current practice written down: laws `_of_hasLaw_<law>`, distribution classes `_of_<class>`, sketch-property interfaces as the namespace, API in its predicate's namespace, dot notation for side conditions allowed. | N9 | no rename |
| 6 | S5, S6, D9 | Applied where they make names more predictable (below); synonyms fixed: `intrinsicDim` → `intrinsicDimension`, `gram` and `fromBlocks_diagonal` resolved against Mathlib's meanings. | N5, N16 | 65 renames |
| 7 | CI | `scripts/check_names.py` with tests (`scripts/test_check_names.py`) and an allowlist (`scripts/names_allow.toml`), in `.github/workflows/ci.yml` and `scripts/stage_check.sh`; error mode once the renames landed. | §4.5, §4.6 | |
| 8 | timing | One branch, before `v0.1`, with a rename map for the explorer's `#d/` redirects. | N12 | |

"Per section" rules (maintainer: allowed) are subsections of CONTRIBUTING §4.4 rather than a
separate file: an author is told to read CONTRIBUTING in full (AGENTS.md, §11) and is most likely
to see a rule there, next to the general ones it refines. Each topic rule has its own id, and
the checker knows the ones it can check (tails, statistics, sample sizes, algorithm tokens,
asymptotic forms).

**No exception was kept.** Every place where the audit offered "keep as a documented exception"
was renamed instead, because each exception is one more rule a human or an LLM author has to
remember:

- *`HasSubgaussianMGF.` tails* (decision 1). Keeping `measure_` for the 5 names would have split
  them from their siblings in NLAlib's own `HasSubexponentialMGF.` namespace, which decision 1
  renames (`HasSubexponentialMGF.measureReal_le_le` next to `HasSubgaussianMGF.measure_le_le`).
  Mathlib's namespace is already mixed (`measure_ge_le` next to `measureReal_le_le_exp`), so
  following the statement there costs nothing in consistency. Mathlib's own names are untouched.
- *Trace estimation* (decision 3). `tr A − estimate` reads as well as `estimate − tr A`: inside
  `|·|` and `‖·‖` the order is invisible, and the one bare identity reads
  `tr A − hutchpp = tr Δ − girardHutchinson Δ` (`trace_sub_hutchpp`). No statement got worse.
- *`sq_singularValues`* (decision 4): renamed, 17 names with `sum_sq_eigenvalue_sub_le_frobNorm_sub_sq`,
  which the checker found and the audit's list missed.

**S5, column space** (`range_mulVecLin_…`, 13 names): applied. The column space is
`LinearMap.range A.mulVecLin` (§5.3), so either spelling is unambiguous, and Mathlib's own names
keep `mulVecLin` (`Matrix.range_mulVecLin`, `Matrix.ker_mulVecLin_conjTranspose_mul_self`). What
decides it is NLAlib's majority: 19 other `range_` names and every hypothesis token
(`_of_range_le`, `_of_range_eq`, used by dozens of names) already omit `mulVecLin`, and a rule
keeping it would have renamed all of those into `_of_range_mulVecLin_le`. One spelling,
`range`/`ker`, is the predictable one. The 4 ForMathlib names in Mathlib's `Matrix` namespace
follow it too; an upstreaming PR renames them anyway.

**S6, sample sizes** (9 definitions, 32 names): applied. A sample size is
`<sketch><property>Dim`, the majority form (5 of 9) and the literature's "embedding dimension".
`countSketchRows` → `countSketchEmbeddingDim`, `samplingSize` → `samplingEmbeddingDim`,
`samplingInjectionSize` → `samplingInjectionDim`, `projectionCostTailRows` →
`projectionCostTailDim`; their theorems follow (`_of_samplingEmbeddingDim_le`), and so do the
`docs/constants.toml` entries. A user who knows `gaussianInjectionDim` now guesses
`samplingInjectionDim`; before, it was `samplingInjectionSize`.

**Synonyms** (D9).

- `intrinsicDim` → `intrinsicDimension`, the definition's name (8).
- `gram` for `G * Gᴴ` → `mul_conjTranspose_self` (5). Mathlib's `Matrix.gram` is the matrix of
  inner products of a family, another object; NLAlib already writes `A * Aᴴ` as
  `mul_conjTranspose_self` (16 names) and `Aᴴ * A` as `conjTranspose_mul_self`.
- `fromBlocks_diagonal` for `fromBlocks A 0 0 B` → `fromBlocks_zero₁₂_zero₂₁` (7), composed from
  Mathlib's `fromBlocks_zero₁₂`/`fromBlocks_zero₂₁` (`det_fromBlocks_zero₂₁`,
  `charpoly_fromBlocks_zero₁₂`) and matching NLAlib's `rank_fromBlocks_zero₁₂_zero₂₁`. Mathlib's
  `fromBlocks_diagonal` is `fromBlocks (diagonal d₁) 0 0 (diagonal d₂) = diagonal …`, which NLAlib
  uses in proofs; Mathlib's `fromBlocks_diagonal_pow` uses the other meaning, so Mathlib is itself
  split, and the composed name is the one that cannot be misread.

**Isolated mismatches** (M1, 6 found by the checker).

- `charpoly_add_vecMulVec_mul` → `X_sub_C_mul_charpoly_add_vecMulVec`;
- `conjTranspose_arnoldiMatrix_mul_mul_arnoldiMatrix_submatrix_castSucc` →
  `submatrix_conjTranspose_arnoldiMatrix_mul_mul_arnoldiMatrix_castSucc` (Mathlib's `submatrix_mul`);
- `posDef_of_exp_mul` → `posDef_exp_mul_of_injective` (its `of` was `Matrix.of`, read as a
  hypothesis separator);
- `variance_quadForm_of_hasLaw_rademacherVector_le` → `variance_quadForm_le_of_hasLaw_rademacherVector`;
- `uniformSphereVector_map_conjTranspose_mulVec_eq`: **kept**. Its left side is
  `(uniformSphereVector n).map (Vᴴ *ᵥ ·)`, and Mathlib names a pushforward from the measure
  (`gaussianReal_map_add_const`); the checker now reads `Measure.map f ν` that way (N2).
- `exists_bernstein_exponent`: kept, on the allowlist. It is the choice of the exponent θ in
  Bernstein's argument, `∃ θ ∈ (0, 3/L), −θt + θ²v/(2(1 − Lθ/3)) ≤ −(t²/2)/(v + Lt/3)`, and the
  inequality has no token form shorter than the statement.

## 1a. Dot notation (maintainer, 2026-10-19, added the same day)

The rules audit of 2026-10-19 (scratchpad `rules-audit/`, check SHAPE-DOT) found 138 root-namespace
theorems whose first explicit argument is a hypothesis `hA : A.IsHermitian`, `A.PosSemidef`,
`A.PosDef`, `IsSVD …` or `HasOrthonormalCols U`, against CONTRIBUTING §5.2 ("lives in
`Matrix.IsHermitian`"). The maintainer: enforce §5.2, not relax it ("go for it"). This reverses
the audit's D7 ("allowed, not required"); the grammar's rule is N18, checked.

Re-derived on this branch with the checker's N18 (which reads the first explicit binder, nested
parentheses included): **120** theorems, renamed into the predicate's namespace (110 Matrix, 5
Sketching, 3 Probability, 1 Krylov, 1 RandomMatrix; 3 of them already renamed by the grammar
rules, composed in the map).

- 108 are on the audit's list.
- 12 the audit missed: its regex skipped a first binder with parentheses, so it did not see
  `h : (fromBlocks A B Bᴴ C).PosSemidef` (the Schur-complement lemmas),
  `h : (hermitianPart A).PosDef`, `h : IsSVD A U (fun i ↦ …) V`.
- 30 of the audit's flags are false positives for the same reason in the other direction: the
  first explicit argument is a `HasLaw` hypothesis (`hasLaw_conjTranspose_mul_of_hasLaw_gaussianMatrix
  (hX : HasLaw X …) (hV : HasOrthonormalCols V)`), and its regex took the second. The checker does
  not flag them, so they are neither renamed nor allowlisted; by N9 a law first is a suffix.

The name drops an `_of_<predicate>` it no longer needs (`re_det_fromBlocks_le_of_posSemidef` →
`Matrix.PosSemidef.re_det_fromBlocks_le`, `eq_sqrt_of_hasOrthonormalCols_mul_eq` →
`HasOrthonormalCols.eq_sqrt_of_mul_eq`). One move collided:
`cfc_mul_mul_conjTranspose` (square `U`, `hr : card r = card n`) would have taken the name of the
existing `HasOrthonormalCols.cfc_mul_mul_conjTranspose` (any frame, with the `f 0` correction); it
is `HasOrthonormalCols.cfc_mul_mul_conjTranspose_of_card_eq`, as
`HasOrthonormalCols.mul_conjTranspose_self_of_card_eq`. N18 applies to root names only: a theorem
in an interface namespace (N9) or in another predicate's namespace keeps it.

## 2. What changed

311 public declarations renamed (194 by the grammar rules below, 117 more by N18, §1a) and 37
statements changed (the 28 scalar tails stated positively,
the 9 trace-estimation errors flipped), in `NLAlib/`, the docstrings that cite them, the live
documents (CONTRIBUTING, `docs/constants.toml`) and `docs/design/Mathlib-deviations.md`. Design
notes stay historical and keep the old names; `docs/renames/2026-10-naming.json` maps them.
Private helpers were not renamed; the checker does not see them.

| rule | Matrix | Krylov | Probability | RandomMatrix | Sketching | LowRank | Regression | Estimation | ForMathlib | total |
|---|---|---|---|---|---|---|---|---|---|---|
| N14 tail prefix (P1, P1x) | | | 17 | | 7 | 29 | 10 | | 1 | 64 |
| N15 scalar event positive (E1) | | | | 7 | 2 | 19 | | | | 28 |
| N15 subject first (E2) | | | 1 | 2 | | | | 1 | | 4 |
| N15 missing relation (E3) | | | 2 | 1 | | | | | | 3 |
| N10 trace estimation (O1, with 2 of E2) | | | | | | | | 9 | | 9 |
| N5 `intrinsicDimension` (S1) | | | 8 | | | | | | | 8 |
| N5 `mul_conjTranspose_self` (S2) | | | | 5 | | | | | | 5 |
| N5 `fromBlocks_zero₁₂_zero₂₁` (S3) | 7 | | | | | | | | | 7 |
| N6 `singularValues_sq` (S4) | 15 | | | | 1 | 1 | | | | 17 |
| N5 `range`, `ker` (S5) | 9 | | | | | | | | 4 | 13 |
| N16 sample sizes (S6) | | | | | 32 | | | | | 32 |
| N2, N3 isolated (M1) | 2 | 1 | 1 | | | | | | | 4 |
| **renamed by the grammar rules** | 33 | 1 | 29 | 15 | 42 | 49 | 10 | 10 | 5 | **194** |
| N18 dot notation (§1a; 3 also above) | 110 | 1 | 3 | 1 | 5 | | | | | 120 |
| **renamed** | 140 | 2 | 32 | 16 | 47 | 49 | 10 | 10 | 5 | **311** |
| statements changed | | | | 7 | 2 | 19 | | 9 | | 37 |

(Polynomial: none. The transfer lemma `measureReal_eq_measureReal_gaussianMatrix_of_isLeftUnitarilyInvariant`
now transfers `{ω | c < f (X ω)}`, so by N15 it is
`measureReal_gt_eq_measureReal_gaussianMatrix_of_isLeftUnitarilyInvariant`.)

The audit's recommended list (122) is in, plus every option (P1x, S4, S5, S6, O1) and the one
extra `sum_sq_eigenvalue_sub_le_frobNorm_sub_sq`. Names not on the list that the checker
accepted were not touched.

## 3. The check in CI

`scripts/check_names.py` runs on the extraction that `scripts/explore_data.sh` writes: in CI the
build job has just built `NLAlib`, so the extraction is one more `lake env lean` run on the
built `.olean`s, about a minute, with no rebuild; `scripts/stage_check.sh` runs the same
extraction on the proved modules only (`--partial`). The checks are those of the audit's
`naming_audit.py`, made strict and given rule ids; they parse Lean's pretty-printed statements
with `scripts/leanexpr.py`, the audit's bracket-depth splitter. It ran in warning mode for one
commit and is in error mode from the commit after the renames.

| rule | what it verifies | audit precision (a4f8773) |
|---|---|---|
| N1 | case by kind | 0 violations |
| N2 | the first token is a head of the left side | 4 flags, 3 real |
| N3 | the main relation is named before `_of_` | 4 flags, 2 real; mutation recall 91% |
| N4 | library-function tokens occur in the statement | 12 flags, 8 real |
| N5 | the synonyms of §4.3 | exact |
| N6 | `sq_f` (anywhere) and `pow_f` (left side) | exact on library heads |
| N7 | quality, source and author words | 0 real cases |
| N9 | a `HasLaw` hypothesis named `hasLaw_<law>` in statistic and tail names | 431 of 437, the rest benign |
| N10 | no `<alg>_sub_` | exact on names |
| N11, N16 | named-bound suffixes, `…Dim` for sample sizes | exact |
| N13 | statistic prefixes, `_sq` for mean squares | 283 of 284 |
| N14 | tail prefix against `μ`/`μ.real` | exact |
| N15 | tail event token, subject first, two relation tokens, no scalar `¬` | exact on set-builder tails |
| N17 | asymptotic names against the derivation from the explicit name | 61 of 61 |
| N18 | a root theorem with a first explicit `IsHermitian`/`PosSemidef`/`PosDef`/`IsSVD`/`HasOrthonormalCols` hypothesis is in that namespace | 120 found, all renamed |

What it cannot verify is listed in CONTRIBUTING §4.6. New notation (`Var[`, `cov[`, `μ[·|m]`)
must be mapped once in `leanexpr.py` before the checker can read statements that use it.

The audit's scripts (`naming_audit.py`, `rename_cost.py`, with `leanexpr.py`) were one-off
reports run from a scratchpad (2026-10-19) on the extraction and on the explorer repository's
TOML; they are not in the repository. `leanexpr.py` is, as `scripts/leanexpr.py`, and every
check of `naming_audit.py` that a CI gate can use is in `scripts/check_names.py`. The audit's
numbers below are from those scripts at a4f8773, before the renames.

## 4. Open

- `norm_toLp` (22 names) spells the vector 2-norm `‖WithLp.toLp 2 x‖` with `toLp` outside bridge
  lemmas, against D9's `norm`. Not decided on 2026-10-19 and not checked; about 10 non-bridge
  names (`norm_toLp_mulVec_le`) would change.
- `truncatedGNFactor` abbreviates `generalizedNystrom` in one named bound.
- The checker sees public declarations of `NLAlib` only: `NLAlibScaffold` statements are checked
  when they move into the library, private helpers never.
- The explorer redirect: `build.py` in the explorer repository reads
  `docs/renames/2026-10-naming.json` to emit `#d/<old>` → `#d/<new>` redirects (explorer session's
  job). Its `results.toml` cites one renamed E1 theorem
  (`measureReal_not_frobNorm_sub_rsvd_sq_le_le_of_hasLaw_gaussianMatrix`, now
  `measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_gaussianMatrix`, statement now `{ω | b < err}`)
  and `rates.toml` cites `variance_quadForm_of_hasLaw_rademacherVector_le`; both need updating there.

- The rules-enforcement stage that follows this branch (`scripts/check_rules.py`, a
  `docs/rules/rules.toml` rule source generating an index, per-topic `NLAlib/<Topic>/RULES.md`
  files and an agent digest, fatal warnings) absorbs or calls `scripts/check_names.py`. For that,
  the rule ids N1–N18 are stable (a retired rule keeps its id unused), each violation is one line
  `N<k> <full name>: <message>`, and the last line is the `check_names:` summary; `check(decls,
  registered)` returns `(rule, name, message)` triples for a caller that imports it.

## 5. The audit

The audit report follows, adapted: its §3 grammar is now CONTRIBUTING §4, its decisions are §1
above, and its rename-cost estimate is superseded by §2.

### Summary (at a4f8773)

The names are **faithful to their statements**. A checker that rebuilds the expected name head and
relation from each conclusion flags 7 of 2,856 theorems, and 5 of those 7 are real. A mutation test
(swap `le`/`lt`, or replace the head function) catches 91% and 100% of the planted errors.
Vocabulary is also uniform: `frobNorm`, `specNorm`, `pinv`, `rsvd`, `eigenvalue` and
`singularValues` each have one spelling, with no `opNorm`, `pseudoinverse` or `rangeFinder`
theorem names.

The inconsistency the maintainer suspected is real, but it is a **small set of competing
conventions**, concentrated in probabilistic statements:

| | count | where |
|---|---|---|
| `measure_` names on `μ.real` statements (the rest use `measureReal_`) | 64 of 188 tails | LowRank 29, Probability 17, Regression 10, Sketching 7, ForMathlib 1 |
| CONTRIBUTING's own tail-prefix rule is broken | 15 | Nyström / `SymmetricGauge` / Hutch++ tails |
| scalar tail events written `¬ (err ≤ b)` instead of `b < err` | 28 of 148 scalar tails | LowRank 19, RandomMatrix 7, Sketching 2; 7 (norm, algorithm) families use both |
| tail named from the bound side (`c_le_X`), not the subject (`X_ge`) | 6 | Hutch++, Gaussian/sphere norms |
| tail name missing its event or tail relation | 3 | `measureReal_norm_sq_le_of_hasLaw_gaussianVector`, … |
| subtraction order `estimate − truth` (everywhere else it is `exact − computed`) | 10 | all of trace estimation |
| distribution hypothesis spelled as a namespace in one family and an `_of_` suffix in another | e.g. `HasSubspaceInjection.` 17/0 vs `_of_isSubgaussianVector` 29 (16 in its namespace) | Sketching/LowRank |
| synonyms for one concept | `intrinsicDim` 8 vs the definition `intrinsicDimension`; `gram` 5 for `G * Gᴴ`; `fromBlocks_diagonal` 7 for `fromBlocks A 0 0 B` (Mathlib uses it for diagonal blocks); sample-size suffixes `Dim`/`Rows`/`Size` | |
| `sq` placement split by head | `singularValues A k ^ 2` is always `sq_singularValues` (16 names); squared norms are `<norm>_…_sq` (101 of 102) | Matrix |

Other forms are already uniform and only need writing down: expectation (`integral_`, 283 of 284),
variance (`variance_`, 20 of 20), second moments (`_sq`, 109 of 109), laws (`_of_hasLaw_<law>`,
431 of 437, with 6 justified omissions), `exists_forall_` asymptotic forms (61 of 61 follow one
rule that CONTRIBUTING does not yet state exactly), Mathlib case conventions (0 violations), and
quality or source words in names (0 real cases).

### 5.1 Method and coverage

**Data.** `explore-data.json` at a4f8773 gives, for each public declaration, its name, kind,
module, pretty-printed signature, docstring and value/type dependencies.

| topic | theorem | def | abbrev | structure | class | instance | total |
|---|---|---|---|---|---|---|---|
| Matrix | 2110 | 98 | 0 | 12 | 0 | 0 | 2220 |
| Krylov | 236 | 39 | 0 | 6 | 0 | 0 | 281 |
| Polynomial | 86 | 13 | 0 | 1 | 0 | 0 | 100 |
| Probability | 372 | 9 | 2 | 6 | 0 | 3 | 392 |
| RandomMatrix | 181 | 8 | 1 | 0 | 2 | 8 | 200 |
| Sketching | 293 | 26 | 1 | 5 | 0 | 6 | 331 |
| LowRank | 300 | 7 | 0 | 0 | 0 | 0 | 307 |
| Regression | 48 | 0 | 0 | 0 | 0 | 0 | 48 |
| Estimation | 29 | 2 | 0 | 0 | 0 | 0 | 31 |
| ForMathlib | 184 | 4 | 0 | 0 | 0 | 7 | 195 |
| **all** | 3839 | 206 | 4 | 30 | 2 | 24 | 4105 |

**What was parsed.**

- Names are split into namespace and short name, and the short name into `_` tokens; the
  hypothesis part is everything after the first `of`.
- Signatures are split into binders and conclusion by `leanexpr.py`, a bracket-depth splitter, not a
  Lean parser. All 3,839 theorem conclusions parsed.
- Outer `∀`, `∀ᵐ`, `∃` and `→` layers are peeled (∃ 220, ∀ᵐ 28, ∀ 14, ∃! 3, → 2).
- 3,024 conclusions have a top-level relation, with ↔ binding loosest, then ∨, ∧, and finally
  = ≤ < ≠ ∈ ⊆. Big-operator binders (`∑ i ∈ s,`) are masked so their `∈` is not read as the relation.
- Set-builder tails `μ.real {ω | P}` are classified by the shape of `P`. The subject is the side
  that mentions ω.
- References for the rename cost were counted in the current `nlalib-block` checkout
  (`NLAlib/**/*.lean`, `docs/**/*.md`, `CONTRIBUTING.md`, `docs/constants.toml`) and in the explorer
  repository's TOML files. The checkout is on branch `regression/sketch-precondition` (bc72b8d),
  close to a4f8773.

**Precedent consulted.**

- The Mathlib naming page.
- Mathlib sources under `.lake/packages/mathlib`:
  - `HasLaw.measure_eq` (μ) next to `HasLaw.measureReal_eq` (μ.real);
  - `HasSubgaussianMGF.measure_ge_le` and `HasSubgaussianMGF.measureReal_le_le_exp`, both about
    `μ.real`, in the same namespace;
  - `measureReal_abs_gt_le_integral_charFun` for `μ.real {x | r < |x|}`;
  - `norm_sub_sq` / `norm_add_sq_real` for `‖x − y‖ ^ 2` (sq after the argument), but `sq_abs`,
    `sq_sqrt` for `|a| ^ 2`, `√a ^ 2`;
  - `fromBlocks_diagonal` (diagonal blocks), `ker_mulVecLin_conjTranspose_mul_self`.
- CONTRIBUTING §4 (names), §5.2 (shape, numerical bounds, asymptotic forms, dot notation), §5.3
  (vocabulary).
- explorer-redesign Appendix B and its parser `explore-audit/audit.py`.

**Checker validation (name versus statement).** Three checks run over the 2,856 theorems that have
a relation and are not tagged asymptotic forms:

- (a) the relation's token appears before the first `_of_`;
- (b) the first token is one the left-hand side can start with: its head function, an operator on
  its leftmost spine, the `nonneg`/`pos` reading of `0 ≤ x`/`0 < x`, or `exists`/`ae`;
- (c) every library-function token in the name occurs in the statement.

Results:

- **Flags**: 4 + 4 + 12 (checks (a) and (b) both flag `IsUniformApproxOn.apply`). Hand review: 5
  of the 7 theorems flagged by (a) or (b) are real, and 8 of the 12 flagged by (c) (§5.3).
- **Mutation test** on 600 passing theorems: a relation swap is caught 337 of 369 times, and a head
  replacement 128 of 128.
- **Random sample** of 30 passing theorems, read by hand: all 30 names are faithful.

### 5.2 Findings

#### 5.2.1 Overall rates by topic

"Recommended renames" are the declarations that break the grammar proposed by the audit under its
recommended options. "Option" counts the further renames that the open decisions would add.

| topic | decls | recommended renames | rate | further, if every option is taken |
|---|---|---|---|---|
| Matrix | 2220 | 9 | 0.4% | 23 |
| Krylov | 281 | 1 | 0.4% | 0 |
| Polynomial | 100 | 0 | 0% | 0 |
| Probability | 392 | 25 | 6.4% | 5 |
| RandomMatrix | 200 | 16 | 8.0% | 0 |
| Sketching | 331 | 9 | 2.7% | 70 (S6: 9 sample-size definitions and the theorems that name them) |
| LowRank | 307 | 48 | 15.6% | 1 |
| Regression | 48 | 10 | 20.8% | 0 |
| Estimation | 31 | 3 | 9.7% | 7 |
| ForMathlib | 195 | 1 | 0.5% | 4 |

The deterministic layers (Matrix, Krylov, Polynomial) are close to clean. The rate rises with the
share of tail bounds in a topic.

#### 5.2.2 Tail bounds

All 188 tails are stated in `μ.real`; none uses `μ` in `ℝ≥0∞`.

**Prefix.** 109 root names use `measureReal_`. Among namespaced names, 64 use `measure_` and 15 use
`measureReal_`.

- CONTRIBUTING §4 (2026-10-14) says namespaced → `measure_`, root → `measureReal_`. That copies
  Mathlib's `HasSubgaussianMGF.measure_ge_le`.
- The rule is broken 15 times by namespaced `measureReal_` names, e.g.
  `Matrix.PosSemidef.measureReal_not_specNorm_sub_nystrom_le_le_of_hasLaw_gaussianMatrix`,
  `SymmetricGauge.measureReal_not_matrixNorm_conjTranspose_mul_self_sub_rsvd_le_le_of_hasLaw_haarFrame`.
  Their namespace comes from dot notation on a side condition, not from an interface.
- The rule also hides what the statement is: the same `μ.real {…} ≤ δ` is spelled
  `HasSubspaceInjection.measure_frobNorm_sub_rsvd_sq_gt_le` in one family and
  `measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_srht` in the next.
- Elsewhere Mathlib lets the statement decide (`HasLaw.measure_eq`/`HasLaw.measureReal_eq`,
  `HasSubgaussianMGF.measureReal_le_le_exp`).

**Event.**

| event in the statement | count | name token |
|---|---|---|
| `b ≤ X ω` (subject on the right) | 63 | `X_ge` 58, `b_le_X` 3, missing 2 |
| `b < X ω` | 57 | `X_gt` 54, `b_lt_X` 3 |
| `¬ (err ≤ b)`, scalar | 28 | `not_err_le` |
| `X ω ≤ b` / `X ω < b` | 17 / 1 | `X_le` / `X_lt` |
| `∃ k, …` | 6 | `exists_…` |
| `b(ω) < err(ω)`, both random (GN vs RSVD) | 6 | `err_gt` |
| `¬` of a Loewner inequality, conjunction or predicate | 4 + 2 + 2 | `not_…` |

The 28 scalar `¬ (err ≤ b)` tails are the LowRank Gaussian RSVD/Nyström tails, the Gaussian
pseudoinverse tails and two sampling tails. They sit next to `gt` tails for the same measure and
algorithm in 7 families (frobNorm/rsvd, specNorm/rsvd, matrixNorm/rsvd, specNorm/nystrom,
nuclearNorm/nystrom, matrixNorm/nystrom, frobNorm/pinv). For example:

- `measureReal_not_frobNorm_sub_rsvd_le_le_of_hasLaw_gaussianMatrix`
- `measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_srht`

The two statements denote the same set (`not_le` is a `@[simp]` lemma, so simp turns the first into
the second); the spelling is a choice, not mathematics. The §5.3 "tail" vocabulary row
(`μ.real {ω | ¬ good ω} ≤ δ`) licenses the `¬` form, which is how it arose.

**Reading order.** 6 tails are named left to right from the bound:

- `measureReal_mul_nuclearNorm_lt_abs_hutchpp_sub_trace_le_of_isSubgaussianVector` for
  `{ε‖A‖_* < |hutchpp − tr A|}`;
- `measureReal_mul_card_le_norm_sq_le_of_hasLaw_gaussianVector`.

Of the 120 subject-on-the-right tails, 112 are named subject first (`abs_hutchpp_sub_trace_ge`);
the other 2 miss a relation token.
Mathlib allows both readings, but recommends `ge`/`gt` "if the second argument is more variable".

**Missing relation.** Three names have only one relation token, e.g.
`measureReal_norm_sq_le_of_hasLaw_gaussianVector` states `μ.real {‖g‖² ≤ n − 2√(nt)} ≤ e^{−t}`;
by the grammar it is `measureReal_norm_sq_le_le_…`.

#### 5.2.3 Expectations, moments, variances: uniform

- 283 of 284 conclusions with an integral on the left start `integral_`. The exception,
  `le_map_integral_of_integral_mem`, is Jensen with the integral on the right.
- 20 of 20 `Var[…]` conclusions start `variance_`.
- The names contain no `expected`, `expectation` or `mean`.
- Second moments: for every integral of a norm (177), `_sq` appears before the relation exactly
  when the integrand is squared. `E‖·‖²` is `integral_<norm>_…_sq_le`; `(E‖·‖)²` does not occur.
- Covariance uses Mathlib's `cov[…]` and `covariance_`; conditional expectation uses `condExp_`
  (Mathlib).

#### 5.2.4 Order of subtraction

Counts are statement occurrences: one (theorem, computed object) pair each.

| family | `exact − computed` | `computed − exact` |
|---|---|---|
| LowRank (rsvd, nystrom, GN, RBKI, NysBKI, early-truncated) | 174 | 5 (`rsvd − truncatedSVD` comparisons between two approximations, not errors) |
| Matrix (algorithm identities) | 29 | 0 |
| Krylov (`xs − cgIterate`, `cfc f A *ᵥ b − lanczosFA`) | 29 | 8 (`x_k − x_0 ∈ K` and residual fields: not errors) |
| Estimation (`hutchpp − tr`, `girardHutchinson − tr`) | 0 | **10** |

The library writes errors as `exact − computed` everywhere except trace estimation, which writes
`estimate − truth` (`hutchpp_sub_trace`, `integral_norm_hutchpp_sub_trace_sq`). Names always follow
their statement: 0 names contradict the statement's order.

#### 5.2.5 Hypotheses: laws, distribution classes, interfaces, namespaces

- **Laws** are uniform. A hypothesis `HasLaw X (law …) μ` appears as `_of_hasLaw_<law>` in 431 of
  437 cases. The 6 omissions name a second law or are transfer lemmas
  (`hasLaw_gaussianMatrix_of_hasLaw_uncurry`).
- Mathlib's scalar Gaussians (`HasGaussianLaw` 9, `gaussianReal` 7) appear only where the object is
  scalar.
- **Instance hypotheses.** `[IsLeftUnitarilyInvariant ν]` is always named in the name (32 of 32), so
  "rotation-invariant law" is a name facet even though the hypothesis is an instance.
- **Distribution classes and sketch interfaces** are split:

  | predicate | in its namespace | `_of_` suffix |
  |---|---|---|
  | `HasSubspaceInjection`, `IsObliviousSubspaceInjection`, `HasJLMoment`, `HasProjectionCostPreserving` | 17, 17, 24, 3 | 0, 0, 1, 0 |
  | `IsSubgaussianVector` | 16 (its API: `IsSubgaussianVector.measure_norm_sq_ge_le`) | 29 (consumers: `measureReal_frobNorm_sub_rsvd_sq_gt_le_of_isSubgaussianVector`) |
  | `IsIsotropic` | 14 | 6 |

  Consumers of a **sketch property** sit in its namespace: `HasSubspaceInjection.measure_…_rsvd_…`.
  Consumers of a **distribution class** take a suffix: `…_rsvd_…_of_isSubgaussianVector`. The
  practice is consistent within each kind but not written down. The explorer has to read both,
  which Appendix B of the redesign already does.
- **Dot notation (§5.2).** Of the 1,626 theorems whose first explicit argument is a predicate
  hypothesis:
  - 1,114 live in that predicate's namespace;
  - 301 use `_of_` (286 of them `HasLaw`, which has no useful namespace);
  - 191 are root with the hypothesis unnamed (`IsHermitian` 56 and `HasOrthonormalCols` 38 among
    them).

  The §5.2 rule is therefore followed loosely. No rename is proposed: namespace or root is a
  usability choice that a script cannot judge, and the explorer gets facets from `typeDeps` anyway.

#### 5.2.6 Synonyms and spellings

| concept | spellings | note |
|---|---|---|
| intrinsic dimension | `intrinsicDim` 8 (matrix Chernoff/Bernstein tails), `intrinsicDimension` 6 (the definition) | synonym |
| `G * Gᴴ` | `gram` 5 (`integral_frobNorm_mul_gram_mul_sub_sq_of_hasLaw_gaussianMatrix`) | §5.3 gives Gram matrices no name; Mathlib's `Matrix.gram` is a different object, bridged by `conjTranspose_mul_self_eq_gram` |
| `fromBlocks A 0 0 B` | `fromBlocks_diagonal` 7 (`cfc_fromBlocks_diagonal`, `inertiaPos_fromBlocks_diagonal`); `fromBlocks_zero₁₂_zero₂₁` (`rank_fromBlocks_zero₁₂_zero₂₁`) | Mathlib's `fromBlocks_diagonal` means `fromBlocks (diagonal d₁) 0 0 (diagonal d₂)` |
| vector 2-norm | `norm` 126, `norm_toLp` 22 for `‖WithLp.toLp 2 x‖` | `toLp` justified in bridge lemmas only; about 10 non-bridge uses (`norm_toLp_mulVec_le`) |
| column space | `range_…` 19, `range_mulVecLin_…` 13 | §5.3 fixes column space as `.mulVecLin.range`, so `range` is unambiguous |
| sample sizes (sketch rows) | `…Dim` 5 (`jlDim`, `gaussianEmbeddingDim`), `…Rows` 2 (`countSketchRows`), `…Size` 2 (`samplingSize`) | one concept, three suffixes; named bounds otherwise use `Constant`, `Factor`, `Tail`, `Bound`, `Ratio` |
| generalized Nyström | `generalizedNystrom` everywhere, but `truncatedGNFactor` | abbreviation in one named bound |
| range finder | `rangeFinderTailRatio`, `subgaussianRangeFinderFactor` (definitions only) | names the analysed step (HMT's range finder), not the algorithm; acceptable |
| `singularValues A k ^ 2` | `sq_singularValues` 16, `singularValues_…_sq` 0 | norms use the opposite placement: `frobNorm_…_sq` 68, `specNorm` 11, `norm` 22 (§2.7) |

No synonym exists for `specNorm`, `frobNorm`, `pinv`, `rsvd`, `eigenvalue`, `rangeProjector`,
`truncatedSVD` or `quadForm`. The vocabulary table (§5.3) has worked.

#### 5.2.7 `sq` and `pow`

- Taken from the statements: when the left side is `f (args) ^ 2` with `f` a norm, the name puts
  `sq` after the argument (`frobNorm_sub_rsvd_sq`, as in Mathlib's `norm_sub_sq`) in 101 of 102
  cases. The remaining one is named differently altogether.
- For `singularValues`, it is `sq_` first in 8 of 8 (16 names in all).
- No name says `pow` where the statement has `^ 2`.

#### 5.2.8 Asymptotic forms

There are 67 `exists_forall_` names; 61 carry an `Asymptotic:` line, and the other 6 are ordinary
∃∀ statements. All 61 follow one rule that CONTRIBUTING §5.2 states only as "followed by the
explicit theorem's conclusion":

- start with `exists_forall_`;
- keep the explicit name's conclusion up to its main relation, and drop the right-hand-side shape
  tokens (`_one_add_mul`, `_mul_exp`, `_mul_rpow`, `_singularGapRatio`);
- add `_of_singularGapRatio_pos` for gapped bounds;
- keep the explicit hypothesis suffixes, except the size threshold
  (`_of_jlDim_le`, `_of_le_card`, …);
- put the theorem in the root namespace. That is necessary: 10 explicit theorems are in
  `Matrix.PosSemidef.`, but `∃ C` comes before `H`, so dot notation is impossible.

Example: `integral_specNorm_sub_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix` →
`exists_forall_integral_specNorm_sub_rbki_sq_le_of_singularGapRatio_pos_of_hasLaw_gaussianMatrix`.

#### 5.2.9 Mathlib conventions and the rest

- **Case.** 0 violations: theorems are snake_case, Prop-valued definitions and structures
  UpperCamelCase, data lowerCamelCase. Acronyms follow Mathlib's group rule (`rsvd`,
  `earlyTruncatedRSVD`).
- **Quality or source words.** None (`mono_error` refers to the error parameter of
  `IsUniformApproxOn`).
- **Classical names as bound-shape tokens.** `_bernstein` 12, `_chernoff` 11, `_freedman` 3,
  `_mcdiarmid` 1. These are allowed by §5.2 rule 1; none matches a definition in its conclusion.
- **RHS shape tokens.** Used for disambiguation per §5.2 rule 4 (`_le_one_add_mul`, `_mul_exp`,
  `_intrinsicDim`). They are optional and inconsistent by design, so the grammar marks them
  "only when needed".
- **Leading scalar factor.** 35 names (Matrix 23, mostly Davis–Kahan and perturbation) start with
  it, e.g. `mul_matrixNorm_conjTranspose_mul_le_of_eigenvalue` for `δ · ‖V⊥ᴴU‖ ≤ ‖R‖`. This is
  Mathlib-correct, but a facet parser must skip `mul_` before the measured norm. That matters for
  extending facets to deterministic results.
- **Isolated mismatches** (checker, hand-confirmed):
  - `variance_quadForm_of_hasLaw_rademacherVector_le`: the relation comes after the hypothesis;
  - `charpoly_add_vecMulVec_mul`: the LHS is `(X − C μ) * charpoly`;
  - `uniformSphereVector_map_conjTranspose_mulVec_eq`: the LHS is `Measure.map … (uniformSphereVector n)`;
  - `conjTranspose_arnoldiMatrix_mul_mul_arnoldiMatrix_submatrix_castSucc`: the inner term is named
    before the outer `submatrix`;
  - `exists_bernstein_exponent`: names a concept, not the statement;
  - `posDef_of_exp_mul`: its `of` is `Matrix.of`, which reads as a hypothesis separator.
- **Conjunction conclusions** (§5.2 "two-sided bounds are two theorems"): 8.

### 5.3 Checker flags and their review

A.3 Checker flags and their review (`out/flags.tsv`):

| check | flags | real | benign |
|---|---|---|---|
| (a) relation | 4 | `variance_quadForm_of_hasLaw_rademacherVector_le`, `exists_bernstein_exponent` | `IsUniformApproxOn.apply` (namespace API), `schattenNorm_anti` (Mathlib `_anti`) |
| (b) head | 4 | `charpoly_add_vecMulVec_mul`, `uniformSphereVector_map_conjTranspose_mulVec_eq`, `conjTranspose_arnoldiMatrix_mul_mul_arnoldiMatrix_submatrix_castSucc` | `IsUniformApproxOn.apply` |
| (c) token absent | 12 | 7 × `fromBlocks_diagonal`, `posDef_of_exp_mul` | `ext_quadForm` (ext lemma names its hypothesis), `isQR_householder` (the `householderQ`/`householderR` pair), `givensHessenbergStep_plane_ne`, `exists_eigenvalue_branch_of_rootMultiplicity_eq_one` |
| tail prefix | 64 | all (D1) | |
| tail reading order | 6 | all (D3) | |
| tail relation missing | 4 | 3 | `measureReal_eq_measureReal_gaussianMatrix_of_isLeftUnitarilyInvariant` (an equation of two tails) |
| asymptotic name | 24 vs the literal "explicit name" | 0 against the derived rule | |
