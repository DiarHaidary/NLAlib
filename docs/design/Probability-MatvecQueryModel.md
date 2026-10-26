# Design note: the matrix–vector query model for lower bounds (stage LB-A)

Status: approved, revised 2026-10-25 after the maintainer's decisions and the Fable review
(`~/nlalib-harness/reports/Review-Fable-LBA-Design.md`), on `design/lb-foundations` (rebased on
`origin/main` 59e1792). Decision sheet: `~/nlalib-harness/state/decisions/LB-A.json` (APPROVE,
OQ1–OQ9 decided: OQ2 (c), all others (a)). The changes against the reviewed draft are listed in
§15 (decision log).
Plan and literature: `~/nlalib-harness/reports/MatvecLowerBounds.md` (§1.2, §2, §3 Stage A);
maintainer decisions of 2026-10-25 (`state/decisions/MatvecLowerBounds.json`): STAGE-FIRST (a)
(this stage in parallel with S10), QUERY-MODEL-SCOPE (a) (adaptive from the start, deterministic
transcript functions, randomness externalized, no `Kernel.traj`), EXPLORER-TIMING (a) (§13).

Every signature in §3 is in the skeleton and elaborates: `lake build --wfail` of the three new
`NLAlib` modules succeeds, and `lake build NLAlibScaffold` gives 41 `sorry` warnings and nothing
else. `scripts/check_rules.py --files`, `check_refs.py`, `check_constants.py` and
`check_latex.mjs` pass on the changed files; `mk_all --check` is clean; the dispatcher's `locate`
finds all 41 targets of `~/nlalib-harness/pilot/lbA-targets.json`, which are exactly the sorried
declarations of the scaffold. The extraction-based name check (N1–N18) was not run; names are
listed for review in §9. `bin/check-skeleton` (rule G3): 41 targets, 0 names missing an import.

## 0. Summary

| | |
|---|---|
| New definitions (20, in `NLAlib`, written) | `QueryAlgorithm` and `history`, `queryAt`, `transcript`, `run`, `truncate` (with the proved `history_truncate`, `transcript_truncate`), `queries`, `queryMatrix`, `IsNonAdaptive`, `IsMeasurable`, `IsMeasurableFamily`, `gramSimulation`; the two-sided oracle `twoSidedMulVec` with `rightQueryMatrix`, `leftQueryMatrix`, `rightCount`, `leftCount`, `IsOneSided`; `QueryAlgorithm.resample`; `InformationTheory.tvDist` |
| New files | `Probability/QueryModel/{Basic,Yao}.lean`, `RandomMatrix/DeferredDecision.lean`, `LowRank/Optimality/RangeRecovery.lean`, `ForMathlib/InformationTheory/TotalVariation.lean` |
| Statements | 41 sorried (S 22, M 12, L 6, H 1) in 8 scaffold files; 63 declarations with the definitions and the two proved `truncate` lemmas |
| Glue in existing files | `ForMathlib/Probability/Independence/Basic.lean` (freezing lemma, F1–F2), `RandomMatrix/Gaussian/Invariance.lean` (G1), `RandomMatrix/Gaussian/Rank.lean` (Z1) |
| First end-to-end theorem | exact range recovery of $\mathbf{X}\mathbf{X}^{\mathsf{H}}$ needs $k$ queries ([ZhangEtAl2026, Lemma 4.2]), R6, for randomized adaptive algorithms (§4) |
| Next theorem the model is designed for | Shamir's $\Omega(\kappa\log(1/\varepsilon))$ for $\mathbf{A}\mathbf{x} = \mathbf{b}$ ([Shamir2026, Theorem 1]), stage C1 (§4) |
| Prototype | nothing: no query, oracle or algorithm notion exists in the prototype or the library (report §2) |
| Mathlib overlap | KL divergence and data processing, `IdentDistrib`, Gaussian independence from covariances, `noAtoms_gaussianReal` reused; no TV, Le Cam or Pinsker (§8) |
| Open questions | 9 (§11), all decided: OQ2 (c), the others (a) |

Four choices carry the design.

1. **One oracle type; matrix–vector by `A.mulVec` and `twoSidedMulVec A`.**
   `QueryAlgorithm Q R q β` is a deterministic adaptive algorithm against any oracle
   `f : Q → R`: `query i` maps the first `i` responses to the next query, `output` maps all `q`
   responses to the answer. The one-sided matvec model is the oracle `A.mulVec`. Access to
   $\mathbf{A}$ and $\mathbf{A}^{\mathsf{H}}$ is the product-type oracle `twoSidedMulVec A`: a
   query is a pair $(\mathbf{x}, \mathbf{y})$, its response $(\mathbf{A}\mathbf{x},
   \mathbf{A}^{\mathsf{H}}\mathbf{y})$ (OQ2 (c)). Either part may be zero; the cost of a
   transcript is counted per side, `rightCount τ` and `leftCount τ` (rounds with a nonzero right,
   respectively left, part), so budgets for products with $\mathbf{A}$ and with
   $\mathbf{A}^{\mathsf{H}}$ are separate hypotheses (OQ9).
2. **Randomness is outside the algorithm.** A randomized algorithm is a family
   `alg : S → QueryAlgorithm Q R q β` with a jointly measurable predicate, and the seed is a
   random variable `s : Ω → S` independent of the input `X : Ω → M`. All statements live on one
   probability space `(Ω, μ)`, as every random-matrix statement of the library does; Yao's
   principle is Fubini (§3.2). No kernels.
3. **Deferred decision as an identity in law, basis-free.** For a Gaussian
   $\mathbf{X}$ queried adaptively through `twoSidedMulVec`, with $\mathbf{E}$, $\mathbf{F}$ the
   projectors onto the complements of the left and right query spans (functions of the
   transcript $\tau$),
   $$(\tau, \mathbf{X}) \overset{d}{=} (\tau, \mathbf{X} - \mathbf{E}\mathbf{X}\mathbf{F} +
   \mathbf{E}\mathbf{X}'\mathbf{F})$$
   with $\mathbf{X}'$ an independent copy (D2). No conditional laws, no orthonormal-query
   normalisation, no transcript-dependent index types: the projectors are `rangeProjector` of the
   left and right query matrices, defined for any rank. The papers' frame form (block $\mathbf{D}_t$ i.i.d.
   Gaussian given the transcript) is the corollary D3. For general right unitarily invariant laws
   (Haar) the form is a stabilizer identity: $(\tau, \mathbf{X}) \overset{d}{=} (\tau,
   \mathbf{X}\mathbf{S}(\tau))$ for any transcript-measurable rotation fixing what was revealed
   (H1, H2).
4. **The freezing lemma is the engine.** Every step above is "for each fixed value of an
   independent variable the laws agree, so the joint laws agree" (F1, F2), in ForMathlib.

## 1. Scope

In: the deterministic adaptive query model with any oracle; transcripts, queries, outputs;
indistinguishability; non-adaptive algorithms; the two-sided oracle with per-side costs and
`IsOneSided`; measurability; randomized algorithms as seeded
families; Yao's principle (both easy-direction forms); the freezing lemma; the Gaussian
two-sided adaptive deferred decision (resampling and frame forms); the stabilizer form for right
unitarily invariant laws (non-adaptive and adaptive); the Gram simulation; exact range recovery
needs $k$ queries (Zhang et al. Lemma 4.2), deterministic and randomized; total variation
distance with data processing, Le Cam's two-point bound and Pinsker's inequality.

Out (§12 has what each needs): orthonormalising queries without loss of generality (not needed:
D2 is basis-free); zero padding ([ZhangEtAl2026, Lemma 3.5]);
the bridge to Mathlib's `Kernel` and `bayesRisk`/`minimaxRisk`; bounded-precision queries; the
two-sided Haar form beyond H2's "fixes what was revealed" (it is H2); χ² divergence, Fano;
Shamir's Theorem 1; MMMW Theorem 8; Zhang et al. Theorem 4.6 and §5–6.

## 2. Objects

### 2.1 `QueryAlgorithm` (in `NLAlib/Probability/QueryModel/Basic.lean`, written)

```lean
structure QueryAlgorithm (Q R : Type*) (q : ℕ) (β : Type*) where
  query : (i : ℕ) → (Fin i → R) → Q
  output : (Fin q → R) → β

def history (alg) (f : Q → R) : (i : ℕ) → Fin i → R            -- by recursion, Fin.snoc
  | 0 => Fin.elim0
  | i + 1 => Fin.snoc (history alg f i) (f (alg.query i (history alg f i)))
def queryAt (alg) (f) (i : ℕ) : Q := alg.query i (alg.history f i)
def transcript (alg) (f) : Fin q → R := alg.history f q
def run (alg) (f) : β := alg.output (alg.transcript f)
def queries (alg) (τ : Fin q → R) (j : Fin q) : Q := alg.query j fun l => τ (Fin.castLE _ l)
def queryMatrix (alg : QueryAlgorithm (n → 𝕜) R q β) (τ) : Matrix n (Fin q) 𝕜 :=
  Matrix.of fun r j => alg.queries τ j r
def IsNonAdaptive (alg) : Prop := ∀ i < q, ∀ h h', alg.query i h = alg.query i h'
structure IsMeasurable (alg) : Prop := measurable_query : ∀ i < q, Measurable (alg.query i);
  measurable_output : Measurable alg.output
structure IsMeasurableFamily (alg : S → QueryAlgorithm Q R q β) : Prop  -- jointly in (seed, history)

def twoSidedMulVec (A : Matrix m n 𝕜) (v : (n → 𝕜) × (m → 𝕜)) : (m → 𝕜) × (n → 𝕜) :=
  (A *ᵥ v.1, Aᴴ *ᵥ v.2)
-- for alg : QueryAlgorithm ((n → 𝕜) × (m → 𝕜)) R q β:
def rightQueryMatrix (alg) (τ) : Matrix n (Fin q) 𝕜 := Matrix.of fun r j => (alg.queries τ j).1 r
def leftQueryMatrix (alg) (τ) : Matrix m (Fin q) 𝕜 := Matrix.of fun r j => (alg.queries τ j).2 r
def rightCount (alg) (τ) : ℕ := {j : Fin q | (alg.queries τ j).1 ≠ 0}.ncard
def leftCount (alg) (τ) : ℕ := {j : Fin q | (alg.queries τ j).2 ≠ 0}.ncard
def IsOneSided (alg) : Prop := ∀ τ, alg.leftCount τ = 0
```

Why these shapes.

* **`query` is indexed by `ℕ`, histories by `Fin i`** (OQ3). `history` is then a structural
  recursion with `Fin.snoc`, the library's style for algorithms (`gaussState`, `cgState`), and
  queries never carry a proof of `i < q`. Queries with $i \ge q$ are junk and never made;
  `IsNonAdaptive` and the measurability predicates quantify over `i < q` only (review item 5),
  so an algorithm's unused tail is unconstrained. `output` sees responses only: the
  queries are functions of the responses (`queries`, Q2).
* **`queries` recomputes the queries from a transcript**, so everything a consumer needs (query
  projectors, frames, the stabilizer condition) is a function of `τ : Fin q → R` alone; this is
  what "transcript-measurable" means in the papers. `queryMatrix` is the vector-query case
  (one-sided `A.mulVec`); `rightQueryMatrix` and `leftQueryMatrix` are the two parts of pair
  queries to `twoSidedMulVec A`.
* **Two-sided access is a product type, not the dilation** (OQ2 (c), maintainer: "i want to be
  able to have different numbers of left and right"). A round asks for
  $\mathbf{A}\mathbf{x}$ and $\mathbf{A}^{\mathsf{H}}\mathbf{y}$ at once; the response types are
  the natural ones ($\Bbbk^m \times \Bbbk^n$), so the Gram simulation, D1–D3, H2 and the
  range-recovery bound read with no block bookkeeping. Mathematically it is the dilation oracle
  with the blocks reordered; what changes is the accounting.
* **Per-side costs count nonzero parts, not `Option` sides** (OQ9). `rightCount τ` is the number of
  rounds whose right part is nonzero, `leftCount τ` likewise; a budget is a hypothesis
  `∀ τ, alg.rightCount τ ≤ q_R` (and `leftCount ≤ q_L`). A zero part returns zero, which the
  algorithm knew, so it is free, and counting nonzero parts is exactly Zhang et al.'s accounting
  (one product per round with the side chosen adaptively embeds as a round with one zero part; a
  pair splits into two such rounds). `Option` sides were considered and rejected: the response
  type would become `Option (m → 𝕜) × Option (n → 𝕜)`, every consumer would match on `none`, and
  the query matrices would need a default column anyway, which is the zero vector. The rank
  lemmas C1/C2 (`rank (rightQueryMatrix τ) ≤ rightCount τ`) are the form consumers use
  ("$q_R$ right products reveal at most a $q_R$-dimensional right span"). `q`, the number of
  rounds, bounds both counts and is what D2/D3/H1/H2/Y1/Y2 are stated for; none of them mention
  budgets. `IsOneSided := ∀ τ, leftCount τ = 0`; a one-sided algorithm is also expressible
  against `A.mulVec`, and for Hermitian $\mathbf{A}$ that oracle counts products exactly (R5, R6).
  The non-adaptive one-pass model (GN-type sketches with $\ell$ right and $p$ left products) is
  `IsNonAdaptive ∧ rightCount ≤ ℓ ∧ leftCount ≤ p`: both parts of every round fixed up front.
* **Measurability is a predicate, not structure fields** (OQ4). Upper-bound users who express an
  algorithm (`rsvd` as two passes) do not have to prove measurability to build one; lower bounds
  take `halg : alg.IsMeasurable` and conclude through its namespace (`halg.identDistrib_…`).
  Measurability is genuinely needed: without it the transcript is not a random variable.
* **Randomized algorithms are seeded families** with joint measurability
  (`IsMeasurableFamily`); `IsMeasurableFamily.isMeasurable` gives each member. This is the
  maintainer's QUERY-MODEL-SCOPE (a).

§5.3 rows (added in the implementing PR):

| query algorithm | `QueryAlgorithm Q R q β`, deterministic and adaptive: `query i` of the first `i` responses, `output` of all `q`; run against an oracle `f : Q → R` with `alg.transcript f`, `alg.run f`; queries from a transcript `alg.queries τ`, for vector queries `alg.queryMatrix τ` (queries as columns); a randomized algorithm is `alg : S → QueryAlgorithm …` with `QueryAlgorithm.IsMeasurableFamily alg` and a seed independent of the input; lower bounds take `alg.IsMeasurable` | `QueryAlgorithm.history_apply`, `QueryAlgorithm.queryAt_eq_queries_transcript`; Mathlib has none (Markov kernels: §8) |
| matrix–vector oracle | `A.mulVec` (one-sided, products $\mathbf{A}\mathbf{x}$); two-sided access is `twoSidedMulVec A`, pair query $(\mathbf{x}, \mathbf{y})$ ↦ $(\mathbf{A}\mathbf{x}, \mathbf{A}^{\mathsf{H}}\mathbf{y})$; right and left query matrices `alg.rightQueryMatrix τ`, `alg.leftQueryMatrix τ`; costs per side `alg.rightCount τ`, `alg.leftCount τ` (rounds with a nonzero part), budgets as hypotheses `∀ τ, alg.rightCount τ ≤ q_R`; one-sided `alg.IsOneSided`; one pass = `IsNonAdaptive` (both parts fixed up front) | `QueryAlgorithm.rank_rightQueryMatrix_le_rightCount`, `QueryAlgorithm.rank_leftQueryMatrix_le_leftCount` |

### 2.2 `gramSimulation` (same file, written)

`alg.gramSimulation k : QueryAlgorithm ((k → 𝕜) × (d → 𝕜)) ((d → 𝕜) × (k → 𝕜)) (2 * q) β` for
`alg : QueryAlgorithm (d → 𝕜) (d → 𝕜) q β`, against `twoSidedMulVec X`, `X : Matrix d k 𝕜`:
round `2i` is the left query $(\mathbf{0}, \mathbf{x}_i)$ (response
$\mathbf{X}^{\mathsf{H}}\mathbf{x}_i$ in the second component), round `2i + 1` the right query
$(\mathbf{X}^{\mathsf{H}}\mathbf{x}_i, \mathbf{0})$ (response
$\mathbf{X}\mathbf{X}^{\mathsf{H}}\mathbf{x}_i$ in the first); the original history is read
off pointwise (the first components of the odd responses), so the definition needs no recursion
of its own. It makes `q` products on each side (R3a, R3b). It reduces the Wishart oracle of Zhang et al. and BHSW to two-sided queries to the
factor, so one Gaussian lemma (D2) serves both. Shamir's oracle
$\mathbf{x} \mapsto (\mathbf{U}\mathbf{D}\mathbf{U}^{\mathsf{H}}\mathbf{x}, \mathbf{U}^{\mathsf{H}}\mathbf{x})$
is the same construction with $\mathbf{D}$ inserted (stage C1).

### 2.3 `QueryAlgorithm.resample` (in `NLAlib/RandomMatrix/DeferredDecision.lean`, written)

```lean
noncomputable def resample (alg : QueryAlgorithm ((k → 𝕜) × (d → 𝕜)) ((d → 𝕜) × (k → 𝕜)) q β)
    (X X' : Matrix d k 𝕜) : Matrix d k 𝕜 :=
  let τ := alg.transcript (twoSidedMulVec X)
  let E := 1 - rangeProjector (alg.leftQueryMatrix τ)
  let F := 1 - rangeProjector (alg.rightQueryMatrix τ)
  X - E * X * F + E * X' * F
```

A definition because D1, D2, R4b and R5 all use it, and the inline form is three lines. Over
`𝕜`, since D1 is deterministic; the Gaussian theorems are real (CONTRIBUTING §5.1, the Gaussian
law is real). No §5.3 row: it is stage-internal vocabulary, used by consumers only through D2,
D3 and D1.

### 2.4 `InformationTheory.tvDist` (in `NLAlib/ForMathlib/InformationTheory/TotalVariation.lean`, written)

```lean
noncomputable def tvDist (μ ν : Measure α) : ℝ :=
  ⨆ A : {A : Set α // MeasurableSet A}, |μ.real A - ν.real A|
```

Real valued, like `Measure.real` tails (CONTRIBUTING §5.2: real quantities stay real); bounded
by the masses for finite measures, so the supremum is genuine; junk for infinite measures,
documented. Namespace `InformationTheory`, next to Mathlib's `klDiv` (P5, P7).

## 3. Statement shapes

IDs are the `note_id`s of `~/nlalib-harness/pilot/lbA-targets.json`. Full docstrings with
`Proof:` lines are in the skeleton; here the shapes and the reasons. `τ X` abbreviates
`alg.transcript (twoSidedMulVec X)`.

### 3.1 `Probability/QueryModel/Basic.lean` (Q1–Q13, C1–C2, R1a–R3)

| ID | Name (`NLAlib.QueryAlgorithm.`) | Shape | Diff |
|---|---|---|---|
| Q1 | `history_apply` | `alg.history f i j = f (alg.queryAt f j)` | S |
| Q2 | `queryAt_eq_queries_transcript` | `alg.queryAt f j = alg.queries (alg.transcript f) j` | S |
| Q3 | `transcript_eq_of_forall_apply_queries_eq` | `(∀ j, g (alg.queries (alg.transcript f) j) = f (…)) → alg.transcript g = alg.transcript f` | M |
| Q4 | `run_eq_of_forall_apply_queries_eq` | same hypothesis `→ alg.run g = alg.run f` | S |
| Q5 | `IsNonAdaptive.queries_eq` | `alg.IsNonAdaptive → alg.queries τ = alg.queries τ'` | S |
| Q6 | `IsMeasurable.measurable_transcript` | `Measurable (uncurry O) → Measurable fun x => alg.transcript (O x)` | M |
| Q7 | `IsMeasurable.measurable_run` | `… → Measurable fun x => alg.run (O x)` | S |
| Q8 | `IsMeasurable.measurable_queryMatrix` | `Measurable alg.queryMatrix` | S |
| Q11 | `IsMeasurable.measurable_rightQueryMatrix` | `Measurable alg.rightQueryMatrix` | S |
| Q12 | `IsMeasurable.measurable_leftQueryMatrix` | `Measurable alg.leftQueryMatrix` | S |
| Q13 | `IsMeasurable.truncate` | `i ≤ q → (alg.truncate i).IsMeasurable` | S |
| Q9 | `IsMeasurableFamily.measurable_run` | `Measurable fun p : S × M => (alg p.1).run (O p.2)` | M |
| Q10 | `IsMeasurableFamily.isMeasurable` | `(alg s).IsMeasurable` | S |
| C1 | `rank_rightQueryMatrix_le_rightCount` | `(alg.rightQueryMatrix τ).rank ≤ alg.rightCount τ` | S |
| C2 | `rank_leftQueryMatrix_le_leftCount` | `(alg.leftQueryMatrix τ).rank ≤ alg.leftCount τ` | S |
| R1a | `gramDecode_history_gramSimulation` | `gramDecode ((alg.gramSimulation k).history (twoSidedMulVec X) (2 * i))` `= alg.history (X * Xᴴ).mulVec i` (the odd first components; decision T9-GRAM), every `i` | M |
| R1 | `run_gramSimulation` | `(alg.gramSimulation k).run (twoSidedMulVec X) = alg.run (X * Xᴴ).mulVec` | S |
| R2 | `IsMeasurable.gramSimulation` | `alg.IsMeasurable → (alg.gramSimulation k).IsMeasurable` | S |
| R3a | `rightCount_gramSimulation_le` | `(alg.gramSimulation k).rightCount τ ≤ q`, every `τ` | S |
| R3b | `leftCount_gramSimulation_le` | `(alg.gramSimulation k).leftCount τ ≤ q`, every `τ` | S |
| R3 | `rank_rightQueryMatrix_gramSimulation_le` | `((alg.gramSimulation k).rightQueryMatrix τ).rank ≤ q`, every `τ` (C1 with R3a) | S |

Q3 is the deterministic half of every adversary argument (two inputs that agree on the queries
made on one are indistinguishable). Its hypothesis is phrased with `queries (transcript f)`, not
`queryAt`, so that consumers (D1, H2) check it from the transcript. Oracles depending on an input
are uncurried families `O : M → Q → R` with `Measurable (Function.uncurry O)`; for matvecs this
is `measurable_fst.matrix_mulVec measurable_snd` (library `Measurable.matrix_mulVec`), so no
bridge lemma is stated.

### 3.2 `Probability/QueryModel/Yao.lean` (Y1, Y2)

```lean
theorem IsMeasurableFamily.measureReal_run_mem_le_of_indepFun [IsProbabilityMeasure μ]
    {alg : S → QueryAlgorithm Q R q β} (halg : IsMeasurableFamily alg) {O : M → Q → R}
    (hO : Measurable (Function.uncurry O)) {s : Ω → S} {X : Ω → M} (hs : AEMeasurable s μ)
    (hX : AEMeasurable X μ) (hsX : IndepFun s X μ) {B : Set (M × β)} (hB : MeasurableSet B)
    {δ : ℝ} (h : ∀ a : QueryAlgorithm Q R q β, a.IsMeasurable →
      μ.real {ω | (X ω, a.run (O (X ω))) ∈ B} ≤ δ) :
    μ.real {ω | (X ω, (alg (s ω)).run (O (X ω))) ∈ B} ≤ δ                       -- Y1, M
theorem IsMeasurableFamily.exists_le_measureReal_run_mem (halg) (hO) (ρ : Measure S)
    [IsProbabilityMeasure ρ] (ν : Measure M) [IsProbabilityMeasure ν] (hB : MeasurableSet B)
    (h : ∀ a, a.IsMeasurable → δ ≤ ν.real {x | (x, a.run (O x)) ∈ B}) :
    ∃ x, δ ≤ ρ.real {s | (x, (alg s).run (O x)) ∈ B}                             -- Y2, M
```

Y1 is the form downstream proofs use (the bad event on a random input, the seed independent);
Y2 is the textbook "distributional lower bound ⇒ worst-case lower bound". The event is a set of
(input, output) pairs because success depends on both (range recovery, relative error). The
direction proved is the easy half of Yao's minimax principle, the only one lower bounds use; the
minimax equality is not stated.

### 3.3 The freezing lemma (glue, `ForMathlib/Probability/Independence/Basic.lean`; F1, F2)

```lean
theorem IndepFun.identDistrib_prodMk_of_forall_map_eq [IsFiniteMeasure μ] (hTZ : IndepFun T Z μ)
    (hT : AEMeasurable T μ) (hZ : AEMeasurable Z μ) (hF : Measurable (uncurry F))
    (hG : Measurable (uncurry G)) (h : ∀ t, (μ.map Z).map (F t) = (μ.map Z).map (G t)) :
    IdentDistrib (fun ω => (T ω, F (T ω) (Z ω))) (fun ω => (T ω, G (T ω) (Z ω))) μ μ  -- F1, M
theorem IndepFun.hasLaw_prodMk_prod_of_forall_map_eq … (h : ∀ t, (μ.map Z).map (F t) = ν) :
    HasLaw (fun ω => (T ω, F (T ω) (Z ω))) ((μ.map T).prod ν) μ                     -- F2, S
```

In `ProbabilityTheory` (Mathlib vocabulary only, P4/P5), next to the file's Tonelli and
section-bound lemmas for independent pairs. F2 with `ProbabilityTheory.indepFun_iff_hasLaw_prodMk_prod`
gives "$F(T, Z)$ has law $\nu$ and is independent of $T$". Shared with S10 (§10).

### 3.4 Deferred decision (`RandomMatrix/DeferredDecision.lean`; G1 in `Gaussian/Invariance.lean`)

| ID | Name | Shape | Diff |
|---|---|---|---|
| G1 | `NLAlib.identDistrib_mul_mul_of_hasLaw_gaussianMatrix` | fixed star projections `E₂`, `F₁`, `F₂` (no hypothesis on `E₁`, decision UNUSED-HE1), `E₁ * E₂ = E₂`, `F₁ * F₂ = F₂`, `X ⊥ X'` Gaussian: `IdentDistrib (E₁ X F₁) (E₁ X F₁ - E₂ X F₂ + E₂ X' F₂)` | L |
| D1 | `QueryAlgorithm.transcript_resample` | `alg.transcript (twoSidedMulVec (alg.resample X X')) = τ X` (over `𝕜`, every `X X'`) | M |
| D2 | `QueryAlgorithm.IsMeasurable.identDistrib_resample_of_hasLaw_gaussianMatrix` | `X ⊥ X'` Gaussian `d × k`: `IdentDistrib (τ X, X) (τ X, alg.resample X X')` | L |
| D3 | `QueryAlgorithm.IsMeasurable.hasLaw_prodMk_conjTranspose_mul_mul_of_hasLaw_gaussianMatrix` | measurable frames `WL τ`, `WR τ` with orthonormal columns, `(WL τ)ᴴ * leftQueryMatrix τ = 0`, `(WR τ)ᴴ * rightQueryMatrix τ = 0`: `HasLaw (τ X, (WL (τ X))ᴴ * X * WR (τ X)) ((μ.map τX).prod (gaussianMatrix r s))` | M |
| H1 | `NLAlib.identDistrib_prodMk_mul_of_isRightUnitarilyInvariant` | `[IsRightUnitarilyInvariant ν]`, `HasLaw X ν μ`, fixed `V`, measurable orthogonal `S Y` with `S Y * V = V`: `IdentDistrib (X V, X) (X V, X * S (X V))` | L |
| H2 | `QueryAlgorithm.IsMeasurable.identDistrib_prodMk_mul_of_isRightUnitarilyInvariant` | `[IsRightUnitarilyInvariant ν]`, measurable orthogonal `S τ` fixing the right query matrix and the matrix of second response components, `S τ * rightQueryMatrix τ = rightQueryMatrix τ`, `S τ * Matrix.of (fun r j => (τ j).2 r) = …`: `IdentDistrib (τ X, X) (τ X, X * S (τ X))` | H |

Why these shapes.

* **D2 is the primary statement; D3 is the papers' form.** The resampling form needs no frames,
  so no index type depends on the transcript, and it composes: R4 and R5 use it as "replace the
  hidden block, then condition on everything else". D3 recovers Zhang et al.'s
  "$\mathbf{D}_t$ i.i.d. given $\mathcal{G}_t$" and BHSW Lemma 3.4 in the frame form a
  posterior-covariance argument (Zhang Lemmas 4.4–4.6) wants. D3's frames are assumed, not
  constructed: a consumer chooses them (orthonormal completion of the query span, measurable by
  `measurable_gramSchmidtQ` or the SVD), and an empty frame type is allowed.
* **D2 takes `X'` as a hypothesis.** A consumer without an independent copy on `Ω` extends the
  space (`μ.prod (gaussianMatrix d k)`); D3 does this inside its proof so that its statement has
  no `X'`.
* **G1 is stated for fixed projectors**, in the existing Gaussian invariance file: it is the
  two-sided analogue of `indepFun_conjTranspose_mul_of_hasLaw_gaussianMatrix` and has consumers
  outside query models (sketch analysis with nested subspaces).
* **H1/H2 are stated for every right unitarily invariant law** (`IsRightUnitarilyInvariant`, the
  library's interface), not for Haar alone: Gaussian, Haar frames and their products all satisfy
  it, and the proof uses only the invariance. Over ℝ, because the stabilizer randomizer uses
  `haarFrame` (real). H2's condition "fixes what was revealed" is in terms of the transcript only,
  and covers one-sided queries (left parts zero: the second response components vanish),
  Shamir's oracle and DEM's two-sided oracle (via the Gram-type simulation). H1 needs no
  finiteness of the query index `p` (review item 4): its outline uses the column span of
  $\mathbf{V}$ instead of `rank V`, and the build's unused-instance linter rejects a
  `[Fintype p]` that the statement does not use.
* **H2 is the one H target** (OQ5). Outline (review item 2): (i) the one-sided single-query Haar
  case on the stabilizer subgroup $K = \operatorname{Stab}(\mathbf{g}) \cong O(c)$ (left query
  $\mathbf{g}$, $\mathbf{S}$ fixing $\mathbf{O}^{\mathsf{H}}\mathbf{g}$; left invariance of Haar
  and transitivity of $K$ on $\{\mathbf{Z} : \mathbf{Z}^{\mathsf{H}}\mathbf{g} = \mathbf{h}\}$),
  the right-query case being H1; (ii) induction over the rounds for Haar, two-sided; (iii) general
  $\nu$ by $\mathbf{X} \overset{d}{=} \mathbf{Y}\mathbf{O}$ with $\mathbf{O}$ Haar independent,
  freezing $\mathbf{Y}$. Second review: the stabilizer of the revealed span cannot be built from a
  transcript-dependent frame (its column count varies), so the randomizer is
  $\operatorname{polar}(\mathbf{P}_{\mathbf{V}} + \mathbf{E}\mathbf{G}\mathbf{E})$ with
  $\mathbf{G}$ Gaussian (fixed types, set to `1` on a null set), and one round is a pair query,
  handled as a right query followed by a left query inside the stabilizer; ≈300 lines in six
  private lemmas. Its consumers are stage C (Shamir, DEM, BN23), not this
  stage's end-to-end theorem.

### 3.5 Measure zero (glue, `RandomMatrix/Gaussian/Rank.lean`; Z1)

`measure_mul_mul_eq_eq_zero_of_hasLaw_gaussianMatrix : N ≠ 0 → F ≠ 0 → μ {ω | N * X ω * F = C} = 0`
(M). The a.s. statements of the library are rank statements (`ae_rank_mul_eq_min_…`); this is the
affine-avoidance fact R4 and R5 need, in `μ` (ℝ≥0∞, N14), since "probability zero" is the
conclusion.

### 3.6 Exact range recovery (`LowRank/Optimality/RangeRecovery.lean`; R4a, R4b, R4–R6)

```lean
theorem rank_mul_of_snoc_eq_rank_of_snoc (B : Matrix k d 𝕜) (U : Matrix d (Fin i) 𝕜) (x : d → 𝕜)
    (hU : (B * U).rank = U.rank)
    (hx : x ∈ span (range Uᵀ) ∨ B *ᵥ x ∉ span (range (B * U)ᵀ)) :
    (B * [U x]).rank = [U x].rank          -- [U x] = Matrix.of fun r => Fin.snoc (U r) (x r); R4a, M
theorem IsMeasurable.measure_queryAt_notMem_span_and_mulVec_mem_span_eq_zero (halg) (hX)
    (hi : i < q) (hik : i < card k) :
    μ {ω | x_i ∉ span {x_l | l < i} ∧ Xᴴ x_i ∈ span {Xᴴ x_l | l < i}} = 0
                                   -- x_l = alg.queryAt (X * Xᴴ).mulVec l, written out; R4b, L
theorem IsMeasurable.ae_rank_conjTranspose_mul_leftQueryMatrix_gramSimulation
    (halg : alg.IsMeasurable) (hX : HasLaw X (gaussianMatrix d k) μ) (hq : q ≤ card k) :
    ∀ᵐ ω ∂μ, ((X ω)ᴴ * U ω).rank = (U ω).rank   -- U = left query matrix of the simulation; R4, M
theorem IsMeasurable.measure_range_le_range_run_eq_zero_of_hasLaw_gaussianMatrix
    {alg : QueryAlgorithm (d → ℝ) (d → ℝ) q (Matrix d p ℝ)} (halg) (hX) (hq : q < card k) :
    μ {ω | LinearMap.range (X ω * (X ω)ᴴ).mulVecLin ≤
        LinearMap.range (alg.run (X ω * (X ω)ᴴ).mulVec).mulVecLin ∧
      (alg.run (X ω * (X ω)ᴴ).mulVec).rank < card d} = 0                           -- R5, L
theorem IsMeasurableFamily.measure_range_le_range_run_eq_zero_of_hasLaw_gaussianMatrix
    (halg : IsMeasurableFamily alg) (hs : AEMeasurable s μ) (hX) (hsX : IndepFun s X μ)
    (hq : q < card k) : μ {… (alg (s ω)).run …} = 0          -- R6, S; Result: range-recovery-k-queries
```

The event. Zhang et al. state it for a rank-$k$ projector $\mathbf{P}$ with
$\mathbf{A}(\mathbf{I} - \mathbf{P}) = \mathbf{0}$ and success probability bounded below. Here
the output is any $\mathbf{V} \in \mathbb{R}^{d \times p}$ and the event is
"range of $\mathbf{A}$ contained in range of $\mathbf{V}$, and $\operatorname{rank}\mathbf{V} <
d$" (OQ7): a rank-$k$ projector with $k < d$ is the case $\mathbf{V} = \mathbf{P}$; outputs of
any width (a basis, a sketch) are covered; the rank condition is necessary (outputting
$\mathbf{I}$ always succeeds) and is the only one. The conclusion "probability zero" is stronger
than "fails with probability $\ge 1/3$".

Degenerate cases (checked by hand): $q = 0$ (constant output; true since $k \ge 1$ forces
$\mathbf{A} \ne \mathbf{0}$ a.s. off a proper subspace); $k \ge d$ (then
$\operatorname{range}\mathbf{A} = \mathbb{R}^d$ a.s. and the event is impossible, so the
hypothesis $k < d$ of the paper is not needed); $d$ empty (rank $< 0$ is false); $p$ empty
($\mathbf{V} = \mathbf{0}$, event needs $\mathbf{X} = \mathbf{0}$); $k$ empty is excluded by
$q < k$. R4 needs only $q \le k$. Why R4 is needed: if the output range contains the complement
of the left query span, the hidden block is invisible to the event and the event becomes a
condition on the revealed $\mathbf{P}_L\mathbf{X}$; R4 (the left responses are in general
position, by deferred decision at each step) rules it out. This case is the one place where the
paper's proof ("quotient by the exposed part") is a sentence and the formal proof a lemma.

R4 is split in three (review item 3; together 100–150 lines): R4a, the deterministic rank step
(appending a column keeps $\operatorname{rank}(\mathbf{B}\mathbf{U}) = \operatorname{rank}\mathbf{U}$
unless the new column is new for $\mathbf{U}$ but not for $\mathbf{B}\mathbf{U}$); R4b, one
probabilistic step (D2 for the Gram simulation truncated at `2 * i` rounds, a freeze, Z1: the
bad event for query $i$ has probability zero), stated through the algorithm's own queries
$\mathbf{x}_l$ = `alg.queryAt (X * Xᴴ).mulVec l` so that no truncated algorithm appears in a
statement; R4, the induction over `i ≤ q` and the transfer to the simulation's left query matrix
(the columns $\mathbf{x}_l$ and zeros, by R1a). R1a, the history-level form of R1, is split out
because R1 and R4b both use it.

### 3.7 Total variation (`ForMathlib/InformationTheory/TotalVariation.lean`; T1–T4)

| ID | Name (`InformationTheory.`) | Shape | Diff |
|---|---|---|---|
| T1 | `tvDist_nonneg` | `0 ≤ tvDist μ ν` | S |
| T2 | `tvDist_map_le` | finite measures, measurable `f`: `tvDist (μ.map f) (ν.map f) ≤ tvDist μ ν` | S |
| T3 | `one_sub_tvDist_le_measureReal_add_measureReal_compl` | probability measures, measurable `A`: `1 - tvDist μ ν ≤ μ.real A + ν.real Aᶜ` (Le Cam) | S |
| T4 | `ofReal_two_mul_tvDist_sq_le_klDiv` | probability measures: `ENNReal.ofReal (2 * tvDist μ ν ^ 2) ≤ klDiv μ ν` (Pinsker) | L |

T4 is stated in `ℝ≥0∞` against Mathlib's `klDiv` so that it holds when the divergence is infinite
(a real form would need `klDiv μ ν ≠ ⊤`). Its proof is Mathlib's data processing
`klDiv_map_le` to `Bool` plus the binary inequality, a private real lemma. Consumers: MMMW
Theorem 8 (stage B2), SAR18, Kacham–Woodruff; none in this stage (OQ6).

## 4. The first end-to-end theorem, and the next one

**In this stage: exact range recovery (R6).** It needs exactly the stage's pieces (Yao, the Gram
simulation, the adaptive two-sided Gaussian deferred decision, measure zero) and nothing else,
so it validates the model end to end at small cost (6 declarations beyond the foundations). It
is adaptive and randomized, which is the point of QUERY-MODEL-SCOPE (a).

**Next, between MMMW Theorem 8 and Shamir Theorem 1: Shamir** (stage C1, OQ8). Following the
report's reasoning (§3 Stage C1, "soonest formalizable"):

* Shamir's oracle $\mathbf{x} \mapsto (\mathbf{A}\mathbf{x}, \mathbf{U}^{\mathsf{H}}\mathbf{x})$
  costs one product on each side of $\mathbf{U}$ per call, which per-side counting (OQ9) records
  directly.
* Shamir is adaptive; MMMW's real-RAM bound is non-adaptive only (its adaptive version needs
  bit-bounded queries), so it would validate only the non-adaptive specialisation.
* Shamir reuses this stage's core (H2 for a Haar orthogonal $\mathbf{U}$, through a Gram-type
  simulation of the oracle $(\mathbf{A}\mathbf{x}, \mathbf{U}^{\mathsf{H}}\mathbf{x})$, and Y1)
  and the library's existing strength: Chebyshev minimax `isLeast_chebyshev_minimax` (Lemma 1);
  Shamir's Lemma 2 is a Kroó–Pinkus-type weighted best-approximation duality, for which the
  library's Sion-based weighted duality `exists_residualMinimax_sq_le_sum_mul_norm_sq` is the
  planned replacement (review item 6: it is not Sion in the paper); χ²
  tails (`Probability/Distributions/ChiSquare.lean`, eq. (10)). It pairs with CG/MINRES upper
  bounds already proved.
* MMMW needs T1–T4 plus a χ² divergence between Gaussian mixtures, Beta moments and a Haar
  reduction (report: ≈30 declarations), most of it information theory Mathlib lacks.

So this stage ships T1–T4 as a small ForMathlib block (OQ6) and designs H2 for Shamir. Estimated
C1 size: ≈35 declarations on top of this stage.

## 5. Consumers

* Q-, Y-lemmas: every query lower bound (C1 Shamir, C2 Zhang 4.6, C4 BN23, B2 non-adaptive LRA,
  MMMW).
* F1, F2: D2, D3, H1, H2 here; S10's "Haar unitary independent of the sketch" arguments (§10);
  Hutch++-style conditioning on one of two independent sketches.
* G1, D1–D3: Zhang et al. Lemma 4.4–4.6 (posterior overlap; D3 gives the Gaussian block), BHSW
  (square Wishart, via `gramSimulation`), the B2 non-adaptive specialisation (fixed frames).
* H1, H2: Shamir Lemmas 3–4, DEM Theorem 3.1 and 1.2, BN23 (Haar eigenvectors).
* Z1, R3, R4a, R4b, R4: the probability-zero steps of any exact-recovery bound.
* C1, C2 and the counts: every lower bound with separate left/right budgets (GN-type one-pass
  bounds, OP2 of the report; one-sided bounds via `IsOneSided`).
* T1–T4: B2 (MMMW), SAR18-type testing bounds; T2 also bounds what any output distinguishes from
  the transcript law.

## 6. Files and placement

**Superseded at the D8 move (2026-10-25, decision LOWERBOUNDS-FOLDER (a)); see §15.** The paths
below are those of the skeleton.

New in `NLAlib` (written, built under `--wfail`): `Probability/QueryModel/Basic.lean` (the
model and `gramSimulation`), `RandomMatrix/DeferredDecision.lean` (`resample`),
`ForMathlib/InformationTheory/TotalVariation.lean` (`tvDist`). Scaffold at the same paths, plus
`Probability/QueryModel/Yao.lean` and `LowRank/Optimality/RangeRecovery.lean`.

Directories (OQ1). `Probability/QueryModel/` (layer 1): the model is deterministic, but its
measurability and Yao are probability, and Krylov (layer 1) may import it for algorithm bridges;
the report's suggestion. `LowRank/Optimality/` (layer 4): the range-recovery bound is about
low-rank outputs; S10 plans `LowRank/Optimality/RotationInvariant.lean`, so the two stages share
the directory. `RandomMatrix/DeferredDecision.lean` (layer 2): one topic file for the Gaussian
and invariant-law forms (expected ≈600 lines; split into `Gaussian/` and `Haar/` files only if
it exceeds 1000).

Additions outside the stage's own files:

| Declaration | Home | Reason |
|---|---|---|
| F1, F2 | `ForMathlib/Probability/Independence/Basic.lean` | facts about independent pairs, no NLAlib vocabulary (P4); the file already holds the Tonelli and section bounds for independent pairs |
| G1 | `RandomMatrix/Gaussian/Invariance.lean` | two-sided analogue of `indepFun_conjTranspose_mul_of_hasLaw_gaussianMatrix`, fixed projectors |
| Z1 | `RandomMatrix/Gaussian/Rank.lean` | almost-sure non-degeneracy of a Gaussian matrix, next to `ae_rank_mul_eq_min_of_hasLaw_gaussianMatrix` |
| `gramSimulation`, R1a–R3 | `Probability/QueryModel/Basic.lean` | a construction on query algorithms; not in the range-recovery file because BHSW and Shamir reuse it |
| R4a | `LowRank/Optimality/RangeRecovery.lean` | linear algebra used only by R4; moves to `Matrix/` if a second consumer appears |

No flags.

## 7. Material

The prototype and the library have no algorithm, oracle or transcript notion (report §2,
"zero hits"); nothing is ported. Mathematics from: Zhang et al. 2026 (Lemmas 4.1, 4.2, §4),
BHSW 2020 (Lemma 3.4), Shamir 2026 (Lemmas 3, 4), DEM 2026 (Theorem 3.1), Tsybakov 2009
(Theorem 2.2, Lemma 2.5), Yao 1977. Reused library API: `rangeProjector` and
`measurable_rangeProjector`, `measurable_rank`, `gaussianMatrix` and
`hasLaw_mul_mul_of_hasLaw_gaussianMatrix`, `hasLaw_uncurry_of_hasLaw_gaussianMatrix`,
`hasLaw_dotProduct_of_hasLaw_gaussianVector`, `IsRightUnitarilyInvariant` and
`hasLaw_mul_const_of_isRightUnitarilyInvariant`, `haarFrame` and
`isRightUnitarilyInvariant_haarFrame`, `polarFactor` and `measurable_polarFactor`,
`ProbabilityTheory.IndepFun.measureReal_mem_le_add`, `Measurable.matrix_mulVec`.

Deliberately not reproduced: the papers' σ-field formulation with conditional laws (replaced by
identities in law, D2/H2); orthonormal queries (every statement is basis-free); a separate
non-adaptive model (`IsNonAdaptive` is a predicate on the same object, and D3 with fixed frames
is the non-adaptive deferred decision); a Wishart law (`gramSimulation` replaces it).

## 8. Mathlib search (pinned v4.33.1)

Searched `Mathlib/` for `tvDist`, `totalVariation`, `Pinsker`, `chiSquared`, `fDiv`, `LeCam`,
`oracle`, `query`, `adaptive`, `Yao`, `freezing`, `bayesRisk`, `minimaxRisk`.

* Present and used: `InformationTheory.klDiv` with `klDiv_map_le` (data processing; T4),
  `klDiv_comp_right_le`, `klDiv_compProd_eq_add` (chain rule; future χ²/KL chains);
  `ProbabilityTheory.IdentDistrib`; `ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map`;
  `HasGaussianLaw.indepFun_of_covariance_eval` (G1); `noAtoms_gaussianReal` (Z1);
  `Set.ncard` (counts); `Fin.snoc`, `Fin.castLE`.
* Present, not used (bridge deferred): `ProbabilityTheory.Kernel.traj`/`partialTraj`
  (Ionescu-Tulcea), `Kernel.compProd`, `Kernel.posterior`; `ProbabilityTheory.bayesRisk`,
  `minimaxRisk`, `bayesRisk_le_minimaxRisk` (`Probability/Decision/Risk`), which take a
  randomized estimator as a kernel. A bridge "a measurable seeded family and a seed law give a
  kernel from inputs to outputs, and Y2 is `bayesRisk ≤ minimaxRisk`" is deferred until a
  consumer states a result in that API.
* Absent: total variation distance between measures (only
  `MeasureTheory.SignedMeasure.totalVariation`, the variation of one signed measure), Le Cam,
  Pinsker, χ², Fano, Gaussian KL; any query model; the freezing lemma (Mathlib has
  `IndepFun.integral_comp`-type statements only, NLAlib its iterated-integral forms).

## 9. Names for review

`history_apply` follows `Fin.snoc_apply`-style projection names. Q3/Q4 are named by the
conclusion and the hypothesis `∀ j, g (queries …) = f (queries …)` (`forall_apply_queries_eq`).
The measurability lemmas follow Mathlib's `Measurable.comp` naming
(`IsMeasurable.measurable_transcript`). The two parts of pair queries are `right`/`left` after
the side of $\mathbf{A}$ the vector multiplies (`rightQueryMatrix`, `rightCount`: products
$\mathbf{A}\mathbf{x}$). R4b is named by its event (`queryAt_notMem_span_and_mulVec_mem_span`),
R4a by its conclusion on `Matrix.of` of a `Fin.snoc`. D2, D3, H2, R4b, R4, R5 live in
`QueryAlgorithm.IsMeasurable` (N9: the algorithm hypothesis is the first explicit argument, so
`halg.identDistrib_resample_of_hasLaw_gaussianMatrix hX hX' hXX'` reads), R6 and Y1, Y2 in
`QueryAlgorithm.IsMeasurableFamily`. H1 and H2 share the short name in different namespaces. R5
and R6 are named by the first conjunct of the event (`range_le_range_run`); the rank conjunct is
in the docstring. Z1's `measure_mul_mul_eq_eq_zero` reads "the event `N * X * F = C` has measure
`0`" (N14, N15). T3 follows the shape `1 - tvDist ≤ … + …`. To be confirmed by `check_names.py`
on the extraction before the first proof PR.

## 10. Coordination with S10 (designed in parallel, `~/nlalib-design-lb-estimators`)

Shared names, so that neither stage duplicates the other:

* **F1, F2** (`ProbabilityTheory.IndepFun.identDistrib_prodMk_of_forall_map_eq`,
  `ProbabilityTheory.IndepFun.hasLaw_prodMk_prod_of_forall_map_eq`, in
  `ForMathlib/Probability/Independence/Basic.lean`): S10's "a Haar unitary independent of the
  sketch" steps should use these rather than a local conditioning lemma.
* **H1** (`NLAlib.identDistrib_prodMk_mul_of_isRightUnitarilyInvariant`): the non-adaptive
  stabilizer form; EW's two-eigenvalue instance arguments with independent Haar $\mathbf{U}$,
  $\mathbf{V}$ may want it.
* **Directory** `LowRank/Optimality/`: this stage adds `RangeRecovery.lean`, S10 adds
  `RotationInvariant.lean`.
* **Bibliography**: this stage adds `BravermanHazanSimchowitzWoodworth2020`,
  `DerezinskiEpperlyMeyer2026`, `Shamir2026`, `Tsybakov2009`, `Yao1977`, `ZhangEtAl2026`
  (the `EtAl` form follows `ChenEtAl2025`, `MackeyEtAl2014`); S10 adds `PaleyZygmund1932` (seen
  in its worktree). The edits touch different lines of `docs/references.bib`.

## 11. Open questions for the maintainer

**OQ1. Where the query model lives** (superseded by LOWERBOUNDS-FOLDER (a), §15). (a) `NLAlib/Probability/QueryModel/` (layer 1),
`RandomMatrix/DeferredDecision.lean`, lower bounds next to their upper bounds
(`LowRank/Optimality/`, later `Krylov/LinearSystems/LowerBound.lean`,
`Estimation/Trace/LowerBound.lean`) (recommended). (b) A new top-level `NLAlib/LowerBounds/`
with everything in it (needs a CONTRIBUTING §2 amendment and a layer number; lower bounds would
then import every layer). Recommendation (a): placement by topic is the library's rule (§8
"Placement"), and the explorer collection can gather lower bounds from any module.

**OQ2. Two-sided access.** (a) The oracle `(dilation A).mulVec`: one query returns
$(\mathbf{A}\mathbf{x}, \mathbf{A}^{\mathsf{H}}\mathbf{y})$, cost one per pair (was recommended).
(b) A sum type `(n → 𝕜) ⊕ (m → 𝕜)` per query (Zhang et al.'s exact cost accounting: one product
each). (c) A product type without the dilation. **Decided (c)** (maintainer: "i want to be able
to have different numbers of left and right"): `twoSidedMulVec A`, with the per-side counts of
OQ9; §2.1.

**OQ9. Separate budgets for left and right products** (new, from the review). (a) Per-side counts
on the transcript, `rightCount τ`, `leftCount τ` (rounds with a nonzero right, left part), budgets
as hypotheses, `IsOneSided := ∀ τ, leftCount τ = 0`, one pass = `IsNonAdaptive`, rank lemmas
C1/C2 (recommended). (b) A sum-type oracle. (c) Two budgets in the type with the side schedule
fixed in advance (cannot state an adaptive choice of side). **Decided (a)**, applied to the
product oracle of OQ2 (c); §2.1 explains zero parts against `Option` sides.

**OQ3. Transcript type.** (a) `query : (i : ℕ) → (Fin i → R) → Q`, history by `Fin.snoc`
recursion, queries beyond `q` junk (recommended). (b) `query : (i : Fin q) → (Fin i → R) → Q`:
no junk, but `history` needs well-founded recursion or proofs of `i ≤ q` in data. (c)
`List R` histories: simplest recursion, but "the first `i` responses" becomes a length
invariant. Recommendation (a), the library's total-recursion style.

**OQ4. Measurability.** (a) Separate predicates `IsMeasurable`, `IsMeasurableFamily`
(recommended). (b) Fields of the structure (a "measurable query algorithm" type): every lower
bound loses a hypothesis, but expressing a library algorithm (`rsvd`, Lanczos) as a
`QueryAlgorithm` then needs measurability proofs it does not otherwise need. Recommendation (a).

**OQ5. The adaptive invariant-law form H2 in this stage.** (a) Keep H2 (H) in stage A; its
consumers are C1 (Shamir), DEM and BN23 (recommended). (b) Move H2 to stage C1 and ship only H1
here. Recommendation (a): it is the hard core the plan names for stage A, its statement is fixed
by its consumers, and the outline has a stated fallback (one-sided Haar case) if the stabilizer
randomizer fails.

**OQ6. Total variation, Le Cam, Pinsker (T1–T4).** (a) In this stage as a ForMathlib block, 5
declarations (recommended). (b) A separate ForMathlib mini-stage with χ² and Fano, when B2
(MMMW) is designed. Recommendation (a): small, independent, provable now, and B2 starts from
them; χ² and Fano wait for B2.

**OQ7. The event of range recovery.** (a) Any output $\mathbf{V} \in \mathbb{R}^{d \times p}$;
event "range $\mathbf{A}$ ⊆ range $\mathbf{V}$ and rank $\mathbf{V} < d$"; conclusion
probability zero (recommended). (b) Zhang et al.'s form: output a rank-$k$ projector
$\mathbf{P}$, event $\mathbf{A}(\mathbf{I} - \mathbf{P}) = \mathbf{0}$. Recommendation (a): it
contains (b) ($\mathbf{V} = \mathbf{P}$, rank $k < d$), covers basis outputs, and drops the
paper's $k < d$.

**OQ8. Which theorem the model is designed for next.** (a) Shamir Theorem 1 (stage C1,
adaptive, pairs with CG; reuses H2, Y1 and the library's Chebyshev/Sion results) (recommended).
(b) MMMW Theorem 8 (non-adaptive trace $\Omega(1/\varepsilon)$, pairs with Hutch++; needs χ²
between Gaussian mixtures). (c) Zhang et al. Theorem 4.6 (adaptive posterior overlap; reuses D3).
Recommendation (a), for the reasons of §4; (c) is the natural third.

## 12. Deferred, with what each needs

* Shamir Theorem 1 (C1): H2, a Gram-type simulation of $(\mathbf{A}\mathbf{x},
  \mathbf{U}^{\mathsf{H}}\mathbf{x})$, Lemma 4's Krylov structure from H2, χ² concentration,
  Chebyshev Lemma 1, Lemma 2 (Kroó–Pinkus in the paper; the library's Sion-based weighted
  duality as replacement). ≈35 declarations.
* DEM Theorems 1.1–1.2: H2; Theorem 1.2 (one-sided, $n$ products for Haar orthogonal
  $\mathbf{A}$) is the shortest consumer of H2.
* Zhang et al. Lemmas 4.4–4.6 and Theorem 4.6 (C2): D3, Haar moments
  (`RandomMatrix/Haar/Moments.lean`).
* Zero padding ([ZhangEtAl2026, Lemma 3.5]) and a general oracle-reduction lemma (one query of
  one oracle answered by one query of another): a `QueryAlgorithm.comap` with recursive decoding.
* Orthonormal queries without loss of generality (SAR18 Observation 3.1): not needed by any
  planned proof.
* Bridge to Mathlib's kernels and `bayesRisk`/`minimaxRisk` (§8).
* χ² divergence, $D_{\mathrm{KL}} \le D_{\chi^2}$, Fano, Gaussian KL formulas: with B2 (MMMW).
* Bounded-precision queries (MMMW Theorem 7).

## 13. Explorer (prepared now, added when the first `Result:` id lands; EXPLORER-TIMING (a))

Result ids introduced: `range-recovery-k-queries` (R6). Proposed ids for later `Result:` lines:
`yao-principle` (Y1/Y2 are helpers now, no id), `gaussian-deferred-decision` (D2),
`hidden-haar` (H2), `pinsker-inequality` (T4), `le-cam-two-point` (T3). When R6 is proved:

1. `topics.toml`: `"LowerBounds"` after `"Estimation"` in `order`, with
   `title = "Lower bounds (matvec model)"`,
   `blurb = "Query models, hidden-Gaussian and hidden-Haar conditioning, and lower bounds paired with the algorithms that match them."`
2. `collections.toml`: `id = "lower-bounds"`, `topic = "LowerBounds"`; groups `query-model`
   (definitions `NLAlib.QueryAlgorithm`, `NLAlib.QueryAlgorithm.transcript`,
   `NLAlib.QueryAlgorithm.IsMeasurableFamily`), `deferred-decision`
   (`gaussian-deferred-decision`, `hidden-haar` when they carry ids), `low-rank`
   (`range-recovery-k-queries`), `information` (`pinsker-inequality`, `le-cam-two-point`).
3. `rates.toml`: no row yet (R6 is an exact statement, not a rate); the first rate row is
   Shamir's $\Omega(\kappa\log(1/\varepsilon))$ paired with the CG rate (stage C1).
4. `facets.toml`: overrides for R5/R6 (`measure = "range"`, `statistic = "tail"`,
   `law = "Gaussian"`); `[sources]` short names `ZhangEtAl2026 = "ZWZ+"`, `Shamir2026 = "Sh"`,
   `DerezinskiEpperlyMeyer2026 = "DEM"`.

## 14. Proof plan for dispatch

41 targets (`~/nlalib-harness/pilot/lbA-targets.json`), waves by dependency:

* wave 0 (independent): Q1, Q5, Q6, Q8, Q9, Q10, Q11, Q12, Q13, C1, C2, R2, R3a, R3b, F1, F2, Z1,
  G1 (L), R4a, T1, T2, T3, T4 (L);
* wave 1: Q2 (Q1), Q7 (Q6), R1a (Q1), R3 (C1, R3a), Y1, Y2 (Q9, Q10), D2 (L; F1, G1, Q1, Q6,
  Q11, Q12, Q13), H1 (L; F1);
* wave 2: Q3 (Q2), R1 (R1a), D3 (D2, F2, Q6), R4b (L; D2, R1a, R2, Q1, Z1, C1, F1, Q13);
* wave 3: Q4 (Q3), D1 (Q3), H2 (H, ≈300 lines; H1, F1, Q3, Q6, Q11, Q13), R4 (R4a, R4b, R1a, Q2);
* wave 4: R5 (L; R1–R4, D1, D2, Z1);
* wave 5: R6 (Y1, R5, Q9).

The critical path is G1 → D2 → R4b → R4 → R5 → R6. L and H rows start on the stronger model
(dispatcher `--hard L,H`); D2, R4b, R5 and H2 have explicit splitting advice in their outlines.
No row has a prototype proof; every outline names the Mathlib/NLAlib lemmas it rests on.

## 15. Decision log (changes against the reviewed draft 2a1e42d)

Maintainer decisions of 2026-10-25 (`state/decisions/LB-A.json`): APPROVE (a); OQ2 (c);
OQ1, OQ3–OQ9 (a). Fable review items 1–6 applied as follows.

* **Oracle (OQ2 (c)).** New definition `twoSidedMulVec`; `(dilation A).mulVec` is no longer the
  two-sided oracle, and the query model no longer imports `Dilation`. Every statement that used
  the dilation is restated over `twoSidedMulVec`, with the query type
  `(k → 𝕜) × (d → 𝕜)` and response type `(d → 𝕜) × (k → 𝕜)` in place of `d ⊕ k → 𝕜`, and
  `rightQueryMatrix`/`leftQueryMatrix` in place of `(queryMatrix τ).toRows₂`/`.toRows₁`:
  `gramSimulation` (round `2i` is $(\mathbf{0}, \mathbf{x}_i)$, round `2i + 1`
  $(\mathbf{X}^{\mathsf{H}}\mathbf{x}_i, \mathbf{0})$), `resample`, R1, R3 (renamed
  `rank_rightQueryMatrix_gramSimulation_le`, now S via C1 and R3a), D1, D2, D3, H2, R4 (renamed
  `ae_rank_conjTranspose_mul_leftQueryMatrix_gramSimulation`). The mathematics of each is
  unchanged (the product oracle is the dilation oracle with blocks reordered), so each stays
  true; degenerate cases rechecked: `q = 0` (D2: `E = F = 1`, `resample X X' = X'`; H2: `S` fixes
  nothing, plain right invariance), empty `d`, `k`, `m`, `n` (all matrices trivial; R3, C1, C2
  bounds `0 ≤ _`), a round with a zero part (its response part is zero and its column of the
  query matrix is zero, contributing nothing to `E`, `F` or the stabilizer condition), H2's
  hypothesis on second response components holds vacuously for one-sided algorithms (they are
  zero).
* **Per-side costs (OQ9).** New definitions `rightQueryMatrix`, `leftQueryMatrix`, `rightCount`,
  `leftCount`, `IsOneSided`; new statements C1, C2 (rank ≤ count), Q11, Q12 (measurability of
  the two query matrices, used by D2 and H2 where Q8 was), R3a, R3b (the Gram simulation makes
  `q` products on each side). `IsOneSided` moves from §12 (deferred) into scope.
* **`IsMeasurable`, `IsMeasurableFamily` (review item 5).** `measurable_query` now quantifies over
  `i < q` (was every `i`), matching `IsNonAdaptive`. This weakens the predicates (more algorithms
  are measurable), so every lower bound becomes stronger; no statement relied on junk queries.
  R4b, which uses `alg.queryAt … i`, carries `i < q`.
* **R1 split.** New R1a `history_gramSimulation` (now `gramDecode_history_gramSimulation`, T9-GRAM) (M, the history-level identity); R1 becomes S.
* **R4 split (review item 3).** New R4a `rank_mul_of_snoc_eq_rank_of_snoc` (M) and R4b
  `IsMeasurable.measure_queryAt_notMem_span_and_mulVec_mem_span_eq_zero` (L); R4 is the M
  assembly, its statement changed only by the oracle (above).
* **H2 outline (review item 2)** rewritten: (i) single left query to Haar on the stabilizer,
  (ii) Haar induction, (iii) general $\nu$ via $\mathbf{X} \overset{d}{=} \mathbf{Y}\mathbf{O}$;
  randomizer `1` off the full-rank set. Statement unchanged except for the oracle.
* **H1 (review item 4).** Not changed: adding `[Fintype p]` trips the unused-instance linter
  (the statement does not need it); the outline now uses the column span of $\mathbf{V}$, which
  needs no finiteness of `p`.
* **Citations (review item 6).** D2, D3 note Zhang et al.'s $\mathcal{N}(0, 1/d)$ entries,
  orthonormal queries and $q \le s$ against unit variance, any queries, any `q` here; §4 and §12
  attribute Shamir's Lemma 2 to Kroó–Pinkus, with the library's Sion duality as the planned
  replacement.
* **Second Fable check (2026-10-25, of this revision).** All restated and new statements true.
  Applied: H2 outline rebuilt on the Gaussian polar stabilizer randomizer (fixed types) with a
  pair-round lemma, re-rated ≈300 lines; new definition `QueryAlgorithm.truncate` (with the
  proved `history_truncate`, `transcript_truncate`) and statement Q13 `IsMeasurable.truncate`,
  used by D2, R4b, H2 instead of each rebuilding `⟨alg.query, fun _ => ()⟩`; R4b's `F ≠ 0` via
  `finrank_span_le_card`; R1a outline (pointwise strong induction, 50 lines); D2 cites G1's
  hypothesis order; "at most `q` products" in `gramSimulation`; H2's `∀ τ` hypotheses explained.
* Counts: 31 → 41 statements (S 13 → 22, M 11 → 12, L 6, H 1), 13 → 20 definitions.
* **Placement at the D8 move (2026-10-25, maintainer decision LOWERBOUNDS-FOLDER (a)).** OQ1 (a)
  is superseded: lower bounds form the top layer `NLAlib/LowerBounds/` (CONTRIBUTING §2, layer 5)
  with topic subfolders, and a lemma they need that is not itself a lower bound stays in its topic
  folder. The query model is not in `Probability/` (layer 1) and nothing below `LowerBounds/` may
  import it, so "Krylov (layer 1) may import it for algorithm bridges" (§6) no longer holds: an
  algorithm bridge (`rsvd`, Lanczos as a `QueryAlgorithm`) lives in `LowerBounds/` too. Files:

  | File | Contents |
  |---|---|
  | `LowerBounds/QueryModel/Basic.lean` | the definitions of §2.1–2.2, Q1–Q13, C1–C2, R1a–R3 |
  | `LowerBounds/QueryModel/Yao.lean` | Y1, Y2 |
  | `LowerBounds/QueryModel/DeferredDecision.lean` | `resample`, D1–D3 |
  | `LowerBounds/QueryModel/HiddenHaar.lean` | H2 |
  | `LowerBounds/LowRank/RangeRecovery.lean` | R4b, R4–R6 (R4a until RANK-STEP-HOME, below) |
  | `RandomMatrix/Haar/Stabilizer.lean` (new) | H1: a fact about invariant laws, used outside query models |
  | `RandomMatrix/Gaussian/{Invariance,Rank}.lean`, `ForMathlib/…` | G1, Z1, F1–F2, T1–T4, as in §6 |

  The scaffold file `RandomMatrix/DeferredDecision.lean` (1738 lines, over the F10 ceiling) was
  split by topic into the Gaussian (D1–D3), non-adaptive (H1) and adaptive (H2) files. R4a stays
  with its only consumer (decision card RANK-STEP-HOME in `Review-LBA.json`).
* **Review-LBA decisions (2026-10-26, `state/decisions/Review-LBA.json`).**
  * UNUSED-HE1 (a): G1 no longer takes `hE₁ : IsStarProjection E₁`; only `E₁ * E₂ = E₂` is used
    on the left. The statement is weaker in its hypotheses, hence stronger.
  * T9-GRAM (a): new definition `QueryAlgorithm.gramDecode` (the first components of the odd
    responses of a `2 * i`-round history), used by `gramSimulation`'s query and output. R1a is
    restated as `gramDecode ((alg.gramSimulation k).history (twoSidedMulVec X) (2 * i)) =
    alg.history (X * Xᴴ).mulVec i`, definitionally the old statement without the `Fin` literal's
    proof term; the T9 ratchet entry is removed. By N2 (the conclusion starts with `gramDecode`) R1a
    is renamed `gramDecode_history_gramSimulation` (was `history_gramSimulation`).
  * RANK-STEP-HOME (a): R4a moves to `ForMathlib/LinearAlgebra/Matrix/Rank.lean`, next to
    `Matrix.rank_mul_eq_iff_injOn`, renamed `Matrix.rank_mul_of_snoc_eq_rank_of_snoc` (statement
    unchanged), with its private finrank helper. R4's call site uses the new name.
  * PUBLIC-HELPERS (a), with Fable's H2 randomizer item: public now are
    `MeasureTheory.Measure.map_prod_eq_of_forall_map_eq` (freezing for a product measure; F1 now
    uses it, the private copies in ForMathlib Independence and HiddenHaar are gone),
    `Measurable.finSnoc` (new `ForMathlib/MeasureTheory/MeasurableSpace/Pi.lean`),
    `Measurable.twoSidedMulVec`, `QueryAlgorithm.IsMeasurable.measurable_history`,
    `QueryAlgorithm.queryAt_gramSimulation_two_mul(_add_one)` (over 𝕜, in `QueryModel/Basic`),
    `QueryAlgorithm.IsMeasurable.measurable_resample` (`DeferredDecision`); `@[fun_prop]` on
    `Measurable.matrix_mul`, `Measurable.matrix_mulVec`. The copies in DeferredDecision,
    HiddenHaar, Stabilizer and RangeRecovery are deleted. For Shamir Lemma 4 the smaller option was
    taken: a public corollary of H2,
    `QueryAlgorithm.IsMeasurable.identDistrib_prodMk_mul_of_isRightUnitarilyInvariant_of_indepFun`,
    with a stabilizer `S τ z` depending on an independent `Z` (F1 + H2); `stabRand` stays private.
