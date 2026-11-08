# Hardening the model of computation

Status (2026-11-08): approved (sheet `HARDENING.json`, all (a)); Stages 0 to 2b carried out,
with the registry entries pending the maintainer's re-pin; the `Instance:` rule, `scripts/Witnesses.lean`
and Stage 3 are not done. Per-item status in §11. Proposal text: Proposed 2026-11-07; revised the same day after `reports/Review-Fable-Hardening.md` (approve with
blocking edits B1–B4, S2-a, S2-b and five uncovered items, all addressed below). Written after the adversarial audit `reports/Audit-Fable-Corrections.md` (harness), §3.3,
§3.4 and §4. No library file, target, tree, check or registry entry is changed by this note. It
proposes theorems and model changes for the library, and exact patches for the maintainer-owned
checks. Those patches are in the harness file `reports/Hardening-maintainer-patches.diff` and are
summarised in §8.

The maintainer's principle governs every item: "we are not 'fixing' things here by ensuring we
do not break things. If there are any vulnerabilities we need to report it and fix it." So each
item is a change to the model or to the checks, together with a regression test. None of them
is a convention that the existing proofs happen to satisfy.

The maintainer asked: "why can the model not block these itself?". The answer is §1. Most of
the guarantees already follow from the model's types and its run, or can follow from one general
theorem; fixtures are only regression tests for them. §1.4 lists what no theorem about the
interpreter can catch, and the lint or meta-theorem that covers each of those risks.

Branch state the note is written against: `origin/main` 5cce6739 (no `bindIdx`, no
`ScalarSem.toNat`), and, for the dynamic constructs, `integrate/compdyn-s2` 1cb63270 (the S2
model: `bindIdx`, `toNat`, `IsExactToNat`, the SIGN/DEFLATE/EIGH targets, unregistered).

## 0. Verdicts

| # | Vulnerability (audit §4) | Proposed fix | Re-pin | Effort |
|---|---|---|---|---|
| G | (new) no general guarantee: each cheat needs its own fixture | **non-interference theorem** `exec_eq_of_agreeOn` (over `Stmt`, transferred to `FStmt`) and its model corollaries, pinned by hash with the models (§1.1, §1.4). It generalises the existing no-query lemma `exec_eq_of_exec_eq_some_of_cnt_load_le`. Cost soundness is already a theorem (§1.2) | none (new theorems; `[[model]]` tables) | M |
| 1 | HIGH: no fixtures for `kcall`, `bindIdx`, `toNat`, `Dist.uniform` or the rounded models | 8 fixtures on main (K1–K4, U1, U2, R1, and the trap H1), 5 on the S2 model (B1, B2, B3, B3', B3b), all typechecked. Stage 2b rewrites K1–K3, U2, R1, B2, B3 and `FixVacuousRounded` (§2.1) | none | S (done); S at Stage 2b |
| 2 | HIGH: inner-hypothesis vacuity is undetected | a `witness` field for every target, checked by `Targets.lean` against a library companion `M.NonVacuous`. The companion is pinned by hash in a `[[model]]` table. Headline theorems get an `Instance:` rule plus a ratchet lint (§2.2) | registry fields and tables only (target hashes unchanged) | M |
| 3 | MEDIUM: the exactness contracts are optional | `IsIndexExactSem dec B` becomes a hypothesis of `MatrixFreeRoundedProb` itself. Lint item 10 forces the model's `dec` on every contract (§2.3) | with the S2 merge | S |
| 4 | MEDIUM: the rounded probabilistic model certifies no cost | `cost` and `mem` arguments, and `RunsWithin` under the standard charge inside the event. A closed-form-cost lint that follows definitions transitively (§2.4) | with the S2 merge | S for the model, M for each target |
| 5 | **CRITICAL** (raised from MEDIUM): the agent host is logged in as the maintainer (a fine-grained PAT) and pushes with write deploy keys, so every review rule is self-satisfiable; the approval SHA is self-service | **credentials first**: revoke the PAT on the host, give agents a machine account, make the deploy keys read-only or delete them. Then the rulesets (no direct push to main, one code-owner review, the required checks, unattributed-changes approval kept, tags locked) and a required check that `docs/targets.approved` changes only in a verified commit by `tchen01` (§2.5) | none | S (maintainer, Stage 0) |
| 6a | LOW: an output handle can be reused as popped scratch | `st₀.store.size = b` in `Prog.RunsWithin` (§2.6) | all 11 registered targets (hash only), folded into the S2 re-pin | S |
| 6b | LOW: silent clamping | `bindIdx` fails when the value exceeds its bound, and `toNat` fails below `0` (strict on both sides), decided before S2 registers its trees (§2.6) | none on main (S2 trees not registered yet) | S, plus S–M for the EIGH proofs |

## 1. General guarantees first

### 1.1 (a) Non-interference

**Statement.** The run of a first-order statement depends on the data-carrying parts of an
interpretation (the oracles, the kernels, the tape and the read-only data) only through the
answers to the queries the run actually makes. It depends on the declared inputs only through
the store. Exact Lean, typechecked with the proof `sorry`'d against `integrate/compdyn-s2`
(scratch `NI.lean`, which covers `kcall`, `bindIdx`, `draw` and therefore `Dist.uniform`):

```lean
/-- A query a run makes of the parts of an interpretation that carry data. -/
inductive Query (ι K : Type) where
  | oracle (o : ι) (cols : ℕ) (X : Array K)            -- `apply`: the block read
  | kernel (o : ι) (ds : List ℕ) (xs : List (Array K))  -- `kcall`: the blocks read
  | draw (d : Dist) (i : ℕ)                             -- `draw`: the tape position (any `Dist`)
  | rom (i : ℕ)                                         -- `rom`

/-- The same answers on the queries `S`. -/
def Interp.AgreeOn (I I' : Interp P ι K C) (S : Set (Query ι K)) : Prop :=
  (∀ o c X, .oracle o c X ∈ S → I'.oracle o c X = I.oracle o c X) ∧
  (∀ o ds xs, .kernel o ds xs ∈ S → I'.kernel o ds xs = I.kernel o ds xs) ∧
  (∀ d i, .draw d i ∈ S → I'.tape d i = I.tape d i) ∧
  (∀ i, .rom i ∈ S → I'.rom i = I.rom i)

/-- The same data-free part. -/
structure Interp.SameShape (I I' : Interp P ι K C) : Prop where
  sem : I'.sem = I.sem
  charge : I'.charge = I.charge
  height : I'.height = I.height
  width : I'.width = I.width
  kshape : I'.kshape = I.kshape
  romSize : I'.romSize = I.romSize  -- not read by `exec`; read by `RunsWithin`'s memory clause

/-- The queries of the run of `s` under `I` from `st`, recorded along `FStmt.exec`
(definition by structural recursion mirroring the run, 60 lines: `seq` adds the queries of the
second part from the state after the first, `loop`/`whileFuel` fold over the iterations,
`bindIdx` recurses at the clamped value, `kcall` records `(o, ds, readBlocks …)` when the reads
succeed). -/
def FStmt.queries (I : Interp P ι K C) : FStmt P ι nb ni → (Fin nb → ℕ) → (Fin ni → ℕ) →
    St P K C → Set (Query ι K)

theorem FStmt.exec_eq_of_agreeOn {I I' : Interp P ι K C} (hI : I.SameShape I')
    (s : FStmt P ι nb ni) (ρB ρI st) (h : I.AgreeOn I' (s.queries I ρB ρI st)) :
    s.exec I' ρB ρI st = s.exec I ρB ρI st

theorem Prog.exec_eq_of_agreeOn {I I' : Interp P ι K C} (hI : I.SameShape I')
    (prog : Prog P ι r b) (N n st)
    (h : I.AgreeOn I' (FStmt.queries I prog (fun j => j) (Fin.cons N n) st)) :
    prog.exec I' N n st = prog.exec I N n st
```

**What exists already.** The no-query end of this theorem is in the library, for the oracle only:
`exec_eq_of_exec_eq_some_of_cnt_load_le` (`Exec.lean:792`; a run whose load counts do not grow is
the same run under any other oracle), its program form `Prog.exec_eq_of_exec_eq_some_of_cnt_load_le`
(`FirstOrder.lean:304`), and `exec_exactInterp_eq_of_exec_eq_some_of_cnt_load_le` (`Model.lean:246`,
any other matrix). That lemma already proves `post_of_noQuery` for the oracle today. What is new here:
the query set, so that a run with queries is covered; the kernels, tape and rom; and the
per-model corollaries. Following that lemma, the induction is best done over `Stmt P ι ℕ ℕ` and
`exec`, where there is no `ρB`/`ρI`, and transferred to `FStmt` by `FStmt.exec_eq_exec_toStmt`. The
statement is given over `FStmt` above, because that is the form the targets use.

**Proof sketch.** Induction on `s`, generalising `ρB`, `ρI` and `st` (no environments over `Stmt`). Leaves: `instr` uses only
`I.sem`, plus `I.tape d (st.pos d)` for a draw, which is the query `.draw d (st.pos d)`. `apply`
uses `I.height` (same shape), then `I.oracle o cols X` on the block read, which is the recorded
query. `rom` is the same. `kcall` uses `I.kshape` (same shape) and `I.kernel o ds xs` on the
blocks read, which is the recorded query; `kcallStore`'s alias check depends only on the shape.
`bindIdx`: `toNatStep` uses `I.sem` and `I.charge`, then the induction hypothesis at the clamped
value. Nodes: `seq` takes the induction hypothesis on `s`; its result rewrites the state for
`t`, whose queries are in the recorded set. `alloc` and `named` take the induction hypothesis.
`ite` uses `cmpStep` (semantics and charge only), then the branch. `loop` and `whileFuel` need an
auxiliary lemma: a `List.foldlM` of runs equals the corresponding fold under `I'`, by induction
on the list, with the accumulated query set of the definition. The charge enters only the counts,
so the theorem also holds for counts and memory: the whole state is equal.

**Probabilistic form.** For each $\omega$, if $I(\omega)$ and $I'(\omega)$ agree on the queries
of the run under $I(\omega)$, the two runs are equal. With `romSize` equal (in `SameShape`), so is
`RunsWithin`'s memory clause. So the events `{ω | ¬ RunsWithin …}` of
`MatrixFreeProb` / `MatrixFreeRoundedProb` coincide, and so do their probabilities and the law
of the output. It is a three-line corollary.

**Model corollaries (meta-theorems on the models).** One per model, S each:

```lean
/-- Under `MatrixFree`, the postcondition holds of a single final state for every pair of
matrices whose oracle answers agree on the queries of the run. -/
theorem MatrixFree.post_of_agreeOn (h : MatrixFree p prog valid X inputs cost mem post)
    (hv : valid N n) (x : X N n) (A A' : Matrix (Fin N) (Fin N) 𝕜) (ξ)
    (hA : (exactInterp (fun _ => A) ξ).AgreeOn (exactInterp (fun _ => A') ξ)
      (FStmt.queries (exactInterp (fun _ => A) ξ) prog _ (Fin.cons N n) (inputState …))) :
    ∃ st, post N n x A ξ st ∧ post N n x A' ξ st
-- and `MatrixFree.post_of_noQuery`: if the run makes no oracle query, `post` holds of one
-- state for all A, so no zero-query program computes a non-constant function of A
-- (`leakTree`, `copyTree`, `drawTree` become one-line instances).
```

The corollaries are not checked for existence only. Each model's `[[model]]` table in
`docs/targets.toml` pins the closure hash of the model together with its companions
(`M.NonVacuous` from Stage 1, `M.post_of_agreeOn` from Stage 2b; lint item 9). So restating a
corollary as `True`, or weakening it, changes a pinned hash and needs the maintainer's approval
(§1.4).

**Effort.** M: `queries` is 60 lines; the induction is 250 to 350 lines, most of it the two fold
lemmas; the corollaries are 40 lines each. Placement: `NLAlib/Computation/NonInterference.lean`
(new), importing `FirstOrder`, with the model corollaries in `Model.lean` and `Tape.lean`. Lands
on main after the S2 model merge (it must cover `bindIdx`). A main-only version without
`bindIdx` is possible but would be redone.

**What it subsumes.** Fixtures stay as regression tests in any case. The table says which ones
become instances of a general theorem:

| Fixture | Subsumed by | Why / why not |
|---|---|---|
| `not_matrixFree_leakTree`, `copyTree`, `drawTree` (existing) | **yes**: `MatrixFree.post_of_noQuery` | each run makes no oracle query and claims the trace, which is not determined |
| `not_matrixFreeProb_drawTree` (existing) | partly | non-interference gives independence from A; the bound $\ge 1/2$ needs the fixed tape law (a fact about the definition, `matrixFreeProb_iff`) |
| K1 kernel reads outside its block | **yes** | the kernel's answer is a function of the recorded blocks only |
| K2 aliased kernel call | no | a failure rule of `kcallStore`, not an information flow; covered by the lemma `kcallStore_eq_none_of_overlap` (S) plus the fixture |
| K3 exact-kernel-only, R1 exact-arithmetic-only | no | these are about quantification over every interpretation that meets the contract (I6), which is the shape of the model definitions (§1.4) |
| K4, B1 cost charged | **yes**, by §1.2 | the count is produced by the run |
| U1, U2 uniform leak | partly | non-interference says the draw is a function of the tape only; that it equals the input with probability 0 needs the uniform law to be non-atomic |
| B2 clamped index | by construction (§1.3) | `min k bound` is in the run |
| B3 inexact `toNat` | no | this is about the contracts; §2.3 makes them part of the model |
| H1 handle reuse | no | handle liveness; §2.6 |

### 1.2 (b) Cost soundness: already true by construction, plus one existing theorem

*Dynamic counts.* The interpreter is the definition of execution, and it increments `st.cnt`
itself at every leaf: `instr` by `I.charge i.kind` (`litIdx` counts as `lit`), `apply` by
`load + cols • matvec`, `rom`, `kcall` once at `.kcall p o (dims.map eval)`, and every test of
`ite`/`whileFuel` (`cmpStep`). On S2, `bindIdx` is charged once as `.toNat p` (`toNatStep`). The
structural nodes (`seq`, `alloc`, `loop`, `named`, `skip`) charge nothing; memory is tracked by
`cur`/`peak`. The models fix the charge (`exactInterp`, `storedInterp`: `Finsupp.single k 1`), so
`st.cnt k` is the number of executed leaves of kind `k`. `RunsWithin`'s
`st.cnt ≤ st₀.cnt + c` then bounds what was executed. There is no second notion of "operations
executed" for a theorem to compare against, so none is needed. A regression test per constructor
(K4 for `kcall`, B1 for `bindIdx`) catches an edit of `exec` that drops a charge.

*Static counts.* `Prog.bounds_staticCost_of_exec_eq_some` (`StaticCost.lean`) already proves that
the static summary bounds every successful run, for every constructor including `kcall`; S2
extends it to `bindIdx` by the supremum over `[0, bound]`.

*What is not covered, deliberately or not:*
1. A `kcall` is counted as calls times dimensions, not flops; a flop total is
   `Finsupp.weight w` with a $w$ the target chooses. Choosing the weight is the target's
   responsibility (review).
2. `IExp` arithmetic, loop bookkeeping and branches on indices are uncounted, the word-RAM
   convention (DynamicPrograms §3, I7).
3. **The rounded models certify no cost at all**: their `I` is quantified with an arbitrary
   charge. This is vulnerability 4, §2.4.
4. A cost stated as "whatever the tree costs" (`cost := prog.staticCost …`) is true and says
   nothing. §1.4 adds a lint for it.

### 1.3 (c) Guarantees enforced by construction (no theorem needed)

| Guarantee | Enforced by |
|---|---|
| a handle cannot be forged or computed | PHOAS `VB` in `Stmt`; `Fin nb` de Bruijn handles in `FStmt` (a handle out of scope is a type error) |
| data never become indices, except through `bindIdx` | `IExp` has no cell constructor; `bindIdx` binds `min k bound` with `bound : IExp` over sizes and outer indices (I7) |
| no Lean function in a tree | `FStmt` constructors take naturals, rationals, strings, `Fin`s, `IExp`/`Cell`/`Instr`/`Arg` and subtrees only; the registry hashes the constructor normal form and the kernel checks it (I1, E3 item 3) |
| the tree is fixed before the data | the tree is an argument of the model, which quantifies the sizes, inputs, matrix, tape and interpretation afterwards; frozen by the closure hash of the model definition |
| contracts and tape contracts cannot see the input | `Contracts : ℕ → (Fin r → ℕ) → Interp → Prop` and `ρOK : (Dist → ℕ → ℝ → K) → Prop` have no argument for `x` (types) |
| the tape law cannot depend on the data | `tapeLaw` is a constant inside `MatrixFreeProb`/`MatrixFreeRoundedProb` |
| a kernel sees only its blocks | `Interp.kernel : ι → List ℕ → List (Array K) → Option …` gets the read blocks, not the store |
| aliased oracle and kernel calls fail | `exec`'s `apply` disjointness test; `kcallStore`'s `Pairwise`/cross disjointness test |
| uninitialised reads fail | `alloc` pushes `none` cells; `Store.read` joins the option |
| counts are what ran | §1.2 |
| memory is freed | `Prog.cur_eq_of_exec_eq_some`, `shape_eq_of_exec_eq_some` (theorems over the run) |

### 1.4 What only fixtures, lints or review can catch, and the lint for each

| Risk | Why no interpreter theorem catches it | Proposed lint or meta-theorem |
|---|---|---|
| **quantifier order / shape of a model definition** (e.g. a new model that binds `A` before the tree, or a hypothesis on the tape law) | it is the definition itself | (i) every model in `Targets.lean`'s `models` has a `[[model]]` table (lint item 9) that pins **by closure hash** the model, its non-vacuity companion `M.NonVacuous` and (from Stage 2b) its non-interference corollary `M.post_of_agreeOn`. The corollary's statement is reviewed once and frozen, and its proof breaks if the order changes. (ii) the closure hash of every target freezes the reviewed definitions; (iii) fixtures as regression |
| **vacuous hypotheses** (outer or inner) | a vacuous target is a true theorem | the witness lint, §2.2 |
| **inadequate postcondition** (`good` claims less than the docstring) | it is a specification question | review of the printed statement (the registry prints it); no lint possible |
| **unrealistic or degenerate contracts** (a kernel contract only an oracle could meet; a witness at $u = 0$ with exact kernels; a decoding at which the clauses disagree) | contracts are data-independent by type but otherwise free | the witness lint detects unsatisfiable hypotheses, not degenerate ones. So the registry records the semantics a witness uses (`witness_sem = "gridSem t, exactMM, exactQR, ρ = roundNearest"`, reviewed with the witness), and the `Instance:` rule asks the same of headline theorems. Lint item 10 forces one decoding: every contract predicate in a rounded target's arguments takes a decoding that mentions the model's `dec` |
| **uninformative cost** (`cost := staticCost …`, also behind a definition) | it is true | lint item 8 (`costErrors`): neither `cost`/`mem` nor the postcondition (`good`/`post`, where a sharp count clause may be stated), nor any library or current-file definition they unfold to (transitively, `unfoldsTo`), mentions a registered tree or `staticCost` |
| **precomputed inputs** | data of the prover's | existing lint item 5 (Q5) |
| **unregistered rounded results** | E3 item 2 exempts rounded program theorems from registration (`isRoundedClaim`), so a `Result:` theorem under `MatrixFreeRoundedProb` with vacuous `Contracts` is neither registered nor witnessed | extend item 7 to rounded claims: a rounded `Result:` theorem carries `Witness: <name>` in its docstring, checked as for targets (Stage 3, §9) |
| **self-approval** | process | §2.5 |
| **the NumPy emitter** | trusted, outside the guarantees (`Computation.md`, "Final audits") | out of scope |

## 2. The six vulnerabilities

### 2.1 HIGH: access-model fixtures (vulnerability 1)

The current state: `scripts/AccessModelFixtures.lean` (CI step "Access-model fixtures
(cheating realisations are false as instances)", `.github/workflows/ci.yml:36–37`) has
`litTree`, `leakTree`, `copyTree` and `drawTree` under `MatrixFree`/`MatrixFreeProb` only.
**`scripts/AccessModelFixtures.lean` is not in `.github/CODEOWNERS`** (only `Targets`,
`Audit`, `Programs`, `Replay` and their fixtures are), so the file the CI step rests on is
editable without the maintainer. §2.5 adds it.

New fixtures. Each one is a theorem `¬ Model … cheatTree …`, and each was typechecked: Part A
against `origin/main` (own build of `design/model-hardening`, the whole file via
`import NLAlib`), Part B against `integrate/compdyn-s2`.

Part A (main, apply now; appended to `scripts/AccessModelFixtures.lean`):

| Id | Theorem | Cheat ruled out |
|---|---|---|
| K1 | `not_matrixFreeRoundedProb_kcallTree` | a kernel reads outside its blocks: with the copy kernel on cell 0, the program claims cell 1. False at input `(0, 1)` |
| K2 | `not_matrixFreeRoundedProb_kcallAliasTree` | an aliased (in-place) kernel call: `kcallStore` rejects output/input overlap, so the run fails for every ω and the failure probability is 1 |
| K3 | `not_matrixFreeRoundedProb_kcallTree_exactKernel` | a program correct only for the exact kernel (the fixture promised by DynamicPrograms §3): the contract allows relative error 1/4, and the kernel `2v·5/4` refutes "output = 2x" |
| K4 | `not_runsWithin_kcallTree_zero` | cost undercounting for a kernel call: a budget of 0 is false, because the run charges `.kcall () () []` once |
| U1 | `not_matrixFreeProb_uniformTree` | a uniform draw used to leak the input: under `tapeLaw` the first uniform draw equals `0` with probability 0 (`measureReal_uniform_eq`), so the failure probability is 1 |
| U2 | `not_matrixFreeRoundedProb_uniformTree` | the same in the rounded model with the strongest tape contract (`ρ = id`): `ρOK` and `Contracts` cannot mention the input |
| R1 | `not_matrixFreeRoundedProb_thirdTree` | a program correct only under exact arithmetic: `upLitSem` (literals scaled by 3/2) meets `IsRelErrSem` at $u = 1/2$, so "cell = 1/3" is false |
| H1 | `runsWithin_scratchTree_emptySt` | **the handle-reuse trap, a positive theorem today**: from the empty state the program's scratch takes the declared output's handle, and the run succeeds with the output unreadable. Stage 2b flips it to `¬ …` (§2.6), so that the change shows as a diff |

Part B (S2 model, apply with the S2 merge, Stage 2a; a new file
`scripts/AccessModelFixturesDynamic.lean` and a CI step):

| Id | Theorem | Cheat ruled out |
|---|---|---|
| B1 | `not_matrixFree_prodTree` | `bindIdx` skipping its cost: a product of two data through two binders and `litIdx` is charged two `toNat` (the fixture promised by DynamicPrograms §3) |
| B2 | `not_matrixFree_idxCopyTree` | unbounded data leaking into indices: the binder clamps to its static bound, so copying every natural input through an index is false (input 1, bound 0) |
| B3 | `not_matrixFreeRoundedProb_sizedTree` | a `toNat` that is not exact but sizes a buffer: `IsRelErrSem` does not constrain `toNat`, so with `toNat = ⌊·⌋₊ − 1` the write at index `n − 1` of a buffer of the converted size fails. False *by failure*. This is the motivation for §2.3, and §2.3 kills it: once `IsIndexExactSem` is a hypothesis of the model, `lowToNatSem` is excluded and the target becomes true. At Stage 2b B3 is therefore replaced by B3b |
| B3b | `not_isExactToNat_lowToNatSem` | the replacement of B3 at Stage 2b: the inexact conversion is outside the model (`¬ IsExactToNat id lowToNatSem`). Trivial, and stays provable |
| B3' | `not_matrixFreeRoundedProb_litSizedTree` | the provable successor of B3's idea: **the exactness bound `B` must cover the sizes the program writes**. With exact literals only up to `0` and an exact conversion (`halfLitSem`: nonzero literals halved, relative error 1/2), a size `2` written by `litIdx` reads back as `1`, and the write into the buffer of that size fails. It survives Stage 2b with the clauses moved into the model's `B := 0` |

The vacuity demonstration V1 (a rounded target with `Contracts := False` holds of every program)
is not an access-model fixture: it is a Targets fixture (`FixVacuousRounded`), detected by
item 7 (§2.2).

How strong each fixture is (from the review). K1 discriminates weakly: a regression that hands
the kernel a longer block makes `writeBlocks` fail on length, and the `¬` still holds, by failure.
It catches only a regression that shifts the block read; its docstring should say so. K2, B3 and
B3' are false by failure (the run is `none`), K3 sits on the boundary of its contract (equality in
`≤`), and none is vacuous.

**Stage 2b rewrites (scheduled, S).** The model arguments of §2.3/§2.4 (`dec B cost mem` and the
`IsIndexExactSem` hypothesis) and strict `bindIdx` (§2.6b) break these fixtures as written:

| Fixture | Change at Stage 2b |
|---|---|
| K1, K2, K3, U2, R1 | pass `dec := fun _ x => x`, `B := fun _ _ => 0`, `cost`/`mem` (any closed form, e.g. `0`; the event becomes `RunsWithin`, the proofs keep their shape, plus a `cnt`/`peak` goal discharged by `simp`); discharge `IsIndexExactSem` with `isIndexExactSem_exactSem 0`, and for `upLitSem` with `⟨by simp [upLitSem], by simp [upLitSem, exactSem]⟩` (its literal 0 is exact) |
| B2 | strict `bindIdx`: input 1 above bound 0 now fails the run; the proof becomes "false by failure" (the `subst hrun` step is replaced by `simp at hrun`). The property tested changes from "clamped" to "over the bound fails". The docstring changes with it |
| B3 | replaced by B3b (already in Part B) |
| B3' | its clauses move into the model (`B := fun _ _ => 0`); the proof is unchanged otherwise |
| H1 | flips to `¬ scratchTree.RunsWithin … emptySt …` (proof: `rintro ⟨hsize, -⟩; simp [emptySt, inputState] at hsize`) |
| `FixVacuousRounded` (Targets, Part C) | new arity: pass `dec B cost mem` |

Effect: none on proofs or registered targets. Effort: done (S); the Stage 2b rewrite is S.

### 2.2 HIGH: non-vacuity witnesses (vulnerability 2)

**Registered targets: a lint (in `scripts/Targets.lean`, maintainer-owned).** The checks:

* The library gets, for each model `M` in `models`, a companion `M.NonVacuous` with exactly `M`'s
  binders followed by `N₀ : ℕ` (§5). For the exact models it is
  `∃ N n, N₀ ≤ N ∧ valid N n ∧ Nonempty (X N n)`. For `MatrixFreeRoundedProb` it is
  `∃ N n, N₀ ≤ N ∧ valid N n ∧ ∃ x, pre N n x ∧ ∃ I ρ, Contracts N n I ∧ ρOK ρ`.
* Each `[[target]]` gets `witness = "<theorem>"`. **Item 7** of `Targets.lean` computes, from the
  target `T := ∀ xs, M a₁ … aₖ`, the expected type `∀ N₀, ∃ xs, M.NonVacuous a₁ … aₖ N₀`
  (`expectedWitness`, Meta: `forallTelescope`, then `mkAppN`, then one `Exists` per outer binder).
  It requires the witness to be a theorem of that type up to reducible unfolding
  (`witnessError`). The mechanism was tested in scratch (`Witness.lean`): a correct witness is
  accepted, and the Targets fixtures reject a witness at a single size, the target's own proof
  and a missing witness.
* Why "for every $N_0$": a precondition satisfiable only at $N = 0$ or $N = 1$ (a statement about
  empty matrices) is the typical vacuity. Quantifying $N_0$ outside the outer binders lets the
  witness pick a finer format ($u = 2^{-t}$, $t$ large) for each size, as the precision
  hypotheses need.
* The witness's quality (a realistic semantics, $u > 0$, kernels that really round) is checked by
  review: the lint detects unsatisfiable hypotheses, not degenerate ones (a rounded target with
  `u` as an outer binder is witnessed at `u = 0`, `I := exactInterp`). So each `[[target]]` also
  records `witness_sem` (the semantics, kernels and tape rounding the witness uses), and the
  reviewer sees it without opening the proof. The audit's §2.1 flag (the bounded-format instance
  has exact `mm`) is the example.
* **The companions are pinned (item 9).** `M.NonVacuous` is not in any target's closure, so an
  edit to `fun … => True` would make every witness trivial. Each model has a `[[model]]` table
  (`name`, `companions`, `hash`) whose hash is that of the closures of the model and of its
  companions. `--update` rewrites it; the maintainer approves it. Fixtures: a tampered model hash, a
  missing table and a missing companion are each detected.
* **A pitfall, now an error.** A companion declared under the model's `variable` line drops the
  instance binders its body does not use (`[RCLike 𝕜]`, `[DecidableEq P]`). Then `mkAppN`
  mis-assigns the arguments. `expectedWitness` therefore runs `Meta.check` on the built type and
  reports "the binders of `M.NonVacuous` differ from those of `M`". The companions spell their
  binders out (§5).

Witnesses to write: the 11 registered exact targets (S each: `N₀`, a size, `⟨()⟩`). The three
S2 targets: M each, at `gridSem t` with `dec = roundNearest ∘ t`, `exactMM`/`exactQR`,
`ρ = roundNearest`, an identity-like Hermitian input and $t$ chosen from $N_0$. They need
`isExactIntLit_gridSem'` (proved in scratch, §5), `isExactToNat_gridSem` and `mulShrinks_gridSem`
(then in `NLAlibScaffold`; now in `Computation/Grid.lean`, 46be887b and 36d32068), and countability and measurability lemmas
for `roundNearest` (TT1's `ρOK`).

**Headline theorems that are not targets: a CONTRIBUTING rule, plus a ratchet lint.** Rule
(statements.md §3, new): *a `Result:` theorem with a contract hypothesis (one whose head is a
library predicate in the contract list: `FloatMachine.IsAccurate`, `IsRelErrSem`, `IsArithErrSem`,
`IsTapeRounding`, `IsMatMulErr`, `IsQRErr`, `IsMatvecErr`, `IsUnifSampler`, `IsNormalSampler`,
`IsExactIntLit`, `IsExactToNat`) carries `Instance: <name>` in its docstring. `<name>` is a
theorem whose type has no hypothesis binder of `Prop` type and whose proof uses the headline
theorem.* A Lean script (`scripts/Witnesses.lean`, maintainer-owned, about 120 lines) enforces
it with a baseline of today's violators, which may only shrink (as `rules_baseline.json` does).
A lint is better than a rule alone, because the failure it catches (EV6–EV8 had no instance) is
invisible in review. HDIAG's EV6–EV8 are the first entries: branch `fix/hdiag-nonvacuity`
(another agent, in progress) is writing `exists_eigh_instance_binaryFloat` and the sampler lemmas
(audit §3.2.1).

Effect: no statement or hash changes. The registry gains `witness` fields, which is a registry
edit, so the maintainer re-approves. Effort: M (library companions S, Targets item 7 S, 11
trivial witnesses S, 3 rounded witnesses M each, Witnesses.lean M).

### 2.3 MEDIUM: mandatory exactness contracts (vulnerability 3)

What is actually at risk. Leaving `IsExactToNat`/`IsExactIntLit` out of a target makes the
target **false**, not vacuous: an interpretation with `toNat = none` (the default) or an inexact
`toNat` meets the other contracts, and the run fails. B3 proves it. The real risks are different:
(i) per-target variants of the clauses, at a decoding that disagrees with the arithmetic contract
(the audit found `isExactIntLit_gridSem` proved at the identity decoding while the targets use
`roundNearest`), and (ii) a missing clause that sends a prover to "fix" the statement by adding
an ad-hoc assumption. The fix is a bundle at **one decoding**, required by the model:

```lean
/-- Index exactness of a rounded semantics at the decoding `dec`: integer literals up to `B`
and the conversion to an index are exact. -/
structure IsIndexExactSem (dec : P → K → ℝ) (B : ℕ) (sem : ScalarSem P K) : Prop where
  intLit : IsExactIntLit dec sem B
  toNat : IsExactToNat dec sem

def MatrixFreeRoundedProb … (dec : P → K → ℝ) (B : ℕ → (Fin r → ℕ) → ℕ)
    (Contracts …) (ρOK …) (pre …) (good …) (bound …) : Prop :=
  ∀ N n, valid N n → ∀ x, pre N n x → ∀ I ρ,
    IsIndexExactSem dec (B N n) I.sem → Contracts N n I → ρOK ρ → …
```

A Targets check ("a tree with `bindIdx` must reach `IsExactToNat`") was considered and rejected:
it is syntactic (a mention under a negation passes) and does not fix the decoding.

**Forcing `dec` on the other contracts (lint item 10).** The bundle fixes the decoding of the
exactness clauses only. `Contracts`, `ρOK`, `pre` and `good` keep their own decoding terms, which
are the target's outer `dec` today by convention only. Item 10 (`decErrors`): in a target of a
model with a `dec` argument, every application of a predicate of `contractPreds` (`IsRelErrSem`,
`IsArithErrSem`, `AddsZeroExactly`, `IsExactIntLit`, `IsExactToNat`, `MulShrinks`, `IsIndexExactSem`,
`IsTapeRounding`, `IsMatvecErr`, `HoldsDecoded`, `IsMatMulErr`, `IsQRErr`, `FloatMachine.IsAccurate`)
in the model's arguments takes, at its binder named `dec`, a term that mentions the model's `dec`.
`decodeComplex (dec p)` passes, another decoding `dec'` fails. Tested: the fixture
`FixTwoDecodings` is detected. On the three S2 targets (with their outer `dec` standing in for the
model's), the lint finds no violation. A type-level alternative, `Contracts : (P → K → ℝ) → ℕ →
… → Prop` applied by the model to its `dec`, was rejected: a contract could ignore its argument
and close over the outer binder.

Changes to existing statements (all on S2, none registered yet): SIGN drops
`IsExactIntLit dec I.sem 1` from `Contracts` and passes `B := fun _ _ => 1`. DEFLATE: `B := 2`.
EIGH TT1–TT3 drop `IsExactIntLit dec I.sem (N + 4)` and `IsExactToNat dec I.sem` and pass
`B := fun N _ => N + 4`; `MulShrinks` stays per-target, because only the sampler needs it. SIGN
and DEFLATE gain the `toNat` clause, which they never use. Their class of semantics shrinks only
by semantics with an inexact floor, which no real arithmetic has. Proofs: each target proof
destructures one more hypothesis (S).

Instances (proved in scratch `S2.lean` against `integrate/compdyn-s2`):
`isIndexExactSem_gridSem (t) (ht : ∀ p, 0 < t p) (B) (hB : ∀ p, B < 2 ^ t p)` at
`dec = fun p => roundNearest (t p)` (with the new `isExactIntLit_gridSem'`, 8 lines);
`isIndexExactSem_binaryFloatSem fmt he r hr B hB hmin hmax` at `dec = fun _ x => x.val`;
`isIndexExactSem_exactSem B`.

Re-pin: `MatrixFreeRoundedProb` is in no registered target's closure today, so this lands with
the S2 merge and needs no extra re-pin. Effort: S.

### 2.4 MEDIUM: cost in the rounded probabilistic model (vulnerability 4)

```lean
def MatrixFreeRoundedProb … (cost : ℕ → (Fin r → ℕ) → OpCount P ι)
    (mem : ℕ → (Fin r → ℕ) → P → ℕ) … : Prop :=
  ∀ N n, valid N n → ∀ x, pre N n x → ∀ I ρ, IsIndexExactSem dec (B N n) I.sem →
    Contracts N n I → ρOK ρ → ∀ Ω _ μ ξ, HasLaw ξ tapeLaw μ →
    μ.real {ω | ¬ prog.RunsWithin
        { I with tape := fun d i => ρ d i (ξ ω d i), charge := fun k => Finsupp.single k 1 }
        N n (inputState p (List.ofFn (inputs N n x))) (cost N n)
        (fun q => mem N n q + I.romSize q) (good N n x)}
      ≤ bound N n x
```

**ROM is counted on top of `mem` (as built, Stage 2b).** The memory argument is
`fun q => mem N n q + I.romSize q`, and `Prog.RunsWithin` checks `st.peak q + I.romSize q ≤ m q`,
so in the rounded model `mem` bounds the peak alone: declared buffers plus scratch, with the
read-only data of $I$ added on top and left unbounded. In the exact models (`MatrixFree`,
`StoredEntries`, `MatrixFreeProb`, through `Prog.RunsWithin` with `m = mem`) the same check reads
`st.peak q + I.romSize q ≤ mem N n q`, so there `mem` **includes** the ROM. **`mem` therefore means
different things in the exact and the rounded model**: a workspace bound of an exact target and
one of a rounded target are not comparable when the interpretation carries ROM. This was chosen
over a contract `I.romSize = 0` on every rounded target (spurious for programs that read no ROM).
Long term the two families should agree.

**Requirement.** Every rounded target (`MatrixFreeRoundedProb`) whose program **reads ROM**
(its tree contains an `FStmt.rom`) must bound `I.romSize` in its `Contracts`, for example
`∀ q, I.romSize q ≤ romBound N n q` with `romBound` closed form, so that input-proportional
storage cannot hide in an unbounded ROM. A program cannot allocate ROM, so a program that reads
none gains nothing from it.

Check at Stage 2b (`design/hardening-stage2`): the three rounded targets' trees
`eighProg.compiled`, `newtonSchulzSignProg.compiled` and `deflateProg.compiled` contain no `rom`
(a structural traversal of the compiled first-order trees returns `false` for each, and `true`
for `lanczosReorthProg.compiled`, which loads its matrix from ROM, as the control). All three
meet the requirement without a ROM contract.

Fixing the charge to the standard one loses no generality, because the charge affects only
`cnt` (`Interp.SameShape` minus `charge`, by non-interference §1.1). The event now contains
"over budget", exactly as in `MatrixFreeProb`. The proof route is
`Prog.runsWithin_staticCost_of_exec_eq_some` (existing) plus a closed-form bound of
`staticCost` (EIGH has EP6; SIGN and DEFLATE need one count lemma each, M). Data-dependent tight
counts (EP7) can be stated directly, since `RunsWithin` is checked on the good event. The
"companion count target" alternative was rejected: it leaves two unlinked statements, and that
gap is the vulnerability.

Lint item 8 (`costErrors`) rejects a `cost`/`mem` that reaches the tree or `staticCost` through
the values of the definitions it unfolds to (`unfoldsTo`: library and current-file definitions,
transitively; Mathlib is not followed). The fixtures `FixTreeCost` (direct) and `FixIndirectCost`
(behind a definition `treeCount`) are both detected. Since 2026-11-08 (approved by the maintainer)
the item also reads the postcondition (`good` of the rounded model, `post` of the exact ones), where
a data-dependent count clause such as EIGH's weighted kernel count is stated; the fixtures
`FixPostCost` and `FixGoodCost` are detected.

Effect: S2 targets only (unregistered). Effort: S for the model, M per target (SIGN, DEFLATE),
S for EIGH.

### 2.5 CRITICAL: credentials, rulesets and the approval (vulnerability 5)

**Severity.** This was MEDIUM in the audit; it is **critical**. Every other item in this note
assumes that a change to a code-owned path needs the maintainer, and today nothing enforces that.

Facts, 2026-11-07:
* **The agent host is the maintainer.** `gh auth status`: logged in to github.com as `tchen01`
  with a fine-grained PAT (`~/.config/gh/hosts.yml`). Every PR, review, push and `targets.approved`
  commit an agent makes through `gh` is made as the maintainer. An agent can approve any PR
  opened by someone else, and if the PAT has `Administration` it can rewrite the rulesets.
* **The agents push with deploy keys** (`~/.ssh/config`: `github-nlalib` →
  `~/.ssh/nlalib_deploy` "nlalib-harness@lightsail", `github-workflow` →
  `nlalib_workflow_deploy`, `github-explore` → `explore_deploy`). A write deploy key can push to
  any branch the rulesets do not protect, including tags and workflow files. Their read/write
  flags are visible only to an admin (`GET /repos/…/keys`), so this note does not know them.
* `.github/CODEOWNERS` names `@tchen01`; the handle exists (Tyler Chen, id 6116933) and
  `codeowners/errors` is `[]`.
* The live ruleset "main" (id 25812074): `deletion`, `non_fast_forward`, `pull_request` with
  `required_approving_review_count: 0`, `require_code_owner_review: false`,
  `dismiss_stale_reviews_on_push: false`, `require_last_push_approval: false`,
  `require_extra_approval_for_unattributed_changes: true`; **no `required_status_checks`**. PR #66
  merged with zero reviews. 16 of the last 30 commits on main are authored `Ubuntu` (the host, no
  GitHub login), and three of the four `targets.approved` commits came from the host.

**Plan, in order. Each step is useless without the ones before it.**

1. **Credentials (maintainer, today).**
   * Revoke the PAT: `gh auth logout` on the host, then delete the token at
     https://github.com/settings/personal-access-tokens. The maintainer's credentials never live
     on the agent host again, and nothing that can sign as him (GPG/SSH signing key) is there
     either.
   * A machine account (e.g. `nlalib-agent`) with the **Write** role on the repository, used for
     every agent push and PR. Its fine-grained token is for `NLA-lib/NLAlib` only, with Contents RW,
     Pull requests RW and Metadata R; **no Administration and no Workflows**, so agents cannot
     change rulesets or `.github/workflows/`. It is never a bypass actor.
   * Deploy keys: delete the write deploy keys the host uses (`nlalib-harness@lightsail` and
     "nlalib-workflow deploy key (lightsail)"), or re-add them **read-only**. The machine account's
     token replaces them for pushes. A deploy key is a separate actor (`DeployKey`): with the
     rulesets below and no `DeployKey` bypass, even a remaining write key cannot push to `main`
     or create, move or delete a tag. The workflow key is the dangerous one, because it is the
     only route by which agents could edit CI.
2. **Branch ruleset** (replace 25812074; exact JSON in the patch header):
   `pull_request` with `required_approving_review_count: 1`, `require_code_owner_review: true`,
   `dismiss_stale_reviews_on_push: true`, `require_last_push_approval: true`, and
   **`require_extra_approval_for_unattributed_changes: true` kept** (the live ruleset has it;
   a PUT replaces the rule, so it must be restated). With no bypass actor, this blocks every
   direct push to `main`. Also `required_status_checks` (strict) on the job names
   **"Build, lint, audit"**, **"Documentation regressions (Windows)"** and **"Registry approval is
   the maintainer's"** (below); `deletion`; `non_fast_forward`. `bypass_actors: []`. If the
   maintainer wants to merge his own PRs, he can add `RepositoryRole` admin with
   `bypass_mode: "pull_request"`, but only after step 1.
3. **Tag ruleset** (new): target `tag`, `~ALL`, rules `creation`, `update`, `deletion`, bypass
   admin only. Agents and deploy keys cannot tag.
4. **`docs/targets.approved` is the maintainer's own commit.** Use the base branch's CODEOWNERS
   to require his review and make the registry approval job in `.github/workflows/approval.yml`
   required on main. The job checks the full history of changes to this file. For each commit
   introducing approval content it checks that the author, committer and signature's signer are
   all `tchen01`, and that GitHub verifies the signature as `VALID` under a personal signing key.
   The maintainer signs the approval commit with a key held off the agent host. Edits signed by
   GitHub's web or API signing key do not qualify.
   A merge that carries the file byte-for-byte from a parent introduces no content of its own.
   A merge that introduces new content needs the same signature. When the PR changes the tip
   relative to both the base and the fork point, one of the qualifying commits in the PR must
   introduce those final bytes. This preserves approval provenance when a merge selects an older
   version. A failed history read or signature lookup fails the check. A push ruleset with
   `file_path_restriction` on `docs/targets.approved` would be stronger. GitHub documents push
   rulesets for private and internal repositories, so for this public repository the guard is
   the review plus the check.
5. **CODEOWNERS** (Part D): add the fixture scripts (`AccessModelFixtures.lean`,
   `AccessModelFixturesDynamic.lean`), `Witnesses.lean`, `Lint.lean`, and every model file the §1.3
   table rests on: `Syntax.lean` (no cell constructor in `IExp`), `Store.lean` (`none` cells,
   failing reads), `Exact.lean` (`inputState`, `exactInterp`, `exactSem.toNat`), `Exec.lean`,
   `FirstOrder.lean`, `RunsWithin.lean`, `Model.lean`, `Contract.lean`, `StaticCost.lean`,
   `Subst.lean`, `KernelCall.lean`, `Grid.lean`, `BinaryFloatSem.lean`, `RandomMatrix/Tape.lean`
   and `NonInterference.lean`. The owned paths also cover the checkers' input and extraction
   scripts, the explorer publication check, and the checkout rules for hashed files.
6. **Optional, later.** `required_signatures` once the machine account has a signing key, which
   also attributes the host's commits. A GitHub review is a better audit trail than a `.sig` file
   the host could be asked to produce, so the SSH-signed registry of the first version is dropped
   in favour of step 4.

Effect: none on proofs or targets. Effort: S (the maintainer: one hour of settings); Part D is a
file patch.

### 2.6 LOW: handle reuse and silent clamping (vulnerability 6)

**(a) Handles.** `alloc` binds `st.store.size`. From a state with fewer than `b` buffers, the
program's first scratch buffer gets the handle of a declared buffer. The program writes its
output into scratch, the pop frees it, and the run succeeds with the output gone. H1
(`runsWithin_scratchTree_emptySt`, typechecked on main) proves this **today** for
`Prog.RunsWithin` from the empty state.

Semantic change:

```lean
def Prog.RunsWithin (I) (prog : Prog P ι r b) (N n) (st₀) (c m Q) : Prop :=
  st₀.store.size = b ∧ ∃ st, prog.exec I N n st₀ = some st ∧ st.cnt ≤ st₀.cnt + c ∧
    (∀ q, st.peak q + I.romSize q ≤ m q) ∧ Q st
```

`b ≤ st₀.store.size` is the necessary and sufficient condition for no collision, and would allow
a program to run above outer buffers. The note proposes `= b` as asked: it matches `inputState`
exactly, and the run cannot see buffers above `b` anyway (OQ6).

Statement changes: `Prog.RunsWithin`; `Prog.runsWithin_iff` (gains `hsize : st₀.store.size = b`);
`Prog.runsWithin_staticCost_of_exec_eq_some` (gains `hsize`); the family-to-program bridges
`ProgFamily.MatrixFree.prog`, `.StoredEntries.prog`, `.MatrixFreeProb.prog` (`Model.lean`,
`Tape.lean`), which use a new lemma `inputState_store_size : (inputState p bufs).store.size =
bufs.length` with `List.length_ofFn`; and one use in `LanczosProgram.lean`. The model
definitions' text does not change: every model starts from
`inputState p (List.ofFn (inputs N n x))`, whose size is `b`. So **every registered tree meets
the condition by construction**, and every registered target stays true and provable with the
same proof plus one `simp` step. The closure hash of **all 11 registered targets** changes,
because `Prog.RunsWithin` is in their closure; their printed statements do not. That needs a
re-pin, which should be folded into the re-pin the S2 merge forces anyway (it changes `FStmt`
and `OpKind`).

What it does **not** do: SG6's `hX`, DF2's `hQ`, SB2's `hX` and EN7's `hcl` are hypotheses of
builder-level lemmas about `exec I stmt st` with handles passed as naturals. They are not about
`Prog.RunsWithin`. There they are the *correct* liveness hypothesis ("`X` is an allocated
buffer"), not a workaround. The change closes the trap at the program level. For the builder
level, the proposal is a rule in programs.md: *a lemma about the run of a builder statement whose
handles are parameters assumes each output handle is live (`X < st.store.size`, or a shape
lookup)*. Plus a helper lemma `Prog.handle_lt_size_of_runsWithin` that discharges it at the top
of every program proof (S).

H1 is in Part A today, as a positive theorem documenting the trap, and flips to `¬ …` at
Stage 2b with this change (§2.1), so that the fix shows as a diff of the fixture.

**(b) Clamping.** Should a clamp event be observable? **Yes. Recommendation: strict semantics
only**: `bindIdx` fails when the converted value exceeds its bound.

```lean
| .bindIdx p x bound body, ρB, ρI, st =>
    (toNatStep I p (x.subst ρB fun v => .const (ρI v)) st).bind fun r =>
      if r.1 ≤ bound.evalIn ρI then body.exec ρB (Fin.snoc ρI r.1) r.2 else none
```

Reasons: a corrupt size then becomes a run failure. The rounded probabilistic model counts
failures in its bad event, so the theorem has to bound it, instead of the program silently
continuing on a wrong size. The static bound is unchanged (supremum over `[0, bound]`). A
program that wants clamping can test and clamp explicitly with `ite`. The counted variant (an
`OpKind.clamp` charge) was rejected, because it changes `OpKind` for every target and makes
static costs over-approximate a charge that should never fire.

**The lower side: `toNat` on negatives.** Strict `bindIdx` removes the upper clamp only.
`toNat` still floors a negative value to `0` (`Nat.floor`; `exactSem.toNat`, `Exact.lean:74`;
`IsExactToNat` says `⌊dec p x⌋₊`), so a corrupt negative size is still silent. Options: (i) document
the asymmetry; (ii) **`toNat` fails below `0` (recommended)**. Then `IsExactToNat` becomes

```lean
def IsExactToNat (dec : P → K → ℝ) (sem : ScalarSem P K) : Prop :=
  ∀ (p : P) (x : K), sem.toNat p x = if 0 ≤ dec p x then some ⌊dec p x⌋₊ else none
```

and `exactSem`, `gridSem` and `binaryFloatSem` get `if 0 ≤ … then some ⌊…⌋₊ else none` (one line
each; their instances go from `rfl` to `by simp`). The floor itself stays: EIGH's split index is
`⌊tr(P₊) + 1/2⌋`, a deliberate rounding to nearest (`SpectralBisectionProgramTree.lean:239–240`).
So a binder accepts a value in $[0, \mathit{bound} + 1)$ and fails outside it. On the good event
every EIGH binder value is nonnegative (sizes and kinds are written by `litIdx`; the trace is
within $1/2$ of a count). On the bad event a failure is counted anyway. Effort S, in the same
change as strict `bindIdx`. An integrality check was rejected because of that rounding.

Effect: the S2 model (`Exec`, `FirstOrder`, `StaticCost`, `Subst`: about 6 lemmas, S) and the
EIGH proofs. Each of the 6 binder sites in `SpectralBisectionProgramTree.lean` (lines 240, 274,
293, 311, 312, 324) needs `k ≤ bound`. The invariants the proofs already carry supply it: size
cells read sizes $\le n - lo$ (EL1/EP1), kinds $\le 4$, $k_+ \le k$ on the good event. S–M.
Nothing on main uses `bindIdx`, and the S2 trees are not registered yet, so there is no re-pin.
This must be decided **before** S2 registers its trees.

**The shallow floor is spec-side only.** `FloatMachine.toNat : F → ℕ` with
`toNat_eq : M.toNat x = ⌊dec x⌋₊` (`Matrix/Computation/Primitives.lean`) is total and floors a
negative value to `0`. That is the **specification's** conversion, inside the shallow algorithm
`eighStep` (`kp := min k (M.toNat …)`), which the program is compared to; nothing executes it. The
program side is strict: before its split binder, EIGH runs an explicit, counted clamp
(`eighClampBlock`: two literals, two comparisons, at most one copy) that stores
`min k ⌊dec w⌋₊`, `0` for a negative trace, so the program's binder never converts a negative
value, and the program never reaches the machine's floor at `0`. The refinement equates the
program's clamped value with the shallow `min k (M.toNat w)`. Making `FloatMachine.toNat` fail
below `0` was rejected: it would make `eigh` `Option`-valued for a case the algorithm handles by
definition, change EV6–EV8, and buy nothing, since the program side is already strict.

## 3. Objects

| Object | Kind | Home | Mathlib bridge |
|---|---|---|---|
| `Computation.Query ι K` | inductive | `Computation/NonInterference.lean` (new) | none (searched: no query-trace notion for this interpreter) |
| `Computation.Interp.AgreeOn`, `Interp.SameShape` | `Prop` def / structure | same | none |
| `Computation.FStmt.queries` | def | same | none |
| `Computation.IsIndexExactSem` | structure (`Prop`) | `Computation/Contract.lean`, after `IsExactToNat` | none |
| `M.NonVacuous` for the four models | def (`Prop`) | `Computation/Model.lean` (3), `RandomMatrix/Tape.lean` (1) | none |
| `Computation.inputState_store_size` | lemma | `Computation/Exact.lean`, after `inputState` | `List.length_map`, `List.length_ofFn` |

## 4. Interfaces

`IsIndexExactSem dec B sem` bundles `IsExactIntLit dec sem B` and `IsExactToNat dec sem`. Its
raw constructor is the anonymous one, `⟨hlit, htoNat⟩`. Instances: `isIndexExactSem_exactSem`,
`isIndexExactSem_gridSem`, `isIndexExactSem_binaryFloatSem`, and `IsIndexExactSem.mono` in `B`.
`Interp.SameShape` is a plain structure of five equalities. `Interp.AgreeOn` is a conjunction
of four pointwise conditions.

## 5. Statement shapes (exact Lean)

The non-interference theorems: §1.1. The model changes: §2.3, §2.4, §2.6. The companions:

```lean
def MatrixFree.NonVacuous {𝕜} [RCLike 𝕜] {P ι} [DecidableEq P] {r b} (p) (prog) (valid) (X)
    (inputs) (cost) (mem) (post) (N₀ : ℕ) : Prop :=
  ∃ N n, N₀ ≤ N ∧ valid N n ∧ Nonempty (X N n)
-- StoredEntries.NonVacuous, MatrixFreeProb.NonVacuous: the same body, their own binders
def MatrixFreeRoundedProb.NonVacuous {P ι} [DecidableEq P] {K} {r b} (p) (prog) (valid) (X)
    (inputs) (Contracts) (ρOK) (pre) (good) (bound) (N₀ : ℕ) : Prop :=
  ∃ N n, N₀ ≤ N ∧ valid N n ∧ ∃ x : X N n, pre N n x ∧
    ∃ (I : Interp P ι K (OpCount P ι)) (ρ : Dist → ℕ → ℝ → K), Contracts N n I ∧ ρOK ρ
```

These four typecheck in scratch with binders identical to the models' (`#check`-compared). They
**must spell out the instance binders** (`[RCLike 𝕜]`, `[DecidableEq P]`) instead of taking them
from the file's `variable` line, which drops the instance binders their bodies do not use
(§2.2); `expectedWitness` reports a mismatch. After
§2.3/§2.4, `MatrixFreeRoundedProb.NonVacuous` gains `dec B cost mem` and the conjunct
`IsIndexExactSem dec (B N n) I.sem`.

The witness of a target `T := ∀ xs, M a₁ … aₖ` has the shape
`theorem T_nonVacuous : ∀ N₀ : ℕ, ∃ xs, M.NonVacuous a₁ … aₖ N₀`.

```lean
theorem isExactIntLit_gridSem' (t : P → ℕ) (ht : ∀ p, 0 < t p) (B : ℕ) (hB : ∀ p, B < 2 ^ t p) :
    IsExactIntLit (fun p => Real.roundNearest (t p)) (gridSem t) B
theorem isIndexExactSem_gridSem (t : P → ℕ) (ht : ∀ p, 0 < t p) (B : ℕ) (hB : ∀ p, B < 2 ^ t p) :
    IsIndexExactSem (fun p => Real.roundNearest (t p)) B (gridSem t)
theorem isIndexExactSem_binaryFloatSem (fmt) (he) (r) (hr) (B) (hB : B < 2 ^ fmt.mantissaBits)
    (hmin : fmt.minExponent ≤ 0) (hmax : 0 ≤ (2 ^ fmt.exponentBits : ℤ) - 2 - fmt.exponentBias -
      fmt.mantissaBitsWithoutImplicit) :
    IsIndexExactSem (fun _ x => x.val) B (binaryFloatSem (P := P) fmt he r hr)
```

## 6. Consumers

* Non-interference: the model corollaries (§1.1), which make the existing exact fixtures one-line
  instances; any future query-complexity lower bound for programs (LowerBounds' `QueryAlgorithm`
  results could then be transferred to trees); and §2.4's "the charge is irrelevant" step.
* `NonVacuous`: `Targets.lean` item 7 and every target's witness.
* `IsIndexExactSem`: `MatrixFreeRoundedProb` and the SIGN, DEFLATE and EIGH targets, plus
  every future rounded target with `litIdx`/`bindIdx`.
* `cost`/`mem` in the rounded model: the S2 targets, and the algorithm pages (rounded costs).

## 7. Files and placement

* `NLAlib/Computation/NonInterference.lean` (new): `Query`, `Interp.AgreeOn`,
  `Interp.SameShape`, `FStmt.queries`, the fold lemmas, `FStmt.exec_eq_of_agreeOn`,
  `Prog.exec_eq_of_agreeOn`, and the probabilistic corollary. It imports `FirstOrder`;
  `RandomMatrix/Tape.lean` imports it for the probabilistic model corollary.
* `Computation/Model.lean`: `MatrixFree.NonVacuous`, `StoredEntries.NonVacuous`,
  `MatrixFreeProb.NonVacuous` belong next to their models, but `MatrixFreeProb` lives in `Tape.lean`,
  so its companion goes there too. Also `MatrixFree.post_of_agreeOn` and `.post_of_noQuery`.
* `RandomMatrix/Tape.lean`: `MatrixFreeRoundedProb.NonVacuous`, and the model changes of §2.3/§2.4.
* `Computation/Contract.lean`: `IsIndexExactSem`, `.mono`, `isIndexExactSem_exactSem`.
* `Computation/Grid.lean`: `isExactIntLit_gridSem'`, plus `isExactToNat_gridSem` and
  `mulShrinks_gridSem` (moved from `NLAlibScaffold/Computation/IndexBinder.lean`, then the only
  home of these instances; done, 46be887b and 36d32068), and `isIndexExactSem_gridSem`.
* `Computation/BinaryFloatSem.lean`: `isExactToNat_binaryFloatSem` (moved),
  `isIndexExactSem_binaryFloatSem`.
* `Computation/FirstOrder.lean`, `Exact.lean`, `StaticCost.lean`, `Model.lean`, `Tape.lean`,
  `Krylov/Processes/LanczosProgram.lean`: §2.6(a).
* Maintainer-owned: `scripts/AccessModelFixtures.lean`, `scripts/AccessModelFixturesDynamic.lean`
  (new), `scripts/Targets.lean`, `.github/workflows/ci.yml`, `.github/workflows/approval.yml`
  (new), `.github/CODEOWNERS`, the registry's `witness`, `witness_sem` and `[[model]]` entries
  (§8).

## 8. Material, and the maintainer's patches

Read: `Exec.lean`, `FirstOrder.lean`, `Model.lean`, `Contract.lean`, `Grid.lean`,
`BinaryFloatSem.lean`, `StaticCost.lean`, `RandomMatrix/Tape.lean` (main and S2);
`NLAlibScaffold/Computation/IndexBinder.lean` (since removed; its content is in
`Computation/{IndexBinder,Contract,Grid,BinaryFloatSem}.lean`); the S2 targets; `scripts/Targets.lean`;
`scripts/AccessModelFixtures.lean`; `docs/design/Computation-DynamicPrograms.md` §3–4; the audit;
the review `reports/Review-Fable-Hardening.md`. Scratch files (not committed, under
`/tmp/hardening/`): `Main1.lean`, `Main2.lean` (Part A), `S2.lean` (Part B and the bundle instances
`isExactIntLit_gridSem'`, `isIndexExactSem_gridSem`, `isIndexExactSem_binaryFloatSem`,
`isIndexExactSem_exactSem`, all proved; to be attached to the Stage 2b dispatch), `NI.lean` (the
non-interference statement), `Witness.lean` and `NonVacuous.lean` (item 7), `DecS2.lean` (item 10
on the S2 targets).

The patch file `reports/Hardening-maintainer-patches.diff` (harness). Its header lists the
credential steps, both rulesets as JSON, and the Stage 2b fixture rewrites. Apply each part with
`git apply --include=<path>` at its stage; every part passes `git apply --check` on main, and
Part B also on `integrate/compdyn-s2`:
* **Part A (Stage 0, main):** `scripts/AccessModelFixtures.lean` gains K1–K4, U1, U2, R1 and H1,
  with their documentation. Checked: the patched file passes `lake env lean` on main.
* **Part B (Stage 2a, with the S2 merge):** new `scripts/AccessModelFixturesDynamic.lean` (B1, B2,
  B3, B3', B3b) and its CI step in `ci.yml`. Checked on `integrate/compdyn-s2`.
* **Part C (Stage 1, with the library companions of §5):** `scripts/Targets.lean`: `models` gains
  `MatrixFreeRoundedProb`; item 7 (`expectedWitness` with `Meta.check`, `witnessError`, the
  `witness` field); item 8 (`costErrors` over `unfoldsTo`); item 9 (`[[model]]` tables,
  `modelHash`, `requiredCompanions`); item 10 (`decErrors`, `contractPreds`). Fixtures:
  `fixHutchpp_nonVacuous`, `fixHutchpp_atOne`, `FixVacuousRounded`, `FixTreeCost`, `treeCount`,
  `FixIndirectCost`, `FixTwoDecodings`, plus tampered, missing and companion-less model tables.
  Checked on main, with the companions prepended to a copy: every fixture passes, and the real
  registry reports exactly the 11 targets without `witness` and the 4 models without a
  `[[model]]` table. The registry gains both in the same PR.
* **Part D (Stage 0):** `.github/CODEOWNERS` (the handle confirmed; the additions of §2.5(5)) and
  the new `.github/workflows/approval.yml` (the required check of §2.5(4)).

## 9. Staged plan

* **Stage 0 (now, maintainer; in this order).** (1) Revoke the PAT on the host and stop agents
  from signing as the maintainer; machine account; deploy keys read-only or deleted (§2.5(1)).
  (2) Branch and tag rulesets (§2.5(2)–(3)). (3) Parts D and A. Nothing to re-pin.
* **Stage 1 (library on main; registry fields and tables only).** The four `NonVacuous` companions
  (binders spelled out), the 11 exact witnesses with `witness_sem`, then Part C with the
  `witness` fields and `[[model]]` tables in one PR. The maintainer re-approves the registry;
  target hashes are unchanged. The `Instance:` rule in statements.md, and `Witnesses.lean`
  with its baseline, starting with HDIAG EV6–EV8 from `fix/hdiag-nonvacuity`.
* **Stage 2a (the S2 merge, as the S2 branch stands).** Part B.
* **Stage 2b (the hardening model changes, in the S2 branch before its trees are registered;
  one re-pin for everything).** Strict `bindIdx` and `toNat` failing below `0` (§2.6b);
  `IsIndexExactSem`, `dec`, `B`, `cost`/`mem` in `MatrixFreeRoundedProb` (§2.3, §2.4);
  `st₀.store.size = b` in `Prog.RunsWithin` (§2.6a); the non-interference theorem and the model
  corollaries, with `post_of_agreeOn` added to `requiredCompanions` and to the `[[model]]` tables.
  **The fixture rewrite of §2.1 (S): K1, K2, K3, U2, R1, B2, B3 → B3b, B3', H1 flipped,
  `FixVacuousRounded`.** Then the S2 targets are restated (audit §3.2.4 plus §2.3/§2.4) and
  registered with their three rounded witnesses, and all registered targets and model tables are
  re-pinned once.
* **Stage 3.** Rounded `Result:` theorems carry `Witness:` (§1.4). Optionally
  `required_signatures` (§2.5(6)).

## 10. Open questions

* **OQ1** Non-interference with the full query set (recommended), or only "the run is independent
  of `oracle` outside its range" (weaker, no `queries` definition)? *Recommend the query set*,
  because it is what makes K1 and the model corollaries instances.
* **OQ2** `N₀` outside the outer binders (recommended), or a fixed nontrivial size such as
  `N = 2`? *Recommend `∀ N₀`*: it rules out preconditions that hold only at small sizes, and a
  witness can still choose the format per size.
* **OQ3** `Instance:` lint scope: the contract-predicate list of §2.2 (recommended), or every
  `Result:` theorem with a library-`Prop` hypothesis (many trivial cases)?
* **OQ4** `MulShrinks` in the bundle? *Recommend no*: only the uniform sampler uses it.
* **OQ5** Rounded cost in the event under the standard charge (recommended), or a separate
  registered count target?
* **OQ6** `st₀.store.size = b` (as asked) or `b ≤ st₀.store.size`? *Recommend `=`*, because
  the run cannot see buffers above `b`.
* **OQ7** Strict `bindIdx` only (recommended), a strict flag, or a counted clamp?
* **OQ8** The approval guard: review plus the verified-commit check (recommended), plus a push
  ruleset if the plan offers one, or plus signed `.sig` files? *Recommend the first*: the
  signature file of the first version is dropped (§2.5(6)).
* **OQ9** `toNat` below `0`: fail (recommended) or floor to `0` and document?

## 11. Status (2026-11-08, `cleanup/compdyn-s2`)

Carried out on `design/hardening-impl` (non-interference), `fix/hardening-fixtures` (Stage 0),
`design/hardening-stage2` (Stage 2b, M2–M4) and `cleanup/compdyn-s2` (Stage 1, Part C, the
witnesses and the registry). Fable reviewed Stage 2b (`reports/Review-Fable-Hardening-Stage2.md`,
approve; items M1–M4).

| # | Status |
|---|---|
| G | **Done.** `Computation/NonInterference.lean`: `Query`, `Interp.AgreeOn`, `Interp.SameShape` (with `romSize`), `Stmt.queries`, `exec_eq_of_agreeOn` over `Stmt` (every constructor, `bindIdx` included), transferred to `FStmt` and `Prog`, `Prog.runsWithin_iff_of_agreeOn`, the probabilistic forms `measureReal_not_runsWithin_eq_of_agreeOn` and `map_exec_eq_of_map_restrict_eq`, and `MatrixFree.post_of_agreeOn`, `.post_of_noQuery` (59e91d3d, a5dda2e9; re-proved over the strict binder). The corollary is in `NonInterference.lean`, not `Model.lean` (§7). Only `MatrixFree` has one, so Part C's `requiredCompanions` stays `[NonVacuous]` (below). |
| 1 | **Done.** Part A (K1–K4, U1, U2, R1, H1) on main (PR #68, 4cceb220). The Stage 2b rewrite (7a0d1cd5): K1–K3, U2, R1 at `dec := id`, `B := 0`, `cost`/`mem` $0$ (new `isIndexExactSem_upLitSem` for R1); K4 and the exact fixtures destructure the size conjunct; H1 flipped to `not_runsWithin_scratchTree_emptySt`. Part B in its Stage 2b form (`scripts/AccessModelFixturesDynamic.lean` and its CI step): B1, B2 (false by failure), B3b (replaces B3), B3'. M2 (68e5a624): `exec_idxCopyTree_eq_none` and `exec_negIdxTree_eq_none`, which a clamping binder or a flooring `toNat` would make false. |
| 2 | **Done for targets; not done for headline theorems.** Companions `MatrixFree.NonVacuous`, `StoredEntries.NonVacuous` (`Model.lean`), `MatrixFreeProb.NonVacuous`, `MatrixFreeRoundedProb.NonVacuous` (`Tape.lean`; with the conjunct `IsIndexExactSem dec (B N n) I.sem`) (cacad174). Part C items 7–10 applied (c983ecc5, adjustments below). 14 witnesses (11 exact: d89f8b8d, next to each target's proof, `P = ι = Unit`, `N = N₀ + 1`; 3 rounded: 399945ec, `RandomMatrix/Computation/RoundedTargetWitnesses.lean`, at `gridSem t` with $u = 2^{-t} > 0$ and $t$ chosen from $N$, the grid kernels `gridMM`/`gridQR` and the machine `gridMachine t` of the new `Matrix/Computation/GridMachine.lean`, tape `roundNearest t`), with `witness` and `witness_sem` in the registry and the four `[[model]]` tables (1f43e0a9). The rounded witnesses use rounding kernels (`gridMM`, `gridQR`: the exact product or QR of the decoded inputs, rounded per part, $\mu(d) = 2d$), not the `exactMM`/`exactQR` planned above. No witness found a vacuous target. `binaryFloatSem` cannot witness the rounded targets: `IsRelErrSem` with every value in range fails by underflow and overflow, and the machine floor $\tau > 0$ is not the targets' $0$. **Not done:** the `Instance:` rule in `statements.md` and `scripts/Witnesses.lean` with its baseline (maintainer-owned). |
| 3 | **Done.** `IsIndexExactSem`, `.mono` and the instances for `exactSem`, `gridSem` (with `isExactIntLit_gridSem'`), `binaryFloatSem` (46be887b); a clause of `MatrixFreeRoundedProb` (b228ea6f); the SIGN, DEFLATE and EIGH targets restated as in §2.3. Lint item 10 (`decErrors`) in Part C. |
| 4 | **Done.** `cost` and `mem` in `MatrixFreeRoundedProb`, the event under the standard charge, `MatrixFreeRoundedProb.of_exec` (b228ea6f); the three targets' closed-form costs and memories as in §2.4. Lint item 8 (`costErrors`, transitive) in Part C. ROM on top of `mem` and the ROM requirement documented in §2.4 and in the model's docstring (M4, 6d1239ab). |
| 5 | **Maintainer.** Part D (CODEOWNERS, `approval.yml`) on main (PR #68). Credentials: the maintainer chose website-only pull requests (`gh` logged out on the host) instead of a machine account (sheet comment). The rulesets of §2.5(2)–(3) are the maintainer's and are not recorded here. |
| 6a | **Done.** `st₀.store.size = b` in `Prog.RunsWithin`; `Prog.runsWithin_iff` and `Prog.runsWithin_staticCost_of_exec_eq_some` gain `hsize`, discharged by `size_store_inputState` (35cee506, f7c8252e, b332c08a). H1 flipped. The programs.md rule for builder-level handle liveness and `Prog.handle_lt_size_of_runsWithin` are not written. |
| 6b | **Done.** `bindIdx` fails above its bound, `toNat` fails below $0$ in `exactSem`, `gridSem`, `binaryFloatSem`, and `IsExactToNat` demands the failure (35cee506, merged at 9151b0dd; repairs f7c8252e). The one program that relied on clamping, `eighProg`'s split index, now clamps by counted instructions (`eighClampBlock`, 40926974; `Computation-EighProgram.md` §8, "End-of-stage status"). The NumPy exporter emits the binder strict (M3, 12aa340e). |

Stages: **0** done (Parts A and D on main; credentials as above). **1** done on this branch rather
than on main: companions, the 11 exact witnesses, Part C and the registry fields and tables; the
`Instance:` rule and `Witnesses.lean` are open. **2a** done (Part B, applied in its Stage 2b form).
**2b** done: the model changes, the fixture rewrite, non-interference, the S2 targets restated and
registered with their three rounded witnesses; `post_of_agreeOn` is required of `MatrixFree` only
(its `[[model]]` table lists it). **3** not started.

Part C was applied with these adjustments (c983ecc5, maintainer-authorised): `FixVacuousRounded`
and `FixTwoDecodings` take the model's new `dec B cost mem` (the vacuous fixture's proof takes the
`IsIndexExactSem` hypothesis); `decErrors` loses its outer-binder mode, and `FixTwoDecodings` (now
at the model's `dec`) is still detected; `requiredCompanions` stays `[NonVacuous]`, since only
`MatrixFree` has `post_of_agreeOn`, and a `[[model]]` table may list more companions. Two further
check edits need the maintainer's review: d166f411 (two `Targets.lean` fixtures discharge the size
conjunct; proof terms only) and eb0bda85 (`set_option maxRecDepth 100000` on the registry
`run_cmd`, needed once `eighProg.compiled` is registered). The branch also carries 3cae40fd (E8
exemption for `NonInterference.lean` in `scripts/check_rules.py`).

Re-pin (Fable M1, outstanding): `scripts/Targets.lean` on the branch reports 28 violations, all
re-pin items (the 3 new trees' hashes and normal forms, the closure hashes of all 14 targets and
the printed statements of the 3 new ones, the 4 `[[model]]` hashes, `docs/targets.approved`); the
`lakefile.toml` pin passes. The maintainer's commit: `TARGETS_UPDATE=1 lake env lean
scripts/Targets.lean`, then `sha256sum docs/targets.toml > docs/targets.approved`.

Open: the `Instance:` rule and `scripts/Witnesses.lean`; `post_of_agreeOn` for the other three
models; Stage 3 (`Witness:` on rounded `Result:` theorems); the programs.md rules of §2.6(a) and
M4 (the ROM convention is in this note and the model's docstring, not yet in programs.md); making
`mem` mean the same in the exact and rounded families.
