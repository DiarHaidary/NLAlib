# Certified routines: one shape for subroutines that other algorithms consume

2026-11-07. Design note; **status: proposal, nothing implemented; Fable review 2026-11-07
(`reports/Review-Fable-CertRoutines-Design.md`): approve with fixes, all 12 findings applied (§7)**. Branch `design/certified-routines`
from `origin/main` @ `2c0d1ec8` (PR #60, Lanczos with full reorthogonalization, merged). Decision
sheet: harness `state/decisions/CERT-ROUTINES.json` (ids CR1–CR10 below).

The maintainer's goal: "what we are working on is partly to build the infrastructure for other
ppl to help add stuff to NLA-lib. so we want to be able to have these certificated subroutines
integrate nicely". Standing rule: an algorithm does not cheat outside the model of computation.
Every data operation is a rounded instruction, an oracle call or a kernel call whose contract
the statement quantifies over.

This note surveys the certified-subroutine patterns on main. It proposes one shape for them,
the proof infrastructure that makes the shape cheap to use, and a contributor guide. It changes
no statement on main and no registered target.

## Summary

* **What exists.** Main has two *routine certificates*: `IsMatvecRoutine`
  (`Computation/MatvecRoutine.lean`; consumed in 13 files: the rounded CG and Lanczos programs
  and Lanczos-FRO) and `IsOrthRoutine` (`Matrix/Computation/OrthRoutine.lean`; consumed by
  `exec_rounded_loop`, with one instance, CGS2). Main also has three neighbouring notions that
  are not routine certificates. *Oracle and kernel contracts* (`IsMatvecErr`, `IsMatMulKernel`
  plus `IsMatMulErr`, `IsQRKernel` plus `IsQRErr`) are model-level black boxes quantified in
  target statements. *Implementation certificates* (`ImplementsOracle`, `ImplementsKernel`) are
  exact store simulations for `RunsWithin.subst`. *Run lemmas* (`exec_dot_frame`,
  `exec_cgsPass_frame`, …) are written in a "shape, reads, outside unchanged" frame style.
* **Shared shape (§1).** A certificate is a `Prop` structure with two fields: `composable` and
  `run`. `run` says: from any state whose inputs decode to some values and whose outputs are
  writable, the routine succeeds, and its final store is *exactly* a list of block writes of the
  original store, so its scratch is scoped. The decoded outputs satisfy a guarantee with named
  real parameters. The two certificates differ in nine places (§1.2). Three of the differences
  are principled or deliberate. The others are accidents, and one of them, the opaque `pre`,
  caused the G5 `hpreFrame` bug.
* **Recommendation (CR1 = b′).** A *generic footprint layer, with typed guarantees*. One generic
  structure, `IsBlockRoutine`, states success plus "writes exactly these blocks", with no
  guarantee. The frame, shape and `pre`-transport lemmas are stated once, on the `writeBlocks`
  equation that every certificate's `run` already yields. `IsBlockRoutine` itself is needed only
  for sequencing (L11) and charge independence (L14). Each
  certificate stays a typed structure with a named guarantee (`IsOrthErr`, and a new name for the
  matvec bound), and it projects to the footprint by a one-line `toBlockRoutine`. A fully generic
  `IsCertifiedRoutine` whose guarantee ranges over `List (Array K)` (option b) is rejected: its
  guarantee would move matrix shapes into list and array index arithmetic, which is the cost we
  want to remove. A template alone (option a) leaves every new certificate to re-prove the same
  frame lemmas.
* **Kernels (CR6 = c1).** A kernel contract yields a certificate (`IsMatvecErr.isMatvecRoutine`
  already does this for oracles; `IsMatMulKernel.isMatMulRoutine` would be next). So a consumer
  parameterised by certificates accepts kernel calls, stored programs and oracles alike. The
  converse (a certified routine becomes a kernel through `ImplementsKernel`) is deferred. It needs
  a "reads only its inputs" clause that certificates do not state, and it is needed only for cost
  targets about trees that contain a `kcall`.
* **Infrastructure (§3).** 20 lemmas and definitions (S 14, M 6, no L). The core is three lemmas:
  a list-of-blocks extensionality lemma (frame style to block-write style; CGS2 proved the
  two-block case privately in 40 lines), a scoped-scratch lemma for `alloc`, and a "write one
  block per iteration" loop lemma. The last two have existential outputs, modelled on CGS2's
  `exists_exec_alloc` and `exists_exec_loop_write`. The rest: `IsFramed` (so a certificate's
  precondition is carried along without a consumer-supplied `hpreFrame`), named
  `ReadsDecoded`/`Writable` predicates (the inline forms occur about 340 and 33 times in
  `NLAlib`), and a `blockDisjoint_iff` lemma so disjointness goals close by `omega`. Estimate:
  about 950 lines. In CGS2 the private helpers it replaces total about 170 lines; the rest of
  CGS2's 785-line program file is rounding composition, which this does not touch. The pilot
  measures the real saving against a 25% gate (CR10).
* **Contributor guide (§4).** "Adding a routine that meets an existing certificate", "adding a
  consumer", "adding a certificate": file placement, naming, checklist, what attaches where in the
  explorer and in `docs/targets.toml`. It opens with a table (§4.0): are you adding a primitive,
  a contract, a certified routine or a consumer, and what does each re-pin. Certificates never
  appear in registered target statements. A target fixes a concrete tree, and the certificate is
  how its proof is modular.

## 0. Inventory (verified on `origin/main` @ `2c0d1ec8`)

| notion | file | quantified where | what it says |
|---|---|---|---|
| `IsMatvecRoutine I dec tag A c pre src dst sOff dOff routine` | `Computation/MatvecRoutine.lean` | consumer hypotheses (`hmv : ∀ t, …`) in 13 files | composable; `pre`, readable source, writable destination ⇒ run succeeds, `writeBlock dst` is the whole effect, $\|Ax - \bar y\| \le c\|x\|$ |
| instances | `IsMatvecErr.isMatvecRoutine` (oracle `apply`), `IsRelErrSem.isMatvecRoutine_gemv` (stored dense, `Matrix/Computation/MatvecRoutine.lean`) | — | `pre = True`, resp. `pre = HoldsDecoded store … matrix aOff A` |
| `IsOrthRoutine I dec tag N j η₀ ε₁ ε₂ ε₃ pre Vb wb hb wo ho routine` | `Matrix/Computation/OrthRoutine.lean` | `exec_rounded_loop` (`horth : ∀ t < q, …`) | composable; `pre`, `HoldsDecoded V`, readable `w`, writable `wb`, `hb`, three buffer inequalities ⇒ success, `writeBlock wb` then `writeBlock hb` is the whole effect, `IsOrthErr` |
| `IsOrthErr η₀ ε₁ ε₂ ε₃ V w h w'` | `Matrix/Perturbation/OrthErr.lean` | — | the decoded guarantee: a pure-math predicate with `mono`, `norm_coef_le`, … |
| instance | `IsRelErrSem.isOrthRoutine_cgs2` (`ClassicalGramSchmidtProgram.lean`, 785 lines) | — | CGS2 at $(\eta_0, 2c_1, 3c_1, 2(\eta_0+c_1)^2)$ |
| `IsOrthCall … (G t) routine` | `Krylov/Processes/LanczosReorthProgramRoundedStep.lean` | `exec_lanczosReorthLoop` | a consumer-local restatement of `IsOrthRoutine` at the workspace shape, with buffer numbers fixed and disjointness discharged |
| `IsMatvecErr I o dec p A c` | `Computation/Contract.lean` | `MatrixFreeRounded` (target level) | oracle contract on words: success and normwise error |
| `IsMatMulKernel I o L mm ∧ IsMatMulErr dec u τ Ω μ mm`, `IsQRKernel`, `IsQRErr` | `Matrix/Computation/KernelContracts.lean` | target level (S1cd's `DeflationTargets`, `NewtonSchulzSignTargets` on `design/compdyn-s1cd`) | the kernel *is* `liftMM L mm`; `mm` is accurate |
| `ImplementsOracle`, `ImplementsKernel` | `Computation/Subst.lean` | `RunsWithin.subst` | an implementation writes *the same store* as the abstract call, at bounded cost and scratch |
| `ExecutionComposable I b` | `Computation/ScalarFrames.lean` | field of both certificates | `exec (b >>= f) = exec b >>= exec f` |
| `exists_exec_withCharge_eq_some` | `Computation/ExecCharge.lean` | run proofs under unit charge (`exec_commitPhase_of_charge`) | the store does not depend on charges |
| frame-style run lemmas | `Computation/BLAS/Frames.lean` (`exec_dot_frame`, …), `exec_cgsPass_frame` | — | `shape = ∧ reads ∧ ∀ q b i, outside → read unchanged ∧ pos/cur/cnt` |

No registered target statement reaches `IsMatvecRoutine` or `IsOrthRoutine` (grep of
`docs/targets.toml`). Certificates are proof infrastructure, so changing them re-pins nothing.
Kernel contracts *are* reached by the S1cd target statements. Changing them re-pins.

## 1. What a certified routine is

### 1.1 The shared shape

Abstracting the two certificates:

```lean
structure Is<Op>Routine (I : Interp P ι K C) (dec : P → K → ℝ) (tag : P)
    (dims…) (params : ℝ…) (pre : Store P K → Prop) (operands : buffers × IExp offsets)
    (routine : Builder P ι ℕ ℕ Unit) : Prop where
  composable : ExecutionComposable I routine
  run : ∀ (st : St P K C) (inputs : typed decoded values), pre st.store →
    <inputs readable and decoding to `inputs`> → <outputs writable> → [disjointness] →
    ∃ (out : St P K C) (Ys : typed word families) (mid…),
      exec I routine.run st = some out ∧
      <st.store, then one writeBlock per output block, gives out.store> ∧
      <Guarantee params inputs (decoded Ys)>
```

Each piece does a separate job.

1. **Success, not partial correctness.** `exec … = some out` is concluded, not assumed.
   A consumer's run lemma needs this, because its own success depends on it.
2. **The exact effect.** The frame is an *equation*: the final store is the initial store after
   the listed block writes. This implies at once that the shape is preserved, so scratch was
   scoped and released. It also implies that every cell outside the blocks is unchanged at every
   tag, and that every other buffer is unchanged. It is strictly stronger than the frame style of
   the BLAS run lemmas, and it is what lets a consumer put a routine inside a larger workspace.
   The success clause rules out an `alloc` that is not released, because the store size would
   change.
3. **Composability.** `ExecutionComposable` lets the consumer split `exec (routine >>= rest)`.
   Every current instance discharges it by `executionComposable_single` (the routine is a
   `scope` or one statement).
4. **The guarantee as a pure-math predicate over named real parameters.** The consumer's
   analysis depends only on the parameters: $c$ for products, $(\eta_0, \varepsilon_1,
   \varepsilon_2, \varepsilon_3)$ for orthogonalization. The arithmetic contract (`IsRelErrSem`,
   `IsMatvecErr`, a kernel contract) is a hypothesis of the *instance theorem*, never of the
   certificate. So one certificate covers exact, rounded and black-box implementations.
5. **Words are existential, decodings are universal.** Outputs are `∃ W : Fin N → K` decoded by
   `dec tag`. Inputs are any reals that the stored words decode to. Nothing fixes *which* words
   are written, which is why a certificate is weaker than `ImplementsKernel` (§2.3).

**Anti-cheating.** A certificate is about `exec I routine.run`, where `routine` is a builder in
the language. The routine therefore touches data only through instructions, oracle calls and
kernel calls of `I`, and an instance theorem proves the guarantee for every `I` that meets the
stated contract. A consumer parameterised by a certificate cannot do anything outside the model
either: it is a program that calls `routine`. Two loopholes remain, and the checklist (§4.3)
closes them. (i) A certificate whose hypotheses are unsatisfiable makes its consumers vacuous.
Every certificate therefore needs an exact witness. CGS2 has one (`exec_cgs2_exactSem`).
The matvec witness, `isMatvecErr_exactInterp`, exists but is `private` in
`Krylov/Processes/LanczosReorthProgram.lean`; it should move next to `IsMatvecErr` and become
public. (ii) A registered target must not take a certificate as a
hypothesis. Rule E3 already rejects outer hypotheses, and targets fix concrete trees.

### 1.2 Where the two certificates differ, and whether the difference is principled

| | `IsMatvecRoutine` | `IsOrthRoutine` | principled? |
|---|---|---|---|
| D1 operator vs data | `A` is a fixed **parameter**; if it is stored, that is hidden in `pre` | `V` is a universally quantified **input** (`HoldsDecoded … V`) | **Yes.** `A` is the same at every call of the consumer; `V` changes per step. Keep both, but say it: *parameters* are fixed across calls, *inputs* are quantified per call. The certificate layer needs no oracle→operator map: a consumer that uses $\mathbf A$ and $\mathbf A^{\mathsf T}$ takes two certificate hypotheses, and the bridge `IsMatvecErr.isMatvecRoutine` is per oracle name, so it takes whatever operator the contract names (`M o`). The map belongs to the model (`exactInterp` already takes `ι → Matrix`); see `docs/design/Computation-Oracles.md` (branch `design/oracle-model`). |
| D2 `pre` | arbitrary `Store → Prop`; the consumer must re-establish it after every step (`hpreFrame`) | arbitrary, used only as `fun _ => True` | **No.** An opaque `pre` forces each consumer to state and prove how `pre` survives its own writes. G5's `hpreFrame` first had an equal-shape form, which could not be discharged because `mv` runs inside the 11-buffer workspace. It was weakened by hand to "the first 8 shape entries and buffer 7". The fix is `IsFramed pre ro` (§3, L6), which says which buffers `pre` reads. It is a hypothesis of instance and consumer theorems, not a new field, so the two structures stay unchanged (CR2, CR3), and every consumer transport becomes one lemma (L7). `IsFramed` compares `shape[b]?` only for `b ∈ ro`, which is exactly what the equal-shape form lacked. |
| D3 disjointness | on the instance theorem (`hdx : dst ≠ src`); the certificate is per operand assignment | inside `run` (`hb ≠ wb → hb ≠ Vb → wb ≠ Vb → …`) | **Deliberate, but to be reversed.** `Krylov-LanczosReorth.md` §1.3 put the inequalities in `run` on purpose ("disjoint from `Vb` and `wb`"). The cost: they must be discharged at every call, and in `exec_rounded_loop` this cost an adapter (`IsOrthCall`) and a 10-line lambda. Both forms are also too strong. They are *buffer* inequalities, which forbids the Arnoldi/GMRES pattern where `w` is the next column of `V` in the same buffer at a disjoint offset. Proposal (CR4): state disjointness at *block* level (`blockDisjoint`, as `kcall` and L4 do) on the instance theorem. |
| D4 output form | one `writeBlock` | `writeBlock` then `writeBlock` through an explicit `mid` | **No, but harmless.** It is the same thing as `Store.writeBlocks tag [(wb, wo, N), (hb, ho, j)] [W, H]`, which `kcall` already uses. One list form scales to $k$ outputs and shares the `kcall` lemmas (`read_of_writeBlocks_eq_some`, `…_of_forall`). Until the CR2 migration, the template's list form disagrees with both exemplars (`writeBlock`; `writeBlock`/`mid`). L3 is the bridge. |
| D5 guarantee | inline inequality | named predicate `IsOrthErr` with an API | **No.** CONTRIBUTING §5.4 makes a hypothesis a named interface. Name the matvec bound (CR5); `IsMatvecErr` is already taken by the oracle contract on words. |
| D6 offsets | buffers `ℕ`, offsets `IExp ℕ` for both blocks | `Vb` at offset `0`, no `IExp` | **No.** Use `(ℕ × IExp ℕ)` operands everywhere, as `kcall` does. A block of a larger arena (Shah's packed nodes) needs an offset. |
| D7 dimensions | from the type of `A` | explicit `N j : ℕ`; the instance has `NE jE : IExp ℕ` with `hN : NE.eval = N` | **Yes.** The routine is built at symbolic sizes; the certificate is about one evaluation. |
| D8 `mono` | `IsMatvecRoutine.mono` | none (`IsOrthErr.mono` only) | **No.** Missing API (checklist). |
| D9 step quantifier | consumers take `hmv : ∀ t, …` at four sites (`LanczosReorthProgramRoundedLoop.lean:336, 436, 545`, `LanczosReorthProgram.lean:253`) | `horth : ∀ t < q, …` | **No.** Over-quantifying is harmless for stored instances, but it is the template contributors copy, and it came from the stage note itself (`Krylov-LanczosReorth.md`). A certificate hypothesis is quantified over the executed steps only (checklist §4.3; CR2 migration list). |

Two further points that both certificates share and that are deliberate for now:

* **No cost or memory clause.** On main, cost and memory are *syntactic*: `FStmt.staticCost`
  (`StaticCost.lean`, compositional through `StaticCost.seq`, `.alloc`, `.sequence`) with
  `bounds_staticCost_of_exec_eq_some`. Both Lanczos-FRO targets discharge their counts by
  `staticCost_count_le` on the compiled tree, never from `exec`. A cost clause inside `run` would
  be charge-dependent and would break charge independence (L14). A routine's cost obligation is
  therefore a `staticCost` lemma on its emitted tree (CR7). A cost-*generic* consumer ("Lanczos-FRO
  costs $q$ times the routine's cost plus $O(qN)$") is not expressible today, because `staticCost`
  is on `FStmt` and certificates are on `Builder`. It is an open problem (§6).
* **No tape clause.** Neither certificate mentions `pos`, so a sampling routine (sketch, uniform
  draw) is out of scope. Its guarantee is distributional and belongs to the `MatrixFreeProb`
  layer. A later certificate kind would add `out.pos = st.pos + draws` and a law.

## 2. Options for making this uniform

### 2.1 The three options

**(a) Per-routine structures, a documented template and a checklist.** Status quo plus §4. Each
new certificate copies the shape, and each consumer proves its own frame, `pre` transport and
adapter lemmas.

**(b) One generic `IsCertifiedRoutine`.**
```lean
structure IsCertifiedRoutine (I) (tag) (α : Type) (pre : α → Store P K → Prop)
    (outs : List (ℕ × IExp ℕ × ℕ)) (G : α → List (Array K) → Prop) (routine) : Prop where
  composable : ExecutionComposable I routine
  run : ∀ st a, pre a st.store → Writable st.store tag outs → ∃ out Ys,
    exec I routine.run st = some out ∧ st.store.writeBlocks tag (eval outs) Ys = some out.store ∧
    G a Ys
abbrev IsOrthRoutine … := IsCertifiedRoutine I tag (Matrix … × (Fin N → ℝ))
  (fun (V, w) s => pre s ∧ HoldsDecoded s dec tag Vb 0 V ∧ ReadsDecoded s dec tag wb wo w)
  [(wb, wo, N), (hb, ho, j)]
  (fun (V, w) Ys => ∃ W H, Ys = [Array.ofFn W, Array.ofFn H] ∧ IsOrthErr … V w (dec ∘ H) (dec ∘ W))
```

**(b′) A generic footprint layer with typed guarantees (recommended).** Only the part that
carries no mathematics is made generic:
```lean
/-- `routine` succeeds from every state satisfying `pre` whose output blocks are writable, and
its whole effect is one write per output block. No guarantee. -/
structure IsBlockRoutine (I : Interp P ι K C) (tag : P) (pre : Store P K → Prop)
    (outs : List (ℕ × ℕ × ℕ)) (routine : Builder P ι ℕ ℕ Unit) : Prop where
  composable : ExecutionComposable I routine
  run : ∀ st : St P K C, pre st.store → Writable st.store tag outs →
    ∃ out Ys, exec I routine.run st = some out ∧ st.store.writeBlocks tag outs Ys = some out.store
```
Each typed certificate keeps its typed `run` and gains a projection, provable in one line from
`run` because the guarantee is dropped:
```lean
theorem IsOrthRoutine.toBlockRoutine (h : IsOrthRoutine …) :
    IsBlockRoutine I tag (fun s => pre s ∧ ∃ V w, HoldsDecoded s … V ∧ ReadsDecoded s … w)
      [(wb, wo.eval, N), (hb, ho.eval, j)] routine
```
The value of b′ is in the *equation*, not the structure. A consumer calls the typed `run` once,
and that call already yields the `writeBlocks` equation. The frame, shape and `pre`-transport
lemmas (L5, L7, L12) are stated on that equation, so the consumer never calls
`toBlockRoutine.run` as well, which would give a second `out` identified only by determinism.
`IsBlockRoutine` is reserved for the lemmas that need a routine, not a run: sequencing (L11) and
charge independence (L14).

**(c) Tie to the COMPDYN kernel contracts.** Two directions, analysed in §2.3. (c1) A kernel
contract yields a certificate. (c2) A certified routine can stand in for a kernel.

### 2.2 Analysis

| criterion | (a) template | (b) generic `IsCertifiedRoutine` | (b′) footprint layer + typed guarantees |
|---|---|---|---|
| frame and disjointness proofs (C3, C6, G3, G5) | re-proved per routine and per consumer: `eq_of_read_writeBlock_writeBlock` (40 lines, private to CGS2), `exec_cgsPass_frame` (90), `StoreContext.succ`'s 8-way frame (50), `IsOrthCall` adapter | proved once | proved once |
| guarantee ergonomics | typed (`Matrix (Fin N) (Fin j) ℝ`) | the guarantee is on `List (Array K)`: every instance and consumer destructures a list, converts `Array.ofFn` and `getElem` back to `Fin` functions, and carries length side conditions. This is the index arithmetic that made C6/G3 hard. | typed |
| shape transport (the G5 bug) | the consumer writes `hpreFrame` by hand | `pre` is per certificate; transport needs `IsFramed` anyway | `IsFramed` hypothesis (L6, L7): the transport is derived, and `hpreFrame` disappears from consumer statements |
| backward compatibility | none needed | `IsMatvecRoutine`/`IsOrthRoutine` become `abbrev`s: `.run` changes type, so the 13 consumer files and 3 instance proofs change | additive: existing structures unchanged; `toBlockRoutine` and `mono` added; D3/D6 clean-ups are optional, separate PRs |
| (i) new routine for an existing certificate (e.g. MGS2 for `IsOrthRoutine`) | prove `run` from scratch | prove `run` against list-typed `G` | prove `run`, using L4, L8 and L9 for the effect clause; the guarantee proof is pure math |
| (ii) new consumer (e.g. GMRES/Arnoldi taking `IsOrthRoutine` and `IsMatvecRoutine`) | re-derive frames for each call | generic | typed `run` for values and its `writeBlocks` equation; L5 and L7 for frames and `pre`; L18 to read `w` as a column of `V` |
| (iii) new certificate (e.g. `IsTrsvRoutine`, `IsSmallEigRoutine`) | copy, 50 lines | a 10-line `abbrev`, but the user-facing API is on lists | a 50-line structure from the template, plus `toBlockRoutine` (S) and `mono` (S) |
| fit with `kcall` | — | close (`writeBlocks` lists) | the same: the effect clause *is* `kcall`'s `writeBlocks` form, so §2.3's bridge reuses `Interp.read_of_kcallStore_eq_some` |

**Recommendation: (b′).** It removes the cost that workers actually paid (frames, `pre`
transport, list-of-writes bookkeeping) without moving the guarantee into list indices. It is
additive on main. (a) is folded into it: the template and checklist of §4 apply to the typed
structures.

### 2.3 Kernels and certificates (option c)

The two notions are different on purpose.

* A **kernel contract** is part of the *model*. A target statement quantifies over every `I`
  whose kernel `o` meets `IsMatMulKernel ∧ IsMatMulErr` (S1cd's SIGN and DEFLATE targets). This
  is how a paper's "for any MM satisfying Definition 1.1" becomes a statement.
* A **routine certificate** is part of a *proof*. The consumer theorem is generic in the routine,
  and the registered tree fixes one routine (CGS2 in `StoredEntriesLanczosReorth`).

**(c1) kernel contract ⇒ certificate: recommended now.** A call `stmt (.kcall o tag dims ins
outs)` under `IsMatMulKernel I o L mm` and `IsMatMulErr dec u τ Ω μ mm`, with readable inputs,
writable disjoint outputs and inputs in range, satisfies a typed `IsMatMulRoutine` certificate.
The proof uses `IsMatMulKernel.kcallStore_eq`, `exec_kcall` and `executionComposable_single`, the
same pattern as `IsMatvecErr.isMatvecRoutine` (M, about 80 lines). Like that bridge it is per
kernel name, so it is unaffected by an oracle/kernel→operator map in the model
(`Computation-Oracles.md`). With it, a consumer written
against `IsMatMulRoutine` takes a black-box kernel, `gemm`, or a Strassen program as interchangeable
instances, and a target can still quantify over the kernel. A certificate is introduced only when a
consumer needs it (CONTRIBUTING §5.4, "interfaces are designed, not accreted"). The first candidate
is the S2 `eighProg` sign/deflate steps, if they are refactored to be MM-generic.

**(c2) certificate ⇒ kernel: deferred.** For a certified routine to *be* a kernel in the
`RunsWithin.subst` sense, `ImplementsKernel` demands `st'.store = s₁`: the routine must write the
exact words the abstract kernel would. That holds only if the routine's output words are a
function of its input blocks, so that one can define the kernel as that function. This needs a
**reads-only clause** (the run depends on the store only through the input blocks and the
read-only `pre` buffers). No certificate states it today, and proving it is a non-interference
induction over `Stmt` (L to H). It is needed only for a *cost target* whose tree contains a `kcall`
that we want to replace by a program. The accuracy side never needs it: by (c1), the consumer
already takes either.

## 3. Reusable proof infrastructure

Sizes: S ≤ 30 lines, M 30–100, L > 100. File: `NLAlib/Computation/RoutineFrames.lean` (new; E5/E6
allow it, since it has no Matrix vocabulary), except L15, which goes in
`Matrix/Computation/KernelContracts.lean`. "Replaces" names what the lemma would have saved.

| id | statement (informal; Lean in the comment below) | size | replaces |
|---|---|---|---|
| L1 | `def ReadsDecoded (s) (dec) (p) (b off : ℕ) (x : Fin N → ℝ) : Prop := ∀ i, ∃ w, s.read p b (off + i) = some w ∧ dec p w = x i`, with `ReadsDecoded.of_read_eq` (equal reads on the block ⇒ transfer) | S | the inline form (about 340 occurrences) |
| L2 | `def Writable (s) (p) (b off n : ℕ) : Prop := ∀ i < n, ∃ len, s.shape[b]? = some (p, len) ∧ off + i < len`, with `Writable.of_shape_eq` and `Writable.of_getElem?_shape_eq` (per-buffer) | S | the inline form (33), and the G5 "first 8 entries" transport |
| L3 | `Store.writeBlocks_cons_eq_some_iff`: a `writeBlocks` on a cons is a `writeBlock` then the rest (the `mid` form of `IsOrthRoutine`) | S | D4 conversions |
| L4 | **extensionality to block writes**: if `s'.shape = s.shape`, `s'` reads `ys[k]` on block `bs[k]` for each `k` (at tag `p`), the blocks are pairwise disjoint (`blockDisjoint`), and `s'` reads as `s` at every tag outside them, then `s.writeBlocks p bs ys = some s'` | M (60) | CGS2's private `eq_of_read_writeBlock_writeBlock` (two blocks, 40) and every frame-style ⇒ certificate conversion |
| L5 | **block writes to frame style** (on the equation, not on `IsBlockRoutine`): `s.writeBlocks p bs ys = some s'` ⇒ `s'.shape = s.shape ∧` read-back on each block `∧` reads unchanged outside (packages `shape_of_writeBlocks_eq_some`, `read_of_writeBlocks_eq_some`, `…_of_forall`) | S | consumer-side unpacking at each call (`StoreContext.succ` hypotheses) |
| L6 | `def IsFramed (pre : Store P K → Prop) (ro : List ℕ) : Prop := ∀ s s', pre s → (∀ b ∈ ro, s'.shape[b]? = s.shape[b]?) → (∀ q, ∀ b ∈ ro, ∀ i, s'.read q b i = s.read q b i) → pre s'`; `isFramed_true`, `IsFramed.and`, `isFramed_holdsDecoded` (with `[b]`), `isFramed_readsDecoded` | S×4 | `hpreFrame` hypotheses (G5, `StoreContext.succ`, `exec_loop`, `exec_lanczosReorthLoop`) |
| L7 | `IsFramed.of_writeBlocks`: `IsFramed pre ro`, `pre s`, `s.writeBlocks p bs ys = some s'`, every block in `bs` in a buffer not in `ro` ⇒ `pre s'`. Also `IsFramed.of_push_pop` (a scoped allocation) | S | the G5 transport, derived instead of assumed |
| L8 | **scoped scratch** (modelled on CGS2's `exists_exec_alloc`, which states it with a predicate `Q out.store.pop`): if for every `σ` with `σ.store = st.store.push (p, replicate len.eval none)` the body succeeds with some `out` such that `out.store.size = st.store.size + 1` and `∃ ys, st.store.writeBlocks p bs ys = some out.store.pop ∧ R ys`, every block in `bs` in a buffer below `st.store.size`, then `∃ out ys, exec I (.alloc p len body) st = some out ∧ st.store.writeBlocks p bs ys = some out.store ∧ R ys`. The arrays `ys` are existential, because the run produces them. Iterated form `…_alloc₂` for two scratch buffers | M (70) | the push/pop half of `exec_cgsPass_frame` (about 50 of its 90 lines), `exists_exec_cgs2` |
| L9 | **one block per iteration** (modelled on CGS2's `exists_exec_loop_write`, where the written word `v` with `Q k v` is existential): for pairwise disjoint blocks `bs` of length `n`, if for every `k < n`, every prefix `ys'` of length `k` with `R k ys'` and every state `s` with `st.store.writeBlocks p (bs.take k) ys' = some s.store`, iteration `k` succeeds with some `s'` and some `y` such that `s.store.writeBlock p bs[k] y = some s'.store ∧ R (k+1) (ys' ++ [y])`, and `R 0 []`, then `∃ out ys, exec I (forRange n body).run st = some out ∧ st.store.writeBlocks p bs ys = some out.store ∧ R n ys` | M (80) | `exists_exec_loop_write` (30), the dots loop of `exec_cgsPass_dots`, and the column-writing loops of the Lanczos-FRO commit phase |
| L10 | `structure IsBlockRoutine` (§2.1 b′); `IsMatvecRoutine.toBlockRoutine`, `IsOrthRoutine.toBlockRoutine` | S×3 | — |
| L11 | **sequencing**: `IsBlockRoutine I p pre₁ bs₁ r₁`, `IsBlockRoutine I p pre₂ bs₂ r₂`, `IsFramed pre₂ ro₂` with `bs₁` outside `ro₂`, and `pre₁ s → pre₂ s` ⇒ `IsBlockRoutine I p pre₁ (bs₁ ++ bs₂) (r₁ >>= fun _ => r₂)` (writable outputs carried by L2; uses `ExecutionComposable.bind`) | M (80) | the two-pass composition in `exec_cgs2_body`; any "routine after routine" consumer step |
| L12 | (on the equation) `Store.writeBlocks_append` (S); `Store.writeBlock_writeBlock_self`: writing the same block twice is the second write (S, 25) | S×2 | normal forms after L11 when a block is rewritten in place (CGS2 rewrites `wb`) |
| L13 | `IsOrthRoutine.mono` (parameters increased, mirroring `IsMatvecRoutine.mono`, via `IsOrthErr.mono`) | S | D8 |
| L14 | **charge independence for certificates**: if `routine.run` is one statement (`∀ k, ContT.run routine k = .seq X (k ())`), a certificate under `I` gives the same certificate under `{ I with charge := ch }` (from `exists_exec_withCharge_eq_some`; `composable` by `executionComposable_single`) | M (50) | `…_of_charge` twins (`exec_initPhase_of_charge`, `exec_commitPhase_of_charge`) when the routine is proved under unit charges |
| L15 | **(c1)** `IsMatMulKernel.isMatMulRoutine`: kernel contract ⇒ typed certificate for one `kcall` (defines `IsMatMulRoutine`, S, only together with its first consumer) | M (80) | — |
| L16 | `IsMatvecRoutine` guarantee name (CR5): `def IsMatvecBound (A) (c) (x y) : Prop := ‖toLp (A *ᵥ x - y)‖ ≤ c * ‖toLp x‖` with `mono`; the certificate field restated through it (definitional, so non-breaking) | S | D5 |
| L17 | **disjointness to the instance, at block level (CR4)**: `IsOrthRoutine'` with the three buffer inequalities removed from `run`; `IsRelErrSem.isOrthRoutine'_cgs2` assumes instead that the blocks `(Vb, 0, N*j)`, `(wb, wo, N)`, `(hb, ho, j)` are pairwise `blockDisjoint`. This admits `w` as the next column of `V` in the same buffer (Arnoldi/GMRES). It needs CGS2's pass lemmas re-checked at block level (`exec_cgsPass_frame` uses `hb ≠ wb ∧ hb ≠ Vb`) | S×2 (M if the pass lemmas need restating) | `IsOrthCall` and the `(by omega) (by omega) (by omega)` lambda in `exec_rounded_loop` |
| L18 | `HoldsDecoded s dec p b off V ↔ ∀ j, ReadsDecoded s dec p b (off + N * j) (fun i => V i j)` | S | needed by `IsOrthRoutine.toBlockRoutine` and by any consumer that reads `w` as a column of `V` |
| L19 | `Writable` from a workspace shape: `s.shape = ws → ws[b]? = some (p, len) → off + n ≤ len → Writable s p b off n`, tagged so that `simp [workspaceShape]` closes it | S | the `fun i hi => ⟨N, by simp [hs, workspaceShape], …⟩` lambdas in `exec_rounded_loop` |
| L20 | `blockDisjoint_iff`: `blockDisjoint (b, o, n) (b', o', n') = true ↔ b ≠ b' ∨ o + n ≤ o' ∨ o' + n' ≤ o` (decidable form for `omega`) | S | CR4 goals |

Totals: 20 items: S 14 (L1–L3, L5–L7, L10, L12, L13, L16–L20), M 6 (L4, L8, L9, L11, L14, L15),
no L. That is about 950 lines with the API lemmas counted inside each item.
**Pilot** (CR10): prove L1–L13 and L18–L20 first, then re-prove CGS2's run (`exec_cgsPass_frame`,
`exists_exec_cgs2`) and the Lanczos-FRO step frame on top of them, and record the line counts.
An earlier estimate here (785 → ~500 lines for CGS2) was optimistic. The private helpers that
L4, L8 and L9 replace total about 170 lines (`eq_of_read_writeBlock_writeBlock` 40,
`exists_exec_alloc` 10, `exists_exec_loop_write` 30, the alloc half of `exec_cgsPass_frame` about
50, `exists_exec_cgs2` about 35). The rest of the file is rounding composition, which b′ does not
touch. The larger saving is expected on the consumer side (Lanczos-FRO: `IsOrthCall`,
`hpreFrame`, the `StoreContext.succ` frame). If the pilot does not reach at least a 25% reduction
on the touched proofs, L8, L9 and L11 should be redesigned before contributors are
asked to use them.

```lean
-- L4 (shape of the statement)
theorem Store.writeBlocks_eq_some_of_read {s s' : Store P K} {p : P}
    {bs : List (ℕ × ℕ × ℕ)} {ys : List (Array K)} (hlen : List.Forall₂ (·.size = ·.2.2) ys bs)
    (hpw : bs.Pairwise fun x y => blockDisjoint x y = true) (hsh : s'.shape = s.shape)
    (hin : ∀ k x y, bs[k]? = some x → ys[k]? = some y → ∀ j < x.2.2,
      s'.read p x.1 (x.2.1 + j) = y[j]?)
    (hout : ∀ q b i, (∀ x ∈ bs, b ≠ x.1 ∨ i < x.2.1 ∨ x.2.1 + x.2.2 ≤ i) →
      s'.read q b i = s.read q b i) :
    s.writeBlocks p bs ys = some s'
```
The hypothesis `hout` is in the form `Interp.read_of_kcallStore_eq_some_of_forall` already uses.
This keeps the kernel and routine lemmas interchangeable.

## 4. Contributor guide (outline; to become CONTRIBUTING §5.6 once CR1 is decided)

### 4.0 What are you adding?

The guide opens with this table. The rungs differ in risk, and the re-pin consequence decides
who approves.

| you are adding | examples | what changes | re-pin | who approves | where the pattern is |
|---|---|---|---|---|---|
| a **primitive** (instruction, statement form, interpretation field) | `kcall`, `bindIdx`, `Dist.uniform` | `Stmt`/`FStmt`, `Interp`, `exec`, `staticCost`, `RunInv`, the substitution cases; a contract, an exact witness, `ImplementsOracle`/`ImplementsKernel` cases | **every** registered target | maintainer (AGENTS.md rules 1–2) | `docs/design/Computation.md`, "Adding a primitive" (ORACLE-MODEL OM6); CONTRIBUTING §5.5 carries only a pointer (CR12); not this guide |
| a **contract** (oracle or kernel) | `IsMatvecErr`, `IsMatMulKernel ∧ IsMatMulErr` | a model-level `Prop` that target statements quantify over | the targets that quantify over it | maintainer | `Matrix/Computation/KernelContracts.lean`; `docs/design/Computation-Oracles.md` for oracle maps and rectangular oracles |
| a **certified routine** (a certificate or an instance) | `IsOrthRoutine`, `isOrthRoutine_cgs2` | proof infrastructure only | none (no target reaches a certificate) | ordinary review | §4.1, §4.3 |
| a **consumer** | Lanczos-FRO, Arnoldi | a program generic in routine families, its run and accuracy theorems | none, until it proposes its own target (then the maintainer registers it) | ordinary review; the target by the maintainer | §4.2 |

### 4.1 Adding a routine that meets an existing certificate

*Example: MGS2 or Householder-based reorthogonalization for `IsOrthRoutine`; a CSR matvec for
`IsMatvecRoutine`.*

**Worked example to copy: `Matrix/Computation/MatvecRoutine.lean`** (58 lines). Its instance
theorem `IsRelErrSem.isMatvecRoutine_gemv` has `pre = HoldsDecoded store … matrix aOff A`,
disjointness on the theorem (`hda`, `hdx`), and `composable` by `executionComposable_single`.
The proof is the existing BLAS run lemma plus a 6-line conversion to the `writeBlock` form.

1. **Where.** The program goes in its topic file next to its mathematical definition (§5.5):
   `NLAlib/Matrix/Computation/ModifiedGramSchmidtProgram.lean`. The rounding-error mathematics
   goes in a separate file with no `exec` (`…RoundingError.lean`), as CGS2 does.
2. **What to prove**, in order:
   (a) the pure-math pass bounds: the guarantee predicate from the trace predicates (`IsDotTrace`
   style), with no store;
   (b) the run lemma in block-write form, using L8/L9/L4;
   (c) the instance theorem, `IsRelErrSem.is<Op>Routine_<impl>`: hypotheses are the
   arithmetic contract (`IsRelErrSem`, `AddsZeroExactly`), the size regime, and the operand
   disjointness (CR4). The conclusion is the certificate at explicit parameters, each parameter
   a named bound recorded in `docs/constants.toml`;
   (d) the exact run under `exactSem` (`exec_<impl>_exactSem`), which is the satisfiability
   witness and what the exact registered target uses;
   (e) if the routine enters a cost target, `staticCost` lemmas on its emitted tree
   (`<impl>.staticCost_count_le` style). Cost is syntactic (§1.2), so the certificate does not
   carry it.
3. **Naming.** `<impl>` for the builder (`cgs2`), `IsRelErrSem.is<Op>Routine_<impl>` for the
   instance, `<impl>Bound` for its parameter function (`cgsPassBound`).
4. **Tag.** The builder's docstring ends with `Algorithm: <id>`, where the id is the
   routine's algorithm (`gram-schmidt`), not the consumer's.
5. **Targets.** Only if the routine is also a stand-alone program with a published cost: propose
   a registered tree and target in the PR description (§5.5). An instance theorem is not a target
   and carries no `Result:` id unless it is a published accuracy result (rule E3).

### 4.2 Adding an algorithm that uses certified routines

*Example: Arnoldi/GMRES taking `IsMatvecRoutine` and `IsOrthRoutine`; Lanczos-FRO.*

1. **Parameterise the builder by routine families**, `mv : ℕ → IExp ℕ → Builder …` and
   `orth : ℕ → ℕ → IExp ℕ → Builder …`, indexed by step and operand offsets (the main pattern).
2. **Fix a workspace layout once**: a `workspaceShape` and a `StoreContext` invariant that lists,
   per buffer, what it holds. Assign operand blocks so every certificate's block disjointness is a
   closed `omega` goal (L20). Writability then follows by `simp` (L19).
3. **Take the certificates as hypotheses** of the run theorem, quantified over the executed
   steps only: `hmv : ∀ t < q, Is…Routine …`, `horth : ∀ t < q, …` (not `∀ t`, the form at
   four sites on main). Require `IsFramed pre ro` of the routine's `pre` (L6). Never ask the
   caller for a hand-written `hpreFrame`.
4. **Step lemma.** Call the routine's typed `run` once. Its values give the guarantee, and its
   `writeBlocks` equation gives the frame through L5/L7. Re-establish `StoreContext` from that
   equation.
5. **The analysis is certificate-generic.** Every accuracy statement depends only on the
   certificate's parameters. The concrete routine enters in one corollary, which instantiates
   the parameters (`exec_rounded_oracle_compiled` style).
6. **Targets.** A registered target fixes the concrete routine (`StoredEntriesLanczosReorth`
   uses CGS2). Its cost statement is about the compiled tree and is proved by `staticCost`
   (`staticCost_count_le`), not from the certificate. Draft the target statement in the PR; the maintainer registers it. A target that
   should hold "for any MM/QR" quantifies over a *kernel* contract in its statement (S1cd style),
   not over a routine certificate.

### 4.3 Adding a certificate

Only when a second consumer or a second implementation is in sight (§5.4). Checklist:

* [ ] `structure Is<Op>Routine` in `NLAlib/<Layer>/Computation/<Op>Routine.lean`. Use the Matrix
  layer if the guarantee uses Matrix vocabulary (E5); otherwise `NLAlib/Computation`.
* [ ] Fields `composable` and `run`, with the shape of §1.1: operands `(ℕ × IExp ℕ)`; parameters
  (fixed across calls) separate from inputs (quantified in `run`); `ReadsDecoded`/`HoldsDecoded`
  inputs; `Writable` outputs; effect as one `writeBlocks` list; disjointness *not* in `run`,
  and stated at block level (`blockDisjoint`) on the instance theorem.
* [ ] `pre` comes with `IsFramed pre ro` as a hypothesis of every instance and consumer theorem.
* [ ] Every certificate hypothesis of a consumer is quantified over the executed steps only
  (`∀ t < q`, not `∀ t`). The harness statement-review checklist should carry the same bullet.
* [ ] The guarantee is a **named** pure-math predicate (`Is<Op>Err`) in the topic's Perturbation
  or analysis file, with `mono` and the API lemmas the first consumer needs.
* [ ] `Is<Op>Routine.mono`, `.toBlockRoutine`.
* [ ] One instance and an **exact witness** (satisfiability).
* [ ] A kernel bridge (L15 style) if a kernel contract for the operation exists.
* [ ] A §5.3 vocabulary row: certificate, guarantee, instances.
* [ ] A design-note paragraph: why these parameters, which consumer needs them.

### 4.4 Attaching results in the explorer and the registry

* **`docs/targets.toml`.** Unchanged. Certificates and instance theorems are not targets. A
  consumer's registered target names its concrete tree, and the closure hash never reaches a
  certificate (verified for the two on main). Changing a certificate therefore needs no re-pin.
  Changing a kernel contract does.
* **Explorer (`~/work/explore`, `algorithms.toml`; `docs/design/algorithm-pages.md` on the
  explorer branch `design/algorithm-pages`).** An algorithm page today has *Uses / used by*,
  computed from `valueDeps` between tagged definitions. A consumer generic in a routine family
  does not *use* CGS2 in its definitions, so that section misses the relation. Proposed (CR8):
  * an overlay table `[certificates]` in `algorithms.toml` mapping each certificate structure to
    an operation title, for example `"NLAlib.Computation.IsOrthRoutine" = { title =
    "orthogonalization routine", guarantee = "NLAlib.IsOrthErr" }`;
  * the build classifies every theorem: one whose conclusion's head is a listed certificate is an
    **instance**, and it attaches to the algorithm of the builder in the conclusion
    (`cgs2` → *gram-schmidt*); one with a hypothesis whose head, *under binders*, is a listed certificate
    is a **consumer** (on main the hypotheses are `∀ t < q, IsOrthRoutine …` and
    `∀ t, IsMatvecRoutine …`), and it attaches to the consumer's algorithm;
  * a page section **Certified subroutines**. On a consumer page it lists each certificate it
    takes, the parameters, and the available instances with links ("Lanczos-FRO takes any
    `IsOrthRoutine`; instances: CGS2 (gram-schmidt), parameters $(\eta_0, 2c_1, 3c_1,
    2(\eta_0+c_1)^2)$"). On a routine page it lists **Meets**: the certificates and the consumers
    that can use it;
  * a ladder note (no new rung): a consumer's *Finite precision* rung counts its
    certificate-generic results.
  No library rule changes: the overlay is curated (a few entries), so no `Certificate:` docstring
  tag is needed.

## 5. Decisions for the maintainer

| id | question | options | recommendation | why |
|---|---|---|---|---|
| APPROVE | Approve this design and the infrastructure stage (L1–L20, pilot first)? | a approve / b not yet | a | Additive on main; it removes the costs workers paid in C3/C6/G3/G5 and gives contributors one template. |
| CR1 | How uniform should certified routines be? | a template + checklist only / b one generic `IsCertifiedRoutine` (guarantee on `List (Array K)`) / **b′ generic footprint `IsBlockRoutine` + typed certificates** | b′ | b′ shares every frame lemma and keeps the guarantees typed; b moves guarantees into list and array indices; a leaves every frame proof to be redone per routine. |
| CR2 | Backward compatibility with main's consumers? | **a additive: keep `IsMatvecRoutine`/`IsOrthRoutine` as they are, add `toBlockRoutine`/`mono`, migrate consumers when touched** / b restate both on the new layer now (13 consumer files, 3 instances) | a | Nothing registered reaches them, but rewriting 13 proven files has no payoff until a consumer is edited anyway. The "when touched" list: `hmv : ∀ t` → `∀ t < q` at `LanczosReorthProgramRoundedLoop.lean:336, 436, 545` and `LanczosReorthProgram.lean:253`; `IsOrthRoutine` to block-level disjointness (L17); and, if CR11 is adopted, the rectangular generalisation of the existing `IsMatvecRoutine` (not a new structure) in the L16 PR. |
| CR3 | How is a certificate's precondition `pre` carried by consumers? | a status quo (consumer supplies `hpreFrame`) / **b `IsFramed pre ro` as a hypothesis of instance and consumer theorems (not a field)** / c no `pre`; only `HoldsDecoded` read-only operands | b | It fixes the G5 class of bug at its source; c is too rigid (a stored sparse matrix is not one `HoldsDecoded` block). |
| CR4 | Where and in what form do operand disjointness conditions go? | **a on the instance theorem, at block level (`blockDisjoint` of (buffer, offset, length), as `kcall` and L4)** / b inside `run` as buffer inequalities (`IsOrthRoutine` today, a deliberate choice of `Krylov-LanczosReorth.md` §1.3) | a | Closed `omega` goals once, by L20, instead of at every call with adapters such as `IsOrthCall`. Block level admits the Arnoldi/GMRES pattern (`w` the next column of `V`, same buffer, disjoint offsets), which buffer inequalities forbid. New certificates now; `IsOrthRoutine` when next edited (L17). |
| CR5 | Must the decoded guarantee be a named predicate? | **a yes, for every certificate; add `IsMatvecBound` for the matvec one (definitional)** / b inline is fine | a | CONTRIBUTING §5.4: hypotheses and conclusions are named interfaces; consumers then reason with `mono` and the API. |
| CR6 | How do kernel contracts and certificates relate? | **a (c1) kernel contract ⇒ certificate lemmas now; (c2) certificate ⇒ `ImplementsKernel` deferred** / b both now (needs a reads-only clause, L–H) / c keep them unrelated | a | c1 is M-sized and makes consumers accept black-box kernels; c2 matters only for cost targets about `kcall` trees substituted by programs. |
| CR7 | Should certificates carry a cost and memory clause? | **a no: cost and memory are syntactic (`FStmt.staticCost`, compositional; `bounds_staticCost_of_exec_eq_some`)** / b a routine that enters a cost target ships a `staticCost` lemma on its emitted tree (`<impl>.staticCost_count_le`), as a guide step, not a certificate field | a, with b as the §4.1 step | Both Lanczos-FRO targets prove their counts by `staticCost_count_le`, never from `exec`. A cost clause in `run` would be charge-dependent and break L14. Cost-generic consumers are not expressible today (`staticCost` is on `FStmt`, certificates on `Builder`): §6 open problem. |
| CR8 | How does the explorer show certified subroutines? | **a curated `[certificates]` overlay + computed instance/consumer attachment + a "Certified subroutines" section** / b a library docstring tag `Certificate:` (new rule) / c nothing (Uses/used-by only) | a | Few certificates, so curation is cheap; no library rule change; c misses the relation entirely for generic consumers. |
| CR9 | Naming and placement convention? | **a `Is<Op>Routine` (execution certificate) / `Is<Op>Err` (decoded guarantee) / `IsRelErrSem.is<Op>Routine_<impl>` (instance) / `Is<Kernel>Kernel.is<Op>Routine` (bridge); file `<Layer>/Computation/<Op>Routine.lean`** / b another scheme | a | It is what main already does for orthogonalization; the matvec one fits except for its unnamed guarantee. |
| CR10 | Order of work? | **a pilot first: L1–L13 and L18–L20 + re-prove CGS2 run and Lanczos-FRO step frame on them; then the contributor guide (CONTRIBUTING §5.6, opening with the §4.0 table); L14–L17 with their first users** / b write the guide now, infrastructure later | a | The guide should point to lemmas that exist and whose savings were measured (the 25% threshold of §3; the CGS2 estimate is optimistic, about 170 helper lines are replaced). |
| CR11 | Generalise `IsMatvecRoutine` to rectangular `A : Matrix (Fin M) (Fin N)` (source block `N`, destination block `M`)? | **a only if rectangular oracles are adopted in the model (`docs/design/Computation-Oracles.md`, branch `design/oracle-model`), and then as a generalisation of the existing structure (same name, square as the case `M = N`) in the same PR as L16 (`IsMatvecBound`)** / b now, independently / c keep it square | a | The certificate layer needs no operator map (D1). This note owns the certificate generalisation; the oracle note owns only the rectangular contract `IsMatvecErrR` and its bridge to the certificate. L16 and the generalisation both restate `run`, so one touch of the 13 consumer files instead of two; no re-pin. |
| CR12 | Where is the pattern for adding a *primitive* documented? | **a the checklist in `docs/design/Computation.md`, "Adding a primitive" (instruction, contract, exact witness, `ImplementsOracle`/`ImplementsKernel`, substitution, `staticCost` and `RunInv` cases; ORACLE-MODEL OM6), with a one-line pointer in CONTRIBUTING §5.5 and from the routine guide's §4.0 table** / b inside the certified-routine guide (§5.6) | a | A primitive re-pins every target and is maintainer-side (AGENTS.md rules 1–2); a certified routine re-pins nothing. One checklist, owned by the model's design note, so the two guides do not diverge. |

## 6. Out of scope and open problems

**Open problem: cost-generic consumers.** "Lanczos-FRO costs $q$ times the routine's cost plus
$O(qN)$" cannot be stated today. `staticCost` is defined on `FStmt` (compiled trees), while
certificates and routine families live on `Builder`, and a registered tree fixes its routine.
A route would need a `staticCost` that is compositional over a builder parameter, or a compiled
routine-family tree. Neither is proposed here.

Out of scope: probabilistic routines (tape-consuming certificates, §1.2); reads-only clauses and
(c2); oracle→operator maps, rectangular oracles and `kcall` substitution in the model
(`docs/design/Computation-Oracles.md`). Block and strided operands (`kcall` is packed and contiguous,
M4). Migration of the CG and plain-Lanczos consumers to `toBlockRoutine` (CR2: when they are next
edited).

## 7. Review record

Fable, 2026-11-07 (`reports/Review-Fable-CertRoutines-Design.md`): approve with fixes. All 12
findings applied: (1) CR7 rationale (cost is syntactic `staticCost`; option b as a `staticCost`
lemma; cost-generic consumers to §6); (2) L8/L9 restated with existential outputs (CGS2's
`exists_exec_alloc`, `exists_exec_loop_write`); (3) CR4 at block level, D3 described as a
deliberate choice being reversed; (4) the `∀ t` vs `∀ t < q` checklist bullet and four migration
sites (D9, CR2); (5) operator map and rectangular matvec (D1, §2.3, CR11, referring to
`Computation-Oracles.md`); (6) the §4.0 table and CR12 (amended after the ORACLE-MODEL review, F3/F4: the primitive checklist lives in `Computation.md`, OM6; CR11 is a generalisation of the existing structure, and the oracle note owns only `IsMatvecErrR`); (7) b′'s value is the equation, and
`IsBlockRoutine` is reserved for L11/L14 (§2.1, D4); (8) the CR8 classifier looks under binders;
(9) inventory counts (about 340, 33, 13 files) and the CGS2 estimate corrected; (10) L18–L20 and
`MatvecRoutine.lean` as the worked example; (11) verified claims, no change; (12) decision
sheet: CR4/CR7 restated, CR11/CR12 added.
