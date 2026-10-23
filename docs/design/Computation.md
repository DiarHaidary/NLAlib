# Design note: computation, stage 1 (exact arithmetic, counts, memory, oracles, draws)

**Approved by the maintainer, 2026-10-23:** D1 option C (deep embedding); all other decisions as recommended; D16 to D19 (added after the first approval) as recommended.

**History.** Drafts 1 to 6, 2026-10-22 and 23, each after a bounded review. The fourth draft's
decisions (D1 to D15) were approved on 2026-10-23. D16 to D19, added for the maintainer's
requirement to reduce higher-level error models to bit operations ("we want to be able to reduce
certain higher level models of error to bit operations easily"), were approved the same day.
Targets: Hutch++ in stage 1, Lanczos in stage 1b.

**Summary.** Algorithms are small programs that work on memory buffers as BLAS code does. They
allocate scoped buffers, overwrite them in place, call BLAS kernels, draw random numbers, and
multiply blocks of vectors by the matrix through an oracle. Running a program gives its result,
its counts and its memory. One proved theorem replaces any scalar instruction or oracle call by a
certified implementation; comparisons, read-only reads and draws are kept. The result is the
same, and the costs are substituted kind by kind. This gives dense and sparse matvecs from the
oracle, and integer and bit operations from floating (here fixed-point) arithmetic. An error
analysis against a rounding contract, which now requires the operations to succeed in range and
not only to be accurate, thus reduces to a word-level program and a bit-operation count by
substitution. Hutch++ keeps its results: exact value, 2 loads, `2k + ℓ` matvecs, operation and
memory counts, and the Gaussian tail with no new probability. Programs print as NumPy and run in
Lean with `Float`.

**What was elaborated and run.** Every Lean definition and statement below was elaborated
during the design, against the library at `88016e3`, in scratch files that the stage-1 skeleton
ports into `NLAlib/Computation/` and the topic files of §11. The core (syntax, semantics, the
substitution theorem) elaborated with no `sorry`, using only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

Proved:
* The substitution theorem `RunsWithin.subst` with `exec_subst_sim`. Its read-only hypothesis is
  now general: the concrete read-only data extends the abstract data, with an identity cost on
  `rom` reads. So substitutions chain, and sparse Hutch++ can be taken on to the bit level.
* The oracle corollary `RunsWithin.substOracle`.
* `isRelErrSem_exactSem`: exact real arithmetic meets the **full** contract (error and success
  clauses, every operation family).
* `not_isRelErrSem_failSem`: the always-failing semantics does not meet it.
* The transfer lemma, the Gaussian tail with draws, and sparse Hutch++. These three rest on the
  stubbed realisations, certificates and tape laws.

Statements elaborated with `sorry`, for the skeleton (eleven), plus a deliberately cheating
realisation kept as the E3 test fixture:
* the kernel specifications `exec_dot` and `exec_axpy`;
* the frame lemma `Holds.write`;
* the Hutch++ realisation;
* the two tape laws;
* the COO certificate;
* the two Lanczos realisations;
* the fixed-point certificate and the fixed-point error contract.

Runs, unchanged:
* The fixed-point example gives the same word at both levels.
* `Float` and NumPy reproduce the table.
* The E1 and E3 checks give the same verdicts.

---

## 1. Decisions (approved 2026-10-23)

### D1. Encoding: structured programs over buffers, two-sorted PHOAS (option C)

Why C was chosen. Tracking memory (point 1) ruled out values held as host data (A). The free
monad over buffer operations (B) met every point except size-generic emission (point 6) and
syntactic control cost for the bit-cost stage. C buys both, for about 900 to 1,500 more lines.
The maintainer asked for code generation, so C was chosen. A first-order deep embedding (D)
gave nothing over C.

### D3. The run: deterministic, state-passing, partial oracles, random tape

`exec I s st` is a deterministic function into `Option`. The interpretation `I` holds:
* the value semantics;
* the charge per kind;
* the tape;
* the oracles, partial (`none` marks an invalid query);
* the read-only data and its size.

Randomness comes from the tape (D12), so the run is a function of `ω`. Still out of reach:
stateful adversarial oracles. Alternatives: a monadic or measure-valued run. Recommendation: this
run.


### D4. Oracles: block calls counted as loads and matvecs; implementations in their own files

* `apply o p dst dOff src sOff cols` computes `A_o · X` for an `N × cols` block. It charges one
  `load o` and `cols` counts of `matvec o`.
* Oracle names carry their own matrices: `exactInterp (A : ι → Matrix (Fin N) (Fin N) 𝕜) ξ`. So
  `Aᴴ` is a second name whose matrix the theorem sets to `(A o)ᴴ`.
* The algorithm theorem states loads, matvecs and its own operations only (point 2).
* An implementation is certified once, by `ImplementsOracle`, and composition is the proved
  theorem:

The current certificates and substitution theorems are displayed under D18 (oracle calls and
scalar instructions are substituted by one theorem; the oracle theorem is its corollary).

The review's four objections are each a hypothesis or a change of form:
* (a) Both interpretations use the standard charge (`hc`, `hc'`).
* (b) The concrete read-only data extends the abstract data (`hrom`; for the oracle corollary,
  the abstract interpretation has none), so a program that reads `rom` cannot succeed abstractly
  and then fail concretely.
* (c) The conclusion keeps the store, tape positions and current memory of an abstract final state
  satisfying `Q`, not `Q` itself, because the concrete peak and counts differ. In practice `Q`
  reads output cells, so it transfers.
* (d) The certificate quantifies over index expressions, as `substOracle` passes them.

The proof is a simulation, `Sim`: equal store, tape and current memory; concrete count at most
the substituted abstract count; concrete peak at most abstract peak plus scratch; and the
abstract invariant that current memory is at most peak. Alternatives: implementation data as an
input buffer (every address shifts, and the proof needs a store renaming); one effect per access
mode. Decision: as above, in the general form of D18.


### D7. Layer and placement

`NLAlib/Computation/` at layer 0 holds the syntax, semantics, interface, composition, exact
semantics and layout, BLAS, and the dense and COO implementations; it imports Mathlib and
ForMathlib only. Programs live with their specifications (`GramSchmidtProgram.lean`,
`HutchPlusPlusProgram.lean`, `Krylov/Processes/LanczosProgram.lean`). The tape laws go in
`RandomMatrix/Tape.lean`. The emitter and the `Float` interpreter go in a tools library
`NLAlibTools` (flag).


### D8. Precision tags, checked at run time

Tags label buffers and operations; a mismatch fails. Each interpretation has one carrier: `𝕜` at
the exact level, unbounded `ℤ` words at the format and word levels (D16), where every format and
integer width is a tag decoded from words. **What is lost**: every realisation must discharge tag-mismatch and
out-of-bounds failures explicitly, at every write. The kernel specifications carry them as the
hypothesis that the final write succeeds (`h₁ : st.store.write … = some s₁`). Alternative: a store
typed by tags (dependent arrays), which removes the tag check but not the bounds check, and is
heavier in every lemma. Recommendation: runtime tags.


### D9. Index layout: flat column-major `ℕ` inside programs, `Fin N` in theorems

Realisations are stated at `Fin N`; a general `Fintype n` reaches them through reindexing lemmas
for the specifications. `hutchpp_reindex` and `lanczosState_reindex` are new work, about 150
lines, now in the size table. Alternative: a `FinEnum` layout map in every realisation, which
needs the same lemmas. Recommendation: `Fin N` plus reindexing.


### D11. Memory model: scoped allocation, two-sorted variables (memory in bits: D17)

* **Two sorts (new; the fix for the forged handle).** `Stmt P ι VB VI`: `alloc` binds a handle of
  sort `VB`, `loop` binds an index of sort `VI`, `IExp VI` is index arithmetic, and
  `Cell VB VI` pairs a handle with an index. A loop variable cannot be used as a handle, and a
  handle cannot enter index arithmetic: both are type errors (checked). The emitter prints
  `b3[i2]`, never `i2[0]`.
* **What the scoping claim covers, exactly.** For a program that is generic in `VB` and `VI` and
  passes E1, every handle it uses is either a parameter (an input buffer, live for the whole run)
  or bound by an enclosing `alloc`, whose buffer is live throughout the body. Hence no use after
  free, no double free (there is no `free`), and no leak (the buffer is popped when the body ends).
  It does not cover:
  * interpreter-level terms at `VB := ℕ` (handles can be any number there; E1 rejects such
    definitions as programs);
  * the caller passing wrong input addresses (a failure or aliasing at run time);
  * implementation files, where `cooImpl` takes a host pattern.
* Alternative: explicit `free` with non-nested lifetimes, which no target needs.
* Units: cells per tag. Fresh cells are uninitialised, and reading one fails.


### D12. Random draws from an i.i.d. tape

`draw p d dst` writes the next tape value of distribution `d` and charges `draw p d`; the tape has
law `iidSequence` per distribution. The tape laws (`hasLaw_tapeMatrix_of_hasLaw_iidSequence`,
`indepFun_tapeMatrix_of_hasLaw_iidSequence`) need an injective-reindexing lemma for
`iidSequence`, which `Probability/Law.lean` lacks; it is included in the 200-line estimate.


### D13. BLAS kernels: derived programs inside `named` nodes

Each kernel has one specification of five parts: value, frame, tape, memory and counts. Offsets
and lengths are index expressions with `eval` hypotheses. Kernels that are not elementwise carry
disjointness hypotheses; in-place kernels allow exact aliasing and forbid partial overlap
(`exec_axpy`).


### D14. Accounting for read-only data

`Interp.romSize : P → ℕ` is the constant memory of an implementation's data. `RunsWithin` bounds
`peak + romSize`, and the composition theorem adds `I'.romSize` (proved). The sparse corollary
therefore certifies `2N(k + ℓ) + 5 + nnz`; without `romSize` it would certify
`2N(k + ℓ) + 5` while holding `nnz` values.
* Inputs and outputs are in the initial store and count from the start.
* The abstract oracle's `A` lives outside the store and is uncounted, as an oracle should be.
* An implementation's `A` is read-only data, counted through `romSize`.
* Index storage of a sparse pattern stays uncounted host data until integer buffers exist.

Alternative: read-only data uncounted, stated plainly. Recommendation: counted, as implemented.


### D15. Lanczos scope: designed now, proved in stage 1b

The program, its counts, memory and realisation statements against `lanczosState` exist now, and
Lanczos shaped the signature (`mod`, `re`, `whileFuel`). The proofs (a loop invariant over three
rotating slots, about 700 lines) are stage 1b, after Hutch++ has exercised the core and BLAS
lemmas. Alternative: both in stage 1, which delays the first complete result by the Lanczos proof.
Recommendation: 1b.


### Settled: D2, D5, D6, D10

* D2: failing operations. Also failing: uninitialised reads, out of bounds, tag mismatch, an
  invalid oracle query, running out of fuel.
* D5: `RunsWithin` is an upper bound (now on counts and on `peak + romSize`).
* D6: in-place rank-revealing modified Gram–Schmidt, realised with no rank hypothesis.
* D10: universe 0.
* Operation kinds, names (`<spec>Prog`, `runsWithin_<spec>Prog`, `<spec>Count`), and `ℓ ≥ 1`
  for `hutchppProg`.


### Decisions added for bit-level reduction (approved 2026-10-23)

Four decisions, all from the requirement to reduce higher-level error models to bit operations.

### D16. The carrier of word-level interpretations

The carrier `K` is a parameter of `Interp`, the store and the run. The exact interpretation keeps
`K := 𝕜`. `RunsWithin.subst` links only interpretations with the **same** `K` (its simulation
uses the identity store relation). So "one carrier" always means one carrier per interpretation:
the exact level (`𝕜`) and the word level are related through the contract and its decoding
(§7), never by substitution.

The options weighed (D8 follows the decision):
* **(i) Unbounded `ℤ` words, decoded per tag (chosen).** A floating cell holds its bit
  pattern as an integer, and integer and bit cells are integers too. The semantics enforces each
  tag's range and width, failing on overflow or wrapping, as chosen per tag. `convert` is
  reinterpretation or conversion. Substitution keeps the identity store relation, so floating
  operations reduce to integer programs by the proved theorem.
  * Stage 1 cost: none; elaborated.
  * Stage 2 cost: per-format encode and decode, and the proof that each format semantics meets the
    contract.
* **(ii) A sum or dependent carrier** (`Σ p, α p`, or an inductive of values). Values are typed
  by format, and `convert` is explicit encode and decode. Reduction to bits is then a data
  refinement: a store relation between carriers, and a second simulation proof (estimate 500
  lines), which §7.3 needs anyway for one-bit-per-cell layouts.
  * Stage 1 cost: none.
  * Stage 2 cost: that simulation, plus heavier lemmas everywhere a cell is read.
* **(iii) `BitVec` per width** (Lean's `BitVec w`, with `bv_decide` available). Widths are exact
  in types and overflow is impossible by construction. But the carrier is dependent as in (ii),
  with the same data-refinement cost, plus `BitVec` arithmetic in every word-level proof. Proofs
  under (i) can still pass through `BitVec` inside decode lemmas.

### D17. Memory in bits

What was added:
* `Interp.width : P → ℕ`, bits per cell;
* the state fields `curW` and `peakW`, current and peak bits over all tags, updated at allocation
  and freeing;
* a sixth part in every kernel specification: bit memory unchanged, bit peak raised by at most
  the scratch.

What it means:
* `RunsWithin` itself bounds cells only: its bound `m` has no bit component, and `romSize` has no
  bit form.
* The substitution theorem bounds the concrete `peakW` **relative to the abstract final state's
  `peakW`** plus the bit scratch. It is not an absolute bound.
* `exactInterp` has width 0, so bit memory is 0 at the exact level and meaningful only for
  word-level interpretations.

Alternatives:
* no joint tracking: the sum of per-tag peaks times widths is a sound but loose upper bound;
* a bit component in `RunsWithin` itself, which changes every statement;
* a separate predicate `RunsWithinBits` with `romBits = Σ romSize · width`, added when the first
  word-level theorem needs it.

Decision: keep the fields now (adding them later would change every kernel specification),
keep `RunsWithin` in cells, and add `RunsWithinBits` with the first word-level result.

### D18. General substitution, the new operations, and the changed certificates

What was added:
* `Stmt.subst implI implO`, `substCountG`, `ImplementsInstr`, and `RunsWithin.subst` (proved),
  with the oracle theorem as its corollary.
* `BinOp.shl`, `shr`, `band`, `bor`, `bxor`, `UnOp.bnot`, and the instruction
  `convert p q dst src`.
* The read-only hypothesis generalised to "the concrete data extends the abstract data", with
  `hcostRom`.
* D4's certificate and theorem changed as follows (current signatures):
```lean
def ImplementsOracle (I : Interp P ι K (OpCount P ι)) (I' : Interp P ι' K (OpCount P ι'))
    (impl : ι → P → ℕ → IExp ℕ → ℕ → IExp ℕ → IExp ℕ → Stmt P ι' ℕ ℕ)
    (cost : OpKind P ι → OpCount P ι') (scratch : P → ℕ) (scratchW : ℕ) : Prop :=
  ∀ o p dst dOff src sOff cols st X Y s₁,
    st.store.readBlock p src sOff.eval (I.height o * cols.eval) = some X →
    I.oracle o cols.eval X = some Y → st.store.writeBlock p dst dOff.eval Y = some s₁ →
    ∃ st', exec I' (impl o p dst dOff src sOff cols) st = some st' ∧ st'.store = s₁ ∧
      st'.pos = st.pos ∧ st'.cur = st.cur ∧ st'.curW = st.curW ∧
      st'.cnt ≤ st.cnt + (cost (.load o) + cols.eval • cost (.matvec o)) ∧
      (∀ q, st'.peak q ≤ max (st.peak q) (st.cur q + scratch q)) ∧
      st'.peakW ≤ max st.peakW (st.curW + scratchW)

def ImplementsInstr (I : Interp P ι K C) (I' : Interp P ι' K (OpCount P ι'))
    (implI : Instr P ℕ ℕ → Stmt P ι' ℕ ℕ) (cost : OpKind P ι → OpCount P ι')
    (scratch : P → ℕ) (scratchW : ℕ) : Prop :=
  ∀ i st r, i.run I.sem I.tape st.store st.pos = some r →
    ∃ st', exec I' (implI i) st = some st' ∧ st'.store = r.1 ∧ st'.pos = r.2 ∧
      st'.cur = st.cur ∧ st'.curW = st.curW ∧ st'.cnt ≤ st.cnt + cost i.kind ∧
      (∀ q, st'.peak q ≤ max (st.peak q) (st.cur q + scratch q)) ∧
      st'.peakW ≤ max st.peakW (st.curW + scratchW)

theorem RunsWithin.subst (hcmp : I'.sem.cmp = I.sem.cmp)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (hc' : ∀ k, I'.charge k = Finsupp.single k 1)
    (hwidth : I'.width = I.width) (hrom : ∀ i v, I.rom i = some v → I'.rom i = some v)
    (hcostCmp : ∀ p, cost (.cmp p) = Finsupp.single (.cmp p) 1)
    (hcostRom : ∀ p, cost (.rom p) = Finsupp.single (.rom p) 1)
    (himplI : ImplementsInstr I I' implI cost scratch scratchW)
    (himplO : ImplementsOracle I I' implO cost scratch scratchW)
    {s} {st₀} (h0 : st₀.cnt = 0) (hcp : ∀ q, st₀.cur q ≤ st₀.peak q)
    (hcpW : st₀.curW ≤ st₀.peakW) {c} {m} {Q} (h : RunsWithin I s st₀ c m Q) :
    ∃ st₁', exec I' (s.subst implI implO) (st₀.withCnt 0) = some st₁' ∧
      st₁'.cnt ≤ substCountG cost c ∧
      (∀ q, st₁'.peak q + I'.romSize q ≤ m q + scratch q + I'.romSize q) ∧
      (∃ st, Q st ∧ st₁'.store = st.store ∧ st₁'.pos = st.pos ∧ st₁'.cur = st.cur ∧
        st₁'.peakW ≤ st.peakW + scratchW)

theorem RunsWithin.substOracle (hsem : I'.sem = I.sem) (htape : I'.tape = I.tape)
    (hc) (hc') (hwidth : I'.width = I.width) (hrom : ∀ i, I.rom i = none)
    (himpl : ImplementsOracle I I' implO (substKind cost) scratch scratchW)
    {s} {st₀} (h0 : st₀.cnt = 0) (hcp : ∀ q, st₀.cur q ≤ st₀.peak q)
    (hcpW : st₀.curW ≤ st₀.peakW) {c} {m} {Q} (h : RunsWithin I s st₀ c m Q) :
    RunsWithin I' (s.substOracle implO) (st₀.withCnt 0) (substCount cost c)
      (fun q => m q + scratch q + I'.romSize q)
      (fun st' => ∃ st, Q st ∧ st'.store = st.store ∧ st'.pos = st.pos ∧ st'.cur = st.cur)
```

Alternatives:
* oracle-only substitution (the fourth draft's D4), with scalar refinement as a separate
  theorem in stage 2;
* bit operations as a separate instruction family typed by width (natural with D16 (iii)).

Decision: as implemented. It is one theorem for every substitution, and it is proved.

### D19. The shape of error contracts

An error-only `IsRelErrSem` (the fifth draft's) had only an error clause, for binary arithmetic. The semantics
that always fails met it, so a contract-level theorem asserting success (as `RunsWithin` does)
was unprovable. The proposal's own warning applies: "if it succeeds it is accurate" is not
enough.

The contract is now a structure with an error clause and a **success clause** per operation
family, under a range predicate `safe : P → ℝ → Prop`:
* arithmetic: `bin_err`, and `bin_ok` (succeeds when the exact result is in range, the divisor
  nonzero);
* literals: `lit_err`, `lit_ok`;
* `neg`, `conj`, `re`: exact and total on real decodings;
* `sqrt`: `sqrt_err`, `sqrt_ok` (on nonnegative decodings);
* comparisons: exact on decoded values (Gram–Schmidt branches on them);
* `convert`: relative error at the target tag, succeeding when in range there.

Both are proved: `isRelErrSem_exactSem` (exact real arithmetic meets the full contract with
`u = 0` and every value in range, for `𝕜 = ℝ`), and `not_isRelErrSem_failSem`.

Variants to define in stage 2 with the same shape: relative error with underflow, absolute error,
and stochastic mean-zero error. Alternatives:
* error-only contracts: unsound for theorems that assert success;
* no contracts, only specified formats: each format would be analysed separately;
* relational (nondeterministic) semantics: these need a run over sets of states.

Decision: the clause structure, one per error model.

---
## 2. The model in one page

(D18 adds `convert` and the integer and bit operations to the instruction set, and D17 the width
and bit-memory fields.)

```lean
inductive Instr (P VB VI : Type) where          -- each writes one destination cell
  | lit (p : P) (dst : Cell VB VI) (q : ℚ) | litIdx (p : P) (dst : Cell VB VI) (e : IExp VI)
  | bin (p : P) (b : BinOp) (dst x y : Cell VB VI) | un (p : P) (u : UnOp) (dst x : Cell VB VI)
  | copy (p : P) (dst src : Cell VB VI) | draw (p : P) (d : Dist) (dst : Cell VB VI)
inductive Stmt (P ι VB VI : Type) where
  | skip | seq (s t : Stmt P ι VB VI) | instr (i : Instr P VB VI)
  | apply (o : ι) (p : P) (dst : VB) (dOff : IExp VI) (src : VB) (sOff cols : IExp VI)
  | rom (p : P) (dst : Cell VB VI) (i : IExp VI)
  | alloc (p : P) (len : IExp VI) (body : VB → Stmt P ι VB VI)
  | loop (n : IExp VI) (body : VI → Stmt P ι VB VI)
  | whileFuel (fuel : IExp VI) (p : P) (c : CmpOp) (x y : Cell VB VI) (body : Stmt P ι VB VI)
  | ite (p : P) (c : CmpOp) (x y : Cell VB VI) (t e : Stmt P ι VB VI)
  | named (name : String) (args : List (Arg VB VI)) (body : Stmt P ι VB VI)
```

* The scalar instructions form one constructor with an interpretation-independent kind
  (`Instr.kind`). That made the composition proof uniform over them.
* The store is a stack of tagged buffers of optional cells.
* `exec` runs at `VB := ℕ`, `VI := ℕ`.
* `RunsWithin I s st₀ c m Q` means: success, counts at most `c` more than at the start,
  `peak + romSize ≤ m` per tag, and `Q` of the final state.
* Counts are `OpKind P ι →₀ ℕ`, with kinds `bin`, `un` (`neg`, `conj`, `re`, `sqrt`), `lit`,
  `cmp`, `copy`, `draw`, `rom`, `load`, `matvec`.

## 3. Objects (§5.3 rows)

| Concept | Spelling | Bridge |
|---|---|---|
| program | `Computation.Stmt P ι VB VI` (handles `VB`, indices `VI`), `Instr P VB VI` | none; Mathlib has no syntax for imperative programs (searched) |
| `do` notation | `Computation.Builder P ι VB VI β := (β → Stmt P ι VB VI) → Stmt P ι VB VI` | Mathlib's `ContT (Stmt P ι VB VI) Id β` is the same type; the skeleton defines `Builder` as that abbreviation, so no deviation arises |
| index expression, cell | `IExp VI`, `Cell VB VI` | none |
| store, state, interpretation, run | `Store P K`, `St P K C` (with `curW`, `peakW`), `Interp P ι K C` (with `rom`, `romSize`, `width`), `exec` | none |
| value semantics | `ScalarSem P K`; exact `exactSem` | none |
| interface | `RunsWithin I s st₀ c m Q` | none |
| counts | `OpCount P ι`, weights `Finsupp.weight`, `substCountG`, `substCount` | Mathlib `Finsupp` |
| layout | `flatten`, `unflatten`, `tapeMatrix x off N k : Matrix (Fin N) (Fin k) 𝕜`, `Holds` | `Matrix.of` |
| oracle semantics | `matOracle A`, `exactInterp (A : ι → Matrix …) ξ` | `Matrix` multiplication |
| substitution | `Stmt.subst`, `Stmt.substOracle`, `ImplementsInstr`, `ImplementsOracle`, `Sim`, `St.withCnt` | none |
| implementations | `denseImpl`, `cooImpl`, `cooMatrix`, `cooInterp`, `cooCost` | none |
| contracts | `IsRelErrSem u dec safe sem` | none |
| tape law | `HasLaw ξ (iidSequence ν) μ` | the library's `iidSequence` |
| BLAS | `dot`, `axpy`, `scal`, `rscl`, `copyv`, `nrm2`, `gemv`, `gemm` (and `ger`) | none |

## 4. BLAS and the kernel specification family

The kernels are `dot`, `axpy`, `scal`, `rscl`, `copyv`, `nrm2`, `gemv` and `gemm`, with `ger` to
add. Specifications now take index-expression arguments with `eval` hypotheses. Elaborated:

```lean
theorem exec_dot (I) (hI : I.sem = exactSem) (hc : ∀ k, I.charge k = Finsupp.single k 1) (p : P)
    (st) (dst : Cell ℕ ℕ) (x : ℕ) (xo : IExp ℕ) (y : ℕ) (yo n : IExp ℕ) (xs ys : ℕ → 𝕜)
    (hx : ∀ i < n.eval, st.store.read p x (xo.eval + i) = some (xs i))
    (hy : ∀ i < n.eval, st.store.read p y (yo.eval + i) = some (ys i))
    (hdx : dst.buf = x → ∀ i < n.eval, dst.idx.eval ≠ xo.eval + i)
    (hdy : dst.buf = y → ∀ i < n.eval, dst.idx.eval ≠ yo.eval + i) (s₁)
    (h₁ : st.store.write p dst.buf dst.idx.eval (∑ i ∈ Finset.range n.eval, star (xs i) * ys i)
      = some s₁) :
    ∃ st', exec I (dot p dst x xo y yo n).run st = some st' ∧ st'.store = s₁ ∧ st'.pos = st.pos ∧
      st'.cur = st.cur ∧ st'.cnt = st.cnt + (n.eval • (single (.un p .conj) 1 +
        single (.bin p .mul) 1 + single (.bin p .add) 1) + single (.lit p) 1) ∧
      st'.peak = Function.update st.peak p (max (st.peak p) (st.cur p + 1))

theorem exec_axpy … (hay : a.buf = y → ∀ i < n.eval, a.idx.eval ≠ yo.eval + i)
    (hxy : x = y → ∀ i < n.eval, ∀ j < n.eval, xo.eval + i = yo.eval + j → i = j) (s₁)
    (h₁ : st.store.writeBlock p y yo.eval ((List.range n.eval).toArray.map
      fun i => av * xs i + ys i) = some s₁) : ∃ st', … ∧ st'.store = s₁ ∧ …

theorem Holds.write (h : Holds s p b off M) (hw : s.write p' b' i' v = some s')
    (hout : b' = b → i' < off ∨ off + N * k ≤ i') : Holds s' p b off M
```

Algorithm proofs address matrices through flat indices `off + i + N * j`. The side conditions are
nonlinear, so `omega` will not close them. A column-arithmetic lemma set handles them (`i + N * j`
injective for `i < N`, columns disjoint, a block lies below `off + N * k`); it is now in the
`Exact.lean` estimate.

## 5. Programs and statements (elaborated)

**Hutch++** (two loads: the second product is batched, `A [Q | G']`; without batching, 3 loads and
the same `2k + ℓ` matvecs; batching costs the `N(k + ℓ)` destination that sets the peak):

```lean
/-- **Hutch++ as a program.** It draws an `N × k` sketch and `N × ℓ` probes from the tape `d`,
forms `Y = A S` (load 1), orthonormalises `Y` in place by rank-revealing modified Gram–Schmidt,
projects the probes in place, forms `A [Q G']` (load 2), and writes
`tr(Qᴴ A Q) + tr(G'ᴴ A G') / ℓ` into `out`. -/
def hutchppProg (p : P) (o : ι) (d : Dist) (N k ℓ : IExp VI) (out : Cell VB VI) :
    Builder P ι VB VI Unit := do
  let B ← alloc p (N * (k + ℓ))
  scope do
    let S ← alloc p (N * k)
    forRange (N * k) fun i => ins (.draw p d ⟨S, .var i⟩)
    stmt (.apply o p B 0 S 0 k)
  forRange (N * ℓ) fun i => ins (.draw p d ⟨B, N * k + .var i⟩)
  let t ← alloc p 2
  forRange k fun j => do
    orthAgainst p N B (.var j) B (N * .var j) ⟨t, 0⟩
    dot p ⟨t, 1⟩ B (N * .var j) B (N * .var j) N
    ins (.lit p ⟨t, 0⟩ 0)
    ifThenElse p .eq ⟨t, 1⟩ ⟨t, 0⟩ (pure ()) do
      ins (.un p .sqrt ⟨t, 1⟩ ⟨t, 1⟩)
      rscl p ⟨t, 1⟩ B (N * .var j) N
  forRange ℓ fun j => orthAgainst p N B k B (N * (k + .var j)) ⟨t, 0⟩
  let C ← alloc p (N * (k + ℓ))
  stmt (.apply o p C 0 B 0 (k + ℓ))
  ins (.lit p out 0)
  forRange k fun j => do
    dot p ⟨t, 0⟩ B (N * .var j) C (N * .var j) N
    ins (.bin p .add out out ⟨t, 0⟩)
  ins (.lit p ⟨t, 1⟩ 0)
  forRange ℓ fun j => do
    dot p ⟨t, 0⟩ B (N * (k + .var j)) C (N * (k + .var j)) N
    ins (.bin p .add ⟨t, 1⟩ ⟨t, 1⟩ ⟨t, 0⟩)
  ins (.litIdx p ⟨t, 0⟩ ℓ)
  ins (.bin p .div ⟨t, 1⟩ ⟨t, 1⟩ ⟨t, 0⟩)
  ins (.bin p .add out out ⟨t, 1⟩)
```

**Lanczos** (stage 1b for the proofs; three vectors rotate through slots `j mod 3`; breakdown by
an exact zero test, matching the library's junk value `0⁻¹ = 0` in `lanczosStep`):

```lean
/-- One Lanczos step from slot `cur` (previous vector in slot `prev`, `s[1] = β_j`) into slot
`nxt`; writes `α_j`, `β_{j+1}`. `s[3]` holds a literal zero. -/
def lanczosStepProg (p : P) (o : ι) (N : IExp VI) (W : VB) (cur prev nxt : IExp VI) (s : VB)
    (alphaCell betaCell : Cell VB VI) : Builder P ι VB VI Unit := do
  stmt (.apply o p W nxt W cur 1)
  ins (.un p .neg ⟨s, 0⟩ ⟨s, 1⟩)
  axpy p ⟨s, 0⟩ W prev W nxt N
  dot p ⟨s, 0⟩ W cur W nxt N
  ins (.un p .re ⟨s, 0⟩ ⟨s, 0⟩)
  ins (.copy p alphaCell ⟨s, 0⟩)
  ins (.un p .neg ⟨s, 0⟩ ⟨s, 0⟩)
  axpy p ⟨s, 0⟩ W cur W nxt N
  dot p ⟨s, 2⟩ W nxt W nxt N
  ins (.un p .sqrt ⟨s, 1⟩ ⟨s, 2⟩)
  ins (.copy p betaCell ⟨s, 1⟩)
  ifThenElse p .eq ⟨s, 2⟩ ⟨s, 3⟩ (pure ()) (rscl p ⟨s, 1⟩ W nxt N)

/-- Start: slot 0 holds `b / ‖b‖` (or `b = 0`), slot 2 holds zero, `β_0 = 0`. -/
def lanczosInit (p : P) (N : IExp VI) (b : VB) (W s : VB) : Builder P ι VB VI Unit := do
  ins (.lit p ⟨s, 3⟩ 0)
  forRange N fun i => ins (.lit p ⟨W, 2 * N + .var i⟩ 0)
  copyv p b 0 W 0 N
  dot p ⟨s, 2⟩ b 0 b 0 N
  ifThenElse p .eq ⟨s, 2⟩ ⟨s, 3⟩ (pure ()) do
    ins (.un p .sqrt ⟨s, 2⟩ ⟨s, 2⟩)
    rscl p ⟨s, 2⟩ W 0 N
  ins (.lit p ⟨s, 1⟩ 0)

/-- **Lanczos as a program**, `q` steps, three vectors rotating through slots `j mod 3`:
memory `3N + 4` besides the inputs `b` and the outputs `alpha`, `beta` (length `q`). -/
def lanczosProg (p : P) (o : ι) (N q : IExp VI) (b alpha beta : VB) : Builder P ι VB VI Unit := do
  let W ← alloc p (3 * N)
  let s ← alloc p 4
  lanczosInit p N b W s
  forRange q fun j =>
    lanczosStepProg p o N W (N * (.var j % 3)) (N * ((.var j + 2) % 3))
      (N * ((.var j + 1) % 3)) s ⟨alpha, .var j⟩ ⟨beta, .var j⟩

/-- The variant that also writes the basis into `Q` (`N × q`): memory `Nq` more, `Nq` copies. -/
def lanczosBasisProg (p : P) (o : ι) (N q : IExp VI) (b alpha beta Q : VB) :
    Builder P ι VB VI Unit := do
  let W ← alloc p (3 * N)
  let s ← alloc p 4
  lanczosInit p N b W s
  forRange q fun j => do
    copyv p W (N * (.var j % 3)) Q (N * .var j) N
    lanczosStepProg p o N W (N * (.var j % 3)) (N * ((.var j + 2) % 3))
      (N * ((.var j + 1) % 3)) s ⟨alpha, .var j⟩ ⟨beta, .var j⟩
```

**Realisations** (statements; the proofs are the skeleton's work):

```lean
theorem runsWithin_hutchppProg (p : P) (o : ι) (d : Dist) {N k ℓ : ℕ} (hℓ : 0 < ℓ)
    (A : Matrix (Fin N) (Fin N) 𝕜) (ξ : Dist → ℕ → ℝ) :
    RunsWithin (exactInterp (fun _ => A) ξ)
      ((hutchppProg p o d (.const N) (.const k) (.const ℓ) ⟨0, .const 0⟩).run)
      (inputState p [Array.replicate 1 none]) (hutchppCount p o d N k ℓ)
      (fun q => if q = p then 2 * N * (k + ℓ) + 4 else 0)
      (fun st => st.store.read p 0 0 =
        some (hutchpp A (tapeMatrix (ξ d) 0 N k) (tapeMatrix (ξ d) (N * k) N ℓ))) := sorry
```

```lean
theorem runsWithin_lanczosProg (p : P) (o : ι) {N q : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜)
    (b : Fin N → 𝕜) :
    RunsWithin (exactInterp (fun _ => A) fun _ _ => 0)
      ((lanczosProg p o (.const N) (.const q) 0 1 2).run)
      (inputState p [(List.ofFn fun i => some (b i)).toArray, Array.replicate q none,
        Array.replicate q none]) (lanczosCount p o N q)
      (fun r => if r = p then 4 * N + 2 * q + 5 else 0)
      (fun st => (∀ j < q, st.store.read p 1 j =
          some (lanczosAlpha A (lanczosState A b j) : 𝕜)) ∧
        ∀ j < q, st.store.read p 2 j = some ((lanczosState A b (j + 1)).beta : 𝕜)) := sorry

theorem runsWithin_lanczosBasisProg (p : P) (o : ι) {N q : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜)
    (b : Fin N → 𝕜) :
    RunsWithin (exactInterp (fun _ => A) fun _ _ => 0)
      ((lanczosBasisProg p o (.const N) (.const q) 0 1 2 3).run)
      (inputState p [(List.ofFn fun i => some (b i)).toArray, Array.replicate q none,
        Array.replicate q none, Array.replicate (N * q) none])
      (lanczosCount p o N q + Finsupp.single (.copy p) (N * q))
      (fun r => if r = p then 4 * N + 2 * q + N * q + 5 else 0)
      (fun st => Holds st.store p 3 0 (lanczosMatrix A b q)) := sorry
```

The Lanczos realisations need neither a Hermitian nor a breakdown hypothesis: they are stated
against the library's total recursion `lanczosState`, and
`Matrix.IsHermitian.lanczosMatrix_eq_arnoldiMatrix` then gives the Krylov meaning. The sparse
Hutch++ corollary `runsWithin_substOracle_hutchppProg_cooImpl` (proved from the composition
theorem) states its representation: the COO pattern is unrolled into the implementation, the
values are read-only data, each matvec costs `nnz` mul, `nnz` add, `nnz` reads and `N` lits, and
memory is `2N(k + ℓ) + 5 + nnz`. The Gaussian tail for the program that draws its own test
matrices is `measureReal_not_runsWithin_hutchppProg_le_of_hasLaw_iidSequence`, proved from the
realisation, the tape laws and the existing
`measureReal_abs_trace_sub_hutchpp_ge_le_of_hasLaw_gaussianMatrix`.

## 6. Counts (verified by execution during the design)

Hutch++, `J = k(k − 1)/2`, full column rank of `AS` (each zero Gram–Schmidt column saves one
square root and `N` divisions):

| kind | count |
|---|---|
| loads, matvecs, draws | `2`, `2k + ℓ`, `N(k + ℓ)` |
| mul | `2NJ + 2Nk + 2Nkℓ + Nℓ` |
| add | `2NJ + 2Nk + 2Nkℓ + Nℓ + k + ℓ + 1` |
| div, sqrt | `Nk + 1`, `k` |
| conj, neg | `NJ + 2Nk + Nkℓ + Nℓ`, `J + kℓ` |
| lit, cmp | `J + 3k + kℓ + ℓ + 3`, `k` |
| flops | `2Nk² + 3Nk + 4Nkℓ + 2Nℓ + 2k + ℓ + 2` |
| peak memory | `2N(k + ℓ) + 4` cells |

Lanczos, `q` steps, no breakdown: loads and matvecs `q`; mul and add `4Nq + N` each; div `Nq + N`;
sqrt `q + 1`; conj `2Nq + N`; neg `2q`; re `q`; copy `2q + N`; lit `2q + N + 3`; cmp `q + 1`;
flops `9Nq + q + 3N + 1`; peak `4N + 2q + 5` (basis variant `+ Nq`, copies `+ Nq`).

Executed with the `Float` interpreter on a 5 × 5 symmetric `A`:

| run | result | flops | loads, matvecs | peak |
|---|---|---|---|---|
| Lanczos, `N = 5`, 4 steps, `b = 1` | α = (5, 1.4, 3.905556, 2.895728), β = (1.414214, 1.2, 0.980914, 1.086654) | 200 | 4, 4 | 33 |
| the same, keeping the basis | same | 200 | 4, 4 | 53 |
| Hutch++, `k = 2`, `ℓ = 1`, sign tape | 19.326978 | 127 | 2, 5 | 34 |
| Hutch++, `k = 5`, `ℓ = 1` | 15.000000 (`tr A`) | 448 | 2, 11 | 64 |

## 7. Reducing higher-level error models to bit operations, and later stages

### 7.1 The chain

1. **Contract.** A program over a tag `p` is analysed once against a contract (D19), quantified
   over every semantics meeting it: `∀ sem, IsRelErrSem u dec safe sem → RunsWithin {I with sem}
   prog … (error bound on decoded outputs)`. The analysis proves that every operation's inputs
   are in range, which yields success through the success clauses, and bounds the error through
   the error clauses. Exact arithmetic is one admissible semantics (`u = 0`, proved), so shared
   lemmas cover it.
2. **A specified format** on words (D16 (i)), for example `f64` with round to nearest, proved to
   meet the contract. Its partiality is the range condition.
3. **A word-level implementation** of each scalar instruction at `p`, certified once by
   `ImplementsInstr` against that format semantics: the same store whenever the format succeeds,
   the cost of its kind, bounded scratch.
4. **Refinement by substitution.** `RunsWithin.subst` gives the word-level program the store of
   the format-level run, hence its output and its error guarantee. Its counts are
   `substCountG cost c`, and a width weight turns them into bit operations.

**Why the transfer is sound.**
* `ImplementsInstr` demands the same store whenever the specification succeeds.
* Specification-level success at every executed operation is exactly what the contract theorem
  proves, through the success clauses.
* So every operation the substituted program executes is one where the implementation is
  certified to agree.
* An implementation that succeeds where the specification fails lies outside the theorem, and
  nothing is claimed for it.

### 7.2 What stage 1 supports

* Substitution of any scalar instruction or oracle call (D18, proved). It chains: the concrete
  read-only data extends the abstract data, so sparse Hutch++, already one substitution away from
  the oracle, can be substituted again down to words.
* Integer and bit operations, and `convert` (D18).
* Memory in bits (D17).
* The contract with success clauses (D19).
* Kept, not substituted: comparisons (the semantics must agree on them), read-only reads
  (identity cost), draws (equal tapes).

### 7.3 What stage 2 adds

* The format semantics on words (`f64`, `f32`, a parameterised `(p, emin, emax)`), the proof that
  it meets `IsRelErrSem` on range-safe inputs, and contract-level analyses of the BLAS kernels
  (floating `dot` and `axpy` bounds, proved once).
* Bit-level implementations of each floating operation, with `ImplementsInstr` certificates.
* **Comparison substitution.** Comparisons in `ite` and `whileFuel` are kept by the stage-1
  theorem (`hcmp`). A bit-level comparison computes a bit into a scratch cell and branches on it;
  stage 2 extends `Stmt.subst` with a comparison implementation and the simulation with the
  scratch cell.
* **Draw substitution** (Gaussian draws from uniform bits): the tape changes, so the simulation
  needs a coupling between tapes, not equal positions. This is a stochastic refinement, beyond
  this theorem.
* **Representation change** (one word into `w` separate bit cells, gate-level circuits): a data
  refinement with an encoding relation between stores, not the identity relation used here.
  Bit-operation counts do not need it: word operations weighted by width are the usual bit
  complexity.

### 7.4 The fixed-point example (run)

* Tags `fx` (Q16, value `w / 2^16`) and `int` over `ℤ`.
* `fxSem` (fixed-point `add`, and `mul` with the product shifted down), and `wordSem` (integer
  operations only).
* `fxImpl` (`add` and `mul` through reinterpretation, integer operations and `shr 16`; `conj` as a
  copy) and `fxCost`.
* Stated: `implementsInstr_fxImpl` and `fxSem_mul_abs_sub_le`.

The run of `dot` at `fx` gives the same word (−0.6875 = −45056/2^16) at both levels: 9 fixed-point
operations versus 9 integer operations and 18 reinterpretations, peak 64 versus 320 bits.

**Caveat**: the `int` tag here is unbounded `ℤ`, with no overflow failure. So the bit cost 12,672
(64 per add and shift, 64² per multiply) is a weighted count, not a certified 64-bit count. A
certified one needs an `int64` semantics that fails or wraps outside its range (D16 (i)), and the
certificate's range side conditions.

### 7.5 Other later stages

Mixed precision (tags, `convert`), stochastic rounding (semantics reading the tape), and bit cost
of control (loop iterations and `IExp` are syntax) attach as described in D3 and D8.

## 8. Executable code (point 6)

A program is data with Lean binders, so an emitter is one more structural function: instantiate
`VB := String`, `VI := String`, let `alloc` and `loop` invent names, print `IExp` as Python
arithmetic. Emission is size-generic because loops, conditions and sizes are nodes of the
signature. The design's emitter (about 60 lines) prints NumPy in two modes: `named` kernels as
calls into a short NumPy prelude (`dot` as `np.vdot`, `axpy` as `y[...] += a * x[...]`, the
oracle as `A @ X.reshape(..., order='F')`), or inlined scalar loops. Fresh buffers are
`np.full(len, np.nan)`, so a read before write shows as NaN. The emitted Lanczos and Hutch++
(`def lanczos(A, N, q, b, alpha, beta)`, `def hutchpp(A, N, k, l, out)` with a `draw_rademacher`
hook) agreed with the Lean `Float` interpreter to six digits, and the reviewer ran them
size-generically at `N = 7`, `q = 5`, `k = 4`, `ℓ = 3`. The emitted code is an unverified
translation, for differential testing; Lean also runs programs directly with `Float`.

## 9. Lanczos

See D15 (stage 1b).

## 10. Rule checks (sketched as `MetaM` code during the design and run)

| id | rule | run during the design |
|---|---|---|
| E1 | A program (type ending in `Builder` or `Stmt`) is generic in its two variable sorts. No instance or hypothesis mentions them. Every argument is a type parameter, a tag or oracle name, a `Dist`, a handle, an index expression, a cell or a program; host data (`ℕ` sizes, `List`, functions) is rejected outside implementation files. | accepts `dot`, `axpy`, `orthAgainst`, `hutchppProg`, `lanczosStepProg`, `lanczosProg`, `lanczosBasisProg`; rejects `cooImpl` at `pattern` (an implementation, allowlisted by file), `forgeNat` (not generic), `forgeFun` at `f : VI → VB`, `hostSize` at `n : ℕ` |
| E2 | Programs, kernels and implementations are computable. | not re-run |
| E3 | In `RunsWithin I s st₀ c m Q`, no data variable of `I` (dimensions in `ℕ` excepted) occurs in `s` or in `st₀`. | accepts `runsWithin_hutchppProg`, `runsWithin_lanczosProg`; rejects `runsWithin_cheat` (which puts `flatten A` in the initial store) at `A` |
| E4 | Every `<spec>Prog` has `runsWithin_<spec>Prog`. | not re-run |
| E5 | `NLAlib/Computation` imports only Mathlib and ForMathlib. | not re-run |
| E6 | Only `NLAlib/Computation` defines a `ScalarSem` or an `Interp`. | not re-run |
| E7 | Merged into E1 (host sizes). | |
| E8 | `Stmt.named` is constructed only in the BLAS and implementation files. | not re-run |

Not checked, and harmless for the information restriction: host-computed `ℚ` literals and
`.const n` sizes are uncounted host work.


## 11. Files and size

| file | lines |
|---|---|
| `Computation/Syntax.lean` (`IExp`, `Cell`, `Instr` with integer and bit operations and `convert`, `Stmt`, `Builder`) | 270 |
| `Computation/Exec.lean` (`Store`, `St` with bit memory, `Interp` with widths, `exec`, read, write and frame lemmas) | 650 |
| `Computation/RunsWithin.lean` (interface, counts, transfer lemma) | 150 |
| `Computation/Subst.lean` (substitution theorem with general read-only data, oracle corollary; proved during the design, about 420 lines) | 440 |
| `Computation/Contract.lean` (`IsRelErrSem` with success clauses, exact instance, failing-semantics counterexample; the variants in stage 2) | 200 |
| `Computation/Exact.lean` (`exactSem`, `exactInterp`, layout, `Holds`, frame, column-arithmetic lemma set) | 450 |
| `Computation/BLAS.lean` (kernels and the specification family, six parts) | 1,050 |
| `Computation/Dense.lean`, `Computation/Sparse.lean` | 400 |
| `RandomMatrix/Tape.lean` | 200 |
| `hutchpp_reindex` | 80 |
| `Matrix/Factorizations/GramSchmidtProgram.lean` | 450 |
| `Estimation/Trace/HutchPlusPlusProgram.lean` | 600 |
| **stage 1** | **about 4,950** |
| stage 1b: Lanczos | 770 |
| tools and the fixed-point example as a test | 400 |
| checks E1 to E8 | 300 |
| stage 2 (word formats and their contract proofs, `int64`-style semantics, comparison substitution, floating kernel bounds, word-level implementations; with D16 (ii) or (iii) also a data-refinement simulation, about 500) | estimate 3,000 to 3,500, its own note |

## 12. Material

* Quarry (`atlas/declarations.json`), searched for flop, matvec, cost, oracle, program, float and
  round: nothing relevant.
* CSLib (read 2026-10-22): `Cslib.FreeM` and its query interpreters (the free-monad option B),
  `Cslib/Algorithms/Lean/TimeM.lean` (annotation-based costs). Not a dependency.
* Mathlib, searched: no free monad and no imperative-program syntax; `WriterT`, `ContT`,
  `Finsupp.weight`, `Finsupp.liftAddHom`, the `Finsupp` order, `FinEnum`, `Mathlib.Data.Int.Bitwise`.
* Library: `hutchpp`, `hutchpp_eq_of_mul_conjTranspose_self_eq_rangeProjector`, the tails of
  `Estimation/Trace/HutchPlusPlusTail.lean`; `gramSchmidtQ`, `gramSchmidtQ_mul_conjTranspose`,
  `gramSchmidtR_apply_self_smul_col`, `mgsSweep_eq_sub_sum`; `Krylov/Processes/LanczosRecurrence.lean`;
  `Probability/Law.lean` (`iidSequence`); `RandomMatrix/Gaussian/Basic.lean`,
  `RandomMatrix/Rademacher/Basic.lean`.
* Citations: [MeyerMuscoMuscoWoodruff2021, Algorithm 1; Theorem 5], [GolubVanLoan2013, §5.2.8],
  [Paige1972, §2] and [Saad2011, §6.6] as `lanczosStep` cites them; [Higham2002] for the standard
  model (locator to check); Flocq, Cucker (arXiv:1403.6241) and Connolly, Higham and Mary to add
  with stage 2.
* Mathlib deviations: none. `Builder` is Mathlib's `ContT`, and no other object duplicates a
  Mathlib notion; `docs/design/Mathlib-deviations.md` is unchanged.
