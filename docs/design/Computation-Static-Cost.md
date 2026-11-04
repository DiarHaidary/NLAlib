# Static resource bounds for fixed first-order programs

Proposed 2026-11-04. No program, target, count definition, arithmetic model or registered result
is changed. The analysis is conditional on the existing interpreter succeeding.

## Objects and placement

All new declarations live in `NLAlib/Computation/StaticCost.lean`, importing `FirstOrder`.
If the execution induction exceeds the file-size guideline it will move to the natural companion
`NLAlib/Computation/StaticCost/Execution.lean`; definitions remain in `StaticCost.lean`.

The sole new data object is `Computation.StaticCost P ι`, a resource summary with fields:

```lean
structure StaticCost (P ι : Type) where
  count : OpCount P ι
  cells : P → ℕ
  bits : ℕ
```

`count` bounds the incremental charge of each operation kind. `cells p` and `bits` bound
additional simultaneously live workspace, above the input state's current memory. They exclude
read-only memory, which the final `RunsWithin` bridge adds explicitly. Existing `OpCount`,
`Interp`, `St`, `FStmt`, `Prog`, `Prog.exec`, and `Prog.RunsWithin` are used directly.

`StaticCost.Bounds c st st'` is a named resource conclusion, not an arithmetic contract. It
records the count upper bound, unchanged current memory, and peak bounds:

```lean
structure StaticCost.Bounds (c : StaticCost P ι)
    (st st' : St P K (OpCount P ι)) : Prop where
  count : st'.cnt ≤ st.cnt + c.count
  cur : st'.cur = st.cur
  curW : st'.curW = st.curW
  peak : ∀ p, st'.peak p ≤ max (st.peak p) (st.cur p + c.cells p)
  peakW : st'.peakW ≤ max st.peakW (st.curW + c.bits)
```

There is no invariant or local arithmetic error assumed by the main theorem. This conclusion
has a reflexivity rule, monotonicity, and sequential composition using the summaries below.
No new store or scalar interface is introduced.

## Static fold

```lean
noncomputable def FStmt.staticCost
    (charge : OpKind P ι → OpCount P ι) (width : P → ℕ) :
    {nb ni : ℕ} → FStmt P ι nb ni → (Fin ni → ℕ) → StaticCost P ι

noncomputable def Prog.staticCost
    (prog : Prog P ι r b) (charge : OpKind P ι → OpCount P ι) (width : P → ℕ)
    (N : ℕ) (n : Fin r → ℕ) : StaticCost P ι :=
  prog.staticCost charge width (Fin.cons N n)
```

The handle environment is absent. The fold sees only the fixed tree, interpreted scalar charges,
cell widths and natural-valued index environment. Noncomputability comes only from Mathlib's
finitely supported count/lattice operations; no program depends on this analysis.

- `skip`: all zero.
- `instr`: exactly its existing instruction-kind charge, no workspace.
- `apply`: `charge (.load p o) + cols * charge (.matvec p o)`, no interpreter-visible scratch.
- `rom`: exactly its read charge, no workspace. Read-only capacity is added externally.
- `seq`: add counts, take the maximum workspace per tag and in bits.
- `ite`: one comparison plus the pointwise maximum of branch counts; maximum branch workspace.
- `alloc`: body counts; add the allocated length at its tag to body workspace, and
  `length * width p` to body bit workspace. Scoped deallocation is essential to sequential maxima.
- bounded `loop`: fold sequential summaries over the actual range, extending the index
  environment by `Fin.snoc`. This handles index-dependent lengths and inner loop bounds.
- `whileFuel`: at most `fuel` copies of comparison plus body counts, and the body workspace.
  This is an upper bound: a successful loop necessarily exits before exhausting true tests.
- `named`: recurse into the actual body; labels are never trusted as cost certificates.

Reusable summary operations are `StaticCost.zero`, `StaticCost.step`, `StaticCost.seq`,
`StaticCost.branch`, `StaticCost.alloc`, and `StaticCost.repetitions`. The loop uses a list fold of
`seq` rather than a second arithmetic simplifier. Pure count inequalities reuse the Finsupp
pointwise lattice. Natural peak inequalities reuse `max` and standard order lemmas.

## Main statements

```lean
theorem FStmt.bounds_staticCost_of_exec_eq_some
    (I : Interp P ι K (OpCount P ι))
    (s : FStmt P ι nb ni) (ρB : Fin nb → ℕ) (ρI : Fin ni → ℕ)
    {st st' : St P K (OpCount P ι)}
    (h : s.exec I ρB ρI st = some st') :
    (s.staticCost I.charge I.width ρI).Bounds st st'

theorem Prog.bounds_staticCost_of_exec_eq_some
    (I : Interp P ι K (OpCount P ι)) (prog : Prog P ι r b)
    (N : ℕ) (n : Fin r → ℕ) {st st' : St P K (OpCount P ι)}
    (h : prog.exec I N n st = some st') :
    (prog.staticCost I.charge I.width N n).Bounds st st'

theorem Prog.runsWithin_staticCost_of_exec_eq_some
    (I : Interp P ι K (OpCount P ι)) (prog : Prog P ι r b)
    (N : ℕ) (n : Fin r → ℕ) {st st' : St P K (OpCount P ι)}
    (h : prog.exec I N n st = some st') :
    prog.RunsWithin I N n st
      (prog.staticCost I.charge I.width N n).count
      (fun p => max (st.peak p)
        (st.cur p + (prog.staticCost I.charge I.width N n).cells p) + I.romSize p)
      (fun out => out = st')
```

All statements quantify over arbitrary stored carriers, scalar semantics, tapes and oracles.
They neither establish successful execution nor claim physical memory bounds for internals of
an external oracle/semantics implementation. The bit bound concerns existing interpreter width
accounting; ROM bits can be added by consumers with a finite-tag summation interface if needed.
The provided `RunsWithin` bridge uses the library's existing cell-memory notion exactly.

## Existing material searched and reused

- Mathlib `Data/Finsupp/Order` and `Order/Preorder/Finsupp`: pointwise order, supremum and
  addition; no matching imperative resource analysis was found.
- Mathlib List `foldlM` lemmas: success decomposition through `Option.bind_eq_some_iff`,
  `Option.map_eq_some_iff`, `List.foldlM_cons`; list induction handles bounded iteration.
- `Computation/Exec.lean`: `Instr.kind`, `snd_of_cmpStep_eq_some`, execution constructor
  equations; existing successful-run current-memory/shape preservation is reused where useful.
- `Computation/Exec.lean` straight-line usage: proves equal usage between two successful
  straight-line runs. It supplies no AST-derived upper bound and excludes both guarded forms.
- `Computation/FirstOrder.lean`: existing actual first-order interpreter and program resource
  interfaces; no new interpreter and no alternate semantics.
- `Computation/RunsWithin.lean`: existing budget/postcondition interface, rather than a new
  access model or target.

## Consumers and scope

The CG prototype will use the resource theorem after its actual rounded execution proof, so
counts/peaks no longer need to be reproved from arithmetic/store invariants. Oracle CG variants
use the same fold's actual load-plus-column-matvec accounting. Other fixed registered trees may
use it without changing their targets, and compare the static summary with their existing
closed-form budgets in ordinary inequalities.

No `Result:` id, new named numerical constant, arithmetic semantics, program registration or
target change is proposed. Root integration owns umbrella imports and vocabulary rows.

## Checked implementation amendment, 2026-11-04

The complete layer fits in `Computation/StaticCost.lean` (no companion module). Lean reserves
`repeat`, so the operation is named `StaticCost.repetitions`. At zero repetitions it keeps the
body workspace as a conservative bound while its count is zero; this also covers inactive
iterations of the fuel loop without introducing size side conditions. `Bounds.alloc` proves
allocation/popping composition directly, and `Bounds.foldlM` / `Bounds.foldlM_repeat` certify
the actual option folds used by `FStmt.exec`. The main theorem is a structural induction on the
actual first-order tree. Every constructor is included; no caller-supplied resource premise is
needed. Both the cell and width-weighted bit peaks are proved.

## Canonical-tree consumers, 2026-11-04

The approved extension adds `Krylov/LinearSystems/CGProgramStaticCost.lean` and
`Krylov/Processes/LanczosProgramStaticCost.lean`: statements about these algorithms belong in
Krylov, and Computation still imports no algorithm files. Their static count inequalities use
the actual `cgProg.compiled` and `lanczosProg.compiled` and the unchanged `cgCount` /
`lanczosCount` formulas. Per-tag workspace bounds are respectively
`if p = tag then N^2+N+10 else 0` and `if p = tag then N^2+N+3 else 0`.
No exact arithmetic realization theorem is imported or used. Conditional successful-run
resource projections consequently apply to arbitrary scalar semantics with standard charges.
The generic sequence field lemmas support symbolic loops without expanding their iterations.

Validation note: the source checker treats an unqualified `.named` elimination pattern as
construction of a named program. The fold now spells the actual constructor `FStmt.named`,
with a comment explaining that it eliminates the label and constructs no program node.
No check or allowlist was changed.

Both canonical consumer modules additionally prove width-weighted workspace bounds:
`(N^2+N+10) * width tag` for CG and `(N^2+N+3) * width tag` for Lanczos. Their
`cgProg.bounds_of_exec_eq_some` and `lanczosProg.bounds_of_exec_eq_some` return the existing
`StaticCost.Bounds` conclusion with the approved count formula and these closed-form cell/bit
bounds. Their only run premises are actual execution success and the standard per-kind charge;
there is no exact-semantics, matrix positivity or recurrence-correctness premise. The generic
`Prog.runsWithin_staticCost_of_exec_eq_some` bridge remains available when clients prefer the
raw AST summary. The successful-run corollaries are supporting API with no result ids.

Targeted validation (warnings fatal) passed for all three modules. Source checks report zero
errors and warnings. Integration owns the full stage, umbrella generation, vocabulary and PR.
