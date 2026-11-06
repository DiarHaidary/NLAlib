# Design note: the bounded index binder, and EIGH as a program (stage COMPDYN S2)

Status: design stage, 2026-11-06. Branch `design/compdyn-s2` (worktree `~/nlalib-design-compdyn-s2`),
from `design/compdyn-s1cd` d610ab95 with `cleanup/hdiag` (bd81bd1d, pushed as `feat/hdiag`) merged
(§11). Parent note: `docs/design/Computation-DynamicPrograms.md` (approved, sheet `COMPDYN.json`):
§4.1 data-dependent sizes (Q1, Q2, M1, M2), §4.2 recursion by levels (Q3), §4.6 costs (Q8), §6 the
EIGH sketch (M4 packed blocks, M5 inputs), §7 refinement shape and effort. Pilot: S1c/S1d,
`docs/design/Computation-SignDeflatePrograms.md` (its 65 targets are being proved in a separate
dispatch; this stage cites them). Shallow specification: hdiag's `NLAlib.eigh`
(`NLAlib/Matrix/Computation/SpectralBisection.lean`) and its theorems EV6, EV7, EV8
(`NLAlib/Eigensolvers/SpectralBisection/Global.lean`), and EV7' (HDIAG-BOUNDS,
`research/hdiag-bounds`, being proved). Skeleton: 63 statements in `NLAlibScaffold/`
(`~/nlalib-harness/pilot/compdyn-s2-targets.json`) and one blocked on HDIAG-BOUNDS (§7.4). Decision
sheet: `~/nlalib-harness/state/decisions/COMPDYN-S2.json` (RP, D1 to D7).

This stage finishes what the maintainer asked for on 2026-11-05: [Shah2024]'s Hermitian eigensolver
EIGH as a genuine program of the model of computation, with [Shah2024, Theorem 4.2] proved for the
program.

## 0. Summary

| | |
|---|---|
| S2a (language) | `Stmt.bindIdx p x bound body` / `FStmt.bindIdx`: read the cell `x` once at tag `p`, convert by the new `ScalarSem.toNat` (default `none`), clamp to the index expression `bound`, bind as an index variable; one charged `OpKind.toNat p`. `StaticCost` takes the supremum of the body over the range of the bound (`StaticCost.supRange`). Contracts `IsExactToNat` (the floor of the decoding, $0$ below zero: M1) and, new, `MulShrinks` (§2.3, D4). Every structural site repaired, proved in `NLAlib/` (`--wfail`). Tool: the index normal form `Stmt.normIdx` (§2.4). |
| Statement changes | `exec_subst_sim` and `RunsWithin.subst` gain `htoNat : I'.sem.toNat = I.sem.toNat` (anticipated by §4.1 of the parent note) and `hcostToNat` (the analogue of `hcostCmp`); their one caller, `RunsWithin.substOracle`, discharges both, so its statement is unchanged. No other statement changes (§2.2). Flagged for the maintainer (D5). |
| Re-pin | the second approved re-pin (Q9 (c)): the nine closure hashes change, nothing else (§2.5). Needs the maintainer's sign-off before merge (RP). |
| `eighProg` | One builder, compiled by `rfl` into `NLAlib.eighProg.compiled : Prog P ι 2 4` (sizes $N$; $\ell_0$, $F$). Level arenas for $D + 1 = \ell_0 + 2$ depths, a downward pass of $D$ levels, the spent level, an upward pass of $D$ levels; every node a packed block at word offset $2n^2 d + 2n\,lo$ (M4); sizes, kinds and $k_+$ stored as integer literals and read back by `bindIdx`; tests on sizes by trip counts $0$/$1$ of loops (D2); the sign step inlined from the pilot's test and step blocks with the shallow step limit, so a run never fails for want of steps (D1); static sample positions per level (D3). About 430 lines (`SpectralBisectionProgramTree.lean`), with 300 lines of vocabulary (`SpectralBisectionTape.lean`). No Lean function of data in the tree (F2). |
| Refinement | (a) **partial equality**: under kernels that are routines on pairs, a semantics that decides flags, `IsExactIntLit` up to $N + 4$ and `IsExactToNat`, every successful run writes exactly `NLAlib.eigh (eighTapeMachine I p mmR qrR) F ℓ₀ A R₀ ε β (eighSlotTree …)`; no correctly rounded `fl` is needed (the pilot's finding, §4). (b) **success**: under the standard model with every value in range, $u < 1$, $\ell_0 \ge 1$ and $\varepsilon, R_0 \ge 0$, every run succeeds. |
| Transfer | `NLAlib.MatrixFreeRoundedProbEigh` (proposed target, `NLAlib/RandomMatrix/Computation/SpectralBisectionTargets.lean`): EV6 for the registered tree, via the sampler rewrite and a lazy-sampling lemma (§6); the program forms of EV7 (bits) and EV8 (a bounded binary format, for the runs that succeed, D6); EV7' in a blocked file (§7.4). Shah's Theorem 4.2 for a program of the model. |
| Skeleton | 63 statements: S 25, M 29, L 8, H 1 (§8). |
| Calibration | S2a: about 350 lines (353 insertions, 56 deletions), proved (estimate 900 – 1,500: below); S2b definitions about 880 lines, statements about 1,850 scaffold lines; S2 projected 7,750 – 9,550 lines, the middle of §7.2's 6,400 – 11,000 for the S2 rows (§10). |

## 1. Files

| File | Content | Lines |
|---|---|---|
| `NLAlib/Computation/{Syntax,Exec,FirstOrder,Compile,Subst,StaticCost}.lean` (amended) | `bindIdx`, `ScalarSem.toNat`, `OpKind.toNat`, `toNatStep`, the run, the bridge, the compiler, `Stmt.subst` and the simulation, `StaticCost.supRange`, the index normal form `Stmt.normIdx` (in `FirstOrder.lean`) | +290 |
| `NLAlib/Computation/{Contract,Exact,Grid,BinaryFloatSem}.lean` (amended) | `IsExactToNat`, `MulShrinks`; `failSem`'s sixth component; `toNat` of `exactSem`, `gridSem`, `binaryFloatSem` | +30 |
| `NLAlib/Estimation/Trace/HutchPlusPlusProgram.lean`, `NLAlibTools/{NumPy,KrylovSmoke,KrylovOracleSmoke}.lean` (amended) | the compile lemma's binder case; the emitter's binder; `toNat` in the smoke tests | +24 |
| `NLAlib/Matrix/Computation/SpectralBisectionProgramTree.lean` (new) | `eighWhen`, `eighEqInd`, `eighSignBlock`, the node blocks, the three levels, `eighProg`, `.compiled`, `eighCount` | 428 |
| `NLAlib/Matrix/Computation/SpectralBisectionTape.lean` (new) | `ScalarSem.tapeUnif`, `uniformUnif`, `eighTapeMachine`, `eighTapeSample`, `eighLoc`, `eighSlotTree`, `eighLevelParams`, `EighArenas` and its predicates, `eighIdealSample`, `eighIdealTree` | 301 |
| `NLAlib/RandomMatrix/Computation/SpectralBisectionTargets.lean` (new, proposed) | `EighData`, `MatrixFreeRoundedProbEigh` | 117 |
| `NLAlibScaffold/` (new files), `NLAlibScaffold.lean` | the skeleton, §8 | 1,854 |

## 2. S2a: the bounded index binder

### 2.1 The construct

```lean
-- Stmt                                         -- FStmt (binds index variable `ni`)
| bindIdx (p : P) (x : Cell VB VI) (bound : IExp VI) (body : VI → Stmt P ι VB VI)
-- ScalarSem, a defaulted field (every `where` construction still elaborates)
toNat : P → K → Option ℕ := fun _ _ => none
-- OpKind
| toNat (p : P)
-- the run: one charged conversion, then the body at the clamped value
| .bindIdx p x bound body, st => (toNatStep I p x st).bind fun r =>
    exec (body (min r.1 bound.eval)) r.2
-- StaticCost: the conversion, then the supremum of the body over k ≤ bound
| .bindIdx p _ bound body, ρI => (step (charge (.toNat p))).seq
    (supRange (bound.evalIn ρI + 1) fun k => body.staticCost charge width (Fin.snoc ρI k))
```

As approved (Q1 (a), Q2 (a), OQ1 clamp). `toNatStep` mirrors `cmpStep` (a read, the conversion,
the charge), so the invariants, the bridge and the simulation treat the binder as a comparison
followed by a loop body. `StaticCost.supRange m f` folds `StaticCost.branch` over $f(0), \ldots,
f(m - 1)$, and `StaticCost.Bounds.supRange` is the one new lemma it needs. `Stmt.StraightLine`
excludes the binder (two runs can bind different values).

`IsExactToNat dec sem : ∀ p x, sem.toNat p x = some ⌊dec p x⌋₊` is the separate contract (M1): total,
$0$ below zero, so the program's binder is hdiag's `M.toNat` with no case split. The library's
semantics get the conversion of their decodings: `exactSem` the floor of a real value (failing on a
non-real one, as its comparisons do), `gridSem` the floor of the rounded decoding,
`binaryFloatSem` the floor of the value. `failSem` (an anonymous constructor) gets its sixth
component. Witnesses: §8, BI4 to BI6.

### 2.2 Repairs and statement changes

One case at each structural site of §4 of the parent note: `exec` and its lemma `exec_bindIdx`; the
invariants `runInv_of_exec_eq_some`, `exec_eq_of_exec_eq_some_of_cnt_load_le`,
`shape_usage_eq_of_exec` (vacuous: not straight-line), `Stmt.StraightLine`; `FStmt.exec`, the bridge
`FStmt.exec_eq_exec_toStmt` (with `toNatStep_subst_congr`), `FStmt.exec_bindIdx`; `Stmt.compile`,
`FStmt.toStmt`; `Stmt.subst`, `substKind`, `toNatStep_sim`, `simRun_bindIdx`; `FStmt.staticCost` and
`FStmt.bounds_staticCost_of_exec_eq_some`; the Hutch++ compile lemma `compile_substOracle_cooImpl`;
the tools `KrylovSmoke` (`opcode`, `kinds`, `mem_kinds`, two budget lemmas), `KrylovOracleSmoke` (two
budget lemmas) and the NumPy emitter (`i{ni} = min(max(int(np.floor(x)), 0), bound)`). All proved.

**Statement changes** (D5). The simulation needs the concrete interpretation to convert as the
abstract one and the substituted count to charge a conversion as itself:
* `exec_subst_sim` and `RunsWithin.subst` (result `computation-substitution`) gain
  `htoNat : I'.sem.toNat = I.sem.toNat` (§4.1 of the parent note: "needs `htoNat` … beside
  `hcmp`") and `hcostToNat : ∀ p, cost (.toNat p) = Finsupp.single (.toNat p) 1` (beside
  `hcostCmp` and `hcostRom`).
* Their only caller, `RunsWithin.substOracle` (result `computation-oracle-substitution`), supplies
  both (`by rw [hsem]`, `fun _ => rfl`): **its statement is unchanged**, and so are all of its
  callers'.

Without the two hypotheses `RunsWithin.subst` is false (a binder whose concrete conversion fails),
so the change is forced by the approved Q1 (a); no other statement of the library changes.

### 2.3 `MulShrinks` (D4, in place of M3's correctly rounded `fl`)

`MulShrinks dec sem : ∀ p x y z, sem.bin p .mul x y = some z → |dec p y| ≤ 1 → |dec p z| ≤ |dec p x|`.
The parent note's M3 asked for a correctly rounded `fl` for EIGH. The pilot showed that the equality
refinement needs no contract on the rounding (the machine of a semantics is a function of the stored
operands, §2.2 there), and the only place EIGH needs more than the standard model is the clause
$\lvert \overline{\mathrm{unif}(s, v)} \rvert \le \bar s$ of `NLAlib.IsUnifSampler`: the shift
$\mathrm{fl}(s\rho(v))$ must stay in the window. `MulShrinks` is exactly that clause, true of every
monotone rounding exact on stored values (IEEE, `gridSem`: BI8), and weaker than correct rounding.

### 2.4 The index normal form

The pilot's run lemmas of the kernels are stated at constant sizes (`.const n`). Inside `eighProg`
every size is an index variable bound by a binder or a loop. `Stmt.normIdx` replaces every index
expression, under every binder, by the constant of its value; `exec_normIdx` (M) says a statement
runs as its normal form, and `exec_eq_of_normIdx_eq` turns it into ten one-line congruences
(`exec_zcopy_congr`, …, `exec_newtonSchulzStepBlock_congr`), each a normal-form computation. This
is a general tool: any later program that calls a kernel at a computed size uses it.

### 2.5 The re-pin

By the documented path, run into a copy of the registry (`TARGETS_REGISTRY`) so that the diff could
be checked first: `TARGETS_UPDATE=1 lake env lean scripts/Targets.lean`. Only the nine target
closure hashes changed (the `ScalarSem` field, the `OpKind` and `Stmt`/`FStmt` constructors are in
every target's closure); the seven tree hashes, the printed statements and normal forms and the
toolchain, Mathlib and manifest pins are unchanged. The tool also rewrote the `lakefile_sha256` pin
to the lakefile with the scaffold entry; that line was restored, as in S1 (the pin matches again
once the clean-up removes the scaffold library). The registry was then replaced by the checked copy
and `docs/targets.approved` rewritten (`sha256sum`), under the approval of Q9 (c), pending the
maintainer's sign-off (RP):

| target | old closure hash | new closure hash |
|---|---|---|
| `MatrixFreeGramSchmidt` | `af26a2cc59a18852…` | `803740ecf5bda027…` |
| `MatrixFreeHutchpp` | `f30f4f842aac163e…` | `6cb6c7ef3a3e0b94…` |
| `MatrixFreeProbHutchpp` | `d9a85ec8490dc567…` | `f15f97400d04881e…` |
| `StoredEntriesDenseHutchpp` | `771e016ca68b29ac…` | `f875bf2c0626616d…` |
| `StoredEntriesCooHutchpp` | `62fcf12585da26e2…` | `25b9142e7748322f…` |
| `StoredEntriesConjugateGradient` | `74f03a01c2627964…` | `fe5dfa37a8a75b53…` |
| `StoredEntriesLanczos` | `3067f8e5a70ba8b5…` | `9c35bcc669cc4c91…` |
| `MatrixFreeConjugateGradient` | `d22d5e3483281f66…` | `381197470600e824…` |
| `MatrixFreeLanczos` | `903a3da3d2951891…` | `c4744e2b3f3edef4…` |

New `docs/targets.approved`: `bc9f33e5dd503e2ad18281e360f466b1745660608dc7f7fafb94efb7f31b84f8`. The old
hashes are those of the S1 re-pin (`7bff66e4…` approved).

## 3. EIGH as a program

### 3.1 Interface (§6.1 of the parent note, M5)

`eighProg.compiled p mm qr : Prog P ι 2 4`. Sizes: $N = n$ (index $0$), the depth counter $\ell_0$
and the sign step limit $F$. Declared buffers: $0$ the matrix ($2n^2$ words, interleaved,
column-major), $1$ the stored $R_0$, $\varepsilon$, $\beta$, $2$ the output $\mathbf{U}$ ($2n^2$
words), $3$ the eigenvalues ($n$ cells). Kernel names `mm`, `qr`.

### 3.2 Layout

The nodes of depth $d$ partition a part of $[0, n)$ into ranges $[lo, lo + k)$
(`eighLoc_bounds`, `eighLoc_disjoint`); the node at $[lo, lo + k)$ is stored at **slot** $lo$ of
level $d$. Arenas, one level per depth $0, \ldots, D$ ($D = \ell_0 + 1$): node matrices `Ma`,
outputs `Ua`, bases `Qa` (complex $n \times n$ blocks: the node's $k \times k$ block at word
$2n^2 d + 2n\,lo$, packed, disjoint across a level since $k^2 \le kn$, M4), eigenvalues `Ea`, sizes
`Sz`, kinds `Kd`, splits `Kp` ($n$ cells per level), windows and tolerances `Lv` (two cells per
level). Memory $O(n^2 \ell_0)$, a function of the sizes.

### 3.3 The passes

* **Initialisation**: the constants $1$, $\mathrm{fl}(2)$ (`litIdx 2`, hdiag's `M.ofNat 2`),
  $\mathrm{fl}(1/2) = \mathrm{fl}(1/\mathrm{fl}(2))$, $-1$; every size cell the literal $0$, the root's
  $n$; $\mathbf{A}$, $R_0$, $\varepsilon$ at depth $0$.
* **Downward level** $d < D$ (`eighDownLevel`): the next window and tolerance exactly as
  `eighNextParams` at $\ell = \ell_0 + d$; the level's $n$ uniform and $4n^2$ Gaussian draws; for
  each slot, the stored size (a binder clamped to $n - lo$) and, for $k \ge 1$, a leaf when $k \le 1$
  (identity, diagonal real parts) or when $R \le \mathrm{fl}(\varepsilon R_0)$ (one counted
  comparison; identity, zeros), else the node step.
* **Node step** (`eighNodeBlock`, `NLAlib.eighStep` line by line): $\sigma = \mathrm{fl}(R/\mathrm{fl}(2))$,
  the shift $c = \mathrm{fl}(\mathrm{fl}(R/\mathrm{fl}(\ell))\,v)$ from the node's seed, $\mathbf{W} =
  \mathbf{A} - c\mathbf{I}$, the sign at $(\beta, \mathrm{fl}(\mathrm{fl}(2)R))$ (`eighSignBlock`), the
  projectors, the rounded trace $t$ and $k_+ = \min(\lfloor\mathrm{fl}(t + \mathrm{fl}(1/2))\rfloor_+,
  k)$ **by a binder**; then one child (positive side if $k_+ = k$, negative if $k_+ = 0$) or a split:
  deflation on the stored samples (`eighDeflateBlock`: $\widetilde{\mathbf{G}}$ from the level's
  Gaussian words times the stored $\sqrt{1/2}$, `mm`, `qr`, the first $r$ columns), the two
  compressions (`eighCompressBlock`), the children's sizes, the kind and $k_+$.
* **Spent level** $D$ (`eighBottomLevel`): every node gets $(\mathbf{I}, \mathbf{0})$, `eighAux` at
  budget $0$.
* **Upward level** $d = D - 1, \ldots, 0$ (`eighUpLevel`): by the stored kind (a binder clamped to
  $4$), a one-child node copies its child's $\mathbf{U}$ and adds $\pm\sigma$; a split reads $k_+$
  and writes $\mathrm{mm}(\mathbf{Q}_+, \mathbf{U}_+)$, $\mathrm{mm}(\mathbf{Q}_-, \mathbf{U}_-)$
  into the two column blocks of its output (column-major, so `Matrix.fromCols` reindexed by
  `finSumFinEquiv` is the concatenation of the two packed blocks) and the shifted eigenvalues.
* **Output**: the root's $\mathbf{U}$ and eigenvalues copied to buffers $2$, $3$.

### 3.4 Choices

* **D1, the sign step never fails.** The pilot's `newtonSchulzSignProg` runs `whileFuel (F + 1)` and
  fails when no iterate passes; hdiag's `newtonSchulzLoop F` returns the $F$-th iterate. Inside EIGH
  a failure would make success depend on a statement the HDIAG stage has not made (the pilot's TR1,
  that the test passes within $N_* + 1$ steps, at every node), and the transfer would need the
  probability of that event, which hdiag bounds only inside the proof of EV6. `eighSignBlock` reuses
  the pilot's set-up, test and step blocks (`newtonSchulzTestBlock`, `newtonSchulzStepBlock`) and
  replaces the loop by $F$ iterations of "if the flag is set, step and test" (one counted comparison
  each): exactly `newtonSchulzLoop`, so the program **succeeds on every run** under the standard
  model and the transfer is a direct application of the shallow theorems. Cost: $F$ comparisons per
  node, the steps only while the test fails.
* **D2, tests on sizes by trip counts.** `eighWhen e b` is `forRange (1 - (1 - e)) fun _ => b`, which
  runs $b$ once if $e \ge 1$ and never otherwise (truncated subtraction); `eighEqInd c m` is the
  indicator of $c = m$. Loop bounds are index expressions, free in the model as every loop's, and no
  new construct is added (OQ8 stays closed). The alternative, comparing stored sizes by `ite` on
  cells, would need a comparison contract in the equality refinement.
* **D3, static sample positions.** Every downward level draws exactly $n$ uniform and $4n^2$
  Gaussian values, whatever the data. So the node at slot $lo$ of depth $d$ reads its seed at uniform
  position $nd + lo$ and entry $(i, j)$ of its test matrix of side $s$ at the complex sample
  $2n^2 d + n(2(lo + j) + s) + i$ (`eighTapeSample`), independent of every other node's. A program
  that drew only what each node uses ($1 + 4k^2$ per split) would read data-dependent positions, and
  the lazy-sampling argument would have to follow the draw counter through the run. Cost: $O(n^2)$
  draws per level, within the $O(T_{\mathrm{MM}}(n))$ of the level.

## 4. The refinement (§7.1 of the parent note)

The machine of a run is `eighTapeMachine I p mmR qrR`: the machine of the semantics
(`ScalarSem.toFloatMachine`), its conversion the semantics' (`none` read as $0$), its black boxes
the kernel routines, its samplers reading the stored tape at a position (`ScalarSem.tapeUnif`,
`ScalarSem.tapeNormal`); seeds and Gaussian samples are positions (`Su = Sg = ℕ`). The tree of
samples is `eighSlotTree M n F R₀ β 0 0 root`, the positions of each node's slot along the shallow
recursion.

* **(a) Partial equality** (`holds_of_exec_eighProg`, `eighProg.holds_of_exec_compiled`):
  kernels that are routines on pairs (`IsMatMulKernel`, `IsQRKernel`), `DecidesFlags` (the sign
  flag), `IsExactIntLit dec I.sem (N + 4)` and `IsExactToNat dec I.sem` (sizes and kinds read back
  through cells, M1, M2) ⟹ every successful run ends with buffers $2$, $3$ holding exactly
  `eigh M F ℓ₀ A R₀ ε β (eighSlotTree …)`. No contract on the rounding.
* **(b) Success** (`exists_exec_eighProg`, `eighProg.exists_exec_compiled`): the standard model at
  $u$ with every value in range, $u(p) < 1$, the two exactness contracts, routines on pairs,
  $\ell_0 \ge 1$ and $\bar\varepsilon, \bar R_0 \ge 0$ ⟹ every run succeeds: every division is by
  $\mathrm{fl}(2)$, $\mathrm{fl}(\ell)$, $\mathrm{fl}(4k)$ or $\mathrm{fl}(2R) \ne 0$ at a node whose
  window test failed, the sign step never fails (D1), the conversion is total.

The proof follows the levels: the arenas hold the nodes of a depth (`EighArenas.LevelHolds`), the
downward level produces the next depth and the records of the node steps (`RecordHolds`), and the
upward level turns the outputs of depth $d + 1$ into those of depth $d$ (`OutHolds`, `eighAux` with
the remaining budget). The vocabulary of the recursion is `eighLoc` (slot and node at a path) with
its lemmas ET1 to ET6.

## 5. Counts (Q8)

* **Static** (`eighProg.cnt_le_of_exec_compiled`): at most `eighCount p mm qr N ℓ₀ F`, which charges,
  per slot visit, the kernel calls of a node of every size $k \le N$ and every split $k_+ \le k$
  (the supremum of `bindIdx` is bounded by the sum), and $1024(F + 2)(\ell_0 + 2)(N + 1)^3$ of each
  scalar kind; peak memory $64(N + 1)^2(\ell_0 + 3)$ cells. Sound for every successful run under every
  semantics, loose by about $N^2$ on the kernels (§4.6 of the parent note).
* **Weighted** (`eighProg.weight_le_of_exec_compiled`, L): for a monotone superadditive cost $T$ of a
  kernel call by its largest dimension (a convex $T$ with $T(0) = 0$), the weighted kernel count is
  at most $(\ell_0 + 1)(2F + 12)\,T(N)$: per level the node sizes sum to at most $N$, each node making
  at most $2F + 12$ calls. This is the operation count of [Shah2024, Theorem 4.2], proved by an
  invariant of the run, not by `StaticCost`.

## 6. Samples (§7.1, the lazy-sampling lemma)

* **Positions to values** (`eigh_eighTapeMachine_eq_eigh_eighIdealTree`, L): for a tape
  $\rho \circ \xi$ with $\rho$ independent of the position (as the pilot's DEFLATE target, D7
  there), `eigh` on the tape machine with the slot tree equals `eigh` on the **ideal machine**
  (samplers `ScalarSem.uniformUnif`, `ScalarSem.gaussianNormal` of $\rho$) with the tree of ideal
  samples `eighIdealTree`: the static positions of each existing node at depth below $D$, on its seed
  and leading block, and positions beyond the program's draws, indexed by the path, elsewhere. Two
  general lemmas: `eigh` sees samples only through the samplers (ES1) and only at the nodes it
  reaches (ES2).
* **Lazy sampling** (`iIndepFun_eighIdealTree`, H): on the ideal tape the ideal tree is independent
  with law `eighSampleLaw` at every path. The positions a node reads are decided by earlier samples
  and disjoint from every other node's. The only H of the stage: a general lemma about adaptively
  chosen disjoint blocks of an i.i.d. sequence, then this instance; hdiag's
  `countable_range_eighNodeAt`, `measurableSet_eighNodeAt_eq` give the measurability.
* **The ideal machine is accurate** (`isAccurate_eighIdealMachine`): the pilot's IM1 and IM3 with
  `isUnifSampler_uniformUnif` (from `MulShrinks`), at the machine roundoff
  $u_{\mathrm M} = (c(\mathrm{uniform}) + 1)u$ and $c_{\mathrm N} = 2(c(\mathrm{gaussian}) + 3)$, when
  the tape range covers the seeds, $1 \le 2\Omega$ (Fable review: without it the tape contract does
  not constrain the rounding of a seed, and the statement fails at $\Omega = 0$); the targets' `pre`
  gives $\Omega \ge 160$.

## 7. Transfer: Theorem 4.2 for the program

### 7.1 The target

`NLAlib.MatrixFreeRoundedProbEigh` (`MatrixFreeRoundedProb` of the registered tree): for every
interpretation meeting the standard model at $u$ with every value in range, `IsExactIntLit` up to
$N + 4$, `IsExactToNat`, `MulShrinks`, and kernels meeting `IsMatMulErr`, `IsQRErr` at $u$, floor
$0$, range $\Omega$; every tape rounding meeting `IsTapeRounding` at range $2\Omega$, independent of
the position, with countable ranges and measurable fibres; and the hypotheses of EV6 at
$u_{\mathrm M}$ and $c_{\mathrm N}$: the probability that the run fails or returns no approximate
diagonalization with residual $2\varepsilon R_0$ and $\mathbf{U}$ within $\varepsilon/3$ of unitary is
at most $\theta$. Proof `matrixFreeRoundedProbEigh` (M): (b), (a), §6, EV6. Its contracts are
satisfiable: `gridSem` meets the four semantic contracts (`isRelErrSem_gridSem`,
`isExactIntLit_gridSem`, BI5, BI8), up to one bridge: `isExactIntLit_gridSem` is stated at the
identity decoding, the others at $x \mapsto \mathrm{fl}_p(x)$, so a two-line restatement at the grid
decoding is needed before a non-vacuity witness of the whole hypothesis set (with `exactMM`,
`exactQR`, `isTapeRounding_id`) can be a theorem (Fable review, later). The S2 statements cite the
pilot's S1c/S1d statements, sorried here; the S2 merge waits for S1cd to land.

### 7.2 EV7: the bit count

`matrixFreeRoundedProb_eighProg_of_logb_le` (M): the same model with EV7's precision condition at
$u_{\mathrm M}$: $\log_2(1/\varepsilon) + O(\log n + \log\log(1/\varepsilon)) +
\tfrac32\log_2(1/\theta)$ bits for the program.

### 7.3 EV8: a bounded binary format (D6)

`measureReal_exec_eighProg_and_not_isApproxDiagonalization_le_of_exponentBits_le` (M): for every
interpretation whose ideal machine meets `IsAccurate` with the constants of a binary format (an
assumption: the analogue of the pilot's IM1 for `binaryFloatSem`, floor $\tau > 0$, is later), the
probability that the run **succeeds** and its output is bad is at most $\theta$, under EV8's
hypotheses. Success is not claimed: `binaryFloatSem` fails out of range, and hdiag does not show
that every operation of a run stays in range (its contract `IsRoundingOf` constrains nothing out of
range). The full form needs that range analysis (D6).

### 7.4 EV7' (blocked on HDIAG-BOUNDS)

`NLAlibScaffold/Eigensolvers/SpectralBisectionProgramSharp.lean`:
`matrixFreeRoundedProb_eighProg_of_logb_le'`, the transfer of EV7' (stated on `research/hdiag-bounds`
as `FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_logb_le_of_hasLaw_eighSampleLaw'`,
being proved). Not in the targets file; dispatched when EV7' lands, after re-checking its hypotheses
against the merged EV7'. Same reduction as §7.2.

### 7.5 Placement

The target definition is in `NLAlib/RandomMatrix/Computation/` (layer 2, where `MatrixFreeRoundedProb`
is, as the pilot's D1); its proof and the samples file import `NLAlib/Eigensolvers` and live there
(`NLAlib/Eigensolvers/SpectralBisectionSamples.lean`, `…/SpectralBisectionProgram.lean`). The
`Eigensolvers` folder has no LAYER entry yet (board T105, maintainer): `check_rules` P1 reports those
files, expected. Registration (D7): one `[[target]]` and one `[[tree]]` in `docs/targets.toml` by
the maintainer once the proof exists.

## 8. Skeleton

63 statements, S 25, M 29, L 8, H 1, in `~/nlalib-harness/pilot/compdyn-s2-targets.json` (waves
0 to 10). External dependencies: the pilot's statements (PK, PP, IM, SG, LP of
`Computation-SignDeflatePrograms.md`), cited by name; they are being proved now.

| ids | statements | file (`NLAlibScaffold/…`) | difficulty |
|---|---|---|---|
| BI1–BI3 | `exec_bindIdx_of_read`, `exec_bindIdx_eq_none`, `IsExactIntLit.toNat_eq_of_lit_eq_some` | `Computation/IndexBinder.lean` | S |
| BI4–BI8 | `isExactToNat_{exactSem,gridSem,binaryFloatSem}`, `mulShrinks_exactSem`, `mulShrinks_gridSem` | same | S ×4, M |
| NI1, NI2 | `exec_normIdx`, `exec_eq_of_normIdx_eq` | same | M, S |
| EC1–EC10 | `exec_{zcopy,zidentity,zneg,zconjTranspose,zhermShift,zhermScale,zhermAvg,ztraceRe}_congr`, `exec_newtonSchulz{Test,Step}Block_congr` | `Computation/KernelCongr.lean` | S |
| SB1–SB3 | `holds_of_exec_eighSignLoop`, `holds_of_exec_eighSignBlock`, `exists_exec_eighSignBlock` | `Matrix/Computation/SpectralBisectionNode.lean` | M |
| EN1–EN10 | leaf, child, deflate (value, success), compress (value, success), split (value, success), node (value, success) | same | M, S, M, M, M, M, M, M, L, M |
| ET1–ET6 | `eighNodeAt_eighSlotTree`, `eighSlotTree_append_of_eighLoc`, `eighLoc_params`, `eighLoc_append_singleton`, `eighLoc_bounds`, `eighLoc_disjoint` | `Matrix/Computation/SpectralBisectionProgram.lean` | M |
| EL1–EL6 | down level (value, success), spent level (value, success), up level (value, success) | same | L, L, M, S, L, M |
| EP1–EP7 | builder (a), (b); tree: `toStmt_compiled`, (a), (b), static counts, weighted counts | same | L, L, S, S, S, M, L |
| ES1–ES4 | `eigh_toFloatMachine_map_samples`, `eigh_congr_samples`, `eigh_eighTapeMachine_eq_eigh_eighIdealTree`, `iIndepFun_eighIdealTree` | `Eigensolvers/SpectralBisectionSamples.lean` | M, M, L, H |
| IA1–IA4 | `isUnifSampler_uniformUnif`, `isAccurate_eighIdealMachine`, `countable_range_uniformUnif`, `countable_range_gaussianNormal` | same | M, M, S, S |
| TT1–TT3 | `matrixFreeRoundedProbEigh`, `matrixFreeRoundedProb_eighProg_of_logb_le`, the bounded format | `Eigensolvers/SpectralBisectionProgram.lean` | M |
| TT4 (blocked) | `matrixFreeRoundedProb_eighProg_of_logb_le'` (EV7') | `Eigensolvers/SpectralBisectionProgramSharp.lean` | M |

## 9. Decisions (sheet `COMPDYN-S2.json`)

RP the re-pin (sign-off); D1 the sign step with the shallow step limit; D2 tests on sizes by trip
counts; D3 static sample positions; D4 `MulShrinks` for M3; D5 the statement change of
`RunsWithin.subst`; D6 EV8 for successful runs only; D7 the target's placement and registration.

## 10. Calibration (§7.2 of the parent note)

| Part | §7.2 estimate | This stage, definitions | statements (scaffold) | proofs (outlined; realistic ×1.5–2) |
|---|---|---|---|---|
| S2a `bindIdx`, `toNat`, `supRange`, all structural cases | 900 – 1,500 | **353 inserted lines, proved** (language, repairs, tools, `normIdx`) | 306 (BI, NI, EC) | 300; 450 – 600 |
| Node step | 1,200 – 2,000 | 220 (blocks, sign) | 526 | 790; 1,200 – 1,600 |
| Level passes, arenas, invariant | 2,500 – 4,000 | 210 (levels, program) + 300 (vocabulary) | 506 | 1,350; 2,000 – 2,700 |
| Lazy sampling and success | 1,000 – 2,000 | (in the vocabulary) | 236 | 730; 1,100 – 1,500 |
| Assembly, target, weighted counts | 800 – 1,500 | 117 (target) + 30 (`eighCount`) | 280 | 330; 500 – 650 |
| **S2** | **6,400 – 11,000** | **about 1,200** | **about 1,850** | **3,500 outlined; 5,250 – 7,050** |

The statements move into `NLAlib/` with their docstrings minus the `Proof:` lines (D8 of
`docs/rules/DIGEST.md`), about 1,300 lines, so S2 lands at about 1,250 + 1,300 + 5,250 to 7,050 =
**7,750 to 9,550 lines**, inside §7.2's 6,400 to 11,000 for the S2 rows, in its middle. Findings:
* **S2a is well below its row** (about 350 lines against 900 to 1,500): every structural case is a few
  lines because `toNatStep` mirrors `cmpStep`, and the binder's body is a loop body; §7.2 priced
  25 to 35 cases at 20 to 60 lines, the actual cases are 5 to 15 lines.
* **The node step is in its row**, as the pilot predicted (two SIGN-sized blocks and the binder).
* **The level passes are below their row** because the recursion vocabulary (`eighLoc`,
  `eighSlotTree`, `EighArenas`) is definitions that make the invariant a statement, and because D3
  makes the samples static: the "hardest part" becomes six M lemmas about `eighLoc` and four L level
  lemmas.
* **Lazy sampling stays the risk**: one H statement (600+ lines realistic, Fable review);
  without D3 it would have followed the draw counter through the whole run.
* S1 (S1a to S1d) plus S2: about 1,200 + 5,300 to 6,400 + 7,750 to 9,550 = **14,000 to 17,000
  lines**, inside the 12,000 to 20,000 of §7.2.

## 11. The merge of `cleanup/hdiag`

`design/compdyn-s1cd` carried copies of six hdiag definition files from `design/hdiag`
(`Matrix/Computation/{Primitives,Deflation,NewtonSchulzSign,EntrywiseRounding}.lean`,
`Polynomial/Approximation/NewtonSchulz.lean`, `RandomMatrix/Gaussian/Complex.lean`; definitions
only). Merging `cleanup/hdiag` (bd81bd1d) gave add/add conflicts in these six and in `NLAlib.lean`.
Resolution: every one of the six takes `cleanup/hdiag`'s file (each declaration of the pilot's copy is
there, byte-identical as Fable confirmed, and its imports are a superset); `NLAlib.lean` keeps both
import lists; the pilot's `KernelContracts.lean` unification (it imports `Primitives.lean` and uses
`NLAlib.MatMulMap`, `QRMap`, `IsMatMulErr`, `IsQRErr`) is kept as is. The merge builds (`--wfail`).
Replaying `Deflation.lean` prints two `PANIC at Lean.Expr.appArg!` infos (lines 216 and 345); they
are in hdiag's file as pushed and do not fail the build.

## 12. Checks

| check | result |
|---|---|
| `lake build --wfail NLAlib NLAlibTools` | passes (4,312 jobs) |
| `lake build NLAlibScaffold` | passes, `sorry` warnings only |
| `scripts/check_rules.py` | 8 errors, all P1 on `NLAlib/Eigensolvers` (no LAYER entry; T105, expected); E8 and S4 found on the way were fixed |
| `scripts/check_refs.py`, `scripts/check_constants.py`, `scripts/check_latex.mjs` (KaTeX) | 0 problems |
| `lake exe mk_all --check` (NLAlib, NLAlibTools) | no update necessary |
| `scripts/Targets.lean` | 1 violation: the `lakefile_sha256` pin (the scaffold entry), expected; closure hashes, trees, statements and approval match after the re-pin |
| `scripts/Programs.lean` | 3 violations, all E4 for the unregistered `newtonSchulzSignProg`, `deflateProg`, `eighProg`, expected |
| `bin/check-skeleton --strict` | 63 targets, 0 names missing an import, 0 unresolved |
