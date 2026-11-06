# Design note: programs with data-dependent sizes, black-box kernels, complex data and samplers (stage COMPDYN, proposal)

Status: approved 2026-11-06 (sheet `COMPDYN.json`); stage S1 implemented and proved, see "S1
implementation status" below. Proposal text, 2026-11-06: Branch `design/computation-dynamic`
(worktree `~/nlalib-design-compdyn`), rebased on `origin/main` a08339af, where Codex's
`feat/rounded-krylov-oracles` has landed (PR #58), so stage S0 is done. Reviewed by Fable
(`~/nlalib-harness/reports/Review-Fable-COMPDYN-Design.md`): approve with changes. Its four
blocking items and items 5 to 11 are applied in this revision (marked "review item n" where they
change a claim). The shallow reference is the amended hdiag branch (`design/hdiag` f5bef8ca,
"algorithms over a floating-point machine interface"). Decision sheet:
`~/nlalib-harness/state/decisions/COMPDYN.json` (APPROVE, Q1 to Q9, M1 to M5). Owner of
`NLAlib/Computation/`: Codex.

**The maintainer's request** (2026-11-05): "The end goal would be for our model of computation
to be able to handle things like this. Perhaps this means we need to allow more in the model."
"This" is the randomized recursive Hermitian eigensolver of [Shah2024], Algorithms 1 to 3
(SIGN, DEFLATE, EIGH), now formalized shallowly on `design/hdiag`
(`docs/design/Eigensolvers-HermitianDiagonalization.md`). The concern is that library algorithms
are examples for later code, so they must not compute outside the model of computation. The aim
is for each such algorithm to be a registered `Prog` with a refinement theorem to its shallow
specification, as for Gram–Schmidt, CG and Lanczos.

## S1 implementation status (2026-11-06)

Stage S1 (S1a + S1b) and M2 are implemented on `design/compdyn-s1` (from `origin/main`
a08339af), by the harness pipeline in place of Codex (decision sheet Q9 = (c); Fable reviews).
Language changes and the repairs they force are proved in `NLAlib/`. The 30 new results were
skeleton statements (`~/nlalib-harness/pilot/compdyn-s1-targets.json`); all are proved and in
`NLAlib/` (placement below), and the scaffold library is gone.

**Language (S1a).**
* `Stmt.kcall o p dims ins outs` and `FStmt.kcall` (operands `(handle, offset)`, dimensions
  `IExp`); `OpKind.kcall p o dims` (one call, recorded with its dimensions);
  `Interp.kernel`/`Interp.kshape` with defaults `none`/`([], [])`, so every existing `Interp`
  construction is unchanged and a kernel call fails unless an interpretation supplies a kernel.
* The run is one shared leaf, `Interp.kcallStore` (`Exec.lean`), called by `exec` and by
  `FStmt.exec`: it reads the contiguous input blocks of the lengths `kshape` gives
  (`Store.readBlocks`), calls the kernel, and writes the output blocks (`Store.writeBlocks`); it
  fails on a wrong number of operands, an output block overlapping another output or an input
  (`blockDisjoint`), a failed read, write or kernel, or a returned block of the wrong length.
  Packed contiguous blocks only (M4): no leading dimension or stride.
* `Stmt.StraightLine` counts `kcall` as straight-line (its kind is fixed by its dimensions);
  `StaticCost` charges one `charge (.kcall p o dims)` step.
* `Stmt.subst` takes a third implementation `implK` for kernel calls; `ImplementsKernel` is the
  certificate, the analogue of `ImplementsOracle`; `exec_subst_sim` and `RunsWithin.subst` gain
  the case and the hypothesis `himplK`. `substKind` maps kernel kinds by `cost`, as oracle kinds.
* `Interp.withKernel` (an interpretation with one kernel replaced) is in `Exec.lean`, since
  rule E6 keeps interpretations in `NLAlib/Computation`.
* `NLAlib/Matrix/Computation/KernelContracts.lean`: `MatMulMap`, `QRMap`, `IsMatMulErr`,
  `IsQRErr` in hdiag's shape (ab8a7041 `Primitives.lean`, decoded normwise contracts, floor
  $\tau$, range $\Omega$), so hdiag's `FloatMachine.IsAccurate` fields are these statements;
  the storage of a matrix in a block (`EntryLayout`, `realLayout`, `pairLayout` for interleaved
  complex pairs, `toMatrix`, `toArray`, column-major, packed); `mmShape`, `qrShape`, `liftMM`,
  `liftQR`; the functional kernel contracts `IsMatMulKernel`, `IsQRKernel` (M3); the exact
  witnesses `exactMM`, `exactQR`.

**Samplers and model (S1b), literals (M2).** `Dist.uniform` with law `volume[|Set.Icc (-1) 1]`
(`Tape.lean`); `IsTapeRounding dec p u c ρ` and `IsExactIntLit dec sem B` (`Contract.lean`);
`MatrixFreeRoundedProb` (`Tape.lean`), the target-level definition approved with the sheet
(Q6/M3).

**Repairs** (no statement of an existing theorem changed, except the three listed below):
structural `kcall` cases in `exec`, `FStmt.exec`, the bridge `FStmt.exec_eq_exec_toStmt`,
`Stmt.compile`, `FStmt.toStmt`, `FStmt.staticCost` and its bound, the run invariants
(`runInv_of_exec_eq_some`, `exec_eq_of_exec_eq_some_of_cnt_load_le`, `shape_usage_eq_of_exec`,
`Stmt.StraightLine`), `Stmt.subst`, `exec_subst_sim`, `substKind`; the `Dist.law` case and its
instance; the Hutch++ compile lemma `compile_substOracle_cooImpl` (one new case); the callers of
`RunsWithin.substOracle` in `Dense.lean` and `Sparse.lean` (one `rfl` argument each); the tools
`KrylovSmoke` (`opcode`, `kinds`, `mem_kinds`) and the NumPy emitter. `ScalarSem` is unchanged in
S1 (its `toNat` is S2), so `failSem` and `binaryFloatSem` need no change yet.

**Statement changes to existing results** (accepted by the coordinator, 2026-11-06; every caller
discharges the new hypothesis by `rfl`).
1. `RunsWithin.subst` (`Subst.lean`, result `computation-substitution`) gains
   `himplK : ImplementsKernel I I' implK cost scratch scratchW`, and `Stmt.subst` takes the third
   implementation `implK`: the simulation needs a certificate for the new node, as §4.3 says. Its
   only caller is `RunsWithin.substOracle`, which supplies it from `hker`.
2. `RunsWithin.substOracle` (result `computation-oracle-substitution`) gains
   `hker : ∀ o ds xs, I.kernel o ds xs = none`. `Stmt.substOracle` renames the oracle names
   `ι → ι'`, and a kernel name in `ι` has no counterpart in `ι'`, so the oracle substitution maps a
   kernel call to `skip` and is stated for abstract interpretations without kernels. The callers
   (`ProgFamily.MatrixFree.storedEntries_substOracle_denseImpl` and `…_cooImpl`) use
   `exactInterp`, whose kernels are the default `none`: they pass `fun _ _ _ => rfl`, and their own
   statements are unchanged. Kernels kept across a substitution with `ι' = ι` use
   `implementsKernel_self` (skeleton K7).
3. `NLAlibTools.KrylovSmoke.mem_kinds` (tools, not the library) gains
   `hk : ∀ ds, k ≠ .kcall () () ds`: kernel kinds are one per dimension list, so no finite list
   contains them all; the smoke programs make no kernel call, and its use (`kinds.all`) is
   unaffected.

**Other deviations from this note.**
1. `IsTapeRounding` takes the rounding `ρ` only (`ρOK` of `MatrixFreeRoundedProb` is a predicate
   on `ρ`); the tape equation `I.tape = ρ ∘ ξ` of §4.5 is built into the model.
2. `MatrixFreeRoundedProb`'s `Contracts` takes the sizes, `Contracts N n I`, since
   `IsExactIntLit dec I.sem n` (§6.3) depends on them.
3. No transposition or conjugation flags in `kcall` dimensions: `dims` is `[l, m, n]` for MM and
   `[m, n]` for QR; $\mathbf{Q}^{\mathsf{H}}$ is formed by the S1c conjugate-transpose kernel.
4. `IsTapeRounding dec p u τ Ω c ρ` has hdiag's floor $\tau$ and range $\Omega$ (as
   `IsNormalSampler`): $\lvert x \rvert \le \Omega \Rightarrow \lvert \mathrm{dec}(\rho(d, i, x)) -
   x \rvert \le c(d)\,u\max(\lvert x \rvert, \tau)$ (Fable S1 review, B3). Without them no rounding
   into a bounded format meets the contract for Gaussian draws. `IsTapeRounding` is in no target's
   closure, so the change moves no registry hash.
5. `scripts/Targets.lean`'s `models` list does not yet name `MatrixFreeRoundedProb` (a check
   script, AGENTS.md rule 1); it needs the entry when the first target concludes it (S1d).

**Re-pin.** By the documented path (CONTRIBUTING §5.5, `docs/targets.toml` header):
`TARGETS_UPDATE=1 lake env lean scripts/Targets.lean` rewrote the closure hashes, then
`sha256sum docs/targets.toml > docs/targets.approved` under the approval given with the sheet
(the S1 change re-pins every target, §4.5, §8.3). Only the nine target closure hashes changed; the
seven tree hashes, the printed statements and normal forms, and the pins are unchanged. The lint
then reports 0 violations. The maintainer's sign-off of this diff is requested before merge (Fable
S1 review, B1). New `docs/targets.approved`:
`7bff66e43f9badd6b21cb2b95b3e21e8a82015d40ce23a58bb7932a9a4a0b234`.

| target | old closure hash | new closure hash |
|---|---|---|
| `MatrixFreeGramSchmidt` | `f4bfd4a997b0e1f2…` | `af26a2cc59a18852…` |
| `MatrixFreeHutchpp` | `8389c47d6d4f5af5…` | `f30f4f842aac163e…` |
| `MatrixFreeProbHutchpp` | `86d55a87d8096636…` | `d9a85ec8490dc567…` |
| `StoredEntriesDenseHutchpp` | `5405ea52c819f343…` | `771e016ca68b29ac…` |
| `StoredEntriesCooHutchpp` | `b30850f87312739f…` | `62fcf12585da26e2…` |
| `StoredEntriesConjugateGradient` | `396272c4512c9f50…` | `74f03a01c2627964…` |
| `StoredEntriesLanczos` | `1c5149f13176c37f…` | `3067f8e5a70ba8b5…` |
| `MatrixFreeConjugateGradient` | `e026690e00398eac…` | `d22d5e3483281f66…` |
| `MatrixFreeLanczos` | `359a6e147dcf49ef…` | `903a3da3d2951891…` |


**Known limitations (non-blocking, Fable S1 review N2, N3, N5).**
* `Stmt.substOracle` turns every kernel call into `skip` (sound under `hker`, but a `kcall` program
  family pushed through `ProgFamily.substOracle` would lose its kernel calls); it should take a
  kernel renaming `ι → ι'`, or fail, when S1c or S1d first substitutes oracles in a `kcall`
  program.
* The NumPy emitter prints `kernel([dims], [ins], [outs])` without the kernel name (the emitter is
  generic in `ι`, which has no `ToString`); to fix when S1d emits a program.
* A kernel does not see the tag `p`, so per-tag kernel accuracy cannot be stated; fine for EIGH
  (one tag), to revisit in S2.

**Checks.** On the language commit (main's `lakefile.toml`): `bash scripts/stage_check.sh`
exit 0 (`--wfail` build, audit, lint, replay, programs, targets 0 violations, refs, constants,
LaTeX, rules), `mk_all --check` for `NLAlib` and `NLAlibTools`. The skeleton commit added an
`NLAlibScaffold` library to `lakefile.toml`, as the stage branches of LB-C and HDIAG do, which moved
the registry's `lakefile_sha256` pin (Targets lint item 4) while the skeleton was being proved. The
clean-up (`cleanup/compdyn-s1`) removes the scaffold library and restores main's `lakefile.toml`
byte for byte, so the pin matches again.

**Skeleton** (`NLAlibScaffold/`, 30 statements, S 20, M 10; revised after Fable's S1 review,
`~/nlalib-harness/reports/Review-Fable-COMPDYN-S1.md`: the read-back of a kernel call split into
the two `Store.writeBlocks` lemmas ST1, ST2, so no statement is L):

| id | statement | file | difficulty |
|---|---|---|---|
| K1 | `exec_kcall` | `Computation/Exec.lean` | S |
| K2 | `Interp.kcallStore_eq_none_of_kernel_eq_none` | `Computation/Exec.lean` | S |
| ST1 | `Store.read_of_writeBlocks_eq_some_of_forall` | `Computation/Store.lean` | M |
| ST2 | `Store.read_of_writeBlocks_eq_some` | `Computation/Store.lean` | M |
| K3 | `Interp.read_of_kcallStore_eq_some_of_forall` | `Computation/Exec.lean` | S |
| K4 | `Interp.read_of_kcallStore_eq_some` | `Computation/Exec.lean` | M |
| K5 | `Interp.exists_kcallStore_eq_some` | `Computation/Exec.lean` | M |
| K6 | `FStmt.exec_kcall` | `Computation/FirstOrder.lean` | S |
| K7 | `implementsKernel_self` | `Computation/Subst.lean` | S |
| KC1 | `EntryLayout.size_toArray` | `Matrix/Computation/KernelContracts.lean` | S |
| KC2 | `EntryLayout.toMatrix_toArray` | `Matrix/Computation/KernelContracts.lean` | M |
| KC3 | `realLayout.get_put` | `Matrix/Computation/KernelContracts.lean` | S |
| KC4 | `pairLayout.get_put` | `Matrix/Computation/KernelContracts.lean` | S |
| KC5 | `isMatMulErr_exactMM` | `Matrix/Computation/KernelContracts.lean` | S |
| KC6 | `isQRErr_exactQR` | `Matrix/Computation/KernelContracts.lean` | S |
| KC7 | `isMatMulKernel_withKernel` | `Matrix/Computation/KernelContracts.lean` | S |
| KC8 | `isQRKernel_withKernel` | `Matrix/Computation/KernelContracts.lean` | S |
| KC9 | `IsMatMulKernel.kcallStore_eq` | `Matrix/Computation/KernelContracts.lean` | M |
| KC10 | `IsQRKernel.kcallStore_eq` | `Matrix/Computation/KernelContracts.lean` | M |
| IL1 | `isExactIntLit_exactSem` | `Computation/Contract.lean` | S |
| IL2 | `IsExactIntLit.mono` | `Computation/Contract.lean` | S |
| IL3 | `IsExactIntLit.exists_exec_litIdx` | `Computation/Contract.lean` | S |
| IL4 | `isExactIntLit_gridSem` | `Computation/Grid.lean` | S |
| IL5 | `isExactIntLit_binaryFloatSem` | `Computation/BinaryFloatSem.lean` | M |
| T1 | `isTapeRounding_id` | `Computation/Contract.lean` | S |
| T2 | `Dist.law_uniform_Icc` | `RandomMatrix/Tape.lean` | S |
| T3 | `Dist.real_law_uniform_Icc` | `RandomMatrix/Tape.lean` | M |
| T4 | `ae_forall_mem_Icc_of_hasLaw_tapeLaw` | `RandomMatrix/Tape.lean` | M |
| T5 | `IsTapeRounding.ae_forall_mem_Icc_of_hasLaw_tapeLaw` | `RandomMatrix/Tape.lean` | S |
| T6 | `MatrixFreeRoundedProb.mono` | `RandomMatrix/Tape.lean` | S |

**Proofs and placement** (2026-11-06, clean-up on `cleanup/compdyn-s1`). All 30 statements are
proved (by haiku workers, one commit per proof on `integrate/compdyn-s1`), golfed, and moved into
`NLAlib/` with the `Proof:` sketches removed (D8). Their elaborated types are unchanged. Each one is
in the file the table names, with one amendment (2026-11-06): **K1 to K5 and ST2 are in a new file
`NLAlib/Computation/KernelCall.lean`** (it imports `Exec.lean`). `Exec.lean` was already 1050
lines and would have grown to about 1210 (rule F10). ST2 is stated with `blockDisjoint`, which is
defined in `Exec.lean`, so it cannot go into `Store.lean`, which `Exec.lean` imports. ST1 is in
`Store.lean`. `RandomMatrix/Tape.lean` now imports `Computation/Contract.lean`, for T5's
`IsTapeRounding`. The proofs of K4 and K5 use two private `Store.writeBlocks` lemmas in
`KernelCall.lean` (a successful write writes one array per block; the writes succeed when every
cell can be written). No public declaration was added beyond the 30. Three were renamed for rule N2 (coordinator,
2026-11-06): KC3 `realLayout_get_put` → `realLayout.get_put`, KC4 `pairLayout_get_put` →
`pairLayout.get_put`, T3 `Dist.measureReal_law_uniform_Icc` → `Dist.real_law_uniform_Icc`.

## 0. Summary

| | |
|---|---|
| Finding | Today's language can already express a data-dependent size, by a *dispatch* loop over every candidate value (checked, §2.2). The result is correct but costly: the counts and the static cost are inflated by a factor of the bound. It cannot express Shah's recursion at a cost the paper would accept, or his black boxes, or a uniform draw. It also has no imaginary unit, so a complex Gaussian cannot be built from real draws in the complex carrier (§2.3). The dispatch idiom is moreover **unsound under `IsRelErrSem`**: `lit_err` lets an integer literal decode to $k(1+\delta)$, so a size stored as a value need not read back as $k$. Hence an **exact-integer-literal contract** is part of the proposal (§4.1, review item 3). |
| Recommendation | Five changes, additive and staged: (1) **black-box kernel calls** `kcall`, with normwise contracts quantified in the model and replaceable by certified programs; (2) **complex data as pairs of real cells**, complex kernels written over real instructions, with no change to the semantics; (3) **`Dist.uniform`** and a **tape-rounding contract** with a **rounded probabilistic model**; (4) **a bounded index binder** `bindIdx p x bound body`, which reads a cell, converts it to a natural (a new `ScalarSem.toNat` with a default value, and a separate exactness contract), clamps it to an index expression `bound`, and binds it as an index variable; (5) **no recursion construct**: EIGH runs level by level (a `loop` over depths), and a `fix` construct is reconsidered when a second recursive algorithm comes. Not recommended: `IExp.cell` (index expressions that read the store), a complex scalar carrier with componentwise rounding of products, and a first-class `fix` now. |
| Anti-cheating | F2 restated as seven invariants I1 to I7 (§3). Every recommended change keeps I1 to I6. One relaxation of I7 is deliberate and stated: data may become an index value, but only through a counted `bindIdx` node whose bound is an index expression over sizes, so resources stay functions of the sizes. |
| Staging | S0 (Codex's branch) is done: PR #58, main a08339af. S1 kernels, complex pairs, uniform draws, tape contract, rounded probabilistic model; then SIGN and DEFLATE as programs (no data-dependent size). S2 `bindIdx`; then EIGH. Each stage is one change of `FStmt`/`exec`, so one re-pin of the target registry, which the maintainer approves. |
| EIGH as a program | §6. Sizes $n$, $D$ (depth budget $\ell_0 + 1$), $F$ (sign fuel). Declared buffers: $\mathbf{A}$ (interleaved complex), parameters, outputs $\mathbf{U}$, $\mathbf{d}$. Level arenas hold block-diagonal node matrices, bases and partial outputs. A downward `loop` over depths and an inner `loop` over slots, with `bindIdx` for each node's size, compute the nodes. An upward `loop` assembles $[\mathbf{Q}_+\mathbf{U}_+\ \mathbf{Q}_-\mathbf{U}_-]$. |
| Effort (estimate) | About 12,000 to 20,000 lines, 2 to 4 times the Lanczos program bridge (5,446 lines) and 1.5 to 2.5 times CG (8,181 on a08339af). An estimate, not a measurement, and probably a floor (review item 8). The pilot S1d (SIGN and DEFLATE as programs) calibrates it before S2b is estimated again (§7.2). |
| Coordination | Codex's work is on main, so there is nothing left to sequence against it; Codex owns `Computation/` and should implement or review S1a and S2a. The breakage, audited on a08339af (§8.1): new `Stmt`/`FStmt` constructors and the new `Dist` constructor each re-hash all nine registered targets; `RunsWithin.subst` gains hypotheses; `substKind` (`Subst.lean`) and `NLAlibTools/KrylovSmoke.lean` match `OpKind` (and `Dist`) exhaustively; and `ScalarSem.toNat` with a default still breaks two anonymous-constructor sites, `failSem` and `binaryFloatSem`. hdiag has already adopted what an equality refinement needs (§8.2): `FloatMachine` with `toNat = ⌊·⌋₊`, machine-computed parameters, $\beta$ as a stored input, one rounding per operation. |

## 1. Requirements

### 1.1 Driving example: EIGH ([Shah2024], Algorithms 1 to 3)

From `~/nlalib-harness/research/hdiag/source/out.tex` (§1.2 model, Definitions 1.1 to 1.4, Algorithms 1 to 3), with what each line needs from a program:

| Source line | Needs |
|---|---|
| Model: $\lvert\mathrm{fl}(z) - z\rvert \le u\lvert z\rvert$ for $z \in \mathbb{C}$; exact halving; $\lg\lg(n/\varepsilon) + O(1)$ exponent bits | complex data with a rounding contract; bounded exponent (Codex's `binaryFloatSem`, a semantics, no language change) |
| Definition 1.1 MM: $\lVert\mathrm{MM}(\mathbf{A}, \mathbf{B}) - \mathbf{A}\mathbf{B}\rVert \le \mu_{\mathrm{MM}}(n)u\lVert\mathbf{A}\rVert\lVert\mathbf{B}\rVert$, $T_{\mathrm{MM}}(n)$ flops, convex | a black-box kernel with a normwise contract and a cost per call |
| Definition 1.2 QR: backward-stable $\mathbf{Q}$, $\mathbf{R}$ | a second black box (none exists; the library's MGS program is not backward stable in $\mathbf{Q}$) |
| Definitions 1.3, 1.4: $\mathrm{Unif}(s)$ within $su$ of a uniform on $[-s, s]$; $\mathrm{Normal}()$ within $c_{\mathrm{N}}u\lvert z\rvert$ of a complex Gaussian | a uniform draw; complex Gaussian from real draws; a coupling contract between computed and ideal draws |
| Algorithm 1 SIGN: repeat $\mathbf{A}_{k+1} = g(\mathbf{A}_k)$ until $\lVert\mathbf{I} - \mathrm{MM}(\mathbf{A}_k, \mathbf{A}_k)\rVert_{\max} \le \varepsilon/(4n)$ | early exit (`whileFuel`, exists); a max-norm reduction (exists, by `ite`) |
| Algorithm 2 DEFLATE: $\mathbf{G}$ Gaussian, $(\mathbf{Q}, \mathbf{R}) = \mathrm{QR}(\mathrm{MM}(\tilde{\mathbf{A}}, \mathbf{G}))$, first $r$ columns | MM, QR; $r$ a size when DEFLATE stands alone, a datum inside EIGH |
| Algorithm 3 lines 1–4: base cases $n = 1$, $R \le \varepsilon R_0$ | comparisons (exist) |
| lines 5–7: $\varepsilon'$, $R'$, $\delta$ with $\sqrt\rho$, $\log(4/\rho)$ | $\varepsilon'$, $R'$ computed by counted operations; $\delta$ replaced by a stored accuracy $\beta$ below the analysis bound, a declared input, as hdiag does (§4.7) |
| line 10: $k_\pm = \mathrm{round}(\operatorname{tr}\mathbf{P}_\pm)$ | **a rounded value becomes an integer** |
| lines 11–14, 18: recursion on $k_\pm \times k_\pm$ matrices | **data-dependent sizes, offsets and trip counts; recursion** |
| line 16: $\mathbf{C}_\pm = \mathrm{MM}(\mathrm{MM}(\mathbf{Q}_\pm^{\mathsf{H}}, \mathbf{A}), \mathbf{Q}_\pm)$ | MM with a conjugate-transposed operand |
| line 20: $[\mathbf{W}_+\ \mathbf{W}_-]$ | **a write at column offset $k_+$** (a data-dependent offset) |
| root call: $R_0 = \lVert\mathbf{A}\rVert$, $\ell = \lceil\lg(1/\varepsilon)\rceil + 5$ | $R_0$, $\varepsilon$, $\beta$: declared inputs with a precondition; $\ell_0$ and the sign fuel: sizes (§4.7, M5) |

### 1.2 Other library algorithms that need the same extensions

| Algorithm (library home) | Today | Needs |
|---|---|---|
| Lanczos and CG with early stopping, followed by the use of the active length $m$ (Lanczos-FA $f(\mathbf{T}_m)\mathbf{e}_1$, the eigenvalues of $\mathbf{T}_m$) (`Krylov/Processes/LanczosProgram*.lean`) | The program runs all $q$ steps and writes zero tails after a breakdown (`Lanczos-Rounded-Program-Bridge.md`, "Active prefix"); $m$ exists only in the theorem | `bindIdx` on the stop index, so a postprocessor of size $m$ (S2) |
| Rank-revealing Gram–Schmidt, adaptive range finders (`Matrix/Factorizations/GramSchmidtProgram.lean`, `LowRank/`) | The rank shows only as zero columns (D6); a consumer cannot size by it | `bindIdx` on the computed rank; column pivoting needs one data-dependent column offset per step (S2) |
| Block Lanczos with deflation, randomized block Krylov | block width fixed | `bindIdx` on the shrinking width (S2) |
| Divide-and-conquer tridiagonal eigensolver, recursive QR or Cholesky, Strassen-type MM | not expressible | recursion: level loops or a worklist with `bindIdx`; `fix` reconsidered then (Q3) |
| Sparse matrices with index arrays (CSR) | `cooImpl` takes its pattern as host data (F5) | `bindIdx` per access with an O(1) conversion: this is why Q2 recommends `ScalarSem.toNat` over conversion by comparisons |
| Complex Krylov, complex Householder | exact kernels already over $\Bbbk$; rounded analyses real only | complex pairs (S1) |

## 2. What the language can and cannot express (verified)

Read: `NLAlib/Computation/{Syntax,Exec,FirstOrder,Compile,StaticCost,Subst,Model,Exact,Contract,Allocation}.lean`, `RandomMatrix/Tape.lean`, `docs/design/Computation.md` (D1, D3, D4, D11, D12, D16 to D19, F1 to F7, G27 to G35).

### 2.1 The brief's list, checked

1. **Sizes from data: confirmed.** `IExp` has `var`, `const`, `add`, truncated `sub`, `mul`
   and `mod`; it has no division and no cell (`Syntax.lean`). `IExp.eval : IExp ℕ → ℕ` is
   store-free (`Exec.lean`). `litIdx` writes an index value into a cell, but nothing converts a
   value into an index. Loop bounds, `alloc` lengths, `apply` offsets and column counts, `rom`
   indices and `whileFuel` fuel are all `IExp`. There is no indirect addressing.
2. **Recursion: confirmed.** `named` is a label (`exec (.named _ _ body) = exec body`, rule E8),
   and F4 chose macro expansion. Subprograms are expanded, so recursion to a symbolic depth
   cannot be unrolled into one finite tree.
3. **Oracles: confirmed.** `apply` multiplies a block of `cols` columns by the
   `height o × height o` matrix of `o`. `MatrixFree` gives every name the same $\mathbf{A}$
   (G32). The only accuracy contract is `IsMatvecErr`, for one column. There is no MM of two
   stored operands and no QR. The real BLAS `gemm` exists as a program (`BLAS/MatrixKernels.lean`).
4. **Real-only rounding: confirmed, with a refinement.** The *exact* semantics is over any
   `RCLike` $\Bbbk$ (`exactSem`: `conj`, `re`, exact complex arithmetic; comparisons fail off the
   real line, Q4 of F12). The exact kernels (`ger` with `conj`) are complex-ready. The contracts
   (`IsRelErrSem`, `IsArithErrSem`, Codex's `AbsRelErr`) decode into $\mathbb{R}$, and `conj`
   and `re` are the identity there.
5. **Samplers: confirmed.** `Dist` is `gaussian | rademacher`, and `Dist.law` and `tapeLaw`
   fix their laws (`RandomMatrix/Tape.lean`). Moreover, **no rounded model has a tape law**:
   `MatrixFreeRounded` quantifies over every `Interp`, tape included, so no rounded result about
   a randomized program can be stated today.
6. **StaticCost: confirmed, and sharper than stated.** `FStmt.staticCost` already handles
   data-dependent *control*: `ite` takes the pointwise maximum, and `whileFuel` charges
   `fuel ×` (comparison + body). What it cannot see is a data invariant, such as "the node sizes
   at one level sum to $n$" (§4.6).

### 2.2 New finding: data-dependent sizes are already expressible, at a cost

A loop over every candidate value, guarded by an equality test, turns a cell's value into a
loop variable. Checked on 2026-11-06 in a scratch file against main (removed afterwards):
```lean
def dispatchFam : ProgFamily Unit Unit 0 1 := fun VB VI N _ h => Builder.run do
  let t ← Builder.alloc () 1
  Builder.forRange (N + 1) fun k => do
    Builder.ins (.litIdx () ⟨t, 0⟩ (.var k))
    Builder.ifThenElse () .eq ⟨h 0, 0⟩ ⟨t, 0⟩
      (do let w ← Builder.alloc () (.var k)                     -- data-dependent length
          Builder.forRange (.var k) fun j => Builder.ins (.copy () ⟨w, .var j⟩ ⟨h 0, 0⟩))
      (pure ())
```
It compiles (`(ProgFamily.compile dispatchFam).isSome = true := by rfl`), and its instantiation
equation is `rfl`. Run under a rational semantics with the input cell holding $3$ and $N = 5$, it
gives peak $5 = 1 + 1 + 3$ cells and $15$ operations (6 `litIdx`, 6 comparisons, 3 copies).
The idiom is sound, but it is a poor model:
* the dispatch costs $O(\text{bound})$ per conversion;
* `StaticCost` sums the body over every $k$, so the bound is $\sum_k \mathrm{body}(k)$ and not
  $\max_k$;
* $d$ data-dependent offsets need $d$ nested dispatches. EIGH's nodes need two (start and size),
  so $O(n^2)$ tests per node and a static cost inflated by $n^2$.

The idiom shows that a binder adds no new *power*. It adds the right *cost*, and that is what
an honest model needs.

**The idiom is also unsound under the standard-model contract, not just slow** (review item 3).
`lit_err` (`Contract.lean`) gives only $\mathrm{dec}(\mathrm{lit}_p\,k) = k(1 + \delta)$ with
$\lvert\delta\rvert \le u$. So the equality test against `litIdx k` may fail for every $k$, and
the program then silently does nothing. The same clause breaks a round trip the proposal itself
needs: a size $k$ written by `litIdx` and read back by `bindIdx` gives
$\lfloor k(1 + \delta)\rfloor_+ = k - 1$ when $\delta < 0$. Hence the separate contract
`IsExactIntLit` (§4.1, M2). With it, stored sizes are ordinary data: words in cells, written by
`litIdx` and read back by `bindIdx`. The model then needs no index-valued storage.

### 2.3 Further gaps found for Algorithms 1 to 3

* **No imaginary unit.** Literals are rational, draws are real (`tape d i := (ξ d i : 𝕜)`), and
  `sqrt` fails off $[0, \infty)$. So a program over $\Bbbk = \mathbb{C}$ produces only real
  values from real data, and a complex Gaussian cannot be formed. With complex pairs (Q5) this
  does not arise.
* **Componentwise rounding of a complex product is not what hardware does.** The imaginary part
  $ad + bc$ computed as $\mathrm{fl}(\mathrm{fl}(ad) + \mathrm{fl}(bc))$ can lose all relative
  accuracy. Example in binary64: $a = 3$, $b = c = 1$, $d = -\mathrm{fl}(1/3)$ with
  $\mathrm{fl}(1/3) = 6004799503160661 \cdot 2^{-54} = 1/3 - 1.85 \cdot 10^{-17}$. Then
  $3\,\mathrm{fl}(1/3)$ rounds to $1$, so $\mathrm{fl}(\mathrm{fl}(ad) + \mathrm{fl}(bc)) = 0$,
  while the exact imaginary part of the stored operands is $5.6 \cdot 10^{-17}$ in magnitude: a
  componentwise relative error of $1$ (checked by Fable). IEEE complex multiplication meets only the normwise
  bound $\lvert\mathrm{fl}(zw) - zw\rvert \le \sqrt2\gamma_2\lvert zw\rvert$ [Higham2002,
  Lemma 3.5]. A contract that rounds every complex operation componentwise would let an algorithm
  cheat in its error model.
* **Integer conversion of a rounded float.** There is no floor or round operation. `round` is not
  expressible from the contract's operations.
* **Transcendental parameters.** $\log(4/\rho)$ in $\delta$ and $\lceil\lg(1/\varepsilon)\rceil$
  in $\ell$ have no operation. The amended hdiag (f5bef8ca) avoids both: it takes one stored
  accuracy $\beta$ below the analysis bound as an input ("no square root or logarithm is
  needed"), and the depth counter $\ell$ is a natural number. The program does the same (§4.7).
* **Rounding granularity and scalar parameters: resolved on hdiag.** The first hdiag version
  rounded composite expressions once (`roundHermitian ((2⁻¹ : ℝ) • (1 + B))`) and kept
  $R'$, $\varepsilon'$ exact. The amended version computes everything on a `FloatMachine`, one
  rounding per operation: `hermShift`, `hermScale`, `hermAvg`, and `eighNextParams` with
  $\mathrm{fl}(\mathrm{fl}(\mathrm{fl}(1/2) + \mathrm{fl}(2/\ell))R)$ and
  $\mathrm{fl}(\mathrm{fl}(1 - \mathrm{fl}(1/\ell))\varepsilon)$. The paper's only exact-halving
  assumption, $\mathrm{fl}(x/2) = \mathrm{fl}(x)/2$, is no longer used (the division by `ofNat 2`
  is rounded); OQ6 records the clause for later.
* **Exact integer literals.** `IsRelErrSem` lets a literal of an integer be inexact (§2.2), and
  hdiag's `ofNat` is rounded too. A size stored as a value needs `IsExactIntLit` (§4.1).
* **No conditional on index expressions.** "$k = 0$" or "$k_+ = k$" goes through two literal
  cells and one counted comparison (cheap; exact only under `IsExactIntLit`). An uncounted
  `iteIdx` (as G11 allows for control on sizes) is possible if programs need many such tests; not
  now (review item 11).
* **Fresh samples at data-dependent tape positions.** The tape is read sequentially, and how many
  nodes precede a node depends on the data. So the tape position of a node's sample is
  data-dependent. Each sample is still fresh (§7.2), but the identity between "the tape" and the
  shallow "tree of samples `List Bool → EighSample N`" is a lazy-sampling lemma, not a
  reindexing.
* **Counts for a black box.** Paper costs are in $T_{\mathrm{MM}}(n)$, so a call must be counted
  with its dimensions.
* **Nothing else is missing.** Early exit (`whileFuel`), max-norm tests (`ite`), base cases,
  bounded exponents (a semantics) and exact halving (a contract clause, Codex's direction) need no
  language change.

## 3. The anti-cheating principle, stated precisely

A *registered* result is `theorem t : T` with `T` a library target about a registered tree
(F1). What F2 and the models guarantee about the witness, as invariants:

* **I1 (finite data).** The witness is a closed term of `FStmt P ι b (r + 1)`. Each constructor
  argument is a natural, a rational, a string, a `Fin`, an `IExp`/`Cell`/`Instr`/`Arg`, a
  subtree, or a value of `P`/`ι`; none is a function. Its constructor normal form is hashed in
  the registry (F1, E3).
* **I2 (fixed before data).** The models bind the tree before the sizes, the inputs, the matrix,
  the tape and the interpretation (G27). The tree cannot depend on any of them, and `P`/`ι` cannot
  carry data (G31).
* **I3 (one run).** The only computation on data is the library run `FStmt.exec`. It is in the
  target's closure and hashed with it, its leaves are written out (F3), and nothing in the tree
  is evaluated by Lean except `IExp` arithmetic (G33).
* **I4 (data enter through counted doors).** Data enter only through counted operations: reads
  of declared buffers by instructions, oracle calls (`load`, `matvec`), `rom` reads and draws.
  Every scalar operation is charged by kind.
* **I5 (resources are functions of sizes).** The target's counts and memory are functions of the
  sizes (G28), and `RunsWithin` makes them upper bounds for every run.
* **I6 (semantics is quantified or fixed).** The arithmetic is either fixed by the library
  (`exactInterp`, `storedInterp`) or quantified over all semantics meeting a contract stated in
  the target (`MatrixFreeRounded`), with success clauses (D19). So a theorem cannot exploit a
  particular rounding.
* **I7 (data never become addresses).** Data reach control only through comparisons (`ite`,
  `whileFuel`), which are counted. Indices, offsets, lengths and trip counts are index
  expressions over sizes and loop variables.

**The test a proposed extension must pass.** It keeps I1 to I6, and if it relaxes I7 it does so
through a counted node with a static bound. Table:

| Extension | I1 | I3, I4 | I5 | I6 | I7 |
|---|---|---|---|---|---|
| `kcall` (Q4) | constructor with `IExp`/handle arguments | the kernel is an `Interp` field, charged once per call with its dimensions | the call count and dimensions are bounded by functions of the sizes | the model quantifies over all kernels meeting a contract the target states; satisfiable by exact witnesses | kept |
| complex pairs (Q5) | unchanged | unchanged | unchanged | unchanged (real contracts) | kept |
| `Dist.uniform`, tape contract (Q6) | one `Dist` constructor | a draw is counted | unchanged | the computed draws are any rounding of the ideal tape meeting the contract; the ideal tape has the library law | kept |
| `bindIdx` (Q1, Q2) | constructor, body a subtree | reads a cell, charged one `toNat` | the bound is an `IExp` over sizes and outer indices, so `StaticCost` takes a supremum over a finite range | the conversion is quantified by a contract (exact floor on decodings, `IsExactToNat`), and stored sizes read back exactly by `IsExactIntLit` | **relaxed**: a value becomes an index, clamped to the bound |
| `IExp.cell` (rejected) | unchanged | **uncounted** reads inside index arithmetic | lengths unbounded unless every use carries a bound | — | relaxed silently, at every use |
| `fix` (deferred) | finite (a node and a `recurse` leaf) | the run grows by a fuel-indexed fixpoint (trusted base +80 to 120 lines) | needs a recurrence-solving `StaticCost` | unchanged | kept |

Two cheats the extensions must be checked against, with fixtures in the style of
`scripts/AccessModelFixtures.lean`:
* **A kernel that answers the problem.** For example, a "QR" whose interpretation returns the
  eigenvectors of its input. This is excluded because the model quantifies over *every*
  interpretation meeting the contract, adversarial ones included, and the contract is part of the
  hashed target. Fixture: a program correct only for the exact QR fails the target.
* **Free arithmetic in index expressions on data.** After `bindIdx`, `IExp` arithmetic
  ($+, -, \times, \%$) on the bound value is uncounted, as address arithmetic is in a word-RAM.
  The value is clamped to `bound`, and each `IExp` has constant size in the tree, so this is
  $O(1)$ word operations on $O(\log \mathrm{bound})$-bit words per executed node. That is the
  standard word-RAM convention, stated here as a (D) item of F10. I7's relaxation was already foreseen by F12-Q1 (an index read for `romIdx`). Fixture: a program that
  computes a product of two data via `bindIdx` and `litIdx` is counted at least the two `toNat`
  charges and one literal.

## 4. Options per gap

The breakage counts below come from `grep` on main a08339af, Codex's files included:
* Structural cases on `Stmt`/`FStmt` live only in `Syntax`, `Exec` (the run and its seven
  invariants, `StraightLine`, `usage_eq`), `Subst` (`Sim`, `RunsWithin.subst`), `FirstOrder`
  (the run and the bridge), `Compile` (`compile`, `toStmt`), `StaticCost` (the fold and its
  theorem) and the NumPy emitter. No program file does an exhaustive case analysis on statements.
* Exhaustive matches on `OpKind`: `substKind` (`Subst.lean`), and `opcode`, `kinds` and
  `mem_kinds` in `NLAlibTools/KrylovSmoke.lean`. The latter also matches `Dist` exhaustively. The
  cost functions `denseCost` and `cooCost` end in a wildcard.
* `ScalarSem` constructions: `exactSem`, `gridSem`, `fixedPointSem`, `checkedFloatSem`,
  `finiteFloatSem` and `NLAlibTools`' `floatSem` use `where`, so a defaulted field is filled.
  `failSem` (`Contract.lean`, an anonymous constructor) and `binaryFloatSem`
  (`BinaryFloatSem.lean`, `refine ⟨?_, ?_, ?_, ?_, ?_⟩`) do not: an anonymous constructor does not
  fill defaults (Fable checked: "Insufficient number of fields"). That is one line each.
* `Interp` constructions all use `where` or `storedInterp …`, so defaulted fields are filled.
* There are 3,236 uses of `IExp.eval` in 124 files.

### 4.1 Data-dependent sizes (Q1) and the conversion (Q2)

* **(a) Bounded index binder (recommended).**
  ```lean
  -- Stmt
  | bindIdx (p : P) (x : Cell VB VI) (bound : IExp VI) (body : VI → Stmt P ι VB VI)
  -- FStmt
  | bindIdx {nb ni : ℕ} (p : P) (x : Cell (Fin nb) (Fin ni)) (bound : IExp (Fin ni))
      (body : FStmt P ι nb (ni + 1)) : FStmt P ι nb ni
  -- exec: read x at tag p, convert, clamp, charge one `toNat p`, bind
  | .bindIdx p x bound body, st => (st.store.read p x.buf x.idx.eval).bind fun v =>
      (I.sem.toNat p v).bind fun k =>
        exec (body (min k bound.eval)) { st with cnt := st.cnt + I.charge (.toNat p) }
  -- StaticCost: the charge, then the supremum of the body over the range of the bound
  | .bindIdx p _ bound body, ρI => (StaticCost.step (charge (.toNat p))).seq
      (StaticCost.supRange (bound.evalIn ρI + 1) fun k => body.staticCost charge width (Fin.snoc ρI k))
  ```
  *Semantics.* An index variable bound once and immutable in the body, exactly like a loop
  variable. It is clamped rather than failing, as the shallow `min k (round …).toNat` does.
  *Proofs.* `IExp` and every `eval` lemma are unchanged. One new case in each of the
  structural sites above, about 25 to 35 cases at 20 to 60 lines each. `StraightLine` excludes
  `bindIdx` (two runs can bind different values). `RunsWithin.subst` keeps `bindIdx` as it keeps
  comparisons and needs `htoNat : I'.sem.toNat = I.sem.toNat`, beside `hcmp`. Existing program
  proofs: none breaks (no program uses the constructor); the registry re-pins. About 700 to
  1,100 lines.
* **(b) `IExp.cell c`**, an index expression that reads a cell, failing if it is not a natural.
  `IExp.eval` becomes `IExp.evalSt : Store → IExp ℕ → Option ℕ`. All 3,236 uses, every kernel
  specification's `eval` hypotheses, the bridge, `IExp.subst` and `StaticCost` (costs then depend
  on the store) change. It also relaxes I7 at every use, uncounted. Not recommended.
* **(c) The dispatch idiom only** (§2.2). No change, but costs are inflated by the bound per
  offset. Acceptable for a one-off. Not a model for examples.
* **Sized allocation from a cell** is (a) followed by `alloc p (.var k)`, so no separate
  construct is needed.

The conversion inside (a) (Q2):
* **(a) `ScalarSem.toNat : P → K → Option ℕ` (recommended),** with default `fun _ _ => none`.
  Every `where` construction still elaborates. The two anonymous-constructor sites, `failSem` and
  `binaryFloatSem`, need one added component each (corrected after review item 1; the first
  version said "none breaks"). It comes with a *separate* contract
  `IsExactToNat dec sem : ∀ p x, sem.toNat p x = some ⌊dec p x⌋₊`, total, with $0$ below zero. That
  is hdiag's `FloatMachine.toNat_eq : M.toNat x = ⌊dec x⌋₊`, so the refinement is an equality
  with no case split (M1). It mirrors `AddsZeroExactly`, so no existing contract proof changes.
  Truncation of a float is exact in IEEE, so the clause is honest.
  `exactSem` gets `toNat x := if im x = 0 then some ⌊re x⌋₊ else none`, using Mathlib's
  `Nat.floor`. The new `OpKind.toNat p` is charged one per conversion, O(1), which sparse access
  needs.
* **The exact-integer-literal clause (review item 3, M2)**, also separate:
  ```lean
  def IsExactIntLit (dec : P → K → ℝ) (sem : ScalarSem P K) (B : ℕ) : Prop :=
    ∀ p (k : ℕ), k ≤ B → ∃ z, sem.lit p k = some z ∧ dec p z = k
  ```
  with $B \ge n$ in the target. It holds in IEEE below $2^{t}$ (binary64: $2^{53}$), for `gridSem`
  and for Codex's `binaryFloatSem` under the paper's precision hypothesis, and for `exactSem` with
  every $B$. Without it, `litIdx k` followed by `bindIdx` can read $k - 1$, and every "$k_+ = k$"
  test through cells can fail (§2.2). It is a member of the target's `Contracts` (§6.3).
* **(b) Floor by counted comparisons:** $k = \#\{1 \le j \le B : \mathrm{lit}_p(j) \le x\}$, using
  only `sem.lit` and `sem.cmp`. No `ScalarSem` field, but O(bound) per conversion; `subst` needs
  `hlit` as well; and under a relative-error literal the floor is only approximate. Adequate for
  EIGH (a trace within $0.1$ of an integer), too slow for sparse.

### 4.2 Recursion (Q3)

* **(a) No construct: level loops or a worklist, with library lemmas (recommended for now).**
  For EIGH the nodes at one depth partition $[0, n)$ into contiguous ranges. So a `loop D` over
  depths, an inner `loop n` over start slots, and `bindIdx` on each slot's stored size compute a
  level, and a reversed `loop D` assembles it (§6). The invariant is "level arena $d$ holds the
  nodes `eighNodeAt` gives at depth $d$". The hdiag branch already defines that function, so the
  proof needs no stack. A general recursion (divide and conquer with a merge) becomes a
  `whileFuel` worklist over an explicit stack arena, and its correctness is one library theorem
  proved once (`exec_worklist`, a fold over a binary tree with pre/mid/post phases, about 800 to
  1,200 lines), written when the second recursive algorithm comes.
  Breakage: none (no semantic change). F2 and I1 to I7 hold trivially.
* **(b) A first-class `fix fuel body` with `recurse hargs iargs` leaves.** The run becomes
  fuel-indexed with an environment of the enclosing body, so `exec` is no longer structural on
  `Stmt` alone. Every invariant lemma, the bridge, `Sim` and `StaticCost` (which must solve a
  recurrence $C(d) = \mathrm{node} + 2C(d - 1)$) change. About 80 to 120 lines of trusted run and
  1,500 to 2,500 lines of lemmas. Its gain is that refinement proofs follow the shallow recursion
  by induction on fuel. F4 already recorded the non-recursive `call` table as an alternative. Revisit
  both when a second recursive algorithm, or the size of expanded trees, asks for it.
* **(c) Non-recursive `call` (F4's alternative).** Smaller trees, no recursion; it does not solve
  this gap.

### 4.3 Black-box kernels versus programs (Q4)

* **(a) First-class kernel calls with contracts (recommended).**
  ```lean
  | kcall (o : ι) (p : P) (dims : List (IExp VI)) (ins outs : List (VB × IExp VI))
  -- Interp, new fields with defaults (no existing Interp construction breaks)
  kernel : ι → List ℕ → List (Array K) → Option (List (Array K)) := fun _ _ _ => none
  kshape : ι → List ℕ → List ℕ × List ℕ := fun _ _ => ([], [])     -- block lengths in, out
  -- OpKind: one call, recorded with its dimensions; flops are a weight (Finsupp.weight)
  | kcall (p : P) (o : ι) (dims : List ℕ)
  ```
  The run reads the input blocks of the lengths `kshape` gives, calls `kernel`, and writes the
  output blocks. The blocks are **contiguous** (`readBlock p buf off len`), and no leading
  dimension or stride is passed (review item 5, M4). The program therefore stores each operand
  packed: in EIGH a node of size $k$ at $[lo, lo + k)$ keeps its $k \times k$ matrix contiguously
  at arena offset $lo \cdot n$. Nodes at one level are disjoint intervals and $k^2 \le kn$, so the
  blocks $[lo\,n, lo\,n + k^2)$ of different nodes are disjoint. This needs no copies and keeps the
  memory at $O(Dn^2)$. A stride argument in `dims` would put more into the trusted run. It fails if the blocks alias, as `apply` does, or if the kernel returns `none`.
  Kernel names reuse `ι`, so no new type parameter is needed. The dimension list carries
  transposition and conjugation flags, as BLAS does (`'N'`/`'C'`), which line 16's
  $\mathbf{Q}^{\mathsf{H}}$ needs.
  *Contracts* live in the Matrix layer, since `specNorm` is Matrix vocabulary (rule E5):
  `NLAlib/Matrix/Computation/KernelContracts.lean`. They lift hdiag's shallow `IsMatMulErr`
  and `IsQRErr`:
  `IsMatMulKernel I o dec mm := I.kernel o = liftMM dec enc mm ∧ I.kshape o = mmShape`, with
  `mm` meeting `IsMatMulErr u τ Ω μ mm`. The lift is *functional* on decodings, which the equality
  refinement of §7 needs. Exact witnesses (exact product, the library's exact QR) make the contracts
  satisfiable, as hdiag C1 and C2 do.
  *Implementations* are certified by `ImplementsKernel`, the analogue of `ImplementsOracle`:
  `gemm` for MM now, a Householder QR program later. The `RunsWithin.subst` simulation gains a
  `kcall` case, so a theorem proved against the contract becomes, by the proved substitution
  theorem, a theorem about a program with no black box. This is D4/D18's pattern, and Codex's
  `IsMatvecRoutine` (one certificate for a stored kernel or an oracle) is its first instance.
  *Breakage:* additive constructor plus defaulted fields. `denseCost`/`cooCost` end in a wildcard
  (`| _ => 0`), so they need no case. `substKind` and `KrylovSmoke`'s `opcode`/`kinds`/`mem_kinds`
  match exhaustively and need one case each. The registry re-pins.
  *Exact model:* `exactInterp.kernel` defaults to `none`, so a `kcall` program has no
  `MatrixFree` (exact) target unless an exact kernel interpretation is supplied. That is fine for
  EIGH. SIGN's pilot target is deterministic (`MatrixFreeRounded` with kernels); DEFLATE's needs
  `MatrixFreeRoundedProb` (review item 9).
  About 800 to 1,300 lines, including contracts and witnesses.
* **(b) Programs only.** MM is `gemm` (real, exists; complex pairs needed). QR must be a
  Householder program with a backward-error analysis ([Higham2002], Theorem 19.4). For complex
  data that is about 2,500 to 4,000 lines before EIGH can start. The paper's statement, which is
  relative to any MM and QR, would also be lost: only one implementation would be proved.

### 4.4 Complex arithmetic (Q5)

* **(a) Complex as pairs of real cells (recommended).** Interleaved layout: entry $(i, j)$ of an
  $m \times n$ complex matrix at $2(i + mj)$ (real) and $2(i + mj) + 1$ (imaginary), as in BLAS,
  LAPACK and NumPy `complex128`. Complex kernels (`zcopy`, `zaxpy`-type, the diagonal shift,
  the Hermitian part, the max-modulus test, the real trace, the conjugate transpose) are `named`
  BLAS kernels over real instructions, each with exact and rounded specifications decoded into
  $\mathbb{C}$ (`HoldsC`, `HoldsDecodedC`).
  *Semantics:* none changes. Every operation is a real IEEE operation, so the rounding is
  exactly componentwise IEEE, which is the maintainer's stated preference. Complex multiplication
  then gets the honest normwise bound (§2.3) as a derived lemma.
  *Breakage:* none. About 1,500 to 2,500 lines of kernels and lemmas.
  *Limit:* a complex *oracle* over pairs is the realification of $\mathbf{A}$, and `MatrixFree`
  quantifies over all real $2N \times 2N$ matrices. So complex matrix-free targets need a model
  with a precondition on $\mathbf{A}$. EIGH stores its matrix, so this is not needed now (OQ4).
* **(b) A complex carrier with a new contract** (`dec : P → K → ℂ`): add and subtract
  componentwise relative, multiply normwise $\sqrt2\gamma_2$, comparisons on the real line. This
  duplicates every kernel analysis, conflicts with the real contracts Codex is extending, and adds
  a carrier relation to the bit-level story (D16).
* **(c) Componentwise rounding of every complex operation** (the shallow `roundScalar` applied
  to products). Unsound for IEEE multiplication (§2.3). Rejected.

### 4.5 Samplers (Q6)

* **(a) Add `Dist.uniform`, with law `volume[|Set.Icc (-1) 1]`, the uniform law on $[-1, 1]$, as hdiag's `eighSampleLaw` (recommended).** One `Dist.law`
  case, the instance proof, and the NumPy emitter case. A complex Gaussian is
  $(\xi_1 + i\xi_2)\cdot\mathrm{fl}(\sqrt{1/2})$ from two `gaussian` draws, with no new
  constructor. The **tape-rounding contract** for rounded runs:
  ```lean
  def IsTapeRounding (I : Interp P ι K C) (dec : P → K → ℝ) (p : P) (u : ℝ) (c : Dist → ℝ)
      (ρ : Dist → ℕ → ℝ → K) (ξ : Dist → ℕ → ℝ) : Prop :=
    I.tape = (fun d i => ρ d i (ξ d i)) ∧ ∀ d i x, |dec p (ρ d i x) - x| ≤ c d * u * |x| ∧
      (d = .uniform → x ∈ Set.Icc (-1) 1 → dec p (ρ d i x) ∈ Set.Icc (-1) 1)
  ```
  This is Definitions 1.3 and 1.4 with "there exists a coupling" realised by the ideal tape, as
  on hdiag. The rounding $\rho$ may depend on the tape position $i$ (review item 6). The paper's
  coupling is per sample, and a hardware sampler's rounding depends on its state; no proof uses
  position independence. Also, hdiag's `IsUnifSampler` clause $\lvert\mathrm{dec}\,c\rvert \le
  \mathrm{dec}\,s$ holds for the program's $c = \mathrm{fl}(\mathrm{fl}(R/\ell)\,\hat v)$ only
  with a monotone `fl` that is exact on the grid. `IsCorrectlyRounded` gives that; `IsRelErrSem`
  alone does not. It comes with **the rounded probabilistic model** `MatrixFreeRoundedProb` (§6.3).
  Breakage: `Dist` is in every target's closure (through `St.pos`, `Instr.draw`, `OpKind.draw`),
  so **all nine targets re-pin**, not only `MatrixFreeProbHutchpp` as the first version said
  (review item 7). The net effect is the same, since S1a and S1b are one change. `KrylovSmoke`'s
  exhaustive `Dist` cases need one line each. About 200 to 400 lines.
* **(b) Uniform from $t$ Rademacher draws**, $\sum_i b_i 2^{-i}$, with no change. Honest $O(t)$
  cost, but it needs a dyadic-coupling lemma and an extra size $t$.
* **(c) Also `Dist.complexGaussian`.** The tape is real-valued (`Dist → ℕ → ℝ`), so this would
  need a complex tape. Not needed.

### 4.6 Costs for data-dependent control flow (Q8)

`StaticCost` stays as it is, a sound bound for every successful run under every semantics
(`Prog.bounds_staticCost_of_exec_eq_some`), extended by the `bindIdx` supremum and the `kcall`
step. For EIGH it is loose by more than a factor of $n$ (corrected after review item 7). With
`OpKind.kcall p o dims`, calls of different sizes are different kinds. So the pointwise supremum
over $k \le \mathrm{bound}$ of the singleton records is the indicator over *all* $k$, and the
weighted static bound is about $nD\sum_{k \le n} T(k)$, loose by about $n^2/(\omega + 1)$ for
$T(k) = k^\omega$. The truth is $\sum_i T(k_i) \le T(n)$ per level, for $\sum_i k_i = n$ and $T$
superadditive.
The paper assumes $T_{\mathrm{MM}}$ convex, which with $T(0) = 0$ gives superadditivity. The tight
count is therefore *proved* by the run invariant, as Lanczos's counts are. It is stated as a
weighted bound on the `kcall` records:
`Finsupp.weight (kernelFlops T) cnt ≤ C · D · F · T(n)` for every convex $T$ with $T(0) = 0$.
Alternative (b): annotate `bindIdx` with a partition budget so that `StaticCost` can sum over a
partition. That is new machinery for one use. Not recommended.

### 4.7 Scalar parameters

The program follows the amended hdiag exactly (review item 2; the first version computed
$\delta$ with a bit-length bound for the logarithm, which is dropped).
* **$\beta$ is a declared input** (in `par`): one stored accuracy below the analysis bound, with
  `pre : dec β ≤ bisectionSignTol …` in the target. It is F6 way 2 applied to data: no square
  root or logarithm is computed. The target carries the Q5 flag of F12 (declared inputs computed
  outside the program).
* **The window and tolerance are computed by the machine,** as `eighNextParams`:
  $\mathrm{fl}(\mathrm{fl}(\mathrm{fl}(1/2) + \mathrm{fl}(2/\ell))R)$ and
  $\mathrm{fl}(\mathrm{fl}(1 - \mathrm{fl}(1/\ell))\varepsilon)$. Here $\ell$ and $2$ are
  `M.ofNat` values, so the program writes them with `litIdx` (exact under `IsExactIntLit`).
  Likewise $\mathrm{fl}(1/2)$ is `M.div M.one (M.ofNat 2)`, so the program computes it by the
  same two operations (`lit 1`, `litIdx 2`, `div`), not as `lit (1/2)`.
* **The shift** is `M.unif (M.div R (M.ofNat ℓ)) v`. **The split** is
  $k_+ = \min(k, \lfloor\mathrm{fl}(t + \mathrm{fl}(1/2))\rfloor_+)$, which is the program's
  clamped `bindIdx` exactly under `IsExactToNat`.
* **Sizes and inputs** (M5): the depth counter $\ell_0$ and the sign fuel are sizes (`D`, `F`);
  $R_0$, $\varepsilon$, $\beta$ are declared inputs. The target's `pre` ties them as hdiag's EV
  hypotheses do. New transcendental `UnOp`s are a later change (F6, way 3), not needed.

## 5. Recommendation and staging

| Stage | Content | Language change | Re-pin |
|---|---|---|---|
| S0 | Codex's `feat/rounded-krylov-oracles`: **done**, PR #58, main a08339af | — | none |
| S1a | `kcall`, `Interp.kernel`/`kshape`, `OpKind.kcall`, `ImplementsKernel`, the `subst` case; `KernelContracts.lean` (MM, QR, exact witnesses) | one constructor, two defaulted fields | all targets (closure of `FStmt`) |
| S1b | `Dist.uniform`; `IsTapeRounding`; `MatrixFreeRoundedProb` (target-level definition, maintainer approval Q3 of F12) | one `Dist` constructor | with S1a |
| S1c | complex-pair kernels and their exact and rounded specifications | none | none |
| S1d | **SIGN** and **DEFLATE** as registered programs, refining hdiag's `newtonSchulzSign` and `deflate` (size parameters $F$, $r$) | none | new targets |
| S2a | `bindIdx`, `ScalarSem.toNat`, `IsExactToNat`, `OpKind.toNat`, `StaticCost.supRange` | one constructor, one defaulted field | all targets |
| S2b | **EIGH** as a registered program (§6), its refinement (§7), weighted kernel counts | none | new target |
| later | `fix`, or the worklist theorem, with the second recursive algorithm; `toNat`-based sparse formats; complex oracle model | — | — |

S1a and S1b go in one change, so the registry re-pins once. S2a is a second, separately approved
change. Each stage is useful on its own: S1d gives the first two genuine `Prog`s of [Shah2024].
The language changes (S1a, S1b, S2a) are in `Computation/`, Codex's area. They should be
implemented by Codex or with its review (§8, Q9). The pilot S1d comes before S2: it exercises
kernels, pairs and the rounded probabilistic model, and it calibrates the EIGH estimate.

## 6. EIGH as a program (sketch under the recommendation)

### 6.1 Interface

`eighProg.compiled : Prog P ι 2 4`, with sizes $N = n$ (index 0; there is no oracle, so index 0 is
just $n$), $D$ (depth budget) and $F$ (sign fuel). Declared buffers:
0. `A`, $2n^2$ words, the interleaved Hermitian input;
1. `par`, the stored parameters $R_0$, $\varepsilon$, $\beta$ (hdiag's `eigh M N ℓ A R₀ ε β s`;
   $\beta$ below the analysis bound by `pre`, §4.7);
2. `U`, $2n^2$ words, output;
3. `d`, $n$ words, output.

Kernel names: `mm`, `qr`. Draws: `uniform` (one per node), `gaussian` ($4k^2$ per node of size
$k$: two complex $k \times k$ matrices).

### 6.2 Program (builder pseudocode; every arithmetic step a counted instruction or kernel)

```text
scope:
  -- level arenas; a node at [lo, lo+k) stores its k×k complex matrix contiguously at offset lo·n
  -- (interleaved pairs, so word offset 2·lo·n), as kernels read contiguous blocks (§4.3, M4)
  alloc arenaM[(D+1)·2n²], arenaQ[(D+1)·2n²], arenaU[(D+1)·2n²], eig[(D+1)·n]
  alloc size[(D+1)·n], kind[(D+1)·n], kp[(D+1)·n], lvl[(D+1)·2]   -- per slot; R, ε per level
  alloc work[c·n²]                                                  -- node scratch, packed
  init: copy A into arenaM level 0 at offset 0; size[0][0] ← litIdx n; size[0][j] ← litIdx 0;
        lvl[0] ← (R₀, ε); half ← div(lit 1, litIdx 2)                -- fl(1/2) as hdiag
  loop D fun dd =>                                     -- downward pass; ℓ = (D − 1) + dd, an index
    lvl[dd+1] ← eighNextParams(R, ε, litIdx ℓ)          -- fl(fl(half + fl(2/ℓ))R), fl(fl(1 − fl(1/ℓ))ε)
    loop n fun lo =>
      bindIdx size[dd][lo] (bound n − lo) fun k =>     -- exact read-back by IsExactIntLit, IsExactToNat
        if k = 0 skip                                  -- litIdx k, lit 0, one cmp
        elif k ≤ 1 or R ≤ fl(ε·R₀): leaf → kind ← leaf; eig, arenaU at level dd
        else:
          v ← draw uniform; c ← unif-rounding of fl(R / litIdx ℓ)·v   -- tape contract
          W ← hermShift(block(arenaM, dd, lo, k), c)                 -- diagonal real parts only
          SIGN (hdiag newtonSchulzSign, tolerance from β, scale fl(2R)):
            whileFuel F (test fails) { X ← kcall mm(W, W); W ← hermAvg(kcall mm(W, 3I − X), 2);
                                        test ← every |part of I − kcall mm(W, W)| ≤ η }
          P₊ ← hermScale(hermShift(W, −1), 2); P₋ ← hermScale(−hermShift(W, 1), 2)
          t ← traceRe P₊ (left to right)
          bindIdx fl(t + half) (bound k) fun k₊ =>      -- k₊ = min k ⌊fl(t + fl(1/2))⌋₊
            if k₊ = k or k₊ = 0: one child: hermShift(block, ±fl(R/2)) to level dd+1 at lo,
                                   size[dd+1][lo] ← litIdx k, kind ← shift±
            else: G₊, G₋ ← complex Gaussian k×k (2 gaussian draws per entry, times fl(√(1/2)))
                  Q₊ ← first k₊ cols of (kcall qr(kcall mm(P₊, G₊))).Q ; Q₋ likewise, k − k₊
                  store [Q₊ Q₋] packed in arenaQ level dd at offset lo·n
                  C₊ ← hermShift(hermAvg(kcall mm(kcall mm(Q₊ᴴ, A_blk), Q₊), 2), fl(R/2))
                       → level dd+1 at offset lo·n;   C₋ likewise → offset (lo+k₊)·n
                  size[dd+1][lo] ← litIdx k₊; size[dd+1][lo+k₊] ← litIdx (k − k₊);
                  kind ← split; kp ← litIdx k₊
  loop D fun dd' => let dd := D − 1 − dd'             -- upward pass
    loop n fun lo => bindIdx size[dd][lo] (bound n − lo) fun k =>
      match kind: leaf → done at the downward pass
                  shift± → U block ← U block of level dd+1; eig ← fl(eig' ± fl(R/2))
                  split → bindIdx kp fun k₊ => U block ← [kcall mm(Q₊, U₊) kcall mm(Q₋, U₋)],
                          eig ← [fl(d₊ + fl(R/2)), fl(d₋ − fl(R/2))]
  copy the level-0 U block and eig into U, d
```

Everything that the shallow `eighAux` does as a Lean function is here an operation of the tree:
each size, offset and trip count is a `bindIdx` variable or a loop variable, each scalar a
counted instruction, each product or factorization a counted `kcall`, each random number a draw.
Memory is $O(Dn^2)$ cells, a function of the sizes. The nodes at a level occupy disjoint packed
blocks $[lo\,n, lo\,n + k^2)$, so one arena of $n^2$ complex entries per level holds them all. The
SIGN loop is hdiag's, with one difference: where hdiag returns the untested $F$-th iterate after
the fuel runs out, `whileFuel` fails. The two agree exactly where the fuel suffices (§7.1). Nodes whose budget is spent (level $D$)
get the junk value $(\mathbf{I}, \mathbf{0})$, as in `eighAux`.

### 6.3 The target (shape; approval needed)

```lean
def MatrixFreeRoundedProb {r b : ℕ} (p : P) (prog : Prog P ι r b) (valid) (X) (inputs)
    (Contracts : Interp P ι K (OpCount P ι) → Prop)      -- scalar, literal, toNat, kernel contracts
    (ρOK : (Dist → ℕ → ℝ → K) → Prop)                      -- the tape-rounding contract
    (pre) (good : (N : ℕ) → (n : Fin r → ℕ) → X N n → St P K (OpCount P ι) → Prop)
    (bound : (N : ℕ) → (n : Fin r → ℕ) → X N n → ℝ) : Prop :=
  ∀ N n, valid N n → ∀ x, pre N n x → ∀ (I : Interp P ι K (OpCount P ι)) (ρ : Dist → ℕ → ℝ → K),
    Contracts I → ρOK ρ → ∀ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω)
    (ξ : Ω → Dist → ℕ → ℝ), HasLaw ξ tapeLaw μ →
    μ.real {ω | ¬ ∃ st', prog.exec { I with tape := fun d i => ρ d i (ξ ω d i) } N n
        (inputState p (List.ofFn (inputs N n x))) = some st' ∧ good N n x st'} ≤ bound N n x
```
For EIGH:
* `good`: the decoded `U`, `d` satisfy `IsApproxDiagonalization A U d (2εR₀) (ε/3)`, and the
  counts satisfy the weighted bound of §4.6;
* `bound` is $\theta$;
* `pre` holds hdiag EV6's precision and range hypotheses, `dec β ≤ bisectionSignTol …`, and the
  tie between $\varepsilon$ and $D$;
* `Contracts I` is the conjunction of:
  * `IsCorrectlyRounded fl dec enc I.sem`: every arithmetic result is the encoded `fl` of the
    exact result, in range, for a monotone `fl` with `IsRoundingFn`;
  * `IsExactIntLit dec I.sem n` (M2);
  * `IsExactToNat dec I.sem` (M1);
  * `IsMatMulKernel I mm dec`, `IsQRKernel I qr dec`, lifted from hdiag's `IsMatMulErr`/`IsQRErr`.

**This is strictly stronger than `MatrixFreeRounded`'s relational `IsRelErrSem` (M3).** EIGH's
target therefore covers fewer semantics than Lanczos's (correctly rounded ones: IEEE, `gridSem`,
`binaryFloatSem`), by design: the equality refinement to hdiag's functional `FloatMachine` needs a
function of the exact result. A relational EIGH target would need a relational shallow
specification (Q7(b)).

## 7. Refinement theorem and effort

### 7.1 Shape (restated after review item 4)

The program fails where hdiag returns a junk value: the fuel runs out, or a `toNat` read fails.
So the refinement has two parts, both under the functional contracts of §6.3, the tape
$\rho \circ \xi$ and `hA` (the declared buffers hold $\mathbf{A}$, $R_0$, $\varepsilon$, $\beta$):

**(a) Partial equality.** Every successful run computes hdiag's `eigh`:
```lean
theorem eighProg_exec_eq (hC : Contracts I) (hA : inputs hold A R₀ ε β)
    (h : eighProg.compiled.exec { I with tape := ρ ∘ ξ } n ![D, F] st₀ = some st') :
    decodeU st' = (eigh M F ℓ₀ A R₀ ε β (sampleTree ρ ξ A)).1 ∧
      decodeD st' = (eigh M F ℓ₀ A R₀ ε β (sampleTree ρ ξ A)).2
```
Here `M : FloatMachine` is read off `I` and `ρ` (`ofNat` from `lit`, `toNat` from `sem.toNat`,
`mm`/`qr` from the kernels, `unif`/`normal` from `ρ`). `sampleTree` gives the path-indexed samples
the run actually reads.

**(b) Success on the good event.** On hdiag's good event (every node's sample good), no
`whileFuel` runs out (SN4 at every node, with $F$ from `pre`) and no `toNat` fails. Since hdiag's
`toNat` is total, the only remaining failure modes are fuel and range.

Then hdiag's theorems (EB*, EV*), stated for every machine meeting `FloatMachine.IsAccurate`,
transfer to the program's outputs. Two further lemmas complete the probabilistic target:
* **lazy sampling:** the output under `sampleTree ρ ξ A`, with $\xi \sim$ `tapeLaw`, equals in law
  the output under an i.i.d. tree. Each node's draws are fresh: they come after every draw that
  decided the node's existence and position. Alternatively, apply hdiag's UB1 (adaptive union
  bound with fresh samples) to the tape directly. Nothing in Mathlib is a precedent;
* **the failure bound:** $\mathbb{P}[\text{fail or not good}] \le \theta$ from (a), (b) and EV6.

### 7.2 Effort (an estimate, not a measurement; revised after review item 8)

Calibration, lines on main a08339af:
* Gram–Schmidt program 879 lines;
* Hutch++ 1,295 lines;
* Lanczos about 5,400 lines (`LanczosProgram*.lean` 4,510, plus the shared `BLAS/Normalization*`
  about 890);
* CG 8,181 lines (7,082 before Codex's PR).

Lanczos is one straight loop. Its prefix, state and commit machinery alone took about 1,000
lines. EIGH has:
* two nested loops in two passes, with `bindIdx` frames;
* a `whileFuel` with a $k^2$-entry flag reduction;
* two kernels, and complex pairs;
* a lazy-sampling lemma with no precedent.

| Part | Estimate (lines) | Basis |
|---|---|---|
| S1a kernels, contracts, witnesses, `subst` case | 1,000 – 1,800 | `ImplementsOracle`/`Sim` cases, hdiag C1–C2 |
| S1b uniform, tape contract, rounded probabilistic model | 300 – 600 | `Tape.lean` 200 |
| S1c complex-pair kernels (elementwise, Hermitian part, trace, max-modulus, conjugate transpose) | 2,000 – 3,000 | real BLAS + RoundingErrors about 2,400 |
| S1d pilot: SIGN and DEFLATE programs, refinement, targets | 2,000 – 3,500 | Lanczos step and rounded step; Hutch++ draws |
| S2a `bindIdx`, `toNat`, literal clause, `supRange`, all structural cases | 900 – 1,500 | 25 – 35 cases + `substKind`, `KrylovSmoke` |
| Node step (shift, trace, `bindIdx`, branches, compressions) | 1,200 – 2,000 | CG guards and body |
| Level passes, packed arena frames, `eighNodeAt` invariant, junk leaves | 2,500 – 4,000 | no precedent; the hardest part |
| Lazy sampling and success | 1,000 – 2,000 | UB1 on hdiag |
| Assembly, target, weighted counts | 800 – 1,500 | Lanczos counts and targets |
| **Total** | **about 12,000 – 20,000** | 2 – 4 × Lanczos |

This is a floor rather than a centre. S1d is the calibration pilot: after it lands, the S2 rows
are estimated again from its measured size.

## 8. Coordination

### 8.1 Codex (`feat/rounded-krylov-oracles`, merged as PR #58, main a08339af)

The first version of this note was written against 4d4e9fc9, with Codex's work open as commit
2b070b3c. It is now on main, and this note is rebased on a08339af. The breakage audit of §4 was
re-run there, Codex's files included. Codex's direction:
* real scalar contracts with mixed absolute/relative error (`AbsRelErr`);
* bounded formats (`BinaryFloat`, `binaryFloatSem`, checked and finite `Float`, `FixedPoint`);
* one certificate for "a routine, stored or oracle" (`IsMatvecRoutine`).

It touched neither `Syntax`, `Exec`, `FirstOrder`, `Compile`, `Subst`, `StaticCost` nor the
registry.

| Proposed change | Effect on main (with Codex's files) |
|---|---|
| `kcall`, `bindIdx` constructors | one case in each structural site of §4; programs (Codex's rounded CG/Lanczos proofs included) unfold `exec` on other constructors and are unaffected; all nine targets re-pin |
| `OpKind.kcall`, `OpKind.toNat` | `substKind` and `KrylovSmoke` (`opcode`, `kinds`, `mem_kinds`) get one case each |
| `ScalarSem.toNat` with a default | `failSem` and `binaryFloatSem` (anonymous constructors) get one component each; every `where` construction is unaffected |
| `Interp.kernel`/`kshape` with defaults | none (every construction uses `where` or `storedInterp`) |
| `Dist.uniform` | `KrylovSmoke`'s `Dist` cases; all nine targets re-pin |
| `RunsWithin.subst` | gains `htoNat` and the `kcall` case; callers add `rfl` arguments |
| kernel contracts | new Matrix-layer file, reusing `IsMatvecRoutine`'s shape (actual block write, normwise error, composability) |
| complex-pair rounded kernels | built on Codex's `AbsRelErr` and `VectorErrors`, not on the older relative-only lemmas |

Remaining coordination (Q9 as re-asked):
* **who implements S1a and S2a**: Codex owns `Computation/`;
* **one re-pin or two**: S1 and S2 as separate changes, or one combined change.

### 8.2 The hdiag branch (`design/hdiag` f5bef8ca; read, not edited)

What the equality refinement needs from the shallow specification is **already done on hdiag**:
* `FloatMachine` with `toNat_eq : M.toNat x = ⌊dec x⌋₊` (total, $0$ below zero);
* machine-computed `eighNextParams`;
* $\beta$ as a stored input (no square root, no logarithm);
* one rounding per operation (`hermShift`, `hermScale`, `hermAvg`, `traceRe` left to right);
* $k_+ = \min(k, \lfloor\mathrm{fl}(t + \mathrm{fl}(1/2))\rfloor_+)$;
* complex numbers as pairs `F × F` decoded by `decodeComplex`, matching Q5(a).

What remains, all on the program side or as notes:
1. hdiag's $\mathrm{fl}(1/2)$ is `M.div M.one (M.ofNat 2)`, so the program computes it by those
   two operations, not `lit (1/2)`.
2. `toNat` on negatives: the program's `IsExactToNat` takes hdiag's total floor (M1), not `none`.
3. hdiag's `M.ofNat` is a rounded conversion. The program's `litIdx` is exact under
   `IsExactIntLit`, so the program's machine has `ofNat k = k` for $k \le n$. That is a
   special case hdiag's contract allows.
4. hdiag's SIGN loop returns the untested $F$-th iterate where `whileFuel F` fails. They agree
   where the fuel suffices, which is part (b) of §7.1.
5. hdiag's `IsMatMulErr`/`IsQRErr` are the contracts `KernelContracts.lean` lifts. Its sample tree
   `List Bool → EighSample` stays, and the program's `sampleTree` is mapped onto it (§7.1).

### 8.3 The target registry

S1 and S2 each change `FStmt`/`exec`, and S1 also changes `Dist`. So each changes the closure
hash of all nine registered targets, with the trees unchanged. `docs/targets.toml` is rewritten
by `TARGETS_UPDATE=1 lake env lean scripts/Targets.lean`, and the maintainer approves the diff
(Q3 of F12). Agents do not edit the registry.

## 9. Open questions (recommendations in bold; the decision sheet has Q1–Q9 and M1–M5)

1. **OQ1 `bindIdx` out of range: clamp (recommended) or fail?** Clamping matches hdiag's `min`.
   Failing makes a wrong size visible as a run failure, but turns an accuracy lemma into a
   success obligation. **Clamp.**
2. **OQ2 Interleaved or split complex layout?** **Interleaved** (BLAS/LAPACK/NumPy). Split
   planes make a complex oracle a real one on each plane, which is simpler for matrix-free
   targets later.
3. **OQ3 `OpKind.kcall` with a dimension list, or one kind per (kernel, shape class)?** **The
   list**: exact call records; flops by `Finsupp.weight`.
4. **OQ4 Complex matrix-free model** (oracle as realification, precondition on $\mathbf{A}$):
   **defer** until a complex Krylov target.
5. **OQ5 Should `MatrixFreeRoundedProb` carry counts?** **No**: counts come from the
   semantics-independent `StaticCost`/invariant theorem, a second clause of the target, so the
   charge can stay arbitrary as in `MatrixFreeRounded`.
6. **OQ6 Exact halving as a contract clause** (`HalvesExactly dec sem`, like `AddsZeroExactly`)
   for the paper's $\mathrm{fl}(x/2) = \mathrm{fl}(x)/2$, its only exact-halving assumption.
   hdiag no longer uses it (division by `ofNat 2` is rounded). **Add only if a later algorithm
   needs it**, with Codex's bounded formats stating its range condition.
7. **OQ7 $R_0$**: **a declared input with precondition $\lVert\mathbf{A}\rVert_2 \le R_0$, as hdiag
   has it (M5)**. Computing a rounded Frobenius norm in the program is a later option: counted,
   $O(n^2)$, the paper's remark.
8. **OQ8 `iteIdx`**, an uncounted conditional on index expressions (G11-style control on
   indices): **not now**. Cell comparisons under `IsExactIntLit` suffice (§2.3).

## 10. Material

* [Shah2024] arXiv 2408.09880, LaTeX source: §1.2, Definitions 1.1 to 1.4, Algorithms 1 to 3,
  Remark on $b$.
* `docs/design/Computation.md`: D1, D3, D4, D11 to D19, F1 to F12, Guarantees G1 to G35.
* `docs/design/{Computation-Static-Cost,Lanczos-Rounded-Program-Bridge,CG-Rounded-Program-Bridge,Krylov-Implementation-Bridge}.md`.
* hdiag: `docs/design/Eigensolvers-HermitianDiagonalization.md` (decisions 1 to 3, §2, §10 to
  §12) and `NLAlib/Matrix/Computation/{SpectralBisection,NewtonSchulzSign,Deflation,Primitives,EntrywiseRounding}.lean`.
* Fable's review `~/nlalib-harness/reports/Review-Fable-COMPDYN-Design.md` (items 1 to 11,
  M1 to M5), applied in this revision.
* hdiag f5bef8ca: `FloatMachine`, `FloatMachine.IsAccurate`, `eighNextParams`, `eighStep`,
  `hermShift`/`hermScale`/`hermAvg`/`traceRe`.
* Codex: commit 2b070b3c (PR #58, on main a08339af), `docs/design/Finite-Precision-Arithmetic.md`, `MatvecRoutine.lean`,
  `Underflow.lean`, `BinaryFloatSem.lean`, the `Contract.lean` and `Allocation.lean` diffs.
* [Higham2002] Lemma 3.5 (complex multiplication), Theorem 19.4 (Householder QR).
* Mathlib reused: `Nat.floor` (`⌊·⌋₊`) for `toNat`, `ProbabilityTheory.cond` (`volume[|Set.Icc (-1) 1]`),
  `Finsupp.weight`. Searched for a lazy-sampling or adaptive-tape lemma: none in Mathlib; hdiag's
  UB1 is the nearest.
* Scratch experiment (§2.2) run with `lake env lean` against a main build. The file was removed
  and not committed.
