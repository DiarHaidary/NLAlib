# Design note: complex-pair kernels, and SIGN and DEFLATE as programs (stage COMPDYN S1c/S1d, pilot)

Status (2026-11-08): all statements proved, sorry-free, and in `NLAlib/`; the two trees and targets
are in the registry, pending the maintainer's re-pin (§11). Design text, 2026-11-06: Branch
`design/compdyn-s1cd` (worktree
`~/nlalib-design-compdyn-s1cd`), from `cleanup/compdyn-s1` fa5b1bc1 (S1 merge-ready; main
a08339af). Parent note: `docs/design/Computation-DynamicPrograms.md` (approved, sheet
`COMPDYN.json`): §4.4 complex pairs, §6 EIGH, §7.1 refinement shape, §7.2 effort, §8.2 hdiag.
Shallow specifications: `design/hdiag` 1db0c258 (read only). Skeleton: 65 statements, in
`NLAlibScaffold/` during the stage and now in `NLAlib/` (§9, §11) (targets `~/nlalib-harness/pilot/compdyn-s1cd-targets.json`) and 3 more blocked
on HDIAG (§5). Decision sheet: `~/nlalib-harness/state/decisions/COMPDYN-S1cd.json` (D1 to D7).

The maintainer's goal: algorithms run inside the model of computation, without cheating, as
examples for later code; this pilot puts the first two algorithms of [Shah2024] into the model and
calibrates the S1 to S2b estimate (§7.2 of the parent note) before S2 (`bindIdx`, then EIGH).

## 0. Summary

| | |
|---|---|
| What runs in the model | `NLAlib.newtonSchulzSignProg` ([Shah2024, Algorithm 1]) and `NLAlib.deflateProg` (Algorithm 2), builders compiled by `rfl` into the trees `….compiled : Prog P ι 1 3` and `Prog P ι 1 2`. Every data operation is an instruction (`lit`, `litIdx`, `bin`, `un`, `copy`, `draw`), a counted comparison (`ite`, `whileFuel`) or a `kcall` of the black boxes `mm`, `qr`; complex numbers are interleaved real pairs; no Lean function of data is in a tree (F2, I1 to I7). |
| S1c | 14 complex kernels over real instructions in `NLAlib/Computation/BLAS.lean` (§2). Each has a **rounded specification**: a successful run writes exactly the result of the matching operation of the `FloatMachine` of the semantics, one rounding per real operation; and an **exact specification**: on exact real arithmetic that machine operation decodes to the exact complex operation. |
| The bridge | `ScalarSem.toFloatMachine sem p toNat mm qr unif normal`: the hdiag machine whose scalar operations are the semantics' operations at tag `p` and whose black boxes are the kernel contracts' routines (§2.2). Under the standard model with every value in range and an exact literal $1$ it meets `FloatMachine.IsAccurate` (IM1). |
| Refinement (S1d) | Two parts, as §7.1 of the parent note. **(a) Partial equality**: under *any* interpretation whose kernels are routines on pairs (`IsMatMulKernel`, `IsQRKernel`) and whose semantics decides flags, every successful run ends with the output block holding *exactly* `newtonSchulzSign M ε b F A` (resp. `deflate M r P G`) on the machine of the same semantics, routines and tape. **(b) Success**: under the standard model, SIGN succeeds when the machine's test passes within the step limit, DEFLATE always. **Counts**: static bounds `newtonSchulzSignCount`, `deflateCount`. |
| Transfer | The proposed targets `MatrixFreeRoundedProbNewtonSchulzSign` and `MatrixFreeRoundedProbDeflate` (in `NLAlib/RandomMatrix/Computation/`) are hdiag's Theorem 2.6 and Theorem 3.3 for the registered trees, in the rounded probabilistic model; their proofs cite hdiag theorems not on this branch and are in a separate scaffold file (§5). |
| Registration | The maintainer adds one line to `scripts/Targets.lean` (§6) and registers the two trees and targets; until then `scripts/Programs.lean` (E4) reports the two `…Prog`s. No re-pin of an existing target. |
| Effort | Definitions and programs about 720 new lines (plus 576 brought from hdiag); statements 1,690 scaffold lines; proofs estimated 3,400 to 4,500 lines; S1c + S1d total about 5,300 to 6,400, in the upper half of §7.2's 4,000 to 6,500 for these rows (§8). |

## 1. Files

| File | Content | Lines |
|---|---|---|
| `NLAlib/Computation/BLAS.lean` (amended) | complex kernels on interleaved pairs, §2.1 | +172 |
| `NLAlib/Matrix/Computation/KernelContracts.lean` (amended) | `EntryLayout.Holds`; `MatMulMap`, `QRMap`, `IsMatMulErr`, `IsQRErr` now hdiag's (deduplicated, §2.3) | 381 → 333 |
| `NLAlib/Matrix/Computation/InterpMachine.lean` (new) | `ScalarSem.toFloatMachine`, `ScalarSem.DecidesFlags`, `ScalarSem.sqrtHalf`, `ScalarSem.tapeNormal`, `ScalarSem.gaussianNormal`, `tapeComplexMatrix`, `tapeIndexMatrix` | 118 |
| `NLAlib/Matrix/Computation/NewtonSchulzSignProgramTree.lean` (new) | `newtonSchulzTestBlock`, `newtonSchulzStepBlock`, `newtonSchulzSignProg`, `.compiled`, `newtonSchulzSignCount` | 128 |
| `NLAlib/Matrix/Computation/DeflationProgramTree.lean` (new) | `deflateProg`, `.compiled`, `deflateCount` | 89 |
| `NLAlib/RandomMatrix/Computation/NewtonSchulzSignTargets.lean` (new, proposed) | `MatrixFreeRoundedProbNewtonSchulzSign` | 91 |
| `NLAlib/RandomMatrix/Computation/DeflationTargets.lean` (new, proposed) | `DeflationData`, `MatrixFreeRoundedProbDeflate` | 116 |
| from `design/hdiag` (unchanged, sorry-free) | `Matrix/Computation/{Primitives,EntrywiseRounding,NewtonSchulzSign,Deflation}.lean`, `Polynomial/Approximation/NewtonSchulz.lean`, `RandomMatrix/Gaussian/Complex.lean`; the five bibliography entries their docstrings cite | 576 |
| `NLAlibTools/NumPy.lean` (amended) | kernel names in emitted calls (N3), DEFLATE emitted with `mm`/`qr` | +17 |
| `NLAlibScaffold/` (new), `NLAlibScaffold.lean`, `lakefile.toml` scaffold entry | the skeleton, §9 (removed at the COMPDYN S2 clean-up, 6b757e18; the statements are in the `NLAlib/` files of §11) | 1,697 |

Not brought from hdiag: its `NLAlibScaffold/`, `SpectralBisection.lean` (EIGH, S2b) and the W4 files.

## 2. S1c: complex pairs

### 2.1 Layout and kernels

Entry $(i, j)$ of an $m \times n$ complex matrix at a buffer offset $o$: real part at
$o + 2(i + mj)$ (`zidx`), imaginary part at the next word; packed, column-major, as BLAS, LAPACK,
NumPy `complex128` and the kernel layout `pairLayout` (M4). The kernels are `named` (E8 allows
`Stmt.named` only in `Computation/BLAS.lean`), have no allocation, and are written so that each
real operation is the machine operation hdiag's definition applies:

| Kernel | Machine operation | Notes |
|---|---|---|
| `zcopy`, `zzero`, `zidentity` | copy, `zeroMat`, `identityMat` | literals $0$, $1$ are `M.zero`, `M.one` |
| `zneg` | `negMat` | in place allowed |
| `zadd`, `zsub`, `zscal` | entrywise `M.add`, `M.sub`, `M.mul a` on both parts | for later stages |
| `zconjTranspose` | `conjTransposeMat` | for $\mathbf{Q}^{\mathsf{H}}$ in EIGH (deviation 3 of S1) |
| `zmirror` | the lower triangle of `hermFrom` | copy and exact negation of the stored upper entry |
| `zhermShift`, `zhermScale`, `zhermAvg` | `hermShift`, `hermScale`, `hermAvg` | upper triangle, diagonal, literal $0$, mirror; out of place |
| `ztraceRe` | `traceRe` | left fold from the literal $0$ |
| `zboxTest` | the test of `newtonSchulzTest` | flag $0$ (pass) or $1$; two comparisons per word |

"Pair patterns" are the four storage lemmas PP1 to PP5 (holding a matrix is reading its packed
storage; one read per part; a block write holds; an input buffer holds) and the two kernel-call
lemmas PP6, PP7 (a kernel call on held matrices holds the routine's output).

### 2.2 The machine of a semantics

`ScalarSem.toFloatMachine sem p toNat mm qr unif normal : FloatMachine K Su Sg` reads every scalar
operation off `sem` at tag `p` (`zero := (sem.lit p 0).getD default`, `ofNat k := (sem.lit p k)
.getD default`, `add x y := (sem.bin p .add x y).getD default`, …, `le x y := (sem.cmp p .le x y)
.getD false`) and takes the black boxes as arguments. A failed operation gives `default`, but a
successful run performs only successful operations, so on it the machine and the program agree
operation by operation. This is why the refinement is an **equality with no contract at all on
the semantics** (part (a)): any `ScalarSem` is already a function of the stored operands, which is
what a `FloatMachine` is. The parent note's M3 ("EIGH needs a correctly rounded `fl`") is
therefore not needed for SIGN and DEFLATE; it remains for EIGH's uniform-sampler clause
$\lvert\mathrm{dec}\,c\rvert \le \mathrm{dec}\,s$ (§4.5 there).

The machine contract (IM1, `isAccurate_toFloatMachine`): if `sem` meets `IsRelErrSem` at $u \ge 0$
with every value in range and its literal $1$ is exact, and the black boxes meet their contracts
at floor $0$, range $\Omega$, the machine meets `FloatMachine.IsAccurate dec u 0 Ω μM μQ cN` with
`toNat` the floor. Every value in range is the setting of the rounded Lanczos and CG programs
(`Lanczos-Rounded-Program-Bridge.md`) and of `gridSem` and `exactSem`; bounded formats
(`binaryFloatSem`, floor $\tau > 0$) are later (D2).

### 2.3 Deduplication with hdiag

S1 copied hdiag's `MatMulMap`, `QRMap`, `IsMatMulErr`, `IsQRErr` into
`NLAlib.Computation` (`KernelContracts.lean`). With hdiag's `Primitives.lean` on the branch the
copies would be two definitions of one concept, so `KernelContracts.lean` now imports
`Primitives.lean` and uses `NLAlib.MatMulMap` etc.; the S1 results `isMatMulErr_exactMM`,
`isQRErr_exactQR` and the kernel contracts elaborate unchanged up to the namespace of these four
names. No registered target reaches them, so no hash moves. The `integrate/hdiag` merge must take
this side (D6).

## 3. S1d: SIGN

### 3.1 The program

`newtonSchulzSignProg p mm n F A ao par po X xo` (declared buffers of the tree: $\mathbf{A}$,
$(\varepsilon, b)$, output): five scratch cells and two $n \times n$ scratch matrices `W`, `V`
in a `scope`;
1. $\eta \leftarrow \mathrm{fl}(\varepsilon/\mathrm{fl}(4n))$ (`litIdx (4n)`, `div`), $-\eta$, the
   stored one; $\mathbf{X} \leftarrow$ `hermScale A b`;
2. the test block: $\mathbf{W} \leftarrow \mathrm{mm}(\mathbf{X}, \mathbf{X})$ (`kcall`),
   $\mathbf{V} \leftarrow$ `hermShift W one`, flag $\leftarrow$ `zboxTest V (−η) η`;
3. `whileFuel (F + 1)` on "flag = one" of the step block ($\mathbf{V} \leftarrow$
   `negMat (hermShift W (ofNat 3))`, $\mathbf{W} \leftarrow \mathrm{mm}(\mathbf{X}, \mathbf{V})$,
   $\mathbf{X} \leftarrow$ `hermAvg W (ofNat 4)`) followed by the test block.

Choices, each kept exact:
* **Fuel $F + 1$ for the step limit $F$.** hdiag's `newtonSchulzLoop F` tests the iterates
  $0, \ldots, F - 1$ and returns the untested $F$-th; `whileFuel (F + 1)` tests $0, \ldots, F$ and
  fails if all fail. On success both return the first passing iterate, or the $F$-th, so (a) is an
  equality with hdiag's `newtonSchulzSign … F` (no off-by-one), and (b) needs a pass at some
  $k \le F$.
* **The product of the test is reused by the step.** hdiag computes `M.mm A A` in the test and
  again in the step; the kernel is a function (`IsMatMulKernel`), so one call gives the same
  value: two kernel calls per step, as [Shah2024, Algorithm 1] counts.
* **The flag is data.** The test result lives in a cell as the literal $0$ or $1$ and the loop
  compares it with the stored one by `.eq`; this needs `ScalarSem.DecidesFlags` (the equality
  test separates the two literals), which holds under the standard model with an exact $1$ (IM2).
* **Stored inputs, computed constants (M5).** $\varepsilon$ and $b$ are declared inputs; $4n$,
  $3$, $4$, $1$ are computed as the machine computes them (`litIdx`, so `M.ofNat`). SIGN has no
  $\beta$ or $\ell$ of its own: inside EIGH it is called with $\varepsilon = \beta$ and
  $b = \mathrm{fl}(2R)$ (hdiag `eighStep`), and $\ell$ only enters EIGH's shift.

### 3.2 Statements (SG1 to SG11)

* (a) SG6 `holds_of_exec_newtonSchulzSignProg`: from any state (inputs at any offsets, output block
  disjoint and in an existing buffer at tag `p` of at least $2n^2$ cells, `hX` as in SG7), a
  successful run ends with the output block holding
  `newtonSchulzSign (I.sem.toFloatMachine p toNat mmR qrR unif normal) ε b F A₀`, for every choice
  of the unused black boxes, and every other cell unchanged. Hypotheses: `IsMatMulKernel I mm
  pairLayout mmR` and `DecidesFlags`. The builder-level form is what EIGH will call. (Statement fix after the pilot: without
  `hX` the output block may be one of the scratch buffers, which the `scope` pops, so a successful
  run leaves it unreadable; the same holds for DF2 and `hQ`.)
* (b) SG7 `exists_exec_newtonSchulzSignProg`: under `IsRelErrSem` (every value in range),
  $u(p) < 1$, an exact $1$, $n \ge 1$, $\bar b \ne 0$, and a passing test at an iterate $k \le F$.
* Steps: the test block SG1/SG2, the step block SG3/SG4, the loop SG5 (induction on the fuel with
  the unrolled `whileFuel`, LP2/LP3); the registered tree SG8 to SG10; counts SG11: at most
  `newtonSchulzSignCount p mm N F` $= (F + 2)\cdot$(two `mm` calls at $[N, N, N]$ and
  $4N^2 + 4N + 4$ of each scalar kind used), peak memory $+4N^2 + 5$ cells.

### 3.3 The target

`MatrixFreeRoundedProbNewtonSchulzSign` concludes `MatrixFreeRoundedProb` with failure bound $0$
(the program draws nothing): for every interpretation meeting `IsRelErrSem` with every value in
range, an exact $1$, an `mm` kernel meeting `IsMatMulErr` at floor $0$, range $\Omega$, constant
$\mu$, on a carrier admitting an accurate machine $M_0$ (D3), and under hdiag's Theorem 2.6
hypotheses with $N_0 + 1 \le F$, almost surely the run succeeds and its output is within
$\bar\varepsilon$ of $\operatorname{sign}(\mathbf{A})$.

## 4. S1d: DEFLATE

### 4.1 The program

`deflateProg p mm qr n r Pm po Q qo`: two scalar cells and four $n \times n$ scratch matrices;
$s \leftarrow \mathrm{fl}(\sqrt{\mathrm{fl}(1/2)})$ (`lit 1`, `litIdx 2`, `div`, `sqrt`); for each of
the $2n^2$ words a Gaussian draw times $s$; $\mathbf{Y} \leftarrow \mathrm{mm}(\mathbf{P},
\widetilde{\mathbf{G}})$, $(\mathbf{Q}_f, \mathbf{R}_f) \leftarrow \mathrm{qr}(\mathbf{Y})$ (two
`kcall`s); copy the first $\min(r, n) = r - (r - n)$ columns of $\mathbf{Q}_f$ and write $r - n$
zero columns (hdiag's junk value for $r > n$), so (a) holds for every $r$.

### 4.2 Samples: positions now, ideal Gaussians in the transfer

hdiag's `deflate M r P G` takes an abstract sample matrix `G : Matrix _ _ Sg` and the sampler
`M.normal : Sg → F × F`. The equality (a) is stated with **`Sg = ℕ` the sample positions**
(`tapeIndexMatrix n`, entry $i + nj$) and the sampler `ScalarSem.tapeNormal` reading the
interpretation's stored tape from the run's position: it holds for every tape, rounded or not.
The transfer needs hdiag's machine with `Sg = ℂ`; for a rounding $\rho$ that does not depend on
the position, `deflate_tapeNormal_eq_deflate_gaussianNormal` (DF4) rewrites the same output as
`deflate` with the sampler `ScalarSem.gaussianNormal` of $\rho$ on the ideal sample
`tapeComplexMatrix ξ n`, entry $(\xi_{2k} + i\xi_{2k+1})/\sqrt2$, whose law is
`complexGaussianMatrix` (CT1), and IM3 gives `IsNormalSampler` with $c_{\mathrm N} = 2(c + 3)$.
Position independence is a hypothesis of the target (D7): `IsTapeRounding` allows dependence
(S1 deviation), hdiag's sampler does not.

### 4.3 Statements (DF1 to DF8) and target

(a) DF2 from any state, the output block in an existing buffer at tag `p` (`hQ` as in DF3);
(b) DF3: always succeeds under `IsRelErrSem` (every value in range),
$u(p) \le 1$ and exact literals up to $2$; DF1 the draw loop; DF5 to DF7 the tree; DF8 the counts
`deflateCount` (exact formula, $2n^2$ draws and products, one call of each kernel, $2n\min(r, n)$
copies) and peak $+8N^2 + 2$. The target `MatrixFreeRoundedProbDeflate`: under the contracts
(including `IsQRKernel` with `IsQRErr`) and the tape-rounding contract at range $2\Omega$, position
independent, and hdiag's Theorem 3.3 hypotheses with $\tau = 0$ and $c_{\mathrm N} = 2(c + 3)$, the
probability that the run fails or returns no $\mathbf{Q}$ with $\|\mathbf{U}\mathbf{W} -
\bar{\mathbf{Q}}\|_2 \le 6\bar m\beta$ for a unitary $\mathbf{W}$ is at most
$2e^{-t^2/2} + r^2x^2$, hdiag's bound unchanged (the run never fails).

## 5. Dependencies on HDIAG (separate scaffold file)

`NLAlibScaffold/RandomMatrix/Computation/SignDeflateTargets.lean` (now
`NLAlib/Eigensolvers/SignDeflatePrograms.lean`, §11) holds the two target proofs
TR2 and TR3, which use hdiag's Theorem 2.6 and Theorem 3.3. TR1, that the shallow test passes
within $N_0 + 1$ steps (shown in step (2) of the proof of Theorem 2.6 but not stated there; the
program's success needs it), is now an HDIAG lemma:
`NLAlib.FloatMachine.IsArithAccurate.exists_le_newtonSchulzTest_iterate` in
`NLAlib/Matrix/Computation/NewtonSchulzSign.lean` (cleanup/hdiag, with the chain helpers of the
Theorem 2.6 proof made public). TR2 and TR3 are proved; both use only the standard axioms.

Two further consequences for hdiag (D3, D7):
* hdiag's SIGN theorem asks for the full `FloatMachine.IsAccurate`, QR and samplers included,
  though it uses only the scalar operations and `mm`. The SIGN target therefore assumes that the
  carrier admits *some* accurate machine $M_0$ (satisfiable: hdiag's
  `exists_floatMachine_isAccurate` over $\mathbb{R}$) and borrows its QR and samplers. Splitting
  `IsAccurate` into a scalar-and-`mm` part on hdiag would remove that hypothesis from SIGN (and
  the uniform sampler from DEFLATE).
* hdiag's `deflate` uses one sampler for every entry; the program's rounding may depend on the
  tape position.
* hdiag's witness `exists_floatMachine_isAccurate` is stated at $u = 0$, so on its own it makes the
  $M_0$ hypothesis non-vacuous only there. This branch adds the monotonicity
  `FloatMachine.IsAccurate.mono` (IM4, S), which with that witness covers every $u \ge 0$;
  follow-up for HDIAG: restate the witness for $u \ge 0$ directly.
* **TR1 is an HDIAG lemma** (`exists_le_newtonSchulzTest_iterate`, proved on `cleanup/hdiag`
  next to Theorem 2.6); COMPDYN does not dispatch it.

## 6. Registration

What the maintainer does (AGENTS rules 1 and 2; board T099):
1. In `scripts/Targets.lean`, `def models`, add the rounded probabilistic model, so that the list
   reads
   ```lean
     [``NLAlib.Computation.MatrixFree, ``NLAlib.Computation.StoredEntries,
      ``NLAlib.Computation.MatrixFreeProb, ``NLAlib.Computation.MatrixFreeRoundedProb]
   ```
   (the one added element: `` ``NLAlib.Computation.MatrixFreeRoundedProb``; Fable's N4 suggests a
   shape check of its `Contracts` argument at the same time).
2. Register the trees `NLAlib.newtonSchulzSignProg.compiled`, `NLAlib.deflateProg.compiled` and
   the targets `NLAlib.MatrixFreeRoundedProbNewtonSchulzSign`
   (`NLAlib/RandomMatrix/Computation/NewtonSchulzSignTargets.lean`) and
   `NLAlib.MatrixFreeRoundedProbDeflate` (`…/DeflationTargets.lean`) in `docs/targets.toml` by
   `TARGETS_UPDATE=1 lake env lean scripts/Targets.lean` once the target proofs exist (E3 requires
   exactly one proof), then approve with `sha256sum docs/targets.toml > docs/targets.approved`.

No existing target re-pins: the new kernels and definitions are additive, and the
`KernelContracts.lean` deduplication is in no target's closure. The scaffold library entry moves
the registry's `lakefile_sha256` pin (Targets lint item 4) while the skeleton exists, as in S1;
the clean-up removes it. Until registration, `scripts/Programs.lean` reports E4 for the two
`…Prog`s and the Targets lint item 1 has nothing to check for them; both are expected.

## 7. S1 follow-ups

* **N3 (done).** `NLAlibTools/NumPy.lean`: `emitF` and `emitProg` take a kernel-name function
  (`emitProg` defaults to `kernel`); `NLAlibTools.deflatePython` emits DEFLATE with `mm` and `qr`,
  checked by `#guard`.
* **N2 (deferred, not in scope).** Neither program calls an oracle, so neither goes through
  `ProgFamily.substOracle`; changing `Stmt.substOracle` would touch `RunsWithin.substOracle`, its two
  callers and the Hutch++ tree definitions for no use here. It is needed when a `kcall` program
  with oracles is substituted (a complex matrix-free target, OQ4).
* **N5** (kernels do not see the tag): unchanged, one tag here.
* The NumPy prelude has no complex kernels yet: emit with `inline = true` (as `deflatePython`).

## 8. Effort and calibration (§7.2 of the parent note)

| Part | §7.2 estimate | Pilot: definitions and programs | Pilot: statements | Pilot: proofs (outlines; realistic) |
|---|---|---|---|---|
| S1c kernels, machine, pair patterns | 2,000 – 3,000 | 172 (kernels) + 118 (machine) + 9 (`Holds`) | 849 (PP, IM, PK, LP) | 1,245; 1,900 – 2,500 |
| S1d SIGN, DEFLATE, targets | 2,000 – 3,500 | 217 (programs) + 207 (targets) | 647 (SG, DF, CT) + 123 (TR) | 836 + 190 (TR); 1,500 – 2,000 |
| **S1c + S1d** | **4,000 – 6,500** | **about 720** | **about 1,620** (scaffold, docstrings included) | **2,270 outlined; 3,400 – 4,500** |

Statements move into `NLAlib/` with their docstrings minus the `Proof:` lines (rule D8 of
`docs/rules/DIGEST.md`: no `Proof:` sentence in a library docstring), about 1,200
lines; so the stage lands at about 720 + 1,200 + 3,400 to 4,500 = **5,300 to 6,400 lines**, plus
576 lines of hdiag definitions that count to HDIAG. The realistic proof range is the outline sum
times 1.5 to 2, the ratio of the Lanczos and CG bridges' final size to their plans.

Findings for S2:
* **S1c is at the top of its row** (about 2,800 to 3,400 lines with statements, against 2,000
  to 3,000), but a third of it is the bridge that §7.2 did not list (the machine of a semantics
  and its contract IM, the loop lemmas LP, the pair patterns PP); the kernels alone (PK, about
  1,700 to 2,100) are below the row. The equality refinement makes every kernel specification
  *functional* (the run writes the machine's value) and keeps the rounding-error analysis on
  hdiag's shallow side, proved once; the §7.2 basis "real BLAS + RoundingErrors about 2,400"
  priced an error analysis the program side no longer does.
* **S1d is in the middle of its row** (about 2,500 to 3,000 with statements, against 2,000 to
  3,500), SIGN's `whileFuel` with two kernels and a $k^2$ flag reduction about 500 outlined
  lines (SG). The node step of EIGH (§7.2 row "Node step", 1,200 to 2,000) is
  about two SIGN-sized blocks plus the `bindIdx` cases: the row stands.
* **No evidence yet on the level passes** (2,500 to 4,000, the hardest row) or lazy sampling
  (1,000 to 2,000): nothing in S1 exercises data-dependent offsets. DEFLATE's position-indexed
  sample (§4.2) is the first instance of the lazy-sampling pattern and was cheap (DF4, CT1) because
  the positions are static; at EIGH they depend on the data.
* S1a and S1b landed at about 1,200 lines in `NLAlib/` (a08339af..fa5b1bc1; estimate 1,300 to
  2,400). With this stage, S1 is about 6,500 to 7,600 lines against §7.2's 5,300 to 8,900: the
  lower half. Total 12,000 to 20,000 for S1 to S2b: keep, with the S2 rows unchanged (they carry
  the risk); re-estimate after S2a.

## 9. Skeleton

65 statements in 7 files (S 28, M 37, no L; waves 0 to 6), in
`~/nlalib-harness/pilot/compdyn-s1cd-targets.json`, plus TR2, TR3 (M) in
`SignDeflateTargets.lean` (proved; TR1 moved to HDIAG). Note ids: LP (loops, `Computation/Exec.lean`, to a new
`Computation/Loops.lean` since `Exec.lean` is at F10), PP (pair patterns, `KernelContracts.lean`),
IM (machine, `InterpMachine.lean`), PK (kernels, new `Matrix/Computation/PairKernels.lean`), SG
(new `NewtonSchulzSignProgram.lean`), DF (new `DeflationProgram.lean`), CT (new
`RandomMatrix/Computation/ComplexTape.lean`).

| ids | statements | difficulty |
|---|---|---|
| LP1–LP3 | `forall_of_exec_loop_eq_some`, `exec_whileFuel_of_eval_eq_zero`, `exec_whileFuel_of_eval_eq_succ` | S, S, M |
| PP1–PP7 | `EntryLayout.holds_iff_readBlock_eq_some`, `pairLayout.holds_iff`, `EntryLayout.holds_of_writeBlock_eq_some`, `EntryLayout.holds_inputState`, `EntryLayout.Holds.of_forall_read_eq`, `IsMatMulKernel.holds_of_kcallStore_eq_some`, `IsQRKernel.holds_of_kcallStore_eq_some` | M, S, M, S, S, M, M |
| IM1–IM3 | `isAccurate_toFloatMachine`, `IsRelErrSem.decidesFlags`, `isNormalSampler_gaussianNormal` | M, S, M |
| IM4 | `FloatMachine.IsAccurate.mono` | S |
| IM5–IM13 | exact specifications: `decodeMatrix_{hermShift,hermScale,hermAvg,conjTransposeMat}_toFloatMachine_exactSem`, `traceRe_toFloatMachine_exactSem`, `all_finRange_toFloatMachine_exactSem_iff`, `decodeMatrix_{add,sub,mul}Parts_toFloatMachine_exactSem` | S each |
| PK1–PK16 | value and success of `zcopy`, `zzero`, `zneg`, `zmirror`, `zhermShift`, `zhermScale`, `zhermAvg`, `zboxTest` | M/S pairs |
| PK17–PK22 | values of `zidentity`, `zadd`, `zsub`, `zscal`, `zconjTranspose`, `ztraceRe` | M each |
| SG1–SG11 | test block, step block (value, success), loop, (a), (b), tree (`toStmt_compiled`, value, success), counts | M ×7, S ×3, M |
| DF1–DF8 | draw loop, (a), (b), sampler rewrite, tree ×3, counts | M, M, M, S, S, S, S, M |
| CT1 | `hasLaw_tapeComplexMatrix_of_hasLaw_tapeLaw` | M |
| TR1–TR3 (proved) | `FloatMachine.IsArithAccurate.exists_le_newtonSchulzTest_iterate` (HDIAG), `matrixFreeRoundedProbNewtonSchulzSign`, `matrixFreeRoundedProbDeflate` | L, M, M |

## 10. Deviations from the brief

1. Program names `newtonSchulzSignProg` and `deflateProg` (`<spec>Prog` of hdiag's
   `newtonSchulzSign`, `deflate`; E4), for the brief's `signProg`, `deflateProg`.
2. The targets live in `NLAlib/RandomMatrix/Computation/` (layer 2, where `MatrixFreeRoundedProb`
   is), the programs in `NLAlib/Matrix/Computation/` (layer 0); hdiag's planned `Eigensolvers/`
   folder is not in the layer table `check_rules.py` holds (D1).
3. The functional contract is the standard model with every value in range, not a correctly
   rounded `fl` (§2.2; D2).
4. N2 deferred (§7).

## 11. End-of-stage status (2026-11-08, `cleanup/compdyn-s2`)

**Proved.** The 65 statements of §9 were proved on `integrate/compdyn-s1cd` and merged into
`design/compdyn-s2` (979305f4); TR2 and TR3 (`matrixFreeRoundedProbNewtonSchulzSign`,
`matrixFreeRoundedProbDeflate`) are proved (a4efd862; TR2 with HDIAG's
`exists_le_newtonSchulzTest_iterate`, 2774bb52). The statement fixes are those of §3.2 (SG6/SG7
`hX`, DF2 `hQ`). At the merge of `origin/main` with the tightened HDIAG bounds (5960c3fa) the
targets file imports `NewtonSchulzSign/Accuracy` (where SN4 and TR1 now are); the statements of TR2
and TR3 did not change there.

**Hardening.** In the hardening stage (`docs/design/Computation-Hardening.md`, Stage 2b) the
rounded model `MatrixFreeRoundedProb` gained the arguments `dec B cost mem`. As recorded in §2.3 and
§2.4 of that note (b228ea6f): SIGN drops `IsExactIntLit dec I.sem 1` from its `Contracts` and passes
`B := 1`, cost `newtonSchulzSignCount p mm N F` and memory $8N^2 + 7$ at tag `p`; DEFLATE drops
`IsExactIntLit dec I.sem 2` and passes `B := 2`, cost `deflateCount p mm qr N r` and memory
$10N^2 + 2Nr + 2$. Both now assume the exact floor conversion through the model's
`IsIndexExactSem`, which they never use. The proofs go through `MatrixFreeRoundedProb.of_exec` and
the existing `cnt_le_of_exec_compiled` lemmas (SG11, DF8).

**Where it lives** (D8 move and F10 splits, 36d32068 and 10b17ab6, statements unchanged):

| ids | file (`NLAlib/…`) |
|---|---|
| LP1–LP3 | `Computation/Loops.lean` (new; `Exec.lean` is over F10) |
| PP1–PP7 | `Matrix/Computation/KernelContracts.lean` (appended) |
| IM1–IM13 | `Matrix/Computation/InterpMachine.lean` (appended) |
| PK1–PK22 | `Matrix/Computation/PairKernels.lean` (copies, zero, negation, mirror), `…/PairKernels/Hermitian.lean` (`zhermShift`, `zhermScale`), `…/PairKernels/HermAvg.lean`, `…/PairKernels/BoxTest.lean`, `…/PairKernels/Arithmetic.lean` (`zidentity`, `zadd`, `zsub`, `zscal`, `zconjTranspose`, `ztraceRe`) |
| SG1–SG5 | `Matrix/Computation/NewtonSchulzSignProgram/Blocks.lean` (test, step, loop; also the block congruences EC9, EC10 of COMPDYN S2) |
| SG6–SG11 | `Matrix/Computation/NewtonSchulzSignProgram.lean` (refinement, registered tree, counts) |
| DF1–DF8 | `Matrix/Computation/DeflationProgram.lean` (new) |
| CT1 | `RandomMatrix/Computation/ComplexTape.lean` (new) |
| TR2, TR3 | `Eigensolvers/SignDeflatePrograms.lean` (new; the proofs import `Eigensolvers`, layer 3) |

The program and target definitions of §1 are where §1 says. Private helpers used across a split
are public now, under their names. `NLAlibScaffold` is removed (6b757e18) and `lakefile.toml` is
main's again.

**Registration (§6).** `scripts/Targets.lean`'s `models` lists `MatrixFreeRoundedProb` (Part C of
the hardening patches, c983ecc5). `docs/targets.toml` has the trees
`NLAlib.newtonSchulzSignProg.compiled`, `NLAlib.deflateProg.compiled` and the targets
`NLAlib.MatrixFreeRoundedProbNewtonSchulzSign`, `NLAlib.MatrixFreeRoundedProbDeflate`, with the
witnesses `NLAlib.matrixFreeRoundedProbNewtonSchulzSign_nonVacuous` and
`NLAlib.matrixFreeRoundedProbDeflate_nonVacuous`
(`RandomMatrix/Computation/RoundedTargetWitnesses.lean`, at `gridSem t` with $u = 2^{-t} > 0$, the
grid kernels `gridMM`/`gridQR` and the grid machine `gridMachine t` of
`Matrix/Computation/GridMachine.lean`) and their `witness_sem` lines (1f43e0a9). Hashes, statements
and normal forms are empty and `reviewed = ""`, for the maintainer's re-pin.
