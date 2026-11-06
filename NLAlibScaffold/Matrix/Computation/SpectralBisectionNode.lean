/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SpectralBisectionProgramTree
public import NLAlib.Matrix.Computation.SpectralBisectionTape
public import NLAlibScaffold.Computation.KernelCongr
public import NLAlibScaffold.Matrix.Computation.NewtonSchulzSignProgram
public import NLAlibScaffold.Matrix.Computation.PairKernels

/-!
# The node step of the spectral bisection program (scaffold)

Statements for a new file `NLAlib/Matrix/Computation/SpectralBisectionNode.lean` (stage COMPDYN
S2b, design note `docs/design/Computation-EighProgram.md`, §4): the blocks of the node step of
`NLAlib.eighProg` compute the matching operations of `NLAlib.eighStep` on the machine of the
semantics (`NLAlib.Computation.ScalarSem.toFloatMachine`, `NLAlib.eighTapeMachine`), and succeed
under the standard model. Each value statement is a partial equality: under kernels that are
routines on pairs and a semantics that decides flags, a successful run writes exactly the machine's
value, with no contract on the rounding. The pilot's statements of stage S1c/S1d
(`NLAlibScaffold/Matrix/Computation/{PairKernels,NewtonSchulzSignProgram}.lean`) are cited at
constant sizes and moved to index expressions by `NLAlibScaffold/Computation/KernelCongr.lean`.

## Main results

* `NLAlib.holds_of_exec_eighSignLoop`, `NLAlib.holds_of_exec_eighSignBlock`,
  `NLAlib.exists_exec_eighSignBlock`: the sign step with the shallow step limit.
* `NLAlib.holds_of_exec_eighLeafBlock`, `NLAlib.holds_of_exec_eighChildBlock`,
  `NLAlib.holds_of_exec_eighDeflateBlock`, `NLAlib.holds_of_exec_eighCompressBlock`,
  `NLAlib.holds_of_exec_eighSplitBlock`: the blocks.
* `NLAlib.holds_of_exec_eighNodeBlock`, `NLAlib.exists_exec_eighNodeBlock`: the node step computes
  `NLAlib.eighStep`, and succeeds.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {Su Sg : Type} {toNat : K → ℕ} {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}
  {unif : K → Su → K} {normal : Sg → K × K}

/-! ### The sign step with the shallow step limit -/

/-- **The bounded Newton–Schulz loop computes `NLAlib.newtonSchulzLoop`**: if kernel `mm` of `I`
is the routine `mmR` on interleaved pairs and the semantics decides flags at `p`, a successful run
of the loop of `NLAlib.eighSignBlock` with $F$ iterations, from a state whose block at `X` holds
$\mathbf{A}$, whose scratch buffer `W` holds $\mathrm{mm}(\mathbf{A}, \mathbf{A})$, whose cells
$0$, $3$, $4$ of the scratch buffer `t` hold $\eta$, the machine's one and $-\eta$, and whose cell
$1$ holds the flag of the test of $\mathbf{A}$, ends with the block at `X` holding
`NLAlib.newtonSchulzLoop M η F A` ($M$ the machine of the semantics at `p` with product `mmR`);
every cell outside the block at `X` and the buffers `t`, `W`, `V` is unchanged, the store shape and
the tape positions too. No printed source.
Proof: induction on $F$ generalizing the state and $\mathbf{A}$; `NLAlib.Computation.exec_run_bind`,
`NLAlib.Computation.exec_loop` and `List.range_succ_eq_map` peel the first iteration, whose
comparison (`NLAlib.Computation.exec_ite`, `NLAlib.Computation.cmpStep`) reads the flag and the
stored one: by `hflag` (`NLAlib.Computation.ScalarSem.DecidesFlags`) it is false exactly when the
flag is the machine's zero, that is when the test passes; then every later iteration skips too
(the state is unchanged, `NLAlib.newtonSchulzLoop` returns $\mathbf{A}$ at every step limit when the
test passes), and otherwise `NLAlib.holds_of_exec_newtonSchulzStepBlock` and
`NLAlib.holds_of_exec_newtonSchulzTestBlock` (pilot) re-establish the hypotheses for
`NLAlib.newtonSchulzRounded M A` and the induction hypothesis applies. M, about 70 lines. -/
theorem holds_of_exec_eighSignLoop {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) (p : P)
    (hflag : I.sem.DecidesFlags p) (n F : ℕ) {X W V t : ℕ} {xo : IExp ℕ} {η : K}
    {st st' : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)}
    (hA : pairLayout.Holds st.store p X xo.eval A)
    (hW : pairLayout.Holds st.store p W 0 (mmR A A))
    (hη : st.store.read p t 0 = some η)
    (hone : st.store.read p t 3 = some (I.sem.toFloatMachine p toNat mmR qrR unif normal).one)
    (hlo : st.store.read p t 4 =
      some ((I.sem.toFloatMachine p toNat mmR qrR unif normal).neg η))
    (hf : st.store.read p t 1 = some (if newtonSchulzTest
      (I.sem.toFloatMachine p toNat mmR qrR unif normal) η A then
        (I.sem.toFloatMachine p toNat mmR qrR unif normal).zero else
        (I.sem.toFloatMachine p toNat mmR qrR unif normal).one))
    (hWX : W ≠ X) (hVX : V ≠ X) (hWV : W ≠ V) (htX : t ≠ X) (htW : t ≠ W) (htV : t ≠ V)
    (h : exec I (forRange (ι := ι) (.const F) fun _ => ifThenElse p .eq ⟨t, 1⟩ ⟨t, 3⟩
      (do
        newtonSchulzStepBlock p mm (.const n) X xo W V ⟨t, 2⟩
        newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩)
      (pure ())).run st = some st') :
    pairLayout.Holds st'.store p X xo.eval
        (newtonSchulzLoop (I.sem.toFloatMachine p toNat mmR qrR unif normal) η F A) ∧
      (∀ q b i, b ≠ t → b ≠ W → b ≠ V →
        blockDisjoint (b, i, 1) (X, xo.eval, 2 * (n * n)) = true →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  sorry

/-- **The sign step computes `NLAlib.newtonSchulzSign`**: if kernel `mm` of `I` is the routine
`mmR` on interleaved pairs and the semantics decides flags at `p`, a successful run of
`NLAlib.eighSignBlock` at size $n$ and step limit $F$, from a state whose block at `A` holds the
stored $\mathbf{A}$ and whose cells `po`, `po + 1` of `par` hold $\varepsilon$ and $b$, with the
output block at `X` disjoint from both, ends with the output block holding
`NLAlib.newtonSchulzSign M ε b F A` (the machine of the semantics at `p` with product `mmR`, for
every choice of its other black boxes); every cell outside the output block is unchanged, the store
shape and the tape positions too. No printed source.
Proof: as the pilot's `NLAlib.holds_of_exec_newtonSchulzSignProg` (scaffold), with the loop by
`NLAlib.holds_of_exec_eighSignLoop` in place of
`NLAlib.holds_of_exec_whileFuel_newtonSchulz`: the set-up (three
`NLAlib.Computation.exec_alloc`s, four instructions, `NLAlib.Computation.holds_of_exec_zhermScale`,
`NLAlib.holds_of_exec_newtonSchulzTestBlock`) gives its hypotheses, and its conclusion is
`NLAlib.newtonSchulzSign` by definition; the pops keep the output block and the frame
(`NLAlib.Computation.Store.read_pop_of_lt`, `NLAlib.Computation.Store.shape_pop`). M, about 80
lines. -/
theorem holds_of_exec_eighSignBlock {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) (p : P)
    (hflag : I.sem.DecidesFlags p) (n F : ℕ) {A par X : ℕ} {ao po xo : IExp ℕ}
    {st st' : St P K C} {A₀ : Matrix (Fin n) (Fin n) (K × K)} {ε b : K}
    (hA : pairLayout.Holds st.store p A ao.eval A₀)
    (hε : st.store.read p par po.eval = some ε) (hb : st.store.read p par (po.eval + 1) = some b)
    (hXA : blockDisjoint (X, xo.eval, 2 * (n * n)) (A, ao.eval, 2 * (n * n)) = true)
    (hXp : blockDisjoint (X, xo.eval, 2 * (n * n)) (par, po.eval, 2) = true)
    (h : exec I (eighSignBlock p mm (.const n) (.const F) A ao par po X xo).run st = some st') :
    pairLayout.Holds st'.store p X xo.eval
        (newtonSchulzSign (I.sem.toFloatMachine p toNat mmR qrR unif normal) ε b F A₀) ∧
      (∀ q b' i, blockDisjoint (b', i, 1) (X, xo.eval, 2 * (n * n)) = true →
        st'.store.read q b' i = st.store.read q b' i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  sorry

/-- **The sign step always succeeds** under the standard model at $u$ with every value in range,
$u(p) < 1$ and an exact literal $1$, if kernel `mm` of `I` is the routine `mmR` on interleaved
pairs, $n \ge 1$, $b$ decodes to a nonzero value and the output block at `X` (tag `p`) has $2n^2$
cells (hypotheses on the inputs as `NLAlib.holds_of_exec_eighSignBlock`): unlike the pilot's
`whileFuel` loop, the bounded loop does not fail when no iterate passes the test. No printed
source.
Proof: the set-up as in the pilot's `NLAlib.exists_exec_newtonSchulzSignProg` (scaffold); then
`NLAlib.Computation.exists_exec_loop_eq_some_of_forall` with the invariant of
`NLAlib.holds_of_exec_eighSignLoop` at the iterate reached: each iteration's comparison succeeds
(`NLAlib.Computation.IsRelErrSem.decidesFlags`, scaffold) and its body succeeds
(`NLAlib.exists_exec_newtonSchulzStepBlock`, `NLAlib.exists_exec_newtonSchulzTestBlock`, pilot);
the pops succeed. M, about 60 lines. -/
theorem exists_exec_eighSignBlock {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    {u : P → ℝ} {dec : P → K → ℝ} (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hlit : IsExactIntLit dec I.sem 1) (p : P) (hu : u p < 1) (n F : ℕ) (hn : 0 < n)
    {A par X : ℕ} {ao po xo : IExp ℕ} {st : St P K C} {A₀ : Matrix (Fin n) (Fin n) (K × K)}
    {ε b : K} (hA : pairLayout.Holds st.store p A ao.eval A₀)
    (hε : st.store.read p par po.eval = some ε) (hb : st.store.read p par (po.eval + 1) = some b)
    (hb0 : dec p b ≠ 0)
    (hXA : blockDisjoint (X, xo.eval, 2 * (n * n)) (A, ao.eval, 2 * (n * n)) = true)
    (hXp : blockDisjoint (X, xo.eval, 2 * (n * n)) (par, po.eval, 2) = true)
    (hX : ∃ len, st.store.shape[X]? = some (p, len) ∧ xo.eval + 2 * (n * n) ≤ len) :
    ∃ st', exec I (eighSignBlock p mm (.const n) (.const F) A ao par po X xo).run st =
      some st' := by
  sorry

/-! ### The blocks of a node -/

/-- **A leaf writes its output**: a successful run of `NLAlib.eighLeafBlock` for a node of size
$k$ whose matrix $\mathbf{A}$ is held at `mo` of `Ma` ends with the block at `uo` of `Ua` holding
the machine's identity (`NLAlib.FloatMachine.identityMat`), the cells $eo + i$ of `Ea` the real
parts $\operatorname{Re} a_{ii}$ (`diag`) or the machine's zero, and the kind cell the literal
$1$; every cell outside these blocks and the kind cell is unchanged, the store shape and the tape
positions too. No printed source.
Proof: `NLAlib.Computation.exec_run_bind`; `NLAlib.Computation.exec_zidentity_congr` (scaffold)
and the pilot's `NLAlib.Computation.holds_of_exec_zidentity`; the loop of copies or literals by
`NLAlib.Computation.forall_of_exec_loop_eq_some` (pilot) with
`NLAlib.Computation.exec_seq_instr_copy` (the source cell is outside the written blocks) or
`NLAlib.Computation.exec_seq_instr_lit`; the literal $1$ by
`NLAlib.Computation.exec_seq_instr_litIdx`. M, about 40 lines. -/
theorem holds_of_exec_eighLeafBlock (p : P) (diag : Bool) (k : ℕ) {Ma Ua Ea : ℕ}
    {mo uo eo : IExp ℕ} {kd : Cell ℕ ℕ} {st st' : St P K C}
    {A : Matrix (Fin k) (Fin k) (K × K)} (hA : pairLayout.Holds st.store p Ma mo.eval A)
    (hUA : blockDisjoint (Ua, uo.eval, 2 * (k * k)) (Ma, mo.eval, 2 * (k * k)) = true)
    (hEA : blockDisjoint (Ea, eo.eval, k) (Ma, mo.eval, 2 * (k * k)) = true)
    (hUE : blockDisjoint (Ua, uo.eval, 2 * (k * k)) (Ea, eo.eval, k) = true)
    (hkd : ∀ x ∈ [(Ma, mo.eval, 2 * (k * k)), (Ua, uo.eval, 2 * (k * k)), (Ea, eo.eval, k)],
      blockDisjoint (kd.buf, kd.idx.eval, 1) x = true)
    (h : exec I (eighLeafBlock (ι := ι) p diag (.const k) Ma mo Ua uo Ea eo kd).run st =
      some st') :
    let M := I.sem.toFloatMachine p toNat mmR qrR unif normal
    pairLayout.Holds st'.store p Ua uo.eval (M.identityMat k) ∧
      (∀ i : Fin k, st'.store.read p Ea (eo.eval + i) = some (if diag then (A i i).1 else M.zero)) ∧
      st'.store.read p kd.buf kd.idx.eval = I.sem.lit p ((1 : ℕ) : ℚ) ∧
      (∀ q b i, blockDisjoint (b, i, 1) (Ua, uo.eval, 2 * (k * k)) = true →
        blockDisjoint (b, i, 1) (Ea, eo.eval, k) = true →
        blockDisjoint (b, i, 1) (kd.buf, kd.idx.eval, 1) = true →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  sorry

/-- **One child on the same slot**: a successful run of `NLAlib.eighChildBlock` for a node of size
$k$ whose matrix $\mathbf{A}$ is held at `mo` of `Ma`, the cell `sg` holding $\sigma$, ends with the
block at `mo'` of `Ma` (disjoint from the one at `mo`) holding `M.hermShift A σ`, the size cell the
literal $k$ and the kind cell the literal `code`; every other cell is unchanged, the store shape and
the tape positions too. No printed source.
Proof: `NLAlib.Computation.exec_run_bind`; `NLAlib.Computation.exec_zhermShift_congr` (scaffold)
and the pilot's `NLAlib.Computation.holds_of_exec_zhermShift`; two
`NLAlib.Computation.exec_seq_instr_litIdx`. S, about 25 lines. -/
theorem holds_of_exec_eighChildBlock (p : P) (k : ℕ) {Ma : ℕ} {mo mo' : IExp ℕ}
    {sg sz kd : Cell ℕ ℕ} (code : ℕ) {σ : K} {st st' : St P K C}
    {A : Matrix (Fin k) (Fin k) (K × K)} (hA : pairLayout.Holds st.store p Ma mo.eval A)
    (hσ : st.store.read p sg.buf sg.idx.eval = some σ)
    (hAA : blockDisjoint (Ma, mo'.eval, 2 * (k * k)) (Ma, mo.eval, 2 * (k * k)) = true)
    (hsg : blockDisjoint (sg.buf, sg.idx.eval, 1) (Ma, mo'.eval, 2 * (k * k)) = true)
    (hsz : blockDisjoint (sz.buf, sz.idx.eval, 1) (Ma, mo'.eval, 2 * (k * k)) = true)
    (hkd : blockDisjoint (kd.buf, kd.idx.eval, 1) (Ma, mo'.eval, 2 * (k * k)) = true)
    (hszkd : blockDisjoint (sz.buf, sz.idx.eval, 1) (kd.buf, kd.idx.eval, 1) = true)
    (h : exec I (eighChildBlock (ι := ι) p (.const k) Ma mo mo' sg sz kd code).run st =
      some st') :
    pairLayout.Holds st'.store p Ma mo'.eval
        ((I.sem.toFloatMachine p toNat mmR qrR unif normal).hermShift A σ) ∧
      st'.store.read p sz.buf sz.idx.eval = I.sem.lit p ((k : ℕ) : ℚ) ∧
      st'.store.read p kd.buf kd.idx.eval = I.sem.lit p ((code : ℕ) : ℚ) ∧
      (∀ q b i, blockDisjoint (b, i, 1) (Ma, mo'.eval, 2 * (k * k)) = true →
        blockDisjoint (b, i, 1) (sz.buf, sz.idx.eval, 1) = true →
        blockDisjoint (b, i, 1) (kd.buf, kd.idx.eval, 1) = true →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  sorry

/-- **Randomized deflation on stored samples computes `NLAlib.deflate`**: if kernels `mm`, `qr` of
`I` are the routines `mmR`, `qrR` on interleaved pairs, a successful run of
`NLAlib.eighDeflateBlock` for a node of size $k \le n$ at slot $lo$ of depth $d$ with rank
$r \le k$, side $b$, the stored projector $\mathbf{P}$ ($k \times k$) at offset $0$ of `Pm`, the
cell `sq` holding the stored $\sqrt{1/2}$ (`NLAlib.Computation.ScalarSem.sqrtHalf`) and the $4n^2$
Gaussian words of the level in `Sg` (word $w$ the tape value at position $4n^2 d + w$), ends with
the block at `qo` of `Qa` holding `NLAlib.deflate M r P G` for $\mathbf{G}$ the leading $k \times k$
block of the test matrix of side $b$ of the node's samples (`NLAlib.eighTapeSample`), $M$ the
machine of the interpretation (`NLAlib.eighTapeMachine`); every cell outside that block and the
scratch buffers `G`, `Y`, `Qf`, `Rf` is unchanged, the store shape and the tape positions too. No
printed source.
Proof: the loop writes the stored test matrix: entry $(i, j)$ is the pair
`NLAlib.Computation.ScalarSem.tapeNormal` of the tape at the sample of `NLAlib.eighTapeSample`
(two `NLAlib.Computation.exec_seq_instr_bin`, `NLAlib.Computation.forall_of_exec_loop_eq_some`,
pilot; the word $2(n(2(lo + j) + s) + i)$ of `Sg` is the tape at twice the sample, `mul_add`),
which is `NLAlib.leadingBlock` of the samples mapped by the machine's normal sampler; the two
kernel calls by the pilot's `NLAlib.Computation.IsMatMulKernel.holds_of_kcallStore_eq_some` and
`NLAlib.Computation.IsQRKernel.holds_of_kcallStore_eq_some`; the copy of the first $r$ columns by
`NLAlib.Computation.exec_zcopy_congr` (scaffold) and the pilot's
`NLAlib.Computation.holds_of_exec_zcopy`, column-major packed so the first $r$ columns of
$\mathbf{Q}$ are its first $2kr$ words; unfold `NLAlib.deflate` ($r \le k$, so no zero column). M,
about 80 lines. -/
theorem holds_of_exec_eighDeflateBlock {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) (p : P) (n k r d lo : ℕ) (hk : lo + k ≤ n)
    (hr : r ≤ k) (b : Bool) {Sg Pm G Y Qf Rf Qa : ℕ} {sq : Cell ℕ ℕ} {qo : IExp ℕ}
    {st st' : St P K C} {Pmat : Matrix (Fin k) (Fin k) (K × K)}
    (hP : pairLayout.Holds st.store p Pm 0 Pmat)
    (hsq : st.store.read p sq.buf sq.idx.eval = some (I.sem.sqrtHalf p))
    (hSg : ∀ w < 4 * (n * n), st.store.read p Sg w = some (I.tape .gaussian (4 * (n * n) * d + w)))
    (hbufs : [Sg, Pm, G, Y, Qf, Rf, Qa].Nodup) (hsqb : sq.buf ∉ [G, Y, Qf, Rf, Qa])
    (h : exec I (eighDeflateBlock p mm qr (.const n) (.const k) (.const r) (.const lo)
      (if b then 0 else 1) Sg sq Pm G Y Qf Rf Qa qo).run st = some st') :
    pairLayout.Holds st'.store p Qa qo.eval
        (deflate (eighTapeMachine I p mmR qrR) r Pmat
          (leadingBlock k ((eighTapeSample n d lo).2 b))) ∧
      (∀ q b' i, b' ∉ [G, Y, Qf, Rf] → blockDisjoint (b', i, 1) (Qa, qo.eval, 2 * (k * r)) = true →
        st'.store.read q b' i = st.store.read q b' i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  sorry

/-- **Deflation on stored samples succeeds** under the standard model with every value in range,
if the kernels are routines on pairs and the buffers `G`, `Y`, `Qf`, `Rf` have $2n^2$ cells and the
block at `qo` of `Qa` fits (hypotheses on the inputs as `NLAlib.holds_of_exec_eighDeflateBlock`).
No printed source.
Proof: each product succeeds (`bin_ok`, `trivial`); the kernel calls succeed by the pilot's
`NLAlib.Computation.IsMatMulKernel.kcallStore_eq`, `NLAlib.Computation.IsQRKernel.kcallStore_eq`
(the reads by `NLAlib.Computation.EntryLayout.holds_iff_readBlock_eq_some`, pilot); the copy by the
pilot's `NLAlib.Computation.exists_exec_zcopy` after `NLAlib.Computation.exec_zcopy_congr`. M,
about 50 lines. -/
theorem exists_exec_eighDeflateBlock {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (n k r d lo : ℕ)
    (hk : lo + k ≤ n) (hr : r ≤ k) (b : Bool) {Sg Pm G Y Qf Rf Qa : ℕ} {sq : Cell ℕ ℕ}
    {qo : IExp ℕ} {st : St P K C} {Pmat : Matrix (Fin k) (Fin k) (K × K)}
    (hP : pairLayout.Holds st.store p Pm 0 Pmat)
    (hsq : st.store.read p sq.buf sq.idx.eval = some (I.sem.sqrtHalf p))
    (hSg : ∀ w < 4 * (n * n), st.store.read p Sg w = some (I.tape .gaussian (4 * (n * n) * d + w)))
    (hbufs : [Sg, Pm, G, Y, Qf, Rf, Qa].Nodup) (hsqb : sq.buf ∉ [G, Y, Qf, Rf, Qa])
    (hscr : ∀ X ∈ [G, Y, Qf, Rf], ∃ len, st.store.shape[X]? = some (p, len) ∧ 2 * (n * n) ≤ len)
    (hQa : ∃ len, st.store.shape[Qa]? = some (p, len) ∧ qo.eval + 2 * (k * r) ≤ len) :
    ∃ st', exec I (eighDeflateBlock p mm qr (.const n) (.const k) (.const r) (.const lo)
      (if b then 0 else 1) Sg sq Pm G Y Qf Rf Qa qo).run st = some st' := by
  sorry

/-- **A compression computes the machine's compression**: if kernel `mm` of `I` is the routine `mmR`
on interleaved pairs, a successful run of `NLAlib.eighCompressBlock` for the stored $k \times r$
basis $\mathbf{Q}$ at `qo` of `Qa`, the node matrix $\mathbf{A}$ at `mo` of `Ma`, the cells `two`
and `sg` holding $c_2$ and $\sigma$, writing at `co` of `Ma` (disjoint from the block at `mo`), ends
with that block holding `M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Q) A) Q) c₂) σ`;
every cell outside it and the scratch buffers is unchanged, the store shape and the tape positions
too. No printed source.
Proof: `NLAlib.Computation.exec_run_bind` splits the block;
`NLAlib.Computation.exec_zconjTranspose_congr`, `NLAlib.Computation.exec_zhermAvg_congr`,
`NLAlib.Computation.exec_zhermShift_congr` (scaffold) and the pilot's
`NLAlib.Computation.holds_of_exec_zconjTranspose`, `NLAlib.Computation.holds_of_exec_zhermAvg`,
`NLAlib.Computation.holds_of_exec_zhermShift`; the two kernel calls by
`NLAlib.Computation.IsMatMulKernel.holds_of_kcallStore_eq_some` (pilot). M, about 50 lines. -/
theorem holds_of_exec_eighCompressBlock {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (p : P) (k r : ℕ) {Qa Ma Qh C1 C2 C3 : ℕ} {qo mo co : IExp ℕ} {two sg : Cell ℕ ℕ} {c₂ σ : K}
    {st st' : St P K C} {Q : Matrix (Fin k) (Fin r) (K × K)} {A : Matrix (Fin k) (Fin k) (K × K)}
    (hQ : pairLayout.Holds st.store p Qa qo.eval Q) (hA : pairLayout.Holds st.store p Ma mo.eval A)
    (htwo : st.store.read p two.buf two.idx.eval = some c₂)
    (hσ : st.store.read p sg.buf sg.idx.eval = some σ)
    (hbufs : [Qa, Ma, Qh, C1, C2, C3].Nodup) (hcells : two.buf ∉ [Qh, C1, C2, C3] ∧
      sg.buf ∉ [Qh, C1, C2, C3])
    (hco : blockDisjoint (Ma, co.eval, 2 * (r * r)) (Ma, mo.eval, 2 * (k * k)) = true)
    (hcocells : blockDisjoint (Ma, co.eval, 2 * (r * r)) (two.buf, two.idx.eval, 1) = true ∧
      blockDisjoint (Ma, co.eval, 2 * (r * r)) (sg.buf, sg.idx.eval, 1) = true)
    (h : exec I (eighCompressBlock p mm (.const k) (.const r) Qa qo Ma mo co two sg Qh C1 C2
      C3).run st = some st') :
    let M := I.sem.toFloatMachine p toNat mmR qrR unif normal
    pairLayout.Holds st'.store p Ma co.eval
        (M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Q) A) Q) c₂) σ) ∧
      (∀ q b i, b ∉ [Qh, C1, C2, C3] → blockDisjoint (b, i, 1) (Ma, co.eval, 2 * (r * r)) = true →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  sorry

/-- **A compression succeeds** under the standard model at $u$ with every value in range, the
cell `two` decoding to a nonzero value, if kernel `mm` is a routine on pairs and the scratch buffers
have $2n^2$ cells, $k, r \le n$ (hypotheses on the inputs as
`NLAlib.holds_of_exec_eighCompressBlock`). No printed source.
Proof: as `NLAlib.exists_exec_eighDeflateBlock`, with the pilot's
`NLAlib.Computation.exists_exec_zhermShift` and the existence statements of `zconjTranspose` and
`zhermAvg` in the pilot's `NLAlib/Matrix/Computation/PairKernels.lean` scaffold (divisions by the
nonzero `two`). M, about 50 lines. -/
theorem exists_exec_eighCompressBlock {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    {u : P → ℝ} {dec : P → K → ℝ} (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P)
    (n k r : ℕ) (hk : k ≤ n) (hr : r ≤ k) {Qa Ma Qh C1 C2 C3 : ℕ} {qo mo co : IExp ℕ}
    {two sg : Cell ℕ ℕ} {c₂ σ : K} {st : St P K C} {Q : Matrix (Fin k) (Fin r) (K × K)}
    {A : Matrix (Fin k) (Fin k) (K × K)} (hQ : pairLayout.Holds st.store p Qa qo.eval Q)
    (hA : pairLayout.Holds st.store p Ma mo.eval A)
    (htwo : st.store.read p two.buf two.idx.eval = some c₂) (htwo0 : dec p c₂ ≠ 0)
    (hσ : st.store.read p sg.buf sg.idx.eval = some σ)
    (hbufs : [Qa, Ma, Qh, C1, C2, C3].Nodup) (hcells : two.buf ∉ [Qh, C1, C2, C3] ∧
      sg.buf ∉ [Qh, C1, C2, C3])
    (hco : blockDisjoint (Ma, co.eval, 2 * (r * r)) (Ma, mo.eval, 2 * (k * k)) = true)
    (hcolen : ∃ len, st.store.shape[Ma]? = some (p, len) ∧ co.eval + 2 * (r * r) ≤ len)
    (hscr : ∀ X ∈ [Qh, C1, C2, C3], ∃ len, st.store.shape[X]? = some (p, len) ∧
      2 * (n * n) ≤ len) :
    ∃ st', exec I (eighCompressBlock p mm (.const k) (.const r) Qa qo Ma mo co two sg Qh C1 C2
      C3).run st = some st' := by
  sorry

/-- **A split writes the outcome of `NLAlib.eighStep`'s split**: if the kernels of `I` are the
routines `mmR`, `qrR` on interleaved pairs, a successful run of `NLAlib.eighSplitBlock` at the slot
$lo$ of depth $d$ for a node of size $k$ (with $lo + k \le n$) whose matrix $\mathbf{A}$ is held at
its block of `Ma`, with $0 < k_+ < k$, the projectors $\mathbf{P}_\pm$ at offset $0$ of `Pp`, `Pm`,
the level's Gaussian words in `Sg`, and the cells `one`, `two`, `sg`, `nsg` holding the machine's
one, $\mathrm{fl}(2)$, $\sigma$ and $-\sigma$, ends with: $\mathbf{Q}_+ =$
`NLAlib.deflate M kp Pp G₊` and $\mathbf{Q}_-$ packed at the node's block of `Qa`, the compressions
of `NLAlib.eighStep` at the blocks of the slots $lo$ and $lo + k_+$ of depth $d + 1$ in `Ma`, the
sizes $k_+$ and $k - k_+$ in their cells of `Sz`, the kind $4$ and $k_+$ in the node's cells of `Kd`
and `Kp`; every other cell of the arenas is unchanged ($M$ = `NLAlib.eighTapeMachine I p mmR qrR`,
the test matrices those of the node's samples, `NLAlib.eighTapeSample`). No printed source.
Proof: `NLAlib.Computation.exec_alloc` eight times and `NLAlib.Computation.exec_run_bind`; the
stored $\sqrt{1/2}$ by two instructions (`NLAlib.Computation.ScalarSem.sqrtHalf`, read off their
successful runs, `Option.getD_some`); `NLAlib.holds_of_exec_eighDeflateBlock` twice,
`NLAlib.holds_of_exec_eighCompressBlock` twice (the blocks of the slots $lo$, $lo + k_+$ of depth
$d + 1$ are disjoint from each other and from depth $d$, `NLAlib.eighBlockOff`, since
$k_+^2 \le k_+ n$), four `NLAlib.Computation.exec_seq_instr_litIdx`; the pops keep the frame. M,
about 90 lines. -/
theorem holds_of_exec_eighSplitBlock {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) (p : P) (n d lo k kp : ℕ) (hk : lo + k ≤ n)
    (hkp : 0 < kp) (hkpk : kp < k) (H : EighArenas) {Sg Pp Pm : ℕ} {one two sg nsg sq : Cell ℕ ℕ}
    {σ : K} {st st' : St P K C} {A : Matrix (Fin k) (Fin k) (K × K)}
    {Ppm Pmm : Matrix (Fin k) (Fin k) (K × K)}
    {D : ℕ} (hd : d < D) (hH : H.Shaped st.store p n D)
    (hbufs : (H.handles ++ [Sg, Pp, Pm]).Nodup)
    (hA : pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hPp : pairLayout.Holds st.store p Pp 0 Ppm) (hPm : pairLayout.Holds st.store p Pm 0 Pmm)
    (hSg : ∀ w < 4 * (n * n), st.store.read p Sg w = some (I.tape .gaussian (4 * (n * n) * d + w)))
    (hone : st.store.read p one.buf one.idx.eval = I.sem.lit p 1)
    (htwo : st.store.read p two.buf two.idx.eval = I.sem.lit p ((2 : ℕ) : ℚ))
    (hσ : st.store.read p sg.buf sg.idx.eval = some σ)
    (hnσ : st.store.read p nsg.buf nsg.idx.eval =
      some ((eighTapeMachine I p mmR qrR).neg σ))
    (hcells : ∀ c ∈ [one, two, sg, nsg, sq], c.buf ∉ H.handles ++ [Sg, Pp, Pm])
    (h : exec I (eighSplitBlock p mm qr (.const n) (.const d) (.const lo) (.const k) (.const kp) Sg
      Pp Pm H.Ma H.Qa H.Sz H.Kd H.Kp one two sg nsg sq).run st = some st') :
    let M := eighTapeMachine I p mmR qrR
    let s := eighTapeSample n d lo
    let Qp := deflate M kp Ppm (leadingBlock k (s.2 true))
    let Qm := deflate M (k - kp) Pmm (leadingBlock k (s.2 false))
    pairLayout.Holds st'.store p H.Qa (2 * (n * n) * d + 2 * n * lo) Qp ∧
      pairLayout.Holds st'.store p H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (k * kp)) Qm ∧
      pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * lo)
        (M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Qp) A) Qp) (M.ofNat 2)) σ) ∧
      pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * (lo + kp))
        (M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Qm) A) Qm) (M.ofNat 2))
          (M.neg σ)) ∧
      st'.store.read p H.Sz (n * (d + 1) + lo) = I.sem.lit p ((kp : ℕ) : ℚ) ∧
      st'.store.read p H.Sz (n * (d + 1) + (lo + kp)) = I.sem.lit p ((k - kp : ℕ) : ℚ) ∧
      st'.store.read p H.Kd (n * d + lo) = I.sem.lit p ((4 : ℕ) : ℚ) ∧
      st'.store.read p H.Kp (n * d + lo) = I.sem.lit p ((kp : ℕ) : ℚ) ∧
      (∀ q b i, ¬ H.LevelCell n d b i → ¬ H.LevelCell n (d + 1) b i →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  sorry

/-- **A split succeeds** under the standard model at $u$ with every value in range and $u(p) < 1$,
with an exact literal $2$, if the kernels are routines on pairs and the arenas are allocated
(hypotheses on the inputs as `NLAlib.holds_of_exec_eighSplitBlock`). No printed source.
Proof: the eight allocations, the division and the square root succeed (`bin_ok` with the exact
literal $2 \ne 0$; `sqrt_ok` for $\sqrt{\cdot}$ of $\mathrm{fl}(1/2) \ge 0$, `lit_err`); then
`NLAlib.exists_exec_eighDeflateBlock` twice, `NLAlib.exists_exec_eighCompressBlock` twice on the
states the value statements describe, and the four literals (`lit_ok`). M, about 70 lines. -/
theorem exists_exec_eighSplitBlock {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hlit : IsExactIntLit dec I.sem 2) (p : P)
    (hu : u p < 1) (n d lo k kp : ℕ) (hk : lo + k ≤ n) (hkp : 0 < kp) (hkpk : kp < k)
    (H : EighArenas) {Sg Pp Pm : ℕ} {one two sg nsg sq : Cell ℕ ℕ} {σ : K} {st : St P K C}
    {A : Matrix (Fin k) (Fin k) (K × K)} {Ppm Pmm : Matrix (Fin k) (Fin k) (K × K)}
    {D : ℕ} (hd : d < D) (hH : H.Shaped st.store p n D) (hbufs : (H.handles ++ [Sg, Pp, Pm]).Nodup)
    (hA : pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hPp : pairLayout.Holds st.store p Pp 0 Ppm) (hPm : pairLayout.Holds st.store p Pm 0 Pmm)
    (hSg : ∀ w < 4 * (n * n), st.store.read p Sg w = some (I.tape .gaussian (4 * (n * n) * d + w)))
    (hone : st.store.read p one.buf one.idx.eval = I.sem.lit p 1)
    (htwo : st.store.read p two.buf two.idx.eval = I.sem.lit p ((2 : ℕ) : ℚ))
    (hσ : st.store.read p sg.buf sg.idx.eval = some σ)
    (hnσ : st.store.read p nsg.buf nsg.idx.eval = some ((eighTapeMachine I p mmR qrR).neg σ))
    (hcells : ∀ c ∈ [one, two, sg, nsg, sq], c.buf ∉ H.handles ++ [Sg, Pp, Pm])
    (hsq : ∃ s, st.store.write p sq.buf sq.idx.eval default = some s) :
    ∃ st', exec I (eighSplitBlock p mm qr (.const n) (.const d) (.const lo) (.const k) (.const kp)
      Sg Pp Pm H.Ma H.Qa H.Sz H.Kd H.Kp one two sg nsg sq).run st = some st' := by
  sorry

/-! ### The node step -/

/-- **The node step computes `NLAlib.eighStep`**: let the kernels of `I` be the routines `mmR`,
`qrR` on interleaved pairs and the semantics decide flags at `p`; let $M$ be the machine of the
interpretation (`NLAlib.eighTapeMachine`). A successful run of `NLAlib.eighNodeBlock` at the slot
$lo$ of depth $d$ for a node of size $k \ge 2$, $lo + k \le n$, whose matrix $\mathbf{A}$ is held at
its block of `Ma`, whose window $R$ is in the cell $2d$ of `Lv`, whose seed is the cell $lo$ of `Su`
(the tape at uniform position $nd + lo$), with the level's Gaussian words in `Sg`, the stored
$\beta$ in cell $2$ of `par` and the constants (the machine's one, $\mathrm{fl}(2)$,
$\mathrm{fl}(1/2)$, $-1$) in the cells of `c`, ends with the outcome of `NLAlib.eighStep` at the
node's samples (`NLAlib.eighTapeSample`, depth counter $\ell_0 + d$), when it is not a leaf: for one
child on side $b$, the shifted matrix at the same slot of depth $d + 1$, the size $k$ there, and the
kind $2$ ($b$ true) or $3$; for a split into $k_+$, everything `NLAlib.holds_of_exec_eighSplitBlock`
writes. Every cell outside depths $d$ and $d + 1$ of the arenas (and outside `Su`, `Sg`, `c`, `par`,
which are only read) is unchanged, the store shape and the tape positions too. No printed source.
Proof: `NLAlib.Computation.exec_alloc` seven times, the instructions computing $\sigma$, $-\sigma$,
$\ell$, $R/\ell$ and the shift $c$ (`NLAlib.Computation.ScalarSem.tapeUnif`), then
`NLAlib.Computation.exec_zhermShift_congr` with the pilot's
`NLAlib.Computation.holds_of_exec_zhermShift`, `NLAlib.holds_of_exec_eighSignBlock` at
$(\beta, \mathrm{fl}(2R))$, the projectors and the trace (the pilot's
`NLAlib.Computation.holds_of_exec_zhermScale`, `NLAlib.Computation.holds_of_exec_zneg`,
`NLAlib.Computation.read_of_exec_ztraceRe` after the congruences); the index binder by
`NLAlib.Computation.exec_bindIdx` reads $k_+ = \min(\lfloor\cdot\rfloor, k)$, the machine's `toNat`
(`Option.getD_some`), equal to `NLAlib.eighStep`'s `min k _` (`min_comm`); the three
`NLAlib.eighWhen` loops run exactly the branch of `NLAlib.eighStep` (trip counts by `omega`), each
by `NLAlib.holds_of_exec_eighChildBlock` or `NLAlib.holds_of_exec_eighSplitBlock`; unfold
`NLAlib.eighStep` with `hk2` and `hR` (the `if`s fall through to the shift). L, about 160 lines
(split the set-up up to the trace into a private lemma). -/
theorem holds_of_exec_eighNodeBlock {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) (p : P) (hflag : I.sem.DecidesFlags p)
    (n ℓ₀ F d lo k : ℕ) (hk : lo + k ≤ n) (hk2 : 2 ≤ k) (H : EighArenas)
    {par Su Sg c : ℕ} {st st' : St P K C} {A : Matrix (Fin k) (Fin k) (K × K)} {R R₀ ε β : K}
    {D : ℕ} (hd : d < D) (hH : H.Shaped st.store p n D)
    (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup)
    (hA : pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hR : st.store.read p H.Lv (2 * d) = some R)
    (hRtest : (eighTapeMachine I p mmR qrR).le R ((eighTapeMachine I p mmR qrR).mul ε R₀) = false)
    (hpar : st.store.read p par 2 = some β)
    (hSu : st.store.read p Su lo = some (I.tape .uniform (n * d + lo)))
    (hSg : ∀ w < 4 * (n * n), st.store.read p Sg w = some (I.tape .gaussian (4 * (n * n) * d + w)))
    (hc : st.store.read p c 0 = I.sem.lit p 1 ∧ st.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
      st.store.read p c 2 = some ((eighTapeMachine I p mmR qrR).div
        (eighTapeMachine I p mmR qrR).one ((eighTapeMachine I p mmR qrR).ofNat 2)) ∧
      st.store.read p c 3 = some ((eighTapeMachine I p mmR qrR).neg
        (eighTapeMachine I p mmR qrR).one))
    (h : exec I (eighNodeBlock p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) (.const lo)
      (.const k) par H.Lv Su Sg H.Ma H.Qa H.Sz H.Kd H.Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩).run st =
        some st') :
    let M := eighTapeMachine I p mmR qrR
    (match eighStep M n F R₀ β A R ε (ℓ₀ + d) (eighTapeSample n d lo) with
      | .leaf _ _ => False
      | .shift b A' _ =>
        pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * lo) A' ∧
          st'.store.read p H.Sz (n * (d + 1) + lo) = I.sem.lit p ((k : ℕ) : ℚ) ∧
          st'.store.read p H.Kd (n * d + lo) = I.sem.lit p (((if b then 2 else 3 : ℕ)) : ℚ)
      | .split kp _ Qp Qm Ap Am _ =>
        pairLayout.Holds st'.store p H.Qa (2 * (n * n) * d + 2 * n * lo) Qp ∧
          pairLayout.Holds st'.store p H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (k * kp)) Qm ∧
          pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * lo) Ap ∧
          pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * (lo + kp)) Am ∧
          st'.store.read p H.Sz (n * (d + 1) + lo) = I.sem.lit p ((kp : ℕ) : ℚ) ∧
          st'.store.read p H.Sz (n * (d + 1) + (lo + kp)) = I.sem.lit p ((k - kp : ℕ) : ℚ) ∧
          st'.store.read p H.Kd (n * d + lo) = I.sem.lit p ((4 : ℕ) : ℚ) ∧
          st'.store.read p H.Kp (n * d + lo) = I.sem.lit p ((kp : ℕ) : ℚ)) ∧
      (∀ q b i, ¬ H.LevelCell n d b i → ¬ H.LevelCell n (d + 1) b i →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  sorry

/-- **The node step succeeds** under the standard model at $u$ with every value in range,
$u(p) < 1$, exact literals up to $2$ and the exact floor conversion, if the kernels are routines on
pairs, the window decodes to a positive value, the depth counter $\ell_0 + d$ is at least $1$ and
the arenas are allocated (hypotheses on the inputs as `NLAlib.holds_of_exec_eighNodeBlock`): no
operation fails (the divisions are by $\mathrm{fl}(2)$, $\ell$ and $b = \mathrm{fl}(2R) \ne 0$, the
sign step does not fail for want of steps, the conversion is total). No printed source.
Proof: the set-up instructions succeed (`bin_ok`, `lit_ok`; $\mathrm{fl}(\ell) \ne 0$ for
$\ell \ge 1$ and $u(p) < 1$, `lit_err`); `NLAlib.exists_exec_eighSignBlock` with
$\overline{\mathrm{fl}(2R)} = 2\bar R(1 + \delta) \ne 0$; the projectors, the trace and the binder
(`htn`, so `NLAlib.Computation.toNatStep` succeeds); then the branch taken
(`NLAlib.exists_exec_eighSplitBlock`, or the child block by the pilot's
`NLAlib.Computation.exists_exec_zhermShift` and two literals). M, about 90 lines. -/
theorem exists_exec_eighNodeBlock {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hlit : IsExactIntLit dec I.sem 2)
    (htn : IsExactToNat dec I.sem) (p : P) (hu : u p < 1) (n ℓ₀ F d lo k : ℕ) (hk : lo + k ≤ n)
    (hk2 : 2 ≤ k) (hℓ : 1 ≤ ℓ₀ + d) (H : EighArenas) {par Su Sg c : ℕ} {st : St P K C}
    {A : Matrix (Fin k) (Fin k) (K × K)} {R β : K}
    {D : ℕ} (hd : d < D) (hH : H.Shaped st.store p n D)
    (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup)
    (hA : pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hR : st.store.read p H.Lv (2 * d) = some R) (hR0 : 0 < dec p R)
    (hpar : st.store.read p par 2 = some β)
    (hSu : ∃ v, st.store.read p Su lo = some v)
    (hSg : ∀ w < 4 * (n * n), ∃ v, st.store.read p Sg w = some v)
    (hc : st.store.read p c 0 = I.sem.lit p 1 ∧ st.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
      (∃ v, st.store.read p c 2 = some v) ∧ ∃ v, st.store.read p c 3 = some v) :
    ∃ st', exec I (eighNodeBlock p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) (.const lo)
      (.const k) par H.Lv Su Sg H.Ma H.Qa H.Sz H.Kd H.Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩).run st =
        some st' := by
  sorry

end NLAlib
