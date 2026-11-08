/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.KernelContracts
public import NLAlib.Matrix.Computation.SpectralBisectionNode.Compress

/-!
# The compression block as a routine specification (scaffold, pilot)

The pilot of stage PROG-LOGIC (design note `docs/design/Computation-ProgramLogic.md` §7.3, ids
PL73–PL76): one specification of `NLAlib.eighCompressBlock` for every mode, from which
`NLAlib.holds_of_exec_eighCompressBlock` (mode `liberal`) and
`NLAlib.exists_exec_eighCompressBlock` (mode `total`) follow with their statements unchanged.
Final home: `NLAlib/Matrix/Computation/SpectralBisectionNode/Compress.lean`.

## Main results

* `NLAlib.spec_zconjTranspose`, `NLAlib.spec_zhermAvg`, `NLAlib.spec_zhermShift`: the pair
  kernels the block calls, as adapters from their existing lemma pairs.
* `NLAlib.spec_eighCompressBlock`: the compression block's specification.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {Su Sg : Type} {toNat : K → ℕ} {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}
  {unif : K → Su → K} {normal : Sg → K × K}

/-- **The conjugate transpose as a routine specification** (adapter; final home
`NLAlib/Matrix/Computation/PairKernels/Arithmetic.lean`): from a state holding the $m \times n$
matrix $\mathbf{A}$ at `xo` of `X`, the run of `NLAlib.zconjTranspose` modifies only the output
block at `yo` of `Y`, which then holds `M.conjTransposeMat A`, and keeps the tape positions; in
mode `total` it also succeeds, given the standard model and the output block writable. No
printed source. -/
theorem spec_zconjTranspose (md : Mode) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : md.Needs (IsRelErrSem u dec (fun _ _ => True) I.sem)) (p : P) (m n : ℕ) {X Y : ℕ}
    {xo yo : IExp ℕ} (A : Matrix (Fin m) (Fin n) (K × K))
    (hXY : blockDisjoint (matBlock Y yo.eval n m 2) (matBlock X xo.eval m n 2) = true) :
    let M := I.sem.toFloatMachine p toNat mmR qrR unif normal
    RoutineSpec md I (fun st => pairLayout.Holds st.store p X xo.eval A ∧
        md.Needs (Writable st.store p Y yo.eval (n * m * 2)))
      (zconjTranspose (ι := ι) p (.const m) (.const n) X xo Y yo) [matBlock Y yo.eval n m 2]
      fun st st' => pairLayout.Holds st'.store p Y yo.eval (M.conjTransposeMat A) ∧
        PosKept st st' := by
  sorry

/-- **The Hermitian average as a routine specification** (adapter; final home
`NLAlib/Matrix/Computation/PairKernels/HermAvg.lean`): from a state holding $\mathbf{A}$ at `xo`
of `X` and the value $c$ in the cell `c` (outside the output block), the run of
`NLAlib.zhermAvg` modifies only the output block at `yo` of `Y`, which then holds
`M.hermAvg A cv`, and keeps the tape positions; in mode `total` it also succeeds, given the
standard model, $c$ decoding to a nonzero value and the output block writable. No printed
source. -/
theorem spec_zhermAvg (md : Mode) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : md.Needs (IsRelErrSem u dec (fun _ _ => True) I.sem)) (p : P) (n : ℕ) {X Y : ℕ}
    {xo yo : IExp ℕ} {c : Cell ℕ ℕ} (cv : K) (A : Matrix (Fin n) (Fin n) (K × K))
    (hXY : blockDisjoint (matBlock Y yo.eval n n 2) (matBlock X xo.eval n n 2) = true)
    (hcY : blockDisjoint (c.buf, c.idx.eval, 1) (matBlock Y yo.eval n n 2) = true) :
    let M := I.sem.toFloatMachine p toNat mmR qrR unif normal
    RoutineSpec md I (fun st => pairLayout.Holds st.store p X xo.eval A ∧
        st.store.read p c.buf c.idx.eval = some cv ∧
        md.Needs (dec p cv ≠ 0 ∧ Writable st.store p Y yo.eval (n * n * 2)))
      (zhermAvg (ι := ι) p (.const n) X xo c Y yo) [matBlock Y yo.eval n n 2]
      fun st st' => pairLayout.Holds st'.store p Y yo.eval (M.hermAvg A cv) ∧ PosKept st st' := by
  sorry

/-- **The Hermitian shift as a routine specification** (adapter; final home
`NLAlib/Matrix/Computation/PairKernels/Hermitian.lean`): as `NLAlib.spec_zhermAvg` for
`NLAlib.zhermShift`, which writes `M.hermShift A cv`. The run succeeds wherever the cell `c` is,
so the cell's disjointness from the output block is a correctness-only hypothesis: it guards the
value clause of the postcondition, not the precondition. No printed source. -/
theorem spec_zhermShift (md : Mode) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : md.Needs (IsRelErrSem u dec (fun _ _ => True) I.sem)) (p : P) (n : ℕ) {X Y : ℕ}
    {xo yo : IExp ℕ} {c : Cell ℕ ℕ} (cv : K) (A : Matrix (Fin n) (Fin n) (K × K))
    (hXY : blockDisjoint (matBlock Y yo.eval n n 2) (matBlock X xo.eval n n 2) = true) :
    let M := I.sem.toFloatMachine p toNat mmR qrR unif normal
    RoutineSpec md I (fun st => pairLayout.Holds st.store p X xo.eval A ∧
        st.store.read p c.buf c.idx.eval = some cv ∧
        md.Needs (Writable st.store p Y yo.eval (n * n * 2)))
      (zhermShift (ι := ι) p (.const n) X xo c Y yo) [matBlock Y yo.eval n n 2]
      fun st st' => (blockDisjoint (c.buf, c.idx.eval, 1) (matBlock Y yo.eval n n 2) = true →
        pairLayout.Holds st'.store p Y yo.eval (M.hermShift A cv)) ∧ PosKept st st' := by
  sorry

/-- **The compression block's specification.** If kernel `mm` is a routine on interleaved pairs,
then from a state holding the $k \times r$ basis $\mathbf{Q}$ at `qo` of `Qa`, the node matrix
$\mathbf{A}$ at `mo` of `Ma` and the values $c_2$ and $\sigma$ in the cells `two` and `sg`, the
run of `NLAlib.eighCompressBlock` modifies only its four scratch blocks and the output block at
`co` of `Ma` and keeps the tape positions. If the cells `two` and `sg` lie outside the output
block (a correctness-only hypothesis, so it guards the value clause), that block then holds
`M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Q) A) Q) c₂) σ` for the machine `M` of
the semantics. In mode `total` the run also succeeds, given the standard model at $u$ with every
value in range, $c_2$ decoding to a nonzero value and the footprint writable. No printed
source. -/
theorem spec_eighCompressBlock {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) (md : Mode)
    {u : P → ℝ} {dec : P → K → ℝ} (hsem : md.Needs (IsRelErrSem u dec (fun _ _ => True) I.sem))
    (p : P) (k r : ℕ) {Qa Ma Qh C1 C2 C3 : ℕ} {qo mo co : IExp ℕ} {two sg : Cell ℕ ℕ}
    (c₂ σ : K) (Q : Matrix (Fin k) (Fin r) (K × K)) (A : Matrix (Fin k) (Fin k) (K × K))
    (hbufs : [Qa, Ma, Qh, C1, C2, C3].Nodup)
    (hcells : two.buf ∉ [Qh, C1, C2, C3] ∧ sg.buf ∉ [Qh, C1, C2, C3]) :
    let M := I.sem.toFloatMachine p toNat mmR qrR unif normal
    let fp := [matBlock Qh 0 r k 2, matBlock C1 0 r k 2, matBlock C2 0 r r 2,
      matBlock C3 0 r r 2, matBlock Ma co.eval r r 2]
    RoutineSpec md I (fun st => pairLayout.Holds st.store p Qa qo.eval Q ∧
        pairLayout.Holds st.store p Ma mo.eval A ∧
        st.store.read p two.buf two.idx.eval = some c₂ ∧
        st.store.read p sg.buf sg.idx.eval = some σ ∧
        md.Needs (dec p c₂ ≠ 0 ∧ WritableBlocks st.store p fp))
      (eighCompressBlock p mm (.const k) (.const r) Qa qo Ma mo co two sg Qh C1 C2 C3) fp
      fun st st' => (blockDisjoint (Ma, co.eval, 2 * (r * r)) (two.buf, two.idx.eval, 1) = true ∧
          blockDisjoint (Ma, co.eval, 2 * (r * r)) (sg.buf, sg.idx.eval, 1) = true →
          pairLayout.Holds st'.store p Ma co.eval
            (M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Q) A) Q) c₂) σ)) ∧
        PosKept st st' := by
  sorry

end NLAlib
