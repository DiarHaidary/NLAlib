/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Contract
public import NLAlib.Computation.BLAS
public import NLAlib.Matrix.Computation.EntrywiseRounding
public import NLAlib.Matrix.Computation.InterpMachine
public import NLAlibScaffold.Computation.Exec

/-!
# The complex-pair kernels compute the floating-point machine's operations (scaffold)

Statements for a new file `NLAlib/Matrix/Computation/PairKernels.lean` (stage COMPDYN S1c,
design note `docs/design/Computation-SignDeflatePrograms.md`, §2): the **rounded
specifications** of the complex kernels of `NLAlib/Computation/BLAS.lean`. Under any
interpretation, a successful run of a kernel on blocks that hold stored complex matrices
(`NLAlib.Computation.EntryLayout.Holds`, interleaved layout) ends with the output block holding
exactly the result of the corresponding operation of the machine of the semantics
(`NLAlib.Computation.ScalarSem.toFloatMachine`), one rounding per real operation, and every other
cell unchanged; and the run succeeds when the operations it performs succeed. With the exact
specifications of `NLAlib/Matrix/Computation/InterpMachine.lean` (scaffold) and the machine
contract, these give the exact and the rounded behaviour of each kernel.

## Main results

* `NLAlib.Computation.holds_of_exec_zcopy`, `NLAlib.Computation.holds_of_exec_zzero`,
  `NLAlib.Computation.holds_of_exec_zneg`, `NLAlib.Computation.holds_of_exec_zmirror`,
  `NLAlib.Computation.holds_of_exec_zhermShift`, `NLAlib.Computation.holds_of_exec_zhermScale`,
  `NLAlib.Computation.holds_of_exec_zhermAvg`, `NLAlib.Computation.read_of_exec_zboxTest`, and
  for the kernels SIGN and DEFLATE do not call, `NLAlib.Computation.holds_of_exec_zidentity`,
  `NLAlib.Computation.holds_of_exec_zadd`, `NLAlib.Computation.holds_of_exec_zsub`,
  `NLAlib.Computation.holds_of_exec_zscal`, `NLAlib.Computation.holds_of_exec_zconjTranspose`,
  `NLAlib.Computation.read_of_exec_ztraceRe`: what a successful run computes.
* `NLAlib.Computation.exists_exec_zcopy`, `NLAlib.Computation.exists_exec_zzero`,
  `NLAlib.Computation.exists_exec_zneg`, `NLAlib.Computation.exists_exec_zmirror`,
  `NLAlib.Computation.exists_exec_zhermShift`, `NLAlib.Computation.exists_exec_zhermScale`,
  `NLAlib.Computation.exists_exec_zhermAvg`, `NLAlib.Computation.exists_exec_zboxTest`: when the
  run succeeds.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Computation

open Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {Su Sg : Type} {toNat : K → ℕ} {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}
  {unif : K → Su → K} {normal : Sg → K × K}

/-! ### Copies and literals -/

/-- **`zcopy` copies**: a successful run of `NLAlib.Computation.zcopy` from a state whose block at
`X` holds the complex $m \times n$ matrix $\mathbf{A}$, into a block at `Y` disjoint from it,
ends with the block at `Y` holding $\mathbf{A}$, every cell outside it unchanged, the same store
shape and the same tape positions. No printed source.
Proof: `NLAlib.Computation.forall_of_exec_loop_eq_some` (scaffold) on the word loop with the
invariant "words below $w$ copied, the rest unchanged"; each step is
`NLAlib.Computation.exec_seq_instr_copy` with `NLAlib.Computation.Store.read_of_write_eq_some`
and `NLAlib.Computation.Store.read_of_write_eq_some_of_ne`; then
`NLAlib.Computation.pairLayout.holds_iff` (scaffold). M, about 40 lines. -/
theorem holds_of_exec_zcopy (p : P) (m n : ℕ) {X Y : ℕ} {xo yo : IExp ℕ} {st st' : St P K C}
    {A : Matrix (Fin m) (Fin n) (K × K)} (hA : pairLayout.Holds st.store p X xo.eval A)
    (hXY : blockDisjoint (Y, yo.eval, 2 * (m * n)) (X, xo.eval, 2 * (m * n)) = true)
    (h : exec I (zcopy (ι := ι) p (.const m) (.const n) X xo Y yo).run st = some st') :
    pairLayout.Holds st'.store p Y yo.eval A ∧
      (∀ q b i, blockDisjoint (b, i, 1) (Y, yo.eval, 2 * (m * n)) = true →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  sorry

/-- **`zcopy` succeeds** from a state whose block at `X` holds a complex $m \times n$ matrix and
whose buffer `Y` at tag `p` is long enough. No printed source.
Proof: `NLAlib.Computation.exists_exec_loop_eq_some_of_forall` with the invariant "the store has
the shape of `st` and the block at `X` still holds $\mathbf{A}$" (disjointness);
`NLAlib.Computation.Store.exists_write_eq_some_of_getElem?_shape`. S, about 20 lines. -/
theorem exists_exec_zcopy (p : P) (m n : ℕ) {X Y : ℕ} {xo yo : IExp ℕ} {st : St P K C}
    {A : Matrix (Fin m) (Fin n) (K × K)} (hA : pairLayout.Holds st.store p X xo.eval A)
    (hXY : blockDisjoint (Y, yo.eval, 2 * (m * n)) (X, xo.eval, 2 * (m * n)) = true)
    (hY : ∃ len, st.store.shape[Y]? = some (p, len) ∧ yo.eval + 2 * (m * n) ≤ len) :
    ∃ st', exec I (zcopy (ι := ι) p (.const m) (.const n) X xo Y yo).run st = some st' := by
  sorry

/-- **`zzero` writes the stored zero matrix**: a successful run of `NLAlib.Computation.zzero`
ends with the block at `Y` holding the machine's zero matrix (`NLAlib.FloatMachine.zeroMat`),
every cell outside it unchanged, the same store shape and the same tape positions. No printed
source.
Proof: as `NLAlib.Computation.holds_of_exec_zcopy`, each step
`NLAlib.Computation.exec_seq_instr_lit`; the literal $0$ read off its successful run is the
machine's zero (`Option.getD_some`). M, about 30 lines. -/
theorem holds_of_exec_zzero (p : P) (m n : ℕ) {Y : ℕ} {yo : IExp ℕ} {st st' : St P K C}
    (h : exec I (zzero (ι := ι) p (.const m) (.const n) Y yo).run st = some st') :
    pairLayout.Holds st'.store p Y yo.eval
      ((I.sem.toFloatMachine p toNat mmR qrR unif normal).zeroMat (Fin m) (Fin n)) ∧
      (∀ q b i, blockDisjoint (b, i, 1) (Y, yo.eval, 2 * (m * n)) = true →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  sorry

/-- **`zzero` succeeds** under the standard model with every value in range, when the buffer `Y`
at tag `p` is long enough. No printed source.
Proof: as `NLAlib.Computation.exists_exec_zcopy`, each literal by `lit_ok` (`trivial`). S, about
15 lines. -/
theorem exists_exec_zzero (p : P) (m n : ℕ) {Y : ℕ} {yo : IExp ℕ} {st : St P K C}
    {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hY : ∃ len, st.store.shape[Y]? = some (p, len) ∧ yo.eval + 2 * (m * n) ≤ len) :
    ∃ st', exec I (zzero (ι := ι) p (.const m) (.const n) Y yo).run st = some st' := by
  sorry

/-! ### Negation and the Hermitian completion -/

/-- **`zneg` negates**: a successful run of `NLAlib.Computation.zneg` from a state whose block at
`X` holds $\mathbf{A}$, into a block at `Y` disjoint from it or equal to it (in place), ends with
the block at `Y` holding the machine's negation of $\mathbf{A}$ (`NLAlib.FloatMachine.negMat`),
every cell outside it unchanged, the same store shape and the same tape positions. No printed
source.
Proof: as `NLAlib.Computation.holds_of_exec_zcopy`; in place, word $w$ is read before it is
written and never read again. M, about 40 lines. -/
theorem holds_of_exec_zneg (p : P) (m n : ℕ) {X Y : ℕ} {xo yo : IExp ℕ} {st st' : St P K C}
    {A : Matrix (Fin m) (Fin n) (K × K)} (hA : pairLayout.Holds st.store p X xo.eval A)
    (hXY : blockDisjoint (Y, yo.eval, 2 * (m * n)) (X, xo.eval, 2 * (m * n)) = true ∨
      (Y = X ∧ yo.eval = xo.eval))
    (h : exec I (zneg (ι := ι) p (.const m) (.const n) X xo Y yo).run st = some st') :
    pairLayout.Holds st'.store p Y yo.eval
      ((I.sem.toFloatMachine p toNat mmR qrR unif normal).negMat A) ∧
      (∀ q b i, blockDisjoint (b, i, 1) (Y, yo.eval, 2 * (m * n)) = true →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  sorry

/-- **`zneg` succeeds** under the standard model with every value in range, when the buffer `Y` at
tag `p` is long enough. No printed source.
Proof: as `NLAlib.Computation.exists_exec_zcopy`, each negation by the `neg` clause. S, about 20
lines. -/
theorem exists_exec_zneg (p : P) (m n : ℕ) {X Y : ℕ} {xo yo : IExp ℕ} {st : St P K C}
    {A : Matrix (Fin m) (Fin n) (K × K)} (hA : pairLayout.Holds st.store p X xo.eval A)
    (hXY : blockDisjoint (Y, yo.eval, 2 * (m * n)) (X, xo.eval, 2 * (m * n)) = true ∨
      (Y = X ∧ yo.eval = xo.eval))
    {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hY : ∃ len, st.store.shape[Y]? = some (p, len) ∧ yo.eval + 2 * (m * n) ≤ len) :
    ∃ st', exec I (zneg (ι := ι) p (.const m) (.const n) X xo Y yo).run st = some st' := by
  sorry

/-- **`zmirror` completes a stored Hermitian matrix**: if the block at `Y` holds the parts of the
entries $b_{ij}$, $i \le j$, of a complex $n \times n$ matrix $\mathbf{B}$ whose diagonal
imaginary parts are the machine's zero, a successful run of `NLAlib.Computation.zmirror` ends
with the block holding the machine's Hermitian matrix with upper triangle and real diagonal those
of $\mathbf{B}$ (`NLAlib.FloatMachine.hermFrom`), every cell outside it unchanged, the same store
shape and the same tape positions. No printed source.
Proof: `NLAlib.Computation.forall_of_exec_loop_eq_some` (scaffold) twice, the invariant "the
upper triangle and the diagonal unchanged, the entries $(j', i)$ with $i < j'$, $j' < j$ written";
each step reads an upper entry (never written by the loop) and writes a lower one
(`NLAlib.Computation.exec_seq_instr_copy`, `NLAlib.Computation.exec_seq_instr_un`); the index
$2(j + ni)$ of a lower entry differs from every upper index (`omega` on `i < j`). M, about 60
lines. -/
theorem holds_of_exec_zmirror (p : P) (n : ℕ) {Y : ℕ} {yo : IExp ℕ} {st st' : St P K C}
    {B : Matrix (Fin n) (Fin n) (K × K)}
    (hB : ∀ i j : Fin n, i ≤ j → st.store.read p Y (yo.eval + 2 * (i + n * j)) = some (B i j).1 ∧
      st.store.read p Y (yo.eval + 2 * (i + n * j) + 1) = some (B i j).2)
    (hdiag : ∀ i, (B i i).2 = (I.sem.toFloatMachine p toNat mmR qrR unif normal).zero)
    (h : exec I (zmirror (ι := ι) p (.const n) Y yo).run st = some st') :
    pairLayout.Holds st'.store p Y yo.eval
      ((I.sem.toFloatMachine p toNat mmR qrR unif normal).hermFrom (fun i j => B i j)
        fun i => (B i i).1) ∧
      (∀ q b i, blockDisjoint (b, i, 1) (Y, yo.eval, 2 * (n * n)) = true →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  sorry

/-- **`zmirror` succeeds** under the standard model with every value in range, when the block at
`Y` holds the upper triangle of $\mathbf{B}$ and the buffer `Y` at tag `p` is long enough. No
printed source.
Proof: as `NLAlib.Computation.exists_exec_zcopy`, with the invariant of
`NLAlib.Computation.holds_of_exec_zmirror`. S, about 25 lines. -/
theorem exists_exec_zmirror (p : P) (n : ℕ) {Y : ℕ} {yo : IExp ℕ} {st : St P K C}
    {B : Matrix (Fin n) (Fin n) (K × K)}
    (hB : ∀ i j : Fin n, i < j → st.store.read p Y (yo.eval + 2 * (i + n * j)) = some (B i j).1 ∧
      st.store.read p Y (yo.eval + 2 * (i + n * j) + 1) = some (B i j).2)
    {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hY : ∃ len, st.store.shape[Y]? = some (p, len) ∧ yo.eval + 2 * (n * n) ≤ len) :
    ∃ st', exec I (zmirror (ι := ι) p (.const n) Y yo).run st = some st' := by
  sorry

/-! ### The Hermitian kernels -/

/-- **`zhermShift` computes the machine's shift**: a successful run of
`NLAlib.Computation.zhermShift` from a state whose block at `X` holds the complex $n \times n$
matrix $\mathbf{A}$ and whose cell `c` holds $c$, into a block at `Y` disjoint from the block at
`X` and from `c`, ends with the block at `Y` holding `M.hermShift A c` for the machine `M` of the
semantics at `p`, every cell outside it unchanged, the same store shape and the same tape
positions. No printed source.
Proof: the run is three statements in sequence (`NLAlib.Computation.exec_run_bind`): the upper
copy loop (as `NLAlib.Computation.holds_of_exec_zcopy`, on the entries $i < j$), the diagonal loop
(`NLAlib.Computation.exec_seq_instr_bin` with the sub's result, then the literal $0$), and
`NLAlib.Computation.holds_of_exec_zmirror` with $\mathbf{B}$ the upper copy and the diagonal; the
read-back values are the machine's (`Option.getD_some`), and `NLAlib.FloatMachine.hermShift`
unfolds to that `NLAlib.FloatMachine.hermFrom`. M, about 60 lines. -/
theorem holds_of_exec_zhermShift (p : P) (n : ℕ) {X Y : ℕ} {xo yo : IExp ℕ} {c : Cell ℕ ℕ}
    {cv : K} {st st' : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)}
    (hA : pairLayout.Holds st.store p X xo.eval A)
    (hc : st.store.read p c.buf c.idx.eval = some cv)
    (hXY : blockDisjoint (Y, yo.eval, 2 * (n * n)) (X, xo.eval, 2 * (n * n)) = true)
    (hcY : blockDisjoint (c.buf, c.idx.eval, 1) (Y, yo.eval, 2 * (n * n)) = true)
    (h : exec I (zhermShift (ι := ι) p (.const n) X xo c Y yo).run st = some st') :
    pairLayout.Holds st'.store p Y yo.eval
      ((I.sem.toFloatMachine p toNat mmR qrR unif normal).hermShift A cv) ∧
      (∀ q b i, blockDisjoint (b, i, 1) (Y, yo.eval, 2 * (n * n)) = true →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  sorry

/-- **`zhermShift` succeeds** under the standard model with every value in range, when the buffer
`Y` at tag `p` is long enough. No printed source.
Proof: `NLAlib.Computation.exists_exec_zcopy`-style loops for the copy and the diagonal, then
`NLAlib.Computation.exists_exec_zmirror`, the frames of the earlier loops giving its hypotheses;
each operation by `bin_ok`, `lit_ok`, `neg` (`trivial` for the range). M, about 40 lines. -/
theorem exists_exec_zhermShift (p : P) (n : ℕ) {X Y : ℕ} {xo yo : IExp ℕ} {c : Cell ℕ ℕ}
    {cv : K} {st : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)}
    (hA : pairLayout.Holds st.store p X xo.eval A)
    (hc : st.store.read p c.buf c.idx.eval = some cv)
    (hXY : blockDisjoint (Y, yo.eval, 2 * (n * n)) (X, xo.eval, 2 * (n * n)) = true)
    (hcY : blockDisjoint (c.buf, c.idx.eval, 1) (Y, yo.eval, 2 * (n * n)) = true)
    {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hY : ∃ len, st.store.shape[Y]? = some (p, len) ∧ yo.eval + 2 * (n * n) ≤ len) :
    ∃ st', exec I (zhermShift (ι := ι) p (.const n) X xo c Y yo).run st = some st' := by
  sorry

/-- **`zhermScale` computes the machine's scaling**: as
`NLAlib.Computation.holds_of_exec_zhermShift`, the block at `Y` ends holding `M.hermScale A c`.
No printed source.
Proof: as `NLAlib.Computation.holds_of_exec_zhermShift`, the upper loop dividing both parts.
M, about 60 lines. -/
theorem holds_of_exec_zhermScale (p : P) (n : ℕ) {X Y : ℕ} {xo yo : IExp ℕ} {c : Cell ℕ ℕ}
    {cv : K} {st st' : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)}
    (hA : pairLayout.Holds st.store p X xo.eval A)
    (hc : st.store.read p c.buf c.idx.eval = some cv)
    (hXY : blockDisjoint (Y, yo.eval, 2 * (n * n)) (X, xo.eval, 2 * (n * n)) = true)
    (hcY : blockDisjoint (c.buf, c.idx.eval, 1) (Y, yo.eval, 2 * (n * n)) = true)
    (h : exec I (zhermScale (ι := ι) p (.const n) X xo c Y yo).run st = some st') :
    pairLayout.Holds st'.store p Y yo.eval
      ((I.sem.toFloatMachine p toNat mmR qrR unif normal).hermScale A cv) ∧
      (∀ q b i, blockDisjoint (b, i, 1) (Y, yo.eval, 2 * (n * n)) = true →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  sorry

/-- **`zhermScale` succeeds** under the standard model with every value in range, when $c$ decodes
to a nonzero value and the buffer `Y` at tag `p` is long enough. No printed source.
Proof: as `NLAlib.Computation.exists_exec_zhermShift`, the divisions by `bin_ok` with `hcv`.
M, about 40 lines. -/
theorem exists_exec_zhermScale (p : P) (n : ℕ) {X Y : ℕ} {xo yo : IExp ℕ} {c : Cell ℕ ℕ}
    {cv : K} {st : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)}
    (hA : pairLayout.Holds st.store p X xo.eval A)
    (hc : st.store.read p c.buf c.idx.eval = some cv)
    (hXY : blockDisjoint (Y, yo.eval, 2 * (n * n)) (X, xo.eval, 2 * (n * n)) = true)
    (hcY : blockDisjoint (c.buf, c.idx.eval, 1) (Y, yo.eval, 2 * (n * n)) = true)
    {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hcv : dec p cv ≠ 0)
    (hY : ∃ len, st.store.shape[Y]? = some (p, len) ∧ yo.eval + 2 * (n * n) ≤ len) :
    ∃ st', exec I (zhermScale (ι := ι) p (.const n) X xo c Y yo).run st = some st' := by
  sorry

/-- **`zhermAvg` computes the machine's Hermitian part**: as
`NLAlib.Computation.holds_of_exec_zhermShift`, the block at `Y` ends holding `M.hermAvg A c`.
No printed source.
Proof: as `NLAlib.Computation.holds_of_exec_zhermShift`; each upper part is written twice (the
sum or difference, then its quotient), which `NLAlib.Computation.Store.write_of_write_eq_some`
collapses. M, about 70 lines. -/
theorem holds_of_exec_zhermAvg (p : P) (n : ℕ) {X Y : ℕ} {xo yo : IExp ℕ} {c : Cell ℕ ℕ}
    {cv : K} {st st' : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)}
    (hA : pairLayout.Holds st.store p X xo.eval A)
    (hc : st.store.read p c.buf c.idx.eval = some cv)
    (hXY : blockDisjoint (Y, yo.eval, 2 * (n * n)) (X, xo.eval, 2 * (n * n)) = true)
    (hcY : blockDisjoint (c.buf, c.idx.eval, 1) (Y, yo.eval, 2 * (n * n)) = true)
    (h : exec I (zhermAvg (ι := ι) p (.const n) X xo c Y yo).run st = some st') :
    pairLayout.Holds st'.store p Y yo.eval
      ((I.sem.toFloatMachine p toNat mmR qrR unif normal).hermAvg A cv) ∧
      (∀ q b i, blockDisjoint (b, i, 1) (Y, yo.eval, 2 * (n * n)) = true →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  sorry

/-- **`zhermAvg` succeeds** under the standard model with every value in range, when $c$ decodes
to a nonzero value and the buffer `Y` at tag `p` is long enough (every addition, subtraction,
negation and literal then succeeds, and every division by $c$). No printed source.
Proof: as `NLAlib.Computation.exists_exec_zhermShift`, each operation by `bin_ok`, `lit_ok`,
`neg` of `NLAlib.Computation.IsRelErrSem` (`trivial` for the range). M, about 45 lines. -/
theorem exists_exec_zhermAvg (p : P) (n : ℕ) {X Y : ℕ} {xo yo : IExp ℕ} {c : Cell ℕ ℕ}
    {cv : K} {st : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)} {u : P → ℝ}
    {dec : P → K → ℝ} (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hcv : dec p cv ≠ 0)
    (hA : pairLayout.Holds st.store p X xo.eval A)
    (hc : st.store.read p c.buf c.idx.eval = some cv)
    (hXY : blockDisjoint (Y, yo.eval, 2 * (n * n)) (X, xo.eval, 2 * (n * n)) = true)
    (hcY : blockDisjoint (c.buf, c.idx.eval, 1) (Y, yo.eval, 2 * (n * n)) = true)
    (hY : ∃ len, st.store.shape[Y]? = some (p, len) ∧ yo.eval + 2 * (n * n) ≤ len) :
    ∃ st', exec I (zhermAvg (ι := ι) p (.const n) X xo c Y yo).run st = some st' := by
  sorry

/-! ### The max-modulus test -/

/-- **`zboxTest` computes the machine's test**: a successful run of
`NLAlib.Computation.zboxTest` from a state whose block at `X` holds the complex $m \times n$
matrix $\mathbf{A}$ and whose cells `lo`, `hi` hold $\ell$, $h$, with the flag cell outside the
block and distinct from `lo` and `hi`, ends with the flag holding the machine's zero if every
part $t$ of every entry has $\ell \le t$ and $t \le h$ by the machine's comparisons, and the
machine's one otherwise, every other cell unchanged, the same store shape and the same tape
positions. No printed source.
Proof: after the literal $0$, the word loop keeps the invariant "the flag holds zero if every
part below $w$ passes, one otherwise" (`NLAlib.Computation.forall_of_exec_loop_eq_some`,
scaffold); each step is two `NLAlib.Computation.exec_ite` with the comparisons read off
(`Option.getD_some`); the flat word order covers the parts of every entry once, and
`List.all_eq_true` with `NLAlib.Computation.pairLayout.holds_iff` (scaffold) matches the nested
`List.finRange` test. M, about 70 lines. -/
theorem read_of_exec_zboxTest (p : P) (m n : ℕ) {X : ℕ} {xo : IExp ℕ} {lo hi f : Cell ℕ ℕ}
    {ℓ h : K} {st st' : St P K C} {A : Matrix (Fin m) (Fin n) (K × K)}
    (hA : pairLayout.Holds st.store p X xo.eval A)
    (hlo : st.store.read p lo.buf lo.idx.eval = some ℓ)
    (hhi : st.store.read p hi.buf hi.idx.eval = some h)
    (hfX : blockDisjoint (f.buf, f.idx.eval, 1) (X, xo.eval, 2 * (m * n)) = true)
    (hflo : blockDisjoint (f.buf, f.idx.eval, 1) (lo.buf, lo.idx.eval, 1) = true)
    (hfhi : blockDisjoint (f.buf, f.idx.eval, 1) (hi.buf, hi.idx.eval, 1) = true)
    (hrun : exec I (zboxTest (ι := ι) p (.const m) (.const n) X xo lo hi f).run st = some st') :
    let M := I.sem.toFloatMachine p toNat mmR qrR unif normal
    st'.store.read p f.buf f.idx.eval = some
      (if (List.finRange m).all (fun i => (List.finRange n).all fun j =>
          M.le ℓ (A i j).1 && M.le (A i j).1 h && M.le ℓ (A i j).2 && M.le (A i j).2 h) then
        M.zero else M.one) ∧
      (∀ q b i, blockDisjoint (b, i, 1) (f.buf, f.idx.eval, 1) = true →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  sorry

/-- **`zboxTest` succeeds** under the standard model with every value in range, when the flag cell
can be written. No printed source.
Proof: as `NLAlib.Computation.exists_exec_zcopy`, the invariant "the store has the shape of
`st`", each step two `NLAlib.Computation.exec_ite` (`cmp_le`), the literals by `lit_ok`. S, about
25 lines. -/
theorem exists_exec_zboxTest (p : P) (m n : ℕ) {X : ℕ} {xo : IExp ℕ} {lo hi f : Cell ℕ ℕ}
    {ℓ h : K} {st : St P K C} {A : Matrix (Fin m) (Fin n) (K × K)}
    (hA : pairLayout.Holds st.store p X xo.eval A)
    (hlo : st.store.read p lo.buf lo.idx.eval = some ℓ)
    (hhi : st.store.read p hi.buf hi.idx.eval = some h)
    (hfX : blockDisjoint (f.buf, f.idx.eval, 1) (X, xo.eval, 2 * (m * n)) = true)
    (hflo : blockDisjoint (f.buf, f.idx.eval, 1) (lo.buf, lo.idx.eval, 1) = true)
    (hfhi : blockDisjoint (f.buf, f.idx.eval, 1) (hi.buf, hi.idx.eval, 1) = true)
    {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hf : ∃ s, st.store.write p f.buf f.idx.eval default = some s) :
    ∃ st', exec I (zboxTest (ι := ι) p (.const m) (.const n) X xo lo hi f).run st = some st' := by
  sorry

/-! ### Kernels for later stages: identity, sums, scaling, conjugate transpose, trace -/

/-- **`zidentity` writes the stored identity**: a successful run of
`NLAlib.Computation.zidentity` ends with the block at `Y` holding the machine's identity matrix
(`NLAlib.FloatMachine.identityMat`), every cell outside it unchanged. No printed source.
Proof: `NLAlib.Computation.holds_of_exec_zzero`'s loop, then a loop of literals $1$ at the
diagonal real parts (the indices $2(i + ni)$ are distinct, `omega`). M, about 35 lines. -/
theorem holds_of_exec_zidentity (p : P) (n : ℕ) {Y : ℕ} {yo : IExp ℕ} {st st' : St P K C}
    (h : exec I (zidentity (ι := ι) p (.const n) Y yo).run st = some st') :
    pairLayout.Holds st'.store p Y yo.eval
      ((I.sem.toFloatMachine p toNat mmR qrR unif normal).identityMat n) ∧
      ∀ q b i, blockDisjoint (b, i, 1) (Y, yo.eval, 2 * (n * n)) = true →
        st'.store.read q b i = st.store.read q b i := by
  sorry

/-- **`zadd` adds the parts**: a successful run of `NLAlib.Computation.zadd` from blocks at `X`,
`Y` holding $\mathbf{A}$, $\mathbf{B}$, into a block at `Z` disjoint from both or equal to one of
them, ends with the block at `Z` holding the entrywise machine sums of the real and of the
imaginary parts, every cell outside it unchanged. No printed source.
Proof: as `NLAlib.Computation.holds_of_exec_zneg`. M, about 40 lines. -/
theorem holds_of_exec_zadd (p : P) (m n : ℕ) {X Y Z : ℕ} {xo yo zo : IExp ℕ} {st st' : St P K C}
    {A B : Matrix (Fin m) (Fin n) (K × K)} (hA : pairLayout.Holds st.store p X xo.eval A)
    (hB : pairLayout.Holds st.store p Y yo.eval B)
    (hZX : blockDisjoint (Z, zo.eval, 2 * (m * n)) (X, xo.eval, 2 * (m * n)) = true ∨
      (Z = X ∧ zo.eval = xo.eval))
    (hZY : blockDisjoint (Z, zo.eval, 2 * (m * n)) (Y, yo.eval, 2 * (m * n)) = true ∨
      (Z = Y ∧ zo.eval = yo.eval))
    (h : exec I (zadd (ι := ι) p (.const m) (.const n) X xo Y yo Z zo).run st = some st') :
    let M := I.sem.toFloatMachine p toNat mmR qrR unif normal
    pairLayout.Holds st'.store p Z zo.eval
      (Matrix.of fun i j => (M.add (A i j).1 (B i j).1, M.add (A i j).2 (B i j).2)) ∧
      ∀ q b i, blockDisjoint (b, i, 1) (Z, zo.eval, 2 * (m * n)) = true →
        st'.store.read q b i = st.store.read q b i := by
  sorry

/-- **`zsub` subtracts the parts**: as `NLAlib.Computation.holds_of_exec_zadd`, with the
machine's subtraction. No printed source.
Proof: as `NLAlib.Computation.holds_of_exec_zadd`. M, about 40 lines. -/
theorem holds_of_exec_zsub (p : P) (m n : ℕ) {X Y Z : ℕ} {xo yo zo : IExp ℕ} {st st' : St P K C}
    {A B : Matrix (Fin m) (Fin n) (K × K)} (hA : pairLayout.Holds st.store p X xo.eval A)
    (hB : pairLayout.Holds st.store p Y yo.eval B)
    (hZX : blockDisjoint (Z, zo.eval, 2 * (m * n)) (X, xo.eval, 2 * (m * n)) = true ∨
      (Z = X ∧ zo.eval = xo.eval))
    (hZY : blockDisjoint (Z, zo.eval, 2 * (m * n)) (Y, yo.eval, 2 * (m * n)) = true ∨
      (Z = Y ∧ zo.eval = yo.eval))
    (h : exec I (zsub (ι := ι) p (.const m) (.const n) X xo Y yo Z zo).run st = some st') :
    let M := I.sem.toFloatMachine p toNat mmR qrR unif normal
    pairLayout.Holds st'.store p Z zo.eval
      (Matrix.of fun i j => (M.sub (A i j).1 (B i j).1, M.sub (A i j).2 (B i j).2)) ∧
      ∀ q b i, blockDisjoint (b, i, 1) (Z, zo.eval, 2 * (m * n)) = true →
        st'.store.read q b i = st.store.read q b i := by
  intro M
  have key : (zsub (ι := ι) p (.const m) (.const n) X xo Y yo Z zo).run = .seq
      (.named "zsub" [.idx (.const m), .idx (.const n), .buf X, .idx xo, .buf Y, .idx yo,
        .buf Z, .idx zo] (.seq (.loop (2 * (IExp.const m * IExp.const n)) fun w => .seq
          (.instr (.bin p .sub ⟨Z, zo + .var w⟩ ⟨X, xo + .var w⟩ ⟨Y, yo + .var w⟩)) .skip) .skip))
      .skip := rfl
  rw [key, exec_seq_skip, exec_named, exec_seq_skip] at h
  -- one word of the loop: the read operands, the write and the position
  have bstep : ∀ (k : ℕ) (s₁ s₂ : St P K C),
      exec I (.seq (.instr (.bin p .sub ⟨Z, zo + .var k⟩ ⟨X, xo + .var k⟩ ⟨Y, yo + .var k⟩))
        .skip) s₁ = some s₂ →
      ∃ a c s, s₁.store.read p X (xo.eval + k) = some a ∧
        s₁.store.read p Y (yo.eval + k) = some c ∧
        s₁.store.write p Z (zo.eval + k) (M.sub a c) = some s ∧
        s₂.store = s ∧ s₂.pos = s₁.pos := by
    intro k s₁ s₂ hr
    obtain ⟨a, ha⟩ : ∃ a, s₁.store.read p X (xo.eval + k) = some a := by
      cases hx : s₁.store.read p X (xo.eval + k) with
      | none => simp [exec_seq, exec_instr, Instr.run, hx] at hr
      | some a => exact ⟨a, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c, s₁.store.read p Y (yo.eval + k) = some c := by
      cases hy : s₁.store.read p Y (yo.eval + k) with
      | none => simp [exec_seq, exec_instr, Instr.run, ha, hy] at hr
      | some c => exact ⟨c, rfl⟩
    obtain ⟨v, hv⟩ : ∃ v, I.sem.bin p .sub a c = some v := by
      cases hb : I.sem.bin p .sub a c with
      | none => simp [exec_seq, exec_instr, Instr.run, ha, hc, hb] at hr
      | some v => exact ⟨v, rfl⟩
    obtain ⟨s, hw⟩ : ∃ s, s₁.store.write p Z (zo.eval + k) v = some s := by
      cases hw : s₁.store.write p Z (zo.eval + k) v with
      | none => simp [exec_seq, exec_instr, Instr.run, ha, hc, hv, hw] at hr
      | some s => exact ⟨s, rfl⟩
    have hMv : M.sub a c = v := by
      show (I.sem.bin p .sub a c).getD default = v
      rw [hv]; rfl
    rw [exec_seq_instr_bin (dst := ⟨Z, zo + .var k⟩) I ha hc hv hw, exec_skip] at hr
    cases hr
    exact ⟨a, c, s, ha, hc, hMv ▸ hw, rfl, rfl⟩
  -- distinct words of the loop are distinct cells, of the output block and of the inputs
  have dis : ∀ k w, k < 2 * (m * n) → w < 2 * (m * n) → w ≠ k →
      (X ≠ Z ∨ xo.eval + w ≠ zo.eval + k) ∧ (Y ≠ Z ∨ yo.eval + w ≠ zo.eval + k) := by
    intro k w hk hw hwk
    refine ⟨?_, ?_⟩
    · rcases hZX with h | ⟨h1, h2⟩
      · by_cases hXZ : X = Z
        · right
          subst hXZ
          simp only [blockDisjoint, bne_self_eq_false, Bool.false_or, decide_eq_true_eq,
            Bool.or_eq_true] at h
          omega
        · exact Or.inl hXZ
      · right; omega
    · rcases hZY with h | ⟨h1, h2⟩
      · by_cases hYZ : Y = Z
        · right
          subst hYZ
          simp only [blockDisjoint, bne_self_eq_false, Bool.false_or, decide_eq_true_eq,
            Bool.or_eq_true] at h
          omega
        · exact Or.inl hYZ
      · right; omega
  have inv := forall_of_exec_loop_eq_some (I := I) (fun k s₁ =>
      (∀ w < k, ∃ a c, st.store.read p X (xo.eval + w) = some a ∧
          st.store.read p Y (yo.eval + w) = some c ∧
          s₁.store.read p Z (zo.eval + w) = some (M.sub a c)) ∧
      (∀ w, k ≤ w → w < 2 * (m * n) →
          s₁.store.read p X (xo.eval + w) = st.store.read p X (xo.eval + w)) ∧
      (∀ w, k ≤ w → w < 2 * (m * n) →
          s₁.store.read p Y (yo.eval + w) = st.store.read p Y (yo.eval + w)) ∧
      (∀ q b i, blockDisjoint (b, i, 1) (Z, zo.eval, 2 * (m * n)) = true →
          s₁.store.read q b i = st.store.read q b i) ∧
      s₁.store.shape = st.store.shape ∧ s₁.pos = st.pos) ?_ ?_ h
  rotate_left
  · refine ⟨fun w hw => absurd hw (Nat.not_lt_zero _), fun w _ _ => rfl, fun w _ _ => rfl,
      fun q b i _ => rfl, rfl, rfl⟩
  · intro k hk s₁ s₂ ⟨hZ, hX, hY, hout, hsh, hpos⟩ hr
    have hk2 : k < 2 * (m * n) := hk
    obtain ⟨a, c, s, ha, hc, hw, hs, hp⟩ := bstep k s₁ s₂ hr
    have ha' : st.store.read p X (xo.eval + k) = some a := by
      rw [← hX k le_rfl hk]; exact ha
    have hc' : st.store.read p Y (yo.eval + k) = some c := by
      rw [← hY k le_rfl hk]; exact hc
    have hXn : ∀ w, k + 1 ≤ w → w < 2 * (m * n) →
        s₂.store.read p X (xo.eval + w) = st.store.read p X (xo.eval + w) := by
      intro w hw1 hw2
      rw [hs, Store.read_of_write_eq_some_of_ne hw (dis k w hk hw2 (by omega)).1,
        hX w (by omega) hw2]
    have hYn : ∀ w, k + 1 ≤ w → w < 2 * (m * n) →
        s₂.store.read p Y (yo.eval + w) = st.store.read p Y (yo.eval + w) := by
      intro w hw1 hw2
      rw [hs, Store.read_of_write_eq_some_of_ne hw (dis k w hk hw2 (by omega)).2,
        hY w (by omega) hw2]
    have hZn : ∀ w < k + 1, ∃ a' c', st.store.read p X (xo.eval + w) = some a' ∧
        st.store.read p Y (yo.eval + w) = some c' ∧
        s₂.store.read p Z (zo.eval + w) = some (M.sub a' c') := by
      intro w hw1
      rcases Nat.lt_or_ge w k with hlt | hge
      · obtain ⟨a', c', hxa, hyc, hz⟩ := hZ w hlt
        refine ⟨a', c', hxa, hyc, ?_⟩
        rw [hs, Store.read_of_write_eq_some_of_ne hw
          (Or.inr (show zo.eval + w ≠ zo.eval + k by omega) : Z ≠ Z ∨ zo.eval + w ≠ zo.eval + k)]
        exact hz
      · have hwk : w = k := by omega
        subst hwk
        exact ⟨a, c, ha', hc', by rw [hs, Store.read_of_write_eq_some hw]⟩
    have hout' : ∀ q b i, blockDisjoint (b, i, 1) (Z, zo.eval, 2 * (m * n)) = true →
        s₂.store.read q b i = st.store.read q b i := by
      intro q b i hd
      have hne : b ≠ Z ∨ i ≠ zo.eval + k := by
        by_cases hb : b = Z
        · right
          subst hb
          simp only [blockDisjoint, bne_self_eq_false, Bool.false_or, decide_eq_true_eq,
            Bool.or_eq_true] at hd
          omega
        · exact Or.inl hb
      rw [hs, Store.read_of_write_eq_some_of_ne hw hne]
      exact hout q b i hd
    exact ⟨hZn, hXn, hYn, hout', by rw [hs, Store.shape_of_write_eq_some hw, hsh],
      by rw [hp, hpos]⟩
  obtain ⟨hZ, hX, hY, hout, hsh, hpos⟩ := inv
  have hbnd : ∀ (i : Fin m) (j : Fin n) (t : Fin 2),
      2 * ((i : ℕ) + m * j) + (t : ℕ) < 2 * (m * n) := by
    intro i j t
    have h1 : (i : ℕ) + m * j < m * n := by
      nlinarith [i.isLt, j.isLt, Nat.mul_le_mul_left m (show (j : ℕ) + 1 ≤ n from j.isLt)]
    have := t.isLt
    omega
  refine ⟨fun i j (t : Fin 2) => ?_, hout⟩
  obtain ⟨a, c, hxa, hyc, hz⟩ := hZ _ (hbnd i j t)
  have ha : a = pairLayout.put (A i j) t := Option.some.inj (hxa.symm.trans (hA i j t))
  have hc : c = pairLayout.put (B i j) t := Option.some.inj (hyc.symm.trans (hB i j t))
  rw [ha, hc] at hz
  convert hz using 2 <;> fin_cases t <;> simp [pairLayout]

/-- **`zscal` scales the parts**: a successful run of `NLAlib.Computation.zscal` from a block at
`X` holding $\mathbf{A}$ and a cell `a` holding $a$, into a block at `Y` disjoint from `a` and
disjoint from or equal to the block at `X`, ends with the block at `Y` holding the entrywise
machine products of $a$ with both parts, every cell outside it unchanged. No printed source.
Proof: as `NLAlib.Computation.holds_of_exec_zneg`. M, about 40 lines. -/
theorem holds_of_exec_zscal (p : P) (m n : ℕ) {X Y : ℕ} {xo yo : IExp ℕ} {a : Cell ℕ ℕ} {av : K}
    {st st' : St P K C} {A : Matrix (Fin m) (Fin n) (K × K)}
    (hA : pairLayout.Holds st.store p X xo.eval A)
    (ha : st.store.read p a.buf a.idx.eval = some av)
    (hXY : blockDisjoint (Y, yo.eval, 2 * (m * n)) (X, xo.eval, 2 * (m * n)) = true ∨
      (Y = X ∧ yo.eval = xo.eval))
    (haY : blockDisjoint (a.buf, a.idx.eval, 1) (Y, yo.eval, 2 * (m * n)) = true)
    (h : exec I (zscal (ι := ι) p (.const m) (.const n) a X xo Y yo).run st = some st') :
    let M := I.sem.toFloatMachine p toNat mmR qrR unif normal
    pairLayout.Holds st'.store p Y yo.eval
      (Matrix.of fun i j => (M.mul av (A i j).1, M.mul av (A i j).2)) ∧
      ∀ q b i, blockDisjoint (b, i, 1) (Y, yo.eval, 2 * (m * n)) = true →
        st'.store.read q b i = st.store.read q b i := by
  intro M
  have key : (zscal (ι := ι) p (.const m) (.const n) a X xo Y yo).run = .seq
      (.named "zscal" [.idx (.const m), .idx (.const n), .cell a, .buf X, .idx xo, .buf Y,
        .idx yo] (.seq (.loop (2 * (IExp.const m * IExp.const n)) fun w => .seq
          (.instr (.bin p .mul ⟨Y, yo + .var w⟩ a ⟨X, xo + .var w⟩)) .skip) .skip))
      .skip := rfl
  rw [key, exec_seq_skip, exec_named, exec_seq_skip] at h
  -- one word of the loop
  have bstep : ∀ (k : ℕ) (s₁ s₂ : St P K C), s₁.store.read p a.buf a.idx.eval = some av →
      exec I (.seq (.instr (.bin p .mul ⟨Y, yo + .var k⟩ a ⟨X, xo + .var k⟩)) .skip) s₁ =
        some s₂ →
      ∃ x s, s₁.store.read p X (xo.eval + k) = some x ∧
        s₁.store.write p Y (yo.eval + k) (M.mul av x) = some s ∧
        s₂.store = s ∧ s₂.pos = s₁.pos := by
    intro k s₁ s₂ hav hr
    obtain ⟨x, hx⟩ : ∃ x, s₁.store.read p X (xo.eval + k) = some x := by
      cases hx : s₁.store.read p X (xo.eval + k) with
      | none => simp [exec_seq, exec_instr, Instr.run, hav, hx] at hr
      | some x => exact ⟨x, rfl⟩
    obtain ⟨v, hv⟩ : ∃ v, I.sem.bin p .mul av x = some v := by
      cases hb : I.sem.bin p .mul av x with
      | none => simp [exec_seq, exec_instr, Instr.run, hav, hx, hb] at hr
      | some v => exact ⟨v, rfl⟩
    obtain ⟨s, hw⟩ : ∃ s, s₁.store.write p Y (yo.eval + k) v = some s := by
      cases hw : s₁.store.write p Y (yo.eval + k) v with
      | none => simp [exec_seq, exec_instr, Instr.run, hav, hx, hv, hw] at hr
      | some s => exact ⟨s, rfl⟩
    have hMv : M.mul av x = v := by
      show (I.sem.bin p .mul av x).getD default = v
      rw [hv]; rfl
    rw [exec_seq_instr_bin (dst := (⟨Y, yo + IExp.var k⟩ : Cell ℕ ℕ))
      (x := a) (y := (⟨X, xo + IExp.var k⟩ : Cell ℕ ℕ)) I hav hx hv hw, exec_skip] at hr
    cases hr
    exact ⟨x, s, hx, hMv ▸ hw, rfl, rfl⟩
  -- distinct words are distinct cells
  have dis : ∀ k w, k < 2 * (m * n) → w < 2 * (m * n) → w ≠ k →
      X ≠ Y ∨ xo.eval + w ≠ yo.eval + k := by
    intro k w hk hw hwk
    rcases hXY with h | ⟨h1, h2⟩
    · by_cases hXY' : X = Y
      · right
        subst hXY'
        simp only [blockDisjoint, bne_self_eq_false, Bool.false_or, decide_eq_true_eq,
          Bool.or_eq_true] at h
        omega
      · exact Or.inl hXY'
    · right; omega
  have inv := forall_of_exec_loop_eq_some (I := I) (fun k s₁ =>
      (∀ w < k, ∃ x, st.store.read p X (xo.eval + w) = some x ∧
          s₁.store.read p Y (yo.eval + w) = some (M.mul av x)) ∧
      (∀ w, k ≤ w → w < 2 * (m * n) →
          s₁.store.read p X (xo.eval + w) = st.store.read p X (xo.eval + w)) ∧
      s₁.store.read p a.buf a.idx.eval = some av ∧
      (∀ q b i, blockDisjoint (b, i, 1) (Y, yo.eval, 2 * (m * n)) = true →
          s₁.store.read q b i = st.store.read q b i) ∧
      s₁.store.shape = st.store.shape ∧ s₁.pos = st.pos) ?_ ?_ h
  rotate_left
  · refine ⟨fun w hw => absurd hw (Nat.not_lt_zero _), fun w _ _ => rfl, ha,
      fun q b i _ => rfl, rfl, rfl⟩
  · intro k hk s₁ s₂ ⟨hY, hX, hav, hout, hsh, hpos⟩ hr
    have hk2 : k < 2 * (m * n) := hk
    obtain ⟨x, s, hx, hw, hs, hp⟩ := bstep k s₁ s₂ hav hr
    have hx' : st.store.read p X (xo.eval + k) = some x := by
      rw [← hX k le_rfl hk2]; exact hx
    have hXn : ∀ w, k + 1 ≤ w → w < 2 * (m * n) →
        s₂.store.read p X (xo.eval + w) = st.store.read p X (xo.eval + w) := by
      intro w hw1 hw2
      rw [hs, Store.read_of_write_eq_some_of_ne hw (dis k w hk2 hw2 (by omega)),
        hX w (by omega) hw2]
    have hYn : ∀ w < k + 1, ∃ x', st.store.read p X (xo.eval + w) = some x' ∧
        s₂.store.read p Y (yo.eval + w) = some (M.mul av x') := by
      intro w hw1
      rcases Nat.lt_or_ge w k with hlt | hge
      · obtain ⟨x', hxa, hyz⟩ := hY w hlt
        refine ⟨x', hxa, ?_⟩
        rw [hs, Store.read_of_write_eq_some_of_ne hw
          (Or.inr (show yo.eval + w ≠ yo.eval + k by omega) : Y ≠ Y ∨ yo.eval + w ≠ yo.eval + k)]
        exact hyz
      · have hwk : w = k := by omega
        subst hwk
        exact ⟨x, hx', by rw [hs, Store.read_of_write_eq_some hw]⟩
    have hav' : s₂.store.read p a.buf a.idx.eval = some av := by
      rw [hs]
      have hne : a.buf ≠ Y ∨ a.idx.eval ≠ yo.eval + k := by
        by_cases hb : a.buf = Y
        · right
          rw [hb] at haY
          simp only [blockDisjoint, bne_self_eq_false, Bool.false_or, decide_eq_true_eq,
            Bool.or_eq_true] at haY
          omega
        · exact Or.inl hb
      rw [Store.read_of_write_eq_some_of_ne hw hne]
      exact hav
    have hout' : ∀ q b i, blockDisjoint (b, i, 1) (Y, yo.eval, 2 * (m * n)) = true →
        s₂.store.read q b i = st.store.read q b i := by
      intro q b i hd
      have hne : b ≠ Y ∨ i ≠ yo.eval + k := by
        by_cases hb : b = Y
        · right
          subst hb
          simp only [blockDisjoint, bne_self_eq_false, Bool.false_or, decide_eq_true_eq,
            Bool.or_eq_true] at hd
          omega
        · exact Or.inl hb
      rw [hs, Store.read_of_write_eq_some_of_ne hw hne]
      exact hout q b i hd
    exact ⟨hYn, hXn, hav', hout', by rw [hs, Store.shape_of_write_eq_some hw, hsh],
      by rw [hp, hpos]⟩
  obtain ⟨hY, hX, hav, hout, hsh, hpos⟩ := inv
  have hbnd : ∀ (i : Fin m) (j : Fin n) (t : Fin 2),
      2 * ((i : ℕ) + m * j) + (t : ℕ) < 2 * (m * n) := by
    intro i j t
    have h1 : (i : ℕ) + m * j < m * n := by
      nlinarith [i.isLt, j.isLt, Nat.mul_le_mul_left m (show (j : ℕ) + 1 ≤ n from j.isLt)]
    have := t.isLt
    omega
  refine ⟨fun i j (t : Fin 2) => ?_, hout⟩
  obtain ⟨x, hxa, hyz⟩ := hY _ (hbnd i j t)
  have hx : x = pairLayout.put (A i j) t := Option.some.inj (hxa.symm.trans (hA i j t))
  rw [hx] at hyz
  convert hyz using 2 <;> fin_cases t <;> simp [pairLayout]

/-- **`zconjTranspose` computes the machine's conjugate transpose**: a successful run of
`NLAlib.Computation.zconjTranspose` from a block at `X` holding the complex $m \times n$ matrix
$\mathbf{A}$, into a block at `Y` disjoint from it, ends with the block at `Y` holding
`M.conjTransposeMat A`, every cell outside it unchanged. No printed source.
Proof: as `NLAlib.Computation.holds_of_exec_zcopy`, two nested loops; the output index
$2(i + nj)$ runs over every entry of the $n \times m$ result once. M, about 45 lines. -/
theorem holds_of_exec_zconjTranspose (p : P) (m n : ℕ) {X Y : ℕ} {xo yo : IExp ℕ}
    {st st' : St P K C} {A : Matrix (Fin m) (Fin n) (K × K)}
    (hA : pairLayout.Holds st.store p X xo.eval A)
    (hXY : blockDisjoint (Y, yo.eval, 2 * (n * m)) (X, xo.eval, 2 * (m * n)) = true)
    (h : exec I (zconjTranspose (ι := ι) p (.const m) (.const n) X xo Y yo).run st = some st') :
    pairLayout.Holds st'.store p Y yo.eval
      ((I.sem.toFloatMachine p toNat mmR qrR unif normal).conjTransposeMat A) ∧
      ∀ q b i, blockDisjoint (b, i, 1) (Y, yo.eval, 2 * (n * m)) = true →
        st'.store.read q b i = st.store.read q b i := by
  sorry

/-- **`ztraceRe` computes the machine's real trace**: a successful run of
`NLAlib.Computation.ztraceRe` from a block at `X` holding the complex $n \times n$ matrix
$\mathbf{A}$, into a cell outside it, ends with the cell holding `M.traceRe A`, every other cell
unchanged. No printed source.
Proof: after the literal $0$, the loop keeps "the cell holds the left fold over the first $i$
diagonal real parts" (`NLAlib.Computation.forall_of_exec_loop_eq_some`, scaffold);
`List.finRange_succ_last`-style `List.foldl_append` matches `NLAlib.FloatMachine.traceRe`. M,
about 30 lines. -/
theorem read_of_exec_ztraceRe (p : P) (n : ℕ) {X : ℕ} {xo : IExp ℕ} {dst : Cell ℕ ℕ}
    {st st' : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)}
    (hA : pairLayout.Holds st.store p X xo.eval A)
    (hdX : blockDisjoint (dst.buf, dst.idx.eval, 1) (X, xo.eval, 2 * (n * n)) = true)
    (h : exec I (ztraceRe (ι := ι) p (.const n) X xo dst).run st = some st') :
    st'.store.read p dst.buf dst.idx.eval =
      some ((I.sem.toFloatMachine p toNat mmR qrR unif normal).traceRe A) ∧
      ∀ q b i, blockDisjoint (b, i, 1) (dst.buf, dst.idx.eval, 1) = true →
        st'.store.read q b i = st.store.read q b i := by
  sorry

end NLAlib.Computation
