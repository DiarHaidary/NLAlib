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
  sorry

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
  sorry

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
