/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import Mathlib.Data.Int.Bitwise
import NLAlib.Computation.BLAS
import NLAlib.Computation.Subst

/-!
# The fixed-point example: reducing an arithmetic to word operations

Two tags over one word carrier `ℤ` (D16 (i)): Q16 fixed point (`fx`, value $w/2^{16}$) and
plain integers (`int`). `NLAlibTools.fxSem` is fixed-point arithmetic on words and
`NLAlibTools.wordSem` has integer operations only; `NLAlibTools.fxImpl` implements fixed-point
addition, subtraction, multiplication and negation by reinterpretation, integer operations and a
shift, so that `NLAlib.Computation.Stmt.subst` turns a fixed-point program into a word-level one.
The run of `dot` at `fx` gives the same word at both levels (`docs/design/Computation.md` §7.4),
and so does a run of `sub`, `neg` and a product rounded toward $-\infty$. The `int` tag is
unbounded, so the bit cost is a weighted count, not a certified 64-bit count.

The certificate `NLAlibTools.implementsInstr_fxImpl` (at most four scratch integer cells, 256
bits) and the error bound `NLAlibTools.fxSem_mul_abs_sub_le` are proved. This is a test of the
design, not part of the library.

## Main results

* `NLAlibTools.implementsInstr_fxImpl`: the word-level implementation of fixed point.
* `NLAlibTools.fxSem_mul_abs_sub_le`: the absolute error of the fixed-point product.
-/

-- A tools file: `#eval` and `#guard` are its point.
set_option linter.hashCommand false

open NLAlib NLAlib.Computation

namespace NLAlibTools

/-- Two tags over one word carrier `ℤ`: Q16 fixed point and plain integers. -/
inductive FxTag where
  /-- Q16 fixed point: the word $w$ stands for $w/2^{16}$. -/
  | fx
  /-- Plain integers. -/
  | int
  deriving DecidableEq, Repr

/-- The value of a stored word: `w / 2^16` at `fx`, `w` at `int`. -/
def fxDecode : FxTag → ℤ → ℚ
  | .fx, w => (w : ℚ) / 65536
  | .int, w => w

/-- Integer and bitwise operations on unbounded words; shifts by a nonnegative amount. -/
def intBin (b : BinOp) (x y : ℤ) : Option ℤ :=
  match b with
  | .add => some (x + y) | .sub => some (x - y) | .mul => some (x * y)
  | .shr => if 0 ≤ y then some (Int.fdiv x (2 ^ y.toNat)) else none
  | .shl => if 0 ≤ y then some (x * 2 ^ y.toNat) else none
  | .band => some (Int.land x y) | .bor => some (Int.lor x y) | .bxor => some (Int.xor x y)
  | .div => none

/-- The higher-level semantics: fixed-point arithmetic on words (product truncated toward
`-∞`), integers on `int`. -/
def fxSem : ScalarSem FxTag ℤ where
  lit p q := match p with
    | .fx => some (Int.fdiv (q.num * 65536) q.den)
    | .int => if q.den = 1 then some q.num else none
  bin p b x y := match p, b with
    | .fx, .add => some (x + y) | .fx, .sub => some (x - y)
    | .fx, .mul => some (Int.fdiv (x * y) 65536)
    | .fx, _ => none
    | .int, b => intBin b x y
  un p u x := match p, u with
    | .fx, .conj => some x | .fx, .neg => some (-x) | .int, .neg => some (-x)
    | _, _ => none
  cmp _ c x y := match c with
    | .eq => some (decide (x = y)) | .lt => some (decide (x < y)) | .le => some (decide (x ≤ y))
  convert _ _ x := some x

/-- The word-level semantics: only integer operations; fixed point keeps its literals and
comparisons, and nothing else. -/
def wordSem : ScalarSem FxTag ℤ :=
  { fxSem with
    bin := fun p b x y => match p with | .fx => none | .int => intBin b x y
    un := fun p u x => match p, u with | .int, .neg => some (-x) | _, _ => none }

/-- A fixed-point `add` or `sub` at the word level: both operands reinterpreted as integers, the
integer operation `b`, and the result reinterpreted back. -/
def fxIntBin {ι VB VI : Type} (b : BinOp) (dst x y : Cell VB VI) : Stmt FxTag ι VB VI :=
  Builder.run do
    let t ← Builder.alloc .int 3
    Builder.ins (.convert .fx .int ⟨t, 0⟩ x)
    Builder.ins (.convert .fx .int ⟨t, 1⟩ y)
    Builder.ins (.bin .int b ⟨t, 2⟩ ⟨t, 0⟩ ⟨t, 1⟩)
    Builder.ins (.convert .int .fx dst ⟨t, 2⟩)

/-- **Fixed-point operations implemented by word operations.** `add`, `sub`, `mul` and `neg` at
`fx` become reinterpretations to `int`, integer operations (and a shift for `mul`) and a
reinterpretation back; `conj` (the identity on reals) a copy; everything else is kept. -/
def fxImpl {ι VB VI : Type} : Instr FxTag VB VI → Stmt FxTag ι VB VI
  | .bin .fx .add dst x y => fxIntBin .add dst x y
  | .bin .fx .sub dst x y => fxIntBin .sub dst x y
  | .bin .fx .mul dst x y => Builder.run do
      let t ← Builder.alloc .int 4
      Builder.ins (.convert .fx .int ⟨t, 0⟩ x)
      Builder.ins (.convert .fx .int ⟨t, 1⟩ y)
      Builder.ins (.bin .int .mul ⟨t, 2⟩ ⟨t, 0⟩ ⟨t, 1⟩)
      Builder.ins (.litIdx .int ⟨t, 3⟩ 16)
      Builder.ins (.bin .int .shr ⟨t, 2⟩ ⟨t, 2⟩ ⟨t, 3⟩)
      Builder.ins (.convert .int .fx dst ⟨t, 2⟩)
  | .un .fx .neg dst x => Builder.run do
      let t ← Builder.alloc .int 2
      Builder.ins (.convert .fx .int ⟨t, 0⟩ x)
      Builder.ins (.un .int .neg ⟨t, 1⟩ ⟨t, 0⟩)
      Builder.ins (.convert .int .fx dst ⟨t, 1⟩)
  | .un .fx .conj dst x => .instr (.copy .fx dst x)
  | i => .instr i

/-- Counts for the demonstration: (fixed-point operations, integer operations, conversions,
bit cost with 64-bit words: `64` per add, subtraction, negation, shift and bitwise operation, `64²`
per multiply). -/
def fxCharge : OpKind FxTag Unit → ℕ × ℕ × ℕ × ℕ
  | .bin .fx _ => (1, 0, 0, 0) | .un .fx _ => (1, 0, 0, 0)
  | .bin .int .mul => (0, 1, 0, 4096) | .bin .int _ => (0, 1, 0, 64)
  | .un .int _ => (0, 1, 0, 64)
  | .convert _ _ => (0, 0, 1, 0)
  | _ => (0, 0, 0, 0)

/-- The interpretation of the example: no oracles, no tape, 64-bit cells. -/
def fxInterp (sem : ScalarSem FxTag ℤ) : Interp FxTag Unit ℤ (ℕ × ℕ × ℕ × ℕ) where
  sem := sem
  charge := fxCharge
  tape _ _ := 0
  oracle _ _ _ := none
  height _ := 0
  rom _ := none
  romSize _ := 0
  width _ := 64

/-- The initial state of the example, memory counted from zero. -/
def fxState (bufs : List (FxTag × Array (Option ℤ))) : St FxTag ℤ (ℕ × ℕ × ℕ × ℕ) where
  store := bufs.toArray
  pos _ := 0
  cnt := 0
  cur _ := 0
  peak _ := 0
  curW := 0
  peakW := 0

/-- `x = (1.5, −2.25, 0.5)`, `y = (2, 0.75, −4)` in Q16; `xᵀy = −0.6875`. -/
def fxBufs : List (FxTag × Array (Option ℤ)) :=
  [(.fx, #[some 98304, some (-147456), some 32768]), (.fx, #[some 131072, some 49152,
    some (-262144)]), (.fx, #[none])]

/-- `dot` of the two vectors at `fx`, into buffer 2. -/
def fxDot : Stmt FxTag Unit ℕ ℕ :=
  (dot .fx ⟨2, .const 0⟩ 0 (.const 0) 1 (.const 0) (.const 3)).run

/-- The two runs: the fixed-point program and its word-level substitution, with the output word,
the counts and the bit peak. -/
def fxRuns :
    Option ((Option ℤ × (ℕ × ℕ × ℕ × ℕ) × ℕ) × (Option ℤ × (ℕ × ℕ × ℕ × ℕ) × ℕ)) := do
  let a ← exec (fxInterp fxSem) fxDot (fxState fxBufs)
  let w ← exec (fxInterp wordSem) (fxDot.subst fxImpl fun _ _ _ _ _ _ _ => .skip)
    (fxState fxBufs)
  some ((a.store.read .fx 2 0, a.cnt, a.peakW), (w.store.read .fx 2 0, w.cnt, w.peakW))

#eval fxRuns

-- The same word, `-0.6875 = -45056 / 2^16`, at both levels (§7.4).
#guard fxRuns == some ((some (-45056), (9, 0, 0, 0), 64), (some (-45056), (0, 9, 18, 12672), 320))

/-- `x = (1.5, −2⁻¹⁶)`, `y = (−2.25, 2⁻¹⁶)` in Q16, and three output cells. -/
def fxOpsBufs : List (FxTag × Array (Option ℤ)) :=
  [(.fx, #[some 98304, some (-1)]), (.fx, #[some (-147456), some 1]), (.fx, #[none, none, none])]

/-- `x₀ − y₀`, `−x₀` and `x₁ y₁` into buffer 2, then `x₀ ← −x₀` in place. -/
def fxOps : Stmt FxTag Unit ℕ ℕ :=
  .seq (.instr (.bin .fx .sub ⟨2, 0⟩ ⟨0, 0⟩ ⟨1, 0⟩)) <|
    .seq (.instr (.un .fx .neg ⟨2, 1⟩ ⟨0, 0⟩)) <|
      .seq (.instr (.bin .fx .mul ⟨2, 2⟩ ⟨0, 1⟩ ⟨1, 1⟩)) <|
        .instr (.un .fx .neg ⟨0, 0⟩ ⟨0, 0⟩)

/-- The two runs of `fxOps`: the four written words, the counts and the bit peak. -/
def fxOpsRuns : Option ((List (Option ℤ) × (ℕ × ℕ × ℕ × ℕ) × ℕ) ×
    (List (Option ℤ) × (ℕ × ℕ × ℕ × ℕ) × ℕ)) := do
  let out (st : St FxTag ℤ (ℕ × ℕ × ℕ × ℕ)) := [st.store.read .fx 2 0, st.store.read .fx 2 1,
    st.store.read .fx 2 2, st.store.read .fx 0 0]
  let a ← exec (fxInterp fxSem) fxOps (fxState fxOpsBufs)
  let w ← exec (fxInterp wordSem) (fxOps.subst fxImpl fun _ _ _ _ _ _ _ => .skip)
    (fxState fxOpsBufs)
  some ((out a, a.cnt, a.peakW), (out w, w.cnt, w.peakW))

#eval fxOpsRuns

-- The same words at both levels: `3.75`, `−1.5`, the product `−2⁻³²` truncated toward `−∞` to
-- `−2⁻¹⁶` (word `−1`, not `0`), and `x₀` negated in place to `−1.5`; 256 scratch bits.
#guard fxOpsRuns == some (([some 245760, some (-98304), some (-1), some (-98304)], (4, 0, 0, 0), 0),
  ([some 245760, some (-98304), some (-1), some (-98304)], (0, 5, 10, 4352), 256))

/-- The cost of each fixed-point kind at the word level. -/
noncomputable def fxCost : OpKind FxTag Unit → OpCount FxTag Unit
  | .bin .fx .add => Finsupp.single (.convert .fx .int) 2 + Finsupp.single (.bin .int .add) 1 +
      Finsupp.single (.convert .int .fx) 1
  | .bin .fx .sub => Finsupp.single (.convert .fx .int) 2 + Finsupp.single (.bin .int .sub) 1 +
      Finsupp.single (.convert .int .fx) 1
  | .bin .fx .mul => Finsupp.single (.convert .fx .int) 2 + Finsupp.single (.bin .int .mul) 1 +
      Finsupp.single (.lit .int) 1 + Finsupp.single (.bin .int .shr) 1 +
      Finsupp.single (.convert .int .fx) 1
  | .un .fx .neg => Finsupp.single (.convert .fx .int) 1 + Finsupp.single (.un .int .neg) 1 +
      Finsupp.single (.convert .int .fx) 1
  | .un .fx .conj => Finsupp.single (.copy .fx) 1
  | k => Finsupp.single k 1

/-- The conclusion of the certificate `NLAlib.Computation.ImplementsInstr` at one instruction:
the statement `S` run from `st` under `I'` ends with the store and tape positions `r`, at most the
count `c` more, and at most four scratch integer cells (256 bits). -/
private def FxStep (I' : Interp FxTag Unit ℤ (OpCount FxTag Unit)) (S : Stmt FxTag Unit ℕ ℕ)
    (st : St FxTag ℤ (OpCount FxTag Unit)) (r : Store FxTag ℤ × (Dist → ℕ))
    (c : OpCount FxTag Unit) : Prop :=
  ∃ st', exec I' S st = some st' ∧ st'.store = r.1 ∧ st'.pos = r.2 ∧ st'.cur = st.cur ∧
    st'.curW = st.curW ∧ st'.cnt ≤ st.cnt + c ∧
    (∀ q, st'.peak q ≤ max (st.peak q) (st.cur q + if q = .int then 4 else 0)) ∧
    st'.peakW ≤ max st.peakW (st.curW + 256)

variable {I' : Interp FxTag Unit ℤ (OpCount FxTag Unit)} {st : St FxTag ℤ (OpCount FxTag Unit)}

/-- A kept instruction: one step, at the cost of its kind, whenever it runs under `wordSem`. -/
private theorem fxStep_instr (hI' : I'.sem = wordSem) (hc' : ∀ k, I'.charge k = Finsupp.single k 1)
    {tape : Dist → ℕ → ℤ} (htape : I'.tape = tape) {i : Instr FxTag ℕ ℕ}
    {r : Store FxTag ℤ × (Dist → ℕ)} (hr : i.run wordSem tape st.store st.pos = some r) :
    FxStep I' (.instr i) st r (Finsupp.single i.kind 1) :=
  ⟨{ st with store := r.1, pos := r.2, cnt := st.cnt + I'.charge i.kind },
    by rw [exec_instr, hI', htape, hr, Option.map_some], rfl, rfl, rfl, rfl, (by rw [hc']),
    fun _ => le_max_left _ _, le_max_left _ _⟩

/-- `fxIntBin` unfolded: the scratch buffer and the four instructions. -/
private theorem fxIntBin_eq {ι : Type} (b : BinOp) (dst x y : Cell ℕ ℕ) :
    (fxIntBin b dst x y : Stmt FxTag ι ℕ ℕ) = .alloc .int 3 fun t =>
      .seq (.instr (.convert .fx .int ⟨t, 0⟩ x)) <| .seq (.instr (.convert .fx .int ⟨t, 1⟩ y)) <|
        .seq (.instr (.bin .int b ⟨t, 2⟩ ⟨t, 0⟩ ⟨t, 1⟩)) <|
          .seq (.instr (.convert .int .fx dst ⟨t, 2⟩)) .skip := rfl

/-- `fxIntBin b` computes the integer operation `b` of the two words into `dst`. The reads come
before the write, so `dst` may be `x` or `y`. -/
private theorem fxStep_fxIntBin (hI' : I'.sem = wordSem)
    (hc' : ∀ k, I'.charge k = Finsupp.single k 1) (hw : I'.width = fun _ => 64) {b : BinOp}
    {dst x y : Cell ℕ ℕ} {a c v : ℤ} {s' : Store FxTag ℤ}
    (hx : st.store.read .fx x.buf x.idx.eval = some a)
    (hy : st.store.read .fx y.buf y.idx.eval = some c) (hv : intBin b a c = some v)
    (hd : st.store.write .fx dst.buf dst.idx.eval v = some s') :
    FxStep I' (fxIntBin b dst x y) st (s', st.pos)
      (Finsupp.single (.convert .fx .int) 2 + Finsupp.single (.bin .int b) 1 +
        Finsupp.single (.convert .int .fx) 1) := by
  have hxl := Store.lt_size_of_read_eq_some hx
  have hyl := Store.lt_size_of_read_eq_some hy
  have hdl := Store.lt_size_of_write_eq_some hd
  rw [FxStep, fxIntBin_eq]
  simp only [exec, IExp.eval_ofNat, hw, Nat.reduceMul, Instr.kind, hc', Instr.run,
    Store.read_push_of_lt hxl, hx, hI', wordSem, fxSem, Array.size_replicate, Nat.ofNat_pos,
    Store.write_push_size, Array.set!_eq_setIfInBounds, Option.map_some, Option.bind_some,
    Option.map_bind, Function.comp_apply, Option.map_map, Option.bind_fun_some,
    Store.read_push_of_lt hyl, hy, Array.size_setIfInBounds, Nat.one_lt_ofNat, Store.read_push_size,
    ↓reduceIte, getElem?_pos, ne_eq, one_ne_zero, not_false_eq_true, Array.getElem_setIfInBounds_ne,
    Array.getElem_setIfInBounds_self, Option.join_some, Nat.lt_add_one, hv,
    Store.write_push_of_lt hdl, hd, Array.pop_push, Function.update_self, add_tsub_cancel_right,
    Function.update_idem, Function.update_eq_self, Option.some.injEq, le_sup_iff, exists_eq_left',
    sup_le_iff, Std.le_refl, true_and, add_le_add_iff_left, Nat.reduceLeDiff, and_true]
  refine ⟨le_of_eq ?_, fun q => ?_, by omega⟩
  · rw [show (2 : ℕ) = 1 + 1 from rfl, Finsupp.single_add]
    abel
  · cases q <;> simp only [Function.update_self, Function.update_of_ne, ne_eq, reduceCtorEq,
      not_false_eq_true, ↓reduceIte, add_zero] <;> omega

/-- The `mul` case of `fxImpl` unfolded. -/
private theorem fxImpl_mul_eq {ι : Type} (dst x y : Cell ℕ ℕ) :
    (fxImpl (.bin .fx .mul dst x y) : Stmt FxTag ι ℕ ℕ) = .alloc .int 4 fun t =>
      .seq (.instr (.convert .fx .int ⟨t, 0⟩ x)) <| .seq (.instr (.convert .fx .int ⟨t, 1⟩ y)) <|
        .seq (.instr (.bin .int .mul ⟨t, 2⟩ ⟨t, 0⟩ ⟨t, 1⟩)) <|
          .seq (.instr (.litIdx .int ⟨t, 3⟩ 16)) <|
            .seq (.instr (.bin .int .shr ⟨t, 2⟩ ⟨t, 2⟩ ⟨t, 3⟩)) <|
              .seq (.instr (.convert .int .fx dst ⟨t, 2⟩)) .skip := rfl

/-- The `mul` case of `fxImpl`: the integer product shifted right by 16 is the fixed-point
product, truncated toward $-\infty$. -/
private theorem fxStep_mul (hI' : I'.sem = wordSem)
    (hc' : ∀ k, I'.charge k = Finsupp.single k 1) (hw : I'.width = fun _ => 64)
    {dst x y : Cell ℕ ℕ} {a c : ℤ} {s' : Store FxTag ℤ}
    (hx : st.store.read .fx x.buf x.idx.eval = some a)
    (hy : st.store.read .fx y.buf y.idx.eval = some c)
    (hd : st.store.write .fx dst.buf dst.idx.eval (Int.fdiv (a * c) 65536) = some s') :
    FxStep I' (fxImpl (.bin .fx .mul dst x y)) st (s', st.pos) (fxCost (.bin .fx .mul)) := by
  have hxl := Store.lt_size_of_read_eq_some hx
  have hyl := Store.lt_size_of_read_eq_some hy
  have hdl := Store.lt_size_of_write_eq_some hd
  rw [FxStep, fxImpl_mul_eq]
  simp only [exec, IExp.eval_ofNat, hw, Nat.reduceMul, Instr.kind, hc', Instr.run,
    Store.read_push_of_lt hxl, hx, hI', wordSem, fxSem, intBin, Array.size_replicate,
    Nat.ofNat_pos, Store.write_push_size, Array.set!_eq_setIfInBounds, Option.map_some,
    Option.bind_some, Option.map_bind, Function.comp_apply, Option.map_map, Nat.cast_ofNat,
    Rat.den_ofNat, ↓reduceIte, Rat.num_ofNat, Option.bind_fun_some, Store.read_push_of_lt hyl, hy,
    Array.size_setIfInBounds, Nat.one_lt_ofNat, Store.read_push_size, getElem?_pos, ne_eq,
    one_ne_zero, not_false_eq_true, Array.getElem_setIfInBounds_ne,
    Array.getElem_setIfInBounds_self, Option.join_some, Nat.reduceLT, Nat.lt_add_one,
    Nat.succ_ne_self, Nat.ofNat_nonneg, Int.reduceToNat, Int.reducePow, Store.write_push_of_lt hdl,
    hd, Array.pop_push, Function.update_self, add_tsub_cancel_right, Function.update_idem,
    Function.update_eq_self, Option.some.injEq, fxCost, le_sup_iff, exists_eq_left', sup_le_iff,
    Std.le_refl, true_and, and_true]
  refine ⟨le_of_eq ?_, fun q => ?_, by omega⟩
  · rw [show (2 : ℕ) = 1 + 1 from rfl, Finsupp.single_add]
    abel
  · cases q <;> simp only [Function.update_self, Function.update_of_ne, ne_eq, reduceCtorEq,
      not_false_eq_true, ↓reduceIte, add_zero] <;> omega

/-- The `neg` case of `fxImpl` unfolded. -/
private theorem fxImpl_neg_eq {ι : Type} (dst x : Cell ℕ ℕ) :
    (fxImpl (.un .fx .neg dst x) : Stmt FxTag ι ℕ ℕ) = .alloc .int 2 fun t =>
      .seq (.instr (.convert .fx .int ⟨t, 0⟩ x)) <| .seq (.instr (.un .int .neg ⟨t, 1⟩ ⟨t, 0⟩)) <|
        .seq (.instr (.convert .int .fx dst ⟨t, 1⟩)) .skip := rfl

/-- The `neg` case of `fxImpl`: the integer negation of the word. -/
private theorem fxStep_neg (hI' : I'.sem = wordSem)
    (hc' : ∀ k, I'.charge k = Finsupp.single k 1) (hw : I'.width = fun _ => 64)
    {dst x : Cell ℕ ℕ} {a : ℤ} {s' : Store FxTag ℤ}
    (hx : st.store.read .fx x.buf x.idx.eval = some a)
    (hd : st.store.write .fx dst.buf dst.idx.eval (-a) = some s') :
    FxStep I' (fxImpl (.un .fx .neg dst x)) st (s', st.pos) (fxCost (.un .fx .neg)) := by
  have hxl := Store.lt_size_of_read_eq_some hx
  have hdl := Store.lt_size_of_write_eq_some hd
  rw [FxStep, fxImpl_neg_eq]
  simp only [exec, IExp.eval_ofNat, hw, Nat.reduceMul, Instr.kind, hc', Instr.run,
    Store.read_push_of_lt hxl, hx, hI', wordSem, fxSem, Array.size_replicate, Order.lt_two_iff,
    zero_le, Store.write_push_size, Array.set!_eq_setIfInBounds, Option.map_some, Option.bind_some,
    Option.map_bind, Function.comp_apply, Option.map_map, Option.bind_fun_some,
    Store.read_push_size, ↓reduceIte, Array.size_setIfInBounds, getElem?_pos,
    Array.getElem_setIfInBounds_self, Option.join_some, Std.le_refl, Store.write_push_of_lt hdl, hd,
    Array.pop_push, Function.update_self, add_tsub_cancel_right, Function.update_idem,
    Function.update_eq_self, Option.some.injEq, fxCost, le_sup_iff, exists_eq_left', sup_le_iff,
    true_and, add_le_add_iff_left, Nat.reduceLeDiff, and_true]
  refine ⟨le_of_eq ?_, fun q => ?_, by omega⟩
  · abel
  · cases q <;> simp only [Function.update_self, Function.update_of_ne, ne_eq, reduceCtorEq,
      not_false_eq_true, ↓reduceIte, add_zero] <;> omega

/-- **The word-level implementation implements the fixed-point semantics**, at most four scratch
integer cells (256 bits). -/
theorem implementsInstr_fxImpl (I I' : Interp FxTag Unit ℤ (OpCount FxTag Unit))
    (hI : I.sem = fxSem) (hI' : I'.sem = wordSem) (hc' : ∀ k, I'.charge k = Finsupp.single k 1)
    (htape : I'.tape = I.tape) (hw : I'.width = fun _ => 64) :
    ImplementsInstr I I' fxImpl fxCost (fun q => if q = .int then 4 else 0) 256 := by
  intro i st r hr
  rw [hI] at hr
  change FxStep I' (fxImpl i) st r (fxCost i.kind)
  rcases i with _ | _ | ⟨_ | _, _ | _ | _ | _ | _ | _ | _ | _ | _, dst, x, y⟩ |
    ⟨_ | _, _ | _ | _ | _ | _, dst, x⟩ | _ | _ | _
  all_goals try exact fxStep_instr hI' hc' htape hr
  all_goals simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
  · obtain ⟨a, hx, c, hy, v, hv, s', hd, rfl⟩ := hr
    exact fxStep_fxIntBin hI' hc' hw hx hy hv hd
  · obtain ⟨a, hx, c, hy, v, hv, s', hd, rfl⟩ := hr
    exact fxStep_fxIntBin hI' hc' hw hx hy hv hd
  · obtain ⟨a, hx, c, hy, v, hv, s', hd, rfl⟩ := hr
    cases Option.some.inj hv
    exact fxStep_mul hI' hc' hw hx hy hd
  · obtain ⟨a, hx, v, hv, s', hd, rfl⟩ := hr
    cases Option.some.inj hv
    exact fxStep_neg hI' hc' hw hx hd

/-- The fixed-point product meets an absolute-error contract: `|ẑ − x̂ŷ| ≤ 2⁻¹⁶`. -/
theorem fxSem_mul_abs_sub_le {x y z : ℤ} (h : fxSem.bin .fx .mul x y = some z) :
    |fxDecode .fx z - fxDecode .fx x * fxDecode .fx y| ≤ 1 / 65536 := by
  have hz : Int.fdiv (x * y) 65536 = z := Option.some.inj h
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by norm_num)] at hz
  have h1 := Int.mul_ediv_add_emod (x * y) 65536
  have h2 := Int.emod_nonneg (x * y) (b := 65536) (by norm_num)
  have h3 := Int.emod_lt_of_pos (x * y) (b := 65536) (by norm_num)
  rw [hz] at h1
  have h1' : 65536 * (z : ℚ) + ((x * y % 65536 : ℤ) : ℚ) = x * y := by exact_mod_cast h1
  have h2' : (0 : ℚ) ≤ ((x * y % 65536 : ℤ) : ℚ) := by exact_mod_cast h2
  have h3' : ((x * y % 65536 : ℤ) : ℚ) < 65536 := by exact_mod_cast h3
  simp only [fxDecode]
  rw [abs_le]
  constructor <;> nlinarith


end NLAlibTools
