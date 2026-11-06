/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.KernelCall
public import NLAlib.Computation.StaticCost
public import NLAlib.Matrix.Computation.Deflation
public import NLAlib.Matrix.Computation.DeflationProgramTree
public import NLAlibScaffold.Computation.Exec
public import NLAlibScaffold.Matrix.Computation.KernelContracts
public import NLAlibScaffold.Matrix.Computation.PairKernels

/-!
# The deflation program computes `deflate` (scaffold)

Statements for a new file `NLAlib/Matrix/Computation/DeflationProgram.lean` (stage COMPDYN S1d,
design note `docs/design/Computation-SignDeflatePrograms.md`, §4): the refinement of the program
`NLAlib.deflateProg` to the shallow `NLAlib.deflate`. Under any interpretation whose kernels `mm`
and `qr` are routines on interleaved pairs, **every successful run computes exactly
`NLAlib.deflate` on the machine of the semantics, the routines and the tape**
(`NLAlib.Computation.ScalarSem.toFloatMachine` with the normal sampler
`NLAlib.Computation.ScalarSem.tapeNormal` of the stored Gaussian tape from the run's tape
position, and the sample matrix `NLAlib.Computation.tapeIndexMatrix` of the positions); under the
standard model with every value in range and exact literals up to $2$ the run always succeeds;
for a tape rounding independent of the position, the same output is `NLAlib.deflate` on the
machine with the sampler `NLAlib.Computation.ScalarSem.gaussianNormal` and the ideal complex
Gaussian sample `NLAlib.Computation.tapeComplexMatrix`. The counts are
`NLAlib.deflateCount`.

## Main results

* `NLAlib.holds_of_exec_forRange_drawMul`: the drawn test matrix.
* `NLAlib.holds_of_exec_deflateProg`, `NLAlib.exists_exec_deflateProg`: the refinement (partial
  equality, success) for the builder from any state.
* `NLAlib.deflate_tapeNormal_eq_deflate_gaussianNormal`: the tape sampler as a sampler of ideal
  complex Gaussians.
* `NLAlib.deflateProg.toStmt_compiled`, `NLAlib.deflateProg.holds_of_exec_compiled`,
  `NLAlib.deflateProg.exists_exec_compiled`, `NLAlib.deflateProg.cnt_le_of_exec_compiled`: the
  registered tree.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {Su : Type} {toNat : K → ℕ} {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}
  {unif : K → Su → K}

/-- **The draw loop stores the tape sampler's matrix**: a successful run of the draw loop of
`NLAlib.deflateProg` (each of the $2n^2$ words of the block at `G` a Gaussian draw times the
stored $\sqrt{1/2}$ in the cell `s`, outside `G`) ends with the block at `G` holding the
$n \times n$ matrix whose entry $k = i + nj$ is sample $k$ of
`NLAlib.Computation.ScalarSem.tapeNormal` on the tape of Gaussian draws from the current
position, the Gaussian position advanced by $2n^2$, and every cell outside the block unchanged.
No printed source.
Proof: `NLAlib.Computation.forall_of_exec_loop_eq_some` (scaffold) with the invariant "words
below $w$ hold the products, the Gaussian position is advanced by $w$"; each step
`NLAlib.Computation.exec_seq_instr_draw` then `NLAlib.Computation.exec_seq_instr_bin` (the
product read off its successful run, `Option.getD_some`); then
`NLAlib.Computation.pairLayout.holds_iff` (scaffold), word $2(i + nj)$ at position
$2(i + nj)$, `NLAlib.Computation.tapeIndexMatrix`. M, about 50 lines. -/
theorem holds_of_exec_forRange_drawMul (p : P) (n : ℕ) {G : ℕ} {s : Cell ℕ ℕ}
    {st st' : St P K C} (hs : st.store.read p s.buf s.idx.eval = some (I.sem.sqrtHalf p))
    (hsG : s.buf ≠ G)
    (h : exec I (forRange (ι := ι) (2 * (.const n * .const n)) fun w => do
      ins (.draw p .gaussian ⟨G, .var w⟩)
      ins (.bin p .mul ⟨G, .var w⟩ ⟨G, .var w⟩ s)).run st = some st') :
    pairLayout.Holds st'.store p G 0 ((tapeIndexMatrix n).map
        (I.sem.tapeNormal p fun i => I.tape .gaussian (st.pos .gaussian + i))) ∧
      st'.pos = Function.update st.pos .gaussian (st.pos .gaussian + 2 * (n * n)) ∧
      (∀ q b i, b ≠ G → st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape := by
  have key : (forRange (ι := ι) (2 * (IExp.const n * IExp.const n)) fun w => do
      ins (.draw p .gaussian ⟨G, .var w⟩)
      ins (.bin p .mul ⟨G, .var w⟩ ⟨G, .var w⟩ s)).run = .seq
      (.loop (2 * (IExp.const n * IExp.const n)) fun w => .seq
        (.instr (.draw p .gaussian ⟨G, .var w⟩)) (.seq
          (.instr (.bin p .mul ⟨G, .var w⟩ ⟨G, .var w⟩ s)) .skip)) .skip := rfl
  rw [key, exec_seq_skip] at h
  -- one word: the draw, then the product with $\sqrt{1/2}$
  have bstep : ∀ (k : ℕ) (t₁ t₂ : St P K C), t₁.store.read p s.buf s.idx.eval =
      some (I.sem.sqrtHalf p) →
      exec I (.seq (.instr (.draw p .gaussian ⟨G, IExp.var k⟩)) (.seq
        (.instr (.bin p .mul ⟨G, IExp.var k⟩ ⟨G, IExp.var k⟩ s)) .skip)) t₁ = some t₂ →
      ∃ (s' s'' : Store P K) (v : K), t₁.store.write p G k (I.tape .gaussian (t₁.pos .gaussian)) =
          some s' ∧
        I.sem.bin p .mul (I.tape .gaussian (t₁.pos .gaussian)) (I.sem.sqrtHalf p) = some v ∧
        s'.write p G k v = some s'' ∧ t₂.store = s'' ∧
        t₂.pos = Function.update t₁.pos .gaussian (t₁.pos .gaussian + 1) := by
    intro k t₁ t₂ hsc hr
    obtain ⟨s', hw⟩ : ∃ s', t₁.store.write p G k (I.tape .gaussian (t₁.pos .gaussian)) = some s' := by
      cases hw : t₁.store.write p G k (I.tape .gaussian (t₁.pos .gaussian)) with
      | none => simp [exec_seq, exec_instr, Instr.run, hw, IExp.eval] at hr
      | some s' => exact ⟨s', rfl⟩
    have hsc' : s'.read p s.buf s.idx.eval = some (I.sem.sqrtHalf p) := by
      rw [Store.read_of_write_eq_some_of_ne hw (Or.inl hsG)]; exact hsc
    obtain ⟨v, hv⟩ : ∃ v, I.sem.bin p .mul (I.tape .gaussian (t₁.pos .gaussian))
        (I.sem.sqrtHalf p) = some v := by
      cases hb : I.sem.bin p .mul (I.tape .gaussian (t₁.pos .gaussian)) (I.sem.sqrtHalf p) with
      | none => simp [exec_seq, exec_instr, Instr.run, hw, hsc', hb, IExp.eval,
          Store.read_of_write_eq_some hw] at hr
      | some v => exact ⟨v, rfl⟩
    obtain ⟨s'', hw2⟩ : ∃ s'', s'.write p G k v = some s'' := by
      cases hw2 : s'.write p G k v with
      | none => simp [exec_seq, exec_instr, Instr.run, hw, hsc', hv, hw2, IExp.eval,
          Store.read_of_write_eq_some hw] at hr
      | some s'' => exact ⟨s'', rfl⟩
    rw [exec_seq_instr_draw (dst := (⟨G, IExp.var k⟩ : Cell ℕ ℕ)) I hw,
      exec_seq_instr_bin (dst := (⟨G, IExp.var k⟩ : Cell ℕ ℕ)) (x := (⟨G, IExp.var k⟩ : Cell ℕ ℕ))
        (y := s) I (Store.read_of_write_eq_some hw) hsc' hv hw2, exec_skip] at hr
    cases hr
    exact ⟨s', s'', v, hw, hv, hw2, rfl, rfl⟩
  -- the loop keeps the drawn products below $k$, the other cells, the shape and the position
  have inv := forall_of_exec_loop_eq_some (I := I) (fun k t =>
      (∀ w < k, t.store.read p G w = some ((I.sem.bin p .mul
        (I.tape .gaussian (st.pos .gaussian + w)) (I.sem.sqrtHalf p)).getD default)) ∧
      (∀ q b i, b ≠ G → t.store.read q b i = st.store.read q b i) ∧
      t.store.shape = st.store.shape ∧
      t.pos = Function.update st.pos .gaussian (st.pos .gaussian + k)) ?_ ?_ h
  rotate_left
  · refine ⟨fun w hw => absurd hw (Nat.not_lt_zero _), fun q b i _ => rfl, rfl, ?_⟩
    simp
  · intro k hk t₁ t₂ ⟨hW, hOUT, hsh, hpos⟩ hr
    have hsc : t₁.store.read p s.buf s.idx.eval = some (I.sem.sqrtHalf p) := by
      rw [hOUT p s.buf s.idx.eval hsG]; exact hs
    have hpk : t₁.pos .gaussian = st.pos .gaussian + k := by rw [hpos]; simp
    obtain ⟨s', s'', v, hw, hv, hw2, hs2, hp2⟩ := bstep k t₁ t₂ hsc hr
    refine ⟨fun w hw' => ?_, fun q b i hb => ?_, ?_, ?_⟩
    · rcases Nat.lt_or_ge w k with hlt | hge
      · rw [hs2, Store.read_of_write_eq_some_of_ne hw2 (Or.inr (show w ≠ k by omega)),
          Store.read_of_write_eq_some_of_ne hw (Or.inr (show w ≠ k by omega))]
        exact hW w hlt
      · have hwk : w = k := by omega
        subst hwk
        rw [hpk] at hv
        rw [hs2, Store.read_of_write_eq_some hw2]
        simp [hv]
    · rw [hs2, Store.read_of_write_eq_some_of_ne hw2 (Or.inl hb),
        Store.read_of_write_eq_some_of_ne hw (Or.inl hb), hOUT q b i hb]
    · rw [hs2, Store.shape_of_write_eq_some hw2, Store.shape_of_write_eq_some hw, hsh]
    · rw [hp2, hpos]
      simp [Function.update_idem, add_assoc]
  obtain ⟨hW, hOUT, hsh, hpos⟩ := inv
  refine ⟨fun i j (t : Fin 2) => ?_, hpos, fun q b i hb => hOUT q b i hb, hsh⟩
  have hij : (i : ℕ) + n * (j : ℕ) < n * n := by
    have e := Nat.mul_le_mul_left n (show (j : ℕ) + 1 ≤ n from j.isLt)
    rw [Nat.mul_add, Nat.mul_one] at e
    have := i.isLt
    omega
  have hn2 : (2 * (IExp.const n * IExp.const n)).eval = 2 * (n * n) := rfl
  have hw := hW (2 * ((i : ℕ) + n * (j : ℕ)) + t) (by have := t.isLt; omega)
  fin_cases t
  · simpa [pairLayout, tapeIndexMatrix, ScalarSem.tapeNormal, Matrix.map_apply,
      Matrix.of_apply] using hw
  · simpa [pairLayout, tapeIndexMatrix, ScalarSem.tapeNormal, Matrix.map_apply,
      Matrix.of_apply] using hw

/-- **The refinement of the deflation program, partial equality**: if kernels `mm` and `qr` of
`I` are the routines `mmR` and `qrR` on interleaved pairs, a successful run of
`NLAlib.deflateProg` at size $n$ and rank $r$, from a state whose block at `Pm` holds the stored
$n \times n$ matrix $\mathbf{P}$, with the output block at `Q` of $2nr$ words disjoint from it,
ends with the output block holding
$$\mathsf{deflate}(\mathbf{P}, r)$$
computed by `NLAlib.deflate` on the machine `M` of the semantics at `p` with product `mmR`, QR
`qrR` and the tape sampler `NLAlib.Computation.ScalarSem.tapeNormal` of the Gaussian tape from the
run's position (for every choice of the machine's other black boxes), with the sample
`NLAlib.Computation.tapeIndexMatrix n`; every cell outside the output block is unchanged, the
store shape too, and the Gaussian position is advanced by $2n^2$. No printed source.
Proof: unfold `NLAlib.deflateProg`; the `scope` and five `NLAlib.Computation.exec_alloc`s push
the scratch buffers at fresh handles; the four instructions leave
`NLAlib.Computation.ScalarSem.sqrtHalf` in cell $0$ (each value read off its successful run);
`NLAlib.holds_of_exec_forRange_drawMul` gives $\widetilde{\mathbf{G}}$, the positions mapped by
the machine's normal sampler;
`NLAlib.Computation.IsMatMulKernel.holds_of_kcallStore_eq_some` and
`NLAlib.Computation.IsQRKernel.holds_of_kcallStore_eq_some` (scaffold, with
`NLAlib.Computation.pairLayout.get_put`) give the product and the factors;
`NLAlib.Computation.holds_of_exec_zcopy` the first $\min(r, n)$ columns of $\mathbf{Q}$
(a column-major block prefix: `Nat.sub_sub_self`, `min_def`) and
`NLAlib.Computation.holds_of_exec_zzero` the zero columns; unfold `NLAlib.deflate` and split on
$j < n$; the pops keep the output block. M, about 80 lines (split the set-up into a private
lemma). -/
theorem holds_of_exec_deflateProg {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) (p : P) (n r : ℕ) {Pm Q : ℕ} {po qo : IExp ℕ}
    {st st' : St P K C} {P₀ : Matrix (Fin n) (Fin n) (K × K)}
    (hP : pairLayout.Holds st.store p Pm po.eval P₀)
    (hQP : blockDisjoint (Q, qo.eval, 2 * (n * r)) (Pm, po.eval, 2 * (n * n)) = true)
    (h : exec I (deflateProg p mm qr (.const n) (.const r) Pm po Q qo).run st = some st') :
    pairLayout.Holds st'.store p Q qo.eval
        (deflate (I.sem.toFloatMachine p toNat mmR qrR unif
          (I.sem.tapeNormal p fun i => I.tape .gaussian (st.pos .gaussian + i))) r P₀
          (tapeIndexMatrix n)) ∧
      (∀ q b i, blockDisjoint (b, i, 1) (Q, qo.eval, 2 * (n * r)) = true →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧
      st'.pos = Function.update st.pos .gaussian (st.pos .gaussian + 2 * (n * n)) := by
  sorry

/-- **The refinement of the deflation program, success**: under the standard model at $u$ with
every value in range, $u(p) \le 1$ and exact literals up to $2$, if kernels `mm` and `qr` of `I`
are routines on interleaved pairs, the input block at `Pm` holds a stored matrix and the output
block at `Q` (tag `p`, $2nr$ words, disjoint from it) exists, the run of `NLAlib.deflateProg`
succeeds. No printed source.
Proof: the literals by `lit_ok`; the literal $2$ decodes to $2$ (`hlit`), so the division
succeeds (`bin_ok`) and decodes to $\tfrac12(1 + \delta)$, $\lvert\delta\rvert \le 1$, which is
nonnegative, so the square root succeeds (`sqrt_ok`); the draws always succeed
(`NLAlib.Computation.exec_seq_instr_draw`, the scratch buffer has $2n^2$ cells), the products by
`bin_ok`; the kernel calls by `NLAlib.Computation.IsMatMulKernel.kcallStore_eq` and
`NLAlib.Computation.IsQRKernel.kcallStore_eq` (fresh, disjoint scratch buffers); then
`NLAlib.Computation.exists_exec_zcopy` and `NLAlib.Computation.exists_exec_zzero`. M, about 60
lines. -/
theorem exists_exec_deflateProg {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hlit : IsExactIntLit dec I.sem 2) (p : P)
    (hu : u p ≤ 1) (n r : ℕ) {Pm Q : ℕ} {po qo : IExp ℕ} {st : St P K C}
    {P₀ : Matrix (Fin n) (Fin n) (K × K)} (hP : pairLayout.Holds st.store p Pm po.eval P₀)
    (hQP : blockDisjoint (Q, qo.eval, 2 * (n * r)) (Pm, po.eval, 2 * (n * n)) = true)
    (hQ : ∃ len, st.store.shape[Q]? = some (p, len) ∧ qo.eval + 2 * (n * r) ≤ len) :
    ∃ st', exec I (deflateProg p mm qr (.const n) (.const r) Pm po Q qo).run st = some st' := by
  sorry

omit [DecidableEq P] [AddMonoid C] in
/-- **The tape sampler is a sampler of ideal complex Gaussians**: for a rounding $\rho$ of real
draws and an ideal real tape $\xi$, deflation on the machine whose normal sampler is the tape
sampler of the stored tape $\rho \circ \xi$, with the sample of positions
`NLAlib.Computation.tapeIndexMatrix n`, equals deflation on the same machine with the sampler
`NLAlib.Computation.ScalarSem.gaussianNormal` of $\rho$ and the ideal complex Gaussian sample
`NLAlib.Computation.tapeComplexMatrix ξ n`. No printed source.
Proof: unfold `NLAlib.deflate`; the two sampled matrices agree entrywise
(`Matrix.ext`, `NLAlib.Computation.ScalarSem.tapeNormal`,
`NLAlib.Computation.ScalarSem.gaussianNormal`, `NLAlib.Computation.tapeComplexMatrix`):
$\sqrt2\,(x/\sqrt2) = x$ (`mul_div_cancel₀`, `Real.sqrt_ne_zero'`); every other field of the two
machines is the same. S, about 10 lines. -/
theorem deflate_tapeNormal_eq_deflate_gaussianNormal (sem : ScalarSem P K) (p : P)
    (ρ : ℝ → K) (ξ : ℕ → ℝ) (n r : ℕ) (P₀ : Matrix (Fin n) (Fin n) (K × K)) :
    deflate (sem.toFloatMachine p toNat mmR qrR unif (sem.tapeNormal p fun i => ρ (ξ i))) r P₀
        (tapeIndexMatrix n) =
      deflate (sem.toFloatMachine p toNat mmR qrR unif (sem.gaussianNormal p ρ)) r P₀
        (tapeComplexMatrix ξ n) := by
  have hsq : (√2 : ℝ) ≠ 0 := by positivity
  have hcancel : ∀ x : ℝ, √2 * (x / √2) = x := fun x => by field_simp
  have hmat : (tapeIndexMatrix n).map
      (sem.toFloatMachine p toNat mmR qrR unif (sem.tapeNormal p fun i => ρ (ξ i))).normal =
      (tapeComplexMatrix ξ n).map
      (sem.toFloatMachine p toNat mmR qrR unif (sem.gaussianNormal p ρ)).normal := by
    ext i j <;>
    simp only [Matrix.map_apply, tapeIndexMatrix, tapeComplexMatrix, Matrix.of_apply,
      ScalarSem.toFloatMachine, ScalarSem.tapeNormal, ScalarSem.gaussianNormal, hcancel]
  unfold deflate
  rw [hmat]
  rfl

/-! ### The registered tree -/

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- **The registered tree instantiates to the builder**: at the sizes $N$ and $(r)$ the tree
`NLAlib.deflateProg.compiled` is `NLAlib.deflateProg` on the declared buffers $0$, $1$ from
offset $0$. No printed source.
Proof: `rfl`, the instantiation equation of a compiled family (as for the Gram–Schmidt
tree). S, 1 line. -/
theorem deflateProg.toStmt_compiled (p : P) (mm qr : ι) (N : ℕ) (n : Fin 1 → ℕ) :
    (deflateProg.compiled p mm qr).toStmt N n =
      ProgFamily.inst (r := 1) (b := 2) (fun _ _ N n h =>
        (deflateProg p mm qr N (n 0) (h 0) 0 (h 1) 0).run) N n := by
  rfl

/-- **The registered tree computes `deflate`**: if kernels `mm` and `qr` of `I` are the routines
`mmR` and `qrR` on interleaved pairs, a successful run of `NLAlib.deflateProg.compiled` at the
sizes $N$ and $(r)$ from the initial state with the stored $\mathbf{P}$ and $2Nr$ empty cells as
declared buffers ends with declared buffer $1$ holding $\mathsf{deflate}(\mathbf{P}, r)$ on the
machine with the tape sampler of the Gaussian tape from position $0$. No printed source.
Proof: `NLAlib.Computation.Prog.exec_eq_exec_toStmt`, `NLAlib.deflateProg.toStmt_compiled`,
`NLAlib.holds_of_exec_deflateProg` with `NLAlib.Computation.EntryLayout.holds_inputState`
(scaffold); the initial tape positions are $0$ (`NLAlib.Computation.inputState`). S, about 12
lines. -/
theorem deflateProg.holds_of_exec_compiled {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) (p : P) (N r : ℕ)
    (P₀ : Matrix (Fin N) (Fin N) (K × K)) {st' : St P K C}
    (h : (deflateProg.compiled p mm qr).exec I N ![r]
      (inputState p [(pairLayout.toArray P₀).map some, Array.replicate (2 * (N * r)) none]) =
        some st') :
    pairLayout.Holds st'.store p 1 0
      (deflate (I.sem.toFloatMachine p toNat mmR qrR unif
        (I.sem.tapeNormal p (I.tape .gaussian))) r P₀ (tapeIndexMatrix N)) := by
  sorry

/-- **The registered tree always succeeds** under the standard model at $u$ with every value in
range, $u(p) \le 1$ and exact literals up to $2$, if kernels `mm` and `qr` of `I` are routines on
interleaved pairs, from the initial state of `NLAlib.deflateProg.holds_of_exec_compiled`. No
printed source.
Proof: as `NLAlib.deflateProg.holds_of_exec_compiled`, with `NLAlib.exists_exec_deflateProg`.
S, about 12 lines. -/
theorem deflateProg.exists_exec_compiled {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hlit : IsExactIntLit dec I.sem 2) (p : P)
    (hu : u p ≤ 1) (N r : ℕ) (P₀ : Matrix (Fin N) (Fin N) (K × K)) :
    ∃ st' : St P K C, (deflateProg.compiled p mm qr).exec I N ![r]
      (inputState p [(pairLayout.toArray P₀).map some, Array.replicate (2 * (N * r)) none]) =
        some st' := by
  sorry

/-- **The counts and the memory of the registered tree**: under the standard charge (one per
operation), every successful run of `NLAlib.deflateProg.compiled` at the sizes $N$ and $(r)$ adds
at most `NLAlib.deflateCount p mm qr N r` to the counts and raises the peak memory at tag `p` by
at most the $8N^2 + 2$ scratch cells above the current memory (by nothing at any other tag). No
printed source.
Proof: `NLAlib.Computation.Prog.bounds_staticCost_of_exec_eq_some`; the tree is straight-line
apart from its loops, and `NLAlib.Computation.FStmt.staticCost` of each loop is its trip count
times its body (`NLAlib.Computation.StaticCost.sequence`); `Nat.sub_sub_self`, `min_def` for the
copied columns. M, about 40 lines. -/
theorem deflateProg.cnt_le_of_exec_compiled {mm qr : ι} {I : Interp P ι K (OpCount P ι)}
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (p : P) (N r : ℕ)
    {st st' : St P K (OpCount P ι)}
    (h : (deflateProg.compiled p mm qr).exec I N ![r] st = some st') :
    st'.cnt ≤ st.cnt + deflateCount p mm qr N r ∧
      ∀ q, st'.peak q ≤ max (st.peak q) (st.cur q + if q = p then 8 * (N * N) + 2 else 0) := by
  have hb := (deflateProg.compiled p mm qr).bounds_staticCost_of_exec_eq_some I N ![r] h
  have hcharge : I.charge = fun k => Finsupp.single k 1 := funext hc
  have hb' := hb.mono (b := ⟨deflateCount p mm qr N r,
    fun q => if q = p then 8 * (N * N) + 2 else 0, _⟩) ?_ ?_ le_rfl
  · exact ⟨hb'.count, hb'.peak⟩
  · rw [hcharge]
    intro k
    change (FStmt.staticCost (fun k => Finsupp.single k 1) I.width
      (deflateProg.compiled (ι := ι) p mm qr) (Fin.cons N ![r])).count k ≤ _
    change (StaticCost.seq _ _).count k ≤ _
    simp only [FStmt.staticCost, StaticCost.seq, StaticCost.alloc, StaticCost.step,
      StaticCost.zero, StaticCost.sequence_count_apply, Instr.kind, Instr.subst, IExp.evalIn,
      Finsupp.add_apply, List.map_const', List.sum_replicate, List.length_range,
      Finsupp.zero_apply]
    simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Fin.cons_zero, Fin.cons_one,
      Matrix.Fin.cons_vecCons, Matrix.cons_val_fin_one, Fin.val_eq_zero, Fin.mk_one, add_zero,
      zero_add, smul_eq_mul, List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, deflateCount, Nat.sub_sub_eq_min]
    simp only [IExp.evalIn, Matrix.cons_val_zero, Finsupp.add_apply]
    classical
    cases k <;> simp only [Finsupp.single_apply, OpKind.bin.injEq, OpKind.un.injEq,
      OpKind.lit.injEq, OpKind.draw.injEq, OpKind.copy.injEq, OpKind.kcall.injEq, reduceCtorEq,
      ite_false, mul_zero, add_zero, zero_add, le_refl]
    all_goals split_ifs <;> linarith
  · intro q
    change (FStmt.staticCost I.charge I.width
      (deflateProg.compiled (ι := ι) p mm qr) (Fin.cons N ![r])).cells q ≤ _
    change (StaticCost.seq _ _).cells q ≤ _
    simp only [FStmt.staticCost, StaticCost.seq, StaticCost.alloc, StaticCost.step,
      StaticCost.zero, IExp.evalIn, Instr.kind, Instr.subst]
    simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Fin.cons_zero,
      Matrix.Fin.cons_vecCons, StaticCost.sequence_cells_mk, List.range_eq_nil, max_self,
      add_zero, Nat.max_zero, ite_self]
    split_ifs <;> omega

end NLAlib
