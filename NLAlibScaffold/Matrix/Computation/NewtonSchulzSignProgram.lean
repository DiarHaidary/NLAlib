/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.KernelCall
public import NLAlib.Computation.StaticCost
public import NLAlib.Matrix.Computation.NewtonSchulzSign
public import NLAlib.Matrix.Computation.NewtonSchulzSignProgramTree
public import NLAlibScaffold.Computation.Exec
public import NLAlibScaffold.Matrix.Computation.KernelContracts
public import NLAlibScaffold.Matrix.Computation.PairKernels

/-!
# The Newton–Schulz sign program computes `newtonSchulzSign` (scaffold)

Statements for a new file `NLAlib/Matrix/Computation/NewtonSchulzSignProgram.lean` (stage
COMPDYN S1d, design note `docs/design/Computation-SignDeflatePrograms.md`, §3): the refinement of
the program `NLAlib.newtonSchulzSignProg` to the shallow `NLAlib.newtonSchulzSign`. Under any
interpretation whose kernel `mm` is a routine on interleaved pairs
(`NLAlib.Computation.IsMatMulKernel`) and whose semantics decides flags, **every successful run
computes exactly `NLAlib.newtonSchulzSign` on the machine of the semantics and the routine**
(`NLAlib.Computation.ScalarSem.toFloatMachine`; the machine's other black boxes are arbitrary,
since the algorithm does not use them), and under the standard model with every value in range
the run succeeds when the machine's test passes within the step limit. The counts are bounded by
`NLAlib.newtonSchulzSignCount`.

## Main results

* `NLAlib.holds_of_exec_newtonSchulzTestBlock`, `NLAlib.exists_exec_newtonSchulzTestBlock`,
  `NLAlib.holds_of_exec_newtonSchulzStepBlock`, `NLAlib.exists_exec_newtonSchulzStepBlock`: the
  test and the step.
* `NLAlib.holds_of_exec_whileFuel_newtonSchulz`: the loop computes `NLAlib.newtonSchulzLoop`.
* `NLAlib.holds_of_exec_newtonSchulzSignProg`, `NLAlib.exists_exec_newtonSchulzSignProg`: the
  refinement (partial equality, success) for the builder from any state.
* `NLAlib.newtonSchulzSignProg.toStmt_compiled`,
  `NLAlib.newtonSchulzSignProg.holds_of_exec_compiled`,
  `NLAlib.newtonSchulzSignProg.exists_exec_compiled`,
  `NLAlib.newtonSchulzSignProg.cnt_le_of_exec_compiled`: the registered tree.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {Su Sg : Type} {toNat : K → ℕ} {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}
  {unif : K → Su → K} {normal : Sg → K × K}

/-- **The test block computes the machine's test**: if kernel `mm` of `I` is the routine `mmR` on
interleaved pairs, a successful run of `NLAlib.newtonSchulzTestBlock` from a state whose block at
`X` holds the complex $n \times n$ matrix $\mathbf{A}$ and whose cells `one`, `lo`, `hi` hold the
machine's one, $-\eta$ and $\eta$ (`M` the machine of the semantics at `p` with product `mmR`),
with the scratch buffers `W`, `V` distinct from `X` and from each other, the cells outside them
and the flag cell outside the block at `X` and distinct from `lo` and `hi`, ends with `W` holding
$\mathrm{mm}(\mathbf{A}, \mathbf{A})$, `V` holding the shift `M.hermShift (mmR A A) M.one`, and
the flag holding the machine's zero if `NLAlib.newtonSchulzTest M η A` and its one otherwise;
every cell outside `W`, `V` and the flag is unchanged, the store shape and the tape positions
too. No printed source.
Proof: `NLAlib.Computation.exec_run_bind` splits the block into the kernel call
(`NLAlib.Computation.exec_kcall`,
`NLAlib.Computation.IsMatMulKernel.holds_of_kcallStore_eq_some` with
`NLAlib.Computation.pairLayout.get_put`), `NLAlib.Computation.holds_of_exec_zhermShift` and
`NLAlib.Computation.read_of_exec_zboxTest`, the frames carrying the hypotheses from one to the
next; unfold `NLAlib.newtonSchulzTest`. M, about 50 lines. -/
theorem holds_of_exec_newtonSchulzTestBlock {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (p : P) (n : ℕ) {X W V : ℕ} {xo : IExp ℕ} {one lo hi f : Cell ℕ ℕ} {η : K}
    {st st' : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)}
    (hA : pairLayout.Holds st.store p X xo.eval A)
    (hone : st.store.read p one.buf one.idx.eval =
      some (I.sem.toFloatMachine p toNat mmR qrR unif normal).one)
    (hlo : st.store.read p lo.buf lo.idx.eval =
      some ((I.sem.toFloatMachine p toNat mmR qrR unif normal).neg η))
    (hhi : st.store.read p hi.buf hi.idx.eval = some η)
    (hWX : W ≠ X) (hVX : V ≠ X) (hWV : W ≠ V)
    (hcells : ∀ c ∈ [one, lo, hi, f], c.buf ≠ W ∧ c.buf ≠ V)
    (hfX : blockDisjoint (f.buf, f.idx.eval, 1) (X, xo.eval, 2 * (n * n)) = true)
    (hflo : blockDisjoint (f.buf, f.idx.eval, 1) (lo.buf, lo.idx.eval, 1) = true)
    (hfhi : blockDisjoint (f.buf, f.idx.eval, 1) (hi.buf, hi.idx.eval, 1) = true)
    (h : exec I (newtonSchulzTestBlock p mm (.const n) X xo W V one lo hi f).run st = some st') :
    let M := I.sem.toFloatMachine p toNat mmR qrR unif normal
    pairLayout.Holds st'.store p W 0 (mmR A A) ∧
      pairLayout.Holds st'.store p V 0 (M.hermShift (mmR A A) M.one) ∧
      st'.store.read p f.buf f.idx.eval = some (if newtonSchulzTest M η A then M.zero else M.one) ∧
      (∀ q b i, b ≠ W → b ≠ V → blockDisjoint (b, i, 1) (f.buf, f.idx.eval, 1) = true →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  intro M
  obtain ⟨hoW, hoV⟩ := hcells one (by simp)
  obtain ⟨hlW, hlV⟩ := hcells lo (by simp)
  obtain ⟨hhW, hhV⟩ := hcells hi (by simp)
  obtain ⟨hfW, hfV⟩ := hcells f (by simp)
  unfold newtonSchulzTestBlock at h
  rw [exec_run_bind I (b := stmt (.kcall mm p [.const n, .const n, .const n]
    [(X, xo), (X, xo)] [(W, 0)])) (fun _ => rfl)] at h
  have hk : (stmt (.kcall mm p [.const n, .const n, .const n] [(X, xo), (X, xo)] [(W, 0)]) :
      Builder P ι ℕ ℕ Unit).run = .seq (.kcall mm p [.const n, .const n, .const n]
        [(X, xo), (X, xo)] [(W, 0)]) .skip := rfl
  rw [hk, exec_seq_skip, exec_kcall] at h
  obtain ⟨σ1, hσ1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨s1, hs1, hσ1⟩ := Option.map_eq_some_iff.mp hσ1
  have hst1 : σ1.store = s1 := by rw [← hσ1]
  have hpos1 : σ1.pos = st.pos := by rw [← hσ1]
  rw [exec_run_bind I (b := zhermShift (ι := ι) p (.const n) W 0 one V 0) (fun _ => rfl)] at h
  obtain ⟨σ2, h2, h⟩ := Option.bind_eq_some_iff.mp h
  have hs1' : I.kcallStore mm p [n, n, n] [(X, xo.eval), (X, xo.eval)] [(W, 0)] st.store =
      some s1 := by
    simpa using hs1
  have hca : blockDisjoint (W, 0, n * n * 2) (X, xo.eval, n * n * 2) = true := by
    simp [blockDisjoint, hWX]
  obtain ⟨hWmm, hfr1⟩ := IsMatMulKernel.holds_of_kcallStore_eq_some hmm pairLayout.get_put p
    hA hA hca hca hs1'
  have hsh1 : s1.shape = st.store.shape := Interp.shape_of_kcallStore_eq_some hs1'
  have hread1 : ∀ q b i, b ≠ W → σ1.store.read q b i = st.store.read q b i := fun q b i hb => by
    rw [hst1]
    exact hfr1 q b i (by simp [blockDisjoint, hb])
  have hA1 : pairLayout.Holds σ1.store p W 0 (mmR A A) := by rw [hst1]; exact hWmm
  have hc1 : σ1.store.read p one.buf one.idx.eval = some M.one := by
    rw [hread1 _ _ _ hoW]; exact hone
  obtain ⟨hVmm, hfr2, hsh2, hpos2⟩ := holds_of_exec_zhermShift p n hA1 hc1
    (by simp [blockDisjoint, Ne.symm hWV]) (by simp [blockDisjoint, hoV]) h2
  have hread2 : ∀ q b i, b ≠ V → σ2.store.read q b i = σ1.store.read q b i :=
    fun q b i hb => hfr2 q b i (by simp [blockDisjoint, hb])
  have hread : ∀ q b i, b ≠ W → b ≠ V → σ2.store.read q b i = st.store.read q b i :=
    fun q b i hbW hbV => (hread2 q b i hbV).trans (hread1 q b i hbW)
  have hlo2 : σ2.store.read p lo.buf lo.idx.eval = some (M.neg η) := by
    rw [hread _ _ _ hlW hlV]; exact hlo
  have hhi2 : σ2.store.read p hi.buf hi.idx.eval = some η := by
    rw [hread _ _ _ hhW hhV]; exact hhi
  obtain ⟨hflag, hfr3, hsh3, hpos3⟩ := read_of_exec_zboxTest p n n hVmm hlo2 hhi2
    (by simp [blockDisjoint, hfV]) hflo hfhi h
  have hWst : pairLayout.Holds st'.store p W 0 (mmR A A) :=
    EntryLayout.Holds.of_forall_read_eq hA1 fun i _ _ =>
      (hfr3 p W i (by simp [blockDisjoint, Ne.symm hfW])).trans
        (hfr2 p W i (by simp [blockDisjoint, hWV]))
  have hVst : pairLayout.Holds st'.store p V 0 (M.hermShift (mmR A A) M.one) :=
    EntryLayout.Holds.of_forall_read_eq hVmm fun i _ _ =>
      hfr3 p V i (by simp [blockDisjoint, Ne.symm hfV])
  have hflag' : st'.store.read p f.buf f.idx.eval =
      some (if newtonSchulzTest M η A = true then M.zero else M.one) := by
    unfold newtonSchulzTest
    exact hflag
  have hfrm : ∀ q b i, b ≠ W → b ≠ V → blockDisjoint (b, i, 1) (f.buf, f.idx.eval, 1) = true →
      st'.store.read q b i = st.store.read q b i := fun q b i hbW hbV hbf =>
    (hfr3 q b i hbf).trans ((hfr2 q b i (by simp [blockDisjoint, hbV])).trans
      (hread1 q b i hbW))
  have hshT : st'.store.shape = st.store.shape :=
    hsh3.trans (hsh2.trans (by rw [hst1]; exact hsh1))
  exact ⟨hWst, hVst, hflag', hfrm, hshT, hpos3.trans (hpos2.trans hpos1)⟩

/-- **The test block succeeds** under the standard model with every value in range, when the
buffers `W` and `V` at tag `p` have $2n^2$ cells and the flag can be written (hypotheses as
`NLAlib.holds_of_exec_newtonSchulzTestBlock`). No printed source.
Proof: `NLAlib.Computation.exec_run_bind`; the kernel call succeeds
(`NLAlib.Computation.IsMatMulKernel.kcallStore_eq`, the reads by
`NLAlib.Computation.EntryLayout.holds_iff_readBlock_eq_some`, the write by
`NLAlib.Computation.Store.exists_writeBlock_eq_some_of_getElem?_shape`), then
`NLAlib.Computation.exists_exec_zhermShift` and `NLAlib.Computation.exists_exec_zboxTest` on the
states the value lemmas describe. M, about 40 lines. -/
theorem exists_exec_newtonSchulzTestBlock {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    {u : P → ℝ} {dec : P → K → ℝ} (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (p : P) (n : ℕ) {X W V : ℕ} {xo : IExp ℕ} {one lo hi f : Cell ℕ ℕ} {cone ℓ η : K}
    {st : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)}
    (hA : pairLayout.Holds st.store p X xo.eval A)
    (hone : st.store.read p one.buf one.idx.eval = some cone)
    (hlo : st.store.read p lo.buf lo.idx.eval = some ℓ)
    (hhi : st.store.read p hi.buf hi.idx.eval = some η)
    (hWX : W ≠ X) (hVX : V ≠ X) (hWV : W ≠ V)
    (hcells : ∀ c ∈ [one, lo, hi, f], c.buf ≠ W ∧ c.buf ≠ V)
    (hfX : blockDisjoint (f.buf, f.idx.eval, 1) (X, xo.eval, 2 * (n * n)) = true)
    (hflo : blockDisjoint (f.buf, f.idx.eval, 1) (lo.buf, lo.idx.eval, 1) = true)
    (hfhi : blockDisjoint (f.buf, f.idx.eval, 1) (hi.buf, hi.idx.eval, 1) = true)
    (hW : ∃ len, st.store.shape[W]? = some (p, len) ∧ 2 * (n * n) ≤ len)
    (hV : ∃ len, st.store.shape[V]? = some (p, len) ∧ 2 * (n * n) ≤ len)
    (hf : ∃ s, st.store.write p f.buf f.idx.eval default = some s) :
    ∃ st', exec I (newtonSchulzTestBlock p mm (.const n) X xo W V one lo hi f).run st =
      some st' := by
  have hw2 : (pairLayout (K := K)).width = 2 := rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hcells
  obtain ⟨⟨honeW, honeV⟩, ⟨hloW, hloV⟩, ⟨hhiW, hhiV⟩, ⟨hfW, hfV⟩⟩ := hcells
  have hd : ∀ {b b' : ℕ} (o o' l l' : ℕ), b ≠ b' → blockDisjoint (b, o, l) (b', o', l') = true :=
    fun _ _ _ _ h => by simp [blockDisjoint, h]
  -- the kernel call
  have hrA := (EntryLayout.holds_iff_readBlock_eq_some pairLayout st.store p X xo.eval A).1 hA
  obtain ⟨len, hWsh, hWlen⟩ := hW
  obtain ⟨s₁, hs₁⟩ := Store.exists_writeBlock_eq_some_of_getElem?_shape (s := st.store) (p := p)
    (b := W) (off := 0) (xs := pairLayout.toArray (mmR (pairLayout.toMatrix n n
      (pairLayout.toArray A)) (pairLayout.toMatrix n n (pairLayout.toArray A))))
    fun i hi => ⟨len, hWsh, by
      rw [EntryLayout.size_toArray, hw2] at hi; rw [Nat.mul_comm (n * n)] at hi; omega⟩
  have hk : I.kcallStore mm p [n, n, n] [(X, xo.eval), (X, xo.eval)] [(W, 0)] st.store =
      some s₁ := by
    rw [hmm.kcallStore_eq p hrA hrA (hd _ _ _ _ hWX) (hd _ _ _ _ hWX), hs₁]
  obtain ⟨hW₁, hfr₁⟩ := hmm.holds_of_kcallStore_eq_some pairLayout.get_put p (a := (X, xo.eval))
    (b := (X, xo.eval)) (c := (W, 0)) hA hA (hd _ _ _ _ hWX) (hd _ _ _ _ hWX) hk
  change ∃ st', exec I (.seq (.kcall mm p [.const n, .const n, .const n] [(X, xo), (X, xo)]
    [(W, 0)]) (.seq (.named _ _ _) (zboxTest (ι := ι) p (.const n) (.const n) V 0 lo hi f).run))
    st = some st'
  rw [exec_seq, exec_kcall]
  erw [hk]
  rw [Option.map_some, Option.bind_some, exec_seq]
  set st₁ : St P K C := { st with store := s₁, cnt := _ }
  have hsh₁ : st₁.store.shape = st.store.shape := Store.shape_of_writeBlock_eq_some hs₁
  -- the shift
  obtain ⟨st₂, h₂⟩ := exists_exec_zhermShift (I := I) (ι := ι) p n (X := W) (xo := 0) (c := one)
    (Y := V) (yo := 0) (st := st₁) hW₁ ((hfr₁ _ _ _ (hd _ _ _ _ honeW)).trans hone)
    (hd _ _ _ _ hWV.symm) (hd _ _ _ _ honeV) hsem
    (by rw [hsh₁, IExp.eval_zero]; simpa only [zero_add] using hV)
  obtain ⟨hV₂, hfr₂, hsh₂, -⟩ := holds_of_exec_zhermShift (toNat := fun _ => 0) (mmR := mmR)
    (qrR := fun {_ _} B => (fun _ _ => default, B)) (unif := fun k (_ : Unit) => k)
    (normal := fun (_ : Unit) => default) p n hW₁ ((hfr₁ _ _ _ (hd _ _ _ _ honeW)).trans hone)
    (hd _ _ _ _ hWV.symm) (hd _ _ _ _ honeV) h₂
  change exec I (.seq (.named _ _ _) .skip) st₁ = some st₂ at h₂
  rw [exec_seq_skip] at h₂
  rw [h₂, Option.bind_some]
  -- the test
  have hrd : ∀ c : Cell ℕ ℕ, c.buf ≠ W → c.buf ≠ V →
      st₂.store.read p c.buf c.idx.eval = st.store.read p c.buf c.idx.eval := fun c h₁ h₂ =>
    (hfr₂ _ _ _ (hd _ _ _ _ h₂)).trans (hfr₁ _ _ _ (hd _ _ _ _ h₁))
  obtain ⟨sf, hsf⟩ := hf
  exact exists_exec_zboxTest p n n (X := V) (xo := 0) hV₂ ((hrd lo hloW hloV).trans hlo)
    ((hrd hi hhiW hhiV).trans hhi) (hd _ _ _ _ hfV) hflo hfhi hsem
    (Store.exists_write_eq_some_of_shape_eq (hsh₂.trans hsh₁) hsf default)

/-- A literal-index instruction writes the machine's value of its index and changes no other
cell, the shape or the tape positions. No printed source. -/
private theorem exec_litIdx_read (p : P) (e : IExp ℕ) (c' : Cell ℕ ℕ) (σ₀ σ : St P K C)
    (hσ : exec I (ins (.litIdx p c' e) : Builder P ι ℕ ℕ Unit).run σ₀ = some σ) :
    σ.store.read p c'.buf c'.idx.eval =
        some ((I.sem.toFloatMachine p toNat mmR qrR unif normal).ofNat e.eval) ∧
      (∀ q b i, ¬(b = c'.buf ∧ i = c'.idx.eval) → σ.store.read q b i = σ₀.store.read q b i) ∧
      σ.store.shape = σ₀.store.shape ∧ σ.pos = σ₀.pos := by
  change exec I (.seq (.instr (.litIdx p c' e)) .skip) σ₀ = some σ at hσ
  rcases hv : I.sem.lit p (e.eval : ℚ) with _ | v
  · simp [exec_seq, exec_instr, Instr.run, hv] at hσ
  rcases hw : σ₀.store.write p c'.buf c'.idx.eval v with _ | s
  · simp [exec_seq, exec_instr, Instr.run, hv, hw] at hσ
  rw [exec_seq_instr_litIdx I hv hw, exec_skip] at hσ
  injection hσ with hσ
  subst hσ
  have hofn : (I.sem.toFloatMachine p toNat mmR qrR unif normal).ofNat e.eval = v := by
    show ((I.sem.lit p ((e.eval : ℕ) : ℚ)).getD default) = v
    rw [hv]; rfl
  refine ⟨?_, fun q b i hne => ?_, Store.shape_of_write_eq_some hw, rfl⟩
  · rw [hofn]; exact Store.read_of_write_eq_some hw
  · exact Store.read_of_write_eq_some_of_ne hw (not_and_or.mp hne)

/-- **The step block computes the machine's rounded step**: if kernel `mm` of `I` is the routine
`mmR` on interleaved pairs, a successful run of `NLAlib.newtonSchulzStepBlock` from a state whose
block at `X` holds the complex $n \times n$ matrix $\mathbf{A}$ and whose scratch buffer `W`
holds $\mathrm{mm}(\mathbf{A}, \mathbf{A})$, with `W`, `V` distinct from `X` and from each other
and the cell `c` outside `W`, `V` and the block at `X`, ends with the block at `X` holding
`NLAlib.newtonSchulzRounded M A` (`M` the machine of the semantics at `p` with product `mmR`);
every cell outside the block at `X`, the buffers `W`, `V` and the cell `c` is unchanged, the store
shape and the tape positions too. No printed source.
Proof: `NLAlib.Computation.exec_run_bind` splits the block:
`NLAlib.Computation.exec_seq_instr_litIdx` (the literal $3$ is the machine's `ofNat 3`),
`NLAlib.Computation.holds_of_exec_zhermShift`,
`NLAlib.Computation.holds_of_exec_zneg` in place, the kernel call
(`NLAlib.Computation.IsMatMulKernel.holds_of_kcallStore_eq_some`), the literal $4$, and
`NLAlib.Computation.holds_of_exec_zhermAvg`; unfold `NLAlib.newtonSchulzRounded`. M, about 50
lines. -/
theorem holds_of_exec_newtonSchulzStepBlock {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (p : P) (n : ℕ) {X W V : ℕ} {xo : IExp ℕ} {c : Cell ℕ ℕ} {st st' : St P K C}
    {A : Matrix (Fin n) (Fin n) (K × K)} (hA : pairLayout.Holds st.store p X xo.eval A)
    (hW : pairLayout.Holds st.store p W 0 (mmR A A)) (hWX : W ≠ X) (hVX : V ≠ X) (hWV : W ≠ V)
    (hcW : c.buf ≠ W) (hcV : c.buf ≠ V)
    (hcX : blockDisjoint (c.buf, c.idx.eval, 1) (X, xo.eval, 2 * (n * n)) = true)
    (h : exec I (newtonSchulzStepBlock p mm (.const n) X xo W V c).run st = some st') :
    pairLayout.Holds st'.store p X xo.eval
        (newtonSchulzRounded (I.sem.toFloatMachine p toNat mmR qrR unif normal) A) ∧
      (∀ q b i, b ≠ W → b ≠ V → blockDisjoint (b, i, 1) (X, xo.eval, 2 * (n * n)) = true →
        blockDisjoint (b, i, 1) (c.buf, c.idx.eval, 1) = true →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  have hsep : ∀ b i, blockDisjoint (b, i, 1) (c.buf, c.idx.eval, 1) = true →
      ¬(b = c.buf ∧ i = c.idx.eval) := by
    intro b i hbi ⟨hb, hi⟩
    rw [hb, hi] at hbi
    simp [blockDisjoint] at hbi
  unfold newtonSchulzStepBlock at h
  rw [exec_run_bind I (b := ins (.litIdx p c 3)) (fun _ => rfl)] at h
  obtain ⟨σ1, h1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hc1, hf1, hsh1, hp1⟩ := exec_litIdx_read p _ _ _ _ h1
  rw [exec_run_bind I (b := zhermShift (ι := ι) p (.const n) W 0 c V 0) (fun _ => rfl)] at h
  obtain ⟨σ2, h2, h⟩ := Option.bind_eq_some_iff.mp h
  have hW1 : pairLayout.Holds σ1.store p W 0 (mmR A A) :=
    EntryLayout.Holds.of_forall_read_eq hW fun i _ _ => hf1 p W i fun hh => hcW hh.1.symm
  obtain ⟨hV2, hf2, hsh2, hp2⟩ := holds_of_exec_zhermShift p n hW1 hc1
    (by simp [blockDisjoint, Ne.symm hWV]) (by simp [blockDisjoint, hcV]) h2
  rw [exec_run_bind I (b := zneg (ι := ι) p (.const n) (.const n) V 0 V 0) (fun _ => rfl)] at h
  obtain ⟨σ3, h3, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hV3, hf3, hsh3, hp3⟩ := holds_of_exec_zneg p n n hV2 (Or.inr ⟨rfl, rfl⟩) h3
  rw [exec_run_bind I (b := stmt (.kcall mm p [.const n, .const n, .const n]
    [(X, xo), (V, 0)] [(W, 0)])) (fun _ => rfl)] at h
  have hk : (stmt (.kcall mm p [.const n, .const n, .const n] [(X, xo), (V, 0)] [(W, 0)]) :
      Builder P ι ℕ ℕ Unit).run = .seq (.kcall mm p [.const n, .const n, .const n]
        [(X, xo), (V, 0)] [(W, 0)]) .skip := rfl
  obtain ⟨σ4, h4, h⟩ := Option.bind_eq_some_iff.mp h
  rw [hk, exec_seq_skip, exec_kcall] at h4
  obtain ⟨s4, hs4, hσ4⟩ := Option.map_eq_some_iff.mp h4
  have hs4' : I.kcallStore mm p [n, n, n] [(X, xo.eval), (V, 0)] [(W, 0)] σ3.store = some s4 := by
    simpa using hs4
  have hst4 : σ4.store = s4 := by rw [← hσ4]
  have hp4 : σ4.pos = σ3.pos := by rw [← hσ4]
  have hsh4 : s4.shape = σ3.store.shape := Interp.shape_of_kcallStore_eq_some hs4'
  have hXc : ∀ i, xo.eval ≤ i → i < xo.eval + n * n * 2 →
      ¬(X = c.buf ∧ i = c.idx.eval) := by
    intro i h1 h2 hh
    have := hcX
    simp only [blockDisjoint, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at this
    rcases this with (h | h) | h
    · exact h hh.1.symm
    · omega
    · omega
  have hX1 : pairLayout.Holds σ1.store p X xo.eval A :=
    EntryLayout.Holds.of_forall_read_eq hA fun i h1 h2 => hf1 p X i (hXc i h1 h2)
  have hX3 : pairLayout.Holds σ3.store p X xo.eval A :=
    EntryLayout.Holds.of_forall_read_eq hX1 fun i _ _ =>
      (hf3 p X i (by simp [blockDisjoint, hVX.symm])).trans
        (hf2 p X i (by simp [blockDisjoint, hVX.symm]))
  have hca : blockDisjoint (W, 0, n * n * 2) (X, xo.eval, n * n * 2) = true := by
    simp [blockDisjoint, hWX]
  have hcb : blockDisjoint (W, 0, n * n * 2) (V, 0, n * n * 2) = true := by
    simp [blockDisjoint, hWV]
  obtain ⟨hW4, hfr4⟩ := IsMatMulKernel.holds_of_kcallStore_eq_some hmm pairLayout.get_put p
    hX3 hV3 hca hcb hs4'
  have hW4s := hW4
  rw [← hst4] at hW4s
  rw [exec_run_bind I (b := ins (.litIdx p c 4)) (fun _ => rfl)] at h
  obtain ⟨σ5, h5, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hc5, hf5, hsh5, hp5⟩ := exec_litIdx_read p _ _ _ _ h5
  have hW5 := EntryLayout.Holds.of_forall_read_eq hW4s fun i _ _ =>
    hf5 p W i fun hh => hcW hh.1.symm
  obtain ⟨hX6, hf6, hsh6, hp6⟩ := holds_of_exec_zhermAvg p n hW5 hc5
    (by simp [blockDisjoint, Ne.symm hWX]) hcX h
  have hfr4' : ∀ q b i, blockDisjoint (b, i, 1) (W, 0, n * n * 2) = true →
      σ4.store.read q b i = σ3.store.read q b i := fun q b i h => by
    rw [hst4]; exact hfr4 q b i h
  refine ⟨hX6, fun q b i hbW hbV hbX hbc => ?_, ?_, ?_⟩
  · exact (hf6 q b i hbX).trans ((hf5 q b i (hsep b i hbc)).trans
      ((hfr4' q b i (by simp [blockDisjoint, hbW])).trans
        ((hf3 q b i (by simp [blockDisjoint, hbV])).trans
          ((hf2 q b i (by simp [blockDisjoint, hbV])).trans (hf1 q b i (hsep b i hbc))))))
  · exact hsh6.trans (hsh5.trans (by rw [hst4]; exact hsh4.trans (hsh3.trans (hsh2.trans hsh1))))
  · exact hp6.trans (hp5.trans (hp4.trans (hp3.trans (hp2.trans hp1))))

/-- **The step block succeeds** under the standard model at $u$ with every value in range and
$u(p) < 1$, when the buffers `W` and `V` at tag `p` have $2n^2$ cells and the cell `c` can be
written (hypotheses as `NLAlib.holds_of_exec_newtonSchulzStepBlock`). No printed source.
Proof: as `NLAlib.exists_exec_newtonSchulzTestBlock`, with
`NLAlib.Computation.exists_exec_zhermShift`, `NLAlib.Computation.exists_exec_zneg`,
`NLAlib.Computation.exists_exec_zhermAvg`; the literal $4$ decodes to $4(1 + \delta)$ with
$\lvert\delta\rvert \le u(p) < 1$ (`lit_err`), so it is nonzero. M, about 40 lines. -/
theorem exists_exec_newtonSchulzStepBlock {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    {u : P → ℝ} {dec : P → K → ℝ} (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (p : P) (hu : u p < 1) (n : ℕ) {X W V : ℕ} {xo : IExp ℕ} {c : Cell ℕ ℕ} {st : St P K C}
    {A : Matrix (Fin n) (Fin n) (K × K)} (hA : pairLayout.Holds st.store p X xo.eval A)
    (hW : pairLayout.Holds st.store p W 0 (mmR A A)) (hWX : W ≠ X) (hVX : V ≠ X) (hWV : W ≠ V)
    (hcW : c.buf ≠ W) (hcV : c.buf ≠ V)
    (hcX : blockDisjoint (c.buf, c.idx.eval, 1) (X, xo.eval, 2 * (n * n)) = true)
    (hV : ∃ len, st.store.shape[V]? = some (p, len) ∧ 2 * (n * n) ≤ len)
    (hc : ∃ s, st.store.write p c.buf c.idx.eval default = some s) :
    ∃ st', exec I (newtonSchulzStepBlock p mm (.const n) X xo W V c).run st = some st' := by
  sorry

/-- **The Newton–Schulz loop of the program computes `NLAlib.newtonSchulzLoop`**: if kernel `mm`
of `I` is the routine `mmR` on interleaved pairs and the semantics decides flags at `p`, a
successful run of the `whileFuel` loop of `NLAlib.newtonSchulzSignProg` with fuel $j + 1$, from a
state whose block at `X` holds $\mathbf{A}$, whose scratch buffer `W` holds
$\mathrm{mm}(\mathbf{A}, \mathbf{A})$, whose cells $0$, $3$, $4$ of the scratch buffer `t` hold
$\eta$, the machine's one and $-\eta$, and whose cell $1$ holds the flag of the test of
$\mathbf{A}$, ends with the block at `X` holding `NLAlib.newtonSchulzLoop M η j A`; every cell
outside the block at `X` and the scratch buffers `t`, `W`, `V` is unchanged, the store shape and
the tape positions too. No printed source.
Proof: induction on $j$ generalizing the state and $\mathbf{A}$, with
`NLAlib.Computation.exec_whileFuel_of_eval_eq_succ` (scaffold). The comparison reads the flag and
the stored one: by `hflag`, it is false exactly when the flag is the machine's zero, that is when
the test passes, and the loop stops with $\mathbf{A}$ (`NLAlib.newtonSchulzLoop` returns
$\mathbf{A}$ when the test passes); otherwise the body runs:
`NLAlib.holds_of_exec_newtonSchulzStepBlock`, then `NLAlib.holds_of_exec_newtonSchulzTestBlock`
re-establish the hypotheses for `NLAlib.newtonSchulzRounded M A`, and the induction hypothesis
at fuel $j$ applies. At $j = 0$ a true comparison runs the body and then
`NLAlib.Computation.exec_whileFuel_of_eval_eq_zero` (scaffold) fails, contradicting `h`. M, about
70 lines. -/
theorem holds_of_exec_whileFuel_newtonSchulz {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (p : P) (hflag : I.sem.DecidesFlags p) (n : ℕ) {X W V t : ℕ} {xo fuel : IExp ℕ} {j : ℕ}
    (hfuel : fuel.eval = j + 1) {η : K} {st st' : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)}
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
    (h : exec I (.whileFuel fuel p .eq ⟨t, 1⟩ ⟨t, 3⟩ (Builder.run do
      newtonSchulzStepBlock p mm (.const n) X xo W V ⟨t, 2⟩
      newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩)) st =
        some st') :
    pairLayout.Holds st'.store p X xo.eval
        (newtonSchulzLoop (I.sem.toFloatMachine p toNat mmR qrR unif normal) η j A) ∧
      (∀ q b i, b ≠ t → b ≠ W → b ≠ V →
        blockDisjoint (b, i, 1) (X, xo.eval, 2 * (n * n)) = true →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  sorry

/-- **The refinement of the Newton–Schulz sign program, partial equality**: if kernel `mm` of `I`
is the routine `mmR` on interleaved pairs and the semantics decides flags at `p`, a successful
run of `NLAlib.newtonSchulzSignProg` at size $n$ and step limit $F$, from a state whose block at
`A` holds the stored $\mathbf{A}$ and whose cells `po`, `po + 1` of `par` hold $\varepsilon$ and
$b$, with the output block at `X` disjoint from both, ends with the output block holding
$$\mathsf{newtonSchulzSign}(\mathbf{A}, \varepsilon, b)$$
computed by `NLAlib.newtonSchulzSign` with step limit $F$ on the machine `M` of the semantics at
`p` with product `mmR` (for every choice of the machine's other black boxes, which the algorithm
does not use); every cell outside the output block is unchanged, the store shape and the tape
positions too. No printed source.
Proof: unfold `NLAlib.newtonSchulzSignProg`; `NLAlib.Computation.exec_seq`, the `scope` and the
three `NLAlib.Computation.exec_alloc`s push the scratch buffers $t$, $W$, $V$ at handles
`st.store.size`, $+1$, $+2$ (distinct from every existing handle); the four instructions give
$\eta = \mathrm{fl}(\bar\varepsilon/\mathrm{fl}(4n))$ in cell $0$, $-\eta$ in cell $4$ and the
machine's one in
cell $3$ (each value read off its successful run, `Option.getD_some`);
`NLAlib.Computation.holds_of_exec_zhermScale` gives the machine's scaling of $\mathbf{A}$ by $b$
(`NLAlib.FloatMachine.hermScale`) at `X`;
`NLAlib.holds_of_exec_newtonSchulzTestBlock` gives the hypotheses of
`NLAlib.holds_of_exec_whileFuel_newtonSchulz` at $j = F$ (fuel `F + 1`, `IExp.eval_add`), whose
conclusion is `NLAlib.newtonSchulzSign` by definition; the pops
(`NLAlib.Computation.Store.read_pop_of_lt`, `NLAlib.Computation.Store.shape_pop`) keep the output
block and the frame. M, about 80 lines (split the set-up into a private lemma). -/
theorem holds_of_exec_newtonSchulzSignProg {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (p : P) (hflag : I.sem.DecidesFlags p) (n F : ℕ) {A par X : ℕ} {ao po xo : IExp ℕ}
    {st st' : St P K C} {A₀ : Matrix (Fin n) (Fin n) (K × K)} {ε b : K}
    (hA : pairLayout.Holds st.store p A ao.eval A₀)
    (hε : st.store.read p par po.eval = some ε) (hb : st.store.read p par (po.eval + 1) = some b)
    (hXA : blockDisjoint (X, xo.eval, 2 * (n * n)) (A, ao.eval, 2 * (n * n)) = true)
    (hXp : blockDisjoint (X, xo.eval, 2 * (n * n)) (par, po.eval, 2) = true)
    (h : exec I (newtonSchulzSignProg p mm (.const n) (.const F) A ao par po X xo).run st =
      some st') :
    pairLayout.Holds st'.store p X xo.eval
        (newtonSchulzSign (I.sem.toFloatMachine p toNat mmR qrR unif normal) ε b F A₀) ∧
      (∀ q b' i, blockDisjoint (b', i, 1) (X, xo.eval, 2 * (n * n)) = true →
        st'.store.read q b' i = st.store.read q b' i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  sorry

/-- **The refinement of the Newton–Schulz sign program, success**: under the standard model at
$u$ with every value in range, $u(p) < 1$ and an exact literal $1$, if kernel `mm` of `I` is the
routine `mmR` on interleaved pairs, $n \ge 1$, $b$ decodes to a nonzero value, the output block at
`X` (tag `p`) has $2n^2$ cells, and the machine's test passes at some iterate $k \le F$ of the
rounded step from `M.hermScale A b`, then the run of `NLAlib.newtonSchulzSignProg` at step limit
$F$ succeeds (hypotheses on the inputs as `NLAlib.holds_of_exec_newtonSchulzSignProg`). No
printed source.
Proof: the set-up succeeds (`lit_ok`, `bin_ok`: the literal $4n$ decodes to $4n(1 + \delta) \ne 0$
for $n \ge 1$, $\lvert\delta\rvert < 1$; `NLAlib.Computation.exists_exec_zhermScale` with `hb0`;
`NLAlib.exists_exec_newtonSchulzTestBlock`); then induction on the fuel with
`NLAlib.Computation.exec_whileFuel_of_eval_eq_succ` (scaffold): while the iterate index is below
$k$ the test of the current iterate may fail and the body succeeds
(`NLAlib.exists_exec_newtonSchulzStepBlock`, `NLAlib.exists_exec_newtonSchulzTestBlock`, the
value lemmas giving their hypotheses); at the first passing iterate (at most $k \le F$, so within
the fuel $F + 1$) the comparison is false (`NLAlib.Computation.IsRelErrSem.decidesFlags`,
scaffold) and the loop stops; the pops succeed. M, about 80 lines. -/
theorem exists_exec_newtonSchulzSignProg {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    {u : P → ℝ} {dec : P → K → ℝ} (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hlit : IsExactIntLit dec I.sem 1) (p : P) (hu : u p < 1) (n F : ℕ) (hn : 0 < n)
    {A par X : ℕ} {ao po xo : IExp ℕ} {st : St P K C} {A₀ : Matrix (Fin n) (Fin n) (K × K)}
    {ε b : K} (hA : pairLayout.Holds st.store p A ao.eval A₀)
    (hε : st.store.read p par po.eval = some ε) (hb : st.store.read p par (po.eval + 1) = some b)
    (hb0 : dec p b ≠ 0)
    (hXA : blockDisjoint (X, xo.eval, 2 * (n * n)) (A, ao.eval, 2 * (n * n)) = true)
    (hXp : blockDisjoint (X, xo.eval, 2 * (n * n)) (par, po.eval, 2) = true)
    (hX : ∃ len, st.store.shape[X]? = some (p, len) ∧ xo.eval + 2 * (n * n) ≤ len)
    (htest : ∃ k ≤ F, newtonSchulzTest (I.sem.toFloatMachine p toNat mmR qrR unif normal)
      ((I.sem.toFloatMachine p toNat mmR qrR unif normal).div ε
        ((I.sem.toFloatMachine p toNat mmR qrR unif normal).ofNat (4 * n)))
      ((newtonSchulzRounded (I.sem.toFloatMachine p toNat mmR qrR unif normal))^[k]
        ((I.sem.toFloatMachine p toNat mmR qrR unif normal).hermScale A₀ b)) = true) :
    ∃ st', exec I (newtonSchulzSignProg p mm (.const n) (.const F) A ao par po X xo).run st =
      some st' := by
  sorry

/-! ### The registered tree -/

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- **The registered tree instantiates to the builder**: at the sizes $N$ and $(F)$ the tree
`NLAlib.newtonSchulzSignProg.compiled` is `NLAlib.newtonSchulzSignProg` on the declared buffers
$0$, $1$, $2$ from offset $0$. No printed source.
Proof: `rfl`, the instantiation equation of a compiled family (as for the Gram–Schmidt
tree). S, 1 line. -/
theorem newtonSchulzSignProg.toStmt_compiled (p : P) (mm : ι) (N : ℕ) (n : Fin 1 → ℕ) :
    (newtonSchulzSignProg.compiled p mm).toStmt N n =
      ProgFamily.inst (r := 1) (b := 3) (fun _ _ N n h =>
        (newtonSchulzSignProg p mm N (n 0) (h 0) 0 (h 1) 0 (h 2) 0).run) N n := by
  rfl

/-- **The registered tree computes `newtonSchulzSign`**: if kernel `mm` of `I` is the routine
`mmR` on interleaved pairs and the semantics decides flags at `p`, a successful run of the tree
`NLAlib.newtonSchulzSignProg.compiled` at the sizes $N$ and $(F)$ from the initial state with the
stored $\mathbf{A}$, the stored $\varepsilon$, $b$ and $2N^2$ empty cells as declared buffers
ends with declared buffer $2$ holding $\mathsf{newtonSchulzSign}(\mathbf{A}, \varepsilon, b)$ on
the machine of the semantics with product `mmR`, step limit $F$. No printed source.
Proof: `NLAlib.Computation.Prog.exec_eq_exec_toStmt`, `NLAlib.newtonSchulzSignProg.toStmt_compiled`,
then `NLAlib.holds_of_exec_newtonSchulzSignProg` with
`NLAlib.Computation.EntryLayout.holds_inputState` (scaffold) and the reads of declared buffer $1$
(`NLAlib.Computation.inputState`); the disjointness hypotheses hold between distinct buffers
(`blockDisjoint`, `bne_iff_ne`). S, about 15 lines. -/
theorem newtonSchulzSignProg.holds_of_exec_compiled {mm : ι}
    (hmm : IsMatMulKernel I mm pairLayout mmR) (p : P) (hflag : I.sem.DecidesFlags p) (N F : ℕ)
    (A₀ : Matrix (Fin N) (Fin N) (K × K)) (ε b : K) {st' : St P K C}
    (h : (newtonSchulzSignProg.compiled p mm).exec I N ![F]
      (inputState p [(pairLayout.toArray A₀).map some, #[some ε, some b],
        Array.replicate (2 * (N * N)) none]) = some st') :
    pairLayout.Holds st'.store p 2 0
      (newtonSchulzSign (I.sem.toFloatMachine p toNat mmR qrR unif normal) ε b F A₀) := by
  rw [Prog.exec_eq_exec_toStmt, newtonSchulzSignProg.toStmt_compiled] at h
  set bufs : List (Array (Option K)) := [(pairLayout.toArray A₀).map some, #[some ε, some b],
    Array.replicate (2 * (N * N)) none] with hbufs
  have hA := EntryLayout.holds_inputState (C := C) pairLayout p (bufs := bufs) (k := 0) (Y := A₀)
    rfl
  have hε : (inputState (C := C) p bufs).store.read p 1 0 = some ε := by
    simp [inputState, Store.read, bufs]
  have hb1 : (inputState (C := C) p bufs).store.read p 1 (0 + 1) = some b := by
    simp [inputState, Store.read, bufs]
  have h' : exec I (newtonSchulzSignProg p mm (.const N) (.const F) 0 0 1 0 2 0).run
      (inputState p bufs) = some st' := h
  exact (holds_of_exec_newtonSchulzSignProg hmm p hflag N F hA hε hb1
    (by simp [blockDisjoint]) (by simp [blockDisjoint]) h').1

/-- **The registered tree succeeds** under the standard model at $u$ with every value in range,
$u(p) < 1$ and an exact literal $1$, if kernel `mm` of `I` is the routine `mmR` on interleaved
pairs, $N \ge 1$, $b$ decodes to a nonzero value and the machine's test passes at some iterate
$k \le F$ (as `NLAlib.exists_exec_newtonSchulzSignProg`), from the initial state of
`NLAlib.newtonSchulzSignProg.holds_of_exec_compiled`. No printed source.
Proof: as `NLAlib.newtonSchulzSignProg.holds_of_exec_compiled`, with
`NLAlib.exists_exec_newtonSchulzSignProg`; declared buffer $2$ has $2N^2$ cells at tag `p`
(`NLAlib.Computation.inputState`, `Array.size_replicate`). S, about 15 lines. -/
theorem newtonSchulzSignProg.exists_exec_compiled {mm : ι}
    (hmm : IsMatMulKernel I mm pairLayout mmR) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hlit : IsExactIntLit dec I.sem 1)
    (p : P) (hu : u p < 1) (N F : ℕ) (hN : 0 < N) (A₀ : Matrix (Fin N) (Fin N) (K × K))
    (ε b : K) (hb0 : dec p b ≠ 0)
    (htest : ∃ k ≤ F, newtonSchulzTest (I.sem.toFloatMachine p toNat mmR qrR unif normal)
      ((I.sem.toFloatMachine p toNat mmR qrR unif normal).div ε
        ((I.sem.toFloatMachine p toNat mmR qrR unif normal).ofNat (4 * N)))
      ((newtonSchulzRounded (I.sem.toFloatMachine p toNat mmR qrR unif normal))^[k]
        ((I.sem.toFloatMachine p toNat mmR qrR unif normal).hermScale A₀ b)) = true) :
    ∃ st' : St P K C, (newtonSchulzSignProg.compiled p mm).exec I N ![F]
      (inputState p [(pairLayout.toArray A₀).map some, #[some ε, some b],
        Array.replicate (2 * (N * N)) none]) = some st' := by
  rw [Prog.exec_eq_exec_toStmt, newtonSchulzSignProg.toStmt_compiled]
  have hA := EntryLayout.holds_inputState (C := C) pairLayout p (k := 0) (Y := A₀)
    (bufs := [(pairLayout.toArray A₀).map some, #[some ε, some b],
      Array.replicate (2 * (N * N)) none]) rfl
  have hε : (inputState (C := C) p [(pairLayout.toArray A₀).map some, #[some ε, some b],
      Array.replicate (2 * (N * N)) none]).store.read p 1 0 = some ε := by
    simp [inputState, Store.read]
  have hb : (inputState (C := C) p [(pairLayout.toArray A₀).map some, #[some ε, some b],
      Array.replicate (2 * (N * N)) none]).store.read p 1 (0 + 1) = some b := by
    simp [inputState, Store.read]
  obtain ⟨st', h⟩ := exists_exec_newtonSchulzSignProg hmm hsem hlit p hu N F hN
    (A := 0) (par := 1) (X := 2) (ao := .const 0) (po := .const 0) (xo := .const 0)
    (A₀ := A₀) (ε := ε) (b := b) hA hε hb hb0
    (by simp [blockDisjoint]) (by simp [blockDisjoint])
    ⟨2 * (N * N), by simp [inputState, Store.shape], by simp⟩ htest
  exact ⟨st', h⟩

/-- Twice the sum of the indices below $N$ is at most $N^2$. -/
private theorem two_mul_sum_range_le (N : ℕ) : 2 * (List.range N).sum ≤ N * N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.sum_append, List.sum_singleton]
    nlinarith

/-- **The counts and the memory of the registered tree**: under the standard charge (one per
operation), every successful run of `NLAlib.newtonSchulzSignProg.compiled` at the sizes $N$ and
$(F)$ adds at most `NLAlib.newtonSchulzSignCount p mm N F` to the counts and raises the peak
memory at tag `p` by at most the $4N^2 + 5$ scratch cells above the current memory (by nothing at
any other tag). No printed source.
Proof: `NLAlib.Computation.Prog.bounds_staticCost_of_exec_eq_some`; the static cost of the tree
is computed by `NLAlib.Computation.FStmt.staticCost` (`simp` with
`NLAlib.Computation.StaticCost.seq`, `NLAlib.Computation.StaticCost.repetitions`,
`NLAlib.Computation.StaticCost.sequence`, `NLAlib.Computation.StaticCost.branch`): one set-up and
test plus $F + 1$ repetitions of a comparison, a step and a test, each kind at most
$4N^2 + 4N + 4$ times per term (the strict triangle has $N(N - 1)/2$ entries,
`Finset.sum_range_id_mul_two`) and two kernel calls; compare kind by kind
(`Finsupp.le_def`). M, about 70 lines. -/
theorem newtonSchulzSignProg.cnt_le_of_exec_compiled {mm : ι} {I : Interp P ι K (OpCount P ι)}
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (p : P) (N F : ℕ)
    {st st' : St P K (OpCount P ι)}
    (h : (newtonSchulzSignProg.compiled p mm).exec I N ![F] st = some st') :
    st'.cnt ≤ st.cnt + newtonSchulzSignCount p mm N F ∧
      ∀ q, st'.peak q ≤ max (st.peak q) (st.cur q + if q = p then 4 * (N * N) + 5 else 0) := by
  have hb := (newtonSchulzSignProg.compiled p mm).bounds_staticCost_of_exec_eq_some I N ![F] h
  have hcharge : I.charge = fun k => Finsupp.single k 1 := funext hc
  have hb' := hb.mono (b := ⟨newtonSchulzSignCount p mm N F,
    fun q => if q = p then 4 * (N * N) + 5 else 0, _⟩) ?_ ?_ le_rfl
  · exact ⟨hb'.count, hb'.peak⟩
  · rw [hcharge]
    intro k
    change (FStmt.staticCost (fun k => Finsupp.single k 1) I.width
      (newtonSchulzSignProg.compiled (ι := ι) p mm) (Fin.cons N ![F])).count k ≤ _
    change (StaticCost.seq _ _).count k ≤ _
    simp only [FStmt.staticCost, StaticCost.seq, StaticCost.branch, StaticCost.alloc,
      StaticCost.step, StaticCost.zero, StaticCost.repetitions, StaticCost.sequence_count_apply,
      Instr.kind, Instr.subst, IExp.evalIn, Finsupp.add_apply, Finsupp.sup_apply,
      Finsupp.smul_apply, List.map_const', List.sum_replicate, List.length_range,
      Finsupp.zero_apply]
    simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Fin.cons_zero, Fin.cons_one,
      Matrix.Fin.cons_vecCons, Matrix.Fin.snoc_vecCons, Matrix.Fin.snoc_vecEmpty,
      Matrix.cons_val_fin_one, Fin.val_eq_zero, Fin.mk_one, add_zero, zero_add, smul_eq_mul,
      List.map_cons, List.map_nil,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    have h2 : ∀ x : ℕ, ![N, F, x] ⟨2, by omega⟩ = x := fun _ => rfl
    simp only [h2, IExp.evalIn, Matrix.cons_val_zero, newtonSchulzSignCount, Finsupp.smul_apply,
      Finsupp.add_apply, smul_eq_mul, List.sum_map_mul_right, List.map_id']
    have hS := two_mul_sum_range_le N
    generalize (List.range N).sum = S at hS ⊢
    have hFS := Nat.mul_le_mul_left F hS
    classical
    cases k <;> simp only [Finsupp.single_apply, OpKind.bin.injEq, OpKind.un.injEq,
      OpKind.lit.injEq, OpKind.cmp.injEq, OpKind.copy.injEq, OpKind.kcall.injEq, reduceCtorEq,
      ite_false, mul_zero, add_zero, zero_add, max_self, Nat.zero_max, Nat.max_zero, le_refl]
    all_goals split_ifs <;> nlinarith [hS, hFS]
  · intro q
    change (FStmt.staticCost I.charge I.width
      (newtonSchulzSignProg.compiled (ι := ι) p mm) (Fin.cons N ![F])).cells q ≤ _
    change (StaticCost.seq _ _).cells q ≤ _
    simp only [FStmt.staticCost, StaticCost.seq, StaticCost.alloc, StaticCost.branch,
      StaticCost.step, StaticCost.zero, StaticCost.repetitions, IExp.evalIn, Instr.kind,
      Instr.subst]
    simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Fin.cons_zero,
      Matrix.Fin.cons_vecCons, Matrix.Fin.snoc_vecCons, Matrix.Fin.snoc_vecEmpty,
      StaticCost.sequence_cells_mk, List.range_eq_nil, max_self, add_zero, Nat.max_zero,
      ite_self]
    split_ifs <;> omega

end NLAlib
