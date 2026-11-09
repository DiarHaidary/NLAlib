/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.KernelCall
public import NLAlib.Matrix.Computation.NewtonSchulzSign
public import NLAlib.Matrix.Computation.NewtonSchulzSignProgramTree
public import NLAlib.Matrix.Computation.KernelContracts
public import NLAlib.Matrix.Computation.PairKernels.HermAvg
public import NLAlib.Matrix.Computation.PairKernels.BoxTest
public import NLAlib.Computation.StaticCost
public import NLAlib.Computation.BLASCongr

/-!
# The blocks of the Newton–Schulz sign program

The test block and the step block of `NLAlib.newtonSchulzSignProg` compute the stopping test and one
step of `NLAlib.newtonSchulzSign` on the machine of the semantics
(`NLAlib.Computation.ScalarSem.toFloatMachine`), under any interpretation whose kernel `mm` is a
routine on interleaved pairs (`NLAlib.Computation.IsMatMulKernel`) and whose semantics decides
flags; they succeed under the standard model with every value in range. The `whileFuel` loop of the
program computes `NLAlib.newtonSchulzLoop`. The two blocks run at an index expression as at the
constant of its value.

## Main results

* `NLAlib.holds_of_exec_newtonSchulzTestBlock`, `NLAlib.exists_exec_newtonSchulzTestBlock`,
  `NLAlib.holds_of_exec_newtonSchulzStepBlock`, `NLAlib.exists_exec_newtonSchulzStepBlock`: the test
  and the step.
* `NLAlib.holds_of_exec_whileFuel_newtonSchulz`: the loop computes `NLAlib.newtonSchulzLoop`.
* `NLAlib.exec_newtonSchulzTestBlock_congr`, `NLAlib.exec_newtonSchulzStepBlock_congr`: the blocks
  at index expressions.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {Su Sg : Type} {toNat : K → ℕ} {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}
  {unif : K → Su → K} {normal : Sg → K × K}

/-- The test block computes the machine's test: if kernel `mm` of `I` is the routine `mmR` on
interleaved pairs, a successful run of `NLAlib.newtonSchulzTestBlock` from a state whose block at
`X` holds the complex $n \times n$ matrix $\mathbf{A}$ and whose cells `one`, `lo`, `hi` hold the
machine's one, $-\eta$ and $\eta$ (`M` the machine of the semantics at `p` with product `mmR`),
with the scratch buffer `W` distinct from `X` and from the scratch buffer `V`, the cells outside
`W` and `V` and the flag cell distinct from `lo` and `hi`, ends with `W` holding
$\mathrm{mm}(\mathbf{A}, \mathbf{A})$, `V` holding the shift `M.hermShift (mmR A A) M.one`, and
the flag holding the machine's zero if `NLAlib.newtonSchulzTest M η A` and its one otherwise;
every cell outside `W`, `V` and the flag is unchanged, the store shape and the tape positions
too. No printed source. -/
theorem holds_of_exec_newtonSchulzTestBlock {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (p : P) (n : ℕ) {X W V : ℕ} {xo : IExp ℕ} {one lo hi f : Cell ℕ ℕ} {η : K}
    {st st' : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)}
    (hA : pairLayout.Holds st.store p X xo.eval A)
    (hone : st.store.read p one.buf one.idx.eval =
      some (I.sem.toFloatMachine p toNat mmR qrR unif normal).one)
    (hlo : st.store.read p lo.buf lo.idx.eval =
      some ((I.sem.toFloatMachine p toNat mmR qrR unif normal).neg η))
    (hhi : st.store.read p hi.buf hi.idx.eval = some η)
    (hWX : W ≠ X) (hWV : W ≠ V)
    (hcells : ∀ c ∈ [one, lo, hi, f], c.buf ≠ W ∧ c.buf ≠ V)
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

/-- The test block succeeds under the standard model with every value in range, when the
buffers `W` and `V` at tag `p` have $2n^2$ cells and the flag can be written (hypotheses as
`NLAlib.holds_of_exec_newtonSchulzTestBlock`). No printed source. -/
theorem exists_exec_newtonSchulzTestBlock {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    {u : P → ℝ} {dec : P → K → ℝ} (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (p : P) (n : ℕ) {X W V : ℕ} {xo : IExp ℕ} {one lo hi f : Cell ℕ ℕ} {cone ℓ η : K}
    {st : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)}
    (hA : pairLayout.Holds st.store p X xo.eval A)
    (hone : st.store.read p one.buf one.idx.eval = some cone)
    (hlo : st.store.read p lo.buf lo.idx.eval = some ℓ)
    (hhi : st.store.read p hi.buf hi.idx.eval = some η)
    (hWX : W ≠ X) (hWV : W ≠ V)
    (hcells : ∀ c ∈ [one, lo, hi, f], c.buf ≠ W ∧ c.buf ≠ V)
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
    change ((I.sem.lit p ((e.eval : ℕ) : ℚ)).getD default) = v
    rw [hv]; rfl
  refine ⟨?_, fun q b i hne => ?_, Store.shape_of_write_eq_some hw, rfl⟩
  · rw [hofn]; exact Store.read_of_write_eq_some hw
  · exact Store.read_of_write_eq_some_of_ne hw (not_and_or.mp hne)

/-- The step block computes the machine's rounded step: if kernel `mm` of `I` is the routine
`mmR` on interleaved pairs, a successful run of `NLAlib.newtonSchulzStepBlock` from a state whose
block at `X` holds the complex $n \times n$ matrix $\mathbf{A}$ and whose scratch buffer `W`
holds $\mathrm{mm}(\mathbf{A}, \mathbf{A})$, with `W`, `V` distinct from `X` and from each other
and the cell `c` outside `W`, `V` and the block at `X`, ends with the block at `X` holding
`NLAlib.newtonSchulzRounded M A` (`M` the machine of the semantics at `p` with product `mmR`);
every cell outside the block at `X`, the buffers `W`, `V` and the cell `c` is unchanged, the store
shape and the tape positions too. No printed source. -/
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
    rintro i h1 h2 ⟨hb, hi⟩
    simp only [blockDisjoint, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hcX
    omega
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

omit [AddMonoid C] [Inhabited K] in
private theorem stepBlock_shape {s : Store P K} {p : P} {b off n : ℕ}
    {Y : Matrix (Fin n) (Fin n) (K × K)} (hY : pairLayout.Holds s p b off Y) (hn : 0 < n) :
    ∃ len, s.shape[b]? = some (p, len) ∧ off + 2 * (n * n) ≤ len := by
  obtain ⟨arr, hr⟩ : ∃ arr, s.readBlock p b off (n * n * 2) = some arr :=
    ⟨_, (EntryLayout.holds_iff_readBlock_eq_some pairLayout s p b off Y).1 hY⟩
  have hN : 0 < n * n := Nat.mul_pos hn hn
  have h₁ := Store.read_of_readBlock_eq_some_of_lt hr (m := n * n * 2 - 1) (by omega)
  rw [Array.getElem?_eq_getElem (by rw [Store.size_of_readBlock_eq_some hr]; omega)] at h₁
  obtain ⟨len, hsh, hlt⟩ := Store.exists_getElem?_shape_of_read_eq_some h₁
  exact ⟨len, hsh, by omega⟩

omit [AddMonoid C] [Inhabited K] in
private theorem stepBlock_holds_write {s s' : Store P K} {p : P} {b off n cb ci : ℕ} {v : K}
    {Y : Matrix (Fin n) (Fin n) (K × K)} (hY : pairLayout.Holds s p b off Y)
    (hw : s.write p cb ci v = some s')
    (hd : blockDisjoint (cb, ci, 1) (b, off, 2 * (n * n)) = true) :
    pairLayout.Holds s' p b off Y := by
  intro i j t
  have hij : 2 * (i + n * j) + t < 2 * (n * n) := by
    have ht : (t : ℕ) < 2 := t.2
    nlinarith [i.2, j.2]
  rw [Store.read_of_write_eq_some_of_ne hw ?_]
  · exact hY i j t
  · simp only [blockDisjoint, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hd
    change b ≠ cb ∨ off + (2 * (i + n * j) + t) ≠ ci
    omega

/-- The step block succeeds under the standard model at $u$ with every value in range and
$u(p) < 1$, when the buffers `W` and `V` at tag `p` have $2n^2$ cells and the cell `c` can be
written (hypotheses as `NLAlib.holds_of_exec_newtonSchulzStepBlock`). No printed source. -/
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
  have hd : ∀ {b b' : ℕ} (o o' l l' : ℕ), b ≠ b' → blockDisjoint (b, o, l) (b', o', l') = true :=
    fun _ _ _ _ h => by simp [blockDisjoint, h]
  change ∃ st', exec I (.seq (.instr (.litIdx p c 3)) (.seq (.named _ _ _) (.seq (.named _ _ _)
    (.seq (.kcall mm p [.const n, .const n, .const n] [(X, xo), (V, 0)] [(W, 0)])
    (.seq (.instr (.litIdx p c 4)) (zhermAvg (ι := ι) p (.const n) W 0 c X xo).run))))) st =
    some st'
  -- the literal `3`
  obtain ⟨v₃, hv₃⟩ := hsem.lit_ok p ((3 : IExp ℕ).eval : ℚ) trivial
  obtain ⟨s₀, hs₀⟩ := hc
  obtain ⟨s₁, hs₁⟩ := Store.exists_write_eq_some_of_shape_eq rfl hs₀ v₃
  rw [exec_seq_instr_litIdx I hv₃ hs₁, exec_seq]
  have hsh₁ : s₁.shape = st.store.shape := Store.shape_of_write_eq_some hs₁
  have hW₁ := stepBlock_holds_write hW hs₁ (hd _ _ _ _ hcW)
  -- the shift by `3`
  obtain ⟨st₂, h₂⟩ := exists_exec_zhermShift (I := I) (ι := ι) p n (X := W) (xo := 0) (c := c)
    (Y := V) (yo := 0) (st := { st with store := s₁, cnt := _ }) hW₁
    (Store.read_of_write_eq_some hs₁) (hd _ _ _ _ hWV.symm) (hd _ _ _ _ hcV) hsem
    (by rw [hsh₁, IExp.eval_zero]; simpa only [zero_add] using hV)
  obtain ⟨hV₂, hfr₂, hsh₂, -⟩ := holds_of_exec_zhermShift (toNat := fun _ => 0) (mmR := mmR)
    (qrR := fun {_ _} B => (fun _ _ => default, B)) (unif := fun k (_ : Unit) => k)
    (normal := fun (_ : Unit) => default) p n hW₁ (Store.read_of_write_eq_some hs₁)
    (hd _ _ _ _ hWV.symm) (hd _ _ _ _ hcV) h₂
  change exec I (.seq (.named _ _ _) .skip) _ = some st₂ at h₂
  rw [exec_seq_skip] at h₂
  rw [h₂, Option.bind_some, exec_seq]
  -- the negation in place
  obtain ⟨st₃, h₃⟩ := exists_exec_zneg (I := I) (ι := ι) p n n (X := V) (xo := 0) (Y := V)
    (yo := 0) hV₂ (Or.inr ⟨rfl, rfl⟩) hsem
    (by rw [hsh₂, hsh₁, IExp.eval_zero]; simpa only [zero_add] using hV)
  obtain ⟨hV₃, hfr₃, hsh₃, -⟩ := holds_of_exec_zneg (toNat := fun _ => 0) (mmR := mmR)
    (qrR := fun {_ _} B => (fun _ _ => default, B)) (unif := fun k (_ : Unit) => k)
    (normal := fun (_ : Unit) => default) p n n hV₂ (Or.inr ⟨rfl, rfl⟩) h₃
  change exec I (.seq (.named _ _ _) .skip) _ = some st₃ at h₃
  rw [exec_seq_skip] at h₃
  rw [h₃, Option.bind_some, exec_seq, exec_kcall]
  -- the product
  have hA₃ : pairLayout.Holds st₃.store p X xo.eval A :=
    (stepBlock_holds_write hA hs₁ hcX).of_forall_read_eq fun i _ _ =>
      (hfr₃ _ _ _ (hd _ _ _ _ hVX.symm)).trans (hfr₂ _ _ _ (hd _ _ _ _ hVX.symm))
  have hsh : st₃.store.shape = st.store.shape := hsh₃.trans (hsh₂.trans hsh₁)
  have hpos : ∀ i, i < n * n * 2 → 0 < n := fun i hi =>
    Nat.pos_of_ne_zero (by rintro rfl; simp at hi)
  obtain ⟨s₄, hk, hsh₄⟩ : ∃ s₄, I.kcallStore mm p [n, n, n] [(X, xo.eval), (V, 0)] [(W, 0)]
      st₃.store = some s₄ ∧ s₄.shape = st.store.shape := by
    rw [hmm.kcallStore_eq p ((EntryLayout.holds_iff_readBlock_eq_some _ _ _ _ _ _).1 hA₃)
      ((EntryLayout.holds_iff_readBlock_eq_some _ _ _ _ _ _).1 hV₃) (hd _ _ _ _ hWX)
      (hd _ _ _ _ hWV)]
    refine (Store.exists_writeBlock_eq_some_of_getElem?_shape fun i hi => ?_).elim
      fun s₄ hs₄ => ⟨s₄, hs₄, (Store.shape_of_writeBlock_eq_some hs₄).trans hsh⟩
    · rw [EntryLayout.size_toArray] at hi
      obtain ⟨len, hl, hle⟩ := stepBlock_shape hW (hpos i hi)
      refine ⟨len, by rw [hsh]; exact hl, ?_⟩
      change i < n * n * 2 at hi
      omega
  obtain ⟨hW₄, -⟩ := hmm.holds_of_kcallStore_eq_some pairLayout.get_put p (a := (X, xo.eval))
    (b := (V, 0)) (c := (W, 0)) hA₃ hV₃ (hd _ _ _ _ hWX) (hd _ _ _ _ hWV) hk
  erw [hk]
  rw [Option.map_some, Option.bind_some]
  -- the literal `4`
  obtain ⟨v₄, hv₄⟩ := hsem.lit_ok p ((4 : IExp ℕ).eval : ℚ) trivial
  obtain ⟨s₅, hs₅⟩ := Store.exists_write_eq_some_of_shape_eq hsh₄ hs₀ v₄
  rw [exec_seq_instr_litIdx I hv₄ hs₅]
  have hv₄0 : dec p v₄ ≠ 0 := by
    obtain ⟨δ, hδ, hdec⟩ := hsem.lit_err p _ v₄ hv₄
    rw [hdec]
    refine mul_ne_zero (by simp) ?_
    linarith [(abs_lt.mp (hδ.trans_lt hu)).1]
  -- the Hermitian average
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨_, rfl⟩
  obtain ⟨len, hl, hle⟩ := stepBlock_shape hA hn
  exact exists_exec_zhermAvg (I := I) (ι := ι) p n (X := W) (xo := 0) (c := c) (Y := X)
    (yo := xo) hsem hv₄0 (stepBlock_holds_write hW₄ hs₅ (hd _ _ _ _ hcW))
    (Store.read_of_write_eq_some hs₅) (hd _ _ _ _ hWX.symm) hcX
    ⟨len, by rw [Store.shape_of_write_eq_some hs₅, hsh₄]; exact hl, hle⟩

omit [Inhabited K] in
private theorem whileNS_unroll {fuel : IExp ℕ} {j : ℕ} (hfuel : fuel.eval = j + 1) {p : P}
    {t : ℕ} {body : Stmt P ι ℕ ℕ} {st st' : St P K C} {z o : K}
    (hzo : I.sem.cmp p .eq z o = some false) (hoo : I.sem.cmp p .eq o o = some true) {b : Bool}
    (hf : st.store.read p t 1 = some (if b then z else o))
    (hone : st.store.read p t 3 = some o)
    (h : exec I (.whileFuel fuel p .eq ⟨t, 1⟩ ⟨t, 3⟩ body) st = some st') :
    (b = true ∧ st'.store = st.store ∧ st'.pos = st.pos) ∨
      (b = false ∧ ∃ st₁, exec I body { st with cnt := st.cnt + I.charge (.cmp p) } = some st₁ ∧
        exec I (.whileFuel (.const j) p .eq ⟨t, 1⟩ ⟨t, 3⟩ body) st₁ = some st') := by
  rw [exec_whileFuel_of_eval_eq_succ I hfuel] at h
  cases b
  · simp only [cmpStep, IExp.eval_ofNat, hf, hone, hoo, Bool.false_eq_true, if_false,
      Option.bind_some, Option.map_some, if_true] at h
    exact Or.inr ⟨rfl, Option.bind_eq_some_iff.mp h⟩
  · simp only [cmpStep, IExp.eval_ofNat, hf, hone, hzo, if_true, Option.bind_some,
      Option.map_some, Bool.false_eq_true, if_false, Option.some.injEq] at h
    exact Or.inl ⟨rfl, by rw [← h], by rw [← h]⟩

omit [Inhabited K] in
/-- Runs of builders followed by a continuation compose: if the runs of `a` and of `b`, each
followed by any `f`, are the run of the builder and then of `f`, so is the run of `a` then `b`. -/
theorem exec_run_bind_bind {a b : Builder P ι ℕ ℕ Unit}
    (ha : ∀ (f : Unit → Builder P ι ℕ ℕ Unit) (st : St P K C),
      exec I (a >>= f).run st = (exec I a.run st).bind (exec I (f ()).run))
    (hb : ∀ (f : Unit → Builder P ι ℕ ℕ Unit) (st : St P K C),
      exec I (b >>= f).run st = (exec I b.run st).bind (exec I (f ()).run))
    (f : Unit → Builder P ι ℕ ℕ Unit) (st : St P K C) :
    exec I ((a >>= fun _ => b) >>= f).run st =
      (exec I (a >>= fun _ => b).run st).bind (exec I (f ()).run) := by
  change exec I (a >>= fun _ => b >>= f).run st = _
  rw [ha, ha]
  simp only [Option.bind_assoc]
  congr 1
  funext out
  exact hb f out

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- Two distinct cells of one buffer are disjoint blocks. -/
theorem blockDisjoint_cell_of_ne {b i j : ℕ} (h : i ≠ j) :
    blockDisjoint (b, i, 1) (b, j, 1) = true := by
  simp only [blockDisjoint, bne_self_eq_false, Bool.false_or, Bool.or_eq_true,
    decide_eq_true_eq]
  omega

omit [Inhabited K] in
/-- The run of the Newton–Schulz test block followed by `f`: the run of the block, then the run
of `f`. No printed source. -/
theorem exec_run_bind_newtonSchulzTestBlock {p : P} {mm : ι} {n : IExp ℕ} {X : ℕ} {xo : IExp ℕ}
    {W V : ℕ} {one lo hi flag : Cell ℕ ℕ} (f : Unit → Builder P ι ℕ ℕ Unit) (st : St P K C) :
    exec I (newtonSchulzTestBlock p mm n X xo W V one lo hi flag >>= f).run st =
      (exec I (newtonSchulzTestBlock p mm n X xo W V one lo hi flag).run st).bind
        (exec I (f ()).run) := by
  unfold newtonSchulzTestBlock
  exact exec_run_bind_bind (fun f st => exec_run_bind I (fun _ => rfl) f st)
    (exec_run_bind_bind (fun f st => exec_run_bind I (fun _ => rfl) f st)
      (fun f st => exec_run_bind I (fun _ => rfl) f st)) f st

omit [Inhabited K] in
/-- The run of the Newton–Schulz step block followed by `f`: the run of the block, then the run
of `f`. No printed source. -/
theorem exec_run_bind_newtonSchulzStepBlock {p : P} {mm : ι} {n : IExp ℕ} {X : ℕ} {xo : IExp ℕ}
    {W V : ℕ} {c : Cell ℕ ℕ} (f : Unit → Builder P ι ℕ ℕ Unit) (st : St P K C) :
    exec I (newtonSchulzStepBlock p mm n X xo W V c >>= f).run st =
      (exec I (newtonSchulzStepBlock p mm n X xo W V c).run st).bind (exec I (f ()).run) := by
  have hs : ∀ (b : Builder P ι ℕ ℕ Unit) (S : Stmt P ι ℕ ℕ),
      (∀ k, ContT.run b k = .seq S (k ())) → ∀ (f : Unit → Builder P ι ℕ ℕ Unit) (st : St P K C),
        exec I (b >>= f).run st = (exec I b.run st).bind (exec I (f ()).run) :=
    fun _ _ hb f st => exec_run_bind I hb f st
  unfold newtonSchulzStepBlock
  exact exec_run_bind_bind (hs _ _ fun _ => rfl) (exec_run_bind_bind (hs _ _ fun _ => rfl)
    (exec_run_bind_bind (hs _ _ fun _ => rfl) (exec_run_bind_bind (hs _ _ fun _ => rfl)
      (exec_run_bind_bind (hs _ _ fun _ => rfl) (hs _ _ fun _ => rfl))))) f st

private theorem whileNS_body {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) (p : P) (n : ℕ)
    {X W V t : ℕ} {xo : IExp ℕ} {η : K} {st st₁ : St P K C}
    {A : Matrix (Fin n) (Fin n) (K × K)} (hA : pairLayout.Holds st.store p X xo.eval A)
    (hW : pairLayout.Holds st.store p W 0 (mmR A A)) (hη : st.store.read p t 0 = some η)
    (hone : st.store.read p t 3 = some (I.sem.toFloatMachine p toNat mmR qrR unif normal).one)
    (hlo : st.store.read p t 4 =
      some ((I.sem.toFloatMachine p toNat mmR qrR unif normal).neg η))
    (hWX : W ≠ X) (hVX : V ≠ X) (hWV : W ≠ V) (htX : t ≠ X) (htW : t ≠ W) (htV : t ≠ V)
    (h : exec I (Builder.run do
      newtonSchulzStepBlock p mm (.const n) X xo W V ⟨t, 2⟩
      newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩) st =
        some st₁) :
    let M := I.sem.toFloatMachine p toNat mmR qrR unif normal
    pairLayout.Holds st₁.store p X xo.eval (newtonSchulzRounded M A) ∧
      pairLayout.Holds st₁.store p W 0 (mmR (newtonSchulzRounded M A) (newtonSchulzRounded M A)) ∧
      st₁.store.read p t 0 = some η ∧ st₁.store.read p t 3 = some M.one ∧
      st₁.store.read p t 4 = some (M.neg η) ∧
      st₁.store.read p t 1 = some
        (if newtonSchulzTest M η (newtonSchulzRounded M A) then M.zero else M.one) ∧
      (∀ q b i, b ≠ t → b ≠ W → b ≠ V →
        blockDisjoint (b, i, 1) (X, xo.eval, 2 * (n * n)) = true →
        st₁.store.read q b i = st.store.read q b i) ∧
      st₁.store.shape = st.store.shape ∧ st₁.pos = st.pos := by
  have hd : ∀ {b b' : ℕ} (o o' l l' : ℕ), b ≠ b' → blockDisjoint (b, o, l) (b', o', l') = true :=
    fun _ _ _ _ h => by simp [blockDisjoint, h]
  have hstep : ∀ (f : Unit → Builder P ι ℕ ℕ Unit) (σ : St P K C),
      exec I (newtonSchulzStepBlock p mm (.const n) X xo W V ⟨t, 2⟩ >>= f).run σ =
        (exec I (newtonSchulzStepBlock p mm (.const n) X xo W V ⟨t, 2⟩).run σ).bind
          (exec I (f ()).run) :=
    exec_run_bind_newtonSchulzStepBlock
  rw [hstep] at h
  obtain ⟨σ, hσ, h₁⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hXσ, hfrσ, hshσ, hposσ⟩ := holds_of_exec_newtonSchulzStepBlock (toNat := toNat)
    (qrR := qrR) (unif := unif) (normal := normal) hmm p n hA hW hWX hVX hWV htW htV
    (hd _ _ _ _ htX) hσ
  have hrσ : ∀ i, i ≠ 2 → σ.store.read p t i = st.store.read p t i := fun i hi =>
    hfrσ p t i htW htV (hd _ _ _ _ htX) (blockDisjoint_cell_of_ne hi)
  obtain ⟨hW₁, -, hf₁, hfr₁, hsh₁, hpos₁⟩ := holds_of_exec_newtonSchulzTestBlock (toNat := toNat)
    (qrR := qrR) (unif := unif) (normal := normal) hmm p n (one := ⟨t, 3⟩) (lo := ⟨t, 4⟩)
    (hi := ⟨t, 0⟩) (f := ⟨t, 1⟩) hXσ ((hrσ 3 (by omega)).trans hone)
    ((hrσ 4 (by omega)).trans hlo) ((hrσ 0 (by omega)).trans hη) hWX hWV
    (by simp [htW, htV]) (by simp [blockDisjoint]) (by simp [blockDisjoint]) h₁
  have hr₁ : ∀ i, i ≠ 1 → i ≠ 2 → st₁.store.read p t i = st.store.read p t i := fun i h1 h2 =>
    (hfr₁ p t i htW htV (blockDisjoint_cell_of_ne h1)).trans (hrσ i h2)
  refine ⟨hXσ.of_forall_read_eq fun i _ _ => hfr₁ _ _ _ hWX.symm hVX.symm (hd _ _ _ _ htX.symm),
    hW₁, (hr₁ 0 (by omega) (by omega)).trans hη, (hr₁ 3 (by omega) (by omega)).trans hone,
    (hr₁ 4 (by omega) (by omega)).trans hlo, hf₁, fun q b i hbt hbW hbV hbX => ?_,
    hsh₁.trans hshσ, hpos₁.trans hposσ⟩
  exact (hfr₁ q b i hbW hbV (hd _ _ _ _ hbt)).trans (hfrσ q b i hbW hbV hbX (hd _ _ _ _ hbt))

/-- The Newton–Schulz loop of the program computes `NLAlib.newtonSchulzLoop`: if kernel `mm`
of `I` is the routine `mmR` on interleaved pairs and the semantics decides flags at `p`, a
successful run of the `whileFuel` loop of `NLAlib.newtonSchulzSignProg` with fuel $j + 1$, from a
state whose block at `X` holds $\mathbf{A}$, whose scratch buffer `W` holds
$\mathrm{mm}(\mathbf{A}, \mathbf{A})$, whose cells $0$, $3$, $4$ of the scratch buffer `t` hold
$\eta$, the machine's one and $-\eta$, and whose cell $1$ holds the flag of the test of
$\mathbf{A}$, ends with the block at `X` holding `NLAlib.newtonSchulzLoop M η j A`; every cell
outside the block at `X` and the scratch buffers `t`, `W`, `V` is unchanged, the store shape and
the tape positions too. No printed source. -/
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
  obtain ⟨z, o, hz, ho, hzo, hoo⟩ := hflag
  have hM0 : (I.sem.toFloatMachine p toNat mmR qrR unif normal).zero = z := by
    simp [ScalarSem.toFloatMachine, hz]
  have hM1 : (I.sem.toFloatMachine p toNat mmR qrR unif normal).one = o := by
    simp [ScalarSem.toFloatMachine, ho]
  induction j generalizing fuel st A with
  | zero =>
    rcases whileNS_unroll hfuel hzo hoo (by rw [hf, hM0, hM1]) (by rw [hone, hM1]) h with
      ⟨-, hs, hp⟩ | ⟨-, st₁, -, h₂⟩
    · exact ⟨by rw [hs]; exact hA, fun q b i _ _ _ _ => by rw [hs], by rw [hs], hp⟩
    · rw [exec_whileFuel_of_eval_eq_zero I rfl] at h₂
      exact absurd h₂ (by simp)
  | succ k ih =>
    rcases whileNS_unroll hfuel hzo hoo (by rw [hf, hM0, hM1]) (by rw [hone, hM1]) h with
      ⟨ht, hs, hp⟩ | ⟨ht, st₁, h₁, h₂⟩
    · refine ⟨by rw [hs]; simpa [newtonSchulzLoop, ht] using hA, fun q b i _ _ _ _ => by rw [hs],
        by rw [hs], hp⟩
    · obtain ⟨hX₁, hW₁, hη₁, hone₁, hlo₁, hf₁, hfr₁, hsh₁, hpos₁⟩ :=
        whileNS_body hmm p n (st := { st with cnt := st.cnt + I.charge (.cmp p) }) hA hW hη hone hlo
          hWX hVX hWV htX htW htV h₁
      obtain ⟨hX', hfr', hsh', hpos'⟩ := ih (fuel := .const (k + 1)) rfl hX₁ hW₁ hη₁ hone₁ hlo₁
        hf₁ h₂
      refine ⟨by simpa [newtonSchulzLoop, ht] using hX', fun q b i h1 h2 h3 h4 =>
        (hfr' q b i h1 h2 h3 h4).trans (hfr₁ q b i h1 h2 h3 h4), hsh'.trans hsh₁,
        hpos'.trans hpos₁⟩

/-! ### The blocks as routine specifications -/

omit [Inhabited K] in
/-- The test block composes with what follows. -/
theorem executionComposable_newtonSchulzTestBlock (p : P) (mm : ι) (n : IExp ℕ) (X : ℕ)
    (xo : IExp ℕ) (W V : ℕ) (one lo hi f : Cell ℕ ℕ) :
    ExecutionComposable I (newtonSchulzTestBlock p mm n X xo W V one lo hi f) :=
  (executionComposable_stmt _).bind ((executionComposable_named _ _ _).bind
    (executionComposable_named _ _ _))

/-- **The test block as a routine specification**: from a state whose block at `X` holds the
complex $n \times n$ matrix $\mathbf{A}$ and whose cells `one`, `lo`, `hi` hold the machine's
one, $-\eta$ and $\eta$, with the scratch buffers `W`, `V` distinct from `X`, from each other and
from the cells' buffers, and the flag distinct from `lo` and `hi`, the run of
`NLAlib.newtonSchulzTestBlock` modifies only the blocks of `W`, `V` and the flag, ends with `W`
holding $\mathrm{mm}(\mathbf{A}, \mathbf{A})$, `V` its shift by the one and the flag the
machine's zero if `NLAlib.newtonSchulzTest M η A` and its one otherwise, and keeps the tape
positions; in mode `total` it also succeeds, given the standard model and the blocks writable.
No printed source. -/
theorem spec_newtonSchulzTestBlock {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) (md : Mode)
    {u : P → ℝ} {dec : P → K → ℝ} (hsem : md.Needs (IsRelErrSem u dec (fun _ _ => True) I.sem))
    (p : P) (n : ℕ) {X W V : ℕ} {xo : IExp ℕ} {one lo hi f : Cell ℕ ℕ} (η : K)
    (A : Matrix (Fin n) (Fin n) (K × K)) (hWX : W ≠ X) (hWV : W ≠ V)
    (hcells : ∀ c ∈ [one, lo, hi, f], c.buf ≠ W ∧ c.buf ≠ V)
    (hflo : blockDisjoint (f.buf, f.idx.eval, 1) (lo.buf, lo.idx.eval, 1) = true)
    (hfhi : blockDisjoint (f.buf, f.idx.eval, 1) (hi.buf, hi.idx.eval, 1) = true) :
    RoutineSpec md I (fun st => pairLayout.Holds st.store p X xo.eval A ∧
        st.store.read p one.buf one.idx.eval =
          some (I.sem.toFloatMachine p toNat mmR qrR unif normal).one ∧
        st.store.read p lo.buf lo.idx.eval =
          some ((I.sem.toFloatMachine p toNat mmR qrR unif normal).neg η) ∧
        st.store.read p hi.buf hi.idx.eval = some η ∧
        md.Needs (Writable st.store p W 0 (n * n * 2) ∧ Writable st.store p V 0 (n * n * 2) ∧
          Writable st.store p f.buf f.idx.eval 1))
      (newtonSchulzTestBlock p mm (.const n) X xo W V one lo hi f)
      [matBlock W 0 n n 2, matBlock V 0 n n 2, (f.buf, f.idx.eval, 1)] fun st st' =>
        pairLayout.Holds st'.store p W 0 (mmR A A) ∧
        pairLayout.Holds st'.store p V 0
          ((I.sem.toFloatMachine p toNat mmR qrR unif normal).hermShift (mmR A A)
            (I.sem.toFloatMachine p toNat mmR qrR unif normal).one) ∧
        st'.store.read p f.buf f.idx.eval = some
          (if newtonSchulzTest (I.sem.toFloatMachine p toNat mmR qrR unif normal) η A then
            (I.sem.toFloatMachine p toNat mmR qrR unif normal).zero else
            (I.sem.toFloatMachine p toNat mmR qrR unif normal).one) ∧ PosKept st st' := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hcells
  obtain ⟨⟨hoW, hoV⟩, ⟨hlW, hlV⟩, ⟨hhW, hhV⟩, ⟨hfW, hfV⟩⟩ := hcells
  refine ⟨executionComposable_newtonSchulzTestBlock _ _ _ _ _ _ _ _ _ _ _,
    fun st ⟨hA, h1, hl, hh, hN⟩ => ?_⟩
  obtain ⟨hNW, hNV, hNf⟩ := Mode.needs_and.mp hN |>.imp id Mode.needs_and.mp
  refine (RoutineSpec.stmt (hmm.spec_kcall pairLayout.get_put md p (X, xo) (X, xo) (W, 0) A
    A)).wp_bind
    (f := fun _ => zhermShift p (.const n) W 0 one V 0 >>= fun _ => zboxTest p (.const n) (.const n)
      V 0 lo hi f) ⟨hA, hA, blockDisjoint_of_fst_ne hWX, blockDisjoint_of_fst_ne hWX, hNW⟩
    fun st₁ hm₁ h₁ => ?_
  -- the cells `one`, `lo`, `hi` and the stored square, kept across the calls in one bundle
  have hC₁ := (readsOnly_cellsHold _).of_modifies (((cellsHold_nil _).cons hh).cons hl |>.cons h1)
    hm₁ (by fp_omega [hoW, hlW, hhW])
  refine (spec_zhermShift (toNat := toNat) (mmR := mmR) (qrR := qrR) (unif := unif)
      (normal := normal) md hsem p n (X := W) (Y := V) (xo := 0) (yo := 0) (c := one) _ _
      (blockDisjoint_of_fst_ne (Ne.symm hWV))).wp_bind_keep
    ((readsOnly_cellsHold _).and (readsOnly_pairLayoutHolds p W 0 _))
    (by fp_omega [hlV, hhV, hWV]) ⟨h₁.1, hC₁.read (.head _), hNV.mono (·.of_modifies hm₁)⟩
    ⟨hC₁.sub fun _ h => .tail _ h, h₁.1⟩ fun st₂ hm₂ h₂ ⟨hC₂, hW₂⟩ => ?_
  have hV₂ := h₂.1 (blockDisjoint_of_fst_ne hoV)
  exact (spec_zboxTest (toNat := toNat) (mmR := mmR) (qrR := qrR) (unif := unif)
      (normal := normal) md hsem p n n (X := V) (xo := 0) (lo := lo) (hi := hi) (f := f) _ _ _
      (blockDisjoint_of_fst_ne hfV) hflo hfhi).wp_run_keep
    ((readsOnly_pairLayoutHolds p W 0 _).and (readsOnly_pairLayoutHolds p V 0 _))
    (by fp_omega [hfW, hfV]) ⟨hV₂, hC₂.read (.head _), hC₂.read (.tail _ (.head _)),
      hNf.mono (·.of_modifies (hm₁.trans hm₂))⟩ ⟨hW₂, hV₂⟩
    fun st₃ hm₃ h₃ ⟨hW₃, hV₃⟩ => ⟨(hm₁.trans hm₂ |>.trans hm₃).mono
      (by simp [matBlock, pairLayout]),
      hW₃, hV₃, by unfold newtonSchulzTest; exact h₃.1, h₃.2.trans (h₂.2.trans h₁.2.2)⟩

omit [Inhabited K] in
/-- The step block composes with what follows. -/
theorem executionComposable_newtonSchulzStepBlock (p : P) (mm : ι) (n : IExp ℕ) (X : ℕ)
    (xo : IExp ℕ) (W V : ℕ) (c : Cell ℕ ℕ) :
    ExecutionComposable I (newtonSchulzStepBlock p mm n X xo W V c) :=
  (executionComposable_ins _).bind ((executionComposable_named _ _ _).bind
    ((executionComposable_named _ _ _).bind ((executionComposable_stmt _).bind
    ((executionComposable_ins _).bind (executionComposable_named _ _ _)))))

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- **A positive literal is nonzero under the standard model** at $u(p) < 1$: its stored value
decodes to $q(1 + \delta)$ with $\lvert \delta \rvert < 1$. No printed source. -/
theorem _root_.NLAlib.Computation.IsRelErrSem.dec_ne_zero_of_lit_eq_some {u : P → ℝ}
    {dec : P → K → ℝ} {safe : P → ℝ → Prop} {sem : ScalarSem P K}
    (hsem : IsRelErrSem u dec safe sem) {p : P} (hu : u p < 1) {q : ℚ} (hq : q ≠ 0) {v : K}
    (hv : sem.lit p q = some v) : dec p v ≠ 0 := by
  obtain ⟨δ, hδ, hdec⟩ := hsem.lit_err p _ v hv
  rw [hdec]
  exact mul_ne_zero (by exact_mod_cast hq) (by linarith [(abs_lt.mp (hδ.trans_lt hu)).1])

/-- **The step block as a routine specification**: from a state whose block at `X` holds the
complex $n \times n$ matrix $\mathbf{A}$ and whose scratch buffer `W` holds
$\mathrm{mm}(\mathbf{A}, \mathbf{A})$, with `W`, `V` distinct from `X` and from each other and
the cell `c` outside `W`, `V` and the block at `X`, the run of `NLAlib.newtonSchulzStepBlock`
modifies only the cell, the blocks of `V` and `W` and the block at `X`, which then holds
`NLAlib.newtonSchulzRounded M A`, and keeps the tape positions; in mode `total` it also succeeds,
given the standard model at $u(p) < 1$ and the blocks writable. No printed source. -/
theorem spec_newtonSchulzStepBlock {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) (md : Mode)
    {u : P → ℝ} {dec : P → K → ℝ} (p : P)
    (hsem : md.Needs (IsRelErrSem u dec (fun _ _ => True) I.sem ∧ u p < 1)) (n : ℕ)
    {X W V : ℕ} {xo : IExp ℕ} {c : Cell ℕ ℕ} (A : Matrix (Fin n) (Fin n) (K × K))
    (hWX : W ≠ X) (hVX : V ≠ X) (hWV : W ≠ V) (hcW : c.buf ≠ W) (hcV : c.buf ≠ V)
    (hcX : blockDisjoint (c.buf, c.idx.eval, 1) (matBlock X xo.eval n n 2) = true) :
    RoutineSpec md I (fun st => pairLayout.Holds st.store p X xo.eval A ∧
        pairLayout.Holds st.store p W 0 (mmR A A) ∧
        md.Needs (Writable st.store p c.buf c.idx.eval 1 ∧ Writable st.store p V 0 (n * n * 2) ∧
          Writable st.store p W 0 (n * n * 2) ∧ Writable st.store p X xo.eval (n * n * 2)))
      (newtonSchulzStepBlock p mm (.const n) X xo W V c)
      [(c.buf, c.idx.eval, 1), matBlock V 0 n n 2, matBlock W 0 n n 2, matBlock X xo.eval n n 2]
      fun st st' => pairLayout.Holds st'.store p X xo.eval
        (newtonSchulzRounded (I.sem.toFloatMachine p toNat mmR qrR unif normal) A) ∧
        PosKept st st' := by
  have hs := hsem.mono (·.1)
  refine ⟨executionComposable_newtonSchulzStepBlock _ _ _ _ _ _ _ _, fun st ⟨hA, hW, hN⟩ => ?_⟩
  have hw := fun {fp} {s : Store P K} (hm : Modifies fp st.store s) =>
    hN.mono fun h => (⟨h.1.of_modifies hm, h.2.1.of_modifies hm, h.2.2.1.of_modifies hm,
      h.2.2.2.of_modifies hm⟩ : _ ∧ _ ∧ _ ∧ _)
  have hlit := fun (q : ℕ) => (hsem.mono fun h => h.1.lit_ok p (q : ℚ) trivial)
  have hcWb : BlocksDisjoint [matBlock W 0 n n 2] [(c.buf, c.idx.eval, 1)] :=
    blocksDisjoint_singleton_of_fst_ne (by simpa [matBlock] using Ne.symm hcW)
  exact (RoutineSpec.ins (spec_litIdx_getD (e := 3))).wp_bind
    ((Mode.needs_and.mpr ⟨hlit 3, (hw (.refl [] _)).mono (·.1)⟩))
    fun st₁ hm₁ h₁ => (spec_zhermShift (toNat := toNat) (mmR := mmR) (qrR := qrR) (unif := unif)
      (normal := normal) md hs p n (X := W) (Y := V) (xo := 0) (yo := 0) (c := c) _ (mmR A A)
      (blockDisjoint_of_fst_ne (Ne.symm hWV))).wp_bind
      ⟨(readsOnly_entryLayoutHolds pairLayout p W 0 _).of_modifies hW hm₁ hcWb, h₁.1,
        (hw hm₁).mono (·.2.1)⟩
    fun st₂ hm₂ h₂ => (spec_zneg (toNat := toNat) (mmR := mmR) (qrR := qrR) (unif := unif)
      (normal := normal) md hs p n n (X := V) (Y := V) (xo := 0) (yo := 0) _
      (.inr ⟨rfl, rfl⟩)).wp_bind ⟨h₂.1 (blockDisjoint_of_fst_ne hcV),
        (hw (hm₁.trans hm₂)).mono (·.2.1)⟩
    fun st₃ hm₃ h₃ => (RoutineSpec.stmt (hmm.spec_kcall pairLayout.get_put md p (X, xo) (V, 0)
      (W, 0) A _)).wp_bind
      ⟨(show ReadsOnly _ [matBlock X xo.eval n n 2] from
        readsOnly_entryLayoutHolds pairLayout p X xo.eval A).of_modifies hA
        (hm₁.trans hm₂ |>.trans hm₃) (by fp_omega [hcX, hVX]), h₃.1,
        blockDisjoint_of_fst_ne hWX, blockDisjoint_of_fst_ne hWV,
        (hw (hm₁.trans hm₂ |>.trans hm₃)).mono (·.2.2.1)⟩
    fun st₄ hm₄ h₄ => (RoutineSpec.ins (spec_litIdx_getD (e := 4))).wp_bind
      ((Mode.needs_and.mpr ⟨hlit 4, (hw (hm₁.trans hm₂ |>.trans hm₃ |>.trans hm₄)).mono (·.1)⟩))
    fun st₅ hm₅ h₅ => (spec_zhermAvg (toNat := toNat) (mmR := mmR) (qrR := qrR) (unif := unif)
      (normal := normal) md hs p n (X := W) (Y := X) (xo := 0) (yo := xo) (c := c) _ _
      (blockDisjoint_of_fst_ne hWX.symm) hcX).wp_run
      ⟨(readsOnly_entryLayoutHolds pairLayout p W 0 _).of_modifies h₄.1 hm₅ hcWb, h₅.1,
        (hsem.elim fun ⟨hr, hu⟩ => (hw (hm₁.trans hm₂ |>.trans hm₃ |>.trans hm₄ |>.trans
          hm₅)).mono fun h => ⟨by
            obtain ⟨v, hv⟩ := hr.lit_ok p ((4 : ℕ) : ℚ) trivial
            change dec p ((I.sem.lit p ((4 : ℕ) : ℚ)).getD default) ≠ 0
            rw [hv]
            exact hr.dec_ne_zero_of_lit_eq_some hu (by norm_num) hv, h.2.2.2⟩)⟩
    fun st₆ hm₆ h₆ => ⟨(hm₁.trans hm₂ |>.trans hm₃ |>.trans hm₄ |>.trans hm₅ |>.trans hm₆).mono
      (by simp [matBlock, pairLayout]), h₆.1,
      h₆.2.trans (h₅.2.trans (h₄.2.2.trans (h₃.2.trans (h₂.2.trans h₁.2))))⟩

end NLAlib

/-! ### The blocks at index expressions -/

namespace NLAlib

open Computation

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] (I : Interp P ι K C) (p : P) (mm : ι)
  (st : St P K C)

/-- The Newton–Schulz test block at an index expression runs as at the constant of its value.
No printed source. -/
theorem exec_newtonSchulzTestBlock_congr (n : IExp ℕ) (X : ℕ) (xo : IExp ℕ) (W V : ℕ)
    (one lo hi f : Cell ℕ ℕ) :
    exec I (newtonSchulzTestBlock p mm n X xo W V one lo hi f).run st =
      exec I (newtonSchulzTestBlock p mm (.const n.eval) X xo W V one lo hi f).run st := by
  exact exec_eq_of_normIdx_eq I
    (by unfold newtonSchulzTestBlock zhermShift zmirror zboxTest; rfl) st

/-- The Newton–Schulz step block at an index expression runs as at the constant of its value.
No printed source. -/
theorem exec_newtonSchulzStepBlock_congr (n : IExp ℕ) (X : ℕ) (xo : IExp ℕ) (W V : ℕ)
    (c : Cell ℕ ℕ) :
    exec I (newtonSchulzStepBlock p mm n X xo W V c).run st =
      exec I (newtonSchulzStepBlock p mm (.const n.eval) X xo W V c).run st := by
  exact exec_eq_of_normIdx_eq I
    (by unfold newtonSchulzStepBlock zhermShift zmirror zneg zhermAvg; rfl) st

end NLAlib
