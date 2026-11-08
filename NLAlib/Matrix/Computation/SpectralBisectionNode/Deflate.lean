/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SpectralBisectionProgramTree
public import NLAlib.Matrix.Computation.SpectralBisectionTape
public import NLAlib.Matrix.Computation.KernelContracts
public import NLAlib.Computation.KernelCall
public import NLAlib.Computation.BLASCongr
public import NLAlib.Matrix.Computation.PairKernels.Arithmetic

/-!
# The leaf, child and deflation blocks of the spectral bisection node step

The blocks of the node step of `NLAlib.eighProg` that end a node or deflate it compute the matching
operations of `NLAlib.eighStep` on the machine of the semantics: a leaf writes the identity basis
and the diagonal, a node with one child writes the shifted matrix on the same slot, and the
deflation block writes the basis that `NLAlib.deflate` computes from the stored samples. Each value
statement is a partial equality: under kernels that are routines on pairs and a semantics that
decides flags, a successful run writes exactly the machine's value.

## Main results

* `NLAlib.holds_of_exec_eighLeafBlock`, `NLAlib.holds_of_exec_eighChildBlock`: the leaf and the
  child.
* `NLAlib.holds_of_exec_eighDeflateBlock`, `NLAlib.exists_exec_eighDeflateBlock`: the deflation
  block computes, and succeeds.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {Su Sg : Type} {toNat : K → ℕ} {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}
  {unif : K → Su → K} {normal : Sg → K × K}

/-! ### The blocks of a node -/

omit [Inhabited K] in
/-- A successful loop of literals into the cells `f w` of one buffer keeps the shape and the tape
positions, leaves the literal in every written cell and every other cell unchanged. -/
private theorem read_of_exec_loop_lit_leaf {p : P} {m : IExp ℕ} {Y : ℕ} {f : ℕ → IExp ℕ} {c : ℚ}
    {st st' : St P K C}
    (h : exec I (.loop m fun w => .seq (.instr (.lit p ⟨Y, f w⟩ c)) .skip) st = some st') :
    st'.store.shape = st.store.shape ∧ st'.pos = st.pos ∧
      (∀ w < m.eval, ∃ z, I.sem.lit p c = some z ∧ st'.store.read p Y (f w).eval = some z) ∧
      ∀ q b i, (b ≠ Y ∨ ∀ w < m.eval, (f w).eval ≠ i) →
        st'.store.read q b i = st.store.read q b i := by
  refine forall_of_exec_loop_eq_some I (fun w s => s.store.shape = st.store.shape ∧
      s.pos = st.pos ∧
      (∀ w' < w, ∃ z, I.sem.lit p c = some z ∧ s.store.read p Y (f w').eval = some z) ∧
      ∀ q b i, (b ≠ Y ∨ ∀ w' < w, (f w').eval ≠ i) → s.store.read q b i = st.store.read q b i)
    ⟨rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ => rfl⟩ ?_ h
  rintro w - s₁ s₂ ⟨hsh, hps, hrd, hfr⟩ hex
  rw [exec_seq_skip, exec_instr] at hex
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hex
  obtain ⟨_, ⟨v, hv, s', hw', rfl⟩, rfl⟩ := hex
  refine ⟨(Store.shape_of_write_eq_some hw').trans hsh, hps, fun w' hw => ?_,
    fun q b i hb => ?_⟩
  · by_cases hww : (f w').eval = (f w).eval
    · exact ⟨v, hv, hww ▸ Store.read_of_write_eq_some hw'⟩
    · have hlt : w' < w := lt_of_le_of_ne (Nat.lt_succ_iff.mp hw) (fun h => hww (h ▸ rfl))
      rw [Store.read_of_write_eq_some_of_ne hw' (Or.inr hww)]
      exact hrd w' hlt
  · rw [Store.read_of_write_eq_some_of_ne hw' ?_]
    · exact hfr q b i (hb.imp_right fun h w' hw => h w' (Nat.lt_succ_of_lt hw))
    · exact hb.imp_right fun h => (h w (Nat.lt_succ_self w)).symm

omit [Inhabited K] in
/-- A successful loop of copies from the cells `g i` of `X` into the distinct cells `f i` of `Y`,
no source among the targets, keeps the shape and the tape positions, copies every source and leaves
every other cell unchanged. -/
private theorem read_of_exec_loop_copy_leaf {p : P} {m : IExp ℕ} {X Y : ℕ} {f g : ℕ → IExp ℕ}
    {st st' : St P K C}
    (hf : ∀ i < m.eval, ∀ j < m.eval, (f i).eval = (f j).eval → i = j)
    (hfg : ∀ i < m.eval, ∀ j < m.eval, X ≠ Y ∨ (g i).eval ≠ (f j).eval)
    (h : exec I (.loop m fun i => .seq (.instr (.copy p ⟨Y, f i⟩ ⟨X, g i⟩)) .skip) st =
      some st') :
    st'.store.shape = st.store.shape ∧ st'.pos = st.pos ∧
      (∀ i < m.eval, st'.store.read p Y (f i).eval = st.store.read p X (g i).eval) ∧
      ∀ q b j, (b ≠ Y ∨ ∀ i < m.eval, (f i).eval ≠ j) →
        st'.store.read q b j = st.store.read q b j := by
  refine forall_of_exec_loop_eq_some I (fun w s => s.store.shape = st.store.shape ∧
      s.pos = st.pos ∧
      (∀ i < w, s.store.read p Y (f i).eval = st.store.read p X (g i).eval) ∧
      ∀ q b j, (b ≠ Y ∨ ∀ i < w, (f i).eval ≠ j) → s.store.read q b j = st.store.read q b j)
    ⟨rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ => rfl⟩ ?_ h
  rintro w hwm s₁ s₂ ⟨hsh, hps, hrd, hfr⟩ hex
  rw [exec_seq_skip, exec_instr] at hex
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hex
  obtain ⟨_, ⟨v, hv, s', hw', rfl⟩, rfl⟩ := hex
  refine ⟨(Store.shape_of_write_eq_some hw').trans hsh, hps, fun i hi => ?_,
    fun q b j hb => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Store.read_of_write_eq_some_of_ne hw' (Or.inr fun he =>
        absurd (hf i (hi.trans hwm) w hwm he) (Nat.ne_of_lt hi))]
      exact hrd i hi
    · rw [Store.read_of_write_eq_some hw', ← hv]
      refine hfr p X (g i).eval ?_
      by_cases hXY : X = Y
      · exact Or.inr fun j hj he =>
          ((hfg i hwm j (hj.trans hwm)).resolve_left (not_not.mpr hXY)) he.symm
      · exact Or.inl hXY
  · rw [Store.read_of_write_eq_some_of_ne hw' ?_]
    · exact hfr q b j (hb.imp_right fun h i hi => h i (Nat.lt_succ_of_lt hi))
    · exact hb.imp_right fun h => (h w (Nat.lt_succ_self w)).symm

/-- The diagonal loop of a leaf: from a block at `mo` of `Ma` holding $\mathbf{A}$, the cells
$eo + i$ of `Ea` get $\operatorname{Re} a_{ii}$ (`diag`) or the machine's zero; the shape, the
positions and every cell outside them are kept. -/
private theorem read_of_exec_leaf_diag (p : P) (diag : Bool) (k : ℕ) {Ma Ea : ℕ}
    {mo eo : IExp ℕ} {s₁ s₂ : St P K C} {A : Matrix (Fin k) (Fin k) (K × K)}
    (hA : pairLayout.Holds s₁.store p Ma mo.eval A)
    (hEA : (¬Ea = Ma ∨ eo.eval + k ≤ mo.eval) ∨ mo.eval + 2 * (k * k) ≤ eo.eval)
    (hl : exec I (.loop (.const k) fun i => (if diag then
        ins (.copy p ⟨Ea, eo + .var i⟩ ⟨Ma, mo + zidx (.const k) (.var i) (.var i)⟩)
      else ins (.lit p ⟨Ea, eo + .var i⟩ 0) : Builder P ι ℕ ℕ Unit).run) s₁ = some s₂) :
    let M := I.sem.toFloatMachine p toNat mmR qrR unif normal
    s₂.store.shape = s₁.store.shape ∧ s₂.pos = s₁.pos ∧
      (∀ i : Fin k, s₂.store.read p Ea (eo.eval + i) = some (if diag then (A i i).1 else M.zero)) ∧
      ∀ q b j, (b ≠ Ea ∨ j < eo.eval ∨ eo.eval + k ≤ j) →
        s₂.store.read q b j = s₁.store.read q b j := by
  intro M
  have hii : ∀ i < k, 2 * (i + k * i) + 2 ≤ 2 * (k * k) := fun i hi => by nlinarith
  cases diag
  · obtain ⟨hsh, hps, hE, hfr⟩ := read_of_exec_loop_lit_leaf hl
    refine ⟨hsh, hps, fun i => ?_, fun q b j hb => hfr q b j (hb.imp_right fun hb w hw => ?_)⟩
    · obtain ⟨z, hz, hr⟩ := hE i i.isLt
      simp only [IExp.eval_add, IExp.eval_var] at hr
      rw [hr]
      simp only [M, ScalarSem.toFloatMachine, hz, Option.getD_some, Bool.false_eq_true,
        if_false]
    · simp only [IExp.eval_add, IExp.eval_var, IExp.eval_const] at hw ⊢
      omega
  · obtain ⟨hsh, hps, hE, hfr⟩ := read_of_exec_loop_copy_leaf
      (f := fun i => eo + .var i) (g := fun i => mo + zidx (.const k) (.var i) (.var i))
      (fun i _ j _ he => by simpa using he) (fun i hi j hj => by
        simp only [zidx, IExp.eval_add, IExp.eval_mul, IExp.eval_var, IExp.eval_const,
          IExp.eval_ofNat] at hi hj ⊢
        have := hii i hi
        by_cases hMa : Ma = Ea
        · right; omega
        · left; exact hMa) hl
    refine ⟨hsh, hps, fun i => ?_, fun q b j hb => hfr q b j (hb.imp_right fun hb w hw => ?_)⟩
    · have := hE i i.isLt
      simp only [zidx, IExp.eval_add, IExp.eval_mul, IExp.eval_var, IExp.eval_const,
        IExp.eval_ofNat] at this
      rw [this]
      have := hA i i ⟨0, by simp [pairLayout]⟩
      simpa [pairLayout] using this
    · simp only [IExp.eval_add, IExp.eval_var, IExp.eval_const] at hw ⊢
      omega

/-- A leaf writes its output: a successful run of `NLAlib.eighLeafBlock` for a node of size
$k$ whose matrix $\mathbf{A}$ is held at `mo` of `Ma` ends with the block at `uo` of `Ua` holding
the machine's identity (`NLAlib.FloatMachine.identityMat`), the cells $eo + i$ of `Ea` the real
parts $\operatorname{Re} a_{ii}$ (`diag`) or the machine's zero, and the kind cell the literal
$1$; every cell outside these blocks and the kind cell is unchanged, the store shape and the tape
positions too. No printed source. -/
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
  intro M
  change exec I (.seq (.named _ _ (.seq (.loop _ _) (.seq (.loop _ _) .skip)))
    (.seq (.loop _ _) (.seq (.instr _) .skip))) st = some st' at h
  rw [exec_seq] at h
  obtain ⟨s₁, hz, h⟩ := Option.bind_eq_some_iff.mp h
  rw [exec_seq] at h
  obtain ⟨s₂, hl, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hI, hIfr⟩ := holds_of_exec_zidentity (I := I) (toNat := toNat) (mmR := mmR)
    (qrR := qrR) (unif := unif) (normal := normal) p k ((exec_seq_skip I _ st).trans hz)
  rw [exec_named, exec_seq] at hz
  obtain ⟨σ, h₀, h₁⟩ := Option.bind_eq_some_iff.mp hz
  rw [exec_seq_skip] at h₁
  obtain ⟨hsh₀, hps₀, -, -⟩ := read_of_exec_loop_lit_leaf h₀
  obtain ⟨hsh₁, hps₁, -, -⟩ := read_of_exec_loop_lit_leaf h₁
  rw [exec_seq_skip, exec_instr] at h
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨v, hv, s₃, hw, rfl⟩, rfl⟩ := h
  simp only [blockDisjoint, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hUA hEA hUE hkd
  have hii : ∀ i < k, 2 * (i + k * i) + 2 ≤ 2 * (k * k) := fun i hi => by nlinarith
  obtain ⟨hsh₂, hps₂, hE, hfr₂⟩ := read_of_exec_leaf_diag (toNat := toNat) (mmR := mmR)
    (qrR := qrR) (unif := unif) (normal := normal) p diag k
    (hA.of_forall_read_eq fun i hi₁ hi₂ => hIfr p Ma i (by
      change i < mo.eval + k * k * 2 at hi₂
      simp only [blockDisjoint, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq]
      by_cases hb : Ma = Ua
      · omega
      · left; left; exact hb)) hEA hl
  have hkdE : ∀ i < k, kd.buf ≠ Ea ∨ kd.idx.eval ≠ eo.eval + i := fun i hi => by
    by_cases hb : kd.buf = Ea
    · right; omega
    · left; exact hb
  refine ⟨hI.of_forall_read_eq fun i hi₁ hi₂ => ?_, fun i => ?_, ?_, fun q b i h₁ h₂ h₃ => ?_,
    ?_, ?_⟩
  · change i < uo.eval + k * k * 2 at hi₂
    rw [Store.read_of_write_eq_some_of_ne hw ?_, hfr₂ p Ua i ?_]
    · by_cases hb : Ua = Ea
      · right; omega
      · left; exact hb
    · by_cases hb : Ua = kd.buf
      · right; omega
      · left; exact hb
  · rw [Store.read_of_write_eq_some_of_ne hw ((hkdE i i.isLt).imp Ne.symm Ne.symm)]
    exact hE i
  · exact (Store.read_of_write_eq_some hw).trans hv.symm
  · simp only [blockDisjoint, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq] at h₁ h₂ h₃
    rw [Store.read_of_write_eq_some_of_ne hw ?_, hfr₂ q b i ?_]
    · exact hIfr q b i (by simpa [blockDisjoint] using h₁)
    · rcases h₂ with (h₂ | h₂) | h₂
      · exact Or.inl h₂
      · right; left; omega
      · right; right; omega
    · rcases h₃ with (h₃ | h₃) | h₃
      · exact Or.inl h₃
      · right; omega
      · right; omega
  · exact (Store.shape_of_write_eq_some hw).trans (hsh₂.trans (hsh₁.trans hsh₀))
  · exact hps₂.trans (hps₁.trans hps₀)

/-- A successful index-literal instruction writes the literal and changes only its cell. -/
private theorem exec_ins_litIdx_read (p : P) (e : IExp ℕ) (c' : Cell ℕ ℕ) {σ₀ σ : St P K C}
    (hσ : exec I (ins (.litIdx p c' e) : Builder P ι ℕ ℕ Unit).run σ₀ = some σ) :
    σ.store.read p c'.buf c'.idx.eval = I.sem.lit p (e.eval : ℚ) ∧
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
  refine ⟨?_, fun q b i hne => ?_, Store.shape_of_write_eq_some hw, rfl⟩
  · exact Store.read_of_write_eq_some hw
  · exact Store.read_of_write_eq_some_of_ne hw (not_and_or.mp hne)

/-- One child on the same slot: a successful run of `NLAlib.eighChildBlock` for a node of size
$k$ whose matrix $\mathbf{A}$ is held at `mo` of `Ma`, the cell `sg` holding $\sigma$, ends with the
block at `mo'` of `Ma` (disjoint from the one at `mo`) holding `M.hermShift A σ`, the size cell the
literal $k$ and the kind cell the literal `code`; every other cell is unchanged, the store shape and
the tape positions too. No printed source. -/
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
  unfold eighChildBlock at h
  rw [exec_run_bind I (b := zhermShift (ι := ι) p (.const k) Ma mo sg Ma mo') (fun _ => rfl)] at h
  obtain ⟨σ1, h1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hM, hf1, hsh1, hp1⟩ := holds_of_exec_zhermShift p k hA hσ hAA hsg h1
  rw [exec_run_bind I (b := ins (.litIdx p sz (.const k))) (fun _ => rfl)] at h
  obtain ⟨σ2, h2, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨rsz, hf2, hsh2, hp2⟩ := exec_ins_litIdx_read p _ _ h2
  obtain ⟨rkd, hf3, hsh3, hp3⟩ := exec_ins_litIdx_read p _ _ h
  have hszb : ∀ {b i : ℕ}, blockDisjoint (b, i, 1) (sz.buf, sz.idx.eval, 1) = true →
      ¬(b = sz.buf ∧ i = sz.idx.eval) := by
    intro b i hbs ⟨hb, hi⟩
    subst hb; subst hi
    simp [blockDisjoint] at hbs
  have hkdb : ∀ {b i : ℕ}, blockDisjoint (b, i, 1) (kd.buf, kd.idx.eval, 1) = true →
      ¬(b = kd.buf ∧ i = kd.idx.eval) := by
    intro b i hbs ⟨hb, hi⟩
    subst hb; subst hi
    simp [blockDisjoint] at hbs
  have hszkd' : ¬(sz.buf = kd.buf ∧ sz.idx.eval = kd.idx.eval) := fun ⟨h1, h2⟩ => by
    simp [blockDisjoint, h1, h2] at hszkd
  have hw : (pairLayout : EntryLayout K (K × K)).width = 2 := rfl
  have hMst : pairLayout.Holds st'.store p Ma mo'.eval
      ((I.sem.toFloatMachine p toNat mmR qrR unif normal).hermShift A σ) :=
    EntryLayout.Holds.of_forall_read_eq hM fun i _ h2 => by
      rw [hw] at h2
      rw [hf3 _ _ _ (fun ⟨hb, hi⟩ => by subst hb; subst hi; simp [blockDisjoint] at hkd; omega),
        hf2 _ _ _ (fun ⟨hb, hi⟩ => by subst hb; subst hi; simp [blockDisjoint] at hsz; omega)]
  refine ⟨hMst, ?_, ?_, fun q b i hb1 hb2 hb3 => ?_, ?_, ?_⟩
  · rw [hf3 _ _ _ hszkd']
    simpa using rsz
  · simpa using rkd
  · rw [hf3 q b i (hkdb hb3), hf2 q b i (hszb hb2), hf1 q b i hb1]
  · rw [hsh3, hsh2, hsh1]
  · rw [hp3, hp2, hp1]

/-- One entry of the test-matrix loop of a deflation: the two products of the words of `Sg` by the
stored $\sqrt{1/2}$ land in the words $2(i + kj)$ and $2(i + kj) + 1$ of `G`; the earlier entries,
every other buffer, the shape and the positions are kept. -/
private theorem deflate_testEntry (p : P) (n k lo s i j : ℕ) {Sg G : ℕ} {sq : Cell ℕ ℕ}
    {sv : K} {st s₁ s₂ : St P K C} (hi : i < k) (hsqG : sq.buf ≠ G) (hSgG : Sg ≠ G)
    (hsq : st.store.read p sq.buf sq.idx.eval = some sv)
    (hsh : s₁.store.shape = st.store.shape) (hps : s₁.pos = st.pos)
    (hfr : ∀ q b x, b ≠ G → s₁.store.read q b x = st.store.read q b x)
    (hent : ∀ i' j', i' < k → j' < k → i' + k * j' < i + k * j → ∃ a a',
      st.store.read p Sg (2 * (n * (2 * (lo + j') + s) + i')) = some a ∧
      st.store.read p Sg (2 * (n * (2 * (lo + j') + s) + i') + 1) = some a' ∧
      s₁.store.read p G (2 * (i' + k * j')) = some ((I.sem.bin p .mul a sv).getD default) ∧
      s₁.store.read p G (2 * (i' + k * j') + 1) = some ((I.sem.bin p .mul a' sv).getD default))
    (hex : exec I (.seq (.instr (.bin p .mul ⟨G, zidx (.const k) (.var i) (.var j)⟩
          ⟨Sg, 2 * (.const n * (2 * (.const lo + .var j) + .const s) + .var i)⟩ sq))
        (.seq (.instr (.bin p .mul ⟨G, zidx (.const k) (.var i) (.var j) + 1⟩
          ⟨Sg, 2 * (.const n * (2 * (.const lo + .var j) + .const s) + .var i) + 1⟩ sq))
        .skip)) s₁ = some s₂) :
    s₂.store.shape = st.store.shape ∧ s₂.pos = st.pos ∧
      (∀ q b x, b ≠ G → s₂.store.read q b x = st.store.read q b x) ∧
      ∀ i' j', i' < k → j' < k → i' + k * j' < i + k * j + 1 → ∃ a a',
        st.store.read p Sg (2 * (n * (2 * (lo + j') + s) + i')) = some a ∧
        st.store.read p Sg (2 * (n * (2 * (lo + j') + s) + i') + 1) = some a' ∧
        s₂.store.read p G (2 * (i' + k * j')) = some ((I.sem.bin p .mul a sv).getD default) ∧
        s₂.store.read p G (2 * (i' + k * j') + 1) =
          some ((I.sem.bin p .mul a' sv).getD default) := by
  rw [exec_seq, exec_instr] at hex
  obtain ⟨s₃, h₃, hex⟩ := Option.bind_eq_some_iff.mp hex
  rw [exec_seq_skip, exec_instr] at hex
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h₃ hex
  obtain ⟨_, ⟨a, ha, c, hc, v, hv, w₁, hw₁, rfl⟩, rfl⟩ := h₃
  obtain ⟨_, ⟨a', ha', c', hc', v', hv', w₂, hw₂, rfl⟩, rfl⟩ := hex
  simp only [zidx, IExp.eval_add, IExp.eval_mul, IExp.eval_var, IExp.eval_const,
    IExp.eval_ofNat] at ha hc hv hw₁ ha' hc' hv' hw₂
  have hsq₁ : s₁.store.read p sq.buf sq.idx.eval = some sv := (hfr _ _ _ hsqG).trans hsq
  rw [hsq₁, Option.some.injEq] at hc
  subst hc
  rw [Store.read_of_write_eq_some_of_ne hw₁ (Or.inl hsqG), hsq₁, Option.some.injEq] at hc'
  subst hc'
  rw [Store.read_of_write_eq_some_of_ne hw₁ (Or.inl hSgG)] at ha'
  have hfr₂ : ∀ q b x, b ≠ G → w₂.read q b x = st.store.read q b x := fun q b x hb => by
    rw [Store.read_of_write_eq_some_of_ne hw₂ (Or.inl hb),
      Store.read_of_write_eq_some_of_ne hw₁ (Or.inl hb), hfr q b x hb]
  refine ⟨(Store.shape_of_write_eq_some hw₂).trans ((Store.shape_of_write_eq_some hw₁).trans hsh),
    hps, hfr₂, fun i' j' hi' hj' hlt => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt | he
  · obtain ⟨b₁, b₂, hb₁, hb₂, hg₁, hg₂⟩ := hent i' j' hi' hj' hlt
    refine ⟨b₁, b₂, hb₁, hb₂, ?_, ?_⟩
    · rw [Store.read_of_write_eq_some_of_ne hw₂ (Or.inr (by omega)),
        Store.read_of_write_eq_some_of_ne hw₁ (Or.inr (by omega)), hg₁]
    · rw [Store.read_of_write_eq_some_of_ne hw₂ (Or.inr (by omega)),
        Store.read_of_write_eq_some_of_ne hw₁ (Or.inr (by omega)), hg₂]
  · obtain ⟨rfl, rfl⟩ : i' = i ∧ j' = j := by
      have hk : 0 < k := by omega
      have h1 : (i' + k * j') % k = (i + k * j) % k := by rw [he]
      simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hi'] at h1
      subst h1
      exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hk (by omega)⟩
    refine ⟨a, a', (hfr _ _ _ hSgG).symm.trans ha, (hfr _ _ _ hSgG).symm.trans ha', ?_, ?_⟩
    · rw [Store.read_of_write_eq_some_of_ne hw₂ (Or.inr (by omega)),
        Store.read_of_write_eq_some hw₁, hv]
      rfl
    · rw [Store.read_of_write_eq_some hw₂, hv']
      rfl

/-- The test-matrix loop of a deflation: entry $(i, j)$ of the block `G` is the pair of products of
the words $2(n(2(lo + j) + s) + i)$ and the next of `Sg` by the stored $\sqrt{1/2}$; every other
buffer, the shape and the positions are kept. -/
private theorem deflate_testLoop (p : P) (n k lo s : ℕ) {Sg G : ℕ} {sq : Cell ℕ ℕ}
    {sv : K} {st st' : St P K C} (hsqG : sq.buf ≠ G) (hSgG : Sg ≠ G)
    (hsq : st.store.read p sq.buf sq.idx.eval = some sv)
    (h : exec I (.loop (.const k) fun j => (forRange (ι := ι) (.const k) fun i => do
        ins (.bin p .mul ⟨G, zidx (.const k) (.var i) (.var j)⟩
          ⟨Sg, 2 * (.const n * (2 * (.const lo + .var j) + .const s) + .var i)⟩ sq)
        ins (.bin p .mul ⟨G, zidx (.const k) (.var i) (.var j) + 1⟩
          ⟨Sg, 2 * (.const n * (2 * (.const lo + .var j) + .const s) + .var i) + 1⟩ sq)).run)
      st = some st') :
    st'.store.shape = st.store.shape ∧ st'.pos = st.pos ∧
      (∀ q b x, b ≠ G → st'.store.read q b x = st.store.read q b x) ∧
      ∀ i j, i < k → j < k → ∃ a a',
        st.store.read p Sg (2 * (n * (2 * (lo + j) + s) + i)) = some a ∧
        st.store.read p Sg (2 * (n * (2 * (lo + j) + s) + i) + 1) = some a' ∧
        st'.store.read p G (2 * (i + k * j)) = some ((I.sem.bin p .mul a sv).getD default) ∧
        st'.store.read p G (2 * (i + k * j) + 1) =
          some ((I.sem.bin p .mul a' sv).getD default) := by
  let Ent : ℕ → St P K C → Prop := fun c s₁ => ∀ i' j', i' < k → j' < k → i' + k * j' < c →
    ∃ a a', st.store.read p Sg (2 * (n * (2 * (lo + j') + s) + i')) = some a ∧
      st.store.read p Sg (2 * (n * (2 * (lo + j') + s) + i') + 1) = some a' ∧
      s₁.store.read p G (2 * (i' + k * j')) = some ((I.sem.bin p .mul a sv).getD default) ∧
      s₁.store.read p G (2 * (i' + k * j') + 1) = some ((I.sem.bin p .mul a' sv).getD default)
  have hR := forall_of_exec_loop_eq_some I (n := .const k) (fun j s₁ => s₁.store.shape =
      st.store.shape ∧ s₁.pos = st.pos ∧
      (∀ q b x, b ≠ G → s₁.store.read q b x = st.store.read q b x) ∧ Ent (k * j) s₁)
    ⟨rfl, rfl, fun _ _ _ _ => rfl, fun _ _ _ _ h => absurd h (by omega)⟩ ?_ h
  · obtain ⟨hsh, hps, hfr, hent⟩ := hR
    exact ⟨hsh, hps, hfr, fun i j hi hj => hent i j hi hj (by
      simp only [IExp.eval_const]; nlinarith)⟩
  rintro j hj s₁ s₂ ⟨hsh, hps, hfr, hent⟩ hex
  change exec I (.seq (.loop _ _) .skip) s₁ = some s₂ at hex
  rw [exec_seq_skip] at hex
  have hR' := forall_of_exec_loop_eq_some I (n := .const k) (fun i s₃ => s₃.store.shape =
      st.store.shape ∧ s₃.pos = st.pos ∧
      (∀ q b x, b ≠ G → s₃.store.read q b x = st.store.read q b x) ∧ Ent (i + k * j) s₃)
    ⟨hsh, hps, hfr, by rwa [zero_add]⟩ (fun i hi s₃ s₄ ⟨hsh, hps, hfr, hent⟩ hex => by
      rw [show i + 1 + k * j = i + k * j + 1 by ring]
      exact deflate_testEntry p n k lo s i j hi hsqG hSgG hsq hsh hps hfr hent hex) hex
  obtain ⟨hsh, hps, hfr, hent⟩ := hR'
  refine ⟨hsh, hps, hfr, ?_⟩
  simp only [IExp.eval_const] at hent
  rwa [show k * (j + 1) = k + k * j by ring]

/-- Randomized deflation on stored samples computes `NLAlib.deflate`: if kernels `mm`, `qr` of
`I` are the routines `mmR`, `qrR` on interleaved pairs, a successful run of
`NLAlib.eighDeflateBlock` for a node of size $k \le n$ at slot $lo$ of depth $d$ with rank
$r \le k$, side $b$, the stored projector $\mathbf{P}$ ($k \times k$) at offset $0$ of `Pm`, the
cell `sq` holding the stored $\sqrt{1/2}$ (`NLAlib.Computation.ScalarSem.sqrtHalf`) and the $4n^2$
Gaussian words of the level in `Sg` (word $w$ the tape value at position $4n^2 d + w$), ends with
the block at `qo` of `Qa` holding `NLAlib.deflate M r P G` for $\mathbf{G}$ the leading $k \times k$
block of the test matrix of side $b$ of the node's samples (`NLAlib.eighTapeSample`), $M$ the
machine of the interpretation (`NLAlib.eighTapeMachine`); every cell outside that block and the
scratch buffers `G`, `Y`, `Qf`, `Rf` is unchanged, the store shape and the tape positions too. No
printed source. -/
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
  set M := eighTapeMachine I p mmR qrR
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hbufs hsqb
  obtain ⟨⟨-, hSgG, -, -, -, -⟩, ⟨hPmG, hPmY, -, -, -⟩, ⟨hGY, -, -, -⟩, ⟨hYQf, hYRf, -⟩,
    ⟨hQfRf, hQfQa⟩, -, -⟩ := hbufs
  obtain ⟨hsG, -, -, -, -⟩ := hsqb
  have hne : ∀ {b b' i i' l l' : ℕ}, b ≠ b' → blockDisjoint (b, i, l) (b', i', l') = true :=
    fun h => by simp [blockDisjoint, h]
  change exec I (.seq (.loop _ _) (.seq (.kcall _ _ _ _ _) (.seq (.kcall _ _ _ _ _)
    (.seq (.named _ _ _) .skip)))) st = some st' at h
  rw [exec_seq] at h
  obtain ⟨s₁, h₁, h⟩ := Option.bind_eq_some_iff.mp h
  rw [exec_seq, exec_kcall] at h
  obtain ⟨s₂, h₂, h⟩ := Option.bind_eq_some_iff.mp h
  rw [exec_seq, exec_kcall] at h
  obtain ⟨s₃, h₃, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨c₂, hc₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
  obtain ⟨c₃, hc₃, rfl⟩ := Option.map_eq_some_iff.mp h₃
  -- the stored test matrix
  obtain ⟨hsh₁, hps₁, hfr₁, hent⟩ := deflate_testLoop p n k lo (if b then 0 else 1) hsG hSgG
    hsq h₁
  have hG : pairLayout.Holds s₁.store p G 0
      ((leadingBlock k ((eighTapeSample n d lo).2 b)).map M.normal) := by
    intro i j t
    obtain ⟨a, a', ha, ha', hg, hg'⟩ := hent i j i.isLt j.isLt
    have hw : 2 * (n * (2 * (lo + j) + (if b then 0 else 1)) + i) + 1 < 4 * (n * n) := by
      have h1 : 2 * (lo + j) + (if b then 0 else 1) + 1 ≤ 2 * n := by split <;> omega
      have h2 := Nat.mul_le_mul_left n h1
      have h3 : (i : ℕ) < n := by omega
      rw [Nat.mul_add, Nat.mul_one] at h2
      nlinarith
    rw [hSg _ (by omega)] at ha
    rw [hSg _ hw] at ha'
    cases ha
    cases ha'
    have hidx : 4 * (n * n) * d + 2 * (n * (2 * (lo + j) + (if b then 0 else 1)) + i) =
        2 * (2 * (n * n) * d + n * (2 * (lo + j) + (if b then 0 else 1)) + i) := by ring
    have hidx' : 4 * (n * n) * d + (2 * (n * (2 * (lo + j) + (if b then 0 else 1)) + i) + 1) =
        2 * (2 * (n * n) * d + (n * (2 * (lo + j) + (if b then 0 else 1)) + i)) + 1 := by ring
    have hi : (i : ℕ) < n ∧ (j : ℕ) < n := ⟨by omega, by omega⟩
    obtain ⟨t, ht⟩ := t
    change t < 2 at ht
    change s₁.store.read p G (0 + (2 * ((i : ℕ) + k * j) + t)) = _
    interval_cases t
    · rw [zero_add, add_zero, hg]
      simp [pairLayout, leadingBlock, hi, eighTapeSample, M, eighTapeMachine,
        ScalarSem.toFloatMachine, ScalarSem.tapeNormal, hidx]
    · rw [zero_add, hg']
      simp [pairLayout, leadingBlock, hi, eighTapeSample, M, eighTapeMachine,
        ScalarSem.toFloatMachine, ScalarSem.tapeNormal, hidx', add_assoc]
  -- the two kernel calls
  obtain ⟨hY, hfr₂⟩ := hmm.holds_of_kcallStore_eq_some (fun _ => rfl) p (l := k) (m := k)
    (n := k) (a := (Pm, 0)) (b := (G, 0)) (c := (Y, 0))
    (hP.of_forall_read_eq fun i _ _ => hfr₁ p Pm i hPmG) hG (hne (Ne.symm hPmY))
    (hne (Ne.symm hGY)) hc₂
  obtain ⟨hQf, -, hfr₃⟩ := hqr.holds_of_kcallStore_eq_some (fun _ => rfl) p (m := k) (n := k)
    (a := (Y, 0)) (q := (Qf, 0)) (r := (Rf, 0)) hY (hne hQfRf) (hne (Ne.symm hYQf))
    (hne (Ne.symm hYRf)) hc₃
  -- the copy of the first `r` columns
  rw [exec_seq_skip] at h
  obtain ⟨hQa, hfr₄, hsh₄, hps₄⟩ := holds_of_exec_zcopy (I := I) p k r
    (A := Matrix.of fun i (j : Fin r) => (qrR (mmR Pmat
      ((leadingBlock k ((eighTapeSample n d lo).2 b)).map M.normal))).1 i
        ⟨j, lt_of_lt_of_le j.isLt hr⟩)
    (fun i j t => hQf i ⟨j, lt_of_lt_of_le j.isLt hr⟩ t) (hne (Ne.symm hQfQa))
    ((exec_seq_skip I _ _).trans h)
  refine ⟨?_, fun q b' i hb' hbd => ?_, ?_, ?_⟩
  · convert hQa using 1
    refine Matrix.ext fun i j => ?_
    simp only [deflate, dif_pos (lt_of_lt_of_le j.isLt hr), Matrix.of_apply]
    rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hb'
    rw [hfr₄ q b' i hbd, hfr₃ q b' i (hne hb'.2.2.1) (hne hb'.2.2.2), hfr₂ q b' i (hne hb'.2.1),
      hfr₁ q b' i hb'.1]
  · rw [hsh₄]
    change c₃.shape = _
    rw [Interp.shape_of_kcallStore_eq_some hc₃, Interp.shape_of_kcallStore_eq_some hc₂, hsh₁]
  · rw [hps₄]
    exact hps₁

omit [Inhabited K] in
/-- The test-matrix loop of a deflation succeeds when the words of `Sg` it reads and the cell `sq`
are initialised and `G` is long enough; it keeps the shape and every other buffer, and initialises
the first $2k^2$ words of `G`. -/
private theorem exists_exec_deflate_testLoop {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (n k lo s : ℕ) {Sg G lenG : ℕ}
    {sq : Cell ℕ ℕ} {sv : K} {st : St P K C} (hsqG : sq.buf ≠ G) (hSgG : Sg ≠ G)
    (hsq : st.store.read p sq.buf sq.idx.eval = some sv)
    (hSg : ∀ i j, i < k → j < k → ∀ t < 2, ∃ a,
      st.store.read p Sg (2 * (n * (2 * (lo + j) + s) + i) + t) = some a)
    (hG : st.store.shape[G]? = some (p, lenG)) (hlen : 2 * (k * k) ≤ lenG) :
    ∃ st', exec I (.loop (.const k) fun j => (forRange (ι := ι) (.const k) fun i => do
        ins (.bin p .mul ⟨G, zidx (.const k) (.var i) (.var j)⟩
          ⟨Sg, 2 * (.const n * (2 * (.const lo + .var j) + .const s) + .var i)⟩ sq)
        ins (.bin p .mul ⟨G, zidx (.const k) (.var i) (.var j) + 1⟩
          ⟨Sg, 2 * (.const n * (2 * (.const lo + .var j) + .const s) + .var i) + 1⟩ sq)).run)
      st = some st' ∧ st'.store.shape = st.store.shape ∧
      (∀ q b x, b ≠ G → st'.store.read q b x = st.store.read q b x) ∧
      ∀ w < 2 * (k * k), ∃ v, st'.store.read p G w = some v := by
  let R : ℕ → St P K C → Prop := fun c s₁ => s₁.store.shape = st.store.shape ∧
    (∀ q b x, b ≠ G → s₁.store.read q b x = st.store.read q b x) ∧
    ∀ w < 2 * c, ∃ v, s₁.store.read p G w = some v
  have hkeep : ∀ {s s' : Store P K} {x : ℕ} {z : K}, s.write p G x z = some s' →
      ∀ w, (∃ v, s.read p G w = some v) → ∃ v, s'.read p G w = some v := by
    intro s s' x z hw w ⟨v, hv⟩
    by_cases hwx : w = x
    · subst hwx; exact ⟨z, Store.read_of_write_eq_some hw⟩
    · exact ⟨v, (Store.read_of_write_eq_some_of_ne hw (Or.inr hwx)).trans hv⟩
  refine (exists_exec_loop_eq_some_of_forall (I := I) (n := .const k) (fun j s₁ => R (k * j) s₁)
    ⟨rfl, fun _ _ _ _ => rfl, fun w hw => absurd hw (by simp)⟩ ?_).imp
    fun st' h => ⟨h.1, h.2⟩
  intro j hj s₁ ⟨hsh₁, hfr₁, hw₁⟩
  simp only [IExp.eval_const] at hj
  change ∃ st', exec I (.seq (.loop (.const k) _) .skip) s₁ = some st' ∧ _
  simp only [exec_seq_skip]
  refine (exists_exec_loop_eq_some_of_forall (I := I) (n := .const k)
    (fun i s₂ => R (i + k * j) s₂) ⟨hsh₁, hfr₁, by simpa using hw₁⟩ ?_).imp
    fun st' h => ⟨h.1, by
      have := h.2
      rwa [IExp.eval_const, show k + k * j = k * (j + 1) by ring] at this⟩
  intro i hi s₂ ⟨hsh₂, hfr₂, hw₂⟩
  simp only [IExp.eval_const] at hi
  obtain ⟨a, ha⟩ := hSg i j hi hj 0 (by norm_num)
  obtain ⟨a', ha'⟩ := hSg i j hi hj 1 (by norm_num)
  obtain ⟨z, hz⟩ := hsem.bin_ok p .mul a sv trivial (fun h => nomatch h) trivial
  obtain ⟨z', hz'⟩ := hsem.bin_ok p .mul a' sv trivial (fun h => nomatch h) trivial
  have hidx : 2 * (i + k * j) + 1 < lenG := by nlinarith
  obtain ⟨w₁, hw₁'⟩ := Store.exists_write_eq_some_of_getElem?_shape (s := s₂.store) z
    (hsh₂ ▸ hG) (show 2 * (i + k * j) < lenG by omega)
  obtain ⟨w₂, hw₂'⟩ := Store.exists_write_eq_some_of_getElem?_shape (s := w₁) z'
    ((Store.shape_of_write_eq_some hw₁').trans hsh₂ ▸ hG) hidx
  have hsq₂ : s₂.store.read p sq.buf sq.idx.eval = some sv := (hfr₂ _ _ _ hsqG).trans hsq
  change ∃ st', exec I (.seq (.instr _) (.seq (.instr _) .skip)) s₂ = some st' ∧ R _ st'
  rw [exec_seq_instr_bin I (a := a) (c := sv) (by
        simp only [IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var,
          IExp.eval_ofNat]
        rw [hfr₂ _ _ _ hSgG]; simpa using ha) hsq₂ hz (by
        simpa [zidx] using hw₁'),
      exec_seq_instr_bin I (a := a') (c := sv) (by
        simp only [IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var,
          IExp.eval_ofNat]
        rw [Store.read_of_write_eq_some_of_ne hw₁' (Or.inl hSgG), hfr₂ _ _ _ hSgG]
        exact ha')
        ((Store.read_of_write_eq_some_of_ne hw₁' (Or.inl hsqG)).trans hsq₂) hz' (by
        simpa [zidx] using hw₂'), exec_skip]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · exact (Store.shape_of_write_eq_some hw₂').trans ((Store.shape_of_write_eq_some hw₁').trans hsh₂)
  · intro q b x hb
    rw [Store.read_of_write_eq_some_of_ne hw₂' (Or.inl hb),
      Store.read_of_write_eq_some_of_ne hw₁' (Or.inl hb), hfr₂ q b x hb]
  · intro w hw
    by_cases hw' : w < 2 * (i + k * j)
    · exact hkeep hw₂' w (hkeep hw₁' w (hw₂ w hw'))
    · by_cases he : w = 2 * (i + k * j) + 1
      · subst he; exact ⟨z', Store.read_of_write_eq_some hw₂'⟩
      · have he' : w = 2 * (i + k * j) := by omega
        subst he'
        exact hkeep hw₂' _ ⟨z, Store.read_of_write_eq_some hw₁'⟩

/-- Deflation on stored samples succeeds, with what it writes: some matrix at the block `qo`
of `Qa`, every other cell outside the scratch buffers unchanged, the shape kept. -/
theorem exists_exec_eighDeflateBlock_facts {mm qr : ι}
    (hmm : IsMatMulKernel I mm pairLayout mmR) (hqr : IsQRKernel I qr pairLayout qrR)
    {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (n k r d lo : ℕ)
    (hk : lo + k ≤ n) (hr : r ≤ k) (b : Bool) {Sg Pm G Y Qf Rf Qa : ℕ} {sq : Cell ℕ ℕ}
    {qo : IExp ℕ} {st : St P K C} {Pmat : Matrix (Fin k) (Fin k) (K × K)}
    (hP : pairLayout.Holds st.store p Pm 0 Pmat)
    (hsq : st.store.read p sq.buf sq.idx.eval = some (I.sem.sqrtHalf p))
    (hSg : ∀ w < 4 * (n * n), ∃ v, st.store.read p Sg w = some v)
    (hbufs : [Sg, Pm, G, Y, Qf, Rf, Qa].Nodup) (hsqb : sq.buf ∉ [G, Y, Qf, Rf, Qa])
    (hscr : ∀ X ∈ [G, Y, Qf, Rf], ∃ len, st.store.shape[X]? = some (p, len) ∧ 2 * (n * n) ≤ len)
    (hQa : ∃ len, st.store.shape[Qa]? = some (p, len) ∧ qo.eval + 2 * (k * r) ≤ len) :
    ∃ st', exec I (eighDeflateBlock p mm qr (.const n) (.const k) (.const r) (.const lo)
      (if b then 0 else 1) Sg sq Pm G Y Qf Rf Qa qo).run st = some st' ∧
      (∃ Q : Matrix (Fin k) (Fin r) (K × K), pairLayout.Holds st'.store p Qa qo.eval Q) ∧
      (∀ q b' i, b' ∉ [G, Y, Qf, Rf] → blockDisjoint (b', i, 1) (Qa, qo.eval, 2 * (k * r)) = true →
        st'.store.read q b' i = st.store.read q b' i) ∧
      st'.store.shape = st.store.shape := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hbufs hsqb
  obtain ⟨⟨-, hSgG, -, -, -, -⟩, ⟨hPmG, hPmY, -, -, -⟩, ⟨hGY, -, -, -⟩, ⟨hYQf, hYRf, -⟩,
    ⟨hQfRf, hQfQa⟩, -, -⟩ := hbufs
  obtain ⟨hsG, -, -, -, -⟩ := hsqb
  have hne : ∀ {b b' i i' l l' : ℕ}, b ≠ b' → blockDisjoint (b, i, l) (b', i', l') = true :=
    fun h => by simp [blockDisjoint, h]
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hscr
  obtain ⟨⟨lG, hG, hlG⟩, ⟨lY, hYs, hlY⟩, ⟨lQ, hQs, hlQ⟩, ⟨lR, hRs, hlR⟩⟩ := hscr
  obtain ⟨lA, hQas, hlA⟩ := hQa
  have hkk : k * k ≤ n * n := Nat.mul_le_mul (by omega) (by omega)
  -- the test loop
  obtain ⟨s₁, h₁, hsh₁, hfr₁, hG₁⟩ := exists_exec_deflate_testLoop (I := I) hsem p n k lo
    (if b then 0 else 1) hsG hSgG hsq (fun i j hi hj t ht => hSg _ (by
      have h1 : 2 * (lo + j) + (if b then 0 else 1) + 1 ≤ 2 * n := by split <;> omega
      have h2 := Nat.mul_le_mul_left n h1
      rw [Nat.mul_add, Nat.mul_one] at h2
      nlinarith)) hG (by omega)
  have hXG : s₁.store.readBlock p G 0 (k * k * 2) = some ((List.range (k * k * 2)).toArray.map
      fun w => (s₁.store.read p G (0 + w)).getD default) :=
    Store.readBlock_eq_some_map_range _ fun w hw => by
      obtain ⟨v, hv⟩ := hG₁ w (by omega)
      rw [zero_add, hv]
      rfl
  have hXP := (EntryLayout.holds_iff_readBlock_eq_some pairLayout s₁.store p Pm 0 Pmat).mp
    (hP.of_forall_read_eq fun i _ _ => hfr₁ p Pm i hPmG)
  -- the product
  have hk₁ := hmm.kcallStore_eq p (l := k) (m := k) (n := k) (a := (Pm, 0)) (b := (G, 0))
    (c := (Y, 0)) hXP hXG (hne (Ne.symm hPmY)) (hne (Ne.symm hGY))
  obtain ⟨c₂, hc₂⟩ : ∃ c₂, I.kcallStore mm p [k, k, k] [(Pm, 0), (G, 0)] [(Y, 0)] s₁.store =
      some c₂ := by
    rw [hk₁]
    exact Store.exists_writeBlock_eq_some_of_getElem?_shape fun i hi => ⟨lY, hsh₁ ▸ hYs, by
      rw [EntryLayout.size_toArray] at hi
      change i < k * k * 2 at hi
      omega⟩
  have hYh := EntryLayout.holds_of_writeBlock_eq_some pairLayout (hk₁.symm.trans hc₂)
  have hsh₂ := (Interp.shape_of_kcallStore_eq_some hc₂).trans hsh₁
  -- the QR factorization
  have hk₂ := hqr.kcallStore_eq p (m := k) (n := k) (a := (Y, 0)) (q := (Qf, 0)) (r := (Rf, 0))
    ((EntryLayout.holds_iff_readBlock_eq_some pairLayout c₂ p Y 0 _).mp hYh) (hne hQfRf)
    (hne (Ne.symm hYQf)) (hne (Ne.symm hYRf))
  obtain ⟨c₃, hc₃⟩ : ∃ c₃, I.kcallStore qr p [k, k] [(Y, 0)] [(Qf, 0), (Rf, 0)] c₂ =
      some c₃ := by
    rw [hk₂]
    obtain ⟨c, hc⟩ := Store.exists_writeBlock_eq_some_of_getElem?_shape (s := c₂) (b := Qf)
      (off := 0) (xs := pairLayout.toArray (qrR (pairLayout.toMatrix k k
        (pairLayout.toArray (mmR (pairLayout.toMatrix k k (pairLayout.toArray Pmat))
          (pairLayout.toMatrix k k ((List.range (k * k * 2)).toArray.map
            fun w => (s₁.store.read p G (0 + w)).getD default)))))).1)
      fun i hi => ⟨lQ, hsh₂ ▸ hQs, by
        rw [EntryLayout.size_toArray] at hi
        change i < k * k * 2 at hi
        omega⟩
    rw [hc, Option.bind_some]
    exact Store.exists_writeBlock_eq_some_of_getElem?_shape fun i hi =>
      ⟨lR, (Store.shape_of_writeBlock_eq_some hc).trans hsh₂ ▸ hRs, by
        rw [EntryLayout.size_toArray] at hi
        change i < k * k * 2 at hi
        omega⟩
  obtain ⟨hQf, -, hfr₃⟩ := hqr.holds_of_kcallStore_eq_some (fun _ => rfl) p (m := k) (n := k)
    (a := (Y, 0)) (q := (Qf, 0)) (r := (Rf, 0)) hYh (hne hQfRf) (hne (Ne.symm hYQf))
    (hne (Ne.symm hYRf)) hc₃
  have hsh₃ := (Interp.shape_of_kcallStore_eq_some hc₃).trans hsh₂
  -- the run
  change ∃ st', exec I (.seq (.loop _ _) (.seq (.kcall _ _ _ _ _) (.seq (.kcall _ _ _ _ _)
    (.seq (.named _ _ _) .skip)))) st = some st' ∧ _
  rw [exec_seq, h₁, Option.bind_some, exec_seq, exec_kcall]
  simp only [List.map_cons, List.map_nil, IExp.eval_const, IExp.eval_zero]
  rw [hc₂, Option.map_some, Option.bind_some, exec_seq, exec_kcall]
  simp only [List.map_cons, List.map_nil, IExp.eval_const, IExp.eval_zero]
  rw [hc₃, Option.map_some, Option.bind_some]
  have key : ∀ S : St P K C, S.store = c₃ → ∃ st', exec I (zcopy (ι := ι) p (.const k) (.const r)
      Qf 0 Qa qo).run S = some st' ∧
      (∃ Q : Matrix (Fin k) (Fin r) (K × K), pairLayout.Holds st'.store p Qa qo.eval Q) ∧
      (∀ q b' i, b' ∉ [G, Y, Qf, Rf] →
        blockDisjoint (b', i, 1) (Qa, qo.eval, 2 * (k * r)) = true →
        st'.store.read q b' i = st.store.read q b' i) ∧
      st'.store.shape = st.store.shape := by
    intro S hS
    subst hS
    obtain ⟨Qm, hQm⟩ : ∃ Q : Matrix (Fin k) (Fin r) (K × K),
        pairLayout.Holds S.store p Qf (0 : IExp ℕ).eval Q :=
      ⟨_, fun i (j : Fin r) t => hQf i ⟨j, lt_of_lt_of_le j.isLt hr⟩ t⟩
    obtain ⟨st', hst'⟩ := exists_exec_zcopy (I := I) p k r (st := S) (X := Qf) (xo := 0)
      (Y := Qa) (yo := qo) hQm (hne (Ne.symm hQfQa)) ⟨lA, hsh₃ ▸ hQas, hlA⟩
    obtain ⟨hQa', hfrc, hshc, -⟩ := holds_of_exec_zcopy (I := I) p k r hQm (hne (Ne.symm hQfQa))
      hst'
    refine ⟨st', hst', ⟨_, hQa'⟩, fun q b' i hb' hbd => ?_, hshc.trans hsh₃⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hb'
    rw [hfrc q b' i hbd, hfr₃ q b' i (hne hb'.2.2.1) (hne hb'.2.2.2),
      Store.read_of_writeBlock_eq_some_of_ne (hk₁.symm.trans hc₂) (Or.inl hb'.2.1),
      hfr₁ q b' i hb'.1]
  exact key _ rfl

/-- Deflation on stored samples succeeds under the standard model with every value in range,
if the kernels are routines on pairs and the buffers `G`, `Y`, `Qf`, `Rf` have $2n^2$ cells and the
block at `qo` of `Qa` fits (hypotheses on the inputs as `NLAlib.holds_of_exec_eighDeflateBlock`).
No printed source. -/
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
  exact (exists_exec_eighDeflateBlock_facts hmm hqr hsem p n k r d lo hk hr b hP hsq
    (fun w hw => ⟨_, hSg w hw⟩) hbufs hsqb hscr hQa).imp fun _ h => h.1

omit [Inhabited K] in
/-- A conjugate transpose keeps the shape of the store and the tape positions. -/
theorem shape_pos_of_exec_zconjTranspose_compress (p : P) (m n : ℕ) {X Y : ℕ}
    {xo yo : IExp ℕ} {st st' : St P K C}
    (h : exec I (zconjTranspose (ι := ι) p (.const m) (.const n) X xo Y yo).run st = some st') :
    st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  have hins : ∀ {i : Instr P ℕ ℕ} {s s' : St P K C}, (∀ q d x, i ≠ .draw q d x) →
      exec I (.instr i) s = some s' → s'.store.shape = s.store.shape ∧ s'.pos = s.pos := by
    intro i s s' hi hs
    rw [exec_instr] at hs
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hs
    refine ⟨Instr.shape_of_run_eq_some hr, ?_⟩
    cases i with
    | draw q d x => exact absurd rfl (hi q d x)
    | _ => simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr; aesop
  change exec I (.seq (.named _ _ (.seq (.loop _ _) .skip)) .skip) st = some st' at h
  rw [exec_seq_skip, exec_named, exec_seq_skip] at h
  refine forall_of_exec_loop_eq_some I
    (fun _ s => s.store.shape = st.store.shape ∧ s.pos = st.pos) ⟨rfl, rfl⟩ ?_ h
  rintro j - s₁ s₂ ⟨hsh, hps⟩ hex
  change exec I (.seq (.loop _ _) .skip) s₁ = some s₂ at hex
  rw [exec_seq_skip] at hex
  refine forall_of_exec_loop_eq_some I
    (fun _ s => s.store.shape = st.store.shape ∧ s.pos = st.pos) ⟨hsh, hps⟩ ?_ hex
  rintro i - s₃ s₄ ⟨hsh, hps⟩ hex
  change exec I (.seq (.instr (.copy _ _ _)) (.seq (.instr (.un _ _ _ _)) .skip)) s₃ =
    some s₄ at hex
  rw [exec_seq] at hex
  obtain ⟨s₅, h₅, hex⟩ := Option.bind_eq_some_iff.mp hex
  rw [exec_seq_skip] at hex
  obtain ⟨hsh₅, hps₅⟩ := hins (by intro _ _ _ h; cases h) h₅
  obtain ⟨hsh₄, hps₄⟩ := hins (by intro _ _ _ h; cases h) hex
  exact ⟨hsh₄.trans (hsh₅.trans hsh), hps₄.trans (hps₅.trans hps)⟩

omit [Inhabited K] in
/-- Blocks of distinct buffers are disjoint. -/
theorem blockDisjoint_of_ne_compress {b b' i i' l l' : ℕ} (h : b ≠ b') :
    blockDisjoint (b, i, l) (b', i', l') = true := by
  simp [blockDisjoint, h]

omit [Inhabited K] in
/-- Disjointness of blocks is symmetric. -/
theorem blockDisjoint_comm_compress {x y : ℕ × ℕ × ℕ} (h : blockDisjoint x y = true) :
    blockDisjoint y x = true := by
  simp only [blockDisjoint, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
  omega

end NLAlib
