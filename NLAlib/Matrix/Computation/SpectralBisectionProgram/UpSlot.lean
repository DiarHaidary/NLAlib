/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.KernelCall
public import NLAlib.Computation.RoutineFrames
public import NLAlib.Matrix.Computation.SpectralBisectionProgramTree
public import NLAlib.Computation.BLASCongr
public import NLAlib.Matrix.Computation.PairKernels
public import NLAlib.Matrix.Computation.SpectralBisectionProgram.Levels

/-!
# A slot of the upward level of the spectral bisection program

The blocks of one level of the upward pass of `NLAlib.eighProg` (`NLAlib.eighUpLevel`) at constant
sizes, the branch each node and slot takes, and what a successful slot computes: a node with one
child adds back its shift, a split multiplies the children's bases by the deflation bases, as the
machine of the interpretation computes them.

## Main results

* `NLAlib.eighUpShift`, `NLAlib.eighUpSplit`, `NLAlib.eighUpNode`, `NLAlib.eighUpSlot`: the blocks
  of a level at constant sizes.
* `NLAlib.exec_eighUpNode_of_readsIdx_one`, `NLAlib.exec_eighUpNode_of_readsIdx_shift`,
  `NLAlib.exec_eighUpNode_of_readsIdx_four`, `NLAlib.exec_eighUpSlot_of_readsIdx`: the branch a
  node or a slot takes.
* `NLAlib.holds_of_exec_eighUpSlot`: what a successful slot computes
  (`NLAlib.EighArenas.UpSlotsDone`).
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}

/-! ### The blocks of a level -/

omit [DecidableEq P] in
/-- The one-child branch of the node of size $k$ at slot $lo$ of depth $d$ in
`NLAlib.eighUpLevel` ($n$ slots per level): the child's output block (depth $d + 1$) copied into
the node's, the shift in the cell `tc` added to the child's eigenvalues. -/
def eighUpShift (p : P) (n d lo k : ℕ) (H : EighArenas) (tc : Cell ℕ ℕ) :
    Builder P ι ℕ ℕ Unit := do
  zcopy p (IExp.var k) (IExp.var k) H.Ua (eighBlockOff (IExp.const n) (IExp.const d + 1)
    (IExp.var lo)) H.Ua (eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo))
  forRange (IExp.var k) fun i => ins (.bin p .add
    ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo) + IExp.var i⟩
    ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d + 1) (IExp.var lo) + IExp.var i⟩ tc)

omit [DecidableEq P] in
/-- The split branch of the node of size $k$ at slot $lo$ of depth $d$ in `NLAlib.eighUpLevel`,
split at $k_+$ ($n$ slots per level, shift in cell $0$ of buffer `t`): the products of the bases
of depth $d$ and the children's outputs into the two column blocks of the node's output, the shift
added to the eigenvalues of the positive child and subtracted from those of the negative one. -/
def eighUpSplit (p : P) (mm : ι) (n d lo k kp t : ℕ) (H : EighArenas) :
    Builder P ι ℕ ℕ Unit := do
  let qo := eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo)
  stmt (.kcall mm p [IExp.var k, IExp.var kp, IExp.var kp]
    [(H.Qa, qo), (H.Ua, eighBlockOff (IExp.const n) (IExp.const d + 1) (IExp.var lo))]
    [(H.Ua, eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo))])
  stmt (.kcall mm p [IExp.var k, IExp.var k - IExp.var kp, IExp.var k - IExp.var kp]
    [(H.Qa, qo + 2 * (IExp.var k * IExp.var kp)),
      (H.Ua, eighBlockOff (IExp.const n) (IExp.const d + 1) (IExp.var lo + IExp.var kp))]
    [(H.Ua, eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo) +
      2 * (IExp.var k * IExp.var kp))])
  forRange (IExp.var kp) fun j => ins (.bin p .add
    ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo) + IExp.var j⟩
    ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d + 1) (IExp.var lo) + IExp.var j⟩ ⟨t, 0⟩)
  forRange (IExp.var k - IExp.var kp) fun j => ins (.bin p .sub
    ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo) + IExp.var kp + IExp.var j⟩
    ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d + 1) (IExp.var lo) + IExp.var kp +
      IExp.var j⟩ ⟨t, 0⟩)

omit [DecidableEq P] in
/-- The node of size $k$ at slot $lo$ of depth $d$ in `NLAlib.eighUpLevel` ($n$ slots per level,
shift $\sigma$ and $-\sigma$ in cells $0$ and $1$ of buffer `t`): the kind binder and its three
branches (`NLAlib.eighUpShift` for kinds $2$ and $3$, `NLAlib.eighUpSplit` for kind $4$). -/
def eighUpNode (p : P) (mm : ι) (n d lo k t : ℕ) (H : EighArenas) : Builder P ι ℕ ℕ Unit :=
  Builder.bindIdx p ⟨H.Kd, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo)⟩ 4 fun c => do
    eighWhen (eighEqInd (IExp.var c) 2) (eighUpShift p n d lo k H ⟨t, 0⟩)
    eighWhen (eighEqInd (IExp.var c) 3) (eighUpShift p n d lo k H ⟨t, 1⟩)
    eighWhen (eighEqInd (IExp.var c) 4) <|
      Builder.bindIdx p ⟨H.Kp, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo)⟩
        (IExp.var k) fun kp => eighUpSplit p mm n d lo k kp t H

omit [DecidableEq P] in
/-- The slot $lo$ of depth $d$ in `NLAlib.eighUpLevel` ($n$ slots per level, shift cells in
buffer `t`): the size binder, and the node (`NLAlib.eighUpNode`) if the size is positive. -/
def eighUpSlot (p : P) (mm : ι) (n d lo t : ℕ) (H : EighArenas) : Builder P ι ℕ ℕ Unit :=
  Builder.bindIdx p ⟨H.Sz, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo)⟩
    (IExp.const n - IExp.var lo) fun k => eighWhen (IExp.var k) (eighUpNode p mm n d lo k t H)

/-! ### Steps, loops and handles -/

/-- A one-child step adds back the shift $\pm\mathrm{fl}(R/2)$. -/
private theorem eq_of_eighStep_eq_shift {F Su Sg : Type*} [Inhabited Sg]
    {M : FloatMachine F Su Sg} {N fuel k ℓ : ℕ} {R₀ β R ε : F} {A : Matrix (Fin k) (Fin k) (F × F)}
    {s : EighSample Su Sg N} {b : Bool} {A' : Matrix (Fin k) (Fin k) (F × F)} {σ : F}
    (h : eighStep M N fuel R₀ β A R ε ℓ s = .shift b A' σ) :
    σ = if b then M.div R (M.ofNat 2) else M.neg (M.div R (M.ofNat 2)) := by
  unfold eighStep at h
  dsimp only at h
  split_ifs at h <;> cases h <;> rfl

/-- A split by `NLAlib.eighStep` (of a node of size $k$ with window $R$, on the sample `s`) at
$k_+$ adds back the shift $\mathrm{fl}(R/2)$ and has $0 < k_+ < k$. -/
theorem eq_div_and_pos_and_lt_of_eighStep_eq_split {F Su Sg : Type*} [Inhabited Sg]
    {M : FloatMachine F Su Sg} {N fuel k ℓ : ℕ} {R₀ β R ε : F} {A : Matrix (Fin k) (Fin k) (F × F)}
    {s : EighSample Su Sg N} {kp : ℕ} {hkp : kp ≤ k} {Qp : Matrix (Fin k) (Fin kp) (F × F)}
    {Qm : Matrix (Fin k) (Fin (k - kp)) (F × F)} {Ap : Matrix (Fin kp) (Fin kp) (F × F)}
    {Am : Matrix (Fin (k - kp)) (Fin (k - kp)) (F × F)} {σ : F}
    (h : eighStep M N fuel R₀ β A R ε ℓ s = .split kp hkp Qp Qm Ap Am σ) :
    σ = M.div R (M.ofNat 2) ∧ 0 < kp ∧ kp < k := by
  unfold eighStep at h
  dsimp only at h
  split_ifs at h with h1 h2 h3 h4
  cases h
  exact ⟨rfl, Nat.pos_of_ne_zero h4, lt_of_le_of_ne (min_le_left _ _) h3⟩

/-- A successful loop of binary operations `Y[f w] ← Y[g w] ∘ c`, $w < m$, whose written cells
are distinct and never read, with `c` outside `Y`: the written cells hold the results, every other
cell is kept, and so are the store shape and the tape positions. -/
theorem shape_and_read_of_exec_loop_bin {p : P} {op : BinOp} {m : IExp ℕ} {Y : ℕ}
    {c : Cell ℕ ℕ} {f g : ℕ → IExp ℕ} {st st' : St P K C} (hYc : c.buf ≠ Y)
    (hfg : ∀ w < m.eval, ∀ w' < m.eval, (f w).eval ≠ (g w').eval)
    (hf : ∀ w < m.eval, ∀ w' < m.eval, (f w).eval = (f w').eval → w = w')
    (h : exec I (.loop m fun w => .seq (.instr (.bin p op ⟨Y, f w⟩ ⟨Y, g w⟩ c)) .skip) st =
      some st') :
    st'.store.shape = st.store.shape ∧ st'.pos = st.pos ∧
      (∀ w < m.eval, ∀ x z, st.store.read p Y (g w).eval = some x →
        st.store.read p c.buf c.idx.eval = some z →
        st'.store.read p Y (f w).eval = some ((I.sem.bin p op x z).getD default)) ∧
      ∀ q b i, (b ≠ Y ∨ ∀ w < m.eval, (f w).eval ≠ i) →
        st'.store.read q b i = st.store.read q b i := by
  refine forall_of_exec_loop_eq_some I (fun w s => s.store.shape = st.store.shape ∧
      s.pos = st.pos ∧
      (∀ w' < w, ∀ x z, st.store.read p Y (g w').eval = some x →
        st.store.read p c.buf c.idx.eval = some z →
        s.store.read p Y (f w').eval = some ((I.sem.bin p op x z).getD default)) ∧
      ∀ q b i, (b ≠ Y ∨ ∀ w' < w, (f w').eval ≠ i) → s.store.read q b i = st.store.read q b i)
    ⟨rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ => rfl⟩ ?_ h
  rintro w hw s₁ s₂ ⟨hsh, hps, hrd, hfr⟩ hex
  rw [exec_seq_skip, exec_instr] at hex
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hex
  obtain ⟨_, ⟨a, ha, b, hb, v, hv, s', hw', rfl⟩, rfl⟩ := hex
  have hga : s₁.store.read p Y (g w).eval = st.store.read p Y (g w).eval :=
    hfr p Y _ (Or.inr fun w' hw' => hfg w' (by omega) w hw)
  have hcb : s₁.store.read p c.buf c.idx.eval = st.store.read p c.buf c.idx.eval :=
    hfr p _ _ (Or.inl hYc)
  refine ⟨(Store.shape_of_write_eq_some hw').trans hsh, hps, fun w' hw'' x z hx hz => ?_,
    fun q b' i hb' => ?_⟩
  · by_cases hww : w' = w
    · subst hww
      rw [Store.read_of_write_eq_some hw']
      rw [hga, hx] at ha
      rw [hcb, hz] at hb
      cases ha; cases hb
      simp [hv]
    · have hlt : w' < w := lt_of_le_of_ne (Nat.lt_succ_iff.mp hw'') hww
      rw [Store.read_of_write_eq_some_of_ne hw' (Or.inr fun e => hww (hf w' (by omega) w hw e))]
      exact hrd w' hlt x z hx hz
  · rw [Store.read_of_write_eq_some_of_ne hw' ?_]
    · exact hfr q b' i (hb'.imp_right fun h w' hw' => h w' (by omega))
    · exact hb'.imp_right fun h => (h w (Nat.lt_succ_self w)).symm

omit [Inhabited K] in
/-- The column map of an assembled split: a column below $k_+$ is on the positive side. -/
private theorem finSumFinEquiv_symm_apply_lt {k kp : ℕ} (h : kp ≤ k) (j : Fin k)
    (hj : (j : ℕ) < kp) :
    ((finCongr (Nat.add_sub_of_le h).symm).trans finSumFinEquiv.symm) j = Sum.inl ⟨j, hj⟩ := by
  simp only [Equiv.trans_apply]
  rw [Equiv.symm_apply_eq]
  ext; simp

omit [Inhabited K] in
/-- The column map of an assembled split: a column from $k_+$ is on the negative side. -/
private theorem finSumFinEquiv_symm_apply_ge {k kp : ℕ} (h : kp ≤ k) (j : Fin k)
    (hj : kp ≤ (j : ℕ)) :
    ((finCongr (Nat.add_sub_of_le h).symm).trans finSumFinEquiv.symm) j =
      Sum.inr ⟨j - kp, by omega⟩ := by
  simp only [Equiv.trans_apply]
  rw [Equiv.symm_apply_eq]
  ext; simp; omega

omit [AddMonoid C] [Inhabited K] in
/-- Two column blocks stored one after the other hold the matrix of their columns. -/
private theorem holds_fromCols {s : Store P K} {p : P} {b off k kp : ℕ} (h : kp ≤ k)
    {X : Matrix (Fin k) (Fin kp) (K × K)} {Y : Matrix (Fin k) (Fin (k - kp)) (K × K)}
    (hX : pairLayout.Holds s p b off X) (hY : pairLayout.Holds s p b (off + 2 * (k * kp)) Y) :
    pairLayout.Holds s p b off ((Matrix.fromCols X Y).submatrix id
      ((finCongr (Nat.add_sub_of_le h).symm).trans finSumFinEquiv.symm)) := by
  intro i j t
  by_cases hj : (j : ℕ) < kp
  · simp only [Matrix.submatrix_apply, id, finSumFinEquiv_symm_apply_lt h j hj,
      Matrix.fromCols_apply_inl]
    exact hX i ⟨j, hj⟩ t
  · simp only [Matrix.submatrix_apply, id, finSumFinEquiv_symm_apply_ge h j (by omega),
      Matrix.fromCols_apply_inr]
    rw [← hY i ⟨j - kp, by omega⟩ t]
    congr 1
    simp only [pairLayout]
    have : (j : ℕ) = kp + (j - kp) := by omega
    conv_lhs => rw [this]
    ring

/-- The one-child branch of a node in the upward pass (`NLAlib.eighUpShift`, node of size $k$ at
slot $lo$, $lo + k \le n$): the child's output copied, the shift added to its eigenvalues. -/
private theorem holds_of_exec_eighUpShift (p : P) (n d lo k : ℕ) (H : EighArenas) (tc : Cell ℕ ℕ)
    {s s' : St P K C} (hk : lo + k ≤ n) (hUE : H.Ua ≠ H.Ea) (htc : tc.buf ≠ H.Ea)
    (htcU : tc.buf ≠ H.Ua) {U : Matrix (Fin k) (Fin k) (K × K)} {e : Fin k → K} {σ : K}
    (hU : pairLayout.Holds s.store p H.Ua (2 * (n * n) * (d + 1) + 2 * n * lo) U)
    (hE : ∀ i : Fin k, s.store.read p H.Ea (n * (d + 1) + lo + i) = some (e i))
    (hσ : s.store.read p tc.buf tc.idx.eval = some σ)
    (h : exec I (eighUpShift (ι := ι) p n d lo k H tc).run s = some s') :
    s'.store.shape = s.store.shape ∧ s'.pos = s.pos ∧
      pairLayout.Holds s'.store p H.Ua (2 * (n * n) * d + 2 * n * lo) U ∧
      (∀ i : Fin k, s'.store.read p H.Ea (n * d + lo + i) =
        some ((I.sem.bin p .add (e i) σ).getD default)) ∧
      ∀ q b i, (b ≠ H.Ua ∨ i < 2 * (n * n) * d + 2 * n * lo ∨
          2 * (n * n) * d + 2 * n * lo + 2 * (k * k) ≤ i) →
        (b ≠ H.Ea ∨ i < n * d + lo ∨ n * d + lo + k ≤ i) →
        s'.store.read q b i = s.store.read q b i := by
  rw [eighUpShift, exec_run_bind I (b := zcopy (ι := ι) p (IExp.var k) (IExp.var k) H.Ua
    (eighBlockOff (IExp.const n) (IExp.const d + 1) (IExp.var lo)) H.Ua
    (eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo))) (fun _ => rfl)] at h
  obtain ⟨s₁, hz, h⟩ := Option.bind_eq_some_iff.mp h
  rw [exec_zcopy_congr] at hz
  have hkk : k * k ≤ n * n := Nat.mul_le_mul (by omega) (by omega)
  obtain ⟨hU₁, hfr₁, hsh₁, hps₁⟩ := holds_of_exec_zcopy p k k
    (xo := eighBlockOff (IExp.const n) (IExp.const d + 1) (IExp.var lo))
    (yo := eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo)) (A := U)
    (by simpa [eighBlockOff, Nat.mul_succ] using hU)
    (blockDisjoint_iff.2 (Or.inr (Or.inl (by
      simp only [eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const,
        IExp.eval_var, IExp.eval_ofNat]
      rw [Nat.mul_succ]; omega)))) hz
  simp only [eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var,
    IExp.eval_ofNat] at hU₁ hfr₁
  change exec I (.seq (.loop _ _) .skip) _ = _ at h
  rw [exec_seq_skip] at h
  obtain ⟨hsh₂, hps₂, hE₂, hfr₂⟩ := shape_and_read_of_exec_loop_bin htc (by
    intro w hw w' hw'
    simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var,
      IExp.eval_ofNat] at hw hw' ⊢
    rw [Nat.mul_succ]; omega) (by
    intro w hw w' hw' e
    simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var] at e
    omega) h
  simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var,
    IExp.eval_ofNat] at hE₂ hfr₂
  refine ⟨hsh₂.trans hsh₁, hps₂.trans hps₁,
    hU₁.of_forall_read_eq fun i _ _ => hfr₂ p _ i (Or.inl hUE), fun i => ?_,
    fun q b i hU' hE' => ?_⟩
  · have hx : s₁.store.read p H.Ea (n * (d + 1) + lo + i) = some (e i) := by
      rw [hfr₁ p _ _ (blockDisjoint_iff.2 (Or.inl (Ne.symm hUE)))]; exact hE i
    exact hE₂ i i.isLt (e i) σ (by rw [Nat.mul_succ] at hx ⊢; simpa [Nat.mul_succ] using hx)
      (by rw [hfr₁ p _ _ (blockDisjoint_iff.2 (Or.inl htcU))]; exact hσ)
  · rw [hfr₂ q b i (hE'.imp_right fun h w hw => by omega), hfr₁ q b i (blockDisjoint_iff.2 hU')]

omit [AddMonoid C] in
/-- The two kernel calls of the split branch (`NLAlib.eighUpSplit`): the products of the bases
and the children's outputs in the two column blocks of the node's output, every cell outside them
kept. -/
private theorem holds_of_kcallStore_eighUpSplit {mm : ι}
    (hmm : IsMatMulKernel I mm pairLayout mmR) (p : P) (n d lo k kp : ℕ) (H : EighArenas)
    {s u₁ u₂ : Store P K} (hk : lo + k ≤ n) (hkp : kp < k) (hUQ : H.Ua ≠ H.Qa)
    {Qp : Matrix (Fin k) (Fin kp) (K × K)} {Qm : Matrix (Fin k) (Fin (k - kp)) (K × K)}
    {Up : Matrix (Fin kp) (Fin kp) (K × K)} {Um : Matrix (Fin (k - kp)) (Fin (k - kp)) (K × K)}
    (hQp : pairLayout.Holds s p H.Qa (2 * (n * n) * d + 2 * n * lo) Qp)
    (hQm : pairLayout.Holds s p H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (k * kp)) Qm)
    (hUp : pairLayout.Holds s p H.Ua (2 * (n * n) * (d + 1) + 2 * n * lo) Up)
    (hUm : pairLayout.Holds s p H.Ua (2 * (n * n) * (d + 1) + 2 * n * (lo + kp)) Um)
    (hu₁ : I.kcallStore mm p [k, kp, kp] [(H.Qa, 2 * (n * n) * d + 2 * n * lo),
      (H.Ua, 2 * (n * n) * (d + 1) + 2 * n * lo)] [(H.Ua, 2 * (n * n) * d + 2 * n * lo)] s =
      some u₁)
    (hu₂ : I.kcallStore mm p [k, k - kp, k - kp]
      [(H.Qa, 2 * (n * n) * d + 2 * n * lo + 2 * (k * kp)),
        (H.Ua, 2 * (n * n) * (d + 1) + 2 * n * (lo + kp))]
      [(H.Ua, 2 * (n * n) * d + 2 * n * lo + 2 * (k * kp))] u₁ = some u₂) :
    pairLayout.Holds u₂ p H.Ua (2 * (n * n) * d + 2 * n * lo)
        ((Matrix.fromCols (mmR Qp Up) (mmR Qm Um)).submatrix id
          ((finCongr (Nat.add_sub_of_le hkp.le).symm).trans finSumFinEquiv.symm)) ∧
      ∀ q b i, (b ≠ H.Ua ∨ i < 2 * (n * n) * d + 2 * n * lo ∨
          2 * (n * n) * d + 2 * n * lo + 2 * (k * k) ≤ i) →
        u₂.read q b i = s.read q b i := by
  have hkk : k * k ≤ n * n := Nat.mul_le_mul (by omega) (by omega)
  have hkpk : k * kp ≤ k * k := Nat.mul_le_mul_left k hkp.le
  have hsplit : k * kp + k * (k - kp) = k * k := by
    rw [← Nat.mul_add, Nat.add_sub_of_le hkp.le]
  have hlok : lo * n + k * n ≤ n * n := by nlinarith
  have hc1 : (k - kp) * k = k * (k - kp) := Nat.mul_comm _ _
  have hc2 : kp * k = k * kp := Nat.mul_comm _ _
  obtain ⟨hP, hfr₁⟩ := hmm.holds_of_kcallStore_eq_some pairLayout.get_put p (l := k) (m := kp)
    (n := kp) (a := (H.Qa, 2 * (n * n) * d + 2 * n * lo))
    (b := (H.Ua, 2 * (n * n) * (d + 1) + 2 * n * lo))
    (c := (H.Ua, 2 * (n * n) * d + 2 * n * lo)) hQp hUp (blockDisjoint_iff.2 (Or.inl hUQ))
    (blockDisjoint_iff.2 (Or.inr (Or.inl (by
      simp only [pairLayout]; rw [Nat.mul_succ]; nlinarith)))) hu₁
  have hQm₁ := hQm.of_forall_read_eq fun i _ _ =>
    hfr₁ p _ i (blockDisjoint_iff.2 (Or.inl (Ne.symm hUQ)))
  have hUm₁ := hUm.of_forall_read_eq fun i hi _ => hfr₁ p _ i (blockDisjoint_iff.2
    (Or.inr (Or.inr (by simp only [pairLayout]; rw [Nat.mul_succ]; nlinarith))))
  obtain ⟨hM, hfr₂⟩ := hmm.holds_of_kcallStore_eq_some pairLayout.get_put p (l := k)
    (m := k - kp) (n := k - kp)
    (a := (H.Qa, 2 * (n * n) * d + 2 * n * lo + 2 * (k * kp)))
    (b := (H.Ua, 2 * (n * n) * (d + 1) + 2 * n * (lo + kp)))
    (c := (H.Ua, 2 * (n * n) * d + 2 * n * lo + 2 * (k * kp))) hQm₁ hUm₁
    (blockDisjoint_iff.2 (Or.inl hUQ))
    (blockDisjoint_iff.2 (Or.inr (Or.inl (by
      simp only [pairLayout]; rw [Nat.mul_succ]; nlinarith)))) (by convert hu₂ using 3)
  have hP₂ := hP.of_forall_read_eq fun i _ hi => hfr₂ p _ i (blockDisjoint_iff.2
    (Or.inr (Or.inl (by simp only [pairLayout] at hi; nlinarith))))
  refine ⟨holds_fromCols hkp.le hP₂ hM, fun q b i hU' => ?_⟩
  rw [hfr₂ q b i (blockDisjoint_iff.2 (hU'.imp_right fun h => by simp only [pairLayout]; omega)),
    hfr₁ q b i (blockDisjoint_iff.2 (hU'.imp_right fun h => by simp only [pairLayout]; omega))]

/-- The split branch of a node in the upward pass (`NLAlib.eighUpSplit`, node of size $k$ at slot
$lo$, $lo + k \le n$, split at $k_+ < k$): the two products into the column blocks of the node's
output, the shifted eigenvalues of the two children. -/
private theorem holds_of_exec_eighUpSplit {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (p : P) (n d lo k kp t : ℕ) (H : EighArenas) {s s' : St P K C} (hk : lo + k ≤ n)
    (hkp : kp < k) (hUE : H.Ua ≠ H.Ea) (hUQ : H.Ua ≠ H.Qa) (htE : t ≠ H.Ea) (htU : t ≠ H.Ua)
    {Qp : Matrix (Fin k) (Fin kp) (K × K)} {Qm : Matrix (Fin k) (Fin (k - kp)) (K × K)}
    {Up : Matrix (Fin kp) (Fin kp) (K × K)} {Um : Matrix (Fin (k - kp)) (Fin (k - kp)) (K × K)}
    {ep : Fin kp → K} {em : Fin (k - kp) → K} {σ : K}
    (hQp : pairLayout.Holds s.store p H.Qa (2 * (n * n) * d + 2 * n * lo) Qp)
    (hQm : pairLayout.Holds s.store p H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (k * kp)) Qm)
    (hUp : pairLayout.Holds s.store p H.Ua (2 * (n * n) * (d + 1) + 2 * n * lo) Up)
    (hUm : pairLayout.Holds s.store p H.Ua (2 * (n * n) * (d + 1) + 2 * n * (lo + kp)) Um)
    (hEp : ∀ j : Fin kp, s.store.read p H.Ea (n * (d + 1) + lo + j) = some (ep j))
    (hEm : ∀ j : Fin (k - kp), s.store.read p H.Ea (n * (d + 1) + (lo + kp) + j) = some (em j))
    (hσ : s.store.read p t 0 = some σ)
    (h : exec I (eighUpSplit p mm n d lo k kp t H).run s = some s') :
    s'.store.shape = s.store.shape ∧ s'.pos = s.pos ∧
      pairLayout.Holds s'.store p H.Ua (2 * (n * n) * d + 2 * n * lo)
        ((Matrix.fromCols (mmR Qp Up) (mmR Qm Um)).submatrix id
          ((finCongr (Nat.add_sub_of_le hkp.le).symm).trans finSumFinEquiv.symm)) ∧
      (∀ j : Fin kp, s'.store.read p H.Ea (n * d + lo + j) =
        some ((I.sem.bin p .add (ep j) σ).getD default)) ∧
      (∀ j : Fin (k - kp), s'.store.read p H.Ea (n * d + lo + kp + j) =
        some ((I.sem.bin p .sub (em j) σ).getD default)) ∧
      ∀ q b i, (b ≠ H.Ua ∨ i < 2 * (n * n) * d + 2 * n * lo ∨
          2 * (n * n) * d + 2 * n * lo + 2 * (k * k) ≤ i) →
        (b ≠ H.Ea ∨ i < n * d + lo ∨ n * d + lo + k ≤ i) →
        s'.store.read q b i = s.store.read q b i := by
  change exec I (.seq (.kcall _ _ _ _ _) (.seq (.kcall _ _ _ _ _)
    (.seq (.loop _ _) (.seq (.loop _ _) .skip)))) s = some s' at h
  rw [exec_seq, exec_kcall] at h
  obtain ⟨s₁, h₁, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨u₁, hu₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
  rw [exec_seq, exec_kcall] at h
  obtain ⟨s₂, h₂, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨u₂, hu₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
  rw [exec_seq] at h
  obtain ⟨s₃, h₃, h⟩ := Option.bind_eq_some_iff.mp h
  rw [exec_seq_skip] at h
  simp only [List.map_cons, List.map_nil, eighBlockOff, IExp.eval_add, IExp.eval_mul,
    IExp.eval_const, IExp.eval_var, IExp.eval_ofNat, IExp.eval_sub] at hu₁ hu₂
  obtain ⟨hP, hfrK⟩ := holds_of_kcallStore_eighUpSplit hmm p n d lo k kp H hk hkp hUQ hQp hQm
    hUp hUm hu₁ hu₂
  obtain ⟨hsh₃, hps₃, hE₃, hfr₃⟩ := shape_and_read_of_exec_loop_bin (c := ⟨t, 0⟩) htE (by
    intro w hw w' hw'
    simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var,
      IExp.eval_ofNat] at hw hw' ⊢
    rw [Nat.mul_succ]; omega) (by
    intro w hw w' hw' e
    simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var] at e
    omega) h₃
  obtain ⟨hsh₄, hps₄, hE₄, hfr₄⟩ := shape_and_read_of_exec_loop_bin (c := ⟨t, 0⟩) htE (by
    intro w hw w' hw'
    simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var,
      IExp.eval_ofNat, IExp.eval_sub] at hw hw' ⊢
    rw [Nat.mul_succ]; omega) (by
    intro w hw w' hw' e
    simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var] at e
    omega) h
  simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var,
    IExp.eval_ofNat, IExp.eval_sub] at hE₃ hfr₃ hE₄ hfr₄
  have hrdE : ∀ i, u₂.read p H.Ea i = s.store.read p H.Ea i := fun i =>
    hfrK p _ i (Or.inl (Ne.symm hUE))
  have hrdt : u₂.read p t 0 = some σ := (hfrK p _ _ (Or.inl htU)).trans hσ
  refine ⟨hsh₄.trans (hsh₃.trans ((Interp.shape_of_kcallStore_eq_some hu₂).trans
    (Interp.shape_of_kcallStore_eq_some hu₁))), hps₄.trans hps₃,
    hP.of_forall_read_eq fun i _ _ => by rw [hfr₄ p _ i (Or.inl hUE), hfr₃ p _ i (Or.inl hUE)],
    fun j => ?_, fun j => ?_, fun q b i hU' hE' => ?_⟩
  · rw [hfr₄ p _ _ (Or.inr fun w hw => by omega)]
    exact hE₃ j j.isLt (ep j) σ (by rw [hrdE, Nat.mul_succ]; simpa [Nat.mul_succ] using hEp j) hrdt
  · refine hE₄ j j.isLt (em j) σ ?_ (by rw [hfr₃ p _ _ (Or.inl htE)]; exact hrdt)
    rw [hfr₃ p _ _ (Or.inr fun w hw => by rw [Nat.mul_succ]; omega), hrdE,
      show n * (d + 1) + lo + kp + j = n * (d + 1) + (lo + kp) + j by omega]
    exact hEm j
  · rw [hfr₄ q b i (hE'.imp_right fun h w hw => by omega),
      hfr₃ q b i (hE'.imp_right fun h w hw => by omega), hfrK q b i hU']

omit [Inhabited K] in
/-- A loop of no trips, then `t`, runs as `t`. -/
theorem exec_seq_loop_of_eval_eq_zero {e : IExp ℕ} {b : ℕ → Stmt P ι ℕ ℕ} {t : Stmt P ι ℕ ℕ}
    {s : St P K C} (he : e.eval = 0) : exec I (.seq (.loop e b) t) s = exec I t s := by
  rw [exec_seq, exec_loop, he]
  simp

omit [Inhabited K] in
/-- A loop of one trip, then `t`, runs as its body at index $0$, then `t`. -/
theorem exec_seq_loop_of_eval_eq_one {e : IExp ℕ} {b : ℕ → Stmt P ι ℕ ℕ} {t : Stmt P ι ℕ ℕ}
    {s : St P K C} (he : e.eval = 1) :
    exec I (.seq (.loop e b) t) s = (exec I (b 0) s).bind (exec I t) := by
  rw [exec_seq, exec_loop, he]
  simp [List.range_one]

omit [AddMonoid C] [Inhabited K] in
/-- The distinct handles of the arenas that the upward pass touches, if the eight handles of `H`
are distinct. -/
theorem EighArenas.ua_ne_ea_and_of_nodup {H : EighArenas} (hnd : H.handles.Nodup) :
    H.Ua ≠ H.Ea ∧ H.Ua ≠ H.Qa ∧ H.Kd ≠ H.Ua ∧ H.Kd ≠ H.Ea ∧ H.Kp ≠ H.Ua ∧ H.Kp ≠ H.Ea ∧
      H.Qa ≠ H.Ea ∧ H.Sz ≠ H.Ua ∧ H.Sz ≠ H.Ea ∧ H.Ma ≠ H.Ua ∧ H.Ma ≠ H.Ea ∧ H.Lv ≠ H.Ua ∧
      H.Lv ≠ H.Ea := by
  simp only [EighArenas.handles] at hnd
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro e <;> simp [e] at hnd

omit [AddMonoid C] [Inhabited K] in
/-- A cell of the output arena of `H` (distinct handles) at level $d$ lies in the block of depth
$d$. -/
theorem EighArenas.mul_le_and_lt_of_levelCell_ua {H : EighArenas} {n d i : ℕ}
    (hnd : H.handles.Nodup) (h : H.LevelCell n d H.Ua i) :
    2 * (n * n) * d ≤ i ∧ i < 2 * (n * n) * (d + 1) := by
  obtain ⟨h1, -, h3, -, h5, -, -, h8, -, -, -, h12, -⟩ := H.ua_ne_ea_and_of_nodup hnd
  rcases h with ⟨-, h⟩ | ⟨hb, -⟩ | ⟨hb, -⟩
  · exact h
  · rcases hb with hb | hb | hb | hb
    exacts [absurd hb h1, absurd hb.symm h8, absurd hb.symm h3, absurd hb.symm h5]
  · exact absurd hb.symm h12

omit [AddMonoid C] [Inhabited K] in
/-- A cell of the eigenvalue arena of `H` (distinct handles) at level $d$ lies in the cells of
depth $d$. -/
theorem EighArenas.mul_le_and_lt_of_levelCell_ea {H : EighArenas} {n d i : ℕ}
    (hnd : H.handles.Nodup) (h : H.LevelCell n d H.Ea i) : n * d ≤ i ∧ i < n * (d + 1) := by
  obtain ⟨h1, -, -, -, -, -, h7, -, -, -, h11, -, h13⟩ := H.ua_ne_ea_and_of_nodup hnd
  rcases h with ⟨hb, -⟩ | ⟨-, h⟩ | ⟨hb, -⟩
  · rcases hb with hb | hb | hb
    exacts [absurd hb.symm h11, absurd hb.symm h1, absurd hb.symm h7]
  · exact h
  · exact absurd hb.symm h13

omit [AddMonoid C] [Inhabited K] in
/-- An index read transfers to a store that reads the cell `i` of buffer `b` as `s` does. -/
theorem readsIdx_of_read_eq {sem : ScalarSem P K} {s s' : Store P K} {p : P} {b i k : ℕ}
    (h : ReadsIdx sem s p b i k) (he : s'.read p b i = s.read p b i) :
    ReadsIdx sem s' p b i k := by
  unfold ReadsIdx at h ⊢
  rw [he]
  exact h

/-! ### The branches of a node and a slot -/

omit [Inhabited K] in
/-- Binding a run into `skip` keeps it. -/
private theorem bind_exec_skip (x : Option (St P K C)) :
    x.bind (exec I (.skip : Stmt P ι ℕ ℕ)) = x := by
  cases x <;> rfl

omit [Inhabited K] in
/-- Binding a run into a loop of no trips, then `t`, binds it into `t`. -/
private theorem bind_exec_seq_loop_of_eval_eq_zero {x : Option (St P K C)} {e : IExp ℕ}
    {b : ℕ → Stmt P ι ℕ ℕ} {t : Stmt P ι ℕ ℕ} (he : e.eval = 0) :
    x.bind (exec I (.seq (.loop e b) t)) = x.bind (exec I t) := by
  cases x
  · rfl
  · exact exec_seq_loop_of_eval_eq_zero he

omit [Inhabited K] in
/-- A leaf node (kind $1$ in its kind cell) of the upward pass only reads its kind. -/
theorem exec_eighUpNode_of_readsIdx_one {mm : ι} {p : P} {n d lo k t : ℕ} {H : EighArenas}
    {s : St P K C} (hc : ReadsIdx I.sem s.store p H.Kd (n * d + lo) 1) :
    exec I (eighUpNode p mm n d lo k t H).run s =
      some { s with cnt := s.cnt + I.charge (.toNat p) } := by
  obtain ⟨v, hv, hk⟩ := Option.bind_eq_some_iff.mp hc
  change exec I (.seq (.bindIdx _ _ _ _) .skip) s = _
  rw [exec_seq_skip, exec_bindIdx_of_read I hv hk (by decide)]
  change exec I (.seq (.loop _ _) (.seq (.loop _ _) (.seq (.loop _ _) .skip))) _ = _
  rw [exec_seq_loop_of_eval_eq_zero rfl, exec_seq_loop_of_eval_eq_zero rfl,
    exec_seq_loop_of_eval_eq_zero rfl, exec_skip]

omit [Inhabited K] in
/-- A one-child node (kind $2$ on the positive side, $3$ on the negative side) of the upward pass
runs as its shift branch, with $\sigma$ (cell $0$ of `t`) or $-\sigma$ (cell $1$). -/
theorem exec_eighUpNode_of_readsIdx_shift {mm : ι} {p : P} {n d lo k t : ℕ} {H : EighArenas}
    {s : St P K C} {b : Bool}
    (hc : ReadsIdx I.sem s.store p H.Kd (n * d + lo) (if b then 2 else 3)) :
    exec I (eighUpNode p mm n d lo k t H).run s =
      exec I (eighUpShift (ι := ι) p n d lo k H ⟨t, if b then 0 else 1⟩).run
        { s with cnt := s.cnt + I.charge (.toNat p) } := by
  obtain ⟨v, hv, hk⟩ := Option.bind_eq_some_iff.mp hc
  change exec I (.seq (.bindIdx _ _ _ _) .skip) s = _
  rw [exec_seq_skip, exec_bindIdx_of_read I hv hk (by split <;> decide)]
  change exec I (.seq (.loop _ _) (.seq (.loop _ _) (.seq (.loop _ _) .skip))) _ = _
  cases b
  · rw [exec_seq_loop_of_eval_eq_zero rfl, exec_seq_loop_of_eval_eq_one rfl,
      bind_exec_seq_loop_of_eval_eq_zero rfl, bind_exec_skip]
    rfl
  · rw [exec_seq_loop_of_eval_eq_one rfl, bind_exec_seq_loop_of_eval_eq_zero rfl,
      bind_exec_seq_loop_of_eval_eq_zero rfl, bind_exec_skip]
    rfl

omit [Inhabited K] in
/-- A split node (kind $4$, $k_+ \le k$ in its split cell) of the upward pass runs as its split
branch. -/
theorem exec_eighUpNode_of_readsIdx_four {mm : ι} {p : P} {n d lo k t kp : ℕ} {H : EighArenas}
    {s : St P K C} (hc : ReadsIdx I.sem s.store p H.Kd (n * d + lo) 4)
    (hkp : ReadsIdx I.sem s.store p H.Kp (n * d + lo) kp) (hkpk : kp ≤ k) :
    exec I (eighUpNode p mm n d lo k t H).run s =
      exec I (eighUpSplit p mm n d lo k kp t H).run
        { s with cnt := s.cnt + I.charge (.toNat p) + I.charge (.toNat p) } := by
  obtain ⟨v, hv, hk⟩ := Option.bind_eq_some_iff.mp hc
  obtain ⟨v', hv', hk'⟩ := Option.bind_eq_some_iff.mp hkp
  change exec I (.seq (.bindIdx _ _ _ _) .skip) s = _
  rw [exec_seq_skip, exec_bindIdx_of_read I hv hk (by decide)]
  change exec I (.seq (.loop _ _) (.seq (.loop _ _) (.seq (.loop _ _) .skip))) _ = _
  rw [exec_seq_loop_of_eval_eq_zero rfl, exec_seq_loop_of_eval_eq_zero rfl,
    exec_seq_loop_of_eval_eq_one rfl, bind_exec_skip]
  change exec I (.seq (.bindIdx _ _ _ _) .skip) _ = _
  rw [exec_seq_skip, exec_bindIdx_of_read I hv' hk' (by exact hkpk)]

omit [Inhabited K] in
/-- An empty slot (size $0$ in its size cell) of the upward pass only reads its size. -/
theorem exec_eighUpSlot_of_readsIdx_zero {mm : ι} {p : P} {n d lo t : ℕ} {H : EighArenas}
    {s : St P K C} (hz : ReadsIdx I.sem s.store p H.Sz (n * d + lo) 0) :
    exec I (eighUpSlot p mm n d lo t H).run s =
      some { s with cnt := s.cnt + I.charge (.toNat p) } := by
  obtain ⟨v, hv, hk⟩ := Option.bind_eq_some_iff.mp hz
  change exec I (.seq (.bindIdx _ _ _ _) .skip) s = _
  rw [exec_seq_skip, exec_bindIdx_of_read I hv hk (Nat.zero_le _)]
  change exec I (.seq (.loop _ _) .skip) _ = _
  rw [exec_seq_loop_of_eval_eq_zero (by simp), exec_skip]

omit [Inhabited K] in
/-- A slot $lo$ with a node of size $1 \le k \le n - lo$ (in its size cell) of the upward pass runs
as the node. -/
theorem exec_eighUpSlot_of_readsIdx {mm : ι} {p : P} {n d lo t k : ℕ} {H : EighArenas}
    {s : St P K C} (hz : ReadsIdx I.sem s.store p H.Sz (n * d + lo) k) (hk1 : 1 ≤ k)
    (hkn : k ≤ n - lo) :
    exec I (eighUpSlot p mm n d lo t H).run s =
      exec I (eighUpNode p mm n d lo k t H).run { s with cnt := s.cnt + I.charge (.toNat p) } := by
  obtain ⟨v, hv, hk⟩ := Option.bind_eq_some_iff.mp hz
  change exec I (.seq (.bindIdx _ _ _ _) .skip) s = _
  rw [exec_seq_skip, exec_bindIdx_of_read I hv hk
    (by simp only [IExp.eval_sub, IExp.eval_const, IExp.eval_var]; omega)]
  change exec I (.seq (.loop _ _) .skip) _ = _
  rw [exec_seq_loop_of_eval_eq_one (by simp; omega), bind_exec_skip]

/-! ### A node, a slot and a level -/

omit [Inhabited K] in
/-- Two nodes at paths of the same length $d$ below the root of size $n \ge 1$, the first at a
slot $lo'$ below the second's $lo$: the first ends before the second starts, and so does its output
block. -/
theorem add_le_and_mul_add_le_of_eighLoc_of_lt {M : FloatMachine K ℕ ℕ} {n F d ℓ₀ : ℕ}
    {R₀ β ε : K} {A : Matrix (Fin n) (Fin n) (K × K)} {a a' : List Bool} {lo lo' : ℕ}
    {y y' : EighNode K} (hn : 1 ≤ n) (ha : a.length = d) (ha' : a'.length = d)
    (hay : eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo, y))
    (hay' : eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a' = some (lo', y')) (hlt : lo' < lo) :
    lo' + y'.k ≤ lo ∧ 2 * n * lo' + 2 * (y'.k * y'.k) ≤ 2 * n * lo := by
  have hb' := eighLoc_bounds hn hay'
  have hne : a' ≠ a := by
    rintro rfl
    rw [hay] at hay'
    cases hay'
    omega
  have := eighLoc_disjoint (ha'.trans ha.symm) hne hay' hay
  have h1 : lo' + y'.k ≤ lo := by omega
  exact ⟨h1, by nlinarith [Nat.mul_le_mul_right y'.k (show y'.k ≤ n by omega)]⟩

/-- A cell outside level $d$ of the output and eigenvalue arenas lies outside the blocks of the
node of size $k$ at slot $lo$, $lo + k \le n$. -/
private theorem not_mem_blocks_of_not_levelCell {H : EighArenas} {n d lo k b i : ℕ}
    (hk : lo + k ≤ n) (hb' : ¬ ((b = H.Ua ∨ b = H.Ea) ∧ H.LevelCell n d b i)) :
    (b ≠ H.Ua ∨ i < 2 * (n * n) * d + 2 * n * lo ∨
        2 * (n * n) * d + 2 * n * lo + 2 * (k * k) ≤ i) ∧
      (b ≠ H.Ea ∨ i < n * d + lo ∨ n * d + lo + k ≤ i) := by
  have hlt : 2 * n * lo + 2 * (k * k) ≤ 2 * (n * n) := by
    nlinarith [Nat.mul_le_mul_left n hk]
  refine ⟨?_, ?_⟩
  · by_cases hbU : b = H.Ua
    · subst hbU
      refine Or.inr (by_contra fun hc =>
        hb' ⟨Or.inl rfl, Or.inl ⟨Or.inr (Or.inl rfl), by omega, ?_⟩⟩)
      rw [Nat.mul_succ]
      omega
    · exact Or.inl hbU
  · by_cases hbE : b = H.Ea
    · subst hbE
      refine Or.inr (by_contra fun hc =>
        hb' ⟨Or.inr rfl, Or.inr (Or.inl ⟨Or.inl rfl, by omega, ?_⟩)⟩)
      rw [Nat.mul_succ]
      omega
    · exact Or.inl hbE

/-- The split node of the upward pass (`NLAlib.eighUpSplit` at the node $y$ of slot $lo$ split
at $k_+$): it writes its output (`NLAlib.eighAux` at budget $D - d$) and keeps the cells outside
its output block and eigenvalue cells, when the cells it reads read as in `s₀`. -/
private theorem holds_of_exec_eighUpNode_split {mm : ι}
    (hmm : IsMatMulKernel I mm pairLayout mmR) (p : P) (n ℓ₀ F d D : ℕ)
    (H : EighArenas) (t : ℕ) {s₀ s₁ s₂ : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)}
    {R₀ ε β : K} {a : List Bool} {lo : ℕ} {y : EighNode K} (ha : a.length = d)
    (hay : eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a =
      some (lo, y)) (hkn : lo + y.k ≤ n)
    (hyR : y.R = (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ d).1)
    (hUE : H.Ua ≠ H.Ea) (hUQ : H.Ua ≠ H.Qa) (hQE : H.Qa ≠ H.Ea) (htU : t ≠ H.Ua)
    (htE : t ≠ H.Ea) {kp : ℕ} {hkp : kp ≤ y.k} {Qp : Matrix (Fin y.k) (Fin kp) (K × K)}
    {Qm : Matrix (Fin y.k) (Fin (y.k - kp)) (K × K)} {Ap : Matrix (Fin kp) (Fin kp) (K × K)}
    {Am : Matrix (Fin (y.k - kp)) (Fin (y.k - kp)) (K × K)} {σ' : K}
    (hs : eighStep (eighTapeMachine I p mmR qrR) n F R₀ β y.A y.R y.ε y.ℓ
      (eighTapeSample n d lo) = .split kp hkp Qp Qm Ap Am σ')
    (hQp : pairLayout.Holds s₀.store p H.Qa (2 * (n * n) * d + 2 * n * lo) Qp)
    (hQm : pairLayout.Holds s₀.store p H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (y.k * kp)) Qm)
    (ht0 : s₀.store.read p t 0 = some ((eighTapeMachine I p mmR qrR).div
      (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ d).1
      ((eighTapeMachine I p mmR qrR).ofNat 2)))
    (hout : H.OutHolds s₀.store p (eighTapeMachine I p mmR qrR) n F D R₀ β ⟨n, A, R₀, ε, ℓ₀⟩
      (d + 1))
    (hRo : ∀ q b i, b ≠ H.Ua → b ≠ H.Ea → s₁.store.read q b i = s₀.store.read q b i)
    (hRU1 : ∀ q i, 2 * (n * n) * (d + 1) ≤ i → s₁.store.read q H.Ua i = s₀.store.read q H.Ua i)
    (hRE1 : ∀ q i, n * (d + 1) ≤ i → s₁.store.read q H.Ea i = s₀.store.read q H.Ea i)
    (h : exec I (eighUpSplit p mm n d lo y.k kp t H).run s₁ = some s₂) :
    s₂.store.shape = s₁.store.shape ∧ s₂.pos = s₁.pos ∧
      (pairLayout.Holds s₂.store p H.Ua (2 * (n * n) * d + 2 * n * lo)
          (eighAux (eighTapeMachine I p mmR qrR) n F R₀ β (D - (d + 1) + 1) y.A y.R y.ε y.ℓ
            (eighSlotTree (eighTapeMachine I p mmR qrR) n F R₀ β d lo y)).1 ∧
        ∀ i : Fin y.k, s₂.store.read p H.Ea (n * d + lo + i) = some
          ((eighAux (eighTapeMachine I p mmR qrR) n F R₀ β (D - (d + 1) + 1) y.A y.R y.ε y.ℓ
            (eighSlotTree (eighTapeMachine I p mmR qrR) n F R₀ β d lo y)).2 i)) ∧
      ∀ q b i, (b ≠ H.Ua ∨ i < 2 * (n * n) * d + 2 * n * lo ∨
          2 * (n * n) * d + 2 * n * lo + 2 * (y.k * y.k) ≤ i) →
        (b ≠ H.Ea ∨ i < n * d + lo ∨ n * d + lo + y.k ≤ i) →
        s₂.store.read q b i = s₁.store.read q b i := by
  set M := eighTapeMachine I p mmR qrR with hM
  obtain ⟨hσ', -, hkpk⟩ := eq_div_and_pos_and_lt_of_eighStep_eq_split hs
  have hchp : eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ (a ++ [true]) = some (lo,
      ⟨kp, Ap, (eighNextParams M y.R y.ε y.ℓ).1, (eighNextParams M y.R y.ε y.ℓ).2,
        y.ℓ + 1⟩) := by
    rw [eighLoc_append_singleton, hay]
    simp [eighLoc, ha, hs]
  have hchm : eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ (a ++ [false]) = some (lo + kp,
      ⟨y.k - kp, Am, (eighNextParams M y.R y.ε y.ℓ).1, (eighNextParams M y.R y.ε y.ℓ).2,
        y.ℓ + 1⟩) := by
    rw [eighLoc_append_singleton, hay]
    simp [eighLoc, ha, hs]
  obtain ⟨hUp, hEp⟩ := hout (a ++ [true]) lo _ (by simp [ha]) hchp
  obtain ⟨hUm, hEm⟩ := hout (a ++ [false]) (lo + kp) _ (by simp [ha]) hchm
  obtain ⟨S1, S2, S3, S4, S5, S6⟩ := holds_of_exec_eighUpSplit hmm p n d lo y.k kp t H hkn hkpk
    hUE hUQ htE htU (hQp.of_forall_read_eq fun i _ _ => hRo p _ i (Ne.symm hUQ) hQE)
    (hQm.of_forall_read_eq fun i _ _ => hRo p _ i (Ne.symm hUQ) hQE)
    (hUp.of_forall_read_eq fun i hi _ => hRU1 p i (by omega))
    (hUm.of_forall_read_eq fun i hi _ => hRU1 p i (by nlinarith))
    (fun j => (hRE1 p _ (by omega)).trans (hEp j))
    (fun j => (hRE1 p _ (by omega)).trans (hEm j)) ((hRo p _ _ htU htE).trans ht0) h
  refine ⟨S1, S2, ?_, S6⟩
  simp only [eighAux, eighSlotTree, hs, ite_true, Bool.false_eq_true, ite_false]
  rw [← hyR] at S4 S5
  refine ⟨S3, fun i => ?_⟩
  by_cases hi : (i : ℕ) < kp
  · rw [finSumFinEquiv_symm_apply_lt hkp i hi, Sum.elim_inl, hσ']
    exact S4 ⟨i, hi⟩
  · rw [finSumFinEquiv_symm_apply_ge hkp i (by omega), Sum.elim_inr, hσ']
    have := S5 ⟨i - kp, by omega⟩
    rw [show n * d + lo + kp + (i - kp) = n * d + lo + i by omega] at this
    exact this

/-- One node of the upward pass (`NLAlib.eighUpNode` at the node $y$ of slot $lo$): it writes its
output (`NLAlib.eighAux` at budget $D - d$) and keeps every cell outside the node's output block
and eigenvalue cells, when the cells it reads (outside depth $d$ of the output and eigenvalue
arenas, or inside the node's own) read as in `s₀`. -/
private theorem holds_of_exec_eighUpNode {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (p : P) (n ℓ₀ F d D : ℕ) (hn : 1 ≤ n) (hd : d < D) (H : EighArenas) (t : ℕ)
    {s₀ s₁ s₂ : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K} {a : List Bool}
    {lo : ℕ} {y : EighNode K} (ha : a.length = d)
    (hay : eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a =
      some (lo, y))
    (hnd : H.handles.Nodup) (htH : t ∉ H.handles)
    (ht0 : s₀.store.read p t 0 = some ((eighTapeMachine I p mmR qrR).div
      (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ d).1
      ((eighTapeMachine I p mmR qrR).ofNat 2)))
    (ht1 : s₀.store.read p t 1 = some ((eighTapeMachine I p mmR qrR).neg
      ((eighTapeMachine I p mmR qrR).div (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ d).1
        ((eighTapeMachine I p mmR qrR).ofNat 2))))
    (hrec : H.RecordHolds I.sem s₀.store p (eighTapeMachine I p mmR qrR) n F R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d)
    (hout : H.OutHolds s₀.store p (eighTapeMachine I p mmR qrR) n F D R₀ β ⟨n, A, R₀, ε, ℓ₀⟩
      (d + 1))
    (hR : ∀ q b i, (¬ ((b = H.Ua ∨ b = H.Ea) ∧ H.LevelCell n d b i) ∨
        ((b = H.Ua → 2 * (n * n) * d + 2 * n * lo ≤ i ∧
            i < 2 * (n * n) * d + 2 * n * lo + 2 * (y.k * y.k)) ∧
          (b = H.Ea → n * d + lo ≤ i ∧ i < n * d + lo + y.k))) →
        s₁.store.read q b i = s₀.store.read q b i)
    (h : exec I (eighUpNode p mm n d lo y.k t H).run s₁ = some s₂) :
    s₂.store.shape = s₁.store.shape ∧ s₂.pos = s₁.pos ∧
      (pairLayout.Holds s₂.store p H.Ua (2 * (n * n) * d + 2 * n * lo)
          (eighAux (eighTapeMachine I p mmR qrR) n F R₀ β (D - d) y.A y.R y.ε y.ℓ
            (eighSlotTree (eighTapeMachine I p mmR qrR) n F R₀ β d lo y)).1 ∧
        ∀ i : Fin y.k, s₂.store.read p H.Ea (n * d + lo + i) = some
          ((eighAux (eighTapeMachine I p mmR qrR) n F R₀ β (D - d) y.A y.R y.ε y.ℓ
            (eighSlotTree (eighTapeMachine I p mmR qrR) n F R₀ β d lo y)).2 i)) ∧
      ∀ q b i, (b ≠ H.Ua ∨ i < 2 * (n * n) * d + 2 * n * lo ∨
          2 * (n * n) * d + 2 * n * lo + 2 * (y.k * y.k) ≤ i) →
        (b ≠ H.Ea ∨ i < n * d + lo ∨ n * d + lo + y.k ≤ i) →
        s₂.store.read q b i = s₁.store.read q b i := by
  set M := eighTapeMachine I p mmR qrR with hM
  obtain ⟨hk1, hkn⟩ := eighLoc_bounds hn hay
  obtain ⟨hyR, -, -⟩ := eighLoc_params hay
  rw [ha] at hyR
  obtain ⟨hUE, hUQ, hKdU, hKdE, hKpU, hKpE, hQE, -⟩ := H.ua_ne_ea_and_of_nodup hnd
  have htU : t ≠ H.Ua := fun e => htH (e ▸ by simp [EighArenas.handles])
  have htE : t ≠ H.Ea := fun e => htH (e ▸ by simp [EighArenas.handles])
  have hRo : ∀ q b i, b ≠ H.Ua → b ≠ H.Ea → s₁.store.read q b i = s₀.store.read q b i :=
    fun q b i h1 h2 => hR q b i (Or.inl fun h => h.1.elim h1 h2)
  have hRU1 : ∀ q i, 2 * (n * n) * (d + 1) ≤ i → s₁.store.read q H.Ua i = s₀.store.read q H.Ua i :=
    fun q i hi => hR q _ i (Or.inl fun ⟨_, hc⟩ => by
      have := H.mul_le_and_lt_of_levelCell_ua hnd hc; omega)
  have hRE1 : ∀ q i, n * (d + 1) ≤ i → s₁.store.read q H.Ea i = s₀.store.read q H.Ea i :=
    fun q i hi => hR q _ i (Or.inl fun ⟨_, hc⟩ => by
      have := H.mul_le_and_lt_of_levelCell_ea hnd hc; omega)
  have hr := hrec a lo y ha hay hk1
  rw [show D - d = (D - (d + 1)) + 1 by omega]
  cases hs : eighStep M n F R₀ β y.A y.R y.ε y.ℓ (eighTapeSample n d lo) with
  | leaf U e =>
    rw [hs] at hr
    obtain ⟨hkd, hU, hE⟩ := hr
    rw [exec_eighUpNode_of_readsIdx_one (readsIdx_of_read_eq hkd (hRo p _ _ hKdU hKdE))] at h
    cases h
    refine ⟨rfl, rfl, ?_, fun _ _ _ _ _ => rfl⟩
    simp only [eighAux, eighSlotTree, hs]
    refine ⟨hU.of_forall_read_eq fun i hi hi' => hR p _ i (Or.inr ⟨fun _ => ⟨hi, ?_⟩,
      fun h => absurd h hUE⟩), fun i => (hR p _ _ (Or.inr ⟨fun h => absurd h.symm hUE,
      fun _ => ⟨by omega, by omega⟩⟩)).trans (hE i)⟩
    simpa [pairLayout, Nat.mul_comm] using hi'
  | shift b A' σ' =>
    rw [hs] at hr
    rw [exec_eighUpNode_of_readsIdx_shift (readsIdx_of_read_eq hr (hRo p _ _ hKdU hKdE))] at h
    have hch : eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ (a ++ [b]) = some (lo,
        ⟨y.k, A', (eighNextParams M y.R y.ε y.ℓ).1, (eighNextParams M y.R y.ε y.ℓ).2,
          y.ℓ + 1⟩) := by
      rw [eighLoc_append_singleton, hay]
      simp [eighLoc, ha, hs]
    obtain ⟨hUc, hEc⟩ := hout (a ++ [b]) lo _ (by simp [ha]) hch
    obtain ⟨S1, S2, S3, S4, S5⟩ := holds_of_exec_eighUpShift p n d lo y.k H ⟨t, if b then 0 else 1⟩
      (s := { s₁ with cnt := s₁.cnt + I.charge (.toNat p) }) hkn hUE htE htU
      (hUc.of_forall_read_eq fun i hi _ => hRU1 p i (by omega))
      (fun i => (hRE1 p _ (by omega)).trans (hEc i))
      (σ := if b then M.div (eighLevelParams M R₀ ε ℓ₀ d).1 (M.ofNat 2)
        else M.neg (M.div (eighLevelParams M R₀ ε ℓ₀ d).1 (M.ofNat 2)))
      (by cases b
          · exact (hRo p _ _ htU htE).trans ht1
          · exact (hRo p _ _ htU htE).trans ht0) h
    refine ⟨S1, S2, ?_, S5⟩
    simp only [eighAux, eighSlotTree, hs]
    refine ⟨S3, fun i => (S4 i).trans ?_⟩
    rw [eq_of_eighStep_eq_shift hs, hyR]
    cases b <;> rfl
  | split kp hkp Qp Qm Ap Am σ' =>
    rw [hs] at hr
    obtain ⟨hkd, hkpr, hQp, hQm⟩ := hr
    rw [exec_eighUpNode_of_readsIdx_four (readsIdx_of_read_eq hkd (hRo p _ _ hKdU hKdE))
      (readsIdx_of_read_eq hkpr (hRo p _ _ hKpU hKpE)) hkp] at h
    exact holds_of_exec_eighUpNode_split hmm p n ℓ₀ F d D H t
      (s₁ := { s₁ with cnt := s₁.cnt + I.charge (.toNat p) + I.charge (.toNat p) }) ha hay hkn hyR
      hUE hUQ hQE htU htE hs hQp hQm ht0 hout hRo hRU1 hRE1 h

/-- **The slots below $lo$ of depth $d$ are done** in the state `s` of the upward pass, run from
the state `s₀` (machine `M`, root `root` of size $n$, depth budget $D$): the store shape and the
tape positions are those of `s₀`; every cell outside depth $d$ of the output and eigenvalue arenas,
or outside the blocks of the nodes at the slots below $lo$, reads as in `s₀`; and every such node
has its output (`NLAlib.eighAux` at budget $D - d$) stored. -/
abbrev EighArenas.UpSlotsDone (H : EighArenas) (s s₀ : St P K C) (p : P) (M : FloatMachine K ℕ ℕ)
    (n F D : ℕ) (R₀ β : K) (root : EighNode K) (d lo : ℕ) : Prop :=
  s.store.shape = s₀.store.shape ∧ s.pos = s₀.pos ∧
    (∀ q b i, (¬ ((b = H.Ua ∨ b = H.Ea) ∧ H.LevelCell n d b i) ∨
      ∀ (a : List Bool) (lo' : ℕ) (y : EighNode K), a.length = d →
        eighLoc M n F R₀ β 0 0 root a = some (lo', y) → lo' < lo →
        (b ≠ H.Ua ∨ i < 2 * (n * n) * d + 2 * n * lo' ∨
          2 * (n * n) * d + 2 * n * lo' + 2 * (y.k * y.k) ≤ i) ∧
        (b ≠ H.Ea ∨ i < n * d + lo' ∨ n * d + lo' + y.k ≤ i)) →
      s.store.read q b i = s₀.store.read q b i) ∧
    ∀ (a : List Bool) (lo' : ℕ) (y : EighNode K), a.length = d →
      eighLoc M n F R₀ β 0 0 root a = some (lo', y) → lo' < lo →
      pairLayout.Holds s.store p H.Ua (2 * (n * n) * d + 2 * n * lo')
          (eighAux M n F R₀ β (D - d) y.A y.R y.ε y.ℓ (eighSlotTree M n F R₀ β d lo' y)).1 ∧
        ∀ i : Fin y.k, s.store.read p H.Ea (n * d + lo' + i) = some
          ((eighAux M n F R₀ β (D - d) y.A y.R y.ε y.ℓ (eighSlotTree M n F R₀ β d lo' y)).2 i)

/-- One slot of the upward pass (`NLAlib.eighUpSlot` at slot $lo < n$ of depth $d < D$): the node
at the slot (if any) gets its output; the shape, the tape positions, every cell outside the blocks
of the nodes at the slots up to $lo$, and the outputs of the slots below are kept, when the arenas
in `s₀` hold the nodes and records of depth $d$ and the outputs of depth $d + 1$, the shift cells
of `t` hold $\pm\mathrm{fl}(R/2)$, and `s₁` reads as `s₀` outside the blocks of the slots below
$lo$, which hold their outputs. -/
theorem holds_of_exec_eighUpSlot {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) (p : P)
    (n ℓ₀ F d D : ℕ) (hd : d < D) (H : EighArenas) (t : ℕ) {s₀ s₁ s₂ : St P K C}
    {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K} {lo : ℕ} (hlo : lo < n)
    (hnd : H.handles.Nodup) (htH : t ∉ H.handles)
    (ht0 : s₀.store.read p t 0 = some ((eighTapeMachine I p mmR qrR).div
      (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ d).1
      ((eighTapeMachine I p mmR qrR).ofNat 2)))
    (ht1 : s₀.store.read p t 1 = some ((eighTapeMachine I p mmR qrR).neg
      ((eighTapeMachine I p mmR qrR).div (eighLevelParams (eighTapeMachine I p mmR qrR) R₀ ε ℓ₀ d).1
        ((eighTapeMachine I p mmR qrR).ofNat 2))))
    (hlev : H.LevelHolds I.sem s₀.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d)
    (hrec : H.RecordHolds I.sem s₀.store p (eighTapeMachine I p mmR qrR) n F R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d)
    (hout : H.OutHolds s₀.store p (eighTapeMachine I p mmR qrR) n F D R₀ β ⟨n, A, R₀, ε, ℓ₀⟩
      (d + 1))
    (hdone : H.UpSlotsDone s₁ s₀ p (eighTapeMachine I p mmR qrR) n F D R₀ β ⟨n, A, R₀, ε, ℓ₀⟩
      d lo)
    (h : exec I (eighUpSlot p mm n d lo t H).run s₁ = some s₂) :
    H.UpSlotsDone s₂ s₀ p (eighTapeMachine I p mmR qrR) n F D R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ d
      (lo + 1) := by
  obtain ⟨hsh, hps, hfr, hdone⟩ := hdone
  obtain ⟨hUE, -, -, -, -, -, -, hSzU, hSzE, -⟩ := H.ua_ne_ea_and_of_nodup hnd
  have hSz : ∀ i, s₁.store.read p H.Sz i = s₀.store.read p H.Sz i := fun i =>
    hfr p _ i (Or.inl fun h => h.1.elim hSzU hSzE)
  by_cases hy : ∃ (a : List Bool) (y : EighNode K), a.length = d ∧
      eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo, y)
  swap
  · push Not at hy
    rw [exec_eighUpSlot_of_readsIdx_zero (readsIdx_of_read_eq
      (hlev.2.1 lo hlo fun a y ha => hy a y ha) (hSz _))] at h
    cases h
    refine ⟨hsh, hps, fun q b i hb => hfr q b i (hb.imp_right fun H' a lo' y ha hay hlt =>
      H' a lo' y ha hay (by omega)), fun a lo' y ha hay hlt =>
      hdone a lo' y ha hay (lt_of_le_of_ne (Nat.lt_succ_iff.mp hlt) ?_)⟩
    rintro rfl
    exact hy a y ha hay
  obtain ⟨a, y, ha, hay⟩ := hy
  obtain ⟨hk1, hb⟩ := eighLoc_bounds (by omega : 1 ≤ n) hay
  rw [exec_eighUpSlot_of_readsIdx (readsIdx_of_read_eq (hlev.1 a lo y ha hay).1 (hSz _)) hk1
    (by omega)] at h
  have hbefore := fun {a' : List Bool} {lo' : ℕ} {y' : EighNode K} (ha' : a'.length = d)
    (hay' : eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a' =
      some (lo', y')) (hlt : lo' < lo) =>
    add_le_and_mul_add_le_of_eighLoc_of_lt (by omega) ha ha' hay hay' hlt
  obtain ⟨N1, N2, N3, N4⟩ := holds_of_exec_eighUpNode hmm p n ℓ₀ F d D (by omega) hd H t ha hay
    hnd htH ht0 ht1 hrec hout (fun q b i hb' => by
      refine hfr q b i (hb'.imp_right fun ⟨hU', hE'⟩ a' lo' y' ha' hay' hlt => ?_)
      obtain ⟨h1, h2⟩ := hbefore ha' hay' hlt
      refine ⟨?_, ?_⟩
      · by_cases hbU : b = H.Ua
        · exact Or.inr (Or.inr (by have := hU' hbU; omega))
        · exact Or.inl hbU
      · by_cases hbE : b = H.Ea
        · exact Or.inr (Or.inr (by have := hE' hbE; omega))
        · exact Or.inl hbE) h
  refine ⟨N1.trans hsh, N2.trans hps, fun q b i hb' => ?_, fun a' lo' y' ha' hay' hlt => ?_⟩
  · have hW := hb'.elim (not_mem_blocks_of_not_levelCell hb) fun hb' =>
      hb' a lo y ha hay (Nat.lt_succ_self lo)
    rw [N4 q b i hW.1 hW.2]
    exact hfr q b i (hb'.imp_right fun H' a lo' y ha hay hlt => H' a lo' y ha hay (by omega))
  · by_cases hll : lo' = lo
    · subst hll
      have haa : a' = a := by
        by_contra hne
        have := eighLoc_disjoint (ha'.trans ha.symm) hne hay' hay
        have := (eighLoc_bounds (by omega : 1 ≤ n) hay').1
        omega
      subst haa
      rw [hay] at hay'
      cases hay'
      exact N3
    · have hlt' : lo' < lo := by omega
      obtain ⟨hU', hE'⟩ := hdone a' lo' y' ha' hay' hlt'
      obtain ⟨h1, h2⟩ := hbefore ha' hay' hlt'
      refine ⟨hU'.of_forall_read_eq fun i hi hi' => N4 p _ i (Or.inr (Or.inl ?_))
        (Or.inl hUE), fun i => (N4 p _ _ (Or.inl (Ne.symm hUE))
          (Or.inr (Or.inl (by omega)))).trans (hE' i)⟩
      simp only [pairLayout] at hi'
      have : y'.k * y'.k * 2 = 2 * (y'.k * y'.k) := by ring
      omega

end NLAlib
