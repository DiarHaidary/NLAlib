/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.KernelCall
public import NLAlib.Matrix.Computation.SpectralBisectionProgramTree
public import NLAlib.Computation.BLASCongr
public import NLAlib.Matrix.Computation.PairKernels
public import NLAlib.Matrix.Computation.SpectralBisectionProgram.Levels

/-!
# The upward level of the spectral bisection program

One level of the upward pass of `NLAlib.eighProg` (`NLAlib.eighUpLevel`) takes the outputs of depth
$d + 1$ to those of depth $d$ (`NLAlib.EighArenas.OutHolds`): a node with one child adds back its
shift, a split multiplies the children's bases by the deflation bases, as the machine of the
interpretation computes them.

## Main results

* `NLAlib.holds_of_exec_eighUpLevel`: what a successful level computes.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}

/-- A one-child step adds back the shift $\pm\mathrm{fl}(R/2)$. -/
private theorem el5_eighStep_shift {F Su Sg : Type*} [Inhabited Sg] {M : FloatMachine F Su Sg}
    {N fuel k ℓ : ℕ} {R₀ β R ε : F} {A : Matrix (Fin k) (Fin k) (F × F)} {s : EighSample Su Sg N}
    {b : Bool} {A' : Matrix (Fin k) (Fin k) (F × F)} {σ : F}
    (h : eighStep M N fuel R₀ β A R ε ℓ s = .shift b A' σ) :
    σ = if b then M.div R (M.ofNat 2) else M.neg (M.div R (M.ofNat 2)) := by
  unfold eighStep at h
  dsimp only at h
  split_ifs at h <;> cases h <;> rfl

/-- A split adds back the shift $\mathrm{fl}(R/2)$ and has $0 < k_+ < k$. -/
theorem el5_eighStep_split {F Su Sg : Type*} [Inhabited Sg] {M : FloatMachine F Su Sg}
    {N fuel k ℓ : ℕ} {R₀ β R ε : F} {A : Matrix (Fin k) (Fin k) (F × F)} {s : EighSample Su Sg N}
    {kp : ℕ} {hkp : kp ≤ k} {Qp : Matrix (Fin k) (Fin kp) (F × F)}
    {Qm : Matrix (Fin k) (Fin (k - kp)) (F × F)} {Ap : Matrix (Fin kp) (Fin kp) (F × F)}
    {Am : Matrix (Fin (k - kp)) (Fin (k - kp)) (F × F)} {σ : F}
    (h : eighStep M N fuel R₀ β A R ε ℓ s = .split kp hkp Qp Qm Ap Am σ) :
    σ = M.div R (M.ofNat 2) ∧ 0 < kp ∧ kp < k := by
  unfold eighStep at h
  dsimp only at h
  split_ifs at h with h1 h2 h3 h4
  cases h
  exact ⟨rfl, Nat.pos_of_ne_zero h4, lt_of_le_of_ne (min_le_left _ _) h3⟩

/-- A successful loop of binary operations `Y[f w] ← Y[g w] ∘ c` whose written cells are distinct
and never read: the written cells hold the results, every other cell is kept. -/
theorem el5_binLoop {p : P} {op : BinOp} {m : IExp ℕ} {Y : ℕ} {c : Cell ℕ ℕ}
    {f g : ℕ → IExp ℕ} {st st' : St P K C} (hYc : c.buf ≠ Y)
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

omit [AddMonoid C] [Inhabited K] in
/-- Two column blocks stored one after the other hold the matrix of their columns. -/
private theorem el5_holds_fromCols {s : Store P K} {p : P} {b off k kp : ℕ} (h : kp ≤ k)
    {X : Matrix (Fin k) (Fin kp) (K × K)} {Y : Matrix (Fin k) (Fin (k - kp)) (K × K)}
    (hX : pairLayout.Holds s p b off X) (hY : pairLayout.Holds s p b (off + 2 * (k * kp)) Y) :
    pairLayout.Holds s p b off ((Matrix.fromCols X Y).submatrix id
      ((finCongr (Nat.add_sub_of_le h).symm).trans finSumFinEquiv.symm)) := by
  intro i j t
  by_cases hj : (j : ℕ) < kp
  · have e : ((finCongr (Nat.add_sub_of_le h).symm).trans finSumFinEquiv.symm) j =
        Sum.inl ⟨j, hj⟩ := by
      simp only [Equiv.trans_apply]
      rw [Equiv.symm_apply_eq]
      ext; simp
    simp only [Matrix.submatrix_apply, id, e, Matrix.fromCols_apply_inl]
    exact hX i ⟨j, hj⟩ t
  · have e : ((finCongr (Nat.add_sub_of_le h).symm).trans finSumFinEquiv.symm) j =
        Sum.inr ⟨j - kp, by omega⟩ := by
      simp only [Equiv.trans_apply]
      rw [Equiv.symm_apply_eq]
      ext; simp; omega
    simp only [Matrix.submatrix_apply, id, e, Matrix.fromCols_apply_inr]
    have := hY i ⟨j - kp, by omega⟩ t
    rw [← this]
    congr 1
    simp only [pairLayout]
    have : (j : ℕ) = kp + (j - kp) := by omega
    conv_lhs => rw [this]
    ring

omit [AddMonoid C] [Inhabited K] in
theorem el5_bd {b i B off len : ℕ} (h : b ≠ B ∨ i < off ∨ off + len ≤ i) :
    blockDisjoint (b, i, 1) (B, off, len) = true := by
  simp only [blockDisjoint, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq]
  omega

omit [AddMonoid C] [Inhabited K] in
theorem el5_bd2 {b b' off off' len len' : ℕ}
    (h : off + len ≤ off' ∨ off' + len' ≤ off) :
    blockDisjoint (b, off, len) (b', off', len') = true := by
  simp only [blockDisjoint, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq]
  omega

omit [AddMonoid C] [Inhabited K] in
theorem el5_bd2' {b b' off off' len len' : ℕ} (h : b ≠ b' ∨ off + len ≤ off') :
    blockDisjoint (b, off, len) (b', off', len') = true := by
  simp only [blockDisjoint, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq]
  omega

/-- The branch of a one-child node in the upward pass: the child's output copied, the shift
added to its eigenvalues. -/
private theorem el5_shift_run (p : P) (n d lo k : ℕ) (H : EighArenas) (tc : Cell ℕ ℕ)
    {s s' : St P K C} (hk : lo + k ≤ n) (hUE : H.Ua ≠ H.Ea) (htc : tc.buf ≠ H.Ea)
    (htcU : tc.buf ≠ H.Ua)
    {U : Matrix (Fin k) (Fin k) (K × K)} {e : Fin k → K} {σ : K}
    (hU : pairLayout.Holds s.store p H.Ua (2 * (n * n) * (d + 1) + 2 * n * lo) U)
    (hE : ∀ i : Fin k, s.store.read p H.Ea (n * (d + 1) + lo + i) = some (e i))
    (hσ : s.store.read p tc.buf tc.idx.eval = some σ)
    (h : exec I (do
        zcopy (ι := ι) p (IExp.var k) (IExp.var k) H.Ua
          (eighBlockOff (IExp.const n) (IExp.const d + 1) (IExp.var lo))
          H.Ua (eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo))
        forRange (IExp.var k) fun i => ins (.bin p .add
          ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo) + IExp.var i⟩
          ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d + 1) (IExp.var lo) + IExp.var i⟩
          tc)).run s = some s') :
    s'.store.shape = s.store.shape ∧ s'.pos = s.pos ∧
      pairLayout.Holds s'.store p H.Ua (2 * (n * n) * d + 2 * n * lo) U ∧
      (∀ i : Fin k, s'.store.read p H.Ea (n * d + lo + i) =
        some ((I.sem.bin p .add (e i) σ).getD default)) ∧
      ∀ q b i, (b ≠ H.Ua ∨ i < 2 * (n * n) * d + 2 * n * lo ∨
          2 * (n * n) * d + 2 * n * lo + 2 * (k * k) ≤ i) →
        (b ≠ H.Ea ∨ i < n * d + lo ∨ n * d + lo + k ≤ i) →
        s'.store.read q b i = s.store.read q b i := by
  rw [exec_run_bind I (b := zcopy (ι := ι) p (IExp.var k) (IExp.var k) H.Ua
    (eighBlockOff (IExp.const n) (IExp.const d + 1) (IExp.var lo)) H.Ua
    (eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo))) (fun _ => rfl)] at h
  obtain ⟨s₁, hz, h⟩ := Option.bind_eq_some_iff.mp h
  rw [exec_zcopy_congr] at hz
  have hkn : k ≤ n := by omega
  have hkk : k * k ≤ n * n := Nat.mul_le_mul hkn hkn
  obtain ⟨hU₁, hfr₁, hsh₁, hps₁⟩ := holds_of_exec_zcopy p k k
    (xo := eighBlockOff (IExp.const n) (IExp.const d + 1) (IExp.var lo))
    (yo := eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo)) (A := U)
    (by simpa [eighBlockOff, Nat.mul_succ] using hU)
    (el5_bd2 (Or.inl (by
      simp only [eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const,
        IExp.eval_var, IExp.eval_ofNat]
      rw [Nat.mul_succ]; omega))) hz
  simp only [eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var,
    IExp.eval_ofNat] at hU₁ hfr₁
  change exec I (.seq (.loop _ _) .skip) _ = _ at h
  rw [exec_seq_skip] at h
  obtain ⟨hsh₂, hps₂, hE₂, hfr₂⟩ := el5_binLoop htc (by
    intro w hw w' hw'
    simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var,
      IExp.eval_ofNat] at hw hw' ⊢
    rw [Nat.mul_succ]; omega) (by
    intro w hw w' hw' e
    simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var] at e
    omega) h
  simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var,
    IExp.eval_ofNat] at hE₂ hfr₂
  have hfr : ∀ q b i, (b ≠ H.Ua ∨ i < 2 * (n * n) * d + 2 * n * lo ∨
      2 * (n * n) * d + 2 * n * lo + 2 * (k * k) ≤ i) →
      (b ≠ H.Ea ∨ i < n * d + lo ∨ n * d + lo + k ≤ i) →
      s'.store.read q b i = s.store.read q b i := by
    intro q b i hU' hE'
    rw [hfr₂ q b i (hE'.imp_right fun h w hw => by omega), hfr₁ q b i (el5_bd hU')]
  refine ⟨hsh₂.trans hsh₁, hps₂.trans hps₁,
    hU₁.of_forall_read_eq fun i _ _ => hfr₂ p _ i (Or.inl hUE), fun i => ?_, hfr⟩
  have hx : s₁.store.read p H.Ea (n * (d + 1) + lo + i) = some (e i) := by
    rw [hfr₁ p _ _ (el5_bd (Or.inl (Ne.symm hUE)))]; exact hE i
  have hz : s₁.store.read p tc.buf tc.idx.eval = some σ := by
    rw [hfr₁ p _ _ (el5_bd (Or.inl htcU))]; exact hσ
  have := hE₂ i i.isLt (e i) σ (by rw [Nat.mul_succ] at hx ⊢; simpa [Nat.mul_succ] using hx) hz
  exact this

/-- The branch of a split in the upward pass: the two products into the column blocks of the
node's output, the shifted eigenvalues of the two children. -/
private theorem el5_split_run {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) (p : P)
    (n d lo k kp t : ℕ) (H : EighArenas) {s s' : St P K C} (hk : lo + k ≤ n) (hkp : kp < k)
    (hUE : H.Ua ≠ H.Ea) (hUQ : H.Ua ≠ H.Qa) (htE : t ≠ H.Ea) (htU : t ≠ H.Ua)
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
    (h : exec I (do
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
            IExp.var j⟩ ⟨t, 0⟩)).run s = some s') :
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
  have hkn : k ≤ n := by omega
  have hkk : k * k ≤ n * n := Nat.mul_le_mul hkn hkn
  have hkpk : k * kp ≤ k * k := Nat.mul_le_mul_left k hkp.le
  have hsplit : k * kp + k * (k - kp) = k * k := by
    rw [← Nat.mul_add, Nat.add_sub_of_le hkp.le]
  have hlok : lo * n + k * n ≤ n * n := by nlinarith
  obtain ⟨hP, hfr₁⟩ := hmm.holds_of_kcallStore_eq_some pairLayout.get_put p (l := k) (m := kp)
    (n := kp) (a := (H.Qa, 2 * (n * n) * d + 2 * n * lo))
    (b := (H.Ua, 2 * (n * n) * (d + 1) + 2 * n * lo))
    (c := (H.Ua, 2 * (n * n) * d + 2 * n * lo)) hQp hUp
    (el5_bd2' (Or.inl hUQ))
    (el5_bd2 (Or.inl (by simp only [pairLayout]; rw [Nat.mul_succ]; nlinarith)))
    hu₁
  have hQm₁ := hQm.of_forall_read_eq fun i _ _ => hfr₁ p _ i (el5_bd (Or.inl (Ne.symm hUQ)))
  have hUm₁ := hUm.of_forall_read_eq fun i hi _ => hfr₁ p _ i (el5_bd (Or.inr (Or.inr (by
    simp only [pairLayout]; rw [Nat.mul_succ]; nlinarith))))
  obtain ⟨hM, hfr₂⟩ := hmm.holds_of_kcallStore_eq_some pairLayout.get_put p (l := k)
    (m := k - kp) (n := k - kp) (a := (H.Qa, 2 * (n * n) * d + 2 * n * lo + 2 * (k * kp)))
    (b := (H.Ua, 2 * (n * n) * (d + 1) + 2 * n * (lo + kp)))
    (c := (H.Ua, 2 * (n * n) * d + 2 * n * lo + 2 * (k * kp))) hQm₁ hUm₁
    (el5_bd2' (Or.inl hUQ)) (el5_bd2 (Or.inl (by
      simp only [pairLayout]; rw [Nat.mul_succ]; nlinarith))) (by convert hu₂ using 3)
  have hP₂ := hP.of_forall_read_eq fun i _ hi => hfr₂ p _ i (el5_bd (Or.inr (Or.inl (by
    simp only [pairLayout] at hi; nlinarith))))
  -- the eigenvalue loops
  obtain ⟨hsh₃, hps₃, hE₃, hfr₃⟩ := el5_binLoop (c := ⟨t, 0⟩) htE (by
    intro w hw w' hw'
    simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var,
      IExp.eval_ofNat] at hw hw' ⊢
    rw [Nat.mul_succ]; omega) (by
    intro w hw w' hw' e
    simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var] at e
    omega) h₃
  obtain ⟨hsh₄, hps₄, hE₄, hfr₄⟩ := el5_binLoop (c := ⟨t, 0⟩) htE (by
    intro w hw w' hw'
    simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var,
      IExp.eval_ofNat, IExp.eval_sub] at hw hw' ⊢
    rw [Nat.mul_succ]; omega) (by
    intro w hw w' hw' e
    simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var] at e
    omega) h
  simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var,
    IExp.eval_ofNat, IExp.eval_sub] at hE₃ hfr₃ hE₄ hfr₄
  have hsh₁ := Interp.shape_of_kcallStore_eq_some hu₁
  have hsh₂ := Interp.shape_of_kcallStore_eq_some hu₂
  have hc1 : (k - kp) * k = k * (k - kp) := Nat.mul_comm _ _
  have hc2 : kp * k = k * kp := Nat.mul_comm _ _
  have hfr : ∀ q b i, (b ≠ H.Ua ∨ i < 2 * (n * n) * d + 2 * n * lo ∨
      2 * (n * n) * d + 2 * n * lo + 2 * (k * k) ≤ i) →
      (b ≠ H.Ea ∨ i < n * d + lo ∨ n * d + lo + k ≤ i) →
      s'.store.read q b i = s.store.read q b i := by
    intro q b i hU' hE'
    rw [hfr₄ q b i (hE'.imp_right fun h w hw => by omega),
      hfr₃ q b i (hE'.imp_right fun h w hw => by omega),
      hfr₂ q b i (el5_bd (hU'.imp_right fun h => by simp only [pairLayout]; omega)),
      hfr₁ q b i (el5_bd (hU'.imp_right fun h => by simp only [pairLayout]; omega))]
  have hrdE : ∀ i, u₂.read p H.Ea i = s.store.read p H.Ea i := fun i => by
    rw [hfr₂ p _ i (el5_bd (Or.inl (Ne.symm hUE))), hfr₁ p _ i (el5_bd (Or.inl (Ne.symm hUE)))]
  have hrdt : u₂.read p t 0 = some σ := by
    rw [hfr₂ p _ _ (el5_bd (Or.inl htU)), hfr₁ p _ _ (el5_bd (Or.inl htU))]; exact hσ
  refine ⟨hsh₄.trans (hsh₃.trans (hsh₂.trans hsh₁)), hps₄.trans hps₃, ?_, fun j => ?_,
    fun j => ?_, hfr⟩
  · refine (el5_holds_fromCols hkp.le hP₂ hM).of_forall_read_eq fun i _ _ => ?_
    rw [hfr₄ p _ i (Or.inl hUE), hfr₃ p _ i (Or.inl hUE)]
  · rw [hfr₄ p _ _ (Or.inr fun w hw => by omega)]
    exact hE₃ j j.isLt (ep j) σ (by rw [hrdE, Nat.mul_succ]; simpa [Nat.mul_succ] using hEp j) hrdt
  · have := hE₄ j j.isLt (em j) σ (by
      rw [hfr₃ p _ _ (Or.inr fun w hw => by rw [Nat.mul_succ]; omega), hrdE,
        show n * (d + 1) + lo + kp + j = n * (d + 1) + (lo + kp) + j by omega]
      exact hEm j) (by rw [hfr₃ p _ _ (Or.inl htE)]; exact hrdt)
    exact this

omit [Inhabited K] in
theorem el5_seq_loop_zero {e : IExp ℕ} {b : ℕ → Stmt P ι ℕ ℕ} {t : Stmt P ι ℕ ℕ}
    {s : St P K C} (he : e.eval = 0) : exec I (.seq (.loop e b) t) s = exec I t s := by
  rw [exec_seq, exec_loop, he]
  simp

omit [Inhabited K] in
theorem el5_seq_loop_one {e : IExp ℕ} {b : ℕ → Stmt P ι ℕ ℕ} {t : Stmt P ι ℕ ℕ}
    {s : St P K C} (he : e.eval = 1) :
    exec I (.seq (.loop e b) t) s = (exec I (b 0) s).bind (exec I t) := by
  rw [exec_seq, exec_loop, he]
  simp [List.range_one]

omit [Inhabited K] in
/-- The column map of an assembled split: a column below $k_+$ is on the positive side. -/
private theorem el5_e_inl {k kp : ℕ} (h : kp ≤ k) (j : Fin k) (hj : (j : ℕ) < kp) :
    ((finCongr (Nat.add_sub_of_le h).symm).trans finSumFinEquiv.symm) j = Sum.inl ⟨j, hj⟩ := by
  simp only [Equiv.trans_apply]
  rw [Equiv.symm_apply_eq]
  ext; simp

omit [Inhabited K] in
/-- The column map of an assembled split: a column from $k_+$ is on the negative side. -/
private theorem el5_e_inr {k kp : ℕ} (h : kp ≤ k) (j : Fin k) (hj : kp ≤ (j : ℕ)) :
    ((finCongr (Nat.add_sub_of_le h).symm).trans finSumFinEquiv.symm) j =
      Sum.inr ⟨j - kp, by omega⟩ := by
  simp only [Equiv.trans_apply]
  rw [Equiv.symm_apply_eq]
  ext; simp; omega

omit [AddMonoid C] [Inhabited K] in
/-- The distinct handles of the arenas that the upward pass touches. -/
theorem el5_hne {H : EighArenas} (hnd : H.handles.Nodup) :
    H.Ua ≠ H.Ea ∧ H.Ua ≠ H.Qa ∧ H.Kd ≠ H.Ua ∧ H.Kd ≠ H.Ea ∧ H.Kp ≠ H.Ua ∧ H.Kp ≠ H.Ea ∧
      H.Qa ≠ H.Ea ∧ H.Sz ≠ H.Ua ∧ H.Sz ≠ H.Ea ∧ H.Ma ≠ H.Ua ∧ H.Ma ≠ H.Ea ∧ H.Lv ≠ H.Ua ∧
      H.Lv ≠ H.Ea := by
  simp only [EighArenas.handles, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or] at hnd
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro e <;> simp_all

omit [AddMonoid C] [Inhabited K] in
theorem el5_lc_Ua {H : EighArenas} {n d i : ℕ} (hnd : H.handles.Nodup)
    (h : H.LevelCell n d H.Ua i) : 2 * (n * n) * d ≤ i ∧ i < 2 * (n * n) * (d + 1) := by
  obtain ⟨h1, -, h3, -, h5, -, -, h8, -, -, -, h12, -⟩ := el5_hne hnd
  rcases h with ⟨-, h⟩ | ⟨hb, -⟩ | ⟨hb, -⟩
  · exact h
  · rcases hb with hb | hb | hb | hb
    exacts [absurd hb h1, absurd hb.symm h8, absurd hb.symm h3, absurd hb.symm h5]
  · exact absurd hb.symm h12

omit [AddMonoid C] [Inhabited K] in
theorem el5_lc_Ea {H : EighArenas} {n d i : ℕ} (hnd : H.handles.Nodup)
    (h : H.LevelCell n d H.Ea i) : n * d ≤ i ∧ i < n * (d + 1) := by
  obtain ⟨h1, -, -, -, -, -, h7, -, -, -, h11, -, h13⟩ := el5_hne hnd
  rcases h with ⟨hb, -⟩ | ⟨-, h⟩ | ⟨hb, -⟩
  · rcases hb with hb | hb | hb
    exacts [absurd hb.symm h11, absurd hb.symm h1, absurd hb.symm h7]
  · exact h
  · exact absurd hb.symm h13

/-- One node of the upward pass: the run of the kind binder at the node $y$ of slot $lo$
writes its output (`NLAlib.eighAux` at budget $D - d$) and keeps every cell outside the node's
output block and eigenvalue cells, when the cells it reads (outside depth $d$ of the output and
eigenvalue arenas, or inside the node's own) read as in `s₀`. -/
private theorem el5_node {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) (p : P)
    (n ℓ₀ F d D : ℕ) (hn : 1 ≤ n) (hd : d < D) (H : EighArenas) (t : ℕ) {s₀ s₁ s₂ : St P K C}
    {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K} {a : List Bool} {lo : ℕ}
    {y : EighNode K} (ha : a.length = d)
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
    (h : exec I (Builder.bindIdx (ι := ι) p
      ⟨H.Kd, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo)⟩ 4 fun c => do
        eighWhen (eighEqInd (IExp.var c) 2) do
          zcopy p (IExp.var y.k) (IExp.var y.k) H.Ua
            (eighBlockOff (IExp.const n) (IExp.const d + 1) (IExp.var lo)) H.Ua
            (eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo))
          forRange (IExp.var y.k) fun i => ins (.bin p .add
            ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo) + IExp.var i⟩
            ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d + 1) (IExp.var lo) + IExp.var i⟩
            ⟨t, 0⟩)
        eighWhen (eighEqInd (IExp.var c) 3) do
          zcopy p (IExp.var y.k) (IExp.var y.k) H.Ua
            (eighBlockOff (IExp.const n) (IExp.const d + 1) (IExp.var lo)) H.Ua
            (eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo))
          forRange (IExp.var y.k) fun i => ins (.bin p .add
            ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo) + IExp.var i⟩
            ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d + 1) (IExp.var lo) + IExp.var i⟩
            ⟨t, 1⟩)
        eighWhen (eighEqInd (IExp.var c) 4) <|
          Builder.bindIdx p ⟨H.Kp, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo)⟩
            (IExp.var y.k) fun kp => do
            let qo := eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo)
            stmt (.kcall mm p [IExp.var y.k, IExp.var kp, IExp.var kp]
              [(H.Qa, qo), (H.Ua, eighBlockOff (IExp.const n) (IExp.const d + 1) (IExp.var lo))]
              [(H.Ua, eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo))])
            stmt (.kcall mm p [IExp.var y.k, IExp.var y.k - IExp.var kp,
                IExp.var y.k - IExp.var kp]
              [(H.Qa, qo + 2 * (IExp.var y.k * IExp.var kp)),
                (H.Ua, eighBlockOff (IExp.const n) (IExp.const d + 1)
                  (IExp.var lo + IExp.var kp))]
              [(H.Ua, eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo) +
                2 * (IExp.var y.k * IExp.var kp))])
            forRange (IExp.var kp) fun j => ins (.bin p .add
              ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo) + IExp.var j⟩
              ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d + 1) (IExp.var lo) + IExp.var j⟩
              ⟨t, 0⟩)
            forRange (IExp.var y.k - IExp.var kp) fun j => ins (.bin p .sub
              ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo) + IExp.var kp +
                IExp.var j⟩
              ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d + 1) (IExp.var lo) + IExp.var kp +
                IExp.var j⟩ ⟨t, 0⟩)).run s₁ = some s₂) :
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
  obtain ⟨hUE, hUQ, hKdU, hKdE, hKpU, hKpE, hQE, -⟩ := el5_hne hnd
  have htU : t ≠ H.Ua := fun e => htH (e ▸ by simp [EighArenas.handles])
  have htE : t ≠ H.Ea := fun e => htH (e ▸ by simp [EighArenas.handles])
  have hRo : ∀ q b i, b ≠ H.Ua → b ≠ H.Ea → s₁.store.read q b i = s₀.store.read q b i :=
    fun q b i h1 h2 => hR q b i (Or.inl fun h => h.1.elim h1 h2)
  have hRU1 : ∀ q i, 2 * (n * n) * (d + 1) ≤ i → s₁.store.read q H.Ua i = s₀.store.read q H.Ua i :=
    fun q i hi => hR q _ i (Or.inl fun ⟨_, hc⟩ => by have := el5_lc_Ua hnd hc; omega)
  have hRE1 : ∀ q i, n * (d + 1) ≤ i → s₁.store.read q H.Ea i = s₀.store.read q H.Ea i :=
    fun q i hi => hR q _ i (Or.inl fun ⟨_, hc⟩ => by have := el5_lc_Ea hnd hc; omega)
  have hRW : ∀ q b i, (b = H.Ua → 2 * (n * n) * d + 2 * n * lo ≤ i ∧
      i < 2 * (n * n) * d + 2 * n * lo + 2 * (y.k * y.k)) →
      (b = H.Ea → n * d + lo ≤ i ∧ i < n * d + lo + y.k) →
      s₁.store.read q b i = s₀.store.read q b i := fun q b i h1 h2 => hR q b i (Or.inr ⟨h1, h2⟩)
  have hr := hrec a lo y ha hay hk1
  rw [show D - d = (D - (d + 1)) + 1 by omega]
  -- the kind binder
  change exec I (.seq (.bindIdx _ _ _ _) .skip) s₁ = some s₂ at h
  rw [exec_seq_skip] at h
  cases hs : eighStep M n F R₀ β y.A y.R y.ε y.ℓ (eighTapeSample n d lo) with
  | leaf U e =>
    rw [hs] at hr
    obtain ⟨hkd, hU, hE⟩ := hr
    obtain ⟨v, hv, hk⟩ := Option.bind_eq_some_iff.mp hkd
    rw [exec_bindIdx_of_read I ((hRo p _ _ hKdU hKdE).trans hv) hk (by decide)] at h
    change exec I (.seq (.loop _ _) (.seq (.loop _ _) (.seq (.loop _ _) .skip))) _ = _ at h
    rw [el5_seq_loop_zero rfl, el5_seq_loop_zero rfl, el5_seq_loop_zero rfl, exec_skip] at h
    cases h
    refine ⟨rfl, rfl, ?_, fun _ _ _ _ _ => rfl⟩
    simp only [eighAux, eighSlotTree, hs]
    refine ⟨hU.of_forall_read_eq fun i hi hi' => hRW p _ i (fun _ => ⟨hi, ?_⟩)
      (fun h => absurd h hUE), fun i => (hRW p _ _ (fun h => absurd h.symm hUE)
      (fun _ => ⟨by omega, by omega⟩)).trans (hE i)⟩
    simpa [pairLayout, Nat.mul_comm] using hi'
  | shift b A' σ' =>
    rw [hs] at hr
    have hσ' := el5_eighStep_shift hs
    obtain ⟨v, hv, hk⟩ := Option.bind_eq_some_iff.mp hr
    rw [exec_bindIdx_of_read I ((hRo p _ _ hKdU hKdE).trans hv) hk (by split <;> decide)] at h
    have hch : eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ (a ++ [b]) = some (lo,
        ⟨y.k, A', (eighNextParams M y.R y.ε y.ℓ).1, (eighNextParams M y.R y.ε y.ℓ).2,
          y.ℓ + 1⟩) := by
      rw [eighLoc_append_singleton, hay]
      simp [eighLoc, ha, hs]
    obtain ⟨hUc, hEc⟩ := hout (a ++ [b]) lo _ (by simp [ha]) hch
    have hUc' := hUc.of_forall_read_eq (s' := s₁.store) fun i hi _ => hRU1 p i (by omega)
    have hEc' : ∀ i : Fin y.k, s₁.store.read p H.Ea (n * (d + 1) + lo + i) = _ := fun i =>
      (hRE1 p _ (by omega)).trans (hEc i)
    change exec I (.seq (.loop _ _) (.seq (.loop _ _) (.seq (.loop _ _) .skip))) _ = _ at h
    cases b
    · rw [el5_seq_loop_zero rfl, el5_seq_loop_one rfl] at h
      obtain ⟨s₃, h₁, h⟩ := Option.bind_eq_some_iff.mp h
      rw [el5_seq_loop_zero rfl, exec_skip] at h
      cases h
      obtain ⟨S1, S2, S3, S4, S5⟩ := el5_shift_run p n d lo y.k H ⟨t, 1⟩ hkn hUE htE htU
        (s := { s₁ with cnt := s₁.cnt + I.charge (.toNat p) }) (h := h₁) hUc' hEc'
        ((hRo p _ _ htU htE).trans ht1)
      refine ⟨S1, S2, ?_, S5⟩
      simp only [eighAux, eighSlotTree, hs]
      refine ⟨S3, fun i => (S4 i).trans ?_⟩
      rw [hσ', hyR]
      rfl
    · rw [el5_seq_loop_one rfl] at h
      obtain ⟨s₃, h₁, h⟩ := Option.bind_eq_some_iff.mp h
      rw [el5_seq_loop_zero rfl, el5_seq_loop_zero rfl, exec_skip] at h
      cases h
      obtain ⟨S1, S2, S3, S4, S5⟩ := el5_shift_run p n d lo y.k H ⟨t, 0⟩ hkn hUE htE htU
        (s := { s₁ with cnt := s₁.cnt + I.charge (.toNat p) }) (h := h₁) hUc' hEc'
        ((hRo p _ _ htU htE).trans ht0)
      refine ⟨S1, S2, ?_, S5⟩
      simp only [eighAux, eighSlotTree, hs]
      refine ⟨S3, fun i => (S4 i).trans ?_⟩
      rw [hσ', hyR]
      rfl
  | split kp hkp Qp Qm Ap Am σ' =>
    rw [hs] at hr
    obtain ⟨hσ', hkp0, hkpk⟩ := el5_eighStep_split hs
    obtain ⟨hkd, hkpr, hQp, hQm⟩ := hr
    obtain ⟨v, hv, hk⟩ := Option.bind_eq_some_iff.mp hkd
    rw [exec_bindIdx_of_read I ((hRo p _ _ hKdU hKdE).trans hv) hk (by decide)] at h
    change exec I (.seq (.loop _ _) (.seq (.loop _ _) (.seq (.loop _ _) .skip))) _ = _ at h
    rw [el5_seq_loop_zero rfl, el5_seq_loop_zero rfl, el5_seq_loop_one rfl] at h
    obtain ⟨s₃, h₁, h⟩ := Option.bind_eq_some_iff.mp h
    rw [exec_skip] at h
    cases h
    obtain ⟨v', hv', hk'⟩ := Option.bind_eq_some_iff.mp hkpr
    change exec I (.seq (.bindIdx _ _ _ _) .skip) _ = some _ at h₁
    rw [exec_seq_skip, exec_bindIdx_of_read I ((hRo p _ _ hKpU hKpE).trans hv') hk'
      (by exact hkp)] at h₁
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
    obtain ⟨S1, S2, S3, S4, S5, S6⟩ := el5_split_run hmm p n d lo y.k kp t H hkn hkpk hUE hUQ
      htE htU
      (s := { s₁ with cnt := s₁.cnt + I.charge (.toNat p) + I.charge (.toNat p) }) (h := h₁)
      (hQp.of_forall_read_eq fun i _ _ => hRo p _ i (Ne.symm hUQ) hQE)
      (hQm.of_forall_read_eq fun i _ _ => hRo p _ i (Ne.symm hUQ) hQE)
      (hUp.of_forall_read_eq fun i hi _ => hRU1 p i (by omega))
      (hUm.of_forall_read_eq fun i hi _ => hRU1 p i (by nlinarith))
      (fun j => (hRE1 p _ (by omega)).trans (hEp j))
      (fun j => (hRE1 p _ (by omega)).trans (hEm j))
      ((hRo p _ _ htU htE).trans ht0)
    refine ⟨S1, S2, ?_, S6⟩
    simp only [eighAux, eighSlotTree, hs, ite_true, Bool.false_eq_true, ite_false]
    rw [← hyR] at S4 S5
    refine ⟨S3, fun i => ?_⟩
    by_cases hi : (i : ℕ) < kp
    · rw [el5_e_inl hkp i hi, Sum.elim_inl, hσ']
      exact S4 ⟨i, hi⟩
    · rw [el5_e_inr hkp i (by omega), Sum.elim_inr, hσ']
      have := S5 ⟨i - kp, by omega⟩
      rw [show n * d + lo + kp + (i - kp) = n * d + lo + i by omega] at this
      exact this

/-- One slot of the upward pass: the node at the slot (if any) gets its output; the shape,
the tape positions, every cell outside the blocks of the nodes at the slots up to $lo$, and the
outputs of the slots below are kept. -/
theorem el5_step {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) (p : P)
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
    (hsh : s₁.store.shape = s₀.store.shape) (hps : s₁.pos = s₀.pos)
    (hfr : ∀ q b i, (¬ ((b = H.Ua ∨ b = H.Ea) ∧ H.LevelCell n d b i) ∨
        ∀ (a : List Bool) (lo' : ℕ) (y : EighNode K), a.length = d →
          eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a =
            some (lo', y) → lo' < lo →
          (b ≠ H.Ua ∨ i < 2 * (n * n) * d + 2 * n * lo' ∨
            2 * (n * n) * d + 2 * n * lo' + 2 * (y.k * y.k) ≤ i) ∧
          (b ≠ H.Ea ∨ i < n * d + lo' ∨ n * d + lo' + y.k ≤ i)) →
        s₁.store.read q b i = s₀.store.read q b i)
    (hdone : ∀ (a : List Bool) (lo' : ℕ) (y : EighNode K), a.length = d →
      eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo', y) →
      lo' < lo →
      pairLayout.Holds s₁.store p H.Ua (2 * (n * n) * d + 2 * n * lo')
          (eighAux (eighTapeMachine I p mmR qrR) n F R₀ β (D - d) y.A y.R y.ε y.ℓ
            (eighSlotTree (eighTapeMachine I p mmR qrR) n F R₀ β d lo' y)).1 ∧
        ∀ i : Fin y.k, s₁.store.read p H.Ea (n * d + lo' + i) = some
          ((eighAux (eighTapeMachine I p mmR qrR) n F R₀ β (D - d) y.A y.R y.ε y.ℓ
            (eighSlotTree (eighTapeMachine I p mmR qrR) n F R₀ β d lo' y)).2 i))
    (h : exec I (Builder.bindIdx (ι := ι) p
      ⟨H.Sz, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo)⟩
      (IExp.const n - IExp.var lo) fun k => eighWhen (IExp.var k) <| Builder.bindIdx p
        ⟨H.Kd, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo)⟩ 4 fun c => do
          eighWhen (eighEqInd (IExp.var c) 2) do
            zcopy p (IExp.var k) (IExp.var k) H.Ua
              (eighBlockOff (IExp.const n) (IExp.const d + 1) (IExp.var lo)) H.Ua
              (eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo))
            forRange (IExp.var k) fun i => ins (.bin p .add
              ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo) + IExp.var i⟩
              ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d + 1) (IExp.var lo) + IExp.var i⟩
              ⟨t, 0⟩)
          eighWhen (eighEqInd (IExp.var c) 3) do
            zcopy p (IExp.var k) (IExp.var k) H.Ua
              (eighBlockOff (IExp.const n) (IExp.const d + 1) (IExp.var lo)) H.Ua
              (eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo))
            forRange (IExp.var k) fun i => ins (.bin p .add
              ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo) + IExp.var i⟩
              ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d + 1) (IExp.var lo) + IExp.var i⟩
              ⟨t, 1⟩)
          eighWhen (eighEqInd (IExp.var c) 4) <|
            Builder.bindIdx p ⟨H.Kp, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo)⟩
              (IExp.var k) fun kp => do
              let qo := eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo)
              stmt (.kcall mm p [IExp.var k, IExp.var kp, IExp.var kp]
                [(H.Qa, qo), (H.Ua, eighBlockOff (IExp.const n) (IExp.const d + 1) (IExp.var lo))]
                [(H.Ua, eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo))])
              stmt (.kcall mm p [IExp.var k, IExp.var k - IExp.var kp,
                  IExp.var k - IExp.var kp]
                [(H.Qa, qo + 2 * (IExp.var k * IExp.var kp)),
                  (H.Ua, eighBlockOff (IExp.const n) (IExp.const d + 1)
                    (IExp.var lo + IExp.var kp))]
                [(H.Ua, eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo) +
                  2 * (IExp.var k * IExp.var kp))])
              forRange (IExp.var kp) fun j => ins (.bin p .add
                ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo) + IExp.var j⟩
                ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d + 1) (IExp.var lo) + IExp.var j⟩
                ⟨t, 0⟩)
              forRange (IExp.var k - IExp.var kp) fun j => ins (.bin p .sub
                ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo) + IExp.var kp +
                  IExp.var j⟩
                ⟨H.Ea, eighSlotOff (IExp.const n) (IExp.const d + 1) (IExp.var lo) + IExp.var kp +
                  IExp.var j⟩ ⟨t, 0⟩)).run s₁ = some s₂) :
    s₂.store.shape = s₀.store.shape ∧ s₂.pos = s₀.pos ∧
      (∀ q b i, (¬ ((b = H.Ua ∨ b = H.Ea) ∧ H.LevelCell n d b i) ∨
        ∀ (a : List Bool) (lo' : ℕ) (y : EighNode K), a.length = d →
          eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a =
            some (lo', y) → lo' < lo + 1 →
          (b ≠ H.Ua ∨ i < 2 * (n * n) * d + 2 * n * lo' ∨
            2 * (n * n) * d + 2 * n * lo' + 2 * (y.k * y.k) ≤ i) ∧
          (b ≠ H.Ea ∨ i < n * d + lo' ∨ n * d + lo' + y.k ≤ i)) →
        s₂.store.read q b i = s₀.store.read q b i) ∧
      ∀ (a : List Bool) (lo' : ℕ) (y : EighNode K), a.length = d →
        eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo', y) →
        lo' < lo + 1 →
        pairLayout.Holds s₂.store p H.Ua (2 * (n * n) * d + 2 * n * lo')
            (eighAux (eighTapeMachine I p mmR qrR) n F R₀ β (D - d) y.A y.R y.ε y.ℓ
              (eighSlotTree (eighTapeMachine I p mmR qrR) n F R₀ β d lo' y)).1 ∧
          ∀ i : Fin y.k, s₂.store.read p H.Ea (n * d + lo' + i) = some
            ((eighAux (eighTapeMachine I p mmR qrR) n F R₀ β (D - d) y.A y.R y.ε y.ℓ
              (eighSlotTree (eighTapeMachine I p mmR qrR) n F R₀ β d lo' y)).2 i) := by
  obtain ⟨hUE, -, -, -, -, -, -, hSzU, hSzE, -⟩ := el5_hne hnd
  have hSz : ∀ i, s₁.store.read p H.Sz i = s₀.store.read p H.Sz i := fun i =>
    hfr p _ i (Or.inl fun h => h.1.elim hSzU hSzE)
  change exec I (.seq (.bindIdx _ _ _ _) .skip) s₁ = some s₂ at h
  rw [exec_seq_skip] at h
  by_cases hy : ∃ (a : List Bool) (y : EighNode K), a.length = d ∧
      eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo, y)
  swap
  · push Not at hy
    obtain ⟨v, hv, hk⟩ := Option.bind_eq_some_iff.mp (hlev.2.1 lo hlo fun a y ha => hy a y ha)
    rw [exec_bindIdx_of_read I ((hSz _).trans hv) hk (Nat.zero_le _)] at h
    change exec I (.seq (.loop _ _) .skip) _ = some s₂ at h
    rw [el5_seq_loop_zero (by simp), exec_skip] at h
    cases h
    refine ⟨hsh, hps, fun q b i hb => hfr q b i (hb.imp_right fun H' a lo' y ha hay hlt =>
      H' a lo' y ha hay (by omega)), fun a lo' y ha hay hlt =>
      hdone a lo' y ha hay (lt_of_le_of_ne (Nat.lt_succ_iff.mp hlt) ?_)⟩
    rintro rfl
    exact hy a y ha hay
  obtain ⟨a, y, ha, hay⟩ := hy
  obtain ⟨v, hv, hk⟩ := Option.bind_eq_some_iff.mp (hlev.1 a lo y ha hay).1
  obtain ⟨hk1, hb⟩ := eighLoc_bounds (by omega : 1 ≤ n) hay
  rw [exec_bindIdx_of_read I ((hSz _).trans hv) hk
    (by simp only [IExp.eval_sub, IExp.eval_const, IExp.eval_var]; omega)] at h
  change exec I (.seq (.loop _ _) .skip) _ = some s₂ at h
  rw [el5_seq_loop_one (by simp; omega)] at h
  obtain ⟨s₃, h₁, h⟩ := Option.bind_eq_some_iff.mp h
  rw [exec_skip] at h
  cases h
  -- the nodes below the slot lie before it
  have hbefore : ∀ (a' : List Bool) (lo' : ℕ) (y' : EighNode K), a'.length = d →
      eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a' = some (lo', y') →
      lo' < lo → lo' + y'.k ≤ lo ∧ y'.k ≤ n := by
    intro a' lo' y' ha' hay' hlt
    have hb' := eighLoc_bounds (by omega : 1 ≤ n) hay'
    have hne : a' ≠ a := by
      rintro rfl
      rw [hay] at hay'
      cases hay'
      omega
    have := eighLoc_disjoint (ha'.trans ha.symm) hne hay' hay
    omega
  have hblk : ∀ lo' k', lo' + k' ≤ lo → k' ≤ n →
      2 * n * lo' + 2 * (k' * k') ≤ 2 * n * lo := fun lo' k' h1 h2 => by
    nlinarith [Nat.mul_le_mul_right k' h2]
  obtain ⟨N1, N2, N3, N4⟩ := el5_node hmm p n ℓ₀ F d D (by omega) hd H t ha hay hnd htH ht0 ht1
    hrec hout (s₁ := { s₁ with cnt := s₁.cnt + I.charge (.toNat p) }) (fun q b i hb' => by
      refine hfr q b i (hb'.imp_right fun ⟨hU', hE'⟩ a' lo' y' ha' hay' hlt => ?_)
      obtain ⟨h1, h2⟩ := hbefore a' lo' y' ha' hay' hlt
      have := hblk lo' y'.k h1 h2
      refine ⟨?_, ?_⟩
      · by_cases hbU : b = H.Ua
        · exact Or.inr (Or.inr (by have := hU' hbU; omega))
        · exact Or.inl hbU
      · by_cases hbE : b = H.Ea
        · exact Or.inr (Or.inr (by have := hE' hbE; omega))
        · exact Or.inl hbE) h₁
  have hWin : ∀ b i, ¬ ((b = H.Ua ∨ b = H.Ea) ∧ H.LevelCell n d b i) →
      (b ≠ H.Ua ∨ i < 2 * (n * n) * d + 2 * n * lo ∨
        2 * (n * n) * d + 2 * n * lo + 2 * (y.k * y.k) ≤ i) ∧
      (b ≠ H.Ea ∨ i < n * d + lo ∨ n * d + lo + y.k ≤ i) := by
    intro b i hb'
    have hlt : 2 * n * lo + 2 * (y.k * y.k) ≤ 2 * (n * n) := by
      nlinarith [Nat.mul_le_mul_left n hb]
    refine ⟨?_, ?_⟩
    · by_cases hbU : b = H.Ua
      · subst hbU
        refine Or.inr ?_
        by_contra hc
        refine hb' ⟨Or.inl rfl, Or.inl ⟨Or.inr (Or.inl rfl), by omega, ?_⟩⟩
        rw [Nat.mul_succ]
        omega
      · exact Or.inl hbU
    · by_cases hbE : b = H.Ea
      · subst hbE
        refine Or.inr ?_
        by_contra hc
        refine hb' ⟨Or.inr rfl, Or.inr (Or.inl ⟨Or.inl rfl, by omega, ?_⟩)⟩
        rw [Nat.mul_succ]
        omega
      · exact Or.inl hbE
  refine ⟨N1.trans hsh, N2.trans hps, fun q b i hb' => ?_, fun a' lo' y' ha' hay' hlt => ?_⟩
  · have hW : (b ≠ H.Ua ∨ i < 2 * (n * n) * d + 2 * n * lo ∨
        2 * (n * n) * d + 2 * n * lo + 2 * (y.k * y.k) ≤ i) ∧
        (b ≠ H.Ea ∨ i < n * d + lo ∨ n * d + lo + y.k ≤ i) := by
      rcases hb' with hb' | hb'
      · exact hWin b i hb'
      · exact hb' a lo y ha hay (Nat.lt_succ_self lo)
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
      obtain ⟨h1, h2⟩ := hbefore a' lo' y' ha' hay' hlt'
      have := hblk lo' y'.k h1 h2
      refine ⟨hU'.of_forall_read_eq fun i hi hi' => N4 p _ i (Or.inr (Or.inl ?_))
        (Or.inl hUE), fun i => (N4 p _ _ (Or.inl (Ne.symm hUE))
          (Or.inr (Or.inl (by omega)))).trans (hE' i)⟩
      simp only [pairLayout] at hi'
      have : y'.k * y'.k * 2 = 2 * (y'.k * y'.k) := by ring
      omega

omit [AddMonoid C] [Inhabited K] in
/-- The level encoding reads only the arenas: it transfers to a store that reads as `s` there. -/
theorem el5_transfer {H : EighArenas} {s s' : Store P K} {p : P}
    {M : FloatMachine K ℕ ℕ} {n F ℓ₀ D d : ℕ} {R₀ β : K} {root : EighNode K}
    {sem : ScalarSem P K} (hs : ∀ q b i, b ∈ H.handles → s'.read q b i = s.read q b i) :
    (H.LevelHolds sem s p M n F ℓ₀ R₀ β root d → H.LevelHolds sem s' p M n F ℓ₀ R₀ β root d) ∧
      (H.RecordHolds sem s p M n F R₀ β root d → H.RecordHolds sem s' p M n F R₀ β root d) ∧
      (H.OutHolds s p M n F D R₀ β root d → H.OutHolds s' p M n F D R₀ β root d) := by
  have hm : ∀ {b}, b ∈ [H.Ma, H.Ua, H.Qa, H.Ea, H.Sz, H.Kd, H.Kp, H.Lv] → b ∈ H.handles :=
    fun h => h
  have hR : ∀ {b i k}, b ∈ H.handles → ReadsIdx sem s p b i k → ReadsIdx sem s' p b i k :=
    fun hb h => by unfold ReadsIdx at h ⊢; rw [hs p _ _ hb]; exact h
  have hH : ∀ {b off l m} {Y : Matrix (Fin l) (Fin m) (K × K)}, b ∈ H.handles →
      pairLayout.Holds s p b off Y → pairLayout.Holds s' p b off Y :=
    fun hb h => h.of_forall_read_eq fun i _ _ => hs p _ i hb
  refine ⟨fun h => ⟨fun a lo y ha hay => ?_, fun lo hlo hno => ?_, ?_, ?_⟩,
    fun h a lo y ha hay hk => ?_, fun h a lo y ha hay => ?_⟩
  · obtain ⟨h1, h2⟩ := h.1 a lo y ha hay
    exact ⟨hR (hm (by simp)) h1, hH (hm (by simp)) h2⟩
  · exact hR (hm (by simp)) (h.2.1 lo hlo hno)
  · rw [hs p _ _ (hm (by simp))]; exact h.2.2.1
  · rw [hs p _ _ (hm (by simp))]; exact h.2.2.2
  · have := h a lo y ha hay hk
    split at this
    · obtain ⟨h1, h2, h3⟩ := this
      exact ⟨hR (hm (by simp)) h1, hH (hm (by simp)) h2,
        fun i => (hs p _ _ (hm (by simp))).trans (h3 i)⟩
    · exact hR (hm (by simp)) this
    · obtain ⟨h1, h2, h3, h4⟩ := this
      exact ⟨hR (hm (by simp)) h1, hR (hm (by simp)) h2, hH (hm (by simp)) h3,
        hH (hm (by simp)) h4⟩
  · obtain ⟨h1, h2⟩ := h a lo y ha hay
    exact ⟨hH (hm (by simp)) h1, fun i => (hs p _ _ (hm (by simp))).trans (h2 i)⟩

/-- One level of the upward pass: if kernel `mm` of `I` is the routine `mmR` on interleaved
pairs, under exact integer literals up to $n + 4$ and the exact floor conversion, a successful run
of `NLAlib.eighUpLevel` at depth $d < D$ from a state whose arenas hold the nodes of depth $d$
(their sizes), the records of depth $d$ and the outputs of depth $d + 1$, with the window of depth
$d$ in its cell and the stored $\mathrm{fl}(2)$ in `two`, ends with the outputs of depth $d$
(`NLAlib.EighArenas.OutHolds` at $d$, budget $D - d$); every cell outside the output and eigenvalue
arenas at depth $d$ is unchanged, the store shape and the tape positions too. No printed source. -/
theorem holds_of_exec_eighUpLevel {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    {dec : P → K → ℝ} (p : P) (n ℓ₀ F d D : ℕ) (hd : d < D)
    (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem) (H : EighArenas)
    {two : Cell ℕ ℕ} {st st' : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hH : H.Shaped st.store p n D) (htwo : two.buf ∉ H.handles)
    (htwov : st.store.read p two.buf two.idx.eval = I.sem.lit p ((2 : ℕ) : ℚ))
    (hlev : H.LevelHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d)
    (hrec : H.RecordHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d)
    (hout : H.OutHolds st.store p (eighTapeMachine I p mmR qrR) n F D R₀ β ⟨n, A, R₀, ε, ℓ₀⟩
      (d + 1))
    (h : exec I (eighUpLevel p mm (.const n) (.const d) H.Lv H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp
      two).run st = some st') :
    H.OutHolds st'.store p (eighTapeMachine I p mmR qrR) n F D R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ d ∧
      (∀ q b i, ¬ ((b = H.Ua ∨ b = H.Ea) ∧ H.LevelCell n d b i) →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  have hsz : ∀ {b : ℕ} {x : P × ℕ}, st.store.shape[b]? = some x → b < st.store.size :=
    fun h => by simpa [Store.size_shape] using (Array.getElem?_eq_some_iff.mp h).1
  obtain ⟨hnd, hMa, hUa, hQa, hEa, hSz, hKd, hKp, hLv⟩ := id hH
  have hltH : ∀ b ∈ H.handles, b < st.store.size := by
    simp only [EighArenas.handles, List.mem_cons, List.not_mem_nil, or_false]
    rintro b (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    exacts [hsz hMa, hsz hUa, hsz hQa, hsz hEa, hsz hSz, hsz hKd, hsz hKp, hsz hLv]
  have htH : st.store.size ∉ H.handles := fun hm => absurd (hltH _ hm) (lt_irrefl _)
  obtain ⟨z2, hz2, -⟩ := hlit p 2 (by omega)
  have htwo' : st.store.read p two.buf two.idx.eval = some z2 := htwov.trans hz2
  have ltwo := Store.lt_size_of_read_eq_some htwo'
  set M := eighTapeMachine I p mmR qrR with hM
  -- the scope and the scratch cells
  change exec I (.seq (.alloc p _ _) .skip) st = some st' at h
  rw [exec_seq_skip, exec_alloc] at h
  obtain ⟨s₁, h₁, rfl⟩ := Option.map_eq_some_iff.mp h
  change exec I (.seq (.instr _) (.seq (.instr _) (.seq (.loop _ _) .skip))) _ = some s₁ at h₁
  rw [exec_seq] at h₁
  obtain ⟨σa, ha, h₁⟩ := Option.bind_eq_some_iff.mp h₁
  rw [exec_seq] at h₁
  obtain ⟨σb, hb, h₁⟩ := Option.bind_eq_some_iff.mp h₁
  rw [exec_seq_skip] at h₁
  rw [exec_instr] at ha hb
  obtain ⟨ra, hra, rfl⟩ := Option.map_eq_some_iff.mp ha
  obtain ⟨rb, hrb, rfl⟩ := Option.map_eq_some_iff.mp hb
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hra hrb
  obtain ⟨xR, hxR, x2, hx2, v0, hv0, wa, hwa, rfl⟩ := hra
  obtain ⟨x0, hx0, v1, hv1, wb, hwb, rfl⟩ := hrb
  set t := st.store.size with ht
  have hP : ∀ {q : P} {b i : ℕ}, b < t →
      Store.read (st.store.push (p, Array.replicate (2 : IExp ℕ).eval none)) q b i =
        st.store.read q b i := fun hb => Store.read_push_of_lt hb
  have hrd₀ : ∀ q b i, b < t → wb.read q b i = st.store.read q b i := fun q b i hb => by
    rw [Store.read_of_write_eq_some_of_ne hwb (Or.inl (Nat.ne_of_lt hb)),
      Store.read_of_write_eq_some_of_ne hwa (Or.inl (Nat.ne_of_lt hb)), hP hb]
  rw [hP (hltH _ (by simp [EighArenas.handles]))] at hxR
  rw [show (2 * IExp.const d : IExp ℕ).eval = 2 * d from rfl, hlev.2.2.1] at hxR
  cases hxR
  rw [hP ltwo, htwo'] at hx2
  cases hx2
  rw [Store.read_of_write_eq_some hwa] at hx0
  cases hx0
  have hv0' : I.sem.bin p .div (eighLevelParams M R₀ ε ℓ₀ d).1 z2 = some v0 := hv0
  rw [IExp.eval_zero] at hwa
  rw [IExp.eval_one] at hwb
  dsimp only at hwb ⊢
  have ht0 : wb.read p t 0 = some (M.div (eighLevelParams M R₀ ε ℓ₀ d).1 (M.ofNat 2)) := by
    rw [Store.read_of_write_eq_some_of_ne hwb (Or.inr (by decide)),
      Store.read_of_write_eq_some hwa]
    change some v0 = some ((I.sem.bin p .div (eighLevelParams M R₀ ε ℓ₀ d).1
      ((I.sem.lit p ((2 : ℕ) : ℚ)).getD default)).getD default)
    rw [hz2, Option.getD_some, hv0', Option.getD_some]
  have ht1 : wb.read p t 1 = some (M.neg (M.div (eighLevelParams M R₀ ε ℓ₀ d).1 (M.ofNat 2))) := by
    rw [Store.read_of_write_eq_some hwb]
    change some v1 = some ((I.sem.un p .neg ((I.sem.bin p .div (eighLevelParams M R₀ ε ℓ₀ d).1
      ((I.sem.lit p ((2 : ℕ) : ℚ)).getD default)).getD default)).getD default)
    rw [hz2, Option.getD_some, hv0', Option.getD_some, hv1, Option.getD_some]
  obtain ⟨T1, T2, T3⟩ := el5_transfer (H := H) (s := st.store) (s' := wb) (p := p) (M := M)
    (n := n) (F := F) (ℓ₀ := ℓ₀) (D := D) (d := d) (R₀ := R₀) (β := β)
    (root := ⟨n, A, R₀, ε, ℓ₀⟩) (sem := I.sem) fun q b i hb => hrd₀ q b i (hltH b hb)
  obtain ⟨T1', T2', T3'⟩ := el5_transfer (H := H) (s := st.store) (s' := wb) (p := p) (M := M)
    (n := n) (F := F) (ℓ₀ := ℓ₀) (D := D) (d := d + 1) (R₀ := R₀) (β := β)
    (root := ⟨n, A, R₀, ε, ℓ₀⟩) (sem := I.sem) fun q b i hb => hrd₀ q b i (hltH b hb)
  refine (fun L => ?_) (forall_of_exec_loop_eq_some I (n := .const n)
    (fun lo (s : St P K C) => s.store.shape = wb.shape ∧ s.pos = st.pos ∧
      (∀ q b i, (¬ ((b = H.Ua ∨ b = H.Ea) ∧ H.LevelCell n d b i) ∨
        ∀ (a : List Bool) (lo' : ℕ) (y : EighNode K), a.length = d →
          eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo', y) → lo' < lo →
          (b ≠ H.Ua ∨ i < 2 * (n * n) * d + 2 * n * lo' ∨
            2 * (n * n) * d + 2 * n * lo' + 2 * (y.k * y.k) ≤ i) ∧
          (b ≠ H.Ea ∨ i < n * d + lo' ∨ n * d + lo' + y.k ≤ i)) →
        s.store.read q b i = wb.read q b i) ∧
      ∀ (a : List Bool) (lo' : ℕ) (y : EighNode K), a.length = d →
        eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo', y) → lo' < lo →
        pairLayout.Holds s.store p H.Ua (2 * (n * n) * d + 2 * n * lo')
            (eighAux M n F R₀ β (D - d) y.A y.R y.ε y.ℓ (eighSlotTree M n F R₀ β d lo' y)).1 ∧
          ∀ i : Fin y.k, s.store.read p H.Ea (n * d + lo' + i) = some
            ((eighAux M n F R₀ β (D - d) y.A y.R y.ε y.ℓ (eighSlotTree M n F R₀ β d lo' y)).2 i))
    ?_ ?_ h₁)
  rotate_left
  · exact ⟨rfl, rfl, fun _ _ _ _ => rfl, fun _ _ _ _ _ h => absurd h (Nat.not_lt_zero _)⟩
  · exact fun lo hlo s₂ s₃ ⟨hsh, hps, hfr, hdone⟩ hex =>
      el5_step hmm p n ℓ₀ F d D hd H t (s₀ := { st with store := wb }) (by simpa using hlo) hnd
        htH ht0 ht1 (T1 hlev) (T2 hrec) (T3' hout) hsh hps hfr hdone hex
  obtain ⟨Lsh, Lps, Lfr, Ldone⟩ := L
  simp only [IExp.eval_const] at Ldone
  have hs₁ : s₁.store.size = t + 1 := by
    have := congrArg Array.size Lsh
    rw [Store.shape_of_write_eq_some hwb, Store.shape_of_write_eq_some hwa] at this
    simpa [Store.shape] using this
  have hpop : ∀ {q : P} {b i : ℕ}, b < t → Store.read s₁.store.pop q b i = s₁.store.read q b i :=
    fun hb => Store.read_pop_of_lt (by omega)
  refine ⟨fun a lo y ha hay => ?_, fun q b i hb => ?_, ?_, Lps⟩
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hy0 : y.k = 0 := by
        cases a with
        | nil => cases hay; rfl
        | cons b a => simp [eighLoc, eighStep] at hay
      have hk : ∀ i : Fin y.k, False := fun i => absurd i.isLt (by omega)
      exact ⟨fun i => (hk i).elim, fun i => (hk i).elim⟩
    have hb := eighLoc_bounds hn hay
    obtain ⟨hU, hE⟩ := Ldone a lo y ha hay (by omega)
    exact ⟨hU.of_forall_read_eq fun i _ _ => hpop (hltH _ (by simp [EighArenas.handles])),
      fun i => (hpop (hltH _ (by simp [EighArenas.handles]))).trans (hE i)⟩
  · by_cases hbt : b < t
    · exact (hpop hbt).trans ((Lfr q b i (Or.inl hb)).trans (hrd₀ q b i hbt))
    · have hsz' : (Array.pop s₁.store).size = t := by simp [hs₁]
      exact (Store.read_eq_none_of_size_le (by omega)).trans
        (Store.read_eq_none_of_size_le (by omega)).symm
  · rw [Store.shape_pop, Lsh, Store.shape_of_write_eq_some hwb, Store.shape_of_write_eq_some hwa]
    simp [Store.shape]

end NLAlib
