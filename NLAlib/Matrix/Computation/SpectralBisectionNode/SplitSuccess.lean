/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SpectralBisectionNode.Compress

/-!
# The split block of the spectral bisection node step succeeds

A split of the node step of `NLAlib.eighProg` (`NLAlib.eighSplitBlock`: two deflations and two
compressions, into the two children of the node) succeeds under the standard model with every value
in range and $u(p) < 1$, with an exact literal $2$, if the kernels are routines on pairs and the
arenas are allocated. The deflation and compression blocks at index expressions run as at the
constants of their values.

## Main results

* `NLAlib.exists_exec_eighSplitBlock`: a split succeeds.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {Su Sg : Type} {toNat : K → ℕ} {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}
  {unif : K → Su → K} {normal : Sg → K × K}

omit [Inhabited K] in
/-- An allocation succeeds when its body succeeds on the allocated state. -/
theorem exists_exec_alloc_of_exists_split {p : P} {len : IExp ℕ}
    {body : ℕ → Stmt P ι ℕ ℕ} {st : St P K C}
    (h : ∃ st', exec I (body st.store.size) { st with
          store := st.store.push (p, Array.replicate len.eval none),
          cur := Function.update st.cur p (st.cur p + len.eval),
          peak := Function.update st.peak p (max (st.peak p) (st.cur p + len.eval)),
          curW := st.curW + len.eval * I.width p,
          peakW := max st.peakW (st.curW + len.eval * I.width p) } = some st') :
    ∃ st', exec I (.alloc p len body) st = some st' := by
  obtain ⟨st', h⟩ := h
  exact ⟨_, by rw [exec_alloc, h]; rfl⟩

omit [Inhabited K] in
/-- A deflation block, then the rest: the run of the block, then the rest. -/
theorem exec_eighDeflateBlock_bind_split (p : P) (mm qr : ι) (n k r lo : IExp ℕ)
    (side : ℕ) (Sg : ℕ) (sq : Cell ℕ ℕ) (Pm G Y Qf Rf Qa : ℕ) (qo : IExp ℕ)
    (f : Unit → Builder P ι ℕ ℕ Unit) (st : St P K C) :
    exec I (eighDeflateBlock p mm qr n k r lo side Sg sq Pm G Y Qf Rf Qa qo >>= f).run st =
      (exec I (eighDeflateBlock p mm qr n k r lo side Sg sq Pm G Y Qf Rf Qa qo).run st).bind
        (exec I (f ()).run) := by
  change exec I (.seq _ (.seq _ (.seq _ (.seq _ _)))) st =
    (exec I (.seq _ (.seq _ (.seq _ (.seq _ .skip)))) st).bind _
  simp only [exec_seq, Option.bind_assoc, exec_skip, Option.bind_some]
  rfl

omit [Inhabited K] in
/-- A compression block, then the rest: the run of the block, then the rest. -/
theorem exec_eighCompressBlock_bind_split (p : P) (mm : ι) (k r : IExp ℕ) (Qa : ℕ)
    (qo : IExp ℕ) (Ma : ℕ) (mo co : IExp ℕ) (two sg : Cell ℕ ℕ) (Qh C1 C2 C3 : ℕ)
    (f : Unit → Builder P ι ℕ ℕ Unit) (st : St P K C) :
    exec I (eighCompressBlock p mm k r Qa qo Ma mo co two sg Qh C1 C2 C3 >>= f).run st =
      (exec I (eighCompressBlock p mm k r Qa qo Ma mo co two sg Qh C1 C2 C3).run st).bind
        (exec I (f ()).run) := by
  change exec I (.seq _ (.seq _ (.seq _ (.seq _ (.seq _ _))))) st =
    (exec I (.seq _ (.seq _ (.seq _ (.seq _ (.seq _ .skip))))) st).bind _
  simp only [exec_seq, Option.bind_assoc, exec_skip, Option.bind_some]
  rfl

omit [Inhabited K] in
/-- A deflation block at an index expression for the rank runs as at its value. -/
theorem exec_eighDeflateBlock_congr_split (p : P) (mm qr : ι) (n k r lo : IExp ℕ)
    (side : ℕ) (Sg : ℕ) (sq : Cell ℕ ℕ) (Pm G Y Qf Rf Qa : ℕ) (qo : IExp ℕ) (st : St P K C) :
    exec I (eighDeflateBlock p mm qr n k r lo side Sg sq Pm G Y Qf Rf Qa qo).run st =
      exec I (eighDeflateBlock p mm qr n k (.const r.eval) lo side Sg sq Pm G Y Qf Rf Qa
        qo).run st :=
  exec_eq_of_normIdx_eq I rfl st

omit [Inhabited K] in
/-- A compression block at an index expression for the rank runs as at its value. -/
theorem exec_eighCompressBlock_congr_split (p : P) (mm : ι) (k r : IExp ℕ) (Qa : ℕ)
    (qo : IExp ℕ) (Ma : ℕ) (mo co : IExp ℕ) (two sg : Cell ℕ ℕ) (Qh C1 C2 C3 : ℕ)
    (st : St P K C) :
    exec I (eighCompressBlock p mm k r Qa qo Ma mo co two sg Qh C1 C2 C3).run st =
      exec I (eighCompressBlock p mm k (.const r.eval) Qa qo Ma mo co two sg Qh C1 C2
        C3).run st :=
  exec_eq_of_normIdx_eq I rfl st

/-- A packed complex entry lies in its block. -/
private theorem pair_idx_lt_split {l m : ℕ} (i : Fin l) (j : Fin m) (t : Fin 2) :
    2 * ((i : ℕ) + l * j) + t < 2 * (l * m) := by
  have := i.2; have := j.2; have := t.2
  have : l * ((j : ℕ) + 1) ≤ l * m := Nat.mul_le_mul_left l j.2
  nlinarith

/-- The index arithmetic of a split: the blocks of the bases and of the compressions fit their
arenas, and the compressions lie past the node's block. -/
private theorem eighSplit_bounds_split {n d lo k kp D : ℕ} (hk : lo + k ≤ n) (hkpk : kp < k)
    (hd : d < D) :
    2 * (n * n) * d + 2 * n * lo + 2 * (k * kp) ≤ 2 * (n * n) * D ∧
      2 * (n * n) * d + 2 * n * lo + 2 * (k * kp) + 2 * (k * (k - kp)) ≤ 2 * (n * n) * D ∧
      2 * (n * n) * (d + 1) + 2 * n * (lo + kp) + 2 * ((k - kp) * (k - kp)) ≤
        2 * (n * n) * (D + 1) ∧
      2 * (n * n) * d + 2 * n * lo + 2 * (k * k) ≤ 2 * (n * n) * (d + 1) + 2 * n * (lo + kp) := by
  obtain ⟨r, rfl⟩ : ∃ r, k = kp + r := ⟨k - kp, by omega⟩
  rw [Nat.add_sub_cancel_left]
  have h1 : r * r ≤ n * r := Nat.mul_le_mul_right _ (by omega)
  have h2 : n * (lo + kp) + n * r ≤ n * n := by
    rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by omega)
  have h3 : n * n * (d + 1) ≤ n * n * D := Nat.mul_le_mul_left _ hd
  have h4 : n * lo + (kp + r) * (kp + r) ≤ n * n := by
    have : (kp + r) * (kp + r) ≤ n * (kp + r) := Nat.mul_le_mul_right _ (by omega)
    have : n * lo + n * (kp + r) ≤ n * n := by
      rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by omega)
    omega
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

-- The kernel call and the four writes unfold large index expressions of the run.
set_option maxHeartbeats 1000000 in
/-- The second compression and the records of a split succeed. -/
private theorem exists_exec_eighSplitTail₂ {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    {u : P → ℝ} {dec : P → K → ℝ} (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P)
    (n d lo k kp : ℕ) (hk : lo + k ≤ n) (hkpk : kp < k) (kpe : IExp ℕ) (hkpe : kpe.eval = kp) (H :
        EighArenas)
    {two nsg : Cell ℕ ℕ} {z2 σ' : K} {st : St P K C} {A : Matrix (Fin k) (Fin k) (K × K)}
    {Qm : Matrix (Fin k) (Fin (k - kp)) (K × K)}
    {D : ℕ} (hd : d < D) (hH : H.Shaped st.store p n D) (Qh C1 C2 C3 : ℕ)
    (hnd : [H.Qa, H.Ma, Qh, C1, C2, C3].Nodup)
    (hscr : ∀ X ∈ [Qh, C1, C2, C3], st.store.shape[X]? = some (p, 2 * (n * n)))
    (hA : pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hQm : pairLayout.Holds st.store p H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (k * kp)) Qm)
    (htwo : st.store.read p two.buf two.idx.eval = some z2) (htwo0 : dec p z2 ≠ 0)
    (hnσ : st.store.read p nsg.buf nsg.idx.eval = some σ')
    (hcells : ∀ c ∈ [two, nsg], c.buf ∉ [H.Ma, Qh, C1, C2, C3]) :
    ∃ st', exec I (do
      eighCompressBlock p mm (.const k) (.const k - kpe) H.Qa
        (eighBlockOff (.const n) (.const d) (.const lo) + 2 * (.const k * kpe)) H.Ma
        (eighBlockOff (.const n) (.const d) (.const lo))
        (eighBlockOff (.const n) (.const d + 1) (.const lo + kpe)) two nsg Qh C1 C2 C3
      ins (.litIdx p ⟨H.Sz, eighSlotOff (.const n) (.const d + 1) (.const lo)⟩ kpe)
      ins (.litIdx p ⟨H.Sz, eighSlotOff (.const n) (.const d + 1) (.const lo + kpe)⟩
        (.const k - kpe))
      ins (.litIdx p ⟨H.Kd, eighSlotOff (.const n) (.const d) (.const lo)⟩ 4)
      ins (.litIdx p ⟨H.Kp, eighSlotOff (.const n) (.const d) (.const lo)⟩ kpe) :
        Builder P ι ℕ ℕ Unit).run st = some st' := by
  subst hkpe
  obtain ⟨-, hMa, -, -, -, hSz, hKd, hKp, -⟩ := id hH
  have hr : ∀ (i : Instr P ℕ ℕ) (b : Builder P ι ℕ ℕ Unit),
      (ins i >>= fun _ => b).run = .seq (.instr i) b.run := fun _ _ => rfl
  have hkn : k ≤ n := by omega
  have hcM : ∀ c ∈ [two, nsg], c.buf ≠ H.Ma := fun c hc h => hcells c hc (by simp [h])
  have hcS : ∀ c ∈ [two, nsg], c.buf ∉ [Qh, C1, C2, C3] := fun c hc h =>
    hcells c hc (List.mem_cons_of_mem _ h)
  have hco2 : blockDisjoint
      (H.Ma, (eighBlockOff (.const n) (.const d + 1) (.const lo + kpe)).eval,
        2 * ((k - (kpe.eval)) * (k - (kpe.eval))))
      (H.Ma, (eighBlockOff (.const n) (.const d) (.const lo)).eval, 2 * (k * k)) = true := by
    simp only [blockDisjoint, eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const,
      IExp.eval_ofNat, bne_self_eq_false, Bool.false_or, Bool.or_eq_true]
    exact Or.inr (decide_eq_true (eighSplit_bounds_split hk hkpk hd).2.2.2)
  rw [exec_eighCompressBlock_bind_split, exec_eighCompressBlock_congr_split]
  simp only [IExp.eval_sub, IExp.eval_const]
  have hcolen2 : (eighBlockOff (.const n) (.const d + 1) (.const lo + kpe)).eval +
      2 * ((k - (kpe.eval)) * (k - (kpe.eval))) ≤ 2 * (n * n) * (D + 1) := by
    simp only [eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat]
    exact (eighSplit_bounds_split hk hkpk hd).2.2.1
  have hqo : pairLayout.Holds st.store p H.Qa
      (eighBlockOff (.const n) (.const d) (.const lo) + 2 * (IExp.const k * kpe)).eval
      Qm := by
    simp only [eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat]
    exact hQm
  have hmo : pairLayout.Holds st.store p H.Ma
      (eighBlockOff (.const n) (.const d) (.const lo)).eval A := by
    simp only [eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat]
    exact hA
  obtain ⟨st6, h6⟩ := exists_exec_eighCompressBlock hmm hsem p n k (k - (kpe.eval)) hkn
      (Nat.sub_le _ _)
    (Qh := Qh) (C1 := C1) (C2 := C2) (C3 := C3)
    (qo := eighBlockOff (.const n) (.const d) (.const lo) + 2 * (IExp.const k * kpe))
    (mo := eighBlockOff (.const n) (.const d) (.const lo))
    (co := eighBlockOff (.const n) (.const d + 1) (.const lo + kpe)) (Q := Qm)
    (A := A) (c₂ := z2) (σ := σ') (two := two) (sg := nsg) hqo hmo htwo htwo0 hnσ hnd
    ⟨hcS two (by simp), hcS nsg (by simp)⟩ hco2 ⟨_, hMa, hcolen2⟩
    (fun X hX => ⟨_, hscr X hX, le_rfl⟩)
  obtain ⟨-, -, hsh6, -⟩ := holds_of_exec_eighCompressBlock (toNat := fun _ => 0)
    (qrR := @fun _ _ X => (Matrix.of fun _ _ => default, X)) (unif := fun x (_ : Unit) => x)
    (normal := fun (_ : Unit) => ((default : K), (default : K))) hmm p k (k - (kpe.eval))
    (qo := eighBlockOff (.const n) (.const d) (.const lo) + 2 * (IExp.const k * kpe))
    (mo := eighBlockOff (.const n) (.const d) (.const lo))
    (co := eighBlockOff (.const n) (.const d + 1) (.const lo + kpe)) (st' := st6) hqo hmo
    htwo hnσ hnd ⟨hcS two (by simp), hcS nsg (by simp)⟩ hco2
    ⟨by simp [blockDisjoint, Ne.symm (hcM two (by simp))],
      by simp [blockDisjoint, Ne.symm (hcM nsg (by simp))]⟩ (by exact h6)
  rw [h6, Option.bind_some]
  have hlt1 : n * (d + 1) + n ≤ n * (D + 1) := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
  obtain ⟨v1, hv1⟩ := hsem.lit_ok p ((kpe).eval : ℚ) trivial
  obtain ⟨s7, hs7⟩ := Store.exists_write_eq_some_of_getElem?_shape v1 (by rw [hsh6]; exact hSz)
    (show (eighSlotOff (.const n) (.const d + 1) (.const lo)).eval < _ by
      simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat]
      omega)
  rw [hr, exec_seq_instr_litIdx I hv1 hs7]
  have hsh7 := (Store.shape_of_write_eq_some hs7).trans hsh6
  obtain ⟨v2, hv2⟩ := hsem.lit_ok p ((IExp.const k - kpe).eval : ℚ) trivial
  obtain ⟨s8, hs8⟩ := Store.exists_write_eq_some_of_getElem?_shape v2 (by rw [hsh7]; exact hSz)
    (show (eighSlotOff (.const n) (.const d + 1) (.const lo + kpe)).eval < _ by
      simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat]
      omega)
  rw [hr, exec_seq_instr_litIdx I hv2 hs8]
  have hsh8 := (Store.shape_of_write_eq_some hs8).trans hsh7
  have hlt2 : n * d + n ≤ n * D := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
  obtain ⟨v3, hv3⟩ := hsem.lit_ok p (((4 : IExp ℕ)).eval : ℚ) trivial
  obtain ⟨s9, hs9⟩ := Store.exists_write_eq_some_of_getElem?_shape v3 (by rw [hsh8]; exact hKd)
    (show (eighSlotOff (.const n) (.const d) (.const lo)).eval < _ by
      simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const]
      omega)
  rw [hr, exec_seq_instr_litIdx I hv3 hs9]
  have hsh9 := (Store.shape_of_write_eq_some hs9).trans hsh8
  obtain ⟨v4, hv4⟩ := hsem.lit_ok p ((kpe).eval : ℚ) trivial
  obtain ⟨s10, hs10⟩ := Store.exists_write_eq_some_of_getElem?_shape v4 (by rw [hsh9]; exact hKp)
    (show (eighSlotOff (.const n) (.const d) (.const lo)).eval < _ by
      simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const]
      omega)
  exact ⟨_, (exec_seq_instr_litIdx I hv4 hs10).trans (exec_skip I _)⟩

/-- The compressions and the records of a split succeed. -/
private theorem exists_exec_eighSplitTail {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    {u : P → ℝ} {dec : P → K → ℝ} (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P)
    (n d lo k kp : ℕ) (hk : lo + k ≤ n) (hkpk : kp < k) (kpe : IExp ℕ) (hkpe : kpe.eval = kp) (H :
        EighArenas)
    {two sg nsg : Cell ℕ ℕ} {z2 σ σ' : K} {st : St P K C} {A : Matrix (Fin k) (Fin k) (K × K)}
    {Qp : Matrix (Fin k) (Fin kp) (K × K)} {Qm : Matrix (Fin k) (Fin (k - kp)) (K × K)}
    {D : ℕ} (hd : d < D) (hH : H.Shaped st.store p n D) (Qh C1 C2 C3 : ℕ)
    (hnd : [H.Qa, H.Ma, Qh, C1, C2, C3].Nodup)
    (hscr : ∀ X ∈ [Qh, C1, C2, C3], st.store.shape[X]? = some (p, 2 * (n * n)))
    (hA : pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hQp : pairLayout.Holds st.store p H.Qa (2 * (n * n) * d + 2 * n * lo) Qp)
    (hQm : pairLayout.Holds st.store p H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (k * kp)) Qm)
    (htwo : st.store.read p two.buf two.idx.eval = some z2) (htwo0 : dec p z2 ≠ 0)
    (hσ : st.store.read p sg.buf sg.idx.eval = some σ)
    (hnσ : st.store.read p nsg.buf nsg.idx.eval = some σ')
    (hcells : ∀ c ∈ [two, sg, nsg], c.buf ∉ [H.Ma, Qh, C1, C2, C3]) :
    ∃ st', exec I (do
      eighCompressBlock p mm (.const k) kpe H.Qa
        (eighBlockOff (.const n) (.const d) (.const lo)) H.Ma
        (eighBlockOff (.const n) (.const d) (.const lo))
        (eighBlockOff (.const n) (.const d + 1) (.const lo)) two sg Qh C1 C2 C3
      eighCompressBlock p mm (.const k) (.const k - kpe) H.Qa
        (eighBlockOff (.const n) (.const d) (.const lo) + 2 * (.const k * kpe)) H.Ma
        (eighBlockOff (.const n) (.const d) (.const lo))
        (eighBlockOff (.const n) (.const d + 1) (.const lo + kpe)) two nsg Qh C1 C2 C3
      ins (.litIdx p ⟨H.Sz, eighSlotOff (.const n) (.const d + 1) (.const lo)⟩ kpe)
      ins (.litIdx p ⟨H.Sz, eighSlotOff (.const n) (.const d + 1) (.const lo + kpe)⟩
        (.const k - kpe))
      ins (.litIdx p ⟨H.Kd, eighSlotOff (.const n) (.const d) (.const lo)⟩ 4)
      ins (.litIdx p ⟨H.Kp, eighSlotOff (.const n) (.const d) (.const lo)⟩ kpe) :
        Builder P ι ℕ ℕ Unit).run st = some st' := by
  subst hkpe
  obtain ⟨-, hMa, -, -, -, hSz, hKd, hKp, -⟩ := id hH
  have hr : ∀ (i : Instr P ℕ ℕ) (b : Builder P ι ℕ ℕ Unit),
      (ins i >>= fun _ => b).run = .seq (.instr i) b.run := fun _ _ => rfl
  have hkn : k ≤ n := by omega
  have hkk : k * k ≤ n * n := Nat.mul_le_mul hkn hkn
  have hlok : n * lo + k * k ≤ n * n := by nlinarith
  have hdD : n * n * (d + 1) ≤ n * n * D := Nat.mul_le_mul_left _ hd
  -- the first compression
  rw [exec_eighCompressBlock_bind_split, exec_eighCompressBlock_congr_split]
  obtain ⟨st5, h5⟩ := exists_exec_eighCompressBlock hmm hsem p n k (kpe.eval) hkn hkpk.le (Qh := Qh)
    (C1 := C1) (C2 := C2) (C3 := C3) (qo := eighBlockOff (.const n) (.const d) (.const lo))
    (mo := eighBlockOff (.const n) (.const d) (.const lo))
    (co := eighBlockOff (.const n) (.const d + 1) (.const lo)) hQp hA htwo htwo0 hσ hnd
    ⟨fun h => hcells two (by simp) (List.mem_cons_of_mem _ h),
      fun h => hcells sg (by simp) (List.mem_cons_of_mem _ h)⟩
    (by
      simp only [blockDisjoint, eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const,
        IExp.eval_ofNat, bne_self_eq_false, Bool.false_or, Bool.or_eq_true]
      right
      exact decide_eq_true (by nlinarith))
    ⟨_, hMa, by simp only [eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const,
      IExp.eval_ofNat]; nlinarith⟩
    (fun X hX => ⟨_, hscr X hX, le_rfl⟩)
  have hQs : H.Qa ∉ [Qh, C1, C2, C3] := fun h => (List.nodup_cons.mp hnd).1
    (List.mem_cons_of_mem _ h)
  have hMs : H.Ma ∉ [Qh, C1, C2, C3] := (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1
  have hQaMa : H.Qa ≠ H.Ma := fun h => (List.nodup_cons.mp hnd).1 (by simp [h])
  have hcM : ∀ c ∈ [two, sg, nsg], c.buf ≠ H.Ma := fun c hc h => hcells c hc (by simp [h])
  have hcS : ∀ c ∈ [two, sg, nsg], c.buf ∉ [Qh, C1, C2, C3] := fun c hc h =>
    hcells c hc (List.mem_cons_of_mem _ h)
  obtain ⟨-, hfr5, hsh5, -⟩ := holds_of_exec_eighCompressBlock (toNat := fun _ => 0)
    (qrR := @fun _ _ X => (Matrix.of fun _ _ => default, X)) (unif := fun x (_ : Unit) => x)
    (normal := fun (_ : Unit) => ((default : K), (default : K))) hmm p k (kpe.eval)
    (qo := eighBlockOff (.const n) (.const d) (.const lo))
    (mo := eighBlockOff (.const n) (.const d) (.const lo))
    (co := eighBlockOff (.const n) (.const d + 1) (.const lo)) (st' := st5) hQp hA htwo hσ hnd
    ⟨hcS two (by simp), hcS sg (by simp)⟩
    (by
      simp only [blockDisjoint, eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const,
        IExp.eval_ofNat, bne_self_eq_false, Bool.false_or, Bool.or_eq_true]
      right
      exact decide_eq_true (by nlinarith)) ⟨by simp [blockDisjoint, Ne.symm (hcM two (by simp))],
      by simp [blockDisjoint, Ne.symm (hcM sg (by simp))]⟩ (by exact h5)
  have hcell5 : ∀ c ∈ [two, sg, nsg],
      st5.store.read p c.buf c.idx.eval = st.store.read p c.buf c.idx.eval := fun c hc =>
    hfr5 p _ _ (hcS c hc) (by simp [blockDisjoint, hcM c hc])
  have hQm5 : pairLayout.Holds st5.store p H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (k *
      (kpe.eval))) Qm :=
    fun i j t => (hfr5 p _ _ hQs (by simp [blockDisjoint, hQaMa])).trans (hQm i j t)
  have hA5 : pairLayout.Holds st5.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A :=
    fun i j t => (hfr5 p _ _ hMs (by
      have := pair_idx_lt_split i j t
      simp only [blockDisjoint, eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const,
        IExp.eval_ofNat, bne_self_eq_false, Bool.false_or, Bool.or_eq_true]
      left
      exact decide_eq_true (by change _ + (2 * _ + _) + 1 ≤ _; nlinarith))).trans (hA i j t)
  rw [h5, Option.bind_some]
  exact exists_exec_eighSplitTail₂ hmm hsem p n d lo k (kpe.eval) hk hkpk kpe rfl H hd
    (by unfold EighArenas.Shaped; rw [hsh5]; exact hH) Qh C1 C2 C3 hnd
    (fun X hX => by rw [hsh5]; exact hscr X hX) hA5 hQm5 ((hcell5 two (by simp)).trans htwo)
    htwo0 ((hcell5 nsg (by simp)).trans hnσ)
    (fun c hc => hcells c (by simp only [List.mem_cons] at hc ⊢; tauto))

/-- A handle outside five handles is outside the first four and is not the fifth. -/
private theorem not_mem_four_of_not_mem_five_split {x a b c e g : ℕ} (h : x ∉ [a, b, c, e, g]) :
    x ∉ [a, b, c, e] ∧ x ≠ g := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h ⊢
  exact ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩, h.2.2.2.2⟩

/-- The deflations, compressions and records of a split succeed. -/
private theorem exists_exec_eighSplitMid {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P)
    (n d lo k kp : ℕ) (hk : lo + k ≤ n) (hkpk : kp < k) (kpe : IExp ℕ) (hkpe : kpe.eval = kp)
    (H : EighArenas) {Sg Pp Pm : ℕ} {two sg nsg sq : Cell ℕ ℕ} {z2 σ σ' : K} {st : St P K C}
    {A : Matrix (Fin k) (Fin k) (K × K)} {Ppm Pmm : Matrix (Fin k) (Fin k) (K × K)}
    {D : ℕ} (hd : d < D) (hH : H.Shaped st.store p n D)
    (G Y Qf Rf Qh C1 C2 C3 : ℕ)
    (hb1 : [Sg, Pp, G, Y, Qf, Rf, H.Qa].Nodup) (hb2 : [Sg, Pm, G, Y, Qf, Rf, H.Qa].Nodup)
    (hb3 : [H.Qa, H.Ma, Qh, C1, C2, C3].Nodup) (hMaS : H.Ma ∉ [G, Y, Qf, Rf])
    (hnew : ∀ X ∈ [G, Y, Qf, Rf, Qh, C1, C2, C3], st.store.shape[X]? = some (p, 2 * (n * n)))
    (hA : pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hPp : pairLayout.Holds st.store p Pp 0 Ppm) (hPm : pairLayout.Holds st.store p Pm 0 Pmm)
    (hSg : ∀ w < 4 * (n * n), ∃ v, st.store.read p Sg w = some v)
    (hsq : st.store.read p sq.buf sq.idx.eval = some (I.sem.sqrtHalf p))
    (htwo : st.store.read p two.buf two.idx.eval = some z2) (htwo0 : dec p z2 ≠ 0)
    (hσ : st.store.read p sg.buf sg.idx.eval = some σ)
    (hnσ : st.store.read p nsg.buf nsg.idx.eval = some σ')
    (hc' : ∀ c ∈ [two, sg, nsg, sq], c.buf ≠ H.Ma ∧ c.buf ≠ H.Qa ∧ c.buf ∉ [G, Y, Qf, Rf] ∧
      c.buf ∉ [Qh, C1, C2, C3]) :
    ∃ st', exec I (do
      eighDeflateBlock p mm qr (.const n) (.const k) kpe (.const lo) 0 Sg sq Pp G Y Qf Rf
        H.Qa (eighBlockOff (.const n) (.const d) (.const lo))
      eighDeflateBlock p mm qr (.const n) (.const k) (.const k - kpe) (.const lo) 1 Sg sq Pm
        G Y Qf Rf H.Qa (eighBlockOff (.const n) (.const d) (.const lo) +
          2 * (.const k * kpe))
      eighCompressBlock p mm (.const k) kpe H.Qa
        (eighBlockOff (.const n) (.const d) (.const lo)) H.Ma
        (eighBlockOff (.const n) (.const d) (.const lo))
        (eighBlockOff (.const n) (.const d + 1) (.const lo)) two sg Qh C1 C2 C3
      eighCompressBlock p mm (.const k) (.const k - kpe) H.Qa
        (eighBlockOff (.const n) (.const d) (.const lo) + 2 * (.const k * kpe)) H.Ma
        (eighBlockOff (.const n) (.const d) (.const lo))
        (eighBlockOff (.const n) (.const d + 1) (.const lo + kpe)) two nsg Qh C1 C2 C3
      ins (.litIdx p ⟨H.Sz, eighSlotOff (.const n) (.const d + 1) (.const lo)⟩ kpe)
      ins (.litIdx p ⟨H.Sz, eighSlotOff (.const n) (.const d + 1) (.const lo + kpe)⟩
        (.const k - kpe))
      ins (.litIdx p ⟨H.Kd, eighSlotOff (.const n) (.const d) (.const lo)⟩ 4)
      ins (.litIdx p ⟨H.Kp, eighSlotOff (.const n) (.const d) (.const lo)⟩ kpe) :
        Builder P ι ℕ ℕ Unit).run st = some st' := by
  subst hkpe
  obtain ⟨-, hMa, -, hQa, -, -, -, -, -⟩ := id hH
  have hsqb : sq.buf ∉ [G, Y, Qf, Rf, H.Qa] := fun h =>
    (List.mem_append (s := [G, Y, Qf, Rf]) (t := [H.Qa])).mp h |>.elim (hc' sq (by simp)).2.2.1
      fun h' => (hc' sq (by simp)).2.1 (List.mem_singleton.mp h')
  have hMaQ : H.Ma ≠ H.Qa := fun h => (List.nodup_cons.mp hb3).1 (by simp [h])
  have hlen1 : (eighBlockOff (IExp.const n) (IExp.const d) (IExp.const lo)).eval + 2 * (k *
      (kpe.eval)) ≤
      2 * (n * n) * D := by
    simp only [eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat]
    exact (eighSplit_bounds_split hk hkpk hd).1
  have hlen2 : (eighBlockOff (IExp.const n) (IExp.const d) (IExp.const lo) +
      2 * (IExp.const k * kpe)).eval + 2 * (k * (k - (kpe.eval))) ≤ 2 * (n * n) * D := by
    simp only [eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat]
    exact (eighSplit_bounds_split hk hkpk hd).2.1
  -- the first deflation
  rw [exec_eighDeflateBlock_bind_split]
  obtain ⟨st3, h3, ⟨Qp3, hQp3⟩, hfr3, hsh3⟩ := exists_exec_eighDeflateBlock_facts hmm hqr hsem p
    n k (kpe.eval) d lo hk hkpk.le true
    (qo := eighBlockOff (IExp.const n) (IExp.const d) (IExp.const lo)) hPp hsq hSg hb1 hsqb
    (fun X hX => ⟨_, hnew X (List.mem_append_left [Qh, C1, C2, C3] hX), le_rfl⟩)
    ⟨_, hQa, hlen1⟩
  have h3' : exec I (eighDeflateBlock p mm qr (.const n) (.const k) kpe (.const lo) 0 Sg sq
      Pp G Y Qf Rf H.Qa (eighBlockOff (.const n) (.const d) (.const lo))).run st = some st3 := h3
  have hk3 : ∀ q b' i, b' ∉ [G, Y, Qf, Rf] → b' ≠ H.Qa →
      st3.store.read q b' i = st.store.read q b' i := fun q b' i h1 h2 =>
    hfr3 q b' i h1 (by simp [blockDisjoint, h2])
  obtain ⟨hPmS, hPmQ⟩ := not_mem_four_of_not_mem_five_split
    (List.nodup_cons.mp (List.nodup_cons.mp hb2).2).1
  obtain ⟨hSgS, hSgQ⟩ := not_mem_four_of_not_mem_five_split
    (fun h => (List.nodup_cons.mp hb1).1 (List.mem_cons_of_mem _ h))
  have hsq3 := (hk3 _ _ _ (hc' sq (by simp)).2.2.1 (hc' sq (by simp)).2.1).trans hsq
  have hPm3 : pairLayout.Holds st3.store p Pm 0 Pmm := fun i j t =>
    (hk3 _ _ _ hPmS hPmQ).trans (hPm i j t)
  have hSg3 : ∀ w < 4 * (n * n), ∃ v, st3.store.read p Sg w = some v := fun w hw =>
    (hSg w hw).imp fun _ hv => (hk3 _ _ _ hSgS hSgQ).trans hv
  rw [h3', Option.bind_some, exec_eighDeflateBlock_bind_split, exec_eighDeflateBlock_congr_split]
  simp only [IExp.eval_sub, IExp.eval_const]
  -- the second deflation
  obtain ⟨st4, h4, ⟨Qm4, hQm4⟩, hfr4, hsh4⟩ := exists_exec_eighDeflateBlock_facts hmm hqr hsem p
    n k (k - (kpe.eval)) d lo hk
    (Nat.sub_le _ _) false (qo := eighBlockOff (IExp.const n) (IExp.const d) (IExp.const lo) +
      2 * (IExp.const k * kpe)) hPm3 hsq3 hSg3 hb2 hsqb
    (fun X hX => ⟨_, by rw [hsh3]; exact hnew X (List.mem_append_left [Qh, C1, C2, C3] hX),
      le_rfl⟩)
    ⟨_, by rw [hsh3]; exact hQa, hlen2⟩
  have h4' : exec I (eighDeflateBlock p mm qr (.const n) (.const k) (.const (k - (kpe.eval)))
      (.const lo) 1
      Sg sq Pm G Y Qf Rf H.Qa (eighBlockOff (.const n) (.const d) (.const lo) +
        2 * (.const k * kpe))).run st3 = some st4 := h4
  have hk4 : ∀ q b' i, b' ∉ [G, Y, Qf, Rf] → b' ≠ H.Qa →
      st4.store.read q b' i = st.store.read q b' i := fun q b' i h1 h2 =>
    (hfr4 q b' i h1 (by simp [blockDisjoint, h2])).trans (hk3 q b' i h1 h2)
  have hQaS : H.Qa ∉ [G, Y, Qf, Rf] := fun h =>
    (List.nodup_append.mp (show ([G, Y, Qf, Rf] ++ [H.Qa]).Nodup from
      (List.nodup_cons.mp (List.nodup_cons.mp hb1).2).2)).2.2 _ h _ (List.mem_singleton_self _) rfl
  rw [h4', Option.bind_some]
  exact exists_exec_eighSplitTail hmm hsem p n d lo k (kpe.eval) hk hkpk kpe rfl H hd
    (by unfold EighArenas.Shaped; rw [hsh4, hsh3]; exact hH) Qh C1 C2 C3 hb3
    (fun X hX => by rw [hsh4, hsh3]; exact hnew X (List.mem_append_right [G, Y, Qf, Rf] hX))
    (fun i j t => (hk4 _ _ _ hMaS hMaQ).trans (hA i j t))
    (fun i j t => (hfr4 _ _ _ hQaS (by
      have := pair_idx_lt_split i j t
      simp only [blockDisjoint, eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const,
        IExp.eval_ofNat, bne_self_eq_false, Bool.false_or, Bool.or_eq_true]
      left
      exact decide_eq_true (by change _ + (2 * _ + _) + 1 ≤ _; nlinarith))).trans (by
        simpa only [eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const,
          IExp.eval_ofNat] using hQp3 i j t))
    (fun i j t => by simpa only [eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const,
      IExp.eval_ofNat] using hQm4 i j t)
    ((hk4 _ _ _ (hc' two (by simp)).2.2.1 (hc' two (by simp)).2.1).trans htwo) htwo0
    ((hk4 _ _ _ (hc' sg (by simp)).2.2.1 (hc' sg (by simp)).2.1).trans hσ)
    ((hk4 _ _ _ (hc' nsg (by simp)).2.2.1 (hc' nsg (by simp)).2.1).trans hnσ)
    (fun c hc h => by
      have := hc' c (by simp only [List.mem_cons] at hc ⊢; tauto)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h this
      tauto)

/-- The body of a split after its eight allocations succeeds. -/
private theorem exists_exec_eighSplitBody {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hlit : IsExactIntLit dec I.sem 2) (p : P)
    (n d lo k kp : ℕ) (hk : lo + k ≤ n) (hkpk : kp < k) (kpe : IExp ℕ) (hkpe :
        kpe.eval = kp)
    (H : EighArenas) {Sg Pp Pm : ℕ} {two sg nsg sq : Cell ℕ ℕ} {σ : K} {st : St P K C}
    {A : Matrix (Fin k) (Fin k) (K × K)} {Ppm Pmm : Matrix (Fin k) (Fin k) (K × K)}
    {D : ℕ} (hd : d < D) (hH : H.Shaped st.store p n D)
    (G Y Qf Rf Qh C1 C2 C3 : ℕ)
    (hb1 : [Sg, Pp, G, Y, Qf, Rf, H.Qa].Nodup) (hb2 : [Sg, Pm, G, Y, Qf, Rf, H.Qa].Nodup)
    (hb3 : [H.Qa, H.Ma, Qh, C1, C2, C3].Nodup) (hMaS : H.Ma ∉ [G, Y, Qf, Rf])
    (hnew : ∀ X ∈ [G, Y, Qf, Rf, Qh, C1, C2, C3], st.store.shape[X]? = some (p, 2 * (n * n)))
    (hA : pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hPp : pairLayout.Holds st.store p Pp 0 Ppm) (hPm : pairLayout.Holds st.store p Pm 0 Pmm)
    (hSg : ∀ w < 4 * (n * n), ∃ v, st.store.read p Sg w = some v)
    (htwo : st.store.read p two.buf two.idx.eval = I.sem.lit p ((2 : ℕ) : ℚ))
    (hσ : st.store.read p sg.buf sg.idx.eval = some σ)
    (hnσ : st.store.read p nsg.buf nsg.idx.eval = some ((eighTapeMachine I p mmR qrR).neg σ))
    (hc' : ∀ c ∈ [two, sg, nsg, sq], c.buf ≠ H.Ma ∧ c.buf ≠ H.Qa ∧ c.buf ∉ [G, Y, Qf, Rf] ∧
      c.buf ∉ [Qh, C1, C2, C3])
    (hsq : st.store.read p sq.buf sq.idx.eval = some (I.sem.sqrtHalf p)) :
    ∃ st', exec I (do
      eighDeflateBlock p mm qr (.const n) (.const k) kpe (.const lo) 0 Sg sq Pp G Y Qf Rf
        H.Qa (eighBlockOff (.const n) (.const d) (.const lo))
      eighDeflateBlock p mm qr (.const n) (.const k) (.const k - kpe) (.const lo) 1 Sg sq Pm
        G Y Qf Rf H.Qa (eighBlockOff (.const n) (.const d) (.const lo) +
          2 * (.const k * kpe))
      eighCompressBlock p mm (.const k) kpe H.Qa
        (eighBlockOff (.const n) (.const d) (.const lo)) H.Ma
        (eighBlockOff (.const n) (.const d) (.const lo))
        (eighBlockOff (.const n) (.const d + 1) (.const lo)) two sg Qh C1 C2 C3
      eighCompressBlock p mm (.const k) (.const k - kpe) H.Qa
        (eighBlockOff (.const n) (.const d) (.const lo) + 2 * (.const k * kpe)) H.Ma
        (eighBlockOff (.const n) (.const d) (.const lo))
        (eighBlockOff (.const n) (.const d + 1) (.const lo + kpe)) two nsg Qh C1 C2 C3
      ins (.litIdx p ⟨H.Sz, eighSlotOff (.const n) (.const d + 1) (.const lo)⟩ kpe)
      ins (.litIdx p ⟨H.Sz, eighSlotOff (.const n) (.const d + 1) (.const lo + kpe)⟩
        (.const k - kpe))
      ins (.litIdx p ⟨H.Kd, eighSlotOff (.const n) (.const d) (.const lo)⟩ 4)
      ins (.litIdx p ⟨H.Kp, eighSlotOff (.const n) (.const d) (.const lo)⟩ kpe) :
        Builder P ι ℕ ℕ Unit).run st = some st' := by
  obtain ⟨z2, hz2, hdz2⟩ := hlit p 2 le_rfl
  exact exists_exec_eighSplitMid hmm hqr hsem p n d lo k kp hk hkpk kpe hkpe H hd hH G Y Qf Rf Qh
    C1 C2 C3 hb1 hb2 hb3 hMaS hnew hA hPp hPm hSg hsq (htwo.trans hz2)
    (by rw [hdz2]; norm_num) hσ hnσ hc'

/-- A split succeeds, with the Gaussian words only initialised. -/
theorem exists_exec_eighSplitBlock_ex {mm qr : ι}
    (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hlit : IsExactIntLit dec I.sem 2) (p : P)
    (hu : u p < 1) (n d lo k kp : ℕ) (hk : lo + k ≤ n) (hkp : 0 < kp) (hkpk : kp < k) (kpe : IExp
        ℕ) (hkpe : kpe.eval = kp)
    (H : EighArenas) {Sg Pp Pm : ℕ} {two sg nsg sq : Cell ℕ ℕ} {σ : K} {st : St P K C}
    {A : Matrix (Fin k) (Fin k) (K × K)} {Ppm Pmm : Matrix (Fin k) (Fin k) (K × K)}
    {D : ℕ} (hd : d < D) (hH : H.Shaped st.store p n D) (hbufs : (H.handles ++ [Sg, Pp, Pm]).Nodup)
    (hA : pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hPp : pairLayout.Holds st.store p Pp 0 Ppm) (hPm : pairLayout.Holds st.store p Pm 0 Pmm)
    (hSg : ∀ w < 4 * (n * n), ∃ v, st.store.read p Sg w = some v)
    (htwo : st.store.read p two.buf two.idx.eval = I.sem.lit p ((2 : ℕ) : ℚ))
    (hσ : st.store.read p sg.buf sg.idx.eval = some σ)
    (hnσ : st.store.read p nsg.buf nsg.idx.eval = some ((eighTapeMachine I p mmR qrR).neg σ))
    (hcells : ∀ c ∈ [two, sg, nsg, sq], c.buf ∉ H.handles ++ [Sg, Pp, Pm])
    (hsq : st.store.read p sq.buf sq.idx.eval = some (I.sem.sqrtHalf p)) :
    ∃ st', exec I (eighSplitBlock p mm qr (.const n) (.const d) (.const lo) (.const k) kpe
      Sg Pp Pm H.Ma H.Qa H.Sz H.Kd H.Kp two sg nsg sq).run st = some st' := by
  subst hkpe
  have hsz : ∀ {b : ℕ} {x : P × ℕ}, st.store.shape[b]? = some x → b < st.store.size :=
    fun h => by simpa [Store.size_shape] using (Array.getElem?_eq_some_iff.mp h).1
  have hk0 : 0 < k := by omega
  have hn2 : 0 < 4 * (n * n) := by have : 0 < n := (by omega); positivity
  obtain ⟨-, hMa, hUa, hQa, hEa, hSz, hKd, hKp, hLv⟩ := id hH
  have lMa := hsz hMa; have lUa := hsz hUa; have lQa := hsz hQa; have lEa := hsz hEa
  have lSz := hsz hSz; have lKd := hsz hKd; have lKp := hsz hKp; have lLv := hsz hLv
  have lSg := Store.lt_size_of_read_eq_some (hSg 0 hn2).choose_spec
  have lPp := Store.lt_size_of_read_eq_some (hPp ⟨0, hk0⟩ ⟨0, hk0⟩ ⟨0, two_pos⟩)
  have lPm := Store.lt_size_of_read_eq_some (hPm ⟨0, hk0⟩ ⟨0, hk0⟩ ⟨0, two_pos⟩)
  obtain ⟨z2, hz2, -⟩ := hlit p 2 le_rfl
  have ltwo := Store.lt_size_of_read_eq_some (htwo.trans hz2)
  have lsg := Store.lt_size_of_read_eq_some hσ
  have lnsg := Store.lt_size_of_read_eq_some hnσ
  have lsq := Store.lt_size_of_read_eq_some hsq
  have hall : ∀ a ∈ H.handles ++ [Sg, Pp, Pm], a < st.store.size := by
    simp only [EighArenas.handles, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro a (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> assumption
  change ∃ st', exec I (.seq _ .skip) st = some st'
  rw [exec_seq_skip]
  refine exists_exec_alloc_of_exists_split ?_
  refine exists_exec_alloc_of_exists_split ?_
  refine exists_exec_alloc_of_exists_split ?_
  refine exists_exec_alloc_of_exists_split ?_
  refine exists_exec_alloc_of_exists_split ?_
  refine exists_exec_alloc_of_exists_split ?_
  refine exists_exec_alloc_of_exists_split ?_
  refine exists_exec_alloc_of_exists_split ?_
  beta_reduce
  have nSgPp : Sg ≠ Pp := fun h => by simp [EighArenas.handles, h] at hbufs
  have nSgPm : Sg ≠ Pm := fun h => by simp [EighArenas.handles, h] at hbufs
  have nSgQa : Sg ≠ H.Qa := fun h => by simp [EighArenas.handles, h] at hbufs
  have nPpQa : Pp ≠ H.Qa := fun h => by simp [EighArenas.handles, h] at hbufs
  have nPmQa : Pm ≠ H.Qa := fun h => by simp [EighArenas.handles, h] at hbufs
  have nMaQa : H.Ma ≠ H.Qa := fun h => by simp [EighArenas.handles, h] at hbufs
  refine exists_exec_eighSplitBody hmm hqr hsem hlit p n d lo k (kpe.eval) hk hkpk kpe rfl H hd
    (A := A) (Ppm := Ppm) (Pmm := Pmm) (σ := σ) (hH := ?_) (hb1 := ?_) (hb2 := ?_) (hb3 := ?_)
    (hMaS := ?_) (hnew := ?_) (hA := ?_) (hPp := ?_) (hPm := ?_) (hSg := ?_)
    (htwo := ?_) (hσ := ?_) (hnσ := ?_) (hc' := ?_) (hsq := ?_) _ _ _ _ _ _ _ _
  all_goals try simp (disch := first | omega | (simp only [Array.size_push]; omega)) only
    [EighArenas.Shaped, EntryLayout.Holds, Store.getElem?_shape_push_of_lt,
      Store.read_push_of_lt, Store.write_push_of_lt, Array.size_push]
  · exact ⟨hH.1, hMa, hUa, hQa, hEa, hSz, hKd, hKp, hLv⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true]
    omega
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true]
    omega
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro X (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      simp [Store.shape, Array.getElem?_push, Array.getElem_push]
  · exact hA
  · exact hPp
  · exact hPm
  · exact hSg
  · exact htwo
  · exact hσ
  · exact hnσ
  · intro c hc
    have hlt : c.buf < st.store.size := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl <;> assumption
    have h1 := hcells c (by simp only [List.mem_cons] at hc ⊢; tauto)
    refine ⟨fun h => h1 (by simp [EighArenas.handles, h]),
      fun h => h1 (by simp [EighArenas.handles, h]), ?_, ?_⟩ <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] <;> omega
  · exact hsq

/-- A split succeeds under the standard model at $u$ with every value in range and $u(p) < 1$,
with an exact literal $2$, if the kernels are routines on pairs and the arenas are allocated
(hypotheses on the inputs as `NLAlib.holds_of_exec_eighSplitBlock`). No printed source.
(The stored $\sqrt{1/2}$ is read from the cell `sq`, which `NLAlib.eighProg` fills once; design
note §8, the hoist of $\sqrt{1/2}$.) -/
theorem exists_exec_eighSplitBlock {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hlit : IsExactIntLit dec I.sem 2) (p : P)
    (hu : u p < 1) (n d lo k kp : ℕ) (hk : lo + k ≤ n) (hkp : 0 < kp) (hkpk : kp < k)
    (H : EighArenas) {Sg Pp Pm : ℕ} {two sg nsg sq : Cell ℕ ℕ} {σ : K} {st : St P K C}
    {A : Matrix (Fin k) (Fin k) (K × K)} {Ppm Pmm : Matrix (Fin k) (Fin k) (K × K)}
    {D : ℕ} (hd : d < D) (hH : H.Shaped st.store p n D) (hbufs : (H.handles ++ [Sg, Pp, Pm]).Nodup)
    (hA : pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hPp : pairLayout.Holds st.store p Pp 0 Ppm) (hPm : pairLayout.Holds st.store p Pm 0 Pmm)
    (hSg : ∀ w < 4 * (n * n), st.store.read p Sg w = some (I.tape .gaussian (4 * (n * n) * d + w)))
    (htwo : st.store.read p two.buf two.idx.eval = I.sem.lit p ((2 : ℕ) : ℚ))
    (hσ : st.store.read p sg.buf sg.idx.eval = some σ)
    (hnσ : st.store.read p nsg.buf nsg.idx.eval = some ((eighTapeMachine I p mmR qrR).neg σ))
    (hcells : ∀ c ∈ [two, sg, nsg, sq], c.buf ∉ H.handles ++ [Sg, Pp, Pm])
    (hsq : st.store.read p sq.buf sq.idx.eval = some (I.sem.sqrtHalf p)) :
    ∃ st', exec I (eighSplitBlock p mm qr (.const n) (.const d) (.const lo) (.const k) (.const kp)
      Sg Pp Pm H.Ma H.Qa H.Sz H.Kd H.Kp two sg nsg sq).run st = some st' := by
  exact exists_exec_eighSplitBlock_ex hmm hqr hsem hlit p hu n d lo k kp hk hkp hkpk (.const kp)
      rfl H
    hd hH hbufs
    hA hPp hPm (fun w hw => ⟨_, hSg w hw⟩) htwo hσ hnσ hcells hsq

end NLAlib
