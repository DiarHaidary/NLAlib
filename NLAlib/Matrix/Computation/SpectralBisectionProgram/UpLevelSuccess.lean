/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SpectralBisectionProgram.UpLevel

/-!
# The upward level of the spectral bisection program succeeds

Under the standard model with every value in range, one level of the upward pass of
`NLAlib.eighProg` (`NLAlib.eighUpLevel`) succeeds from arenas that hold the outputs of the depth
below and the records of its depth.

## Main results

* `NLAlib.exists_exec_eighUpLevel`: the level succeeds.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}

omit [AddMonoid C] in
/-- A product kernel call on held matrices succeeds when the output block fits. -/
private theorem exists_kcallStore_of_holds {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (p : P) {l m n : ℕ} {a b c : ℕ × ℕ} {s : Store P K} {A : Matrix (Fin l) (Fin m) (K × K)}
    {B : Matrix (Fin m) (Fin n) (K × K)} (hA : pairLayout.Holds s p a.1 a.2 A)
    (hB : pairLayout.Holds s p b.1 b.2 B)
    (hca : blockDisjoint (c.1, c.2, n * l * 2) (a.1, a.2, m * l * 2) = true)
    (hcb : blockDisjoint (c.1, c.2, n * l * 2) (b.1, b.2, n * m * 2) = true)
    {len : ℕ} (hc : s.shape[c.1]? = some (p, len)) (hlen : c.2 + n * l * 2 ≤ len) :
    ∃ s', I.kcallStore mm p [l, m, n] [a, b] [c] s = some s' := by
  rw [hmm.kcallStore_eq p ((EntryLayout.holds_iff_readBlock_eq_some pairLayout s p _ _ A).mp hA)
    ((EntryLayout.holds_iff_readBlock_eq_some pairLayout s p _ _ B).mp hB) hca hcb]
  exact Store.exists_writeBlock_eq_some_of_getElem?_shape fun i hi => ⟨len, hc, by
    rw [EntryLayout.size_toArray] at hi
    change i < n * l * 2 at hi
    omega⟩

omit [Inhabited K] in
/-- A loop of binary operations `Y[f w] ← Y[g w] ∘ c` succeeds when the written cells fit, the
read cells are initialised and never written, and the operation always succeeds. -/
private theorem exists_exec_loop_bin {p : P} {op : BinOp} {m : IExp ℕ} {Y : ℕ} {c : Cell ℕ ℕ}
    {f g : ℕ → IExp ℕ} {st : St P K C} {len : ℕ} (hYc : c.buf ≠ Y)
    (hfg : ∀ w < m.eval, ∀ w' < m.eval, (f w).eval ≠ (g w').eval)
    (hY : st.store.shape[Y]? = some (p, len)) (hf : ∀ w < m.eval, (f w).eval < len)
    (hg : ∀ w < m.eval, ∃ x, st.store.read p Y (g w).eval = some x)
    (hc : ∃ z, st.store.read p c.buf c.idx.eval = some z)
    (hop : ∀ x z, ∃ v, I.sem.bin p op x z = some v) :
    ∃ st', exec I (.loop m fun w => .seq (.instr (.bin p op ⟨Y, f w⟩ ⟨Y, g w⟩ c)) .skip) st =
      some st' := by
  refine (exists_exec_loop_eq_some_of_forall (I := I)
    (fun w s => s.store.shape = st.store.shape ∧
      ∀ q b i, (b ≠ Y ∨ ∀ w' < w, (f w').eval ≠ i) → s.store.read q b i = st.store.read q b i)
    ⟨rfl, fun _ _ _ _ => rfl⟩ ?_).imp fun _ h => h.1
  rintro w hw s ⟨hsh, hrd⟩
  obtain ⟨x, hx⟩ := hg w hw
  obtain ⟨z, hz⟩ := hc
  obtain ⟨v, hv⟩ := hop x z
  obtain ⟨s', hs'⟩ := Store.exists_write_eq_some_of_getElem?_shape (s := s.store) v
    (hsh ▸ hY) (hf w hw)
  refine ⟨_, (exec_seq_instr_bin I (x := ⟨Y, g w⟩) (y := c)
    ((hrd p _ _ (Or.inr fun w' hw' => hfg w' (by omega) w hw)).trans hx)
    ((hrd p _ _ (Or.inl hYc)).trans hz) hv hs').trans (exec_skip I _), ?_, fun q b i hb => ?_⟩
  · exact (Store.shape_of_write_eq_some hs').trans hsh
  · rw [Store.read_of_write_eq_some_of_ne hs' ?_]
    · exact hrd q b i (hb.imp_right fun h w' hw' => h w' (by omega))
    · exact hb.imp_right fun h => (h w (Nat.lt_succ_self w)).symm


omit [Inhabited K] in
/-- The branch of a one-child node in the upward pass (`NLAlib.eighUpShift`) succeeds. -/
private theorem exists_exec_eighUpShift (p : P) (n d D lo k : ℕ) (hd : d < D) (H : EighArenas)
    (tc : Cell ℕ ℕ) {s : St P K C} (hk : lo + k ≤ n) (hUE : H.Ua ≠ H.Ea) (htc : tc.buf ≠ H.Ea)
    (htcU : tc.buf ≠ H.Ua) {U : Matrix (Fin k) (Fin k) (K × K)}
    (hUs : s.store.shape[H.Ua]? = some (p, 2 * (n * n) * (D + 1)))
    (hEs : s.store.shape[H.Ea]? = some (p, n * (D + 1)))
    (hU : pairLayout.Holds s.store p H.Ua (2 * (n * n) * (d + 1) + 2 * n * lo) U)
    (hE : ∀ i < k, ∃ x, s.store.read p H.Ea (n * (d + 1) + lo + i) = some x)
    (hσ : ∃ σ, s.store.read p tc.buf tc.idx.eval = some σ)
    (hop : ∀ x z, ∃ v, I.sem.bin p .add x z = some v) :
    ∃ s', exec I (eighUpShift (ι := ι) p n d lo k H tc).run s = some s' := by
  rw [eighUpShift, exec_run_bind I (b := zcopy (ι := ι) p (IExp.var k) (IExp.var k) H.Ua
    (eighBlockOff (IExp.const n) (IExp.const d + 1) (IExp.var lo)) H.Ua
    (eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo))) (fun _ => rfl), exec_zcopy_congr]
  have hkk : k * k ≤ n * n := Nat.mul_le_mul (by omega) (by omega)
  have hU' : pairLayout.Holds s.store p H.Ua
      (eighBlockOff (IExp.const n) (IExp.const d + 1) (IExp.var lo)).eval U := by
    simpa [eighBlockOff, Nat.mul_succ] using hU
  have hXY : blockDisjoint (H.Ua, (eighBlockOff (IExp.const n) (IExp.const d) (IExp.var lo)).eval,
      2 * (k * k)) (H.Ua, (eighBlockOff (IExp.const n) (IExp.const d + 1) (IExp.var lo)).eval,
      2 * (k * k)) = true :=
    blockDisjoint_iff.2 (Or.inr (Or.inl (by
      simp only [eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const,
        IExp.eval_var, IExp.eval_ofNat]
      rw [Nat.mul_succ]; omega)))
  obtain ⟨s₁, hz⟩ := exists_exec_zcopy (I := I) p k k (st := s) hU' hXY ⟨_, hUs, by
    simp only [eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var,
      IExp.eval_ofNat]
    have : lo * n + k * n ≤ n * n := by nlinarith
    nlinarith⟩
  obtain ⟨-, hfr₁, hsh₁, -⟩ := holds_of_exec_zcopy p k k hU' hXY hz
  rw [IExp.eval_var, hz, Option.bind_some]
  change ∃ s', exec I (.seq (.loop _ _) .skip) _ = _
  simp only [exec_seq_skip]
  refine exists_exec_loop_bin htc ?_ (hsh₁ ▸ hEs) ?_ ?_ ?_ hop
  · intro w hw w' hw'
    simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var,
      IExp.eval_ofNat] at hw hw' ⊢
    rw [Nat.mul_succ]; omega
  · intro w hw
    simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var] at hw ⊢
    have := Nat.mul_le_mul_left n hd
    rw [Nat.mul_succ] at this ⊢; omega
  · intro w hw
    simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var,
      IExp.eval_ofNat] at hw ⊢
    rw [hfr₁ p _ _ (blockDisjoint_iff.2 (Or.inl (Ne.symm hUE)))]
    obtain ⟨x, hx⟩ := hE w hw
    exact ⟨x, by rw [← hx, Nat.mul_succ]⟩
  · obtain ⟨σ, hσ⟩ := hσ
    exact ⟨σ, by rw [hfr₁ p _ _ (blockDisjoint_iff.2 (Or.inl htcU))]; exact hσ⟩

omit [AddMonoid C] in
/-- The two kernel calls of the split branch (`NLAlib.eighUpSplit`) succeed, keep the shape and
every cell outside the output arena. -/
private theorem exists_kcallStore_eighUpSplit {mm : ι}
    (hmm : IsMatMulKernel I mm pairLayout mmR) (p : P) (n d D lo k kp : ℕ) (hd : d < D)
    (H : EighArenas) {s : Store P K} (hk : lo + k ≤ n) (hkp : kp < k) (hUQ : H.Ua ≠ H.Qa)
    {Qp : Matrix (Fin k) (Fin kp) (K × K)} {Qm : Matrix (Fin k) (Fin (k - kp)) (K × K)}
    {Up : Matrix (Fin kp) (Fin kp) (K × K)} {Um : Matrix (Fin (k - kp)) (Fin (k - kp)) (K × K)}
    (hUs : s.shape[H.Ua]? = some (p, 2 * (n * n) * (D + 1)))
    (hQp : pairLayout.Holds s p H.Qa (2 * (n * n) * d + 2 * n * lo) Qp)
    (hQm : pairLayout.Holds s p H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (k * kp)) Qm)
    (hUp : pairLayout.Holds s p H.Ua (2 * (n * n) * (d + 1) + 2 * n * lo) Up)
    (hUm : pairLayout.Holds s p H.Ua (2 * (n * n) * (d + 1) + 2 * n * (lo + kp)) Um) :
    ∃ u₁ u₂, I.kcallStore mm p [k, kp, kp] [(H.Qa, 2 * (n * n) * d + 2 * n * lo),
        (H.Ua, 2 * (n * n) * (d + 1) + 2 * n * lo)] [(H.Ua, 2 * (n * n) * d + 2 * n * lo)] s =
        some u₁ ∧
      I.kcallStore mm p [k, k - kp, k - kp]
        [(H.Qa, 2 * (n * n) * d + 2 * n * lo + 2 * (k * kp)),
          (H.Ua, 2 * (n * n) * (d + 1) + 2 * n * (lo + kp))]
        [(H.Ua, 2 * (n * n) * d + 2 * n * lo + 2 * (k * kp))] u₁ = some u₂ ∧
      u₂.shape = s.shape ∧ ∀ q b i, b ≠ H.Ua → u₂.read q b i = s.read q b i := by
  have hkk : k * k ≤ n * n := Nat.mul_le_mul (by omega) (by omega)
  have hkpk : k * kp ≤ k * k := Nat.mul_le_mul_left k hkp.le
  have hsplit : k * kp + k * (k - kp) = k * k := by
    rw [← Nat.mul_add, Nat.add_sub_of_le hkp.le]
  have hlok : lo * n + k * n ≤ n * n := by nlinarith
  have hc1 : (k - kp) * k = k * (k - kp) := Nat.mul_comm _ _
  have hc2 : kp * k = k * kp := Nat.mul_comm _ _
  have hnD := Nat.mul_le_mul_left n hd
  rw [Nat.mul_succ] at hnD
  obtain ⟨u₁, hu₁⟩ := exists_kcallStore_of_holds hmm p (l := k) (m := kp) (n := kp)
    (a := (H.Qa, 2 * (n * n) * d + 2 * n * lo))
    (b := (H.Ua, 2 * (n * n) * (d + 1) + 2 * n * lo))
    (c := (H.Ua, 2 * (n * n) * d + 2 * n * lo)) hQp hUp (blockDisjoint_iff.2 (Or.inl hUQ))
    (blockDisjoint_iff.2 (Or.inr (Or.inl (by dsimp only; rw [Nat.mul_succ]; nlinarith)))) hUs
    (by dsimp only; rw [Nat.mul_succ]; nlinarith)
  obtain ⟨-, hfr₁⟩ := hmm.holds_of_kcallStore_eq_some pairLayout.get_put p hQp hUp
    (blockDisjoint_iff.2 (Or.inl hUQ)) (blockDisjoint_iff.2 (Or.inr (Or.inl (by
      simp only [pairLayout]; rw [Nat.mul_succ]; nlinarith)))) hu₁
  have hQm₁ := hQm.of_forall_read_eq fun i _ _ =>
    hfr₁ p _ i (blockDisjoint_iff.2 (Or.inl (Ne.symm hUQ)))
  have hUm₁ := hUm.of_forall_read_eq fun i hi _ => hfr₁ p _ i (blockDisjoint_iff.2
    (Or.inr (Or.inr (by simp only [pairLayout]; rw [Nat.mul_succ]; nlinarith))))
  have hsh₁ := Interp.shape_of_kcallStore_eq_some hu₁
  obtain ⟨u₂, hu₂⟩ := exists_kcallStore_of_holds hmm p (l := k) (m := k - kp) (n := k - kp)
    (a := (H.Qa, 2 * (n * n) * d + 2 * n * lo + 2 * (k * kp)))
    (b := (H.Ua, 2 * (n * n) * (d + 1) + 2 * n * (lo + kp)))
    (c := (H.Ua, 2 * (n * n) * d + 2 * n * lo + 2 * (k * kp))) hQm₁ hUm₁
    (blockDisjoint_iff.2 (Or.inl hUQ)) (blockDisjoint_iff.2 (Or.inr (Or.inl (by
      dsimp only; rw [Nat.mul_succ]; nlinarith)))) (hsh₁ ▸ hUs)
    (by dsimp only; rw [Nat.mul_succ]; nlinarith)
  obtain ⟨-, hfr₂⟩ := hmm.holds_of_kcallStore_eq_some pairLayout.get_put p hQm₁ hUm₁
    (blockDisjoint_iff.2 (Or.inl hUQ)) (blockDisjoint_iff.2 (Or.inr (Or.inl (by
      simp only [pairLayout]; rw [Nat.mul_succ]; nlinarith)))) hu₂
  refine ⟨u₁, u₂, hu₁, hu₂, (Interp.shape_of_kcallStore_eq_some hu₂).trans hsh₁,
    fun q b i hb => ?_⟩
  rw [hfr₂ q b i (blockDisjoint_iff.2 (Or.inl hb)), hfr₁ q b i (blockDisjoint_iff.2 (Or.inl hb))]

/-- The branch of a split in the upward pass (`NLAlib.eighUpSplit`) succeeds. -/
private theorem exists_exec_eighUpSplit {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (p : P) (n d D lo k kp t : ℕ) (hd : d < D) (H : EighArenas) {s : St P K C} (hk : lo + k ≤ n)
    (hkp : kp < k) (hUE : H.Ua ≠ H.Ea) (hUQ : H.Ua ≠ H.Qa) (htE : t ≠ H.Ea) (htU : t ≠ H.Ua)
    {Qp : Matrix (Fin k) (Fin kp) (K × K)} {Qm : Matrix (Fin k) (Fin (k - kp)) (K × K)}
    {Up : Matrix (Fin kp) (Fin kp) (K × K)} {Um : Matrix (Fin (k - kp)) (Fin (k - kp)) (K × K)}
    (hUs : s.store.shape[H.Ua]? = some (p, 2 * (n * n) * (D + 1)))
    (hEs : s.store.shape[H.Ea]? = some (p, n * (D + 1)))
    (hQp : pairLayout.Holds s.store p H.Qa (2 * (n * n) * d + 2 * n * lo) Qp)
    (hQm : pairLayout.Holds s.store p H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (k * kp)) Qm)
    (hUp : pairLayout.Holds s.store p H.Ua (2 * (n * n) * (d + 1) + 2 * n * lo) Up)
    (hUm : pairLayout.Holds s.store p H.Ua (2 * (n * n) * (d + 1) + 2 * n * (lo + kp)) Um)
    (hEp : ∀ j < kp, ∃ x, s.store.read p H.Ea (n * (d + 1) + lo + j) = some x)
    (hEm : ∀ j < k - kp, ∃ x, s.store.read p H.Ea (n * (d + 1) + (lo + kp) + j) = some x)
    (hσ : ∃ σ, s.store.read p t 0 = some σ)
    (hadd : ∀ x z, ∃ v, I.sem.bin p .add x z = some v)
    (hsub : ∀ x z, ∃ v, I.sem.bin p .sub x z = some v) :
    ∃ s', exec I (eighUpSplit p mm n d lo k kp t H).run s = some s' := by
  change ∃ s', exec I (.seq (.kcall _ _ _ _ _) (.seq (.kcall _ _ _ _ _)
    (.seq (.loop _ _) (.seq (.loop _ _) .skip)))) s = some s'
  obtain ⟨u₁, u₂, hu₁, hu₂, hsh₂, hfrK⟩ := exists_kcallStore_eighUpSplit hmm p n d D lo k kp hd H
    hk hkp hUQ hUs hQp hQm hUp hUm
  rw [exec_seq, exec_kcall]
  simp only [List.map_cons, List.map_nil, eighBlockOff, IExp.eval_add, IExp.eval_mul,
    IExp.eval_const, IExp.eval_var, IExp.eval_ofNat]
  rw [hu₁, Option.map_some, Option.bind_some, exec_seq, exec_kcall]
  simp only [List.map_cons, List.map_nil, IExp.eval_add, IExp.eval_mul,
    IExp.eval_const, IExp.eval_var, IExp.eval_ofNat, IExp.eval_sub]
  rw [hu₂, Option.map_some, Option.bind_some]
  have hrdE : ∀ i, u₂.read p H.Ea i = s.store.read p H.Ea i := fun i => hfrK p _ i hUE.symm
  have hrdt : u₂.read p t 0 = s.store.read p t 0 := hfrK p _ _ htU
  have hEs₂ : u₂.shape[H.Ea]? = some (p, n * (D + 1)) := by rw [hsh₂]; exact hEs
  rw [exec_seq]
  obtain ⟨s₃, h₃⟩ := exists_exec_loop_bin (I := I) (c := ⟨t, 0⟩) (Y := H.Ea)
    (st := { s with
      store := u₂
      cnt := s.cnt + I.charge (.kcall p mm [k, kp, kp]) +
        I.charge (.kcall p mm [k, k - kp, k - kp]) })
    (f := fun j => eighSlotOff (IExp.const n) (IExp.const d) (IExp.var lo) + IExp.var j)
    (g := fun j => eighSlotOff (IExp.const n) (IExp.const d + 1) (IExp.var lo) + IExp.var j)
    (m := IExp.var kp) htE (by
      intro w hw w' hw'
      simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var,
        IExp.eval_ofNat] at hw hw' ⊢
      rw [Nat.mul_succ]; omega) hEs₂ (by
      intro w hw
      simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const,
        IExp.eval_var] at hw ⊢
      have := Nat.mul_le_mul_left n hd
      rw [Nat.mul_succ] at this ⊢; omega) (by
      intro w hw
      simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var,
        IExp.eval_ofNat] at hw ⊢
      rw [hrdE]
      obtain ⟨x, hx⟩ := hEp w hw
      exact ⟨x, by rw [← hx, Nat.mul_succ]⟩) (by
      obtain ⟨σ, hσ⟩ := hσ
      exact ⟨σ, by rw [IExp.eval_zero, hrdt]; exact hσ⟩) hadd
  obtain ⟨hsh₃, -, -, hfr₃⟩ := shape_and_read_of_exec_loop_bin htE (by
      intro w hw w' hw'
      simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var,
        IExp.eval_ofNat] at hw hw' ⊢
      rw [Nat.mul_succ]; omega) (by
    intro w hw w' hw' e
    simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var] at e
    omega) h₃
  erw [h₃]
  rw [Option.bind_some, exec_seq_skip]
  refine exists_exec_loop_bin htE ?_ (hsh₃ ▸ hEs₂) ?_ ?_ ?_ hsub
  · intro w hw w' hw'
    simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var,
      IExp.eval_ofNat, IExp.eval_sub] at hw hw' ⊢
    rw [Nat.mul_succ]; omega
  · intro w hw
    simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var,
      IExp.eval_sub] at hw ⊢
    have := Nat.mul_le_mul_left n hd
    rw [Nat.mul_succ] at this ⊢; omega
  · intro w hw
    simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var,
      IExp.eval_ofNat, IExp.eval_sub] at hw ⊢
    rw [hfr₃ p _ _ (Or.inr fun w' hw' => by
      simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const,
        IExp.eval_var] at hw' ⊢
      rw [Nat.mul_succ]; omega), hrdE]
    obtain ⟨x, hx⟩ := hEm w hw
    exact ⟨x, by rw [← hx, Nat.mul_succ]; congr 1; omega⟩
  · obtain ⟨σ, hσ⟩ := hσ
    exact ⟨σ, by rw [hfr₃ p _ _ (Or.inl htE), IExp.eval_zero, hrdt]; exact hσ⟩

/-- One node of the upward pass (`NLAlib.eighUpNode`) succeeds, under the hypotheses of its run
(`NLAlib.holds_of_exec_eighUpSlot`) and with the output and eigenvalue arenas allocated. -/
private theorem exists_exec_eighUpNode {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (p : P) (n ℓ₀ F d D : ℕ) (hn : 1 ≤ n) (hd : d < D) (H : EighArenas) (t : ℕ)
    {s₀ s₁ : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K} {a : List Bool}
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
    (hUs : s₁.store.shape[H.Ua]? = some (p, 2 * (n * n) * (D + 1)))
    (hEs : s₁.store.shape[H.Ea]? = some (p, n * (D + 1)))
    (hadd : ∀ x z, ∃ v, I.sem.bin p .add x z = some v)
    (hsub : ∀ x z, ∃ v, I.sem.bin p .sub x z = some v) :
    ∃ s₂, exec I (eighUpNode p mm n d lo y.k t H).run s₁ = some s₂ := by
  set M := eighTapeMachine I p mmR qrR with hM
  obtain ⟨hk1, hkn⟩ := eighLoc_bounds hn hay
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
  cases hs : eighStep M n F R₀ β y.A y.R y.ε y.ℓ (eighTapeSample n d lo) with
  | leaf U e =>
    rw [hs] at hr
    exact ⟨_, exec_eighUpNode_of_readsIdx_one (readsIdx_of_read_eq (hRo p _ _ hKdU hKdE) hr.1)⟩
  | shift b A' σ' =>
    rw [hs] at hr
    rw [exec_eighUpNode_of_readsIdx_shift (readsIdx_of_read_eq (hRo p _ _ hKdU hKdE) hr)]
    have hch : eighLoc M n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ (a ++ [b]) = some (lo,
        ⟨y.k, A', (eighNextParams M y.R y.ε y.ℓ).1, (eighNextParams M y.R y.ε y.ℓ).2,
          y.ℓ + 1⟩) := by
      rw [eighLoc_append_singleton, hay]
      simp [eighLoc, ha, hs]
    obtain ⟨hUc, hEc⟩ := hout (a ++ [b]) lo _ (by simp [ha]) hch
    refine exists_exec_eighUpShift p n d D lo y.k hd H _ hkn hUE htE htU hUs hEs
      (hUc.of_forall_read_eq fun i hi _ => hRU1 p i (by omega))
      (fun i hi => ⟨_, (hRE1 p _ (by omega)).trans (hEc ⟨i, hi⟩)⟩) ?_ hadd
    cases b
    · exact ⟨_, (hRo p _ _ htU htE).trans ht1⟩
    · exact ⟨_, (hRo p _ _ htU htE).trans ht0⟩
  | split kp hkp Qp Qm Ap Am σ' =>
    rw [hs] at hr
    obtain ⟨-, -, hkpk⟩ := eq_div_and_pos_and_lt_of_eighStep_eq_split hs
    obtain ⟨hkd, hkpr, hQp, hQm⟩ := hr
    rw [exec_eighUpNode_of_readsIdx_four (readsIdx_of_read_eq (hRo p _ _ hKdU hKdE) hkd)
      (readsIdx_of_read_eq (hRo p _ _ hKpU hKpE) hkpr) hkp]
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
    exact exists_exec_eighUpSplit hmm p n d D lo y.k kp t hd H hkn hkpk hUE hUQ htE htU hUs hEs
      (hQp.of_forall_read_eq fun i _ _ => hRo p _ i (Ne.symm hUQ) hQE)
      (hQm.of_forall_read_eq fun i _ _ => hRo p _ i (Ne.symm hUQ) hQE)
      (hUp.of_forall_read_eq fun i hi _ => hRU1 p i (by omega))
      (hUm.of_forall_read_eq fun i hi _ => hRU1 p i (by nlinarith))
      (fun j hj => ⟨_, (hRE1 p _ (by omega)).trans (hEp ⟨j, hj⟩)⟩)
      (fun j hj => ⟨_, (hRE1 p _ (by omega)).trans (hEm ⟨j, hj⟩)⟩)
      ⟨_, (hRo p _ _ htU htE).trans ht0⟩ hadd hsub

/-- One slot of the upward pass (`NLAlib.eighUpSlot`) succeeds, under the hypotheses of its run
(`NLAlib.holds_of_exec_eighUpSlot`) and with the output and eigenvalue arenas allocated. -/
private theorem exists_exec_eighUpSlot {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (p : P) (n ℓ₀ F d D : ℕ) (hd : d < D) (H : EighArenas) (t : ℕ) {s₀ s₁ : St P K C}
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
    (hfr : ∀ q b i, (¬ ((b = H.Ua ∨ b = H.Ea) ∧ H.LevelCell n d b i) ∨
        ∀ (a : List Bool) (lo' : ℕ) (y : EighNode K), a.length = d →
          eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a =
            some (lo', y) → lo' < lo →
          (b ≠ H.Ua ∨ i < 2 * (n * n) * d + 2 * n * lo' ∨
            2 * (n * n) * d + 2 * n * lo' + 2 * (y.k * y.k) ≤ i) ∧
          (b ≠ H.Ea ∨ i < n * d + lo' ∨ n * d + lo' + y.k ≤ i)) →
        s₁.store.read q b i = s₀.store.read q b i)
    (hUs : s₁.store.shape[H.Ua]? = some (p, 2 * (n * n) * (D + 1)))
    (hEs : s₁.store.shape[H.Ea]? = some (p, n * (D + 1)))
    (hadd : ∀ x z, ∃ v, I.sem.bin p .add x z = some v)
    (hsub : ∀ x z, ∃ v, I.sem.bin p .sub x z = some v) :
    ∃ s₂, exec I (eighUpSlot p mm n d lo t H).run s₁ = some s₂ := by
  obtain ⟨-, -, -, -, -, -, -, hSzU, hSzE, -⟩ := H.ua_ne_ea_and_of_nodup hnd
  have hSz : ∀ i, s₁.store.read p H.Sz i = s₀.store.read p H.Sz i := fun i =>
    hfr p _ i (Or.inl fun h => h.1.elim hSzU hSzE)
  by_cases hy : ∃ (a : List Bool) (y : EighNode K), a.length = d ∧
      eighLoc (eighTapeMachine I p mmR qrR) n F R₀ β 0 0 ⟨n, A, R₀, ε, ℓ₀⟩ a = some (lo, y)
  swap
  · push Not at hy
    exact ⟨_, exec_eighUpSlot_of_readsIdx_zero (readsIdx_of_read_eq
      (hSz _) (hlev.2.1 lo hlo fun a y ha => hy a y ha))⟩
  obtain ⟨a, y, ha, hay⟩ := hy
  obtain ⟨hk1, hb⟩ := eighLoc_bounds (by omega : 1 ≤ n) hay
  rw [exec_eighUpSlot_of_readsIdx (readsIdx_of_read_eq (hSz _) (hlev.1 a lo y ha hay).1) hk1
    (by omega)]
  refine exists_exec_eighUpNode hmm p n ℓ₀ F d D (by omega) hd H t ha hay hnd htH ht0 ht1 hrec
    hout (fun q b i hb' => ?_) hUs hEs hadd hsub
  refine hfr q b i (hb'.imp_right fun ⟨hU', hE'⟩ a' lo' y' ha' hay' hlt => ?_)
  obtain ⟨h1, h2⟩ := add_le_and_mul_add_le_of_eighLoc_of_lt (by omega) ha ha' hay hay' hlt
  refine ⟨?_, ?_⟩
  · by_cases hbU : b = H.Ua
    · exact Or.inr (Or.inr (by have := hU' hbU; omega))
    · exact Or.inl hbU
  · by_cases hbE : b = H.Ea
    · exact Or.inr (Or.inr (by have := hE' hbE; omega))
    · exact Or.inl hbE

omit [Inhabited K] in
/-- An option that is `some` stays `some` under `Option.map`. -/
private theorem exists_map_eq_some {α β : Type} {o : Option α} (f : α → β)
    (h : ∃ a, o = some a) : ∃ b, o.map f = some b := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨f a, rfl⟩

/-- One level of the upward pass succeeds: if kernel `mm` of `I` is the routine `mmR` on interleaved
pairs, under a relative-error semantics `I.sem` (unit roundoff `u`, decoding `dec`) with every value
in range and exact integer literals up to $n + 4$, the run of `NLAlib.eighUpLevel` at depth $d < D$
succeeds from a state whose arenas `H` are allocated (`NLAlib.EighArenas.Shaped` at size $n$ and
budget $D$) and hold the nodes and records of depth $d$ and the outputs of depth $d + 1$, with the
stored $\mathrm{fl}(2)$ in the cell `two`. No printed source. -/
theorem exists_exec_eighUpLevel {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    {u : P → ℝ} {dec : P → K → ℝ} (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P)
    (n ℓ₀ F d D : ℕ) (hd : d < D) (hlit : IsExactIntLit dec I.sem (n + 4))
    (H : EighArenas) {two : Cell ℕ ℕ} {st : St P K C}
    {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hH : H.Shaped st.store p n D)
    (htwov : st.store.read p two.buf two.idx.eval = I.sem.lit p ((2 : ℕ) : ℚ))
    (hlev : H.LevelHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d)
    (hrec : H.RecordHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d)
    (hout : H.OutHolds st.store p (eighTapeMachine I p mmR qrR) n F D R₀ β ⟨n, A, R₀, ε, ℓ₀⟩
      (d + 1)) :
    ∃ st', exec I (eighUpLevel p mm (.const n) (.const d) H.Lv H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp
      two).run st = some st' := by
  have hsz : ∀ {b : ℕ} {x : P × ℕ}, st.store.shape[b]? = some x → b < st.store.size :=
    fun h => by simpa [Store.size_shape] using (Array.getElem?_eq_some_iff.mp h).1
  obtain ⟨hnd, -, hUa, -, hEa, -⟩ := id hH
  have hltH : ∀ b ∈ H.handles, b < st.store.size := fun b hb => hH.lt_size_of_mem hb
  have htH : st.store.size ∉ H.handles := fun hm => absurd (hltH _ hm) (lt_irrefl _)
  obtain ⟨z2, hz2, hdz2⟩ := hlit p 2 (by omega)
  have htwo' : st.store.read p two.buf two.idx.eval = some z2 := htwov.trans hz2
  have ltwo := Store.lt_size_of_read_eq_some htwo'
  have hadd : ∀ x z, ∃ v, I.sem.bin p .add x z = some v :=
    fun x z => hsem.bin_ok p .add x z trivial (fun h => nomatch h) trivial
  have hsub : ∀ x z, ∃ v, I.sem.bin p .sub x z = some v :=
    fun x z => hsem.bin_ok p .sub x z trivial (fun h => nomatch h) trivial
  set M := eighTapeMachine I p mmR qrR with hM
  set t := st.store.size with ht
  change ∃ st', exec I (.seq (.alloc p _ _) .skip) st = some st'
  rw [exec_seq_skip, exec_alloc]
  refine exists_map_eq_some _ ?_
  change ∃ s₁, exec I (.seq (.instr _) (.seq (.instr _) (.seq (.loop _ _) .skip))) _ = some s₁
  have hP : ∀ {q : P} {b i : ℕ}, b < t →
      Store.read (st.store.push (p, Array.replicate (2 : IExp ℕ).eval none)) q b i =
        st.store.read q b i := fun hb => Store.read_push_of_lt hb
  have hPs : (Store.shape (st.store.push (p, Array.replicate (2 : IExp ℕ).eval none)))[t]? =
      some (p, 2) := Store.getElem?_shape_push_size _ _ _
  have hxR : Store.read (st.store.push (p, Array.replicate (2 : IExp ℕ).eval none)) p H.Lv
      (2 * IExp.const d : IExp ℕ).eval = some (eighLevelParams M R₀ ε ℓ₀ d).1 :=
    (hP (hltH _ (by simp [EighArenas.handles]))).trans hlev.2.2.1
  obtain ⟨v0, hv0⟩ := hsem.bin_ok p .div (eighLevelParams M R₀ ε ℓ₀ d).1 z2 trivial
    (fun _ => by rw [hdz2]; norm_num) trivial
  obtain ⟨wa, hwa⟩ := Store.exists_write_eq_some_of_getElem?_shape (p := p) (b := t) (i := 0) v0
    hPs (by norm_num)
  obtain ⟨v1, hv1, -⟩ := hsem.neg p v0
  obtain ⟨wb, hwb⟩ := Store.exists_write_eq_some_of_getElem?_shape (p := p) (b := t) (i := 1) v1
    ((Store.shape_of_write_eq_some hwa).symm ▸ hPs) (by norm_num)
  rw [exec_seq_instr_bin I (x := ⟨H.Lv, 2 * IExp.const d⟩) (y := two) hxR
    ((hP ltwo).trans htwo') hv0 hwa]
  rw [exec_seq_instr_un I (x := ⟨t, 0⟩) (Store.read_of_write_eq_some hwa) hv1 hwb]
  rw [exec_seq_skip]
  have hrd₀ : ∀ q b i, b ∈ H.handles → wb.read q b i = st.store.read q b i := fun q b i hb => by
    rw [Store.read_of_write_eq_some_of_ne hwb (Or.inl (Nat.ne_of_lt (hltH b hb))),
      Store.read_of_write_eq_some_of_ne hwa (Or.inl (Nat.ne_of_lt (hltH b hb))), hP (hltH b hb)]
  obtain ⟨ht0, ht1⟩ := read_eq_div_and_read_eq_neg_of_write (mmR := mmR) (qrR := qrR) hz2 hv0
    hv1 hwa hwb
  have hshw : ∀ {b}, b < t → wb.shape[b]? = st.store.shape[b]? := fun hb => by
    rw [Store.shape_of_write_eq_some hwb, Store.shape_of_write_eq_some hwa,
      Store.getElem?_shape_push_of_lt _ hb]
  have hUs : wb.shape[H.Ua]? = some (p, 2 * (n * n) * (D + 1)) := (hshw (hsz hUa)).trans hUa
  have hEs : wb.shape[H.Ea]? = some (p, n * (D + 1)) := (hshw (hsz hEa)).trans hEa
  have hT := fun d' => EighArenas.holds_of_forall_read_eq (H := H) (p := p) (M := M) (n := n)
    (F := F) (ℓ₀ := ℓ₀) (D := D) (d := d') (R₀ := R₀) (β := β) (root := ⟨n, A, R₀, ε, ℓ₀⟩)
    (sem := I.sem) hrd₀
  have hT1 := (hT d).1 hlev
  have hT2 := (hT d).2.1 hrec
  have hT3 := (hT (d + 1)).2.2 hout
  refine ⟨_, (exists_exec_loop_eq_some_of_forall (I := I) (n := .const n)
    (fun lo (s : St P K C) =>
      H.UpSlotsDone s { st with store := wb } p M n F D R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ d lo)
    ?_ ?_).choose_spec.1⟩
  · exact ⟨rfl, rfl, fun _ _ _ _ => rfl, fun _ _ _ _ _ h => absurd h (Nat.not_lt_zero _)⟩
  rintro lo hlo s ⟨hsh, hps, hfr, hdone⟩
  simp only [IExp.eval_const] at hlo
  obtain ⟨s', hs'⟩ := exists_exec_eighUpSlot hmm p n ℓ₀ F d D hd H t (s₀ := { st with store := wb })
    (s₁ := s) hlo hnd htH ht0 ht1 hT1 hT2 hT3 hfr (hsh ▸ hUs) (hsh ▸ hEs) hadd hsub
  exact ⟨s', hs', holds_of_exec_eighUpSlot hmm p n ℓ₀ F d D hd H t (s₀ := { st with store := wb })
    hlo hnd htH ht0 ht1 hT1 hT2 hT3 ⟨hsh, hps, hfr, hdone⟩ hs'⟩

end NLAlib
