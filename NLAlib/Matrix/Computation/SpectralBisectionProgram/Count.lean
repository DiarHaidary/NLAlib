/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.NewtonSchulzSignProgram
public import NLAlib.Matrix.Computation.SpectralBisectionProgram.CountTree

/-!
# The static count of the spectral bisection program

The counts of every successful run of the registered tree `NLAlib.eighProg.compiled` are bounded by
the static bound `NLAlib.eighCount`, the memory included: the scalar counts by the polynomial checks
of the tree, and the kernel counts by the tree of kernel calls.

## Main results

* `NLAlib.eighProg.cnt_le_of_exec_compiled`: the static bound.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}

/-! #### The kernel counts of a tree of kernel calls -/

/-- The static kernel count of a tree of kernel calls, as `NLAlib.Computation.FStmt.staticCost`
counts it. -/
private noncomputable def ep6_kc {P ι : Type} : {ni : ℕ} → ep6_KT P ι ni → (Fin ni → ℕ) →
    OpCount P ι
  | _, .skip, _ => 0
  | _, .seq a b, ρ => ep6_kc a ρ + ep6_kc b ρ
  | _, .loop n b, ρ =>
      ((List.range (n.evalIn ρ)).map fun i => ep6_kc b (Fin.snoc (α := fun _ => ℕ) ρ i)).sum
  | _, .rep n b, ρ => n.evalIn ρ • ep6_kc b ρ
  | _, .br a b, ρ => ep6_kc a ρ ⊔ ep6_kc b ρ
  | _, .bind n b, ρ => (List.range (n.evalIn ρ + 1)).foldr
      (fun k c => ep6_kc b (Fin.snoc (α := fun _ => ℕ) ρ k) ⊔ c) 0
  | _, .call o p d, ρ => Finsupp.single (.kcall p o (d.map (·.evalIn ρ))) 1

omit [DecidableEq P] in
private theorem ep6_foldr_zero (l : List ℕ) :
    l.foldr (fun _ c => (0 : OpCount P ι) ⊔ c) 0 = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp

omit [DecidableEq P] in
private theorem ep6_kc_sseq {ni : ℕ} (a b : ep6_KT P ι ni) (ρ : Fin ni → ℕ) :
    ep6_kc (ep6_sseq a b) ρ = ep6_kc a ρ + ep6_kc b ρ := by
  unfold ep6_sseq
  split <;> simp [ep6_kc]

omit [DecidableEq P] in
private theorem ep6_kc_sbr {ni : ℕ} (a b : ep6_KT P ι ni) (ρ : Fin ni → ℕ) :
    ep6_kc (ep6_sbr a b) ρ = ep6_kc a ρ ⊔ ep6_kc b ρ := by
  unfold ep6_sbr
  split <;> simp [ep6_kc]

omit [DecidableEq P] in
private theorem ep6_kc_sloop {ni : ℕ} (n : IExp (Fin ni)) (b : ep6_KT P ι (ni + 1))
    (ρ : Fin ni → ℕ) : ep6_kc (ep6_sloop n b) ρ = ep6_kc (.loop n b) ρ := by
  unfold ep6_sloop
  split <;> simp [ep6_kc]

omit [DecidableEq P] in
private theorem ep6_kc_srep {ni : ℕ} (n : IExp (Fin ni)) (b : ep6_KT P ι ni)
    (ρ : Fin ni → ℕ) : ep6_kc (ep6_srep n b) ρ = ep6_kc (.rep n b) ρ := by
  unfold ep6_srep
  split <;> simp [ep6_kc]

omit [DecidableEq P] in
private theorem ep6_kc_sbind {ni : ℕ} (n : IExp (Fin ni)) (b : ep6_KT P ι (ni + 1))
    (ρ : Fin ni → ℕ) : ep6_kc (ep6_sbind n b) ρ = ep6_kc (.bind n b) ρ := by
  unfold ep6_sbind
  split
  · simp only [ep6_kc]; exact (ep6_foldr_zero _).symm
  · rfl

omit [DecidableEq P] in
private theorem ep6_lsum_apply (l : List ℕ) (f : ℕ → OpCount P ι) (κ : OpKind P ι) :
    (l.map f).sum κ = (l.map fun i => f i κ).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

omit [DecidableEq P] in
private theorem ep6_supRange_count_eq {f : ℕ → StaticCost P ι} {g : ℕ → OpCount P ι} {m : ℕ}
    {κ : OpKind P ι} (h : ∀ k, (f k).count κ = g k κ) :
    (StaticCost.supRange m f).count κ = (List.range m).foldr (fun k c => g k ⊔ c) 0 κ := by
  unfold StaticCost.supRange
  induction List.range m with
  | nil => rfl
  | cons a l ih =>
    change ((f a).count ⊔ (l.foldr (fun k c => (f k).branch c) StaticCost.zero).count) κ =
      (g a ⊔ l.foldr (fun k c => g k ⊔ c) 0) κ
    rw [Finsupp.sup_apply, Finsupp.sup_apply, h, ih]

omit [DecidableEq P] in
private theorem ep6_single_zero {k κ : OpKind P ι} (h : ep6_cls k ≠ ep6_cls κ) :
    (Finsupp.single k 1 : OpCount P ι) κ = 0 := by
  classical
  rw [Finsupp.single_apply, if_neg]
  rintro rfl
  exact h rfl

omit [DecidableEq P] in
private theorem ep6_cls_instr (i : Instr P ℕ ℕ) : ep6_cls (i.kind (ι := ι)) ≠ 9 := by
  cases i <;> simp only [Instr.kind, ep6_cls] <;> first | decide | (split <;> decide)

/-- The kernel counts are those of the tree of kernel calls. -/
private theorem ep6_count_prune (w : P → ℕ) (κ : OpKind P ι) (h9 : ep6_cls κ = 9) :
    ∀ {nb ni : ℕ} (s : FStmt P ι nb ni) (ρ : Fin ni → ℕ),
      (s.staticCost (fun k => Finsupp.single k 1) w ρ).count κ = ep6_kc (ep6_prune s) ρ κ := by
  have hz : ∀ k : OpKind P ι, ep6_cls k ≠ 9 → (Finsupp.single k 1 : OpCount P ι) κ = 0 :=
    fun k hk => ep6_single_zero (h9 ▸ hk)
  intro nb ni s
  induction s with
  | skip => intro ρ; rfl
  | seq s t ihs iht =>
    intro ρ
    simp only [FStmt.staticCost, StaticCost.seq, Finsupp.add_apply, ep6_prune, ep6_kc_sseq, ihs,
      iht]
  | instr i =>
    intro ρ
    exact hz _ (ep6_cls_instr _)
  | apply o p d dOff s sOff cols =>
    intro ρ
    simp only [FStmt.staticCost, StaticCost.step, Finsupp.add_apply, Finsupp.smul_apply,
      smul_eq_mul, ep6_prune, ep6_kc, Finsupp.zero_apply]
    rw [hz _ (by simp [ep6_cls]), hz _ (by simp [ep6_cls])]
    simp
  | rom p d i =>
    intro ρ
    exact hz _ (by simp [ep6_cls])
  | alloc p len body ih =>
    intro ρ
    exact ih ρ
  | loop n body ih =>
    intro ρ
    simp only [FStmt.staticCost, StaticCost.sequence_count_apply, ep6_prune, ep6_kc_sloop,
      ep6_kc, ep6_lsum_apply, ih]
  | whileFuel fuel p c x y body ih =>
    intro ρ
    simp only [FStmt.staticCost, StaticCost.repetitions, StaticCost.seq, StaticCost.step,
      Finsupp.smul_apply, Finsupp.add_apply, smul_eq_mul, ep6_prune, ep6_kc_srep, ep6_kc, ih,
      hz (.cmp p) (by simp [ep6_cls]), zero_add]
  | ite p c x y t e iht ihe =>
    intro ρ
    simp only [FStmt.staticCost, StaticCost.branch, StaticCost.seq, StaticCost.step,
      Finsupp.add_apply, Finsupp.sup_apply, ep6_prune, ep6_kc_sbr, iht, ihe,
      hz (.cmp p) (by simp [ep6_cls]), zero_add]
  | named name args body ih =>
    intro ρ
    exact ih ρ
  | kcall o p dims ins outs =>
    intro ρ
    rfl
  | bindIdx p x bound body ih =>
    intro ρ
    simp only [FStmt.staticCost, StaticCost.seq, StaticCost.step, Finsupp.add_apply,
      hz (.toNat p) (by simp [ep6_cls]), zero_add, ep6_prune, ep6_kc_sbind, ep6_kc]
    exact ep6_supRange_count_eq fun k => ih _

/-! #### The polynomial checks -/

private theorem ep6_ev_le_mul (N L F M : ℕ) (p : ep6_Poly)
    (h : ∀ e ∈ p, N ^ e.2.1 * L ^ e.2.2.1 * F ^ e.2.2.2 ≤ M) :
    ep6_ev N L F p ≤ (p.map (·.1)).sum * M := by
  induction p with
  | nil => simp [ep6_ev]
  | cons a p ih =>
    have ih' := ih fun e he => h e (List.mem_cons_of_mem a he)
    simp only [ep6_ev, List.map_cons, List.sum_cons, add_mul] at ih' ⊢
    exact Nat.add_le_add (Nat.mul_le_mul_left _ (h a List.mem_cons_self)) ih'

private theorem ep6_pow_le_succ (L b : ℕ) (hb : b ≤ 1) : L ^ b ≤ L + 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with rfl | rfl <;> simp

private theorem ep6_okS_le (N L F : ℕ) (p : ep6_Poly) (h : ep6_okS p = true) :
    ep6_ev N L F p ≤ 1024 * (F + 2) * (L + 2) * (N + 1) ^ 3 := by
  simp only [ep6_okS, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨hall, hsum⟩ := h
  refine (ep6_ev_le_mul N L F ((N + 1) ^ 3 * (L + 1) * (F + 1)) p fun e he => ?_).trans ?_
  · obtain ⟨⟨ha, hb⟩, hc⟩ := hall e he
    refine Nat.mul_le_mul (Nat.mul_le_mul ?_ (ep6_pow_le_succ L _ hb)) (ep6_pow_le_succ F _ hc)
    exact (Nat.pow_le_pow_left (Nat.le_succ N) _).trans (Nat.pow_le_pow_right (by omega) ha)
  · calc (p.map (·.1)).sum * ((N + 1) ^ 3 * (L + 1) * (F + 1))
        ≤ 1024 * ((N + 1) ^ 3 * (L + 1) * (F + 1)) := Nat.mul_le_mul_right _ hsum
      _ ≤ 1024 * (F + 2) * (L + 2) * (N + 1) ^ 3 := by
        have h1 : (L + 1) * (F + 1) ≤ (L + 2) * (F + 2) := Nat.mul_le_mul (by omega) (by omega)
        have h2 := Nat.mul_le_mul_left (1024 * (N + 1) ^ 3) h1
        calc 1024 * ((N + 1) ^ 3 * (L + 1) * (F + 1))
            = 1024 * (N + 1) ^ 3 * ((L + 1) * (F + 1)) := by ring
          _ ≤ 1024 * (N + 1) ^ 3 * ((L + 2) * (F + 2)) := h2
          _ = 1024 * (F + 2) * (L + 2) * (N + 1) ^ 3 := by ring

private theorem ep6_okC_le (N L F : ℕ) (p : ep6_Poly) (h : ep6_okC p = true) :
    ep6_ev N L F p ≤ 64 * (N + 1) ^ 2 * (L + 3) := by
  simp only [ep6_okC, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hall, h0⟩, h1⟩ := h
  have key : ep6_ev N L F p ≤ (N + 1) ^ 2 * ((p.map fun e => if e.2.2.1 = 0 then e.1 else 0).sum +
      (p.map fun e => if e.2.2.1 = 0 then 0 else e.1).sum * L) := by
    clear h0 h1
    induction p with
    | nil => simp [ep6_ev]
    | cons a p ih =>
      have ih' := ih fun e he => hall e (List.mem_cons_of_mem a he)
      obtain ⟨⟨ha, hb⟩, hc⟩ := hall a List.mem_cons_self
      simp only [ep6_ev, List.map_cons, List.sum_cons] at ih' ⊢
      have hN : N ^ a.2.1 ≤ (N + 1) ^ 2 :=
        (Nat.pow_le_pow_left (Nat.le_succ N) _).trans (Nat.pow_le_pow_right (by omega) ha)
      have hterm : a.1 * (N ^ a.2.1 * L ^ a.2.2.1 * F ^ a.2.2.2) ≤
          (N + 1) ^ 2 * ((if a.2.2.1 = 0 then a.1 else 0) +
            (if a.2.2.1 = 0 then 0 else a.1) * L) := by
        rw [hc, pow_zero, mul_one]
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with hb0 | hb1
        · simp only [hb0, pow_zero, mul_one, if_true, zero_mul, add_zero]
          calc a.1 * N ^ a.2.1 ≤ a.1 * (N + 1) ^ 2 := Nat.mul_le_mul_left _ hN
            _ = (N + 1) ^ 2 * a.1 := Nat.mul_comm _ _
        · simp only [hb1, pow_one, one_ne_zero, if_false, zero_add]
          calc a.1 * (N ^ a.2.1 * L) ≤ a.1 * ((N + 1) ^ 2 * L) :=
                Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hN)
            _ = (N + 1) ^ 2 * (a.1 * L) := by ring
      calc a.1 * (N ^ a.2.1 * L ^ a.2.2.1 * F ^ a.2.2.2) + ep6_ev N L F p
          ≤ _ + _ := Nat.add_le_add hterm ih'
        _ = _ := by ring
  refine key.trans ?_
  calc (N + 1) ^ 2 * (_ + _ * L) ≤ (N + 1) ^ 2 * (192 + 64 * L) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add h0 (Nat.mul_le_mul_right _ h1))
    _ = 64 * (N + 1) ^ 2 * (L + 3) := by ring

/-! #### The kernel bound -/

/-- The kernel calls charged by `NLAlib.eighCount` for a node of size $k$ split at $k_+$. -/
private noncomputable def ep6_G (p : P) (mm qr : ι) (F k kp : ℕ) : OpCount P ι :=
  (2 * F + 8) • Finsupp.single (.kcall p mm [k, k, k]) 1 +
    Finsupp.single (.kcall p qr [k, k]) 2 +
    Finsupp.single (.kcall p mm [kp, k, k]) 1 + Finsupp.single (.kcall p mm [kp, k, kp]) 1 +
    Finsupp.single (.kcall p mm [k - kp, k, k]) 1 +
    Finsupp.single (.kcall p mm [k - kp, k, k - kp]) 1 +
    Finsupp.single (.kcall p mm [k, kp, kp]) 1 +
    Finsupp.single (.kcall p mm [k, k - kp, k - kp]) 1

/-- The kernel calls charged for a node of size $k$, every split. -/
private noncomputable def ep6_Gk (p : P) (mm qr : ι) (F k : ℕ) : OpCount P ι :=
  ∑ kp ∈ Finset.range (k + 1), ep6_G p mm qr F k kp

omit [DecidableEq P] in
private theorem ep6_eighCount_eq (p : P) (mm qr : ι) (n L F : ℕ) :
    eighCount p mm qr n L F = ((eighScalarKinds (ι := ι) p).map fun κ =>
      Finsupp.single κ (1024 * (F + 2) * (L + 2) * (n + 1) ^ 3)).sum +
      (2 * (L + 1) * n) • ∑ k ∈ Finset.range (n + 1), ep6_Gk p mm qr F k := rfl

omit [DecidableEq P] in
private theorem ep6_lsum_le (m : ℕ) (f : ℕ → OpCount P ι) (B : OpCount P ι)
    (h : ∀ i < m, f i ≤ B) : ((List.range m).map f).sum ≤ m • B := by
  simpa using ep6_sum_le (List.range m) f B fun i hi => h i (List.mem_range.mp hi)

omit [DecidableEq P] in
private theorem ep6_trip_le {m : ℕ} (hm : m ≤ 1) (f : ℕ → OpCount P ι) :
    ((List.range m).map f).sum ≤ f 0 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hm with rfl | rfl <;> simp

omit [DecidableEq P] in
private theorem ep6_fsup_le (l : List ℕ) (f : ℕ → OpCount P ι) (B : OpCount P ι)
    (h : ∀ k ∈ l, f k ≤ B) : l.foldr (fun k c => f k ⊔ c) 0 ≤ B := by
  induction l with
  | nil => exact zero_le
  | cons a l ih =>
    exact sup_le (h a List.mem_cons_self) (ih fun k hk => h k (List.mem_cons_of_mem a hk))

omit [DecidableEq P] in
private theorem ep6_fsup_le_sum (m : ℕ) (f : ℕ → OpCount P ι) :
    (List.range m).foldr (fun k c => f k ⊔ c) 0 ≤ ∑ k ∈ Finset.range m, f k :=
  ep6_fsup_le _ _ _ fun _ hk => Finset.single_le_sum (fun _ _ => zero_le)
    (Finset.mem_range.mpr (List.mem_range.mp hk))

omit [DecidableEq P] in
private theorem ep6_Dsplit_le (p : P) (mm qr : ι) (ρ : Fin 10 → ℕ) :
    (2 * ρ ⟨2, by decide⟩ + 6) • Finsupp.single (OpKind.kcall p mm
      [ρ ⟨5, by decide⟩, ρ ⟨5, by decide⟩, ρ ⟨5, by decide⟩]) 1 +
      ep6_kc (ep6_Dsplit p mm qr) ρ ≤
      ep6_G p mm qr (ρ ⟨2, by decide⟩) (ρ ⟨5, by decide⟩) (ρ ⟨8, by decide⟩) := by
  simp only [ep6_Dsplit, ep6_kc, ep6_v, IExp.evalIn, List.map_cons, List.map_nil, ep6_G]
  generalize ρ ⟨2, by decide⟩ = F
  generalize ρ ⟨5, by decide⟩ = k
  generalize ρ ⟨8, by decide⟩ = kp
  have e2 : Finsupp.single (OpKind.kcall p qr [k, k]) 2 =
      Finsupp.single (OpKind.kcall p qr [k, k]) 1 +
        Finsupp.single (OpKind.kcall p qr [k, k]) 1 := by
    rw [← Finsupp.single_add]
  rw [e2]
  refine (le_self_add (b := Finsupp.single (OpKind.kcall p mm [k, kp, kp]) 1 +
    Finsupp.single (OpKind.kcall p mm [k, k - kp, k - kp]) 1)).trans_eq ?_
  ext κ
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  ring

omit [DecidableEq P] in
private theorem ep6_D9_le (p : P) (mm qr : ι) (ρ : Fin 9 → ℕ) :
    (2 * ρ ⟨2, by decide⟩ + 6) • Finsupp.single (OpKind.kcall p mm
      [ρ ⟨5, by decide⟩, ρ ⟨5, by decide⟩, ρ ⟨5, by decide⟩]) 1 +
      ep6_kc (ep6_D9 p mm qr) ρ ≤
      ep6_G p mm qr (ρ ⟨2, by decide⟩) (ρ ⟨5, by decide⟩) (ρ ⟨8, by decide⟩) := by
  simp only [ep6_D9, ep6_kc]
  refine (add_le_add le_rfl (ep6_trip_le (Nat.sub_le _ _) _)).trans ?_
  exact ep6_Dsplit_le p mm qr (Fin.snoc ρ 0)

omit [DecidableEq P] in
private theorem ep6_D8_le (p : P) (mm qr : ι) (ρ : Fin 8 → ℕ) :
    ep6_kc (ep6_D8 p mm qr) ρ ≤ ep6_Gk p mm qr (ρ ⟨2, by decide⟩) (ρ ⟨5, by decide⟩) := by
  simp only [ep6_D8, ep6_kc, ep6_v, IExp.evalIn, List.map_cons, List.map_nil]
  set F := ρ ⟨2, by decide⟩
  set k := ρ ⟨5, by decide⟩
  set s := Finsupp.single (OpKind.kcall p mm [k, k, k]) (1 : ℕ)
  have h1 : s + ((List.range F).map fun _ => s + s).sum ≤ (2 * F + 6) • s := by
    rw [List.map_const', List.sum_replicate, List.length_range]
    have : s + F • (s + s) = (2 * F + 1) • s := by
      ext κ; simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]; ring
    rw [this]
    exact nsmul_le_nsmul_left zero_le (by omega)
  refine (add_le_add h1 le_rfl).trans ?_
  have hX : ∀ kp, (2 * F + 6) • s + ep6_kc (ep6_D9 p mm qr) (Fin.snoc (α := fun _ => ℕ) ρ kp) ≤
      ep6_G p mm qr F k kp := fun kp => ep6_D9_le p mm qr (Fin.snoc ρ kp)
  refine (add_le_add le_rfl (ep6_fsup_le_sum _ _)).trans ?_
  unfold ep6_Gk
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  calc (2 * F + 6) • s + (∑ i ∈ Finset.range k, ep6_kc (ep6_D9 p mm qr)
        (Fin.snoc (α := fun _ => ℕ) ρ (i + 1)) +
        ep6_kc (ep6_D9 p mm qr) (Fin.snoc (α := fun _ => ℕ) ρ 0))
      = (∑ i ∈ Finset.range k, ep6_kc (ep6_D9 p mm qr) (Fin.snoc (α := fun _ => ℕ) ρ (i + 1))) +
        ((2 * F + 6) • s + ep6_kc (ep6_D9 p mm qr) (Fin.snoc (α := fun _ => ℕ) ρ 0)) := by abel
    _ ≤ _ := add_le_add (Finset.sum_le_sum fun i _ => le_add_self.trans (hX (i + 1))) (hX 0)

omit [DecidableEq P] in
private theorem ep6_D6_le (p : P) (mm qr : ι) (ρ : Fin 6 → ℕ) :
    ep6_kc (ep6_D6 p mm qr) ρ ≤ ep6_Gk p mm qr (ρ ⟨2, by decide⟩) (ρ ⟨5, by decide⟩) := by
  simp only [ep6_D6, ep6_kc]
  refine (ep6_trip_le (Nat.sub_le _ _) _).trans ?_
  refine (ep6_trip_le (Nat.sub_le _ _) _).trans ?_
  exact ep6_D8_le p mm qr _

omit [DecidableEq P] in
private theorem ep6_U10_le (p : P) (mm qr : ι) (ρ : Fin 10 → ℕ) :
    ep6_kc (ep6_U10 p mm) ρ ≤
      ep6_G p mm qr (ρ ⟨2, by decide⟩) (ρ ⟨5, by decide⟩) (ρ ⟨9, by decide⟩) := by
  simp only [ep6_U10, ep6_kc, ep6_v, IExp.evalIn, List.map_cons, List.map_nil, ep6_G]
  rw [add_assoc _ (Finsupp.single _ 1) (Finsupp.single _ 1)]
  exact le_add_self

omit [DecidableEq P] in
private theorem ep6_U6_le (p : P) (mm qr : ι) (ρ : Fin 6 → ℕ) :
    ep6_kc (ep6_U6 p mm) ρ ≤ ep6_Gk p mm qr (ρ ⟨2, by decide⟩) (ρ ⟨5, by decide⟩) := by
  simp only [ep6_U6, ep6_kc]
  refine (ep6_trip_le (Nat.sub_le _ _) _).trans ?_
  refine ep6_fsup_le _ _ _ fun c _ => ?_
  simp only [ep6_U8, ep6_kc]
  refine (ep6_trip_le (Nat.sub_le _ _) _).trans ?_
  simp only [ep6_U9, ep6_kc]
  refine ep6_fsup_le _ _ _ fun kp hkp => ?_
  refine (ep6_U10_le p mm qr _).trans ?_
  exact Finset.single_le_sum (f := fun kp => ep6_G p mm qr _ _ kp) (fun _ _ => zero_le)
    (Finset.mem_range.mpr (List.mem_range.mp hkp))

omit [DecidableEq P] in
/-- The kernel calls of the registered tree are at most those of `NLAlib.eighCount`. -/
private theorem ep6_T_le (p : P) (mm qr : ι) (N L F : ℕ) :
    ep6_kc (ep6_T p mm qr) (Fin.cons N ![L, F]) ≤
      (2 * (L + 1) * N) • ∑ k ∈ Finset.range (N + 1), ep6_Gk p mm qr F k := by
  set Gs := ∑ k ∈ Finset.range (N + 1), ep6_Gk p mm qr F k
  have hG : ∀ k ≤ N, ep6_Gk p mm qr F k ≤ Gs := fun k hk =>
    Finset.single_le_sum (f := fun k => ep6_Gk p mm qr F k) (fun _ _ => zero_le)
      (Finset.mem_range.mpr (by omega))
  have hlev : ∀ (X : ep6_KT P ι 6), (∀ ρ : Fin 6 → ℕ, ρ ⟨2, by decide⟩ = F → ρ ⟨5, by decide⟩ ≤ N →
      ep6_kc X ρ ≤ Gs) →
      ep6_kc (ep6_KT.loop (.add (ep6_v 1) (.const 1)) (.loop (ep6_v 0)
        (.bind (.sub (ep6_v 0) (ep6_v 4)) X))) (Fin.cons N ![L, F]) ≤ (L + 1) • N • Gs := by
    intro X hX
    simp only [ep6_kc]
    refine ep6_lsum_le _ _ _ fun d _ => ?_
    refine ep6_lsum_le _ _ _ fun lo _ => ?_
    refine ep6_fsup_le _ _ _ fun k hk => hX _ rfl ?_
    have := List.mem_range.mp hk
    simp only [IExp.evalIn, ep6_v] at this
    change k ≤ N
    have h0 : (Fin.snoc (α := fun _ => ℕ) (Fin.snoc (α := fun _ => ℕ)
        (Fin.cons N ![L, F] : Fin 3 → ℕ) d) lo) ⟨0, by decide⟩ = N := rfl
    rw [h0] at this
    omega
  simp only [ep6_T, ep6_kc]
  refine (add_le_add (hlev _ fun ρ hF hk => (ep6_D6_le p mm qr ρ).trans (hF ▸ hG _ hk))
    (hlev _ fun ρ hF hk => (ep6_U6_le p mm qr ρ).trans (hF ▸ hG _ hk))).trans_eq ?_
  rw [smul_smul, ← add_nsmul]
  congr 1
  ring

/-! #### Assembly -/

private theorem ep6_ρ0 (N L F : ℕ) :
    ∀ v, (Fin.cons N ![L, F] : Fin 3 → ℕ) v ≤ ep6_ev N L F (ep6_σ0 v) := by
  intro v
  fin_cases v <;> simp [ep6_σ0, ep6_ev]

omit [DecidableEq P] in
private theorem ep6_scalar_ge (p : P) (mm qr : ι) (n L F : ℕ) {κ : OpKind P ι}
    (hκ : κ ∈ eighScalarKinds (ι := ι) p) :
    1024 * (F + 2) * (L + 2) * (n + 1) ^ 3 ≤ eighCount p mm qr n L F κ := by
  rw [ep6_eighCount_eq, Finsupp.add_apply]
  refine le_trans ?_ (Nat.le_add_right _ _)
  have h := List.single_le_sum (fun _ _ => zero_le) _
    (List.mem_map_of_mem (f := fun κ : OpKind P ι =>
      Finsupp.single κ (1024 * (F + 2) * (L + 2) * (n + 1) ^ 3)) hκ)
  simpa using h κ

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
omit [DecidableEq P] in
private theorem ep6_scalar_bound (p : P) (mm qr : ι) (N L F : ℕ) (κ : OpKind P ι)
    (h9 : ep6_cls κ ≠ 9) (ht : ep6_ktag κ = p) :
    ep6_ev N L F (ep6_C (ep6_cls κ) (eighProg.compiled () true false) ep6_σ0) ≤
      eighCount p mm qr N L F κ := by
  have hz : ∀ c ∈ [3, 4, 5, 8, 14, 21, 31], c = ep6_cls κ →
      ep6_ev N L F (ep6_C (ep6_cls κ) (eighProg.compiled () true false) ep6_σ0) ≤
        eighCount p mm qr N L F κ := by
    intro c hc he
    rw [← he, ep6_zero_compiled0 c hc]
    simp [ep6_ev]
  have hs : ∀ c ∈ [1, 2, 6, 7, 10, 11, 12, 13, 20, 23, 30, 32], c = ep6_cls κ →
      κ ∈ eighScalarKinds (ι := ι) p →
      ep6_ev N L F (ep6_C (ep6_cls κ) (eighProg.compiled () true false) ep6_σ0) ≤
        eighCount p mm qr N L F κ := by
    intro c hc he hk
    rw [← he]
    exact (ep6_okS_le N L F _ (ep6_okS_compiled0 c hc)).trans (ep6_scalar_ge p mm qr N L F hk)
  cases κ with
  | bin q b =>
    simp only [ep6_ktag] at ht; subst ht
    cases b <;> first
      | exact hz 3 (by simp) rfl
      | exact hz 4 (by simp) rfl
      | exact hz 5 (by simp) rfl
      | exact hz 8 (by simp) rfl
      | exact hz 14 (by simp) rfl
      | exact hz 21 (by simp) rfl
      | exact hz 31 (by simp) rfl
      | exact hs 1 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 2 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 6 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 7 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 10 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 11 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 12 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 13 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 20 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 23 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 30 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 32 (by simp) rfl (by simp [eighScalarKinds])
  | un q u =>
    simp only [ep6_ktag] at ht; subst ht
    cases u <;> first
      | exact hz 3 (by simp) rfl
      | exact hz 4 (by simp) rfl
      | exact hz 5 (by simp) rfl
      | exact hz 8 (by simp) rfl
      | exact hz 14 (by simp) rfl
      | exact hz 21 (by simp) rfl
      | exact hz 31 (by simp) rfl
      | exact hs 1 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 2 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 6 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 7 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 10 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 11 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 12 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 13 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 20 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 23 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 30 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 32 (by simp) rfl (by simp [eighScalarKinds])
  | draw q d =>
    simp only [ep6_ktag] at ht; subst ht
    cases d <;> first
      | exact hz 3 (by simp) rfl
      | exact hz 4 (by simp) rfl
      | exact hz 5 (by simp) rfl
      | exact hz 8 (by simp) rfl
      | exact hz 14 (by simp) rfl
      | exact hz 21 (by simp) rfl
      | exact hz 31 (by simp) rfl
      | exact hs 1 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 2 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 6 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 7 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 10 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 11 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 12 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 13 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 20 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 23 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 30 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 32 (by simp) rfl (by simp [eighScalarKinds])
  | kcall q o d => exact absurd rfl h9
  | _ =>
    simp only [ep6_ktag] at ht; subst ht
    first
      | exact hz 3 (by simp) rfl
      | exact hz 4 (by simp) rfl
      | exact hz 5 (by simp) rfl
      | exact hz 8 (by simp) rfl
      | exact hz 14 (by simp) rfl
      | exact hz 21 (by simp) rfl
      | exact hz 31 (by simp) rfl
      | exact hs 1 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 2 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 6 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 7 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 10 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 11 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 12 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 13 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 20 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 23 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 30 (by simp) rfl (by simp [eighScalarKinds])
      | exact hs 32 (by simp) rfl (by simp [eighScalarKinds])

omit [DecidableEq P] in
set_option maxRecDepth 100000 in
private theorem ep6_tags_compiled (p : P) (mm qr : ι) :
    ∀ q ∈ ep6_tags (eighProg.compiled p mm qr), q = p := by
  rw [ep6_compiled_map, ep6_tags_map]
  intro q hq
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hq
  rfl

omit [DecidableEq P] in
set_option maxRecDepth 100000 in
private theorem ep6_C_compiled (p : P) (mm qr : ι) (c : ℕ) :
    ep6_C c (eighProg.compiled p mm qr) ep6_σ0 =
      ep6_C c (eighProg.compiled () true false) ep6_σ0 := by
  rw [ep6_compiled_map, ep6_C_map]

omit [DecidableEq P] in
set_option maxRecDepth 100000 in
private theorem ep6_Cc_compiled (p : P) (mm qr : ι) :
    ep6_Cc (eighProg.compiled p mm qr) ep6_σ0 =
      ep6_Cc (eighProg.compiled () true false) ep6_σ0 := by
  rw [ep6_compiled_map, ep6_Cc_map]

private theorem ep6_count_bound (w : P → ℕ) (p : P) (mm qr : ι) (N L F : ℕ)
    (T : FStmt P ι 4 3) (hpr : ep6_prune T = ep6_T p mm qr)
    (hC : ∀ c, ep6_C c T ep6_σ0 = ep6_C c (eighProg.compiled () true false) ep6_σ0)
    (htag : ∀ q ∈ ep6_tags T, q = p) (κ : OpKind P ι) :
    (FStmt.staticCost (fun k => Finsupp.single k 1) w T (Fin.cons N ![L, F])).count κ ≤
      eighCount p mm qr N L F κ := by
  by_cases h9 : ep6_cls κ = 9
  · rw [ep6_count_prune w κ h9, hpr, ep6_eighCount_eq, Finsupp.add_apply]
    exact (ep6_T_le p mm qr N L F κ).trans (Nat.le_add_left _ _)
  · by_cases ht : ep6_ktag κ = p
    · refine (ep6_count_le w κ N L F T _ ep6_σ0 (ep6_ρ0 N L F)).trans ?_
      rw [hC]
      exact ep6_scalar_bound p mm qr N L F κ h9 ht
    · have := ep6_count_tag w κ T (Fin.cons N ![L, F]) fun hm => ht (htag _ hm)
      omega

private theorem ep6_cells_bound (charge : OpKind P ι → OpCount P ι) (w : P → ℕ) (p : P)
    (N L F : ℕ) (T : FStmt P ι 4 3)
    (hC : ep6_Cc T ep6_σ0 = ep6_Cc (eighProg.compiled () true false) ep6_σ0)
    (htag : ∀ q ∈ ep6_tags T, q = p) (q : P) :
    (FStmt.staticCost charge w T (Fin.cons N ![L, F])).cells q ≤
      if q = p then 64 * (N + 1) ^ 2 * (L + 3) else 0 := by
  split_ifs with hq
  · refine (ep6_cells_le charge w q N L F T _ ep6_σ0 (ep6_ρ0 N L F)).trans ?_
    rw [hC]
    exact ep6_okC_le N L F _ ep6_okC_compiled0
  · exact ep6_cells_tag charge w q _ _ fun hm => hq (htag _ hm)

/-- The counts and the memory of the registered tree: under the standard charge (one per
operation), every successful run of `NLAlib.eighProg.compiled` at the sizes $N$ and $(\ell_0, F)$
adds at most `NLAlib.eighCount p mm qr N ℓ₀ F` to the counts and raises the peak memory at tag `p`
by at most $64(N + 1)^2(\ell_0 + 3)$ cells above the current memory (by nothing at any other tag):
the arenas of $D + 1 = \ell_0 + 2$ levels and the scratch of one node, $O(N^2 \ell_0)$. No printed
source. -/
theorem eighProg.cnt_le_of_exec_compiled {mm qr : ι} {I : Interp P ι K (OpCount P ι)}
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (p : P) (N ℓ₀ F : ℕ)
    {st st' : St P K (OpCount P ι)}
    (h : (eighProg.compiled p mm qr).exec I N ![ℓ₀, F] st = some st') :
    st'.cnt ≤ st.cnt + eighCount p mm qr N ℓ₀ F ∧
      ∀ q, st'.peak q ≤ max (st.peak q)
        (st.cur q + if q = p then 64 * (N + 1) ^ 2 * (ℓ₀ + 3) else 0) := by
  have hb := (eighProg.compiled p mm qr).bounds_staticCost_of_exec_eq_some I N ![ℓ₀, F] h
  have hpr := ep6_prune_compiled p mm qr
  have hC := ep6_C_compiled p mm qr
  have hCc := ep6_Cc_compiled p mm qr
  have htag := ep6_tags_compiled p mm qr
  generalize eighProg.compiled p mm qr = T at hb hpr hC hCc htag
  have hcharge : I.charge = fun k => Finsupp.single k 1 := funext hc
  have hcount := ep6_count_bound I.width p mm qr N ℓ₀ F T hpr hC htag
  rw [← hcharge] at hcount
  exact ⟨hb.count.trans (add_le_add le_rfl fun κ => hcount κ), fun q => (hb.peak q).trans
    (max_le_max le_rfl
      (add_le_add le_rfl (ep6_cells_bound I.charge I.width p N ℓ₀ F T hCc htag q)))⟩

end NLAlib
