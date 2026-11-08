/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SpectralBisectionProgram
public import NLAlib.Matrix.Computation.SpectralBisectionProgram.FrameRules

/-!
# The weighted kernel cost of the spectral bisection program

The weighted kernel bound of [Shah2024, Section 4] for the registered tree
`NLAlib.eighProg.compiled`: for a cost $T$ of a kernel call by its largest dimension that is
monotone and superadditive, every successful run adds at most $(\ell_0 + 1)(2F + 12)\,T(N)$ to the
weighted kernel count: per level, the nodes have sizes summing to at most $N$ (they stay packed in
$[0, N)$), each with at most $2F + 12$ kernel calls of largest dimension at most its size.

## Main results

* `NLAlib.eighProg.weight_le_of_exec_compiled`: the weighted kernel bound.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}

section EP7

omit [AddMonoid C] [Inhabited K]

variable {I : Interp P ι K (OpCount P ι)} {T : ℕ → ℕ} {p : P} {b m : ℕ}

local macro "ep7_side" : tactic => `(tactic| (simp only [ep7_dst, List.mem_cons, List.mem_singleton,
  forall_eq_or_imp, forall_eq, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true,
  IExp.eval_var, IExp.eval_add, IExp.eval_sub, IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat,
  ne_eq, false_or, or_false, false_implies, forall_const, true_and] at * <;> omega))

local macro "ep7_z" : tactic => `(tactic| repeat (first
  | exact ep7_bw_pure
  | (apply ep7_bw_ins; ep7_side)
  | (apply ep7_bw_forRange0; intro _)
  | apply ep7_bw_scope
  | apply ep7_bw_named
  | apply ep7_bw_ite0
  | (apply ep7_bw_bindIdx; intro _ _)
  | apply ep7_bw_when
  | (apply ep7_bw_allocBind; intro _ _)
  | apply ep7_bw_bind0))

local macro "ep7_k" : tactic => `(tactic| first
  | (with_reducible apply ep7_bw_zhermShift); ep7_side
  | (with_reducible apply ep7_bw_zhermScale); ep7_side
  | (with_reducible apply ep7_bw_zhermAvg); ep7_side
  | (with_reducible apply ep7_bw_zcopy); ep7_side
  | (with_reducible apply ep7_bw_zneg); ep7_side
  | (with_reducible apply ep7_bw_zconjTranspose); ep7_side
  | (with_reducible apply ep7_bw_zidentity); ep7_side
  | (with_reducible apply ep7_bw_ztraceRe); ep7_side
  | (with_reducible apply ep7_bw_zboxTest); ep7_side)

local macro "ep7_bw_tac" : tactic => `(tactic| repeat (first
  | (with_reducible exact ep7_bw_pure)
  | (with_reducible apply ep7_bw_ins); ep7_side
  | (with_reducible apply ep7_bw_kcall) <;> ep7_side
  | ep7_k
  | (with_reducible apply ep7_bw_forRange0); intro _; ep7_z; done
  | (with_reducible apply ep7_bw_forRange); intro _
  | (with_reducible apply ep7_bw_scope)
  | (with_reducible apply ep7_bw_named)
  | (with_reducible apply ep7_bw_ite)
  | (with_reducible apply ep7_bw_bindIdx); intro _ _
  | (with_reducible apply ep7_bw_when)
  | (with_reducible apply ep7_bw_allocBind); intro _ _
  | (with_reducible apply ep7_bw_bind)))

local macro "ep7_bwx" : tactic => `(tactic| first
  | (with_reducible apply ep7_bw_deflate) <;> ep7_side
  | (with_reducible apply ep7_bw_compress) <;> ep7_side
  | (with_reducible apply ep7_bw_sign) <;> ep7_side
  | (with_reducible apply ep7_bw_leaf) <;> ep7_side
  | (with_reducible apply ep7_bw_clamp) <;> ep7_side
  | (with_reducible apply ep7_bw_ins); ep7_side
  | (with_reducible apply ep7_bw_kcall) <;> ep7_side
  | ep7_k
  | ep7_bw_tac)

local macro "ep7_ht_tac" : tactic => `(tactic| repeat (first
  | (with_reducible apply ep7_ht_allocK); intro _ _
  | (with_reducible apply ep7_ht_bindK); (with_reducible apply ep7_ht_litK)
  | (with_reducible apply ep7_ht_litK)
  | (with_reducible apply ep7_ht_bwBindK); on_goal 1 => (ep7_bwx; done)
  | (with_reducible apply ep7_ht_bwK); on_goal 1 => (ep7_bwx; done)
  | exact ep7_ht_skipK rfl))

/-! Packing -/

/-- the positive entries of `g` on `[a, c)` are disjoint ranges inside `[a, c)` -/
private def ep7_Packed (g : ℕ → ℕ) (a c : ℕ) : Prop :=
  ∀ j, a ≤ j → j < c → 0 < g j → j + g j ≤ c ∧ ∀ i, j < i → i < j + g j → g i = 0

omit [DecidableEq P] in
private theorem ep7_T_zero (hTs : ∀ a b, T a + T b ≤ T (a + b)) : T 0 = 0 := by
  have := hTs 0 0; simp at this; omega

private theorem ep7_packed_sum (hT : Monotone T) (hTs : ∀ a b, T a + T b ≤ T (a + b)) {g : ℕ → ℕ}
    {c : ℕ} : ∀ a, ep7_Packed g a c → ∑ j ∈ Finset.Ico a c, T (g j) ≤ T (c - a) := by
  have hT0 := ep7_T_zero hTs
  intro a
  induction h : c - a using Nat.strong_induction_on generalizing a with
  | _ r ih =>
    intro hp
    rcases Nat.lt_or_ge a c with hac | hac
    · rcases Nat.eq_zero_or_pos (g a) with hg | hg
      · rw [Finset.sum_eq_sum_Ico_succ_bot hac, hg, hT0, zero_add]
        refine (ih (c - (a + 1)) (by omega) (a + 1) rfl fun j h1 h2 h3 =>
          hp j (by omega) h2 h3).trans (hT (by omega))
      · obtain ⟨h1, h2⟩ := hp a le_rfl hac hg
        rw [← Finset.sum_Ico_consecutive _ (show a ≤ a + g a by omega) h1,
          Finset.sum_eq_sum_Ico_succ_bot (show a < a + g a by omega)]
        have hz : ∑ j ∈ Finset.Ico (a + 1) (a + g a), T (g j) = 0 :=
          Finset.sum_eq_zero fun j hj => by
            rw [Finset.mem_Ico] at hj; rw [h2 j (by omega) (by omega), hT0]
        rw [hz, add_zero]
        have := ih (c - (a + g a)) (by omega) (a + g a) rfl fun j h1 h2 h3 => hp j (by omega) h2 h3
        calc T (g a) + ∑ j ∈ Finset.Ico (a + g a) c, T (g j) ≤ T (g a) + T (c - (a + g a)) :=
              Nat.add_le_add_left this _
          _ ≤ T (g a + (c - (a + g a))) := hTs _ _
          _ ≤ T r := hT (by omega)
    · rw [Finset.Ico_eq_empty (by omega)]; simp

private theorem ep7_packed_extend {g : ℕ → ℕ} {a c c' : ℕ} (h : ep7_Packed g a c) (hcc : c ≤ c')
    (hz : ∀ j, c ≤ j → j < c' → g j = 0) : ep7_Packed g a c' := by
  intro j h1 h2 h3
  rcases Nat.lt_or_ge j c with hj | hj
  · obtain ⟨h4, h5⟩ := h j h1 hj h3; exact ⟨by omega, h5⟩
  · rw [hz j hj h2] at h3; omega

private theorem ep7_packed_append {g : ℕ → ℕ} {a c e : ℕ} (h : ep7_Packed g a c)
    (h' : ep7_Packed g c e) (hce : c ≤ e) : ep7_Packed g a e := by
  intro j h1 h2 h3
  rcases Nat.lt_or_ge j c with hj | hj
  · obtain ⟨h4, h5⟩ := h j h1 hj h3; exact ⟨by omega, h5⟩
  · exact h' j hj h2 h3

private theorem ep7_packed_congr {g g' : ℕ → ℕ} {a c : ℕ} (h : ep7_Packed g a c)
    (he : ∀ j, a ≤ j → j < c → g' j = g j) : ep7_Packed g' a c := by
  intro j h1 h2 h3
  rw [he j h1 h2] at h3 ⊢
  obtain ⟨h4, h5⟩ := h j h1 h2 h3
  exact ⟨h4, fun i hi1 hi2 => by rw [he i (by omega) (by omega)]; exact h5 i hi1 hi2⟩

private theorem ep7_packed_zero {g : ℕ → ℕ} {a c : ℕ} (hz : ∀ j, a ≤ j → j < c → g j = 0) :
    ep7_Packed g a c := by
  intro j h1 h2 h3; rw [hz j h1 h2] at h3; omega

private theorem ep7_comb_child {g g' : ℕ → ℕ} {lo s N : ℕ} (hpk : ep7_Packed g 0 lo)
    (hz : ∀ j, lo ≤ j → j < N → g j = 0) (hs : lo + s ≤ N) (hs0 : 0 < s)
    (hg' : ∀ j, g' j = if j = lo then s else g j) :
    ep7_Packed g' 0 (lo + s) ∧ ∀ j, lo + s ≤ j → j < N → g' j = 0 := by
  refine ⟨ep7_packed_append (ep7_packed_congr hpk fun j _ h2 => by rw [hg', if_neg (by omega)])
    ?_ (by omega), fun j h1 h2 => by rw [hg', if_neg (by omega)]; exact hz j (by omega) h2⟩
  intro j h1 h2 h3
  rcases Nat.lt_or_ge lo j with hj | hj
  · rw [hg', if_neg (by omega), hz j (by omega) (by omega)] at h3; omega
  · have : j = lo := by omega
    subst this
    rw [hg', if_pos rfl]
    refine ⟨le_rfl, fun i hi1 hi2 => ?_⟩
    rw [hg', if_neg (by omega)]; exact hz i (by omega) (by omega)

private theorem ep7_comb_split {g g' : ℕ → ℕ} {lo s kp N : ℕ} (hpk : ep7_Packed g 0 lo)
    (hz : ∀ j, lo ≤ j → j < N → g j = 0) (hs : lo + s ≤ N) (hkp0 : 0 < kp) (hkp : kp < s)
    (hg' : ∀ j, g' j = if j = lo + kp then s - kp else if j = lo then kp else g j) :
    ep7_Packed g' 0 (lo + s) ∧ ∀ j, lo + s ≤ j → j < N → g' j = 0 := by
  refine ⟨ep7_packed_append (ep7_packed_congr hpk fun j _ h2 => by
      rw [hg', if_neg (by omega), if_neg (by omega)])
    ?_ (by omega), fun j h1 h2 => by
      rw [hg', if_neg (by omega), if_neg (by omega)]; exact hz j (by omega) h2⟩
  have hzero : ∀ i, lo ≤ i → i < lo + s → i ≠ lo → i ≠ lo + kp → g' i = 0 := fun i h1 h2 h3 h4 => by
    rw [hg', if_neg h4, if_neg h3]; exact hz i h1 (by omega)
  intro j h1 h2 h3
  by_cases hj1 : j = lo
  · subst hj1
    rw [hg', if_neg (by omega), if_pos rfl]
    exact ⟨by omega, fun i hi1 hi2 => hzero i (by omega) (by omega) (by omega) (by omega)⟩
  by_cases hj2 : j = lo + kp
  · subst hj2
    rw [hg', if_pos rfl]
    exact ⟨by omega, fun i hi1 hi2 => hzero i (by omega) (by omega) (by omega) (by omega)⟩
  · rw [hzero j h1 h2 hj1 hj2] at h3; omega

omit [DecidableEq P] in
private theorem ep7_f_update {V : ℕ → Option K} {i : ℕ} {v : Option K} (j : ℕ) :
    ep7_f I p (Function.update V i v) j =
      if j = i then (v.bind (I.sem.toNat p)).getD 0 else ep7_f I p V j := by
  unfold ep7_f
  by_cases h : j = i
  · subst h; simp
  · simp [h]

omit [DecidableEq P] in
private theorem ep7_lit_toNat {dec : P → K → ℝ} {B : ℕ} (hlit : IsExactIntLit dec I.sem B)
    (htn : IsExactToNat dec I.sem) {j : ℕ} (hj : j ≤ B) :
    ((I.sem.lit p (j : ℚ)).bind (I.sem.toNat p)).getD 0 = j := by
  obtain ⟨z, hz, -⟩ := hlit p j hj
  rw [hz]
  simp [IsExactIntLit.toNat_eq_of_lit_eq_some hlit htn hj hz]

/-- the invariant of the slot loop of a downward level, after the slots below `lo` -/
private def ep7_Inv (I : Interp P ι K (OpCount P ι)) (p : P) (V₀ : ℕ → Option K) (N d lo : ℕ)
    (V : ℕ → Option K) : Prop :=
  ∃ C, lo ≤ C ∧ C ≤ N ∧ (∀ i, (i < N * (d + 1) ∨ N * (d + 1) + N ≤ i) → V i = V₀ i) ∧
    ep7_Packed (fun j => ep7_f I p V (N * (d + 1) + j)) 0 C ∧
    (∀ j, C ≤ j → j < N → ep7_f I p V (N * (d + 1) + j) = 0) ∧
    (∀ j, lo ≤ j → j < C → ep7_f I p V₀ (N * d + j) = 0)

omit [DecidableEq P] in
private theorem ep7_inv_step {dec : P → K → ℝ} {B : ℕ} (hlit : IsExactIntLit dec I.sem B)
    (htn : IsExactToNat dec I.sem) {V₀ V V' : ℕ → Option K} {N d lo : ℕ} (hNB : N ≤ B)
    (hlo : lo < N) (hpk : ep7_Packed (fun j => ep7_f I p V₀ (N * d + j)) 0 N)
    (hinv : ep7_Inv I p V₀ N d lo V)
    (hQ : V' = V ∨ (2 ≤ min (ep7_f I p V (N * d + lo)) (N - lo) ∧
      ep7_RN I p V (N * (d + 1) + lo) (min (ep7_f I p V (N * d + lo)) (N - lo)) V')) :
    ep7_Inv I p V₀ N d (lo + 1) V' := by
  obtain ⟨C, hC1, hC2, hfr, hpC, hzC, hz0⟩ := hinv
  have hD : N * (d + 1) = N * d + N := Nat.mul_succ N d
  have hgs : ep7_f I p V (N * d + lo) = ep7_f I p V₀ (N * d + lo) := by
    unfold ep7_f; rw [hfr _ (Or.inl (by omega))]
  rw [hgs] at hQ
  set s := ep7_f I p V₀ (N * d + lo) with hs
  -- the slot's range at depth `d`
  have hsr : 0 < s → C = lo ∧ lo + s ≤ N ∧ ∀ j, lo < j → j < lo + s →
      ep7_f I p V₀ (N * d + j) = 0 := by
    intro hs0
    have hCl : C = lo := by
      rcases Nat.lt_or_ge lo C with h | h
      · have := hz0 lo le_rfl h; omega
      · omega
    obtain ⟨h1, h2⟩ := hpk lo (Nat.zero_le _) hlo hs0
    exact ⟨hCl, h1, h2⟩
  rcases hQ with rfl | ⟨hk2, kp, hkp, hRN⟩
  · -- no write
    rcases Nat.eq_zero_or_pos s with hs0 | hs0
    · rcases Nat.lt_or_ge lo C with h | h
      · exact ⟨C, h, hC2, hfr, hpC, hzC, fun j h1 h2 => hz0 j (by omega) h2⟩
      · refine ⟨lo + 1, le_rfl, by omega, hfr, ep7_packed_extend hpC (by omega) fun j h1 h2 =>
          hzC j h1 (by omega), fun j h1 h2 => hzC j (by omega) h2, fun j h1 h2 => by omega⟩
    · obtain ⟨hCl, hsN, hsz⟩ := hsr hs0
      subst hCl
      refine ⟨C + s, by omega, hsN, hfr, ep7_packed_extend hpC (by omega) fun j h1 h2 =>
          hzC j h1 (by omega), fun j h1 h2 => hzC j (by omega) h2,
          fun j h1 h2 => hsz j (by omega) h2⟩
  · have hs0 : 0 < s := by omega
    obtain ⟨hCl, hsN, hsz⟩ := hsr hs0
    subst hCl
    have hmin : min s (N - C) = s := by omega
    rw [hmin] at hkp hRN hk2
    have hlit' : ∀ j ≤ N, ((I.sem.lit p (j : ℚ)).bind (I.sem.toNat p)).getD 0 = j :=
      fun j hj => ep7_lit_toNat hlit htn (hj.trans hNB)
    rcases hRN with ⟨-, rfl⟩ | ⟨hkp0, hkps, rfl⟩
    · obtain ⟨h1, h2⟩ := ep7_comb_child (g := fun j => ep7_f I p V (N * (d + 1) + j))
        (g' := fun j => ep7_f I p (Function.update V (N * (d + 1) + C) (I.sem.lit p (s : ℚ)))
          (N * (d + 1) + j)) hpC hzC hsN hs0 fun j => by
          simp only [ep7_f_update, hlit' s (by omega)]
          by_cases hj : j = C <;> simp [hj]
      refine ⟨C + s, by omega, hsN, fun i hi => ?_, h1, h2, fun j h1 h2 => hsz j (by omega) h2⟩
      rw [Function.update_of_ne (by omega)]; exact hfr i hi
    · obtain ⟨h1, h2⟩ := ep7_comb_split (g := fun j => ep7_f I p V (N * (d + 1) + j))
        (g' := fun j => ep7_f I p (Function.update (Function.update V (N * (d + 1) + C)
          (I.sem.lit p (kp : ℚ))) (N * (d + 1) + C + kp) (I.sem.lit p ((s - kp : ℕ) : ℚ)))
          (N * (d + 1) + j)) hpC hzC hsN hkp0 hkps fun j => by
          simp only [ep7_f_update, hlit' kp (by omega), hlit' (s - kp) (by omega)]
          by_cases hj : j = C + kp
          · simp [hj, Nat.add_assoc]
          · by_cases hj' : j = C
            · simp [hj']
            · simp [hj, hj', show ¬ (N * (d + 1) + j = N * (d + 1) + C + kp) by omega]
      refine ⟨C + s, by omega, hsN, fun i hi => ?_, h1, h2, fun j h1 h2 => hsz j (by omega) h2⟩
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hfr i hi

private theorem ep7_ht_downLoop {dec : P → K → ℝ} {B : ℕ} (hlit : IsExactIntLit dec I.sem B)
    (htn : IsExactToNat dec I.sem) {mm qr : ι} {n L F d : IExp ℕ}
    {par Lv Su Sg Ma Ua Qa Ea Kd Kp t : ℕ} {one two half negone sqh : Cell ℕ ℕ}
    {V₀ : ℕ → Option K} (hMa : Ma ≠ b) (hUa : Ua ≠ b)
    (hQa : Qa ≠ b) (hEa : Ea ≠ b) (hKd : Kd ≠ b) (hKp : Kp ≠ b) (ht : t ≠ b) (hNB : n.eval ≤ B)
    (hTs : ∀ a b, T a + T b ≤ T (a + b))
    (hpk : ep7_Packed (fun j => ep7_f I p V₀ (n.eval * d.eval + j)) 0 n.eval)
    (hz : ∀ j, j < n.eval → ep7_f I p V₀ (n.eval * (d.eval + 1) + j) = 0) :
    ep7_HT I T p b n.eval V₀ (.loop n fun lo => (bindIdx p ⟨b, eighSlotOff n d (IExp.var lo)⟩
      (n - IExp.var lo) fun k => ep7_downSlot p mm qr n L F d par Lv Su Sg Ma Ua Qa Ea b Kd Kp t
        one two half negone sqh lo k).run) (2 * F.eval + 9)
      (ep7_Inv I p V₀ n.eval d.eval n.eval) := by
  intro hT hch st st' hb hV hex
  set N := n.eval
  set c := 2 * F.eval + 9
  set g₀ : ℕ → ℕ := fun j => ep7_f I p V₀ (N * d.eval + j)
  have := forall_of_exec_loop_eq_some I (fun lo s => b < s.store.size ∧
      Finsupp.weight (ep7_wt T) s.cnt ≤ Finsupp.weight (ep7_wt T) st.cnt +
        c * ∑ j ∈ Finset.range lo, T (g₀ j) ∧ ep7_Inv I p V₀ N d.eval lo (ep7_V s.store p b))
    ⟨hb, by simp, 0, le_rfl, Nat.zero_le _, fun i _ => by rw [hV],
      fun j _ h => absurd h (Nat.not_lt_zero _), fun j _ h => by rw [hV]; exact hz j h,
      fun j h1 h2 => absurd h2 (by omega)⟩
    (fun lo hlo s₁ s₂ ⟨h1, h2, h3⟩ hs => by
      have hslot : ep7_HT I T p b (min (ep7_f I p (ep7_V s₁.store p b) (N * d.eval + lo)) (N - lo))
          (ep7_V s₁.store p b) ((bindIdx p ⟨b, eighSlotOff n d (IExp.var lo)⟩
          (n - IExp.var lo) fun k => ep7_downSlot p mm qr n L F d par Lv Su Sg Ma Ua Qa Ea b Kd Kp
            t one two half negone sqh lo k).run) (c + 0)
          (fun V => V = ep7_V s₁.store p b ∨
            (2 ≤ min (ep7_f I p (ep7_V s₁.store p b) (N * d.eval + lo)) (N - lo) ∧
            ep7_RN I p (ep7_V s₁.store p b) (N * (d.eval + 1) + lo)
              (min (ep7_f I p (ep7_V s₁.store p b) (N * d.eval + lo)) (N - lo)) V)) := by
        apply ep7_ht_run
        apply ep7_ht_bindIdxReadK _ fun V h => ep7_ht_skipK h
        have e1 : (eighSlotOff n d (IExp.var lo)).eval = N * d.eval + lo := by simp [eighSlotOff, N]
        have e2 : (eighSlotOff n (d + 1) (IExp.var lo)).eval = N * (d.eval + 1) + lo := by
          simp [eighSlotOff, N]
        have e3 : (n - IExp.var lo).eval = N - lo := by simp [N]
        rw [e1, e3]
        have := ep7_ht_slot (I := I) (T := T) (p := p) (b := b) (V₀ := ep7_V s₁.store p b)
          (mm := mm) (qr := qr) (n := n) (L := L) (F := F) (d := d) (par := par) (Lv := Lv)
          (Su := Su) (Sg := Sg) (one := one) (two := two) (half := half) (negone := negone)
          (sqh := sqh) hMa hUa hQa hEa hKd hKp ht lo
          (min (ep7_f I p (ep7_V s₁.store p b) (N * d.eval + lo)) (N - lo)) le_rfl
        rw [e2] at this
        exact this
      obtain ⟨a1, a2⟩ := hslot hT hch s₁ s₂ h1 rfl hs
      rw [Nat.add_zero] at a1
      have h3' := h3
      obtain ⟨C, -, -, hfr, -⟩ := h3'
      have hg : ep7_f I p (ep7_V s₁.store p b) (N * d.eval + lo) = g₀ lo := by
        simp only [g₀, ep7_f]; rw [hfr _ (Or.inl (by rw [Nat.mul_succ]; omega))]
      refine ⟨by rw [ep7_size hs]; exact h1, ?_, ep7_inv_step hlit htn hNB hlo hpk h3 a2⟩
      rw [Finset.sum_range_succ, Nat.mul_add]
      have : T (min (ep7_f I p (ep7_V s₁.store p b) (N * d.eval + lo)) (N - lo)) ≤ T (g₀ lo) :=
        hT (by rw [hg]; exact min_le_left _ _)
      have := Nat.mul_le_mul_left c this
      omega) hex
  obtain ⟨-, h2, h3⟩ := this
  refine ⟨h2.trans (Nat.add_le_add_left (Nat.mul_le_mul_left c ?_) _), h3⟩
  have := ep7_packed_sum hT hTs 0 hpk
  rwa [← Finset.range_eq_Ico, Nat.sub_zero] at this

private theorem ep7_ht_down {dec : P → K → ℝ} {B : ℕ} (hlit : IsExactIntLit dec I.sem B)
    (htn : IsExactToNat dec I.sem) {mm qr : ι} {n L F d : IExp ℕ}
    {par Lv Su Sg Ma Ua Qa Ea Kd Kp : ℕ} {one two half negone sqh : Cell ℕ ℕ}
    {V₀ : ℕ → Option K} (hLv : Lv ≠ b) (hSu : Su ≠ b) (hSg : Sg ≠ b) (hMa : Ma ≠ b)
    (hUa : Ua ≠ b) (hQa : Qa ≠ b) (hEa : Ea ≠ b) (hKd : Kd ≠ b) (hKp : Kp ≠ b)
    (hNB : n.eval ≤ B) (hTs : ∀ a b, T a + T b ≤ T (a + b))
    (hpk : ep7_Packed (fun j => ep7_f I p V₀ (n.eval * d.eval + j)) 0 n.eval)
    (hz : ∀ j, j < n.eval → ep7_f I p V₀ (n.eval * (d.eval + 1) + j) = 0) :
    ep7_HT I T p b n.eval V₀ (eighDownLevel p mm qr n L F d par Lv Su Sg Ma Ua Qa Ea b Kd Kp one
      two half negone sqh).run (2 * F.eval + 9) (ep7_Inv I p V₀ n.eval d.eval n.eval) := by
  unfold eighDownLevel
  apply ep7_ht_run
  apply ep7_ht_mono (hm := le_rfl) (hQ := fun _ h => h)
  · apply ep7_ht_scopeK
    · apply ep7_ht_run
      ep7_ht_tac
      exact ep7_ht_forRangeK (ep7_ht_downLoop hlit htn hMa hUa hQa hEa hKd hKp (by omega) hNB hTs
        hpk hz) fun V h => ep7_ht_skipK h
    · intro V h; exact ep7_ht_skipK h
  · simp only [Nat.add_zero, Nat.zero_add]
    omega

/-- the body of a slot of an upward level, at the size `k` it reads -/
private def ep7_upSlot (p : P) (mm : ι) (n d : IExp ℕ) (Ua Qa Ea Kd Kp t : ℕ) (lo k : ℕ) :
    Builder P ι ℕ ℕ Unit :=
  eighWhen (IExp.var k) <| bindIdx p ⟨Kd, eighSlotOff n d (IExp.var lo)⟩ 4 fun c => do
    eighWhen (eighEqInd (IExp.var c) 2) do
      zcopy p (IExp.var k) (IExp.var k) Ua (eighBlockOff n (d + 1) (IExp.var lo)) Ua
        (eighBlockOff n d (IExp.var lo))
      forRange (IExp.var k) fun i => ins (.bin p .add ⟨Ea, eighSlotOff n d (IExp.var lo) + .var i⟩
        ⟨Ea, eighSlotOff n (d + 1) (IExp.var lo) + .var i⟩ ⟨t, 0⟩)
    eighWhen (eighEqInd (IExp.var c) 3) do
      zcopy p (IExp.var k) (IExp.var k) Ua (eighBlockOff n (d + 1) (IExp.var lo)) Ua
        (eighBlockOff n d (IExp.var lo))
      forRange (IExp.var k) fun i => ins (.bin p .add ⟨Ea, eighSlotOff n d (IExp.var lo) + .var i⟩
        ⟨Ea, eighSlotOff n (d + 1) (IExp.var lo) + .var i⟩ ⟨t, 1⟩)
    eighWhen (eighEqInd (IExp.var c) 4) <|
      bindIdx p ⟨Kp, eighSlotOff n d (IExp.var lo)⟩ (IExp.var k) fun kp => do
        let qo := eighBlockOff n d (IExp.var lo)
        stmt (.kcall mm p [IExp.var k, IExp.var kp, IExp.var kp]
          [(Qa, qo), (Ua, eighBlockOff n (d + 1) (IExp.var lo))]
          [(Ua, eighBlockOff n d (IExp.var lo))])
        stmt (.kcall mm p [IExp.var k, IExp.var k - IExp.var kp, IExp.var k - IExp.var kp]
          [(Qa, qo + 2 * (IExp.var k * IExp.var kp)),
            (Ua, eighBlockOff n (d + 1) (IExp.var lo + IExp.var kp))]
          [(Ua, eighBlockOff n d (IExp.var lo) + 2 * (IExp.var k * IExp.var kp))])
        forRange (IExp.var kp) fun j => ins (.bin p .add
          ⟨Ea, eighSlotOff n d (IExp.var lo) + .var j⟩
          ⟨Ea, eighSlotOff n (d + 1) (IExp.var lo) + .var j⟩ ⟨t, 0⟩)
        forRange (IExp.var k - IExp.var kp) fun j => ins (.bin p .sub
          ⟨Ea, eighSlotOff n d (IExp.var lo) + IExp.var kp + .var j⟩
          ⟨Ea, eighSlotOff n (d + 1) (IExp.var lo) + IExp.var kp + .var j⟩ ⟨t, 0⟩)

private theorem ep7_bw_upSlot {mm : ι} {n d : IExp ℕ} {Ua Qa Ea Kd Kp t : ℕ} (hUa : Ua ≠ b)
    (hEa : Ea ≠ b) (lo k : ℕ) :
    ep7_BW I T p b k (ep7_upSlot p mm n d Ua Qa Ea Kd Kp t lo k) 2 := by
  unfold ep7_upSlot
  apply ep7_bw_mono
  · dsimp only
    ep7_bw_tac
  · simp

private theorem ep7_ht_upLoop {mm : ι} {n d : IExp ℕ} {Ua Qa Ea Kd Kp t : ℕ} {V₀ : ℕ → Option K}
    (hUa : Ua ≠ b) (hEa : Ea ≠ b) (hTs : ∀ a b, T a + T b ≤ T (a + b))
    (hpk : ep7_Packed (fun j => ep7_f I p V₀ (n.eval * d.eval + j)) 0 n.eval) :
    ep7_HT I T p b n.eval V₀ (.loop n fun lo => (bindIdx p ⟨b, eighSlotOff n d (IExp.var lo)⟩
      (n - IExp.var lo) fun k => ep7_upSlot p mm n d Ua Qa Ea Kd Kp t lo k).run) 2 (· = V₀) := by
  intro hT hch st st' hb hV hex
  set N := n.eval
  set g₀ : ℕ → ℕ := fun j => ep7_f I p V₀ (N * d.eval + j)
  have := forall_of_exec_loop_eq_some I (fun lo s => b < s.store.size ∧
      Finsupp.weight (ep7_wt T) s.cnt ≤ Finsupp.weight (ep7_wt T) st.cnt +
        2 * ∑ j ∈ Finset.range lo, T (g₀ j) ∧ ep7_V s.store p b = V₀)
    ⟨hb, by simp, hV⟩
    (fun lo hlo s₁ s₂ ⟨h1, h2, h3⟩ hs => by
      have hslot : ep7_HT I T p b (min (ep7_f I p V₀ (N * d.eval + lo)) (N - lo))
          V₀ ((bindIdx p ⟨b, eighSlotOff n d (IExp.var lo)⟩
          (n - IExp.var lo) fun k => ep7_upSlot p mm n d Ua Qa Ea Kd Kp t lo k).run) (2 + 0)
          (· = V₀) := by
        apply ep7_ht_run
        apply ep7_ht_bindIdxReadK _ fun V h => ep7_ht_skipK h
        have e1 : (eighSlotOff n d (IExp.var lo)).eval = N * d.eval + lo := by simp [eighSlotOff, N]
        have e3 : (n - IExp.var lo).eval = N - lo := by simp [N]
        rw [e1, e3]
        exact ep7_sf_run (ep7_bw_upSlot hUa hEa lo _) V₀
      obtain ⟨a1, a2⟩ := hslot hT hch s₁ s₂ h1 h3 hs
      rw [Nat.add_zero] at a1
      refine ⟨by rw [ep7_size hs]; exact h1, ?_, a2⟩
      rw [Finset.sum_range_succ, Nat.mul_add]
      have : T (min (ep7_f I p V₀ (N * d.eval + lo)) (N - lo)) ≤ T (g₀ lo) :=
        hT (min_le_left _ _)
      omega) hex
  obtain ⟨-, h2, h3⟩ := this
  refine ⟨h2.trans (Nat.add_le_add_left (Nat.mul_le_mul_left 2 ?_) _), h3⟩
  have := ep7_packed_sum hT hTs 0 hpk
  rwa [← Finset.range_eq_Ico, Nat.sub_zero] at this

private theorem ep7_ht_up {mm : ι} {n d : IExp ℕ} {Lv Ua Qa Ea Kd Kp : ℕ} {two : Cell ℕ ℕ}
    {V₀ : ℕ → Option K} (hUa : Ua ≠ b) (hEa : Ea ≠ b) (hTs : ∀ a b, T a + T b ≤ T (a + b))
    (hpk : ep7_Packed (fun j => ep7_f I p V₀ (n.eval * d.eval + j)) 0 n.eval) :
    ep7_HT I T p b n.eval V₀ (eighUpLevel p mm n d Lv Ua Qa Ea b Kd Kp two).run 2 (· = V₀) := by
  unfold eighUpLevel
  apply ep7_ht_run
  apply ep7_ht_mono (hm := le_rfl) (hQ := fun _ h => h)
  · apply ep7_ht_scopeK
    · apply ep7_ht_run
      ep7_ht_tac
      exact ep7_ht_forRangeK (ep7_ht_upLoop hUa hEa hTs hpk) fun V h => ep7_ht_skipK h
    · intro V h; exact ep7_ht_skipK h
  · simp only [Nat.add_zero, Nat.zero_add]
    omega

private theorem ep7_bw_bottom {n D : IExp ℕ} {Ua Ea : ℕ} (hUa : Ua ≠ b) (hEa : Ea ≠ b) :
    ep7_BW I T p b m (eighBottomLevel p n D Ua Ea b) 0 := by
  unfold eighBottomLevel; ep7_z

private theorem ep7_ht_zeroLoop {M : IExp ℕ} {V₀ : ℕ → Option K} :
    ep7_HT I T p b m V₀ (.loop M fun w => (ins (.litIdx p ⟨b, IExp.var w⟩ 0)).run) 0
      (fun V => ∀ w, V w = if w < M.eval then I.sem.lit p 0 else V₀ w) := by
  intro hT hch st st' hb hV hex
  have := forall_of_exec_loop_eq_some I (fun i s => b < s.store.size ∧
      Finsupp.weight (ep7_wt T) s.cnt ≤ Finsupp.weight (ep7_wt T) st.cnt ∧
      ∀ w, ep7_V s.store p b w = if w < i then I.sem.lit p 0 else V₀ w)
    ⟨hb, le_rfl, fun w => by simp [hV]⟩
    (fun i _ s₁ s₂ ⟨h1, h2, h3⟩ hs => by
      have hl : ep7_HT I T p b m (ep7_V s₁.store p b)
          (.seq (.instr (.litIdx p ⟨b, IExp.var i⟩ 0)) .skip) (0 + 0)
          (· = Function.update (ep7_V s₁.store p b) (IExp.var i).eval
            (I.sem.lit p ((0 : IExp ℕ).eval : ℚ))) :=
        ep7_ht_seq ep7_ht_litIdx fun V₁ h => ep7_ht_skip h
      obtain ⟨a1, a2⟩ := hl hT hch s₁ s₂ h1 rfl hs
      refine ⟨by rw [ep7_size hs]; exact h1, by omega, fun w => ?_⟩
      rw [a2]
      by_cases hw : w = i
      · subst hw; simp
      · rw [Function.update_of_ne (by simpa using hw), h3 w]
        by_cases hwi : w < i
        · simp [hwi, show w < i + 1 by omega]
        · simp [hwi, show ¬ w < i + 1 by omega]) hex
  obtain ⟨-, h2, h3⟩ := this
  exact ⟨by omega, h3⟩

private theorem ep7_ht_downPass {dec : P → K → ℝ} {B : ℕ} (hlit : IsExactIntLit dec I.sem B)
    (htn : IsExactToNat dec I.sem) {mm qr : ι} {n L F : IExp ℕ}
    {par Lv Su Sg Ma Ua Qa Ea Kd Kp : ℕ} {one two half negone sqh : Cell ℕ ℕ}
    {V₀ : ℕ → Option K} (hLv : Lv ≠ b) (hSu : Su ≠ b) (hSg : Sg ≠ b) (hMa : Ma ≠ b)
    (hUa : Ua ≠ b) (hQa : Qa ≠ b) (hEa : Ea ≠ b) (hKd : Kd ≠ b) (hKp : Kp ≠ b)
    (hNB : n.eval ≤ B) (hTs : ∀ a b, T a + T b ≤ T (a + b))
    (hpk : ep7_Packed (fun j => ep7_f I p V₀ (n.eval * 0 + j)) 0 n.eval)
    (hz : ∀ e, 0 < e → e ≤ L.eval + 1 → ∀ j, j < n.eval → ep7_f I p V₀ (n.eval * e + j) = 0) :
    ep7_HT I T p b n.eval V₀ (.loop (L + 1) fun d => (eighDownLevel p mm qr n L F (IExp.var d)
      par Lv Su Sg Ma Ua Qa Ea b Kd Kp one two half negone sqh).run)
      ((L.eval + 1) * (2 * F.eval + 9))
      (fun V => ∀ e ≤ L.eval + 1, ep7_Packed (fun j => ep7_f I p V (n.eval * e + j)) 0 n.eval) := by
  intro hT hch st st' hb hV hex
  have := forall_of_exec_loop_eq_some I (fun d s => b < s.store.size ∧
      Finsupp.weight (ep7_wt T) s.cnt ≤
        Finsupp.weight (ep7_wt T) st.cnt + d * ((2 * F.eval + 9) * T n.eval) ∧
      (∀ e ≤ d, ep7_Packed (fun j => ep7_f I p (ep7_V s.store p b) (n.eval * e + j)) 0 n.eval) ∧
      (∀ e, d < e → e ≤ L.eval + 1 → ∀ j, j < n.eval →
        ep7_f I p (ep7_V s.store p b) (n.eval * e + j) = 0))
    ⟨hb, by simp, fun e he => by
      rw [Nat.le_zero.mp he, hV]; exact hpk, fun e h1 h2 => by rw [hV]; exact hz e h1 h2⟩
    (fun d hd s₁ s₂ ⟨h1, h2, h3, h4⟩ hs => by
      have hdn := ep7_ht_down (I := I) (T := T) (p := p) (b := b) (mm := mm) (qr := qr) (n := n)
        (L := L) (F := F) (d := IExp.var d) (par := par) (one := one) (two := two) (half := half)
        (negone := negone) (sqh := sqh) hlit htn hLv hSu hSg hMa hUa hQa hEa hKd hKp hNB hTs
        (h3 d le_rfl) (h4 (d + 1) (by omega) (by simpa using hd))
      obtain ⟨a1, ⟨C, hC1, hC2, hfr, hpC, -, -⟩⟩ := hdn hT hch s₁ s₂ h1 rfl hs
      simp only [IExp.eval_var] at hfr hpC
      have hCN : C = n.eval := by omega
      rw [hCN] at hpC
      refine ⟨by rw [ep7_size hs]; exact h1, by rw [Nat.succ_mul]; omega, fun e he => ?_,
        fun e h5 h6 j hj => ?_⟩
      · rcases Nat.lt_or_ge d e with hde | hde
        · have : e = d + 1 := by omega
          subst this; exact hpC
        · refine ep7_packed_congr (h3 e hde) fun j _ hj => ?_
          have : n.eval * e ≤ n.eval * d := Nat.mul_le_mul_left n.eval hde
          simp only [ep7_f]; rw [hfr _ (Or.inl (by rw [Nat.mul_succ]; omega))]
      · have : n.eval * (d + 2) ≤ n.eval * e := Nat.mul_le_mul_left n.eval (by omega)
        have h7 := h4 e (by omega) h6 j hj
        have e1 : n.eval * (d + 2) = n.eval * d + n.eval + n.eval := by ring
        have e2 : n.eval * (d + 1) = n.eval * d + n.eval := by ring
        simp only [ep7_f] at h7 ⊢; rw [hfr _ (Or.inr (by omega))]
        exact h7) hex
  obtain ⟨-, h2, h3, -⟩ := this
  refine ⟨?_, h3⟩
  simp only [IExp.eval_add, IExp.eval_ofNat] at h2
  rw [Nat.mul_assoc]; exact h2

private theorem ep7_ht_upPass {mm : ι} {n L : IExp ℕ} {Lv Ua Qa Ea Kd Kp : ℕ} {two : Cell ℕ ℕ}
    {V₀ : ℕ → Option K} (hUa : Ua ≠ b) (hEa : Ea ≠ b) (hTs : ∀ a b, T a + T b ≤ T (a + b))
    (hpk : ∀ e ≤ L.eval, ep7_Packed (fun j => ep7_f I p V₀ (n.eval * e + j)) 0 n.eval) :
    ep7_HT I T p b n.eval V₀ (.loop (L + 1) fun d' => (eighUpLevel p mm n (L - IExp.var d') Lv Ua
      Qa Ea b Kd Kp two).run) ((L.eval + 1) * 2) (· = V₀) := by
  intro hT hch st st' hb hV hex
  have := forall_of_exec_loop_eq_some I (fun d s => b < s.store.size ∧
      Finsupp.weight (ep7_wt T) s.cnt ≤ Finsupp.weight (ep7_wt T) st.cnt + d * (2 * T n.eval) ∧
      ep7_V s.store p b = V₀)
    ⟨hb, by simp, hV⟩
    (fun d hd s₁ s₂ ⟨h1, h2, h3⟩ hs => by
      have hup := ep7_ht_up (I := I) (T := T) (p := p) (b := b) (mm := mm) (n := n)
        (d := L - IExp.var d) (Lv := Lv) (Qa := Qa) (Kd := Kd) (Kp := Kp) (two := two) hUa hEa hTs
        (hpk (L - IExp.var d).eval (by simp))
      obtain ⟨a1, a2⟩ := hup hT hch s₁ s₂ h1 h3 hs
      exact ⟨by rw [ep7_size hs]; exact h1, by rw [Nat.succ_mul]; omega, a2⟩) hex
  obtain ⟨-, h2, h3⟩ := this
  refine ⟨?_, h3⟩
  simp only [IExp.eval_add, IExp.eval_ofNat] at h2
  rw [Nat.mul_assoc]; exact h2

/-- a cost bound for a run before the tracked buffer is allocated, `j` allocations ahead -/
private def ep7_HTpre (I : Interp P ι K (OpCount P ι)) (T : ℕ → ℕ) (b m j : ℕ) (s : Stmt P ι ℕ ℕ)
    (c : ℕ) : Prop :=
  Monotone T → (∀ κ, I.charge κ = Finsupp.single κ 1) → ∀ st st' : St P K (OpCount P ι),
    st.store.size + j = b → exec I s st = some st' →
    Finsupp.weight (ep7_wt T) st'.cnt ≤ Finsupp.weight (ep7_wt T) st.cnt + c * T m

private theorem ep7_pre_allocSucc {j : ℕ} {q : P} {len : IExp ℕ} {f : ℕ → Builder P ι ℕ ℕ Unit}
    {k : Unit → Stmt P ι ℕ ℕ} {c : ℕ}
    (h : ∀ h, h + (j + 1) = b → ep7_HTpre I T b m j (ep7_run (f h) k) c) :
    ep7_HTpre I T b m (j + 1) (ep7_run (alloc q len >>= f) k) c := by
  intro hT hch st st' hb hex
  change exec I (.alloc q len fun h => ep7_run (f h) k) st = some st' at hex
  rw [exec_alloc] at hex
  obtain ⟨st₂, h₂, rfl⟩ := Option.map_eq_some_iff.mp hex
  have := h st.store.size hb hT hch _ st₂ (by simp only [Array.size_push]; omega) h₂
  exact this

private theorem ep7_pre_allocZero {q : P} {len : IExp ℕ} {f : ℕ → Builder P ι ℕ ℕ Unit}
    {k : Unit → Stmt P ι ℕ ℕ} {c : ℕ} {Q : (ℕ → Option K) → Prop}
    (h : ep7_HT I T p b m (fun _ => none) (ep7_run (f b) k) c Q) :
    ep7_HTpre I T b m 0 (ep7_run (alloc q len >>= f) k) c := by
  intro hT hch st st' hb hex
  change exec I (.alloc q len fun h => ep7_run (f h) k) st = some st' at hex
  rw [exec_alloc] at hex
  obtain ⟨st₂, h₂, rfl⟩ := Option.map_eq_some_iff.mp hex
  rw [Nat.add_zero] at hb
  subst hb
  have := (h hT hch _ st₂ (by simp) (by
    funext i; simp only [ep7_V]; rw [Store.read_push_size]
    rw [Array.getElem?_replicate]; split_ifs <;> rfl) h₂).1
  exact this

private theorem ep7_pre_scope {j : ℕ} {x : Builder P ι ℕ ℕ Unit} {c : ℕ}
    (h : ep7_HTpre I T b m j (ep7_run x fun _ => .skip) c) :
    ep7_HTpre I T b m j (scope x).run c := by
  intro hT hch st st' hb hex
  change exec I (.seq (ep7_run x fun _ => .skip) .skip) st = some st' at hex
  rw [exec_seq_skip] at hex
  exact h hT hch st st' hb hex

omit [DecidableEq P] in
private theorem ep7_init {dec : P → K → ℝ} (N ℓ₀ : ℕ) (hlit : IsExactIntLit dec I.sem (N + 4))
    (htn : IsExactToNat dec I.sem) {V₀ V₁ : ℕ → Option K}
    (h₁ : ∀ w, V₁ w = if w < N * (ℓ₀ + 1 + 1) + 1 then I.sem.lit p 0 else V₀ w) :
    ep7_Packed (fun j => ep7_f I p (Function.update V₁ 0 (I.sem.lit p (N : ℚ))) (N * 0 + j)) 0 N ∧
      ∀ e, 0 < e → e ≤ ℓ₀ + 1 → ∀ j, j < N →
        ep7_f I p (Function.update V₁ 0 (I.sem.lit p (N : ℚ))) (N * e + j) = 0 := by
  have hz : ∀ i, i ≠ 0 → i < N * (ℓ₀ + 1 + 1) + 1 →
      ep7_f I p (Function.update V₁ 0 (I.sem.lit p (N : ℚ))) i = 0 := by
    intro i hi hiM
    rw [ep7_f_update, if_neg hi]
    unfold ep7_f; rw [h₁, if_pos hiM]
    exact_mod_cast ep7_lit_toNat (j := 0) hlit htn (Nat.zero_le _)
  have hbig : ∀ e ≤ ℓ₀ + 1, ∀ j < N, N * e + j < N * (ℓ₀ + 1 + 1) + 1 := by
    intro e he j hj
    have : N * e ≤ N * (ℓ₀ + 1) := Nat.mul_le_mul_left N he
    have : N * (ℓ₀ + 1 + 1) = N * (ℓ₀ + 1) + N := Nat.mul_succ _ _
    omega
  have hf0 : ep7_f I p (Function.update V₁ 0 (I.sem.lit p (N : ℚ))) 0 = N := by
    rw [ep7_f_update, if_pos rfl]; exact ep7_lit_toNat hlit htn (by omega)
  have hb0 : ∀ j < N, j < N * (ℓ₀ + 1 + 1) + 1 := fun j hj => by simpa using hbig 0 (by omega) j hj
  refine ⟨fun j _ hj hpos => ?_, fun e he0 he j hj => hz _ ?_ (hbig e he j hj)⟩
  · dsimp only at hpos ⊢
    rw [Nat.mul_zero, Nat.zero_add] at hpos ⊢
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [hf0]
      refine ⟨by omega, fun i hi1 hi2 => ?_⟩
      rw [Nat.zero_add]
      exact hz i (by omega) (hb0 i (by omega))
    · rw [hz j (by omega) (hb0 j hj)] at hpos
      omega
  · have : N * e ≥ N := Nat.le_mul_of_pos_right N he0
    omega

set_option maxHeartbeats 2000000 in
-- the whole program is unfolded and every block is checked in one proof
private theorem ep7_main {dec : P → K → ℝ} {mm qr : ι} (N ℓ₀ F : ℕ)
    (hlit : IsExactIntLit dec I.sem (N + 4)) (htn : IsExactToNat dec I.sem)
    (hTs : ∀ a b, T a + T b ≤ T (a + b)) (hb5 : 5 ≤ b) :
    ep7_HTpre I T b N 5 (eighProg p mm qr (.const N) (.const ℓ₀) (.const F) 0 1 2 3).run
      ((ℓ₀ + 1) * (2 * F + 9) + (ℓ₀ + 1) * 2) := by
  unfold eighProg
  apply ep7_pre_scope
  dsimp only
  apply ep7_pre_allocSucc; intro hc hhc
  apply ep7_pre_allocSucc; intro hMa hhMa
  apply ep7_pre_allocSucc; intro hUa hhUa
  apply ep7_pre_allocSucc; intro hQa hhQa
  apply ep7_pre_allocSucc; intro hEa hhEa
  apply ep7_pre_allocZero (p := p) (Q := fun _ => True)
  apply ep7_ht_mono (hm := le_rfl) (hQ := fun _ _ => trivial)
  · ep7_ht_tac
    apply ep7_ht_bindK
    apply ep7_ht_forRangeK ep7_ht_zeroLoop
    · intro V₁ h₁
      apply ep7_ht_bindK
      apply ep7_ht_litK
      ep7_ht_tac
      apply ep7_ht_bindK
      obtain ⟨hpk, hz⟩ := ep7_init (I := I) (p := p) N ℓ₀ hlit htn (V₀ := fun _ => none)
        (V₁ := V₁) (by simpa using h₁)
      apply ep7_ht_forRangeK (ep7_ht_downPass hlit htn (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by simp) hTs (by simpa using hpk)
        (by simpa using hz))
      · intro V₂ h₂
        apply ep7_ht_bwK (ep7_bw_bottom (by omega) (by omega))
        · apply ep7_ht_bindK
          apply ep7_ht_forRangeK (ep7_ht_upPass (by omega) (by omega) hTs fun e he =>
            h₂ e (by simp at he ⊢; omega))
          · intro V₃ h₃
            ep7_ht_tac
            exact ep7_ht_skipK (Q := fun _ => True) trivial
  · simp only [IExp.eval_const, Nat.zero_add, Nat.add_zero]
    exact le_rfl

end EP7

/-- **The kernel cost of the registered tree, weighted** ([Shah2024, Section 4], the operation count
of Theorem 4.2): for a cost $T$ of a kernel call by its largest dimension that is monotone and
superadditive ($T(a) + T(b) \le T(a + b)$, as a convex $T$ with $T(0) = 0$ is), under the standard
charge, exact integer literals up to $N + 4$ and the exact floor conversion (the sizes, kinds and
$k_+$ are control data in rounded cells, read back by binders: without the contracts a slot that
starts no node can read back a size $\ge 1$, design note §8), every successful run of
`NLAlib.eighProg.compiled` at the sizes $N$ and $(\ell_0, F)$ adds
at most $(\ell_0 + 1)(2F + 12)\,T(N)$ to the weighted kernel count: per level, the nodes have sizes
summing to at most $N$, each with at most $2F + 12$ kernel calls of largest dimension at most its
size. The static bound `NLAlib.eighCount` charges every size at every slot, a factor of about $N^2$
more. No printed source. -/
theorem eighProg.weight_le_of_exec_compiled {mm qr : ι} {I : Interp P ι K (OpCount P ι)}
    (hc : ∀ k, I.charge k = Finsupp.single k 1) {dec : P → K → ℝ} (p : P) (N ℓ₀ F : ℕ)
    (hlit : IsExactIntLit dec I.sem (N + 4)) (htn : IsExactToNat dec I.sem) (T : ℕ → ℕ)
    (hT : Monotone T) (hTsup : ∀ a b, T a + T b ≤ T (a + b)) {st st' : St P K (OpCount P ι)}
    (h : (eighProg.compiled p mm qr).exec I N ![ℓ₀, F] st = some st') :
    Finsupp.weight (fun κ : OpKind P ι => match κ with
        | .kcall _ _ ds => T (ds.foldr max 0)
        | _ => 0) st'.cnt ≤
      Finsupp.weight (fun κ : OpKind P ι => match κ with
        | .kcall _ _ ds => T (ds.foldr max 0)
        | _ => 0) st.cnt + (ℓ₀ + 1) * (2 * F + 12) * T N := by
  rw [Prog.exec_eq_exec_toStmt, eighProg.toStmt_compiled] at h
  have h' : exec I (eighProg p mm qr (.const N) (.const ℓ₀) (.const F) 0 1 2 3).run st =
      some st' := h
  change Finsupp.weight (ep7_wt T) st'.cnt ≤
    Finsupp.weight (ep7_wt T) st.cnt + (ℓ₀ + 1) * (2 * F + 12) * T N
  have := ep7_main (I := I) (T := T) (p := p) (b := st.store.size + 5) (mm := mm) (qr := qr)
    N ℓ₀ F hlit htn hTsup (by omega) hT hc st st' rfl h'
  refine this.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ ?_) _)
  rw [← Nat.mul_add]
  exact Nat.mul_le_mul_left _ (by omega)

end NLAlib
