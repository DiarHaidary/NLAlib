/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.RoutineAlloc
public import NLAlib.Matrix.Computation.SpectralBisectionProgram.BottomLevel
public import NLAlib.Matrix.Computation.SpectralBisectionProgram.DownLevel
public import NLAlib.Matrix.Computation.SpectralBisectionProgram.UpLevel
public import NLAlib.Matrix.Computation.SpectralBisectionProgram.Transfer

/-!
# The spectral bisection program as a routine specification

Under kernels that are routines on pairs, a semantics that decides flags, exact integer literals up
to $n + 4$ and the exact floor conversion, `NLAlib.eighProg` meets one routine specification in
every mode (`NLAlib.spec_eighProg`), built procedurally: the eleven allocations by a chain of named
states (`NLAlib.Computation.spec_allocBind_chain`), the constants, the root, the downward pass, the
spent level, the upward pass and the copies out by the call rule, the two passes as loops over the
level specifications with the arenas as their invariants. In the liberal mode it is the refinement:
every successful run writes exactly `NLAlib.eigh` on the machine of the interpretation
(`NLAlib.eighTapeMachine`) with the tree of samples at the slots. In the total mode, under the
standard model, it is success (`NLAlib.exists_exec_eighProg`).

## Main results

* `NLAlib.spec_eighProg`: the routine specification of the driver.
* `NLAlib.holds_of_exec_eighProg`: the refinement (partial equality) for the builder.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}

/-! ### The passes -/

omit [AddMonoid C] [Inhabited K] in
/-- A cell that is not an output or eigenvalue cell of depth $d$ reads the same after a change
confined to the outputs and eigenvalues of depth $d$. -/
theorem read_eq_of_modifies_eighOutFp {H : EighArenas} (hnd : H.handles.Nodup) {n d b i : ℕ}
    {s s' : Store P K} {q : P}
    (hm : Modifies [(H.Ua, 2 * (n * n) * d, 2 * (n * n)), (H.Ea, n * d, n)] s s')
    (hb : ¬ ((b = H.Ua ∨ b = H.Ea) ∧ H.LevelCell n d b i)) :
    s'.read q b i = s.read q b i := by
  obtain ⟨hUE, -⟩ := H.ua_ne_ea_and_of_nodup hnd
  exact hm.2 q b i (by unfold EighArenas.LevelCell at hb; fp_omega [hb, hUE])

/-- The blocks one level of the downward pass may write lie in the arenas. -/
theorem eighDownFp_sub_arena {H : EighArenas} {n d D Su Sg : ℕ} (hd : d < D) :
    ∀ x ∈ eighDownFp H n d Su Sg, ∃ y ∈ eighArenaFp H n D Su Sg,
      x.1 = y.1 ∧ y.2.1 ≤ x.2.1 ∧ x.2.1 + x.2.2 ≤ y.2.1 + y.2.2 := by
  have f1 : 2 * (n * n) * d + 2 * (n * n) ≤ 2 * (n * n) * (D + 1) := by
    have := Nat.mul_le_mul_left (2 * (n * n)) (show d + 1 ≤ D + 1 by omega); nlinarith
  have f2 : 2 * (n * n) * (d + 1) + 2 * (n * n) ≤ 2 * (n * n) * (D + 1) := by
    have := Nat.mul_le_mul_left (2 * (n * n)) (show d + 1 + 1 ≤ D + 1 by omega); nlinarith
  have f3 : n * d + n ≤ n * (D + 1) := by
    have := Nat.mul_le_mul_left n (show d + 1 ≤ D + 1 by omega); nlinarith
  have f4 : n * (d + 1) + n ≤ n * (D + 1) := by
    have := Nat.mul_le_mul_left n (show d + 1 + 1 ≤ D + 1 by omega); nlinarith
  intro x hx
  simp only [eighDownFp, eighRecordBlocks, eighLevelBlocks, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  rcases hx with ((rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)) |
    rfl | rfl
  · exact ⟨(H.Qa, 0, 2 * (n * n) * (D + 1)), by simp [eighArenaFp], rfl, Nat.zero_le _, by
      dsimp only; omega⟩
  · exact ⟨(H.Ua, 0, 2 * (n * n) * (D + 1)), by simp [eighArenaFp], rfl, Nat.zero_le _, by
      dsimp only; omega⟩
  · exact ⟨(H.Ea, 0, n * (D + 1)), by simp [eighArenaFp], rfl, Nat.zero_le _, by
      dsimp only; omega⟩
  · exact ⟨(H.Kd, 0, n * (D + 1)), by simp [eighArenaFp], rfl, Nat.zero_le _, by
      dsimp only; omega⟩
  · exact ⟨(H.Kp, 0, n * (D + 1)), by simp [eighArenaFp], rfl, Nat.zero_le _, by
      dsimp only; omega⟩
  · exact ⟨(H.Ma, 0, 2 * (n * n) * (D + 1)), by simp [eighArenaFp], rfl, Nat.zero_le _, by
      dsimp only; omega⟩
  · exact ⟨(H.Ua, 0, 2 * (n * n) * (D + 1)), by simp [eighArenaFp], rfl, Nat.zero_le _, by
      dsimp only; omega⟩
  · exact ⟨(H.Qa, 0, 2 * (n * n) * (D + 1)), by simp [eighArenaFp], rfl, Nat.zero_le _, by
      dsimp only; omega⟩
  · exact ⟨(H.Ea, 0, n * (D + 1)), by simp [eighArenaFp], rfl, Nat.zero_le _, by
      dsimp only; omega⟩
  · exact ⟨(H.Sz, 0, n * (D + 1) + 1), by simp [eighArenaFp], rfl, Nat.zero_le _, by
      dsimp only; omega⟩
  · exact ⟨(H.Kd, 0, n * (D + 1)), by simp [eighArenaFp], rfl, Nat.zero_le _, by
      dsimp only; omega⟩
  · exact ⟨(H.Kp, 0, n * (D + 1)), by simp [eighArenaFp], rfl, Nat.zero_le _, by
      dsimp only; omega⟩
  · exact ⟨(H.Lv, 0, 2 * (D + 1)), by simp [eighArenaFp], rfl, Nat.zero_le _, by
      dsimp only; omega⟩
  · exact ⟨(Su, 0, n), by simp [eighArenaFp], rfl, le_rfl, le_rfl⟩
  · exact ⟨(Sg, 0, 4 * (n * n)), by simp [eighArenaFp], rfl, le_rfl, le_rfl⟩


omit [AddMonoid C] [Inhabited K] in
/-- A cell that is neither a record of depth $d$ nor of depth $d + 1$, nor in the samples, reads
the same after a change confined to the footprint of the level. -/
theorem read_eq_of_modifies_eighDownFp {H : EighArenas} (hnd : H.handles.Nodup) {n d Su Sg b i : ℕ}
    {s s' : Store P K} {q : P} (hm : Modifies (eighDownFp H n d Su Sg) s s') (hSu : b ≠ Su)
    (hSg : b ≠ Sg)
    (hrec : ¬ ((b = H.Qa ∨ b = H.Ua ∨ b = H.Ea ∨ b = H.Kd ∨ b = H.Kp) ∧ H.LevelCell n d b i))
    (hlev : ¬ H.LevelCell n (d + 1) b i) : s'.read q b i = s.read q b i := by
  refine hm.2 q b i fun x hx => ?_
  simp only [eighDownFp, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with (hx | hx) | hx | hx
  · exact (blockDisjoint_eighRecordBlocks_iff hnd).mpr hrec x hx
  · exact (blockDisjoint_eighLevelBlocks_iff.mpr hlev) x hx
  · rw [hx]; exact blockDisjoint_of_fst_ne hSu
  · rw [hx]; exact blockDisjoint_of_fst_ne hSg


/-- **The downward pass** as a routine specification. -/
theorem spec_eighDownLoop {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) (md : Mode) {u : P → ℝ} {dec : P → K → ℝ}
    {safe : P → ℝ → Prop} (p : P) (n ℓ₀ F : ℕ)
    (hsem : md.Needs (IsRelErrSem u dec safe I.sem ∧ (∀ p x, safe p x) ∧ u p < 1))
    (hflag : I.sem.DecidesFlags p)
    (hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y)))
    (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem) (H : EighArenas)
    {par Su Sg c b : ℕ} {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup) (hlt : ∀ x ∈ H.handles ++ [par, c], x < b) :
    RoutineSpec md I (fun st => st.store.size = b ∧ H.Shaped st.store p n (ℓ₀ + 1) ∧
        H.LevelHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
          ⟨n, A, R₀, ε, ℓ₀⟩ 0 ∧
        (∀ e lo, 0 < e → e ≤ ℓ₀ + 1 → lo < n → ReadsIdx I.sem st.store p H.Sz (n * e + lo) 0) ∧
        (st.pos .uniform = 0 ∧ st.pos .gaussian = 0) ∧
        (st.store.read p par 0 = some R₀ ∧ st.store.read p par 2 = some β) ∧
        (st.store.read p c 0 = I.sem.lit p 1 ∧ st.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
          st.store.read p c 2 = some ((eighTapeMachine I p mmR qrR).div
            (eighTapeMachine I p mmR qrR).one ((eighTapeMachine I p mmR qrR).ofNat 2)) ∧
          st.store.read p c 3 = some ((eighTapeMachine I p mmR qrR).neg
            (eighTapeMachine I p mmR qrR).one) ∧
          st.store.read p c 4 = some (I.sem.sqrtHalf p)) ∧
        md.Needs (Writable st.store p Su 0 n ∧ Writable st.store p Sg 0 (4 * (n * n)) ∧
          0 ≤ dec p R₀ ∧ 1 ≤ ℓ₀))
      (forRange (.const ℓ₀ + 1) fun d => eighDownLevel p mm qr (.const n) (.const ℓ₀)
        (.const F) (.var d) par H.Lv Su Sg H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp ⟨c, 0⟩ ⟨c, 1⟩
        ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩)
      (eighArenaFp H n (ℓ₀ + 1) Su Sg) fun _ st' =>
        H.LevelHolds I.sem st'.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
          ⟨n, A, R₀, ε, ℓ₀⟩ (ℓ₀ + 1) ∧
        ∀ e < ℓ₀ + 1, H.LevelHolds I.sem st'.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
            ⟨n, A, R₀, ε, ℓ₀⟩ e ∧
          H.RecordHolds I.sem st'.store p (eighTapeMachine I p mmR qrR) n F R₀ β
            ⟨n, A, R₀, ε, ℓ₀⟩ e := by
  refine (RoutineSpec.forRange_const (m := md) (I := I) (n := IExp.const ℓ₀ + 1)
    (body := fun d => eighDownLevel p mm qr (.const n) (.const ℓ₀) (.const F) (.var d) par H.Lv Su
      Sg H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩)
    (eighArenaFp H n (ℓ₀ + 1) Su Sg) (fun st₀ k st =>
    Modifies (eighArenaFp H n (ℓ₀ + 1) Su Sg) st₀.store st.store ∧
    st.pos .uniform = n * k ∧ st.pos .gaussian = 4 * (n * n) * k ∧
    H.LevelHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ k ∧
    (∀ e < k, H.LevelHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
        ⟨n, A, R₀, ε, ℓ₀⟩ e ∧
      H.RecordHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ e) ∧
    (∀ e lo, k < e → e ≤ ℓ₀ + 1 → lo < n → ReadsIdx I.sem st.store p H.Sz (n * e + lo) 0))
    (fun st ⟨hsz, hH, hlev, hz, hpos, hpar, hc, hN⟩ => ⟨Modifies.refl _ _, by rw [hpos.1]; ring,
      by rw [hpos.2]; ring, hlev, fun e he => absurd he (Nat.not_lt_zero _), hz⟩) ?_).conseq
    (fun st h => h) (fun x hx => hx) (fun st st' _ h => ⟨h.2.2.2.1, fun e he => h.2.2.2.2.1 e he⟩)
  intro st₀ ⟨hsz, hH, hlev, hz, hpos, hpar, hc, hN⟩ k hk
  have hk' : k < ℓ₀ + 1 := hk
  have hnd : H.handles.Nodup := hH.1
  have hSuH : Su ∉ H.handles := not_mem_handles_of_mem hbufs (by simp)
  have hSgH : Sg ∉ H.handles := not_mem_handles_of_mem hbufs (by simp)
  have hS := spec_eighDownLevel hmm hqr md p n ℓ₀ F k (ℓ₀ + 1) hsem hflag hcmp hlit htn H
    (par := par) (Su := Su) (Sg := Sg) (c := c) (b := b) (A := A) (R₀ := R₀) (ε := ε) (β := β)
    hbufs hlt
  refine Spec.of_exec_eq ((hS.spec.with_modifies.sub (fp' := eighArenaFp H n (ℓ₀ + 1) Su Sg)
    (eighDownFp_sub_arena hk')).conseq ?_ (fun x hx => hx) ?_) fun st =>
    exec_eighDownLevel_var p mm qr n ℓ₀ F k par H.Lv Su Sg H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp c st
  · rintro st ⟨hm, hpu, hpg, hlk, hlow, hzk⟩
    have hfr : ∀ q b i, b ∉ H.handles → b ≠ Su → b ≠ Sg →
        st.store.read q b i = st₀.store.read q b i := fun q b i hb h1 h2 =>
      read_eq_of_modifies_eighArenaFp hm hb h1 h2
    have hparH : par ∉ H.handles := not_mem_handles_of_mem hbufs (x := par) (by simp)
    have hcH : c ∉ H.handles := not_mem_handles_of_mem hbufs (x := c) (by simp)
    have h4 := (List.nodup_append.mp hbufs).2.1
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true] at h4
    obtain ⟨⟨hparSu, hparSg, -⟩, ⟨-, hSuc⟩, hSgc, -⟩ := h4
    refine ⟨(Store.size_eq_of_shape_eq hm.1).trans hsz,
      EighArenas.Shaped.of_shape_eq (fun b _ => by rw [hm.1]) hH, hlk, ⟨hpu, hpg⟩,
      ⟨(hfr p par 0 hparH hparSu hparSg).trans hpar.1,
        (hfr p par 2 hparH hparSu hparSg).trans hpar.2⟩,
      ⟨(hfr p c 0 hcH (Ne.symm hSuc) (Ne.symm hSgc)).trans hc.1,
        (hfr p c 1 hcH (Ne.symm hSuc) (Ne.symm hSgc)).trans hc.2.1,
        (hfr p c 2 hcH (Ne.symm hSuc) (Ne.symm hSgc)).trans hc.2.2.1,
        (hfr p c 3 hcH (Ne.symm hSuc) (Ne.symm hSgc)).trans hc.2.2.2.1,
        (hfr p c 4 hcH (Ne.symm hSuc) (Ne.symm hSgc)).trans hc.2.2.2.2⟩,
      hN.mono fun h => ⟨h.1.of_shape_eq hm.1, h.2.1.of_shape_eq hm.1, h.2.2.1, h.2.2.2, hk'⟩⟩
  · rintro st st' ⟨hm, hpu, hpg, hlk, hlow, hzk⟩ ⟨hmd, hnext, hrec, hpu', hpg'⟩
    have F1 : ∀ q b i, (b = H.Ma ∨ b = H.Sz ∨ b = H.Lv) → ¬ H.LevelCell n (k + 1) b i →
        st'.store.read q b i = st.store.read q b i := fun q b i hb hl =>
      read_eq_of_modifies_eighDownFp hnd hmd (fun h => hSuH (h ▸ mem_handles_of_node_arena hb))
        (fun h => hSgH (h ▸ mem_handles_of_node_arena hb))
        (fun h => false_of_node_arena_of_record_arena hnd hb h.1) hl
    have F2 : ∀ e, e < k → ∀ q b i, (b = H.Ua ∨ b = H.Qa ∨ b = H.Ea ∨ b = H.Kd ∨ b = H.Kp) →
        H.LevelCell n e b i → st'.store.read q b i = st.store.read q b i := fun e he q b i hb hl =>
      read_eq_of_modifies_eighDownFp hnd hmd (fun h => hSuH (h ▸ mem_handles_of_record_arena hb))
        (fun h => hSgH (h ▸ mem_handles_of_record_arena hb))
        (fun h => not_levelCell_of_ne hnd (by omega) hl h.2)
        (not_levelCell_of_ne hnd (by omega) hl)
    refine ⟨(hm.trans (hmd.of_sub (eighDownFp_sub_arena hk'))).mono (fun x hx => by simpa using hx),
      by rw [hpu', hpu]; ring, by rw [hpg', hpg]; ring,
      hnext fun lo hlo => hzk (k + 1) lo (Nat.lt_succ_self k) (by omega) hlo, fun e he => ?_,
      fun e lo he1 he2 hlo => ?_⟩
    · have hLe : H.LevelHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
          ⟨n, A, R₀, ε, ℓ₀⟩ e := by
        rcases Nat.lt_succ_iff_lt_or_eq.mp he with he' | rfl
        · exact (hlow e he').1
        · exact hlk
      refine ⟨EighArenas.LevelHolds.of_read_eq (fun q b i hb hi => F1 q b i hb
        (not_levelCell_of_lt hnd he hi)) hLe, ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp he with he' | rfl
      · exact EighArenas.RecordHolds.of_read_eq (fun q b i hb hi => F2 e he' q b i hb hi)
          (hlow e he').2
      · exact hrec
    · have hSz : H.Sz = H.Ma ∨ H.Sz = H.Sz ∨ H.Sz = H.Lv := Or.inr (Or.inl rfl)
      refine readsIdx_of_read_eq (F1 p H.Sz (n * e + lo) (Or.inr (Or.inl rfl))
        (not_levelCell_sz_of_le hnd ?_)) (hzk e lo (by omega) he2 hlo)
      have := Nat.mul_le_mul_left n (show k + 1 + 1 ≤ e by omega)
      omega

/-- **The upward pass** as a routine specification. -/
theorem spec_eighUpLoop {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) (md : Mode)
    {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : md.Needs (IsRelErrSem u dec (fun _ _ => True) I.sem)) (p : P) (n ℓ₀ F : ℕ)
    (hlit : IsExactIntLit dec I.sem (n + 4)) (H : EighArenas) {c b Su Sg : ℕ}
    (hcH : c ∉ H.handles) (hcSu : c ≠ Su) (hcSg : c ≠ Sg)
    {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K} :
    RoutineSpec md I (fun st => st.store.size = b ∧ H.Shaped st.store p n (ℓ₀ + 1) ∧
        st.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
        (∀ e < ℓ₀ + 1, H.LevelHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
            ⟨n, A, R₀, ε, ℓ₀⟩ e ∧
          H.RecordHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F R₀ β
            ⟨n, A, R₀, ε, ℓ₀⟩ e) ∧
        H.OutHolds st.store p (eighTapeMachine I p mmR qrR) n F (ℓ₀ + 1) R₀ β
          ⟨n, A, R₀, ε, ℓ₀⟩ (ℓ₀ + 1))
      (forRange (.const ℓ₀ + 1) fun d' => eighUpLevel p mm (.const n) (.const ℓ₀ - .var d')
        H.Lv H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp ⟨c, 1⟩)
      (eighArenaFp H n (ℓ₀ + 1) Su Sg) fun _ st' =>
        H.OutHolds st'.store p (eighTapeMachine I p mmR qrR) n F (ℓ₀ + 1) R₀ β
          ⟨n, A, R₀, ε, ℓ₀⟩ 0 := by
  refine (RoutineSpec.forRange_const (m := md) (I := I) (n := IExp.const ℓ₀ + 1)
    (body := fun d' => eighUpLevel p mm (.const n) (.const ℓ₀ - .var d') H.Lv H.Ua H.Qa H.Ea H.Sz
      H.Kd H.Kp ⟨c, 1⟩) (eighArenaFp H n (ℓ₀ + 1) Su Sg) (fun st₀ j st =>
    Modifies (eighArenaFp H n (ℓ₀ + 1) Su Sg) st₀.store st.store ∧
    H.OutHolds st.store p (eighTapeMachine I p mmR qrR) n F (ℓ₀ + 1) R₀ β ⟨n, A, R₀, ε, ℓ₀⟩
      (ℓ₀ + 1 - j) ∧
    ∀ e < ℓ₀ + 1 - j, H.LevelHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
        ⟨n, A, R₀, ε, ℓ₀⟩ e ∧
      H.RecordHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ e)
    (fun st ⟨hsz, hH, htwo, hlow, hout⟩ => ⟨Modifies.refl _ _, by simpa using hout,
      by simpa using hlow⟩)
    ?_).conseq (fun _ h => h) (fun x hx => hx) (fun st st' _ h => ?_)
  · intro st₀ ⟨hsz, hH, htwo, hlow, hout⟩ j hj
    have hj' : j < ℓ₀ + 1 := hj
    have hnd : H.handles.Nodup := hH.1
    have hS := spec_eighUpLevel hmm md hsem p n ℓ₀ F (ℓ₀ - j) (ℓ₀ + 1) (by omega) hlit H
      (qrR := qrR) (two := ⟨c, 1⟩) (b := b) (A := A) (R₀ := R₀) (ε := ε) (β := β)
    have e1 : ℓ₀ + 1 - j = ℓ₀ - j + 1 := by omega
    have hS2 := (hS.spec.with_modifies.sub (fp' := eighArenaFp H n (ℓ₀ + 1) Su Sg)
      (eighOutFp_sub_arena (by omega)))
    have key := fun st : St P K C => exec_eighUpLevel_of_eval_eq (I := I) p mm n (ℓ₀ - j)
      (.const ℓ₀ - .var j) rfl H.Lv H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp c st
    refine Spec.of_exec_eq (hS2.conseq ?_ (fun x hx => hx) ?_) key
    · rintro st ⟨hm, hout', hlow'⟩
      rw [e1] at hout' hlow'
      refine ⟨(Store.size_eq_of_shape_eq hm.1).trans hsz,
        EighArenas.Shaped.of_shape_eq (fun b _ => by rw [hm.1]) hH, ?_,
        (hlow' _ (by omega)).1, (hlow' _ (by omega)).2, hout'⟩
      exact (read_eq_of_modifies_eighArenaFp hm hcH hcSu hcSg).trans htwo
    · rintro st st' ⟨hm, hout', hlow'⟩ ⟨hmu, hO, -⟩
      have e2 : ℓ₀ + 1 - (j + 1) = ℓ₀ - j := by omega
      rw [e1] at hlow'
      refine ⟨(hm.trans (hmu.of_sub (eighOutFp_sub_arena (H := H) (n := n) (Su := Su) (Sg := Sg)
        (d := ℓ₀ - j)
        (D := ℓ₀ + 1) (by omega)))).mono
        (fun x hx => by simpa using hx), by rw [e2]; exact hO, fun e he => ?_⟩
      rw [e2] at he
      exact ⟨EighArenas.LevelHolds.of_read_eq (fun q b i hb hi =>
          read_eq_of_modifies_eighOutFp hnd hmu
            (fun h => false_of_node_arena_of_out_arena hnd hb h.1))
          (hlow' e (by omega)).1,
        EighArenas.RecordHolds.of_read_eq (fun q b i hb hi =>
          read_eq_of_modifies_eighOutFp hnd hmu (fun h => by
            have := eq_of_levelCell_of_levelCell hnd hi h.2; omega)) (hlow' e (by omega)).2⟩
  · simpa using h.2.1

/-- **The copies out of the driver**: the root's output block into `U` and its eigenvalues into
`dv`. -/
theorem wp_eighProgOut (md : Mode) (p : P) (n : ℕ) {Ua Ea U dv : ℕ}
    {Y : Matrix (Fin n) (Fin n) (K × K)} {e : Fin n → K} {Q : St P K C → Prop} {st : St P K C}
    (hUaU : U ≠ Ua) (hEaU : Ea ≠ U) (hEadv : Ea ≠ dv)
    (hU : pairLayout.Holds st.store p Ua 0 Y) (hE : ∀ i : Fin n, st.store.read p Ea i = some (e i))
    (hW : md.Needs (Writable st.store p U 0 (2 * (n * n)) ∧ Writable st.store p dv 0 n))
    (hk : ∀ st' : St P K C, Modifies [(U, 0, 2 * (n * n)), (dv, 0, n)] st.store st'.store →
      (U ≠ dv → pairLayout.Holds st'.store p U 0 Y) →
      (∀ i : Fin n, st'.store.read p dv i = some (e i)) →
      Q st') :
    Wp md I (do
        zcopy p (.const n) (.const n) Ua 0 U 0
        forRange (.const n) fun i => ins (.copy p ⟨dv, .var i⟩ ⟨Ea, .var i⟩) :
          Builder P ι ℕ ℕ Unit).run Q st := by
  have s1 := spec_zcopy (I := I) md p n n (X := Ua) (Y := U) (xo := 0) (yo := 0) Y
    (blockDisjoint_of_fst_ne hUaU)
  refine s1.wp_bind ⟨hU, hW.mono fun h => h.1⟩ fun st₁ hm₁ h₁ => ?_
  replace hm₁ : Modifies [(U, 0, 2 * (n * n))] st.store st₁.store := hm₁
  have s2 := spec_forRange_copy (m := md) (I := I) (p := p) (n := .const n) (Y := dv) (off := 0)
    (X := Ea) (didx := fun i => .var i) (sidx := fun i => .var i)
    (fun i => if h : i < n then e ⟨i, h⟩ else default) (fun i => by simp)
    (fun i hi => blockDisjoint_of_fst_ne hEadv)
  refine s2.wp_run ⟨fun i hi => ?_, hW.mono fun h => (h.2.of_shape_eq hm₁.1)⟩ fun st₂ hm₂ h₂ => ?_
  · have hi' : i < n := hi
    simp only [IExp.eval_var, dif_pos hi']
    exact (hm₁.2 p Ea i (by fp_omega [hEaU])).trans (hE ⟨i, hi'⟩)
  replace hm₂ : Modifies [(dv, 0, n)] st₁.store st₂.store := hm₂
  refine hk st₂ ((hm₁.trans hm₂).mono fun x hx => by simpa using hx) ?_ fun i => ?_
  · exact fun hUdv => pairLayout_holds_of_read_eq h₁.1 fun j _ _ => hm₂.2 p U j (by fp_omega [hUdv])
  · simpa [i.isLt] using h₂.1 i i.isLt

/-- **The spent level, the upward pass and the copies out** of the driver. -/
theorem wp_eighProgTail {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) (md : Mode)
    {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : md.Needs (IsRelErrSem u dec (fun _ _ => True) I.sem)) (p : P) (n ℓ₀ F : ℕ)
    (hlit : IsExactIntLit dec I.sem (n + 4)) (H : EighArenas) {c b Su Sg U dv : ℕ}
    (hcH : c ∉ H.handles) (hcSu : c ≠ Su) (hcSg : c ≠ Sg) (hU : U ∉ H.handles)
    (hdvH : dv ∉ H.handles)
    {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K} {Q : St P K C → Prop} {st : St P K C}
    (hsz : st.store.size = b) (hH : H.Shaped st.store p n (ℓ₀ + 1))
    (htwo : st.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ))
    (hlow : ∀ e < ℓ₀ + 1, H.LevelHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
        ⟨n, A, R₀, ε, ℓ₀⟩ e ∧
      H.RecordHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ e)
    (hLD : H.LevelHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ (ℓ₀ + 1))
    (hW : md.Needs (Writable st.store p U 0 (2 * (n * n)) ∧ Writable st.store p dv 0 n))
    (hk : ∀ st' : St P K C, Modifies (eighArenaFp H n (ℓ₀ + 1) Su Sg ++
        [(U, 0, 2 * (n * n)), (dv, 0, n)]) st.store st'.store →
      (U ≠ dv → pairLayout.Holds st'.store p U 0 (eighSlotOut I p mmR qrR n F ℓ₀ A R₀ ε β).1) →
      (∀ i : Fin n, st'.store.read p dv i = some ((eighSlotOut I p mmR qrR n F ℓ₀ A R₀ ε β).2 i)) →
      Q st') :
    Wp md I (do
        eighBottomLevel p (.const n) (.const ℓ₀ + 1) H.Ua H.Ea H.Sz
        forRange (.const ℓ₀ + 1) fun d' =>
          eighUpLevel p mm (.const n) (.const ℓ₀ - .var d') H.Lv H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp
            ⟨c, 1⟩
        zcopy p (.const n) (.const n) H.Ua 0 U 0
        forRange (.const n) fun i => ins (.copy p ⟨dv, .var i⟩ ⟨H.Ea, .var i⟩) :
          Builder P ι ℕ ℕ Unit).run Q st := by
  have hnd : H.handles.Nodup := hH.1
  have hB := spec_eighBottomLevel (mmR := mmR) (qrR := qrR) (I := I) md p n ℓ₀ F (ℓ₀ + 1) H
    (A := A) (R₀ := R₀) (ε := ε) (β := β)
  have hB' := hB.congr (by unfold eighBottomLevel; exact executionComposable_forRange _ _)
    fun st => exec_eighBottomLevel_of_eval_eq p n (ℓ₀ + 1) (IExp.const ℓ₀ + 1) rfl H.Ua H.Ea
      H.Sz st
  obtain ⟨hlit0, -, hlit1⟩ : (∃ v, I.sem.lit p 0 = some v) ∧ True ∧ (∃ v, I.sem.lit p 1 = some v) :=
    ⟨(hlit p 0 (by omega)).imp fun v h => by simpa using h.1, trivial,
      (hlit p 1 (by omega)).imp fun v h => by simpa using h.1⟩
  refine hB'.wp_bind ⟨hH, hLD, Mode.needs_of ⟨hlit0, hlit1⟩ md⟩ fun st₁ hm₁ h₁ => ?_
  replace hm₁ : Modifies [(H.Ua, 2 * (n * n) * (ℓ₀ + 1), 2 * (n * n)),
    (H.Ea, n * (ℓ₀ + 1), n)] st.store st₁.store := hm₁
  have hnl : ∀ e < ℓ₀ + 1, ∀ b i, H.LevelCell n e b i → ¬ H.LevelCell n (ℓ₀ + 1) b i :=
    fun e he b i h h' => by have := eq_of_levelCell_of_levelCell hnd h h'; omega
  have hlow₁ : ∀ e < ℓ₀ + 1, H.LevelHolds I.sem st₁.store p (eighTapeMachine I p mmR qrR) n F ℓ₀
      R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ e ∧ H.RecordHolds I.sem st₁.store p (eighTapeMachine I p mmR qrR) n F
      R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ e := fun e he =>
    ⟨EighArenas.LevelHolds.of_read_eq (fun q b i hb hi => read_eq_of_modifies_eighOutFp hnd hm₁
        (fun h => false_of_node_arena_of_out_arena hnd hb h.1)) (hlow e he).1,
      EighArenas.RecordHolds.of_read_eq (fun q b i hb hi => read_eq_of_modifies_eighOutFp hnd hm₁
        (fun h => hnl e he b i hi h.2)) (hlow e he).2⟩
  have hc₁ : ∀ j, st₁.store.read p c j = st.store.read p c j := fun j =>
    hm₁.2 p c j fun x hx => blockDisjoint_of_fst_ne (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;>
        exact fun h => hcH (by simp only at h; rw [h]; simp [EighArenas.handles]))
  have hUp := spec_eighUpLoop (qrR := qrR) hmm md hsem p n ℓ₀ F hlit H hcH hcSu hcSg (b := b)
    (Su := Su)
    (Sg := Sg) (A := A) (R₀ := R₀) (ε := ε) (β := β)
  refine hUp.wp_bind ⟨(Store.size_eq_of_shape_eq hm₁.1).trans hsz,
    EighArenas.Shaped.of_shape_eq (fun x _ => by rw [hm₁.1]) hH, (hc₁ 1).trans htwo, hlow₁,
    h₁.1⟩ fun st₂ hm₂ h₂ => ?_
  have hUa : U ≠ H.Ua := fun h => hU (h ▸ by simp [EighArenas.handles])
  have hEa : H.Ea ≠ U := fun h => hU (h ▸ by simp [EighArenas.handles])
  have hEadv : H.Ea ≠ dv := fun h => hdvH (h ▸ by simp [EighArenas.handles])
  obtain ⟨hU0, hE0⟩ := h₂ [] 0 ⟨n, A, R₀, ε, ℓ₀⟩ rfl rfl
  simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero] at hU0 hE0
  refine wp_eighProgOut md p n (Ua := H.Ua) (Ea := H.Ea) (U := U) (dv := dv)
    (Y := (eighSlotOut I p mmR qrR n F ℓ₀ A R₀ ε β).1)
    (e := (eighSlotOut I p mmR qrR n F ℓ₀ A R₀ ε β).2) hUa hEa hEadv hU0 hE0
    (hW.mono fun h => ⟨h.1.of_shape_eq ((hm₂.1.trans hm₁.1)), h.2.of_shape_eq (hm₂.1.trans hm₁.1)⟩)
    fun st₃ hm₃ hUh hdh => hk st₃ ?_ hUh hdh
  have hm₁' := hm₁.of_sub (fp' := eighArenaFp H n (ℓ₀ + 1) Su Sg) (eighOutFp_sub_arena (d := ℓ₀ + 1)
    (D := ℓ₀ + 1) le_rfl)
  exact ((hm₁'.trans hm₂).trans hm₃).mono fun x hx => by
    simp only [List.mem_append] at hx ⊢
    tauto

/-! ### The constants and the root -/

omit [DecidableEq P] [AddMonoid C] in
/-- **The constants of the driver are defined**: under the standard model at $u$ with $u(p) < 1$
and exact integer literals up to $B \ge 2$, the literals $1$ and $2$, the quotient
$\mathrm{fl}(1/\mathrm{fl}(2))$, the negation $-1$ and the square root of the quotient are
defined. -/
theorem eighConsts_defined {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (hu : u p < 1) {B : ℕ}
    (hlit : IsExactIntLit dec I.sem B) (hB : 2 ≤ B) :
    (∃ v, I.sem.lit p 1 = some v) ∧ (∃ v, I.sem.lit p ((2 : ℕ) : ℚ) = some v) ∧
      (∃ v, I.sem.bin p .div ((I.sem.lit p 1).getD default)
        ((I.sem.lit p ((2 : ℕ) : ℚ)).getD default) = some v) ∧
      (∃ v, I.sem.un p .neg ((I.sem.lit p 1).getD default) = some v) ∧
      ∃ v, I.sem.un p .sqrt ((I.sem.bin p .div ((I.sem.lit p 1).getD default)
        ((I.sem.lit p ((2 : ℕ) : ℚ)).getD default)).getD default) = some v := by
  obtain ⟨o, ho, ho1⟩ := hlit p 1 (by omega)
  have ho' : I.sem.lit p 1 = some o := by simpa using ho
  obtain ⟨tw, htw, htw2⟩ := hlit p 2 hB
  obtain ⟨hf, hfh, δ, hδ, hfd⟩ := exists_bin_eq_some hsem p (b := .div) trivial (x := o) (y := tw)
    (fun _ => by rw [htw2]; norm_num)
  obtain ⟨ng, hng, -⟩ := hsem.neg p o
  have hf0 : 0 ≤ dec p hf := by
    rw [hfd, ho1, htw2]
    have := (abs_le.mp hδ).1
    simp only [BinOp.realOp]
    apply mul_nonneg (by positivity)
    linarith
  obtain ⟨sq, hsq⟩ := hsem.sqrt_ok p hf hf0
  have htw' : I.sem.lit p ((2 : ℕ) : ℚ) = some tw := htw
  refine ⟨⟨o, ho'⟩, ⟨tw, htw'⟩, ?_, ?_, ?_⟩
  · rw [ho', htw']; exact ⟨hf, hfh⟩
  · rw [ho']; exact ⟨ng, hng⟩
  · rw [ho', htw', Option.getD_some, Option.getD_some]
    simp only [hfh, Option.getD_some]
    exact ⟨sq, hsq⟩

/-- **The constants of the driver**: the five instructions that write one, $\mathrm{fl}(2)$,
$\mathrm{fl}(1/2)$, $-1$ and $\sqrt{1/2}$ into the cells $0$ to $4$ of `c`, then the rest, which
starts from a state whose cells hold the constants of the machine
`NLAlib.eighTapeMachine I p mmR qrR` and changes nothing else. -/
theorem wp_eighProgConsts (md : Mode) {dec : P → K → ℝ} (p : P) {n c : ℕ}
    (hlit : IsExactIntLit dec I.sem (n + 4)) {rest : Builder P ι ℕ ℕ Unit}
    {Q : St P K C → Prop} {st : St P K C}
    (hN : md.Needs ((∃ v, I.sem.lit p 1 = some v) ∧ (∃ v, I.sem.lit p ((2 : ℕ) : ℚ) = some v) ∧
      (∃ v, I.sem.bin p .div ((I.sem.lit p 1).getD default)
        ((I.sem.lit p ((2 : ℕ) : ℚ)).getD default) = some v) ∧
      (∃ v, I.sem.un p .neg ((I.sem.lit p 1).getD default) = some v) ∧
      (∃ v, I.sem.un p .sqrt ((I.sem.bin p .div ((I.sem.lit p 1).getD default)
        ((I.sem.lit p ((2 : ℕ) : ℚ)).getD default)).getD default) = some v) ∧
      Writable st.store p c 0 5))
    (hk : ∀ st' : St P K C, Modifies [(c, 0, 5)] st.store st'.store → PosKept st st' →
      (st'.store.read p c 0 = I.sem.lit p 1 ∧
        st'.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
        st'.store.read p c 2 = some ((eighTapeMachine I p mmR qrR).div
          (eighTapeMachine I p mmR qrR).one ((eighTapeMachine I p mmR qrR).ofNat 2)) ∧
        st'.store.read p c 3 = some ((eighTapeMachine I p mmR qrR).neg
          (eighTapeMachine I p mmR qrR).one) ∧
        st'.store.read p c 4 = some (I.sem.sqrtHalf p)) → Wp md I rest.run Q st') :
    Wp md I (do
        ins (.lit p ⟨c, 0⟩ 1)
        ins (.litIdx p ⟨c, 1⟩ 2)
        ins (.bin p .div ⟨c, 2⟩ ⟨c, 0⟩ ⟨c, 1⟩)
        ins (.un p .neg ⟨c, 3⟩ ⟨c, 0⟩)
        ins (.un p .sqrt ⟨c, 4⟩ ⟨c, 2⟩)
        rest : Builder P ι ℕ ℕ Unit).run Q st := by
  obtain ⟨o, ho, -⟩ := hlit p 1 (by omega)
  obtain ⟨tw, htw, -⟩ := hlit p 2 (by omega)
  have ho' : I.sem.lit p 1 = some o := by simpa using ho
  have htw' : I.sem.lit p ((2 : ℕ) : ℚ) = some tw := htw
  have hW : ∀ {s : Store P K}, Writable s p c 0 5 → ∀ i < 5, Writable s p c i 1 :=
    fun h i hi => h.of_le (by omega) (by omega)
  have s1 := RoutineSpec.ins (spec_lit_getD (I := I) (m := md) (p := p) (dst := ⟨c, 0⟩) (q := 1))
  refine s1.wp_bind (hN.mono fun h => ⟨h.1, hW h.2.2.2.2.2 0 (by omega)⟩) fun st₁ hm₁ h₁ => ?_
  have s2 := RoutineSpec.ins (spec_litIdx_getD (I := I) (m := md) (p := p) (dst := ⟨c, 1⟩)
    (e := 2))
  refine s2.wp_bind (hN.mono fun h => ⟨h.2.1, (hW h.2.2.2.2.2 1 (by omega)).of_shape_eq hm₁.1⟩)
    fun st₂ hm₂ h₂ => ?_
  have r0 : st₂.store.read p c 0 = some ((I.sem.lit p 1).getD default) :=
    (hm₂.2 p c 0 (by fp_omega)).trans h₁.1
  have s3 := RoutineSpec.ins (spec_bin_getD (I := I) (m := md) (p := p) (dst := ⟨c, 2⟩)
    (x := ⟨c, 0⟩) (y := ⟨c, 1⟩) (op := .div) (a := (I.sem.lit p 1).getD default)
    (b := (I.sem.lit p ((2 : ℕ) : ℚ)).getD default))
  refine s3.wp_bind ⟨r0, h₂.1, hN.mono fun h => ⟨h.2.2.1,
    (hW h.2.2.2.2.2 2 (by omega)).of_shape_eq (hm₂.1.trans hm₁.1)⟩⟩
    fun st₃ hm₃ h₃ => ?_
  have r1 : st₃.store.read p c 1 = some ((I.sem.lit p ((2 : ℕ) : ℚ)).getD default) :=
    (hm₃.2 p c 1 (by fp_omega)).trans h₂.1
  have r0' : st₃.store.read p c 0 = some ((I.sem.lit p 1).getD default) :=
    (hm₃.2 p c 0 (by fp_omega)).trans r0
  have s4 := RoutineSpec.ins (spec_un_getD (I := I) (m := md) (p := p) (dst := ⟨c, 3⟩)
    (x := ⟨c, 0⟩) (op := .neg) (a := (I.sem.lit p 1).getD default))
  refine s4.wp_bind ⟨r0', hN.mono fun h => ⟨h.2.2.2.1,
    (hW h.2.2.2.2.2 3 (by omega)).of_shape_eq (hm₃.1.trans (hm₂.1.trans hm₁.1))⟩⟩
    fun st₄ hm₄ h₄ => ?_
  have s5 := RoutineSpec.ins (spec_un_getD (I := I) (m := md) (p := p) (dst := ⟨c, 4⟩)
    (x := ⟨c, 2⟩) (op := .sqrt) (a := (I.sem.bin p .div ((I.sem.lit p 1).getD default)
      ((I.sem.lit p ((2 : ℕ) : ℚ)).getD default)).getD default))
  refine s5.wp_bind ⟨(hm₄.2 p c 2 (by fp_omega)).trans h₃.1, hN.mono fun h => ⟨h.2.2.2.2.1,
    (hW h.2.2.2.2.2 4 (by omega)).of_shape_eq (hm₄.1.trans (hm₃.1.trans (hm₂.1.trans hm₁.1)))⟩⟩
    fun st₅ hm₅ h₅ => ?_
  have hm := ((((hm₁.trans hm₂).trans hm₃).trans hm₄).trans hm₅)
  refine hk st₅ (hm.of_sub fun x hx => ?_) ?_ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false, List.cons_append, List.nil_append] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> exact ⟨(c, 0, 5), by simp, rfl, by simp, by simp⟩
  · exact h₅.2.trans (h₄.2.trans (h₃.2.trans (h₂.2.trans h₁.2)))
  · refine ⟨((hm₅.2 p c 0 (by fp_omega)).trans ((hm₄.2 p c 0 (by fp_omega)).trans r0')).trans
      (by rw [ho']; rfl), ((hm₅.2 p c 1 (by fp_omega)).trans ((hm₄.2 p c 1 (by fp_omega)).trans
      r1)).trans (by rw [htw']; rfl), (hm₅.2 p c 2 (by fp_omega)).trans
      ((hm₄.2 p c 2 (by fp_omega)).trans h₃.1), (hm₅.2 p c 3 (by fp_omega)).trans h₄.1, h₅.1⟩

omit [Inhabited K] in
/-- **The root of the driver**: the zero fill of the sizes, the root's size, the copy of the
stored matrix into the node arena and the copies of $R_0$, $\varepsilon$ into the windows, then
the rest, which starts from the root at depth $0$ and changes nothing else. -/
theorem wp_eighProgInit (md : Mode) {dec : P → K → ℝ} (p : P) (n ℓ₀ : ℕ)
    (hlit : IsExactIntLit dec I.sem (n + 4)) {A par Ma Sz Lv : ℕ}
    {A₀ : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε : K} {rest : Builder P ι ℕ ℕ Unit}
    {Q : St P K C → Prop} {st : St P K C} (hMa : Ma ≠ A) (hSzA : Sz ≠ A) (hSzp : Sz ≠ par)
    (hLvp : Lv ≠ par) (hMap : Ma ≠ par) (hMaSz : Ma ≠ Sz)
    (hLvSz : Lv ≠ Sz) (hLvMa : Lv ≠ Ma)
    (hA : pairLayout.Holds st.store p A 0 A₀)
    (hpar : st.store.read p par 0 = some R₀ ∧ st.store.read p par 1 = some ε)
    (hW : md.Needs (Writable st.store p Sz 0 (n * (ℓ₀ + 1 + 1) + 1) ∧
      Writable st.store p Ma 0 (2 * (n * n)) ∧ Writable st.store p Lv 0 2))
    (hk : ∀ st' : St P K C, Modifies [(Sz, 0, n * (ℓ₀ + 1 + 1) + 1), (Ma, 0, 2 * (n * n)),
        (Lv, 0, 2)] st.store st'.store → PosKept st st' →
      (st'.store.read p Sz 0 = I.sem.lit p ((n : ℕ) : ℚ) ∧
        (∀ w, w ≠ 0 → w < n * (ℓ₀ + 1 + 1) + 1 →
          st'.store.read p Sz w = I.sem.lit p ((0 : ℕ) : ℚ)) ∧
        pairLayout.Holds st'.store p Ma 0 A₀ ∧ st'.store.read p Lv 0 = some R₀ ∧
        st'.store.read p Lv 1 = some ε) → Wp md I rest.run Q st') :
    Wp md I (do
        forRange (.const n * (.const ℓ₀ + 1 + 1) + 1) fun w => ins (.litIdx p ⟨Sz, .var w⟩ 0)
        ins (.litIdx p ⟨Sz, 0⟩ (.const n))
        zcopy p (.const n) (.const n) A 0 Ma 0
        ins (.copy p ⟨Lv, 0⟩ ⟨par, 0⟩)
        ins (.copy p ⟨Lv, 1⟩ ⟨par, 1⟩)
        rest : Builder P ι ℕ ℕ Unit).run Q st := by
  obtain ⟨z0, hz0, -⟩ := hlit p 0 (by omega)
  obtain ⟨zn, hzn, -⟩ := hlit p n (by omega)
  have s1 := spec_forRange_litIdx (m := md) (I := I) (p := p) (e := 0)
    (n := .const n * (.const ℓ₀ + 1 + 1) + 1) (Y := Sz) (off := 0) (didx := fun w => .var w)
    (fun i => by simp)
  refine s1.wp_bind (hW.mono fun h => ⟨⟨z0, by simpa using hz0⟩, h.1⟩) fun st₁ hm₁ h₁ => ?_
  replace hm₁ : Modifies [(Sz, 0, n * (ℓ₀ + 1 + 1) + 1)] st.store st₁.store := hm₁
  have s2 := RoutineSpec.ins (spec_litIdx_read (I := I) (m := md) (p := p) (dst := ⟨Sz, 0⟩)
    (e := .const n))
  refine s2.wp_bind (hW.mono fun h => ⟨⟨zn, hzn⟩, (h.1.of_shape_eq hm₁.1).of_le (le_refl _)
    (by change 0 + 1 ≤ 0 + (n * (ℓ₀ + 1 + 1) + 1); omega)⟩) fun st₂ hm₂ h₂ => ?_
  replace hm₂ : Modifies [(Sz, 0, 1)] st₁.store st₂.store := hm₂
  have s3 := spec_zcopy (I := I) md p n n (X := A) (Y := Ma) (xo := 0) (yo := 0) A₀
    (blockDisjoint_of_fst_ne hMa)
  have hA₂ : pairLayout.Holds st₂.store p A 0 A₀ := pairLayout_holds_of_read_eq hA fun i _ _ =>
    (hm₂.2 p A i (by fp_omega [hSzA])).trans (hm₁.2 p A i (by fp_omega [hSzA]))
  refine s3.wp_bind ⟨hA₂, hW.mono fun h => (h.2.1.of_shape_eq (hm₂.1.trans hm₁.1))⟩
    fun st₃ hm₃ h₃ => ?_
  replace hm₃ : Modifies [(Ma, 0, 2 * (n * n))] st₂.store st₃.store := hm₃
  have s4 := RoutineSpec.ins (spec_copy (I := I) (m := md) (p := p) (dst := ⟨Lv, 0⟩)
    (x := ⟨par, 0⟩) (a := R₀))
  have hp₃ : ∀ j, st₃.store.read p par j = st.store.read p par j := fun j =>
    (hm₃.2 p par j (by fp_omega [hMap])).trans
      ((hm₂.2 p par j (by fp_omega [hSzp])).trans (hm₁.2 p par j (by fp_omega [hSzp])))
  refine s4.wp_bind ⟨(hp₃ 0).trans hpar.1, hW.mono fun h => ?_⟩ fun st₄ hm₄ h₄ => ?_
  · exact show Writable st₃.store p Lv 0 1 from (h.2.2.of_shape_eq
      (hm₃.1.trans (hm₂.1.trans hm₁.1))).of_le (by omega) (by omega)
  replace hm₄ : Modifies [(Lv, 0, 1)] st₃.store st₄.store := hm₄
  have s5 := RoutineSpec.ins (spec_copy (I := I) (m := md) (p := p) (dst := ⟨Lv, 1⟩)
    (x := ⟨par, 1⟩) (a := ε))
  refine s5.wp_bind ⟨(hm₄.2 p par 1 (by fp_omega [hLvp])).trans ((hp₃ 1).trans hpar.2),
    hW.mono fun h => ?_⟩ fun st₅ hm₅ h₅ => ?_
  · exact show Writable st₄.store p Lv 1 1 from (h.2.2.of_shape_eq
      (hm₄.1.trans (hm₃.1.trans (hm₂.1.trans hm₁.1)))).of_le (by omega) (by omega)
  replace hm₅ : Modifies [(Lv, 1, 1)] st₄.store st₅.store := hm₅
  have hm := ((((hm₁.trans hm₂).trans hm₃).trans hm₄).trans hm₅)
  refine hk st₅ (hm.of_sub fun x hx => ?_) ?_ ?_
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact ⟨(Sz, 0, n * (ℓ₀ + 1 + 1) + 1), by simp, rfl, le_rfl, le_rfl⟩
    · exact ⟨(Sz, 0, n * (ℓ₀ + 1 + 1) + 1), by simp, rfl, le_rfl, by dsimp only; omega⟩
    · exact ⟨(Ma, 0, 2 * (n * n)), by simp, rfl, le_rfl, le_rfl⟩
    · exact ⟨(Lv, 0, 2), by simp, rfl, le_rfl, by dsimp only; omega⟩
    · exact ⟨(Lv, 0, 2), by simp, rfl, by dsimp only; omega, by dsimp only; omega⟩
  · exact h₅.2.2.trans (h₄.2.2.trans (h₃.2.trans (h₂.2.trans h₁.2)))
  · refine ⟨?_, fun w hw0 hw => ?_, ?_, ?_, ?_⟩
    · exact (hm₅.2 p Sz 0 (by fp_omega [hLvSz])).trans ((hm₄.2 p Sz 0 (by fp_omega [hLvSz])).trans
        ((hm₃.2 p Sz 0 (by fp_omega [hMaSz])).trans h₂.1))
    · refine (hm₅.2 p Sz w (by fp_omega [hLvSz])).trans ((hm₄.2 p Sz w (by fp_omega [hLvSz])).trans
        ((hm₃.2 p Sz w (by fp_omega [hMaSz])).trans ((hm₂.2 p Sz w (by fp_omega [hw0])).trans
        ?_)))
      simpa using h₁.1 w (by simpa using hw)
    · exact pairLayout_holds_of_read_eq h₃.1 fun i _ _ =>
        (hm₅.2 p Ma _ (by fp_omega [hLvMa])).trans (hm₄.2 p Ma _ (by fp_omega [hLvMa]))
    · exact (hm₅.2 p Lv 0 (by fp_omega)).trans h₄.1
    · exact h₅.1

/-! ### The driver -/

/-- **The passes of the driver**: the downward pass, the spent level, the upward pass and the
copies out, from the root at depth $0$. -/
theorem wp_eighProgPasses {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) (md : Mode) {u : P → ℝ} {dec : P → K → ℝ}
    {safe : P → ℝ → Prop} (p : P) (n ℓ₀ F : ℕ)
    (hsem : md.Needs (IsRelErrSem u dec safe I.sem ∧ (∀ p x, safe p x) ∧ u p < 1))
    (hflag : I.sem.DecidesFlags p)
    (hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y)))
    (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem) (H : EighArenas)
    {par Su Sg c U dv : ℕ} {A₀ : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup) (hU : U ∉ H.handles) (hdv : dv ∉ H.handles)
    {Q : St P K C → Prop} {s : St P K C} (hlt : ∀ x ∈ H.handles ++ [par, c], x < s.store.size)
    (hH : H.Shaped s.store p n (ℓ₀ + 1))
    (hlev : H.LevelHolds I.sem s.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A₀, R₀, ε, ℓ₀⟩ 0)
    (hz : ∀ e lo, 0 < e → e ≤ ℓ₀ + 1 → lo < n → ReadsIdx I.sem s.store p H.Sz (n * e + lo) 0)
    (hpos : s.pos .uniform = 0 ∧ s.pos .gaussian = 0)
    (hpar : s.store.read p par 0 = some R₀ ∧ s.store.read p par 2 = some β)
    (hc : s.store.read p c 0 = I.sem.lit p 1 ∧ s.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
      s.store.read p c 2 = some ((eighTapeMachine I p mmR qrR).div
        (eighTapeMachine I p mmR qrR).one ((eighTapeMachine I p mmR qrR).ofNat 2)) ∧
      s.store.read p c 3 = some ((eighTapeMachine I p mmR qrR).neg
        (eighTapeMachine I p mmR qrR).one) ∧
      s.store.read p c 4 = some (I.sem.sqrtHalf p))
    (hSu : s.store.shape[Su]? = some (p, n)) (hSg : s.store.shape[Sg]? = some (p, 4 * (n * n)))
    (hN : md.Needs (0 ≤ dec p R₀ ∧ 1 ≤ ℓ₀ ∧ Writable s.store p U 0 (2 * (n * n)) ∧
      Writable s.store p dv 0 n))
    (hk : ∀ s' : St P K C, Modifies (eighArenaFp H n (ℓ₀ + 1) Su Sg ++
        [(U, 0, 2 * (n * n)), (dv, 0, n)]) s.store s'.store →
      (U ≠ dv → pairLayout.Holds s'.store p U 0 (eighSlotOut I p mmR qrR n F ℓ₀ A₀ R₀ ε β).1) →
      (∀ i : Fin n, s'.store.read p dv i =
        some ((eighSlotOut I p mmR qrR n F ℓ₀ A₀ R₀ ε β).2 i)) → Q s') :
    Wp md I (do
        forRange (.const ℓ₀ + 1) fun d =>
          eighDownLevel p mm qr (.const n) (.const ℓ₀) (.const F) (.var d) par H.Lv Su Sg H.Ma
            H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩
        eighBottomLevel p (.const n) (.const ℓ₀ + 1) H.Ua H.Ea H.Sz
        forRange (.const ℓ₀ + 1) fun d' =>
          eighUpLevel p mm (.const n) (.const ℓ₀ - .var d') H.Lv H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp
            ⟨c, 1⟩
        zcopy p (.const n) (.const n) H.Ua 0 U 0
        forRange (.const n) fun i => ins (.copy p ⟨dv, .var i⟩ ⟨H.Ea, .var i⟩) :
          Builder P ι ℕ ℕ Unit).run Q s := by
  have hcH : c ∉ H.handles := not_mem_handles_of_mem hbufs (x := c) (by simp)
  have h4 := (List.nodup_append.mp hbufs).2.1
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at h4
  obtain ⟨⟨-, -, -⟩, ⟨-, hSuc⟩, hSgc, -⟩ := h4
  have hdown := spec_eighDownLoop hmm hqr md p n ℓ₀ F hsem hflag hcmp hlit htn H (par := par)
    (Su := Su) (Sg := Sg) (c := c) (b := s.store.size) (A := A₀) (R₀ := R₀) (ε := ε) (β := β)
    hbufs hlt
  refine hdown.wp_bind ⟨rfl, hH, hlev, hz, hpos, hpar, hc, hN.mono fun h =>
    ⟨fun i hi => ⟨_, hSu, by omega⟩, fun i hi => ⟨_, hSg, by omega⟩, h.1, h.2.1⟩⟩
    fun s3 hm3 h3 => ?_
  have hsh : s3.store.shape = s.store.shape := hm3.1
  refine wp_eighProgTail hmm md (hsem.mono fun h => h.1.mono_safe (safe' := fun _ _ => True)
    fun q x _ => h.2.1 q x) p n ℓ₀ F hlit H (c := c) (b := s.store.size) (Su := Su) (Sg := Sg)
    (U := U) (dv := dv) hcH (Ne.symm hSuc) (Ne.symm hSgc) hU hdv (A := A₀) (R₀ := R₀) (ε := ε)
    (β := β) (Store.size_eq_of_shape_eq hsh)
    (EighArenas.Shaped.of_shape_eq (fun x _ => by rw [hsh]) hH)
    ((read_eq_of_modifies_eighArenaFp hm3 hcH (Ne.symm hSuc) (Ne.symm hSgc)).trans hc.2.1)
    h3.2 h3.1 (hN.mono fun h => ⟨h.2.2.1.of_shape_eq hsh, h.2.2.2.of_shape_eq hsh⟩)
    fun s4 hm4 hU hd => hk s4 (hm3.trans hm4 |>.mono fun x hx => ?_) hU hd
  rcases List.mem_append.mp hx with h | h
  · exact List.mem_append_left _ h
  · exact h

omit [Inhabited K] in
/-- The footprints of the stages of the driver lie in the footprint of the body. -/
theorem modifies_eighProgBody {H : EighArenas} {n ℓ₀ Su Sg U dv c : ℕ}
    {s s1 s2 s4 : Store P K}
    (hm1 : Modifies [(c, 0, 5)] s s1)
    (hm2 : Modifies [(H.Sz, 0, n * (ℓ₀ + 1 + 1) + 1), (H.Ma, 0, 2 * (n * n)), (H.Lv, 0, 2)] s1 s2)
    (hm4 : Modifies (eighArenaFp H n (ℓ₀ + 1) Su Sg ++ [(U, 0, 2 * (n * n)), (dv, 0, n)]) s2 s4) :
    Modifies ([(U, 0, 2 * (n * n)), (dv, 0, n), (c, 0, 5)] ++ eighArenaFp H n (ℓ₀ + 1) Su Sg)
      s s4 := by
  have hge : 2 * (n * n) ≤ 2 * (n * n) * (ℓ₀ + 1 + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hm2' := hm2.of_sub (fp' := [(U, 0, 2 * (n * n)), (dv, 0, n), (c, 0, 5)] ++
      eighArenaFp H n (ℓ₀ + 1) Su Sg) fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨(H.Sz, 0, n * (ℓ₀ + 1 + 1) + 1), by simp [eighArenaFp], rfl, le_rfl, le_rfl⟩
    · exact ⟨(H.Ma, 0, 2 * (n * n) * (ℓ₀ + 1 + 1)), by simp [eighArenaFp], rfl, le_rfl,
        by dsimp only; omega⟩
    · exact ⟨(H.Lv, 0, 2 * (ℓ₀ + 1 + 1)), by simp [eighArenaFp], rfl, le_rfl,
        by dsimp only; omega⟩
  have m1 := hm1.mono (fp' := [(U, 0, 2 * (n * n)), (dv, 0, n), (c, 0, 5)] ++
      eighArenaFp H n (ℓ₀ + 1) Su Sg) fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx; simp
  have m4 := hm4.mono (fp' := [(U, 0, 2 * (n * n)), (dv, 0, n), (c, 0, 5)] ++
      eighArenaFp H n (ℓ₀ + 1) Su Sg) fun x hx => by
    rcases List.mem_append.mp hx with h | h
    · exact List.mem_append_right _ h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> simp
  exact (m1.trans hm2').trans m4 |>.mono fun x hx => by
    rcases List.mem_append.mp hx with h | h
    · rcases List.mem_append.mp h with h | h <;> exact h
    · exact h

/-- **The body of the driver** after its allocations. -/
theorem wp_eighProgBody {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) (md : Mode) {u : P → ℝ} {dec : P → K → ℝ}
    {safe : P → ℝ → Prop} (p : P) (n ℓ₀ F : ℕ)
    (hsem : md.Needs (IsRelErrSem u dec safe I.sem ∧ (∀ p x, safe p x) ∧ u p < 1))
    (hflag : I.sem.DecidesFlags p)
    (hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y)))
    (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem) (H : EighArenas)
    {A par U dv Su Sg c : ℕ} {A₀ : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup)
    (hold : ∀ x ∈ [A, par, U, dv], x ∉ H.handles ∧ x ≠ Su ∧ x ≠ Sg ∧ x ≠ c)
    {Q : St P K C → Prop} {s : St P K C}
    (hlt : ∀ x ∈ H.handles ++ [par, c], x < s.store.size)
    (hH : H.Shaped s.store p n (ℓ₀ + 1)) (hsc : s.store.shape[c]? = some (p, 5))
    (hSu : s.store.shape[Su]? = some (p, n)) (hSg : s.store.shape[Sg]? = some (p, 4 * (n * n)))
    (hA : pairLayout.Holds s.store p A 0 A₀)
    (hpar : s.store.read p par 0 = some R₀ ∧ s.store.read p par 1 = some ε ∧
      s.store.read p par 2 = some β)
    (hpos : s.pos .uniform = 0 ∧ s.pos .gaussian = 0)
    (hN : md.Needs (0 ≤ dec p R₀ ∧ 1 ≤ ℓ₀ ∧ Writable s.store p U 0 (2 * (n * n)) ∧
      Writable s.store p dv 0 n))
    (hk : ∀ s' : St P K C, Modifies ([(U, 0, 2 * (n * n)), (dv, 0, n), (c, 0, 5)] ++
        eighArenaFp H n (ℓ₀ + 1) Su Sg) s.store s'.store →
      (U ≠ dv → pairLayout.Holds s'.store p U 0 (eighSlotOut I p mmR qrR n F ℓ₀ A₀ R₀ ε β).1) →
      (∀ i : Fin n, s'.store.read p dv i = some ((eighSlotOut I p mmR qrR n F ℓ₀ A₀ R₀ ε β).2 i)) →
      Q s') :
    Wp md I (do
        ins (.lit p ⟨c, 0⟩ 1)
        ins (.litIdx p ⟨c, 1⟩ 2)
        ins (.bin p .div ⟨c, 2⟩ ⟨c, 0⟩ ⟨c, 1⟩)
        ins (.un p .neg ⟨c, 3⟩ ⟨c, 0⟩)
        ins (.un p .sqrt ⟨c, 4⟩ ⟨c, 2⟩)
        forRange (.const n * (.const ℓ₀ + 1 + 1) + 1) fun w => ins (.litIdx p ⟨H.Sz, .var w⟩ 0)
        ins (.litIdx p ⟨H.Sz, 0⟩ (.const n))
        zcopy p (.const n) (.const n) A 0 H.Ma 0
        ins (.copy p ⟨H.Lv, 0⟩ ⟨par, 0⟩)
        ins (.copy p ⟨H.Lv, 1⟩ ⟨par, 1⟩)
        forRange (.const ℓ₀ + 1) fun d =>
          eighDownLevel p mm qr (.const n) (.const ℓ₀) (.const F) (.var d) par H.Lv Su Sg H.Ma
            H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩
        eighBottomLevel p (.const n) (.const ℓ₀ + 1) H.Ua H.Ea H.Sz
        forRange (.const ℓ₀ + 1) fun d' =>
          eighUpLevel p mm (.const n) (.const ℓ₀ - .var d') H.Lv H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp
            ⟨c, 1⟩
        zcopy p (.const n) (.const n) H.Ua 0 U 0
        forRange (.const n) fun i => ins (.copy p ⟨dv, .var i⟩ ⟨H.Ea, .var i⟩) :
          Builder P ι ℕ ℕ Unit).run Q s := by
  have hnd : H.handles.Nodup := hH.1
  obtain ⟨hAH, hAu, hAg, hAc⟩ := hold A (by simp)
  obtain ⟨hpH, hpu, hpg, hpc⟩ := hold par (by simp)
  obtain ⟨hUH, hUu, hUg, hUc⟩ := hold U (by simp)
  obtain ⟨hdH, hdu, hdg, hdc⟩ := hold dv (by simp)
  have hcH : c ∉ H.handles := not_mem_handles_of_mem hbufs (x := c) (by simp)
  have hSuH : Su ∉ H.handles := not_mem_handles_of_mem hbufs (x := Su) (by simp)
  have hSgH : Sg ∉ H.handles := not_mem_handles_of_mem hbufs (x := Sg) (by simp)
  have h4 := (List.nodup_append.mp hbufs).2.1
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at h4
  obtain ⟨⟨-, -, -⟩, ⟨-, hSuc⟩, hSgc, -⟩ := h4
  have hsem' := hsem.mono fun h => h.1.mono_safe (safe' := fun _ _ => True) fun q x _ => h.2.1 q x
  have hu := hsem.mono fun h => h.2.2
  have hdef := hsem.mono fun h => eighConsts_defined (h.1.mono_safe (safe' := fun _ _ => True)
    fun q x _ => h.2.1 q x) p h.2.2 hlit (B := n + 4) (by omega)
  have hne : ∀ x, x ∉ H.handles → H.Ma ≠ x ∧ H.Sz ≠ x ∧ H.Lv ≠ x := fun x hx =>
    ⟨fun h => hx (h ▸ by simp [EighArenas.handles]), fun h => hx (h ▸ by simp [EighArenas.handles]),
      fun h => hx (h ▸ by simp [EighArenas.handles])⟩
  have hMaSz : H.Ma ≠ H.Sz := fun h => by simp [EighArenas.handles, h] at hnd
  have hLvSz : H.Lv ≠ H.Sz := fun h => by simp [EighArenas.handles, h] at hnd
  have hLvMa : H.Lv ≠ H.Ma := fun h => by simp [EighArenas.handles, h] at hnd
  obtain ⟨hMaA, hSzA, hLvA⟩ := hne A hAH
  obtain ⟨hMap, hSzp, hLvp⟩ := hne par hpH
  obtain ⟨hMac, hSzc, hLvc⟩ := hne c hcH
  have hW5 : Writable s.store p c 0 5 := fun i hi => ⟨5, hsc, by omega⟩
  refine wp_eighProgConsts (mmR := mmR) (qrR := qrR) md p hlit (hdef.mono fun h =>
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, hW5⟩) fun s1 hm1 hp1 hc => ?_
  obtain ⟨-, hshMa, -, -, -, hshSz, -, -, hshLv⟩ := id hH
  have hsh1 := hm1.1
  have hge : 2 * (n * n) ≤ 2 * (n * n) * (ℓ₀ + 1 + 1) := Nat.le_mul_of_pos_right _ (by omega)
  refine wp_eighProgInit md p n ℓ₀ hlit (A := A) (par := par) (Ma := H.Ma) (Sz := H.Sz)
    (Lv := H.Lv) (A₀ := A₀) (R₀ := R₀) (ε := ε) hMaA hSzA hSzp hLvp hMap hMaSz hLvSz hLvMa
    (pairLayout_holds_of_read_eq hA fun i _ _ => hm1.2 p A i (by fp_omega [hAc]))
    ⟨(hm1.2 p par 0 (by fp_omega [hpc])).trans hpar.1,
      (hm1.2 p par 1 (by fp_omega [hpc])).trans hpar.2.1⟩
    (Mode.needs_of ⟨fun i hi => ⟨_, by rw [hsh1]; exact hshSz, by omega⟩,
      fun i hi => ⟨_, by rw [hsh1]; exact hshMa, by omega⟩,
      fun i hi => ⟨_, by rw [hsh1]; exact hshLv, by omega⟩⟩ md)
    fun s2 hm2 hp2 ⟨hSz0, hSz, hMa', hLv0, hLv1⟩ => ?_
  have hsh2 : s2.store.shape = s.store.shape := hm2.1.trans hsh1
  have fc : ∀ j, s2.store.read p c j = s1.store.read p c j := fun j =>
    hm2.2 p c j (by fp_omega [hSzc, hMac, hLvc])
  have fp : ∀ j, s2.store.read p par j = s.store.read p par j := fun j =>
    (hm2.2 p par j (by fp_omega [hSzp, hMap, hLvp])).trans (hm1.2 p par j (by fp_omega [hpc]))
  refine wp_eighProgPasses hmm hqr md p n ℓ₀ F hsem hflag hcmp hlit htn H hbufs hUH hdH
    (U := U) (dv := dv) (A₀ := A₀) (R₀ := R₀) (ε := ε) (β := β) (s := s2)
    (fun x hx => (hlt x hx).trans_eq (Store.size_eq_of_shape_eq hsh2).symm)
    (EighArenas.Shaped.of_shape_eq (fun x _ => by rw [hsh2]) hH)
    (levelHolds_zero_of_init hlit htn hSz0 hSz hMa' hLv0 hLv1) (fun e lo he1 he2 hlo => ?_)
    (hp2.trans hp1 ▸ hpos) ⟨(fp 0).trans hpar.1, (fp 2).trans hpar.2.2⟩
    ⟨(fc 0).trans hc.1, (fc 1).trans hc.2.1, (fc 2).trans hc.2.2.1, (fc 3).trans hc.2.2.2.1,
      (fc 4).trans hc.2.2.2.2⟩ (by rw [hsh2]; exact hSu) (by rw [hsh2]; exact hSg)
    (hN.mono fun h => ⟨h.1, h.2.1, h.2.2.1.of_shape_eq hsh2, h.2.2.2.of_shape_eq hsh2⟩)
    fun s4 hm4 hU hd => hk s4 (modifies_eighProgBody hm1 hm2 hm4) hU hd
  have h1 : n * e ≤ n * (ℓ₀ + 1) := Nat.mul_le_mul_left _ he2
  have h2 : n ≤ n * e := Nat.le_mul_of_pos_right _ he1
  have h3 : n * (ℓ₀ + 1 + 1) = n * (ℓ₀ + 1) + n := by ring
  exact readsIdx_of_read_eq_lit hlit htn (k := 0) (by omega) (hSz _ (by omega) (by omega))

/-- **The lengths of the eleven buffers** that `NLAlib.eighProg` allocates, in order: the
constants, the node matrices and outputs, the bases, the eigenvalues, the sizes, the kinds and
splits, the windows, and the samples. -/
def eighAllocLens (n ℓ₀ : ℕ) : List ℕ :=
  [5, 2 * (n * n) * (ℓ₀ + 1 + 1), 2 * (n * n) * (ℓ₀ + 1 + 1), 2 * (n * n) * (ℓ₀ + 1),
    n * (ℓ₀ + 1 + 1), n * (ℓ₀ + 1 + 1) + 1, n * (ℓ₀ + 1), n * (ℓ₀ + 1), 2 * (ℓ₀ + 1 + 1), n,
    4 * (n * n)]

omit [DecidableEq P] [Inhabited K] in
/-- The eleven buffers of the driver have the shapes of their allocations. -/
theorem shaped_eighAllocs {s : Store P K} {p : P} {n ℓ₀ b : ℕ}
    (hsh : ∀ j, j < 11 → s.shape[b + j]? = some (p, (eighAllocLens n ℓ₀).getD j 0)) :
    (⟨b + 1, b + 2, b + 3, b + 4, b + 5, b + 6, b + 7, b + 8⟩ : EighArenas).Shaped s p n (ℓ₀ + 1) ∧
      s.shape[b + 0]? = some (p, 5) ∧ s.shape[b + 9]? = some (p, n) ∧
      s.shape[b + 10]? = some (p, 4 * (n * n)) := by
  refine ⟨⟨by simp [EighArenas.handles], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  all_goals first
    | simpa [eighAllocLens] using hsh 0 (by omega) | simpa [eighAllocLens] using hsh 1 (by omega)
    | simpa [eighAllocLens] using hsh 2 (by omega) | simpa [eighAllocLens] using hsh 3 (by omega)
    | simpa [eighAllocLens] using hsh 4 (by omega) | simpa [eighAllocLens] using hsh 5 (by omega)
    | simpa [eighAllocLens] using hsh 6 (by omega) | simpa [eighAllocLens] using hsh 7 (by omega)
    | simpa [eighAllocLens] using hsh 8 (by omega) | simpa [eighAllocLens] using hsh 9 (by omega)
    | simpa [eighAllocLens] using hsh 10 (by omega)

omit [Inhabited K] [AddMonoid C] in
/-- The footprint of the body of the driver lies in the blocks of its allocations. -/
theorem modifies_eighAllocs {s s' : Store P K} {p : P} {n ℓ₀ b U dv : ℕ}
    (hsh : ∀ j, j < 11 → s.shape[b + j]? = some (p, (eighAllocLens n ℓ₀).getD j 0))
    (hm : Modifies ([(U, 0, 2 * (n * n)), (dv, 0, n), (b + 0, 0, 5)] ++ eighArenaFp
      ⟨b + 1, b + 2, b + 3, b + 4, b + 5, b + 6, b + 7, b + 8⟩ n (ℓ₀ + 1) (b + 9) (b + 10)) s s') :
    Modifies ([(U, 0, 2 * (n * n)), (dv, 0, n)] ++ (List.range (10 + 1)).map
      fun i => (b + i, 0, (eighAllocLens n ℓ₀).getD i 0)) s s' := by
  have hmem : ∀ j < 11, (b + j, 0, (eighAllocLens n ℓ₀).getD j 0) ∈
      [(U, 0, 2 * (n * n)), (dv, 0, n)] ++ (List.range (10 + 1)).map
        fun i => (b + i, 0, (eighAllocLens n ℓ₀).getD i 0) := fun j hj =>
    List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩)
  refine hm.of_sub_shape (p := p) fun x hx => ?_
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, eighArenaFp] at hx
  rcases hx with (rfl | rfl | rfl) | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨(U, 0, 2 * (n * n)), by simp, rfl, le_rfl, Or.inl le_rfl⟩
  · exact ⟨(dv, 0, n), by simp, rfl, le_rfl, Or.inl le_rfl⟩
  all_goals first
    | exact ⟨_, hmem 3 (by omega), rfl, le_rfl,
        Or.inr ⟨_, hsh 3 (by omega), by simp [eighAllocLens]⟩⟩
    | exact ⟨_, hmem 6 (by omega), rfl, le_rfl,
        Or.inr ⟨_, hsh 6 (by omega), by simp [eighAllocLens]⟩⟩
    | exact ⟨_, hmem 7 (by omega), rfl, le_rfl,
        Or.inr ⟨_, hsh 7 (by omega), by simp [eighAllocLens]⟩⟩
    | exact ⟨_, hmem 0 (by omega), rfl, le_rfl, Or.inl (by simp [eighAllocLens])⟩
    | exact ⟨_, hmem 1 (by omega), rfl, le_rfl, Or.inl (by simp [eighAllocLens])⟩
    | exact ⟨_, hmem 2 (by omega), rfl, le_rfl, Or.inl (by simp [eighAllocLens])⟩
    | exact ⟨_, hmem 4 (by omega), rfl, le_rfl, Or.inl (by simp [eighAllocLens])⟩
    | exact ⟨_, hmem 5 (by omega), rfl, le_rfl, Or.inl (by simp [eighAllocLens])⟩
    | exact ⟨_, hmem 8 (by omega), rfl, le_rfl, Or.inl (by simp [eighAllocLens])⟩
    | exact ⟨_, hmem 9 (by omega), rfl, le_rfl, Or.inl (by simp [eighAllocLens])⟩
    | exact ⟨_, hmem 10 (by omega), rfl, le_rfl, Or.inl (by simp [eighAllocLens])⟩

/-- **The spectral bisection program as a routine specification**. -/
theorem spec_eighProg {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) (md : Mode) {u : P → ℝ} {dec : P → K → ℝ}
    {safe : P → ℝ → Prop} (p : P) (n ℓ₀ F : ℕ)
    (hsem : md.Needs (IsRelErrSem u dec safe I.sem ∧ (∀ p x, safe p x) ∧ u p < 1))
    (hflag : I.sem.DecidesFlags p)
    (hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y)))
    (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem)
    {A par U dv b : ℕ} {A₀ : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hbuf : ∀ j ∈ [A, par, U, dv], j < b) :
    RoutineSpec md I (fun st => st.store.size = b ∧ pairLayout.Holds st.store p A 0 A₀ ∧
        (st.store.read p par 0 = some R₀ ∧ st.store.read p par 1 = some ε ∧
          st.store.read p par 2 = some β) ∧ (st.pos .uniform = 0 ∧ st.pos .gaussian = 0) ∧
        md.Needs (0 ≤ dec p R₀ ∧ 1 ≤ ℓ₀ ∧ Writable st.store p U 0 (2 * (n * n)) ∧
          Writable st.store p dv 0 n))
      (eighProg p mm qr (.const n) (.const ℓ₀) (.const F) A par U dv)
      [(U, 0, 2 * (n * n)), (dv, 0, n)] fun _ st' =>
        (U ≠ dv → pairLayout.Holds st'.store p U 0 (eighSlotOut I p mmR qrR n F ℓ₀ A₀ R₀ ε β).1) ∧
        ∀ i : Fin n, st'.store.read p dv i =
          some ((eighSlotOut I p mmR qrR n F ℓ₀ A₀ R₀ ε β).2 i) := by
  obtain ⟨Post, hPost⟩ : ∃ Post : St P K C → St P K C → Prop, Post = fun st st' =>
      (U ≠ dv → pairLayout.Holds st'.store p U 0 (eighSlotOut I p mmR qrR n F ℓ₀ A₀ R₀ ε β).1) ∧
      ∀ i : Fin n, st'.store.read p dv i =
        some ((eighSlotOut I p mmR qrR n F ℓ₀ A₀ R₀ ε β).2 i) := ⟨_, rfl⟩
  suffices h : RoutineSpec md I (fun st => st.store.size = b ∧ pairLayout.Holds st.store p A 0 A₀ ∧
        (st.store.read p par 0 = some R₀ ∧ st.store.read p par 1 = some ε ∧
          st.store.read p par 2 = some β) ∧ (st.pos .uniform = 0 ∧ st.pos .gaussian = 0) ∧
        md.Needs (0 ≤ dec p R₀ ∧ 1 ≤ ℓ₀ ∧ Writable st.store p U 0 (2 * (n * n)) ∧
          Writable st.store p dv 0 n))
      (eighProg p mm qr (.const n) (.const ℓ₀) (.const F) A par U dv)
      [(U, 0, 2 * (n * n)), (dv, 0, n)] Post by rw [hPost] at h; exact h
  unfold eighProg
  have hb : ∀ st : St P K C, (st.store.size = b ∧ pairLayout.Holds st.store p A 0 A₀ ∧
      (st.store.read p par 0 = some R₀ ∧ st.store.read p par 1 = some ε ∧
        st.store.read p par 2 = some β) ∧ (st.pos .uniform = 0 ∧ st.pos .gaussian = 0) ∧
      md.Needs (0 ≤ dec p R₀ ∧ 1 ≤ ℓ₀ ∧ Writable st.store p U 0 (2 * (n * n)) ∧
        Writable st.store p dv 0 n)) → st.store.size = b := fun st h => h.1
  refine RoutineSpec.scope (Spec.conseq (spec_allocBind_chain (m := md) (I := I) (p := p)
    (fp := [(U, 0, 2 * (n * n)), (dv, 0, n)]) (b := b)
    (pre := fun st => st.store.size = b ∧ pairLayout.Holds st.store p A 0 A₀ ∧
        (st.store.read p par 0 = some R₀ ∧ st.store.read p par 1 = some ε ∧
          st.store.read p par 2 = some β) ∧ (st.pos .uniform = 0 ∧ st.pos .gaussian = 0) ∧
        md.Needs (0 ≤ dec p R₀ ∧ 1 ≤ ℓ₀ ∧ Writable st.store p U 0 (2 * (n * n)) ∧
          Writable st.store p dv 0 n))
    (post := Post)
    (eighAllocLens n ℓ₀) 0 rfl hb ?_) (fun s hs => ⟨s, hs, rfl⟩) (fun x hx => by simpa using hx)
    fun s _ hs hp => hp s hs rfl)
  iterate 10 (refine spec_allocBind_chain (eighAllocLens n ℓ₀) _ ?_ hb ?_; rotate_left)
  · rintro s ⟨st, ⟨hsz, hA, hpar, hpos, hN⟩, rfl⟩
    have htk : (eighAllocLens n ℓ₀).take (10 + 1) = eighAllocLens n ℓ₀ := by
      simp [eighAllocLens]
    rw [htk]
    obtain ⟨hs, hold, hnew, hp⟩ := St.allocs_facts st p (I.width p)
      ((eighAllocLens n ℓ₀).take (10 + 1))
    rw [htk] at hs hold hnew hp
    have hlen : (eighAllocLens n ℓ₀).length = 11 := by simp [eighAllocLens]
    rw [hlen, hsz] at hs
    have hsh : ∀ j, j < 11 → (st.allocs p (I.width p) (eighAllocLens n ℓ₀)).store.shape[b + j]? =
        some (p, (eighAllocLens n ℓ₀).getD j 0) := fun j hj => by
      have := hnew j (by omega)
      rwa [hsz] at this
    obtain ⟨hH, hsc, hSu, hSg⟩ := shaped_eighAllocs hsh
    set s := st.allocs p (I.width p) (eighAllocLens n ℓ₀) with hsdef
    have hAb : A < st.store.size := hsz ▸ hbuf A (by simp)
    have hpb : par < st.store.size := hsz ▸ hbuf par (by simp)
    have hUb : U < st.store.size := hsz ▸ hbuf U (by simp)
    have hdb : dv < st.store.size := hsz ▸ hbuf dv (by simp)
    refine wp_eighProgBody hmm hqr md p n ℓ₀ F hsem hflag hcmp hlit htn
      (⟨b + 1, b + 2, b + 3, b + 4, b + 5, b + 6, b + 7, b + 8⟩ : EighArenas) (A := A) (par := par)
      (U := U) (dv := dv) (Su := b + 9) (Sg := b + 10) (c := b + 0) (A₀ := A₀) (R₀ := R₀)
      (ε := ε) (β := β) (by simp [EighArenas.handles]; omega) (fun x hx => by
        have := hbuf x hx
        simp [EighArenas.handles]; omega) (fun x hx => ?_) hH hsc hSu hSg
      (pairLayout_holds_of_read_eq hA fun i _ _ => (hold A hAb).2 p i)
      ⟨((hold par hpb).2 p 0).trans hpar.1, ((hold par hpb).2 p 1).trans hpar.2.1,
        ((hold par hpb).2 p 2).trans hpar.2.2⟩ (by rw [hp]; exact hpos)
      (hN.mono fun h => ⟨h.1, h.2.1, fun i hi => ?_, fun i hi => ?_⟩) fun s' hm hU hd => ?_
    · simp only [EighArenas.handles, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at hx
      rw [hs]
      omega
    · obtain ⟨len, hl, hlt⟩ := h.2.2.1 i hi
      exact ⟨len, ((hold U hUb).1).trans hl, hlt⟩
    · obtain ⟨len, hl, hlt⟩ := h.2.2.2 i hi
      exact ⟨len, ((hold dv hdb).1).trans hl, hlt⟩
    · refine ⟨modifies_eighAllocs hsh hm, fun st0 _ _ => ?_⟩
      have hsz' : s'.store.size = b + (eighAllocLens n ℓ₀).length := by
        rw [hlen]; exact (Store.size_eq_of_shape_eq hm.1).trans hs
      obtain ⟨-, hrel, -⟩ := St.releases_facts p (I.width p) (eighAllocLens n ℓ₀) s' b hsz'
      rw [hPost]
      exact ⟨fun hUdv => pairLayout_holds_of_read_eq (hU hUdv) fun i _ _ =>
        (hrel U (hsz ▸ hbuf U (by simp))).2 p _,
        fun i => ((hrel dv (hsz ▸ hbuf dv (by simp))).2 p i).trans (hd i)⟩
  all_goals rfl

/-- **The refinement of the spectral bisection program, partial equality**: let the kernels `mm`,
`qr` of `I` be the routines `mmR`, `qrR` on interleaved pairs, and the semantics decide flags at
`p`, with exact integer literals up to $n + 4$ and the exact floor conversion. A successful run of
`NLAlib.eighProg` at size $n$, depth counter $\ell_0$ and step limit $F$, from a state with the tape
positions at $0$, whose block at offset $0$ of `A` holds the stored $\mathbf{A}$ and whose cells
$0$, $1$, $2$ of `par` hold $R_0$, $\varepsilon$, $\beta$, ends with the block at offset $0$ of `U`
and the cells $0, \ldots, n - 1$ of `dv` holding exactly
$$\mathsf{eigh}(\mathbf{A}, R_0, \varepsilon, \beta)$$
computed by `NLAlib.eigh` with step limit $F$ and depth counter $\ell_0$ on the machine of the
interpretation (`NLAlib.eighTapeMachine`), with the tree of samples at the slots
(`NLAlib.eighSlotTree`). [Shah2024, Algorithm 3], for the program. No printed source. -/
theorem holds_of_exec_eighProg {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {dec : P → K → ℝ} (p : P) (hflag : I.sem.DecidesFlags p)
    (hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y)))
    (n ℓ₀ F : ℕ) (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem)
    {A par U dv : ℕ} {st st' : St P K C} {A₀ : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hbufs : [A, par, U, dv].Nodup) (hsize : ∀ j ∈ [A, par, U, dv], j < st.store.size)
    (hA : pairLayout.Holds st.store p A 0 A₀)
    (hpar : st.store.read p par 0 = some R₀ ∧ st.store.read p par 1 = some ε ∧
      st.store.read p par 2 = some β)
    (hpos : st.pos .uniform = 0 ∧ st.pos .gaussian = 0)
    (h : exec I (eighProg p mm qr (.const n) (.const ℓ₀) (.const F) A par U dv).run st =
      some st') :
    let M := eighTapeMachine I p mmR qrR
    let r := eigh M F ℓ₀ A₀ R₀ ε β (eighSlotTree M n F R₀ β 0 0 ⟨n, A₀, R₀, ε, ℓ₀⟩)
    pairLayout.Holds st'.store p U 0 r.1 ∧ ∀ i : Fin n, st'.store.read p dv i = some (r.2 i) := by
  have hUdv : U ≠ dv := by
    intro e
    simp [e] at hbufs
  obtain ⟨-, hU, hd⟩ := (spec_eighProg hmm hqr .liberal (u := fun _ => 0)
    (safe := fun _ _ => True) p n ℓ₀ F trivial hflag hcmp hlit htn (A₀ := A₀) (R₀ := R₀)
    (ε := ε) (β := β) (b := st.store.size) hsize).spec.holds_of_exec
    ⟨rfl, hA, hpar, hpos, trivial⟩ h
  exact ⟨hU hUdv, hd⟩

end NLAlib
