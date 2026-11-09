/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SpectralBisectionClamp
public import NLAlib.Matrix.Computation.SpectralBisectionNode.Setup

/-!
# The node step of the spectral bisection program

The blocks of the node step of `NLAlib.eighProg` compute the matching operations of
`NLAlib.eighStep` on the machine of the semantics (`NLAlib.Computation.ScalarSem.toFloatMachine`,
`NLAlib.eighTapeMachine`). Each value statement is a partial equality: under kernels that are
routines on pairs and a semantics that decides flags, a successful run writes exactly the machine's
value, with no contract on the rounding. The blocks are in the files
`NLAlib/Matrix/Computation/SpectralBisectionNode/*.lean`; this file assembles the branch after the
index binder (one child or a split) and the whole node step, as routine specifications of the
program logic (`docs/design/Computation-ProgramLogic.md`): the set-up, the clamp and the branch
are calls, the split index an index binder, the scratch a chain of allocations.

## Main results

* `NLAlib.spec_eighNodeBranch`, `NLAlib.spec_eighNodeBody`, `NLAlib.spec_eighNodeBlock`: the
  branch, the body and the node step as routine specifications.
* `NLAlib.holds_of_exec_eighNodeBlock`: the node step computes `NLAlib.eighStep`.
* `NLAlib.holds_of_exec_eighNodeBlock_frame`: the same, with the window it writes.
* `NLAlib.spec_eighWhen`: a guarded block as a specification of the program logic.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {Su Sg : Type} {toNat : K → ℕ} {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}
  {unif : K → Su → K} {normal : Sg → K × K}

omit [Inhabited K] in
/-- A loop of no iterations. -/
theorem eq_of_exec_loop_of_eval_eq_zero {e : IExp ℕ} {b : ℕ → Stmt P ι ℕ ℕ} {s s' : St P K C}
    (he : e.eval = 0) (h : exec I (.seq (.loop e b) .skip) s = some s') : s' = s := by
  rw [exec_seq_skip, exec_loop, he] at h
  simp only [List.range_zero, List.foldlM_nil] at h
  exact (Option.some_inj.mp h).symm

omit [Inhabited K] in
/-- A loop of one iteration. -/
theorem exec_loop_one_eq {e : IExp ℕ} {b : ℕ → Stmt P ι ℕ ℕ} {s s' : St P K C}
    (he : e.eval = 1) (h : exec I (.seq (.loop e b) .skip) s = some s') :
    exec I (b 0) s = some s' := by
  rw [exec_seq_skip, exec_loop, he] at h
  simpa [List.range_one] using h

omit [Inhabited K] in
/-- **A guarded block as a specification**: `NLAlib.eighWhen e body` (a loop of
$1 - (1 - e)$ trips) leaves the state unchanged if $e = 0$ and meets the body's specification if
$e > 0$. No printed source. -/
theorem spec_eighWhen {m : Mode} {e : IExp ℕ} {body : Builder P ι ℕ ℕ Unit}
    {pre : St P K C → Prop} {fp : List (ℕ × ℕ × ℕ)} {post : St P K C → St P K C → Prop}
    (h : 0 < e.eval → Spec m I pre body.run fp post) :
    RoutineSpec m I pre (eighWhen e body) fp
      fun st st' => (e.eval = 0 → st' = st) ∧ (0 < e.eval → post st st') := by
  refine ⟨executionComposable_forRange _ _, fun st hst => (wp_seq).mpr ?_⟩
  rw [Wp, exec_loop]
  rcases Nat.eq_zero_or_pos e.eval with he | he
  · rw [show (1 - (1 - e)).eval = 0 by simp [he], List.range_zero, List.foldlM_nil]
    exact Mode.sat_some.mpr ((wp_skip).mpr ⟨Modifies.refl _ _, fun _ => rfl, by omega⟩)
  · rw [show (1 - (1 - e)).eval = 1 by simp; omega, List.range_one, List.foldlM_cons]
    simp only [List.foldlM_nil, bind_pure]
    exact Mode.Sat.mono (h he st hst) fun st' hp =>
      (wp_skip).mpr ⟨hp.1, fun h0 => absurd h0 (by omega), fun _ => hp.2⟩

omit [Inhabited K] in
/-- A guarded block, then the rest. -/
theorem run_eighWhen_bind {e : IExp ℕ} {b : Builder P ι ℕ ℕ Unit}
    {f : Unit → Builder P ι ℕ ℕ Unit} {st st' : St P K C}
    (h : exec I (eighWhen e b >>= f).run st = some st') :
    ∃ σ, exec I (.seq (.loop (1 - (1 - e)) fun _ => b.run) .skip) st = some σ ∧
      exec I (f ()).run σ = some st' := by
  rw [exec_run_bind I (b := eighWhen e b) (fun _ => rfl)] at h
  exact Option.bind_eq_some_iff.mp h

omit [Inhabited K] in
/-- The run of a scoped index binder, inverted. -/
theorem exists_of_exec_bindIdx {p : P} {x : Cell ℕ ℕ} {bound : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ}
    {st st' : St P K C} (h : exec I (.seq (.bindIdx p x bound body) .skip) st = some st') :
    ∃ v w, st.store.read p x.buf x.idx.eval = some w ∧ I.sem.toNat p w = some v ∧
      v ≤ bound.eval ∧
      exec I (body v) { st with cnt := st.cnt + I.charge (.toNat p) } = some st' := by
  rw [exec_seq_skip, exec_bindIdx] at h
  obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
  unfold toNatStep at hr
  obtain ⟨w, hw, hr⟩ := Option.bind_eq_some_iff.mp hr
  obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hr
  split_ifs at h with hle
  exact ⟨v, w, hw, hv, hle, h⟩

/-- The outcome of a node step's branch at the split index $k_+$, in the store `s`: for
$k_+ = k$ one child on the positive side, for $k_+ = 0$ one on the negative side, for
$0 < k_+ < k$ the split of `NLAlib.holds_of_exec_eighSplitBlock` (bases from `Ppv`, `Pmv`). -/
abbrev EighBranchHolds (I : Interp P ι K C) (p : P) (mmR : MatMulMap (K × K))
    (qrR : QRMap (K × K)) (H : EighArenas) (n d lo k kp : ℕ)
    (A Ppv Pmv : Matrix (Fin k) (Fin k) (K × K)) (half : K) (s : Store P K) : Prop :=
  let M := eighTapeMachine I p mmR qrR
  (kp = k → pairLayout.Holds s p H.Ma (2 * (n * n) * (d + 1) + 2 * n * lo)
      (M.hermShift A half) ∧
    s.read p H.Sz (n * (d + 1) + lo) = I.sem.lit p ((k : ℕ) : ℚ) ∧
    s.read p H.Kd (n * d + lo) = I.sem.lit p ((2 : ℕ) : ℚ)) ∧
  (kp = 0 → pairLayout.Holds s p H.Ma (2 * (n * n) * (d + 1) + 2 * n * lo)
      (M.hermShift A (M.neg half)) ∧
    s.read p H.Sz (n * (d + 1) + lo) = I.sem.lit p ((k : ℕ) : ℚ) ∧
    s.read p H.Kd (n * d + lo) = I.sem.lit p ((3 : ℕ) : ℚ)) ∧
  (0 < kp → kp < k →
    let smp := eighTapeSample n d lo
    let Qp := deflate M kp Ppv (leadingBlock k (smp.2 true))
    let Qm := deflate M (k - kp) Pmv (leadingBlock k (smp.2 false))
    pairLayout.Holds s p H.Qa (2 * (n * n) * d + 2 * n * lo) Qp ∧
    pairLayout.Holds s p H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (k * kp)) Qm ∧
    pairLayout.Holds s p H.Ma (2 * (n * n) * (d + 1) + 2 * n * lo)
      (M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Qp) A) Qp) (M.ofNat 2)) half) ∧
    pairLayout.Holds s p H.Ma (2 * (n * n) * (d + 1) + 2 * n * (lo + kp))
      (M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Qm) A) Qm) (M.ofNat 2))
        (M.neg half)) ∧
    s.read p H.Sz (n * (d + 1) + lo) = I.sem.lit p ((kp : ℕ) : ℚ) ∧
    s.read p H.Sz (n * (d + 1) + (lo + kp)) = I.sem.lit p ((k - kp : ℕ) : ℚ) ∧
    s.read p H.Kd (n * d + lo) = I.sem.lit p ((4 : ℕ) : ℚ) ∧
    s.read p H.Kp (n * d + lo) = I.sem.lit p ((kp : ℕ) : ℚ))

/-- The blocks one child of a node step writes: its matrix at the slot of depth $d + 1$, its size
and its kind. -/
def eighChildWindow (H : EighArenas) (n d lo k : ℕ) : List (ℕ × ℕ × ℕ) :=
  [matBlock H.Ma (2 * (n * n) * (d + 1) + 2 * n * lo) k k 2, (H.Sz, n * (d + 1) + lo, 1),
    (H.Kd, n * d + lo, 1)]

/-- The blocks a node step's branch writes at the split index $k_+$: a split's window for
$0 < k_+ < k$, a child's otherwise. -/
def eighBranchWindow (H : EighArenas) (n d lo k kp : ℕ) : List (ℕ × ℕ × ℕ) :=
  if 0 < kp ∧ kp < k then eighSplitWindow H n d lo k kp else eighChildWindow H n d lo k

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- A cell outside a child's node window is disjoint from every block of the child's window. -/
theorem blockDisjoint_eighChildWindow {H : EighArenas} {n d lo k j b i : ℕ} (hk : lo + k ≤ n)
    (hW : ¬ EighNodeWindow H n d lo k j b i) :
    ∀ x ∈ eighChildWindow H n d lo k, blockDisjoint (b, i, 1) x = true := by
  have hkk : k * k ≤ n * k := Nat.mul_le_mul_right k (by omega)
  simp only [EighNodeWindow, not_or, not_and, not_lt] at hW
  obtain ⟨-, hWM, hWS, hWK⟩ := hW
  simp only [eighChildWindow, List.forall_mem_cons, matBlock, blockDisjoint_iff]
  refine ⟨?_, ?_, ?_, fun x hx => absurd hx List.not_mem_nil⟩
  · by_cases hb : b = H.Ma
    · have := hWM hb
      have key : i + 1 ≤ 2 * (n * n) * (d + 1) + 2 * n * lo ∨
          2 * (n * n) * (d + 1) + 2 * n * lo + k * k * 2 ≤ i := by
        by_cases hi : 2 * (n * n) * (d + 1) + 2 * n * lo ≤ i
        · have := this hi; right; nlinarith
        · left; omega
      omega
    · exact Or.inl hb
  · by_cases hb : b = H.Sz
    · have := hWS hb; omega
    · exact Or.inl hb
  · by_cases hb : b = H.Kd
    · have := hWK (Or.inl hb); omega
    · exact Or.inl hb

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- The window of a node step's branch is writable in arenas of depth $D > d$. -/
theorem writableBlocks_eighBranchWindow {H : EighArenas} {s : Store P K} {p : P}
    {n d lo k kp D : ℕ} (hk : lo + k ≤ n) (hk0 : 0 < k) (hd : d < D) (hH : H.Shaped s p n D) :
    WritableBlocks s p (eighBranchWindow H n d lo k kp) := by
  unfold eighBranchWindow
  split_ifs with hs
  · exact writableBlocks_eighSplitWindow hk hs.2 hd hH
  obtain ⟨-, hMa, -, -, -, hSz, hKd, -, -⟩ := hH
  have hlok : n * lo + n * k ≤ n * n := by rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ hk
  have hkk : k * k ≤ n * k := Nat.mul_le_mul_right k (by omega)
  have hdD : n * n * (d + 1) + n * n ≤ n * n * (D + 1) := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
  have h1 := Nat.mul_le_mul_left n (show d + 2 ≤ D + 1 by omega)
  have h2 := Nat.mul_le_mul_left n (show d + 1 ≤ D by omega)
  simp only [WritableBlocks, eighChildWindow, List.forall_mem_cons]
  exact ⟨writable_of_shape_eq rfl hMa (by simp only [matBlock]; nlinarith),
    writable_of_shape_eq rfl hSz (by nlinarith), writable_of_shape_eq rfl hKd (by nlinarith),
    fun x hx => absurd hx List.not_mem_nil⟩

/-- **The branch of a node step at a fixed split index, as a specification**: for $k_+ \le k$,
the three guarded blocks run one child ($k_+ = k$ or $k_+ = 0$) or the split, modify only the
branch's window and keep the tape positions; with the level's tape words in `Sg` and the
literal $\mathrm{fl}(2)$ in the cell `two`, the window then holds the outcome of
`NLAlib.eighStep`'s branch. In mode `total` the run also succeeds, given the standard model, the
window writable and the literals. No printed source. -/
theorem spec_eighNodeBranch {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) (md : Mode) {u : P → ℝ} {dec : P → K → ℝ}
    {safe : P → ℝ → Prop} (hsem : md.Needs (IsRelErrSem u dec safe I.sem ∧ ∀ p x, safe p x))
    (p : P) (n d lo k : ℕ) (hk : lo + k ≤ n) (hk2 : 2 ≤ k) (H : EighArenas) {Sg c t Pp Pm : ℕ}
    (A Ppv Pmv : Matrix (Fin k) (Fin k) (K × K)) (c₂ half : K) (kp : ℕ) (hkpk : kp ≤ k) (b : ℕ)
    (hbufs : (H.handles ++ [Sg, Pp, Pm]).Nodup) (hcS : c ∉ H.handles ++ [Sg, Pp, Pm])
    (htS : t ∉ H.handles ++ [Sg, Pp, Pm]) (hlt : ∀ x ∈ H.handles ++ [Sg, Pp, Pm, c, t], x < b) :
    RoutineSpec md I (fun st => st.store.size = b ∧
        pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A ∧
        pairLayout.Holds st.store p Pp 0 Ppv ∧ pairLayout.Holds st.store p Pm 0 Pmv ∧
        (∀ w < 4 * (n * n), ∃ v, st.store.read p Sg w = some v) ∧
        (md = .liberal → ∀ w < 4 * (n * n),
          st.store.read p Sg w = some (I.tape .gaussian (4 * (n * n) * d + w))) ∧
        st.store.read p c 1 = some c₂ ∧ st.store.read p c 4 = some (I.sem.sqrtHalf p) ∧
        st.store.read p t 0 = some half ∧
        st.store.read p t 1 = some ((eighTapeMachine I p mmR qrR).neg half) ∧
        md.Needs (dec p c₂ ≠ 0 ∧ WritableBlocks st.store p (eighBranchWindow H n d lo k kp) ∧
          ∀ q : ℕ, ∃ z, I.sem.lit p (q : ℚ) = some z))
      (do
        eighWhen (1 - (.const k - .var kp))
          (eighChildBlock p (.const k) H.Ma (eighBlockOff (.const n) (.const d) (.const lo))
            (eighBlockOff (.const n) (.const d + 1) (.const lo)) ⟨t, 0⟩
            ⟨H.Sz, eighSlotOff (.const n) (.const d + 1) (.const lo)⟩
            ⟨H.Kd, eighSlotOff (.const n) (.const d) (.const lo)⟩ 2)
        eighWhen (1 - .var kp)
          (eighChildBlock p (.const k) H.Ma (eighBlockOff (.const n) (.const d) (.const lo))
            (eighBlockOff (.const n) (.const d + 1) (.const lo)) ⟨t, 1⟩
            ⟨H.Sz, eighSlotOff (.const n) (.const d + 1) (.const lo)⟩
            ⟨H.Kd, eighSlotOff (.const n) (.const d) (.const lo)⟩ 3)
        eighWhen (.var kp * (.const k - .var kp))
          (eighSplitBlock p mm qr (.const n) (.const d) (.const lo) (.const k) (.var kp) Sg Pp Pm
            H.Ma H.Qa H.Sz H.Kd H.Kp ⟨c, 1⟩ ⟨t, 0⟩ ⟨t, 1⟩ ⟨c, 4⟩) : Builder P ι ℕ ℕ Unit)
      (eighBranchWindow H n d lo k kp) fun st st' =>
        ((∀ w < 4 * (n * n), st.store.read p Sg w = some (I.tape .gaussian (4 * (n * n) * d + w)))
          → c₂ = (eighTapeMachine I p mmR qrR).ofNat 2 →
          EighBranchHolds I p mmR qrR H n d lo k kp A Ppv Pmv half st'.store) ∧ PosKept st st' := by
  have hnd := hbufs
  simp only [EighArenas.handles, List.cons_append, List.nil_append, List.nodup_cons,
    List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  have hlok : n * lo + n * k ≤ n * n := by rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ hk
  have hev : ∀ dd, (eighBlockOff (IExp.const n) dd (IExp.const lo)).eval =
      2 * (n * n) * dd.eval + 2 * n * lo := by simp [eighBlockOff]
  have child := fun (code : ℕ) (sg : Cell ℕ ℕ) (σ : K) => spec_eighChildBlock
    (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    (Ma := H.Ma) (mo := eighBlockOff (.const n) (.const d) (.const lo))
    (mo' := eighBlockOff (.const n) (.const d + 1) (.const lo)) (sg := sg)
    (sz := ⟨H.Sz, eighSlotOff (.const n) (.const d + 1) (.const lo)⟩)
    (kd := ⟨H.Kd, eighSlotOff (.const n) (.const d) (.const lo)⟩) md hsem p k code σ A
    (by rw [hev, hev]; exact blockDisjoint_iff.mpr (.inr (.inr (.inr (.inr (by
      simp only [matBlock, IExp.eval_add, IExp.eval_const, IExp.eval_ofNat]
      nlinarith [Nat.mul_le_mul_right k (show k ≤ n by omega)]))))))
    (blockDisjoint_of_fst_ne fun h => hnd.1.2.2.2.1 h.symm)
    (blockDisjoint_of_fst_ne fun h => hnd.1.2.2.2.2.1 h.symm)
    (blockDisjoint_of_fst_ne hnd.2.2.2.2.1.1)
  have htM : t ≠ H.Ma := fun h => htS (by simp [EighArenas.handles, h])
  have hct : ∀ c' ∈ [(⟨c, 1⟩ : Cell ℕ ℕ), ⟨t, 0⟩, ⟨t, 1⟩, ⟨c, 4⟩],
      c'.buf ∉ H.handles ++ [Sg, Pp, Pm] := by
    simp only [List.forall_mem_cons]; exact ⟨hcS, htS, htS, hcS, nofun⟩
  refine ⟨(executionComposable_forRange _ _).bind ((executionComposable_forRange _ _).bind
    (executionComposable_forRange _ _)), fun st ⟨hsz, hA, hPp, hPm, hSg, hT, htwo, hsq, ht0, ht1,
      hN⟩ => ?_⟩
  have hA' := (hev (.const d)).symm ▸ hA
  have hWc := fun (hs : ¬ (0 < kp ∧ kp < k)) => hN.mono fun ⟨_, hw, _⟩ => by
    simp only [eighBranchWindow, if_neg hs, eighChildWindow, WritableBlocks, List.forall_mem_cons,
      matBlock] at hw
    exact (⟨by simpa [hev] using hw.1, by simpa [eighSlotOff] using hw.2.1, by simpa [eighSlotOff]
      using hw.2.2.1⟩ : Writable st.store p H.Ma (eighBlockOff (IExp.const n) (IExp.const d + 1)
      (IExp.const lo)).eval (k * k * 2) ∧ Writable st.store p H.Sz (eighSlotOff (IExp.const n)
      (IExp.const d + 1) (IExp.const lo)).eval 1 ∧ Writable st.store p H.Kd
      (eighSlotOff (IExp.const n) (IExp.const d) (IExp.const lo)).eval 1)
  have none_ := fun {e : IExp ℕ} {bd : Builder P ι ℕ ℕ Unit} (he : e.eval = 0) =>
    spec_eighWhen (I := I) (m := md) (e := e) (body := bd) (pre := fun _ => True) (fp := [])
      (post := fun _ _ => True) fun h => absurd h (by omega)
  rcases Nat.eq_or_lt_of_le hkpk with rfl | hlt'
  · exact (spec_eighWhen (fun _ => (child 2 ⟨t, 0⟩ half).spec)).wp_bind
      ⟨hA', ht0, hWc (by omega)⟩ fun st₁ hm₁ h₁ =>
      (none_ (by simp; omega)).wp_bind trivial fun st₂ hm₂ h₂ =>
      (none_ (by simp)).wp_run trivial fun st₃ hm₃ h₃ => by
        obtain rfl := h₂.1 (by simp; omega)
        obtain rfl := h₃.1 (by simp)
        obtain ⟨hv, hs1, hs2, hp⟩ := h₁.2 (by simp)
        refine ⟨(hm₁.trans hm₂ |>.trans hm₃).mono (by simp [eighBranchWindow, eighChildWindow,
          hev, eighSlotOff]), fun _ _ => ⟨fun _ => ?_, fun h => by omega, fun _ h => by omega⟩, hp⟩
        exact ⟨by simpa [hev, eighTapeMachine] using hv (blockDisjoint_of_fst_ne htM),
          by simpa [eighSlotOff] using hs1, by simpa [eighSlotOff] using hs2⟩
  rcases Nat.eq_zero_or_pos kp with rfl | hpos
  · exact (none_ (by simp; omega)).wp_bind trivial fun st₁ hm₁ h₁ => by
      obtain rfl := h₁.1 (by simp; omega)
      exact (spec_eighWhen (fun _ => (child 3 ⟨t, 1⟩ _).spec)).wp_bind
        ⟨hA', ht1, hWc (by omega)⟩ fun st₂ hm₂ h₂ =>
        (none_ (by simp)).wp_run trivial fun st₃ hm₃ h₃ => by
          obtain rfl := h₃.1 (by simp)
          obtain ⟨hv, hs1, hs2, hp⟩ := h₂.2 (by simp)
          refine ⟨(hm₁.trans hm₂ |>.trans hm₃).mono (by simp [eighBranchWindow, eighChildWindow,
            hev, eighSlotOff]), fun _ _ => ⟨fun h => by omega, fun _ => ?_, fun h => by omega⟩, hp⟩
          exact ⟨by simpa [hev, eighTapeMachine] using hv (blockDisjoint_of_fst_ne htM),
            by simpa [eighSlotOff] using hs1, by simpa [eighSlotOff] using hs2⟩
  have hs : 0 < kp ∧ kp < k := ⟨hpos, hlt'⟩
  exact (none_ (by simp; omega)).wp_bind trivial fun st₁ hm₁ h₁ => by
    obtain rfl := h₁.1 (by simp; omega)
    exact (none_ (by simp; omega)).wp_bind trivial fun st₂ hm₂ h₂ => by
      obtain rfl := h₂.1 (by simp; omega)
      have hsp := spec_eighSplitBlock hmm hqr md hsem p n d lo k hk (.var kp) hpos hlt' H c₂ half
        ((eighTapeMachine I p mmR qrR).neg half) A Ppv Pmv b hbufs hct
        fun x hx => hlt x (List.mem_append.mpr ((List.mem_append.mp hx).imp id fun h => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; omega))
      refine (spec_eighWhen (e := .var kp * (.const k - .var kp)) fun _ => hsp.spec).wp_run
        ⟨hsz, hA, hPp, hPm, hSg, hT, htwo, ht0, ht1, hsq, hN.mono fun ⟨h0, hw, hl⟩ =>
          ⟨h0, by simpa only [IExp.eval_var, eighBranchWindow, if_pos hs] using hw, hl _, hl _,
            hl _⟩⟩
        fun st₃ hm₃ h₃ => ?_
      obtain ⟨hv, hr, hp⟩ := h₃.2 (by simp; omega)
      refine ⟨(hm₁.trans hm₂ |>.trans hm₃).mono (by simp [eighBranchWindow, if_pos hs]),
        fun hT' h2 => ⟨fun h => by omega, fun h => by omega, fun _ _ => ?_⟩, hp⟩
      exact h2 ▸ ⟨(hv hT').1, (hv hT').2.1, (hv hT').2.2.1, (hv hT').2.2.2, hr⟩

/-- The handles of a split inside a node step are distinct, and the constants are not among the
arenas and the samples. -/
theorem nodup_scratch_node {H : EighArenas} {par Su Sg c Pp Pm s₀ : ℕ}
    (hb : (H.handles ++ [par, Su, Sg, c]).Nodup)
    (hlt : ∀ b ∈ H.handles ++ [par, Su, Sg, c], b < s₀) (h1 : s₀ ≤ Pp) (h2 : s₀ ≤ Pm)
    (h3 : Pp ≠ Pm) : (H.handles ++ [Sg, Pp, Pm]).Nodup ∧ c ∉ H.handles ++ [Sg] := by
  have hsub : (H.handles ++ [Sg]).Sublist (H.handles ++ [par, Su, Sg, c]) :=
    List.Sublist.append_left (List.singleton_sublist.mpr (by simp)) _
  have hS := hsub.nodup hb
  refine ⟨?_, ?_⟩
  · rw [show H.handles ++ [Sg, Pp, Pm] = (H.handles ++ [Sg]) ++ [Pp, Pm] by simp]
    refine List.nodup_append.mpr ⟨hS, by simp [h3], fun a ha b hb' => ?_⟩
    have := hlt a (hsub.subset ha)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb'
    omega
  · intro hc
    rw [show H.handles ++ [par, Su, Sg, c] = (H.handles ++ [par, Su, Sg]) ++ [c] by simp] at hb
    have hsub' : (H.handles ++ [Sg]).Sublist (H.handles ++ [par, Su, Sg]) :=
      List.Sublist.append_left (List.singleton_sublist.mpr (by simp)) _
    exact (List.nodup_append.mp hb).2.2 c (hsub'.subset hc) c (by simp) rfl

/-- The handles of a node step's branch: from distinct arenas, `par`, `Su`, `Sg`, `c` below `b`,
the scratch buffers at `b`, `b + 5`, `b + 6` (of a store of $b + 7$ buffers) give the
distinctness and bounds `NLAlib.spec_eighNodeBranch` assumes. -/
private theorem node_branch_handles {H : EighArenas} {par Su Sg c b : ℕ}
    (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup)
    (hlt : ∀ x ∈ H.handles ++ [par, Su, Sg, c], x < b) :
    (H.handles ++ [Sg, b + 5, b + 6]).Nodup ∧ c ∉ H.handles ++ [Sg, b + 5, b + 6] ∧
      b ∉ H.handles ++ [Sg, b + 5, b + 6] ∧
      ∀ x ∈ H.handles ++ [Sg, b + 5, b + 6, c, b], x < b + 7 := by
  obtain ⟨hnd, hcS⟩ := nodup_scratch_node (Pp := b + 5) (Pm := b + 6) hbufs hlt (by omega)
    (by omega) (by omega)
  have lH : ∀ x ∈ H.handles, x < b := fun x hx => hlt x (List.mem_append_left _ hx)
  have lSg : Sg < b := hlt Sg (by simp)
  have lc : c < b := hlt c (by simp)
  refine ⟨hnd, fun h => ?_, fun h => ?_, fun x hx => ?_⟩
  · rcases List.mem_append.mp h with h | h
    · exact hcS (List.mem_append_left _ h)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h
      · exact hcS (by simp [h])
      all_goals omega
  · rcases List.mem_append.mp h with h | h
    · have := lH b h; omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h; omega
  · rcases List.mem_append.mp hx with h | h
    · have := lH x h; omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h; omega

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- The blocks of a node step's branch window lie in the arenas. -/
theorem fst_mem_handles_of_mem_eighBranchWindow {H : EighArenas} {n d lo k kp : ℕ}
    {x : ℕ × ℕ × ℕ} (hx : x ∈ eighBranchWindow H n d lo k kp) : x.1 ∈ H.handles := by
  unfold eighBranchWindow at hx
  split_ifs at hx
  · simp only [eighSplitWindow, matBlock, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [EighArenas.handles]
  · simp only [eighChildWindow, matBlock, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [EighArenas.handles]

omit [AddMonoid C] in
/-- The outcome of a node step's branch is kept by a store that reads as the old one in every
buffer below `N`, the arenas among them. -/
theorem EighBranchHolds.of_read_eq {p : P} {H : EighArenas} {n d lo k kp N : ℕ}
    {A Ppv Pmv : Matrix (Fin k) (Fin k) (K × K)} {half : K} {s s' : Store P K}
    (hH : ∀ x ∈ H.handles, x < N) (hr : ∀ q x i, x < N → s'.read q x i = s.read q x i)
    (h : EighBranchHolds I p mmR qrR H n d lo k kp A Ppv Pmv half s) :
    EighBranchHolds I p mmR qrR H n d lo k kp A Ppv Pmv half s' := by
  have l := fun x (hx : x ∈ H.handles) q i => hr q x i (hH x hx)
  have lQa := l H.Qa (by simp [EighArenas.handles])
  have lMa := l H.Ma (by simp [EighArenas.handles])
  have lSz := l H.Sz (by simp [EighArenas.handles])
  have lKd := l H.Kd (by simp [EighArenas.handles])
  have lKp := l H.Kp (by simp [EighArenas.handles])
  obtain ⟨B1, B2, B3⟩ := h
  refine ⟨fun e => ?_, fun e => ?_, fun h0 h1 => ?_⟩
  · obtain ⟨x1, x2, x3⟩ := B1 e
    exact ⟨fun i j t => (lMa _ _).trans (x1 i j t), (lSz _ _).trans x2, (lKd _ _).trans x3⟩
  · obtain ⟨x1, x2, x3⟩ := B2 e
    exact ⟨fun i j t => (lMa _ _).trans (x1 i j t), (lSz _ _).trans x2, (lKd _ _).trans x3⟩
  · obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8⟩ := B3 h0 h1
    exact ⟨fun i j t => (lQa _ _).trans (x1 i j t), fun i j t => (lQa _ _).trans (x2 i j t),
      fun i j t => (lMa _ _).trans (x3 i j t), fun i j t => (lMa _ _).trans (x4 i j t),
      (lSz _ _).trans x5, (lSz _ _).trans x6, (lKd _ _).trans x7, (lKp _ _).trans x8⟩

/-- **The body of a node step as a specification**: from a state of $b + 7$ buffers whose top
seven are the node step's scratch, holding the node's inputs below $b$ (the matrix
$\mathbf{A}$, the window $R$, $\beta$, the uniform word $v$, the constants $o$, $z_2$, $h$, $m$
and the stored $\sqrt{1/2}$ in the cells $0$ to $4$ of `c`, the Gaussian words $g$ in `Sg`), the
set-up, the clamp and the branch at the split index $k_+ = \min(k, \lfloor\mathrm{fl}(t +
h)\rfloor_+)$ ($t$ the rounded trace of $\mathbf{P}_+$) modify only the branch's window and the
scratch and keep the tape positions; if the Gaussian words are the tape's and $z_2$ is the
machine's $2$, the window then holds the outcome of `NLAlib.eighStep`'s branch. In mode `total`
the run also succeeds, given the standard model on the range `safe` holding everywhere,
$u(p) < 1$, $z_2$ and $R$ decoding to nonzero values, $\ell_0 + d \ge 1$, the window writable and
every integer literal. Exact comparisons, literals up to $k$ and conversion at `p`. No printed
source. -/
theorem spec_eighNodeBody {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) (md : Mode) {u : P → ℝ} {dec : P → K → ℝ}
    {safe : P → ℝ → Prop} (p : P) (n ℓ₀ F d lo k : ℕ)
    (hsem : md.Needs (IsRelErrSem u dec safe I.sem ∧ (∀ p x, safe p x) ∧ u p < 1))
    (hflag : I.sem.DecidesFlags p)
    (hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y)))
    (hlit : IsExactIntLit dec I.sem k) (htn : IsExactToNat dec I.sem) (hk : lo + k ≤ n)
    (hk2 : 2 ≤ k) (H : EighArenas) {par Su Sg c b : ℕ}
    (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup)
    (hlt : ∀ x ∈ H.handles ++ [par, Su, Sg, c], x < b)
    (A Bm Ppm Pmm : Matrix (Fin k) (Fin k) (K × K)) (R β v o z₂ h m : K) (g : ℕ → K) (kp : ℕ)
    (hBm : Bm = newtonSchulzSign (eighTapeMachine I p mmR qrR) β
      ((eighTapeMachine I p mmR qrR).mul z₂ R) F ((eighTapeMachine I p mmR qrR).hermShift A
        ((eighTapeMachine I p mmR qrR).mul ((eighTapeMachine I p mmR qrR).div R
          ((eighTapeMachine I p mmR qrR).ofNat (ℓ₀ + d))) v)))
    (hPp : Ppm = (eighTapeMachine I p mmR qrR).hermScale
      ((eighTapeMachine I p mmR qrR).hermShift Bm m) z₂)
    (hPm : Pmm = (eighTapeMachine I p mmR qrR).hermScale ((eighTapeMachine I p mmR qrR).negMat
      ((eighTapeMachine I p mmR qrR).hermShift Bm o)) z₂)
    (hkp : kp = min k ⌊dec p ((eighTapeMachine I p mmR qrR).add
      ((eighTapeMachine I p mmR qrR).traceRe Ppm) h)⌋₊) :
    Spec md I (fun st => st.store.size = b + 7 ∧
        (pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A ∧
          st.store.read p H.Lv (2 * d) = some R ∧ st.store.read p par 2 = some β ∧
          st.store.read p Su lo = some v ∧ st.store.read p c 0 = some o ∧
          st.store.read p c 1 = some z₂ ∧ st.store.read p c 2 = some h ∧
          st.store.read p c 3 = some m ∧ st.store.read p c 4 = some (I.sem.sqrtHalf p) ∧
          ∀ w < 4 * (n * n), st.store.read p Sg w = some (g w)) ∧
        st.store.shape[b]? = some (p, 7) ∧ st.store.shape[b + 1]? = some (p, 2) ∧
        (∀ j < 5, st.store.shape[b + 2 + j]? = some (p, 2 * (n * n))) ∧
        (md = .liberal → ∀ w < 4 * (n * n), g w = I.tape .gaussian (4 * (n * n) * d + w)) ∧
        md.Needs (dec p z₂ ≠ 0 ∧ dec p R ≠ 0 ∧ 1 ≤ ℓ₀ + d ∧
          WritableBlocks st.store p (eighBranchWindow H n d lo k kp) ∧
          ∀ q : ℕ, ∃ z, I.sem.lit p (q : ℚ) = some z))
      (((do
        ins (.bin p .div ⟨b, 0⟩ ⟨H.Lv, 2 * .const d⟩ ⟨c, 1⟩)
        ins (.un p .neg ⟨b, 1⟩ ⟨b, 0⟩)
        ins (.litIdx p ⟨b, 2⟩ (.const ℓ₀ + .const d))
        ins (.bin p .div ⟨b, 3⟩ ⟨H.Lv, 2 * .const d⟩ ⟨b, 2⟩)
        ins (.bin p .mul ⟨b, 4⟩ ⟨b, 3⟩ ⟨Su, .const lo⟩) : Builder P ι ℕ ℕ Unit) >>= fun _ =>
      (do
        zhermShift p (.const k) H.Ma (eighBlockOff (.const n) (.const d) (.const lo)) ⟨b, 4⟩
          (b + 2) 0
        ins (.copy p ⟨b + 1, 0⟩ ⟨par, 2⟩)
        ins (.bin p .mul ⟨b + 1, 1⟩ ⟨c, 1⟩ ⟨H.Lv, 2 * .const d⟩)
        eighSignBlock p mm (.const k) (.const F) (b + 2) 0 (b + 1) 0 (b + 3) 0 :
          Builder P ι ℕ ℕ Unit) >>= fun _ =>
      (do
        zhermShift p (.const k) (b + 3) 0 ⟨c, 3⟩ (b + 4) 0
        zhermScale p (.const k) (b + 4) 0 ⟨c, 1⟩ (b + 5) 0
        zhermShift p (.const k) (b + 3) 0 ⟨c, 0⟩ (b + 4) 0
        zneg p (.const k) (.const k) (b + 4) 0 (b + 4) 0
        zhermScale p (.const k) (b + 4) 0 ⟨c, 1⟩ (b + 6) 0 : Builder P ι ℕ ℕ Unit) >>= fun _ => do
        ztraceRe p (.const k) (b + 5) 0 ⟨b, 5⟩
        ins (.bin p .add ⟨b, 6⟩ ⟨b, 5⟩ ⟨c, 2⟩)) >>= fun _ => do
        eighClampBlock p (.const k) ⟨b, 6⟩ ⟨b, 2⟩ ⟨b, 3⟩
        Builder.bindIdx p ⟨b, 6⟩ (.const k) fun kp => do
          eighWhen (1 - (.const k - .var kp))
            (eighChildBlock p (.const k) H.Ma (eighBlockOff (.const n) (.const d) (.const lo))
              (eighBlockOff (.const n) (.const d + 1) (.const lo)) ⟨b, 0⟩
              ⟨H.Sz, eighSlotOff (.const n) (.const d + 1) (.const lo)⟩
              ⟨H.Kd, eighSlotOff (.const n) (.const d) (.const lo)⟩ 2)
          eighWhen (1 - .var kp)
            (eighChildBlock p (.const k) H.Ma (eighBlockOff (.const n) (.const d) (.const lo))
              (eighBlockOff (.const n) (.const d + 1) (.const lo)) ⟨b, 1⟩
              ⟨H.Sz, eighSlotOff (.const n) (.const d + 1) (.const lo)⟩
              ⟨H.Kd, eighSlotOff (.const n) (.const d) (.const lo)⟩ 3)
          eighWhen (.var kp * (.const k - .var kp))
            (eighSplitBlock p mm qr (.const n) (.const d) (.const lo) (.const k) (.var kp) Sg
              (b + 5) (b + 6) H.Ma H.Qa H.Sz H.Kd H.Kp ⟨c, 1⟩ ⟨b, 0⟩ ⟨b, 1⟩ ⟨c, 4⟩)).run
      (eighBranchWindow H n d lo k kp ++ [(b, 0, 7), (b + 1, 0, 2), (b + 2, 0, 2 * (n * n)),
        (b + 3, 0, 2 * (n * n)), (b + 4, 0, 2 * (n * n)), (b + 5, 0, 2 * (n * n)),
        (b + 6, 0, 2 * (n * n))])
      fun st st' => ((∀ w < 4 * (n * n), g w = I.tape .gaussian (4 * (n * n) * d + w)) →
        z₂ = (eighTapeMachine I p mmR qrR).ofNat 2 →
        EighBranchHolds I p mmR qrR H n d lo k kp A Ppm Pmm
          ((eighTapeMachine I p mmR qrR).div R z₂) st'.store) ∧ PosKept st st' := by
  have hl := hlt
  simp only [EighArenas.handles, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hl
  obtain ⟨lMa, -, -, -, -, -, -, lLv, lpar, lSu, lSg, lc⟩ := hl
  obtain ⟨hbS, hcS, htS, hlt'⟩ := node_branch_handles hbufs hlt
  intro st ⟨hsz, ⟨hA, hR, hβ, hv, hc0, hc1, hc2, hc3, hc4, hSg⟩, ht, hsp, hW, hT, hN⟩
  have s₁ := spec_eighNodeSetup hmm md p n ℓ₀ F d lo k
    (hsem.mono fun h => ⟨h.1, h.2.1, h.2.2, by omega⟩) hflag (by omega) (Ma := H.Ma)
    (Lv := H.Lv) (par := par) (Su := Su) (c := c) (b := b) ⟨lMa, lLv, lpar, lSu, lc⟩ A Bm Ppm
    Pmm R β v o z₂ h m hBm hPp hPm
  refine s₁.wp_bind_keep ((readsOnly_pairLayoutHolds p H.Ma _ A).and
      ((readsOnly_forall_read p Sg (4 * (n * n)) fun w x => x = some (g w)).and
        (readsOnly_cellsHold [(p, c, 1, some z₂), (p, c, 4, some (I.sem.sqrtHalf p))])))
    (by fp_omega [lMa, lSg, lc])
    ⟨hsz, hA, hR, hβ, hv, hc0, hc1, hc2, hc3, ht, hsp, hW, hN.mono fun h => ⟨h.1, h.2.1, h.2.2.1⟩⟩
    ⟨hA, hSg, ((cellsHold_nil _).cons hc4).cons hc1⟩ fun st₁ hm₁ h₁ hF₁ => ?_
  have s₂ := spec_eighClampBlock (I := I) md hcmp hlit htn (t := b)
    ((eighTapeMachine I p mmR qrR).add ((eighTapeMachine I p mmR qrR).traceRe Ppm) h)
  refine s₂.wp_bind_keep ((((readsOnly_pairLayoutHolds p H.Ma _ A).and
      ((readsOnly_forall_read p Sg (4 * (n * n)) fun w x => x = some (g w)).and
        (readsOnly_cellsHold _))).and (readsOnly_cellsHold [(p, b, 0, some
          ((eighTapeMachine I p mmR qrR).div R z₂)), (p, b, 1, some ((eighTapeMachine I p mmR
            qrR).neg ((eighTapeMachine I p mmR qrR).div R z₂)))])).and
      ((readsOnly_pairLayoutHolds p (b + 5) 0 Ppm).and (readsOnly_pairLayoutHolds p (b + 6) 0
        Pmm))) (by fp_omega [lMa, lSg, lc]) h₁.2.2.1
    ⟨⟨hF₁, ((cellsHold_nil _).cons h₁.2.1).cons h₁.1⟩, h₁.2.2.2.1, h₁.2.2.2.2.1⟩
    fun st₂ hm₂ ⟨⟨wc, hwc, hwk⟩, hp₂⟩ ⟨⟨⟨hA₂, hSg₂, hC₂⟩, hT₂⟩, hPp₂, hPm₂⟩ => ?_
  have hkk : kp ≤ k := hkp ▸ min_le_left _ _
  refine (RoutineSpec.bindIdx_of_read (m := md) (I := I) (pre := fun s => s = st₂)
    (x := ⟨b, 6⟩) (bound := .const k) (fun _ e => e ▸ hwc) (hkp ▸ hwk) (Mode.needs_of hkk md)
    (fun _ => (spec_eighNodeBranch hmm hqr md (hsem.mono fun h => ⟨h.1, h.2.1⟩) p n d lo k hk hk2
      H (Sg := Sg) (c := c) (t := b) (Pp := b + 5) (Pm := b + 6) A Ppm Pmm z₂
      ((eighTapeMachine I p mmR qrR).div R z₂) kp hkk (b + 7) hbS hcS htS hlt').spec)
    ?_).wp_run rfl ?_
  · rintro _ rfl
    exact ⟨(Store.size_eq_of_shape_eq (hm₁.trans hm₂).1).trans hsz, hA₂, hPp₂, hPm₂,
        fun w hw => ⟨_, hSg₂ w hw⟩, fun hl w hw => (hSg₂ w hw).trans (by rw [hT hl w hw]),
        hC₂.read (.head _), hC₂.read (.tail _ (.head _)), hT₂.read (.head _),
        hT₂.read (.tail _ (.head _)), hN.mono fun h =>
          ⟨h.1, h.2.2.2.1.of_modifies (hm₁.trans hm₂), h.2.2.2.2⟩⟩
  rintro st₃ hm₃ ⟨_, h₃, hp₃⟩
  refine ⟨?_, fun hg h2 => h₃ (fun w hw => (hSg₂ w hw).trans (by rw [hg w hw])) h2,
    hp₃.trans (hp₂.trans h₁.2.2.2.2.2)⟩
  refine ((hm₁.trans (hm₂.of_sub (fp' := [(b, 0, 7)]) (by simp))).trans hm₃).mono fun x hx => ?_
  rcases List.mem_append.mp hx with hx | hx
  · refine List.mem_append_right _ ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (h | h | h | h | h | h | h) | h <;> simp [h]
  · exact List.mem_append_left _ hx

/-- **The node step as a routine specification**: let the kernels of `I` be the routines `mmR`,
`qrR` on interleaved pairs, with exact comparisons, literals up to $k$ and conversion at `p`. From
a state of $b$ buffers holding the node's inputs (the matrix $\mathbf{A}$ at its block of `Ma`, the
window $R$, $\beta$, the uniform word $v$, the constants $o$, $z_2$, $h$, $m$ and the stored
$\sqrt{1/2}$ in the cells $0$ to $4$ of `c`, the Gaussian words $g$ in `Sg`; the arenas, `par`,
`Su`, `Sg`, `c` distinct and below $b$), the run of `NLAlib.eighNodeBlock` modifies only the
window of its branch at the split index $k_+ = \min(k, \lfloor\mathrm{fl}(t + h)\rfloor_+)$ ($t$
the rounded trace of the projector $\mathbf{P}_+$ of the sign $\mathbf{B}$) and keeps the tape
positions; if the Gaussian words are the tape's and $z_2$ is the machine's $2$, the window then
holds the outcome of `NLAlib.eighStep`'s branch. In mode `total` the run also succeeds, given the
standard model on the range `safe` holding everywhere, $u(p) < 1$, $z_2$ and $R$ decoding to
nonzero values, $\ell_0 + d \ge 1$, the window writable and every integer literal. No printed
source. -/
theorem spec_eighNodeBlock {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) (md : Mode) {u : P → ℝ} {dec : P → K → ℝ}
    {safe : P → ℝ → Prop} (p : P) (n ℓ₀ F d lo k : ℕ)
    (hsem : md.Needs (IsRelErrSem u dec safe I.sem ∧ (∀ p x, safe p x) ∧ u p < 1))
    (hflag : I.sem.DecidesFlags p)
    (hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y)))
    (hlit : IsExactIntLit dec I.sem k) (htn : IsExactToNat dec I.sem) (hk : lo + k ≤ n)
    (hk2 : 2 ≤ k) (H : EighArenas) {par Su Sg c b : ℕ}
    (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup)
    (hlt : ∀ x ∈ H.handles ++ [par, Su, Sg, c], x < b)
    (A Bm Ppm Pmm : Matrix (Fin k) (Fin k) (K × K)) (R β v o z₂ h m : K) (g : ℕ → K) (kp : ℕ)
    (hBm : Bm = newtonSchulzSign (eighTapeMachine I p mmR qrR) β
      ((eighTapeMachine I p mmR qrR).mul z₂ R) F ((eighTapeMachine I p mmR qrR).hermShift A
        ((eighTapeMachine I p mmR qrR).mul ((eighTapeMachine I p mmR qrR).div R
          ((eighTapeMachine I p mmR qrR).ofNat (ℓ₀ + d))) v)))
    (hPp : Ppm = (eighTapeMachine I p mmR qrR).hermScale
      ((eighTapeMachine I p mmR qrR).hermShift Bm m) z₂)
    (hPm : Pmm = (eighTapeMachine I p mmR qrR).hermScale ((eighTapeMachine I p mmR qrR).negMat
      ((eighTapeMachine I p mmR qrR).hermShift Bm o)) z₂)
    (hkp : kp = min k ⌊dec p ((eighTapeMachine I p mmR qrR).add
      ((eighTapeMachine I p mmR qrR).traceRe Ppm) h)⌋₊) :
    RoutineSpec md I (fun st => st.store.size = b ∧
        (pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A ∧
          st.store.read p H.Lv (2 * d) = some R ∧ st.store.read p par 2 = some β ∧
          st.store.read p Su lo = some v ∧ st.store.read p c 0 = some o ∧
          st.store.read p c 1 = some z₂ ∧ st.store.read p c 2 = some h ∧
          st.store.read p c 3 = some m ∧ st.store.read p c 4 = some (I.sem.sqrtHalf p) ∧
          ∀ w < 4 * (n * n), st.store.read p Sg w = some (g w)) ∧
        (md = .liberal → ∀ w < 4 * (n * n), g w = I.tape .gaussian (4 * (n * n) * d + w)) ∧
        md.Needs (dec p z₂ ≠ 0 ∧ dec p R ≠ 0 ∧ 1 ≤ ℓ₀ + d ∧
          WritableBlocks st.store p (eighBranchWindow H n d lo k kp) ∧
          ∀ q : ℕ, ∃ z, I.sem.lit p (q : ℚ) = some z))
      (eighNodeBlock p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) (.const lo) (.const k)
        par H.Lv Su Sg H.Ma H.Qa H.Sz H.Kd H.Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩)
      (eighBranchWindow H n d lo k kp)
      fun st st' => ((∀ w < 4 * (n * n), g w = I.tape .gaussian (4 * (n * n) * d + w)) →
        z₂ = (eighTapeMachine I p mmR qrR).ofNat 2 →
        EighBranchHolds I p mmR qrR H n d lo k kp A Ppm Pmm
          ((eighTapeMachine I p mmR qrR).div R z₂) st'.store) ∧ PosKept st st' := by
  have lH : ∀ x ∈ H.handles, x < b := fun x hx => hlt x (List.mem_append_left _ hx)
  have hl := hlt
  simp only [EighArenas.handles, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hl
  obtain ⟨lMa, -, -, -, -, -, -, lLv, lpar, lSu, lSg, lc⟩ := hl
  -- the inputs, below the scratch, as one bundle
  have hF := (readsOnly_pairLayoutHolds p H.Ma (2 * (n * n) * d + 2 * n * lo) A).and
    ((readsOnly_read p H.Lv (2 * d) (some R)).and ((readsOnly_read p par 2 (some β)).and
    ((readsOnly_read p Su lo (some v)).and ((readsOnly_read p c 0 (some o)).and
    ((readsOnly_read p c 1 (some z₂)).and ((readsOnly_read p c 2 (some h)).and
    ((readsOnly_read p c 3 (some m)).and ((readsOnly_read p c 4 (some (I.sem.sqrtHalf p))).and
    (readsOnly_forall_read p Sg (4 * (n * n)) fun w x => x = some (g w))))))))))
  refine spec_eighNodeBlock_of_body p mm qr _ _ _ _ _ _ par H.Lv Su Sg H.Ma H.Qa H.Sz H.Kd H.Kp
    _ _ _ _ _ (fun _ h => h.1) (fun st st' ⟨_, hin, hT, hN⟩ h7 hr hsh h8 h9 h10 _ =>
      ⟨h7, hF.of_read_eq_below (by fp_omega [lMa, lLv, lpar, lSu, lc, lSg]) hin hsh hr, h8, h9,
        h10, hT, hN.mono fun h => ⟨h.1, h.2.1, h.2.2.1, fun x hx =>
          (h.2.2.2.1 x hx).of_getElem?_shape_eq
            (hsh x.1 (lH _ (fst_mem_handles_of_mem_eighBranchWindow hx))), h.2.2.2.2⟩⟩)
    (spec_eighNodeBody hmm hqr md p n ℓ₀ F d lo k hsem hflag hcmp hlit htn hk hk2 H hbufs hlt A Bm
      Ppm Pmm R β v o z₂ h m g kp hBm hPp hPm hkp)
    fun st s s' _ hp hps _ s'' hr hpos => ⟨fun hg h2 => (hp.1 hg h2).of_read_eq lH hr,
      hpos.trans (hp.2.trans hps)⟩

omit [AddMonoid C] in
/-- The node step's outcome from its branch's: if `NLAlib.eighStep` is not a leaf
($k \ge 2$, window test false), the branch's outcome at the machine's split index in the store
`s` gives, in a store `s'` reading as `s` in the buffers below `N` (the arenas among them), the
outcome of `NLAlib.holds_of_exec_eighNodeBlock`. -/
theorem eighStep_holds_of_branch {n F d lo k ℓ₀ N : ℕ} (hk2 : 2 ≤ k) (H : EighArenas)
    {p : P} {R R₀ ε β : K} {A : Matrix (Fin k) (Fin k) (K × K)} {s s' : Store P K}
    (hlt : ∀ b ∈ H.handles, b < N)
    (hpop : ∀ {q : P} {b i : ℕ}, b < N → s'.read q b i = s.read q b i)
    (hRt : (eighTapeMachine I p mmR qrR).le R ((eighTapeMachine I p mmR qrR).mul ε R₀) = false)
    (hB : let M := eighTapeMachine I p mmR qrR
      let B' := newtonSchulzSign M β (M.mul (M.ofNat 2) R) F
        (M.hermShift A (M.unif (M.div R (M.ofNat (ℓ₀ + d))) (eighTapeSample n d lo).1))
      let Pp' := M.hermScale (M.hermShift B' (M.neg M.one)) (M.ofNat 2)
      let Pm' := M.hermScale (M.negMat (M.hermShift B' M.one)) (M.ofNat 2)
      EighBranchHolds I p mmR qrR H n d lo k
        (min k (M.toNat (M.add (M.traceRe Pp') (M.div M.one (M.ofNat 2))))) A Pp' Pm'
        (M.div R (M.ofNat 2)) s) :
    let M := eighTapeMachine I p mmR qrR
    match eighStep M n F R₀ β A R ε (ℓ₀ + d) (eighTapeSample n d lo) with
      | .leaf _ _ => False
      | .shift b A' _ =>
        pairLayout.Holds s' p H.Ma (2 * (n * n) * (d + 1) + 2 * n * lo) A' ∧
          s'.read p H.Sz (n * (d + 1) + lo) = I.sem.lit p ((k : ℕ) : ℚ) ∧
          s'.read p H.Kd (n * d + lo) = I.sem.lit p (((if b then 2 else 3 : ℕ)) : ℚ)
      | .split kp _ Qp Qm Ap Am _ =>
        pairLayout.Holds s' p H.Qa (2 * (n * n) * d + 2 * n * lo) Qp ∧
          pairLayout.Holds s' p H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (k * kp)) Qm ∧
          pairLayout.Holds s' p H.Ma (2 * (n * n) * (d + 1) + 2 * n * lo) Ap ∧
          pairLayout.Holds s' p H.Ma (2 * (n * n) * (d + 1) + 2 * n * (lo + kp)) Am ∧
          s'.read p H.Sz (n * (d + 1) + lo) = I.sem.lit p ((kp : ℕ) : ℚ) ∧
          s'.read p H.Sz (n * (d + 1) + (lo + kp)) = I.sem.lit p ((k - kp : ℕ) : ℚ) ∧
          s'.read p H.Kd (n * d + lo) = I.sem.lit p ((4 : ℕ) : ℚ) ∧
          s'.read p H.Kp (n * d + lo) = I.sem.lit p ((kp : ℕ) : ℚ) := by
  intro M
  obtain ⟨B1, B2, B3⟩ := hB
  have lQa := hlt H.Qa (by simp [EighArenas.handles])
  have lMa := hlt H.Ma (by simp [EighArenas.handles])
  have lSz := hlt H.Sz (by simp [EighArenas.handles])
  have lKd := hlt H.Kd (by simp [EighArenas.handles])
  have lKp := hlt H.Kp (by simp [EighArenas.handles])
  unfold eighStep
  dsimp only
  split_ifs with h0 hle h1 h2
  · omega
  · exact absurd hle (by rw [hRt]; decide)
  · obtain ⟨x1, x2, x3⟩ := B1 h1
    exact ⟨fun i j t => (hpop lMa).trans (x1 i j t), (hpop lSz).trans x2, (hpop lKd).trans x3⟩
  · obtain ⟨x1, x2, x3⟩ := B2 h2
    exact ⟨fun i j t => (hpop lMa).trans (x1 i j t), (hpop lSz).trans x2, (hpop lKd).trans x3⟩
  · obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8⟩ :=
      B3 (Nat.pos_of_ne_zero h2) (lt_of_le_of_ne (min_le_left _ _) h1)
    exact ⟨fun i j t => (hpop lQa).trans (x1 i j t), fun i j t => (hpop lQa).trans (x2 i j t),
      fun i j t => (hpop lMa).trans (x3 i j t), fun i j t => (hpop lMa).trans (x4 i j t),
      (hpop lSz).trans x5, (hpop lSz).trans x6, (hpop lKd).trans x7, (hpop lKp).trans x8⟩

omit [DecidableEq P] [AddMonoid C] in
/-- The window of a node step's branch lies in the window of `NLAlib.eighStep`'s outcome: if the
outcome is not a leaf ($k \ge 2$, window test false), a cell outside the basis block of depth
$d$, the matrix block and size cells of depth $d + 1$ and the kind and split cells of depth $d$
(the size cells as the outcome uses them) is outside `NLAlib.EighNodeWindow` at the machine's
split index. -/
private theorem not_eighNodeWindow_of_eighStep {n F d lo k ℓ₀ : ℕ} (hk2 : 2 ≤ k)
    {H : EighArenas} {p : P} {R R₀ ε β : K} {A : Matrix (Fin k) (Fin k) (K × K)} {b i : ℕ}
    (hRt : (eighTapeMachine I p mmR qrR).le R ((eighTapeMachine I p mmR qrR).mul ε R₀) = false) :
    let M := eighTapeMachine I p mmR qrR
    let B' := newtonSchulzSign M β (M.mul (M.ofNat 2) R) F
      (M.hermShift A (M.unif (M.div R (M.ofNat (ℓ₀ + d))) (eighTapeSample n d lo).1))
    let Pp' := M.hermScale (M.hermShift B' (M.neg M.one)) (M.ofNat 2)
    let kp := min k (M.toNat (M.add (M.traceRe Pp') (M.div M.one (M.ofNat 2))))
    ¬ ((b = H.Qa ∧ 2 * (n * n) * d + 2 * n * lo ≤ i ∧
          i < 2 * (n * n) * d + 2 * n * (lo + k)) ∨
        (b = H.Ma ∧ 2 * (n * n) * (d + 1) + 2 * n * lo ≤ i ∧
          i < 2 * (n * n) * (d + 1) + 2 * n * (lo + k)) ∨
        (b = H.Sz ∧ n * (d + 1) + lo ≤ i ∧ i < n * (d + 1) + lo + k ∧
          (i = n * (d + 1) + lo ∨
            match eighStep M n F R₀ β A R ε (ℓ₀ + d) (eighTapeSample n d lo) with
            | .split kp _ _ _ _ _ _ => i = n * (d + 1) + (lo + kp)
            | _ => False)) ∨
        ((b = H.Kd ∨ b = H.Kp) ∧ i = n * d + lo)) →
      ¬ EighNodeWindow H n d lo k (if 0 < kp ∧ kp < k then lo + kp else lo) b i := by
  intro M B' Pp' kp hW hN
  apply hW
  unfold EighNodeWindow at hN
  rcases hN with h1 | h1 | ⟨hbS, hi⟩ | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · refine Or.inr (Or.inr (Or.inl ⟨hbS, ?_⟩))
    split_ifs at hi with hc
    · rcases hi with rfl | rfl
      · exact ⟨by omega, by omega, Or.inl rfl⟩
      · refine ⟨by omega, by omega, Or.inr ?_⟩
        unfold eighStep
        dsimp only
        split_ifs with h0 hle h1 h2
        · omega
        · exact absurd hle (by rw [hRt]; decide)
        · exact absurd h1 (Nat.ne_of_lt hc.2)
        · exact absurd h2 (Nat.pos_iff_ne_zero.mp hc.1)
        · rfl
    · rcases hi with rfl | rfl <;> exact ⟨by omega, by omega, Or.inl rfl⟩
  · exact Or.inr (Or.inr (Or.inr h1))

omit [AddMonoid C] [Inhabited K] in
/-- The buffers a node step reads exist: the handles of arenas shaped for $n$ and $D$ in the
store `s`, and the buffers `par`, `Su`, `Sg`, `c` of cells read in `s`, are below its size. -/
theorem EighArenas.Shaped.forall_lt_size {n D : ℕ} {H : EighArenas} {p : P} {par Su Sg c : ℕ}
    {s : Store P K} {w₁ w₂ w₃ w₄ : K} (hH : H.Shaped s p n D) (hSg : s.read p Sg 0 = some w₁)
    (hpar : s.read p par 2 = some w₂) (hSu : ∃ lo, s.read p Su lo = some w₃)
    (hc : s.read p c 0 = some w₄) : ∀ b ∈ H.handles ++ [par, Su, Sg, c], b < s.size := by
  have hsz : ∀ {b : ℕ} {x : P × ℕ}, s.shape[b]? = some x → b < s.size :=
    fun h => by simpa [Store.size_shape] using (Array.getElem?_eq_some_iff.mp h).1
  obtain ⟨-, hMa, hUa, hQa, hEa, hSz, hKd, hKp, hLv⟩ := id hH
  obtain ⟨lo, hSu⟩ := hSu
  simp only [EighArenas.handles, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false]
  rintro b (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  exacts [hsz hMa, hsz hUa, hsz hQa, hsz hEa, hsz hSz, hsz hKd, hsz hKp, hsz hLv,
    Store.lt_size_of_read_eq_some hpar, Store.lt_size_of_read_eq_some hSu,
    Store.lt_size_of_read_eq_some hSg, Store.lt_size_of_read_eq_some hc]

/-- The node step computes `NLAlib.eighStep`, with the window it writes: let the kernels of `I`
be the routines `mmR`, `qrR` on interleaved pairs and the semantics decide flags at `p`, with exact
comparisons, literals up to $n + 2$ and conversion; let $M$ be the machine of the interpretation
(`NLAlib.eighTapeMachine`). A successful run of `NLAlib.eighNodeBlock` at the slot $lo$ of depth
$d$ (arenas shaped for $n$ and a depth $D$) for a node of size $k \ge 2$, $lo + k \le n$, whose
matrix $\mathbf{A}$ is held at its block of `Ma`, whose window $R$ is in the cell $2d$ of `Lv` (with
$R \le \mathrm{fl}(\varepsilon R_0)$ false), whose seed is the cell $lo$ of `Su`, with the
level's Gaussian words in `Sg`, the stored $\beta$ in cell $2$ of `par` and the constants (the
machine's one, $\mathrm{fl}(2)$, $\mathrm{fl}(1/2)$, $-1$ and the stored $\sqrt{1/2}$) in cells
$0$ to $4$ of `c` (the arenas, `par`, `Su`, `Sg`, `c` distinct), ends with the outcome of
`NLAlib.eighStep` at the node's samples (depth counter $\ell_0 + d$), which is not a leaf: for one
child on side $b$, the shifted matrix at the same slot of depth $d + 1$, the size $k$ there and
the kind $2$ ($b$ true) or $3$; for a split into $k_+$, everything
`NLAlib.holds_of_exec_eighSplitBlock` writes. Every cell outside the node's basis block at depth
$d$, its matrix block and size cells at depth $d + 1$, and its kind and split cells at depth $d$
(the window of the slots $[lo, lo + k)$) is unchanged, the store shape and the tape positions too.
No printed source. -/
theorem holds_of_exec_eighNodeBlock_frame {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) (p : P) (hflag : I.sem.DecidesFlags p)
    {dec : P → K → ℝ} (hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y)))
    (n ℓ₀ F d lo k : ℕ) (hlit : IsExactIntLit dec I.sem (n + 2)) (htn : IsExactToNat dec I.sem)
    (hk : lo + k ≤ n) (hk2 : 2 ≤ k) (H : EighArenas)
    {par Su Sg c : ℕ} {st st' : St P K C} {A : Matrix (Fin k) (Fin k) (K × K)} {R R₀ ε β : K}
    {D : ℕ} (hH : H.Shaped st.store p n D)
    (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup)
    (hA : pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hR : st.store.read p H.Lv (2 * d) = some R)
    (hRtest : (eighTapeMachine I p mmR qrR).le R ((eighTapeMachine I p mmR qrR).mul ε R₀) = false)
    (hpar : st.store.read p par 2 = some β)
    (hSu : st.store.read p Su lo = some (I.tape .uniform (n * d + lo)))
    (hSg : ∀ w < 4 * (n * n), st.store.read p Sg w = some (I.tape .gaussian (4 * (n * n) * d + w)))
    (hc : st.store.read p c 0 = I.sem.lit p 1 ∧ st.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
      st.store.read p c 2 = some ((eighTapeMachine I p mmR qrR).div
        (eighTapeMachine I p mmR qrR).one ((eighTapeMachine I p mmR qrR).ofNat 2)) ∧
      st.store.read p c 3 = some ((eighTapeMachine I p mmR qrR).neg
        (eighTapeMachine I p mmR qrR).one) ∧
      st.store.read p c 4 = some (I.sem.sqrtHalf p))
    (h : exec I (eighNodeBlock p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) (.const lo)
      (.const k) par H.Lv Su Sg H.Ma H.Qa H.Sz H.Kd H.Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩
        ⟨c, 4⟩).run st = some st') :
    let M := eighTapeMachine I p mmR qrR
    (match eighStep M n F R₀ β A R ε (ℓ₀ + d) (eighTapeSample n d lo) with
      | .leaf _ _ => False
      | .shift b A' _ =>
        pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * lo) A' ∧
          st'.store.read p H.Sz (n * (d + 1) + lo) = I.sem.lit p ((k : ℕ) : ℚ) ∧
          st'.store.read p H.Kd (n * d + lo) = I.sem.lit p (((if b then 2 else 3 : ℕ)) : ℚ)
      | .split kp _ Qp Qm Ap Am _ =>
        pairLayout.Holds st'.store p H.Qa (2 * (n * n) * d + 2 * n * lo) Qp ∧
          pairLayout.Holds st'.store p H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (k * kp)) Qm ∧
          pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * lo) Ap ∧
          pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * (lo + kp)) Am ∧
          st'.store.read p H.Sz (n * (d + 1) + lo) = I.sem.lit p ((kp : ℕ) : ℚ) ∧
          st'.store.read p H.Sz (n * (d + 1) + (lo + kp)) = I.sem.lit p ((k - kp : ℕ) : ℚ) ∧
          st'.store.read p H.Kd (n * d + lo) = I.sem.lit p ((4 : ℕ) : ℚ) ∧
          st'.store.read p H.Kp (n * d + lo) = I.sem.lit p ((kp : ℕ) : ℚ)) ∧
      (∀ q b i, ¬ ((b = H.Qa ∧ 2 * (n * n) * d + 2 * n * lo ≤ i ∧
            i < 2 * (n * n) * d + 2 * n * (lo + k)) ∨
          (b = H.Ma ∧ 2 * (n * n) * (d + 1) + 2 * n * lo ≤ i ∧
            i < 2 * (n * n) * (d + 1) + 2 * n * (lo + k)) ∨
          (b = H.Sz ∧ n * (d + 1) + lo ≤ i ∧ i < n * (d + 1) + lo + k ∧
            (i = n * (d + 1) + lo ∨
              match eighStep M n F R₀ β A R ε (ℓ₀ + d) (eighTapeSample n d lo) with
              | .split kp _ _ _ _ _ _ => i = n * (d + 1) + (lo + kp)
              | _ => False)) ∨
          ((b = H.Kd ∨ b = H.Kp) ∧ i = n * d + lo)) →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  intro M
  obtain ⟨-, o, -, hl1, -, -⟩ := id hflag
  obtain ⟨z₂, hz₂, -⟩ := hlit p 2 (by omega)
  have hM1 : some (eighTapeMachine I p mmR qrR).one = some o := by
    change some ((I.sem.lit p 1).getD default) = _; rw [hl1, Option.getD_some]
  have hM2 : some ((eighTapeMachine I p mmR qrR).ofNat 2) = some z₂ := by
    change some ((I.sem.lit p ((2 : ℕ) : ℚ)).getD default) = _; rw [hz₂, Option.getD_some]
  have hlt := hH.forall_lt_size (hSg 0 (by have : 0 < n := (by omega); positivity)) hpar
    ⟨lo, hSu⟩ (hc.1.trans hl1)
  obtain ⟨hm, hv, hp⟩ := (spec_eighNodeBlock (u := fun _ => 0) (safe := fun _ _ => True) hmm hqr
    .liberal p n ℓ₀ F d lo k trivial hflag hcmp (fun q m hm => hlit q m (by omega)) htn hk hk2 H
    hbufs hlt A _ _ _ R β _ _ _ _ _ _ _ rfl rfl rfl rfl).spec.holds_of_exec
    ⟨rfl, ⟨hA, hR, hpar, hSu, hc.1.trans (hl1.trans hM1.symm), hc.2.1.trans (hz₂.trans hM2.symm),
      hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2, hSg⟩, fun _ _ _ => rfl, trivial⟩ h
  have hM : ∀ w, (eighTapeMachine I p mmR qrR).toNat w = ⌊dec p w⌋₊ := fun w => by
    change (I.sem.toNat p w).getD 0 = _
    rw [htn p w]
    split_ifs with h0
    · rfl
    · exact (Nat.floor_eq_zero.mpr (by linarith [not_le.mp h0])).symm
  have hB := hv (fun _ _ => rfl) rfl
  rw [← hM] at hm hB
  refine ⟨eighStep_holds_of_branch hk2 H (fun x hx => hlt x (List.mem_append_left _ hx))
    (fun _ => rfl) hRtest hB, fun q b i hW => hm.2 q b i ?_, hm.1, hp⟩
  have hN := not_eighNodeWindow_of_eighStep hk2 hRtest hW
  unfold eighBranchWindow
  split_ifs at hN ⊢ with h1 h2 h2
  exacts [blockDisjoint_eighSplitWindow hk h2.2 hN, absurd h1 h2, absurd h2 h1,
    blockDisjoint_eighChildWindow hk hN]

/-- The node step computes `NLAlib.eighStep`: let the kernels of `I` be the routines `mmR`,
`qrR` on interleaved pairs and the semantics decide flags at `p`; let $M$ be the machine of the
interpretation (`NLAlib.eighTapeMachine`). A successful run of `NLAlib.eighNodeBlock` at the slot
$lo$ of depth $d$ for a node of size $k \ge 2$, $lo + k \le n$, whose matrix $\mathbf{A}$ is held at
its block of `Ma`, whose window $R$ is in the cell $2d$ of `Lv`, whose seed is the cell $lo$ of `Su`
(the tape at uniform position $nd + lo$), with the level's Gaussian words in `Sg`, the stored
$\beta$ in cell $2$ of `par` and the constants (the machine's one, $\mathrm{fl}(2)$,
$\mathrm{fl}(1/2)$, $-1$ and the stored $\sqrt{1/2}$, `NLAlib.Computation.ScalarSem.sqrtHalf`) in
cells $0$ to $4$ of `c`, ends with the outcome of `NLAlib.eighStep` at the
node's samples (`NLAlib.eighTapeSample`, depth counter $\ell_0 + d$), when it is not a leaf: for one
child on side $b$, the shifted matrix at the same slot of depth $d + 1$, the size $k$ there, and the
kind $2$ ($b$ true) or $3$; for a split into $k_+$, everything `NLAlib.holds_of_exec_eighSplitBlock`
writes. Every cell outside depths $d$ and $d + 1$ of the arenas (and outside `Su`, `Sg`, `c`, `par`,
which are only read) is unchanged, the store shape and the tape positions too. No printed source. -/
theorem holds_of_exec_eighNodeBlock {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) (p : P) (hflag : I.sem.DecidesFlags p)
    {dec : P → K → ℝ} (hcmp : ∀ x y : K, I.sem.cmp p .le x y = some (decide (dec p x ≤ dec p y)))
    (n ℓ₀ F d lo k : ℕ) (hlit : IsExactIntLit dec I.sem (n + 2)) (htn : IsExactToNat dec I.sem)
    (hk : lo + k ≤ n) (hk2 : 2 ≤ k) (H : EighArenas)
    {par Su Sg c : ℕ} {st st' : St P K C} {A : Matrix (Fin k) (Fin k) (K × K)} {R R₀ ε β : K}
    {D : ℕ} (hH : H.Shaped st.store p n D)
    (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup)
    (hA : pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hR : st.store.read p H.Lv (2 * d) = some R)
    (hRtest : (eighTapeMachine I p mmR qrR).le R ((eighTapeMachine I p mmR qrR).mul ε R₀) = false)
    (hpar : st.store.read p par 2 = some β)
    (hSu : st.store.read p Su lo = some (I.tape .uniform (n * d + lo)))
    (hSg : ∀ w < 4 * (n * n), st.store.read p Sg w = some (I.tape .gaussian (4 * (n * n) * d + w)))
    (hc : st.store.read p c 0 = I.sem.lit p 1 ∧ st.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
      st.store.read p c 2 = some ((eighTapeMachine I p mmR qrR).div
        (eighTapeMachine I p mmR qrR).one ((eighTapeMachine I p mmR qrR).ofNat 2)) ∧
      st.store.read p c 3 = some ((eighTapeMachine I p mmR qrR).neg
        (eighTapeMachine I p mmR qrR).one) ∧
      st.store.read p c 4 = some (I.sem.sqrtHalf p))
    (h : exec I (eighNodeBlock p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) (.const lo)
      (.const k) par H.Lv Su Sg H.Ma H.Qa H.Sz H.Kd H.Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩
        ⟨c, 4⟩).run st = some st') :
    let M := eighTapeMachine I p mmR qrR
    (match eighStep M n F R₀ β A R ε (ℓ₀ + d) (eighTapeSample n d lo) with
      | .leaf _ _ => False
      | .shift b A' _ =>
        pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * lo) A' ∧
          st'.store.read p H.Sz (n * (d + 1) + lo) = I.sem.lit p ((k : ℕ) : ℚ) ∧
          st'.store.read p H.Kd (n * d + lo) = I.sem.lit p (((if b then 2 else 3 : ℕ)) : ℚ)
      | .split kp _ Qp Qm Ap Am _ =>
        pairLayout.Holds st'.store p H.Qa (2 * (n * n) * d + 2 * n * lo) Qp ∧
          pairLayout.Holds st'.store p H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (k * kp)) Qm ∧
          pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * lo) Ap ∧
          pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * (lo + kp)) Am ∧
          st'.store.read p H.Sz (n * (d + 1) + lo) = I.sem.lit p ((kp : ℕ) : ℚ) ∧
          st'.store.read p H.Sz (n * (d + 1) + (lo + kp)) = I.sem.lit p ((k - kp : ℕ) : ℚ) ∧
          st'.store.read p H.Kd (n * d + lo) = I.sem.lit p ((4 : ℕ) : ℚ) ∧
          st'.store.read p H.Kp (n * d + lo) = I.sem.lit p ((kp : ℕ) : ℚ)) ∧
      (∀ q b i, ¬ H.LevelCell n d b i → ¬ H.LevelCell n (d + 1) b i →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  obtain ⟨hstep, hfr, hsh, hps⟩ := holds_of_exec_eighNodeBlock_frame hmm hqr p hflag hcmp n ℓ₀ F
    d lo k hlit htn hk hk2 H hH hbufs hA hR hRtest hpar hSu hSg hc h
  refine ⟨hstep, fun q b i h1 h2 => hfr q b i fun hW => ?_, hsh, hps⟩
  have hlok : n * (lo + k) ≤ n * n := Nat.mul_le_mul_left _ hk
  rcases hW with ⟨rfl, hi1, hi2⟩ | ⟨rfl, hi1, hi2⟩ | ⟨rfl, hi1, hi2, -⟩ | ⟨hb, rfl⟩
  · exact h1 (Or.inl ⟨Or.inr (Or.inr rfl), by linarith [Nat.zero_le (n * lo)],
      by linarith⟩)
  · exact h2 (Or.inl ⟨Or.inl rfl, by linarith [Nat.zero_le (n * lo)], by linarith⟩)
  · exact h2 (Or.inr (Or.inl ⟨Or.inr (Or.inl rfl), by linarith, by
      rw [Nat.mul_succ]; omega⟩))
  · exact h1 (Or.inr (Or.inl ⟨by rcases hb with rfl | rfl <;> simp, by omega, by
      rw [Nat.mul_succ]; omega⟩))

end NLAlib
