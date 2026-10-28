/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlibScaffold.Krylov.Processes.LanczosStep

/-!
# The run of the Lanczos program in the standard model

A run of `NLAlib.lanczosBasisProgWith` under `NLAlib.Computation.IsRelErrSem`, for any product
`mv` that meets `NLAlib.LanczosMvSpec`, succeeds, and its outputs are the coefficients and
vectors of a computed Lanczos recurrence whose every step has the local errors of the kernels
(`NLAlib.LanczosRunFacts`). The loop invariant (`NLAlib.LanczosLoopInv`) is over the three
rotating slots. This is the program half of the bridge of
`NLAlibScaffold/Krylov/Processes/LanczosRounding.lean`; the assembly of a `NLAlib.LanczosRun`
is there. Design: `docs/design/Krylov-LanczosRounding.md` (§2).

## Main definitions

* `NLAlib.LanczosLoopInv`: the loop invariant.
* `NLAlib.LanczosRunFacts`: the facts of a run on its outputs.

## Main results

* `NLAlib.exec_lanczosInit`: the start.
* `NLAlib.Computation.IsRelErrSem.exists_lanczosRunFacts_of_lanczosBasisProgWith`: the run.
-/

@[expose] public section

open Finset
open scoped Matrix

namespace NLAlib

open Computation Builder

section Pieces

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] (I : Interp P ι K C) {p : P}
  {u : P → ℝ} {dec : P → K → ℝ}

/-- **A loop writing one cell per index**: if body $i$, from any state in the frame of the
first $i$ cells of the block at `off`, succeeds and only writes cell $\mathit{off} + i$ with a
word decoding to $f_i$, the loop of $n$ bodies writes the block of $n$ cells with
$f_0, \dots, f_{n-1}$ and nothing else. -/
theorem exec_loop_write (st : St P K C) {Y off n : ℕ} (f : ℕ → ℝ)
    {body : ℕ → Stmt P ι ℕ ℕ}
    (hstep : ∀ i < n, ∀ st' : St P K C, StoreFrame p st.store st'.store (StoreBlock Y off i) →
      ∃ (st'' : St P K C) (w : K), exec I (body i) st' = some st'' ∧
        st'.store.write p Y (off + i) w = some st''.store ∧ dec p w = f i) :
    ∃ st' : St P K C, exec I (.loop (.const n) body) st = some st' ∧
      StoreFrame p st.store st'.store (StoreBlock Y off n) ∧
      ∀ i < n, DecCell st'.store p dec Y (off + i) (f i) := by
  obtain ⟨st', h', hR⟩ := exists_exec_loop_eq_some_of_forall I (n := .const n) (body := body)
    (fun i st' => StoreFrame p st.store st'.store (StoreBlock Y off i) ∧
      ∀ k < i, DecCell st'.store p dec Y (off + k) (f k))
    ⟨StoreFrame.refl _ _,
      fun k hk => absurd hk (Nat.not_lt_zero _)⟩
    fun i hi st' ⟨hf, hc⟩ => by
      obtain ⟨st'', w, he, hw, hd⟩ := hstep i hi st' hf
      have hfw := storeFrame_of_write hw
      refine ⟨st'', he, (hf.trans hfw).mono fun b j hb => ?_, fun k hk => ?_⟩
      · rcases hb with ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩
        · exact ⟨rfl, h1, by omega⟩
        · exact ⟨rfl, by omega, by omega⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
        · exact (hc k hk).frame hfw fun hb => by obtain ⟨-, h1, h2⟩ := hb; omega
        · exact ⟨w, Store.read_of_write_eq_some hw, hd⟩
  exact ⟨st', h', hR⟩

/-- **`copy` of a decoded vector** into a writable block that does not overlap it. -/
theorem exec_copyv_decVec (st : St P K C) {S : Array (P × ℕ)} (hsh : st.store.shape = S)
    (X : ℕ) (xo : IExp ℕ) (Y : ℕ) (yo : IExp ℕ) {N nY : ℕ} {v : Fin N → ℝ}
    (hx : DecVec st.store p dec X xo.eval v) (hSY : S[Y]? = some (p, nY))
    (hY : yo.eval + N ≤ nY) (hXY : X = Y → xo.eval + N ≤ yo.eval ∨ yo.eval + N ≤ xo.eval) :
    ∃ st' : St P K C, exec I (copyv p X xo Y yo (.const N)).run st = some st' ∧
      StoreFrame p st.store st'.store (StoreBlock Y yo.eval N) ∧
      DecVec st'.store p dec Y yo.eval v := by
  have hrun : (copyv (ι := ι) p X xo Y yo (.const N)).run = .seq (.named "copy"
      [.buf X, .idx xo, .buf Y, .idx yo, .idx (.const N)]
      (.seq (.loop (.const N) fun i =>
        .seq (.instr (.copy p ⟨Y, yo + .var i⟩ ⟨X, xo + .var i⟩)) .skip) .skip)) .skip := rfl
  rw [hrun, exec_seq_skip, exec_named, exec_seq_skip]
  obtain ⟨st', h', hf, hc⟩ := exec_loop_write I st (Y := Y) (off := yo.eval) (finExt v)
      fun i hi st' hf => by
    obtain ⟨w, hw, hd⟩ := hx.nat i hi
    have hw' : st'.store.read p X (xo.eval + i) = some w := by
      rw [hf.2 _ _ fun hb => ?_, hw]
      obtain ⟨rfl, h1, h2⟩ := hb
      rcases hXY rfl with h | h <;> omega
    obtain ⟨s', hs'⟩ := exists_write_of_shape (hf.1.trans hsh) hSY (by omega : yo.eval + i < nY) w
    exact ⟨_, w, (exec_seq_instr_copy I (dst := ⟨Y, yo + .var i⟩) (src := ⟨X, xo + .var i⟩)
      hw' hs').trans (exec_skip I _), hs', hd⟩
  refine ⟨st', h', hf, fun i => ?_⟩
  obtain ⟨w, hw, hd⟩ := hc i i.2
  exact ⟨w, hw, by rw [hd, finExt_fin]⟩

theorem StoreFrame.trans_same {p : P} {s s' s'' : Store P K} {A : ℕ → ℕ → Prop}
    (h : StoreFrame p s s' A) (h' : StoreFrame p s' s'' A) : StoreFrame p s s'' A :=
  (h.trans h').mono fun _ _ hb => hb.elim id id

/-- The first part of the start: `s[3] ← 0`, slot 2 ← $\mathbf{0}$, slot 0 ← $\mathbf{b}$. -/
theorem exec_lanczosInit_fill (h : IsRelErrSem u dec (fun _ _ => True) I.sem) {N : ℕ}
    (st : St P K C) {S : Array (P × ℕ)} (hsh : st.store.shape = S) {B W sb : ℕ}
    {bv : Fin N → ℝ} (hb : DecVec st.store p dec B 0 bv) (hBW : B ≠ W) (hBs : B ≠ sb)
    (hWs : W ≠ sb) (hSW : S[W]? = some (p, 3 * N)) (hS : S[sb]? = some (p, 4)) :
    ∃ st' : St P K C, (∀ f, exec I (ins (.lit p ⟨sb, 3⟩ 0) >>=
        fun _ => forRange (.const N) (fun i => ins (.lit p ⟨W, 2 * IExp.const N + IExp.var i⟩ 0))
        >>= fun _ => copyv p B 0 W 0 (.const N) >>= f).run st = exec I (f ()).run st') ∧
      StoreFrame p st.store st'.store (fun b i => StoreBlock W 0 (3 * N) b i ∨
        StoreBlock sb 0 4 b i) ∧
      DecVec st'.store p dec W 0 bv ∧ DecVec st'.store p dec W (N * 2) (0 : Fin N → ℝ) ∧
      DecCell st'.store p dec sb 3 0 := by
  obtain ⟨z0, hz0⟩ := h.lit_ok p 0 trivial
  have hdz0 : dec p z0 = 0 := by
    obtain ⟨δ, -, hδ⟩ := h.lit_err p 0 z0 hz0
    simpa using hδ
  obtain ⟨s₁, hs₁⟩ := exists_write_of_shape hsh hS (by norm_num : 3 < 4) z0
  obtain ⟨st₁, h₁, hst₁⟩ := exec_ins_lit I (st := st) (dst := ⟨sb, 3⟩) hz0 hs₁
  have hf₁ := storeFrame_of_write hs₁
  rw [← hst₁] at hf₁
  obtain ⟨st₂, h₂, hf₂, hc₂⟩ := exec_loop_write I st₁ (p := p) (dec := dec) (Y := W)
    (off := 2 * N) (n := N) (fun _ => 0)
    (body := fun i => (ins (.lit p ⟨W, 2 * IExp.const N + IExp.var i⟩ 0)).run)
    fun i hi st' hf => by
      obtain ⟨s', hs'⟩ := exists_write_of_shape ((hf.1.trans hf₁.1).trans hsh) hSW
        (by omega : 2 * N + i < 3 * N) z0
      have hs'' : st'.store.write p W (IExp.eval (2 * IExp.const N + IExp.var i)) z0 = some s' :=
        hs'
      exact ⟨_, z0, (exec_seq_instr_lit I (dst := ⟨W, 2 * IExp.const N + IExp.var i⟩)
        (t := .skip) (st := st') hz0 hs'').trans (exec_skip I _), hs', hdz0⟩
  have hf₁₂ := hf₁.trans hf₂
  obtain ⟨st₃, h₃, hf₃, hv₃⟩ := exec_copyv_decVec I st₂ (hf₁₂.1.trans hsh) B 0 W 0
    (hb.frame hf₁₂ fun i _ hb' => hb'.elim (fun h' => hBs h'.1) fun h' => hBW h'.1) hSW
    (by simp; omega) fun h' => absurd h' hBW
  refine ⟨st₃, fun f => ?_, (hf₁₂.trans hf₃).mono fun b i hb' => ?_, hv₃, fun i => ?_,
    hdz0 ▸ (DecCell.of_write (dec := dec) hs₁).frame ((hst₁ ▸ hf₂).trans hf₃) fun hb' => ?_⟩
  · rw [exec_bind_of_exec_eq_some I (seqShape_ins _) h₁,
      exec_bind_of_exec_eq_some I (seqShape_forRange _ _) ((exec_seq_skip I _ _).trans h₂),
      exec_bind_of_exec_eq_some I (seqShape_copyv _ _ _ _ _ _) h₃]
  · rcases hb' with (⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩) | ⟨rfl, h1, h2⟩
    · exact Or.inr ⟨rfl, by omega, by omega⟩
    · exact Or.inl ⟨rfl, by omega, by omega⟩
    · exact Or.inl ⟨rfl, by omega, by simp at h2; omega⟩
  · obtain ⟨w, hw, hd⟩ := hc₂ i i.2
    refine ⟨w, ?_, by rw [hd]; rfl⟩
    rw [hf₃.2 _ _ fun hb' => by obtain ⟨-, -, h2⟩ := hb'; simp at h2; omega, Nat.mul_comm]
    exact hw
  · rcases hb' with ⟨h', -⟩ | ⟨h', -⟩ <;> exact hWs h'.symm

/-- **The start of the Lanczos program** (`NLAlib.lanczosInit`) in the standard model: from
$\mathbf{b} \ne \mathbf{0}$ in buffer `B`, it writes only `W` and `s`, and leaves the computed
normalisation $\mathbf{v}_1$ of $\mathbf{b}$ in slot 0 ($c\mathbf{v}_1 = \mathbf{b} +
\boldsymbol\delta_0$, $c > 0$, $\|\boldsymbol\delta_0\| \le u\|\mathbf{b}\|$, nearly
unit), $\mathbf{0}$ in slot 2, and $0$ in `s[1]` and `s[3]`. -/
theorem exec_lanczosInit (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem) {N : ℕ} (hN : ((N + 4 : ℕ) : ℝ) * u p < 1) (st : St P K C)
    {S : Array (P × ℕ)} (hsh : st.store.shape = S) {B W sb : ℕ} {bv : Fin N → ℝ}
    (hb : DecVec st.store p dec B 0 bv) (hb0 : bv ≠ 0) (hBW : B ≠ W) (hBs : B ≠ sb)
    (hWs : W ≠ sb) (hSW : S[W]? = some (p, 3 * N)) (hS : S[sb]? = some (p, 4)) :
    ∃ (st' : St P K C) (v : Fin N → ℝ),
      (∀ f, exec I (lanczosInit p (.const N) B W sb >>= f).run st = exec I (f ()).run st') ∧
      StoreFrame p st.store st'.store (fun b i => StoreBlock W 0 (3 * N) b i ∨
        StoreBlock sb 0 4 b i) ∧
      DecVec st'.store p dec W 0 v ∧ DecVec st'.store p dec W (N * 2) (0 : Fin N → ℝ) ∧
      DecCell st'.store p dec sb 1 0 ∧ DecCell st'.store p dec sb 3 0 ∧
      (∃ (c : ℝ) (δ₀ : Fin N → ℝ), 0 < c ∧ c • v = bv + δ₀ ∧
        ‖WithLp.toLp 2 δ₀‖ ≤ u p * ‖WithLp.toLp 2 bv‖) ∧
      |‖WithLp.toLp 2 v‖ ^ 2 - 1| ≤ roundingFactor (N + 4) (u p) := by
  have hu0 : 0 ≤ u p := h.nonneg trivial
  have hu1 : u p < 1 := by simpa using cast_mul_lt_one_of_le (m := 1) hu0 (by omega) hN
  have hT : ∀ b i, (StoreBlock W 0 (3 * N) b i ∨ StoreBlock sb 0 4 b i) → b ≠ B :=
    fun b i hb' => by rcases hb' with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> [exact hBW.symm; exact hBs.symm]
  obtain ⟨st₁, h₁, hf₁, hv₁, h0₁, h3₁⟩ := exec_lanczosInit_fill I h st hsh hb hBW hBs hWs hSW hS
  obtain ⟨st₂, η, σ, β, h₂, hf₂, hβ₂, hη, hσ, hβ⟩ := exec_dot_sqrt I h hz hu1 st₁
    (hf₁.1.trans hsh) 0 2 hBs hS ⟨by norm_num, le_rfl⟩
    (hb.frame hf₁ fun i _ hb' => hT _ _ hb' rfl)
  have hsb : ∀ i, ¬ StoreBlock sb 1 2 W i := fun i hb' => hWs hb'.1
  obtain ⟨st₃, v, h₃, hf₃, hv₃, hv0, hv⟩ := exec_ifThenElse_rscl I h st₂ 2 0 hWs hβ₂
    (h3₁.frame hf₂ fun hb' => by obtain ⟨-, -, h'⟩ := hb'; omega)
    (hv₁.frame hf₂ fun i _ => hsb _)
  obtain ⟨hβ0, -, -, hunit, hδ, hpos⟩ := facts_of_relErr_normalize hu0 hN hη rfl hσ hβ hv0 hv
  obtain ⟨z0, hz0⟩ := h.lit_ok p 0 trivial
  obtain ⟨s₄, hs₄⟩ := exists_write_of_shape ((hf₃.1.trans hf₂.1).trans (hf₁.1.trans hsh)) hS
    (by norm_num : 1 < 4) z0
  obtain ⟨st₄, h₄, hst₄⟩ := exec_ins_lit I (st := st₃) (dst := ⟨sb, 1⟩) hz0 hs₄
  have hf₄ := storeFrame_of_write hs₄
  rw [← hst₄] at hf₄
  have hβpos := hpos hb0
  have h1₄ : DecCell st₄.store p dec sb 1 0 := by
    obtain ⟨δ, -, hδ⟩ := h.lit_err p 0 z0 hz0
    refine ⟨z0, by rw [hst₄]; exact Store.read_of_write_eq_some hs₄, by simpa using hδ⟩
  have hW4 : ∀ i, ¬ StoreBlock sb 1 1 W i := fun i hb' => hWs hb'.1
  refine ⟨st₄, v, fun f => ?_, ?_, hv₃.frame hf₄ fun i _ => hW4 _,
    ((h0₁.frame hf₂ fun i _ => hsb _).frame hf₃ fun i _ hb' => by
      obtain ⟨-, -, h'⟩ := hb'; simp at h'; omega).frame hf₄ fun i _ => hW4 _,
    h1₄, h3₁.frame hf₂ (fun hb' => by obtain ⟨-, -, h'⟩ := hb'; omega) |>.frame hf₃
      (fun hb' => hWs hb'.1.symm) |>.frame hf₄ fun hb' => by obtain ⟨-, -, h'⟩ := hb'; omega,
    ⟨β, β • v - bv, hβpos, by abel, hδ⟩, hunit hβpos.ne'⟩
  · unfold lanczosInit
    simp only [bind_assoc]
    rw [h₁ _, h₂ _, exec_bind_of_exec_eq_some I (seqShape_ifThenElse _ _ _ _ _ _) h₃,
      exec_bind_of_exec_eq_some I (seqShape_ins _) h₄]
  · refine ((hf₁.trans_same (hf₂.mono fun b i hb' => ?_)).trans_same
      (hf₃.mono fun b i hb' => ?_)).trans_same (hf₄.mono fun b i hb' => ?_)
    · obtain ⟨rfl, h1, h2⟩ := hb'; exact Or.inr ⟨rfl, by omega, by omega⟩
    · obtain ⟨rfl, h1, h2⟩ := hb'; exact Or.inl ⟨rfl, by omega, by simp at h2; omega⟩
    · obtain ⟨rfl, h1, h2⟩ := hb'; exact Or.inr ⟨rfl, by omega, by simp at h2 ⊢; omega⟩

/-- Two distinct slots of length $N$ do not overlap. -/
theorem slot_disjoint (N : ℕ) {a b : ℕ} (hab : a ≠ b) : N * a + N ≤ N * b ∨ N * b + N ≤ N * a := by
  rcases Nat.lt_or_gt_of_ne hab with h | h
  · exact Or.inl (by nlinarith)
  · exact Or.inr (by nlinarith)

/-- **One iteration of the loop of the Lanczos program**: copy the current slot into column $j$
of `Q`, then one step (`NLAlib.Computation.exec_lanczosStepWith`) with the slots rotated. -/
theorem exec_lanczos_iter (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem) {N : ℕ} (hN : ((N + 4 : ℕ) : ℝ) * u p < 1)
    {mv : ℕ → IExp ℕ → IExp ℕ → Builder P ι ℕ ℕ Unit} {R : ℕ} {s₀ : Store P K}
    {H : Matrix (Fin N) (Fin N) ℝ} {c : ℝ} (hmv : LanczosMvSpec I mv p dec R s₀ H c)
    (st : St P K C) {S : Array (P × ℕ)} (hsh : st.store.shape = S)
    (hR : ∀ i, st.store.read p R i = s₀.read p R i) {W sb La Lb LQ q : ℕ} (j : ℕ) (hj : j < q)
    (hSW : S[W]? = some (p, 3 * N)) (hS : S[sb]? = some (p, 4)) (hSa : S[La]? = some (p, q))
    (hSb : S[Lb]? = some (p, q)) (hSQ : S[LQ]? = some (p, N * (q + 1)))
    (hWs : W ≠ sb) (hRW : R ≠ W) (haW : La ≠ W) (has : La ≠ sb) (hbW : Lb ≠ W) (hbs : Lb ≠ sb)
    (hab : La ≠ Lb) (hRQ : R ≠ LQ) (hQW : LQ ≠ W) (hQs : LQ ≠ sb) (hQa : LQ ≠ La) (hQb : LQ ≠ Lb)
    {x y : Fin N → ℝ} {b₀ : ℝ} (hx : DecVec st.store p dec W (N * (j % 3)) x)
    (hy : DecVec st.store p dec W (N * ((j + 2) % 3)) y) (hb₀ : DecCell st.store p dec sb 1 b₀)
    (h3 : DecCell st.store p dec sb 3 0) :
    ∃ (st' : St P K C) (uv w zv v : Fin N → ℝ) (α β : ℝ),
      exec I (copyv p W (IExp.const N * (IExp.var j % 3)) LQ (IExp.const N * IExp.var j)
        (.const N) >>= fun _ => lanczosStepWith mv p (.const N) W
          (IExp.const N * (IExp.var j % 3)) (IExp.const N * ((IExp.var j + 2) % 3))
          (IExp.const N * ((IExp.var j + 1) % 3)) sb ⟨La, IExp.var j⟩ ⟨Lb, IExp.var j⟩).run st =
        some st' ∧
      StoreFrame p st.store st'.store (fun b i => StoreBlock W 0 (3 * N) b i ∨
        StoreBlock sb 0 3 b i ∨ StoreBlock La j 1 b i ∨ StoreBlock Lb j 1 b i ∨
        StoreBlock LQ (N * j) N b i) ∧
      DecVec st'.store p dec W (N * ((j + 1) % 3)) v ∧
      DecVec st'.store p dec W (N * ((j + 1 + 2) % 3)) x ∧ DecCell st'.store p dec sb 1 β ∧
      DecCell st'.store p dec sb 3 0 ∧ DecCell st'.store p dec La j α ∧
      DecCell st'.store p dec Lb j β ∧ DecVec st'.store p dec LQ (N * j) x ∧
      LanczosStepErr H c (roundingFactor 2 (u p)) (roundingFactor N (u p)) (u p)
        (roundingFactor (N + 4) (u p)) y x b₀ uv w zv α β v := by
  obtain ⟨st₁, h₁, hf₁, hq₁⟩ := exec_copyv_decVec I st hsh W (IExp.const N * (IExp.var j % 3)) LQ
    (IExp.const N * IExp.var j) hx hSQ (by simp; nlinarith) fun h' => absurd h'.symm hQW
  have hm3 : ∀ a, a % 3 < 3 := fun a => Nat.mod_lt _ (by norm_num)
  obtain ⟨st₂, uv, w, zv, v, α, β, h₂, hf₂, hv₂, hα₂, hβ₂, hβ₂', hE⟩ := exec_lanczosStepWith I h hz
    hN hmv (x := x) (y := y) (b₀ := b₀) st₁ (hf₁.1.trans hsh)
    (fun i => (hf₁.2 _ _ fun hb' => hRQ hb'.1).trans (hR i))
    (IExp.const N * (IExp.var j % 3)) (IExp.const N * ((IExp.var j + 2) % 3))
    (IExp.const N * ((IExp.var j + 1) % 3)) ⟨La, IExp.var j⟩ ⟨Lb, IExp.var j⟩ hWs hRW hS hSW
    (by simp; nlinarith [hm3 (j + 1)]) hSa hj has haW hSb hj hbs hbW hab
    (by simpa using slot_disjoint N (a := j % 3) (b := (j + 1) % 3) (by omega))
    (by simpa using slot_disjoint N (a := (j + 2) % 3) (b := (j + 1) % 3) (by omega))
    (by exact hx.frame hf₁ fun i _ hb' => hQW hb'.1.symm)
    (by exact hy.frame hf₁ fun i _ hb' => hQW hb'.1.symm) (hb₀.frame hf₁ fun hb' => hQs hb'.1.symm)
    (h3.frame hf₁ fun hb' => hQs hb'.1.symm)
  have hcn := slot_disjoint N (a := j % 3) (b := (j + 1) % 3) (by omega)
  refine ⟨st₂, uv, w, zv, v, α, β, ?_, (hf₁.trans hf₂).mono fun b i hb' => ?_, by exact hv₂, ?_,
    hβ₂', (h3.frame hf₁ fun hb' => hQs hb'.1.symm).frame hf₂ fun hb' => ?_, by exact hα₂,
    by exact hβ₂, hq₁.frame hf₂ fun i _ hb' => ?_, hE⟩
  · rw [exec_bind_of_exec_eq_some I (seqShape_copyv _ _ _ _ _ _) h₁, h₂]
  · rcases hb' with ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩ | hb' | hb' | hb'
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, h1, h2⟩)))
    · refine Or.inl ⟨rfl, Nat.zero_le _, ?_⟩
      simp at h2
      nlinarith [hm3 (j + 1)]
    · exact Or.inr (Or.inl hb')
    · exact Or.inr (Or.inr (Or.inl hb'))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hb')))
  · rw [show (j + 1 + 2) % 3 = j % 3 by omega]
    refine (hx.frame hf₁ fun i _ hb' => hQW hb'.1.symm).frame hf₂ fun i hi hb' => ?_
    rcases hb' with ⟨-, h1, h2⟩ | ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩
    · simp at h1 h2; omega
    · exact hWs h'
    · exact haW h'.symm
    · exact hbW h'.symm
  · rcases hb' with ⟨h', -⟩ | ⟨-, -, h'⟩ | ⟨h', -⟩ | ⟨h', -⟩
    · exact hWs h'.symm
    · omega
    · exact has h'.symm
    · exact hbs h'.symm
  · rcases hb' with ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩
    · exact hQW h'
    · exact hQs h'
    · exact hQa h'
    · exact hQb h'

/-- The region the Lanczos program writes: the three slots, the scalars, and the outputs. -/
def lanczosRegion (W sb La Lb LQ N q : ℕ) (b i : ℕ) : Prop :=
  StoreBlock W 0 (3 * N) b i ∨ StoreBlock sb 0 4 b i ∨ StoreBlock La 0 q b i ∨
    StoreBlock Lb 0 q b i ∨ StoreBlock LQ 0 (N * (q + 1)) b i

/-- **The loop invariant of the Lanczos program** after $j$ iterations: the store is in the
frame of the region of the program, and there are computed vectors and coefficients
(`LanczosRun` indexing) with the start facts, the local errors of the first $j$ steps, the
current and previous vectors in the rotating slots, $\beta_j$ and $0$ in `s[1]`, `s[3]`, and
the first $j$ outputs written. -/
def LanczosLoopInv (p : P) (dec : P → K → ℝ) (s₁ : Store P K) (W sb La Lb LQ q : ℕ) {N : ℕ}
    (H : Matrix (Fin N) (Fin N) ℝ) (c u : ℝ) (bv : Fin N → ℝ) (j : ℕ) (s : Store P K) : Prop :=
  StoreFrame p s₁ s (lanczosRegion W sb La Lb LQ N q) ∧
  ∃ (v uv w z : ℕ → Fin N → ℝ) (α β : ℕ → ℝ), v 0 = 0 ∧ β 0 = 0 ∧
    (∃ (c₀ : ℝ) (δ₀ : Fin N → ℝ), 0 < c₀ ∧ c₀ • v 1 = bv + δ₀ ∧
      ‖WithLp.toLp 2 δ₀‖ ≤ u * ‖WithLp.toLp 2 bv‖) ∧
    |‖WithLp.toLp 2 (v 1)‖ ^ 2 - 1| ≤ roundingFactor (N + 4) u ∧
    (∀ i < j, LanczosStepErr H c (roundingFactor 2 u) (roundingFactor N u) u
      (roundingFactor (N + 4) u) (v i) (v (i + 1)) (β i) (uv (i + 1)) (w (i + 1)) (z (i + 1))
      (α (i + 1)) (β (i + 1)) (v (i + 2))) ∧
    DecVec s p dec W (N * (j % 3)) (v (j + 1)) ∧ DecVec s p dec W (N * ((j + 2) % 3)) (v j) ∧
    DecCell s p dec sb 1 (β j) ∧ DecCell s p dec sb 3 0 ∧
    ∀ k < j, DecCell s p dec La k (α (k + 1)) ∧ DecCell s p dec Lb k (β (k + 1)) ∧
      DecVec s p dec LQ (N * k) (v (k + 1))

/-- **The loop invariant is kept** by one iteration (`NLAlib.Computation.exec_lanczos_iter`). -/
theorem LanczosLoopInv.succ (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem) {N : ℕ} (hN : ((N + 4 : ℕ) : ℝ) * u p < 1)
    {mv : ℕ → IExp ℕ → IExp ℕ → Builder P ι ℕ ℕ Unit} {R : ℕ} {s₀ s₁ : Store P K}
    {H : Matrix (Fin N) (Fin N) ℝ} {c : ℝ} (hmv : LanczosMvSpec I mv p dec R s₀ H c)
    {S : Array (P × ℕ)} (hS₁ : s₁.shape = S) (hR₁ : ∀ i, s₁.read p R i = s₀.read p R i)
    {W sb La Lb LQ q : ℕ} (hSW : S[W]? = some (p, 3 * N)) (hS : S[sb]? = some (p, 4))
    (hSa : S[La]? = some (p, q)) (hSb : S[Lb]? = some (p, q))
    (hSQ : S[LQ]? = some (p, N * (q + 1))) (hWs : W ≠ sb) (haW : La ≠ W) (has : La ≠ sb)
    (hbW : Lb ≠ W) (hbs : Lb ≠ sb) (hab : La ≠ Lb) (hQW : LQ ≠ W) (hQs : LQ ≠ sb)
    (hQa : LQ ≠ La) (hQb : LQ ≠ Lb) (hRW : R ≠ W) (hRs : R ≠ sb) (hRa : R ≠ La) (hRb : R ≠ Lb)
    (hRQ : R ≠ LQ) {bv : Fin N → ℝ} (j : ℕ) (hj : j < q) (st : St P K C)
    (hinv : LanczosLoopInv p dec s₁ W sb La Lb LQ q H c (u p) bv j st.store) :
    ∃ st' : St P K C, exec I (copyv p W (IExp.const N * (IExp.var j % 3)) LQ
        (IExp.const N * IExp.var j) (.const N) >>= fun _ => lanczosStepWith mv p (.const N) W
          (IExp.const N * (IExp.var j % 3)) (IExp.const N * ((IExp.var j + 2) % 3))
          (IExp.const N * ((IExp.var j + 1) % 3)) sb ⟨La, IExp.var j⟩ ⟨Lb, IExp.var j⟩).run st =
        some st' ∧
      LanczosLoopInv p dec s₁ W sb La Lb LQ q H c (u p) bv (j + 1) st'.store := by
  obtain ⟨hf, v, uv, w, z, α, β, hv0, hβ0, hst, hun, hE, hcur, hprev, hb1, h3, hout⟩ := hinv
  have hR : ∀ i, st.store.read p R i = s₀.read p R i := fun i =>
    (hf.2 R i fun hb' => by
      rcases hb' with ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ <;> contradiction).trans
      (hR₁ i)
  obtain ⟨st', uvn, wn, zn, vn, αn, βn, he, hf', hv', hx', hb1', h3', hα', hβ', hq', hE'⟩ :=
    exec_lanczos_iter I h hz hN hmv st (hf.1.trans hS₁) hR j hj hSW hS hSa hSb hSQ hWs hRW haW
      has hbW hbs hab hRQ hQW hQs hQa hQb hcur hprev hb1 h3
  refine ⟨st', he, (hf.trans hf').mono fun b i hb' => ?_, Function.update v (j + 2) vn,
    Function.update uv (j + 1) uvn, Function.update w (j + 1) wn, Function.update z (j + 1) zn,
    Function.update α (j + 1) αn, Function.update β (j + 1) βn, ?_, ?_, ?_, ?_, fun i hi => ?_,
    ?_, ?_, ?_, h3', fun k hk => ?_⟩
  · rcases hb' with hb' | ⟨rfl, -, h2⟩ | ⟨rfl, -, h2⟩ | ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩ |
      ⟨rfl, h1, h2⟩
    · exact hb'
    · exact Or.inl ⟨rfl, Nat.zero_le _, by simpa using h2⟩
    · exact Or.inr (Or.inl ⟨rfl, Nat.zero_le _, by omega⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, Nat.zero_le _, by omega⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Nat.zero_le _, by omega⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, Nat.zero_le _, by nlinarith⟩)))
  · rw [Function.update_of_ne (by omega), hv0]
  · rw [Function.update_of_ne (by omega), hβ0]
  · rw [Function.update_of_ne (by omega)]; exact hst
  · rw [Function.update_of_ne (by omega)]; exact hun
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · simp only [Function.update_of_ne (show i ≠ j + 2 by omega),
        Function.update_of_ne (show i + 1 ≠ j + 2 by omega),
        Function.update_of_ne (show i + 2 ≠ j + 2 by omega),
        Function.update_of_ne (show i ≠ j + 1 by omega),
        Function.update_of_ne (show i + 1 ≠ j + 1 by omega)]
      exact hE i hi
    · simp only [Function.update_self, Function.update_of_ne (show i ≠ i + 2 by omega),
        Function.update_of_ne (show i + 1 ≠ i + 2 by omega),
        Function.update_of_ne (show i ≠ i + 1 by omega)]
      exact hE'
  · rw [Function.update_self]; exact hv'
  · rw [Function.update_of_ne (by omega)]; exact hx'
  · rw [Function.update_self]; exact hb1'
  · have hfr := hf'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · obtain ⟨ha, hb, hq⟩ := hout k hk
      simp only [Function.update_of_ne (show k + 1 ≠ j + 1 by omega),
        Function.update_of_ne (show k + 1 ≠ j + 2 by omega)]
      refine ⟨ha.frame hfr ?_, hb.frame hfr ?_, hq.frame hfr fun i hi => ?_⟩
      · rintro (⟨h', -⟩ | ⟨h', -⟩ | ⟨-, h1, h2⟩ | ⟨h', -⟩ | ⟨h', -⟩)
        · exact haW h'
        · exact has h'
        · omega
        · exact hab h'
        · exact hQa h'.symm
      · rintro (⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ | ⟨-, h1, h2⟩ | ⟨h', -⟩)
        · exact hbW h'
        · exact hbs h'
        · exact hab h'.symm
        · omega
        · exact hQb h'.symm
      · rintro (⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ | ⟨-, h1, h2⟩)
        · exact hQW h'
        · exact hQs h'
        · exact hQa h'
        · exact hQb h'
        · nlinarith
    · simp only [Function.update_self, Function.update_of_ne (show k + 1 ≠ k + 2 by omega)]
      exact ⟨hα', hβ', hq'⟩

/-- The run of an allocation, for a postcondition on the popped store. -/
theorem exec_alloc_of {p : P} {len : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ} {st : St P K C}
    {Q : Store P K → Prop} (h' : ∀ st₁ : St P K C,
      st₁.store = st.store.push (p, Array.replicate len.eval none) →
      ∃ st₂ : St P K C, exec I (body st.store.size) st₁ = some st₂ ∧ Q st₂.store.pop) :
    ∃ st' : St P K C, exec I (.alloc p len body) st = some st' ∧ Q st'.store := by
  obtain ⟨st₂, h₂, hQ⟩ := h' { st with
      store := st.store.push (p, Array.replicate len.eval none)
      cur := Function.update st.cur p (st.cur p + len.eval)
      peak := Function.update st.peak p (max (st.peak p) (st.cur p + len.eval))
      curW := st.curW + len.eval * I.width p
      peakW := max st.peakW (st.curW + len.eval * I.width p) } rfl
  exact ⟨_, by rw [exec_alloc, h₂]; rfl, hQ⟩

omit [DecidableEq P] [AddMonoid C] in
theorem run_alloc_bind (p : P) (len : IExp ℕ) (f : ℕ → Builder P ι ℕ ℕ Unit) :
    (Builder.alloc p len >>= f).run = .alloc p len fun b => (f b).run := rfl

/-- The facts of a run of the Lanczos program on its outputs, at the store `s`: computed vectors
and coefficients with the start facts, the local errors of the $q$ steps, and the output buffers
holding $\alpha_{j+1}$, $\beta_{j+1}$ ($j < q$) and $\mathbf{v}_{j+1}$ ($j \le q$). -/
def LanczosRunFacts (p : P) (dec : P → K → ℝ) (La Lb LQ q : ℕ) {N : ℕ}
    (H : Matrix (Fin N) (Fin N) ℝ) (c u : ℝ) (bv : Fin N → ℝ) (s : Store P K) : Prop :=
  ∃ (v uv w z : ℕ → Fin N → ℝ) (α β : ℕ → ℝ), v 0 = 0 ∧ β 0 = 0 ∧
    (∃ (c₀ : ℝ) (δ₀ : Fin N → ℝ), 0 < c₀ ∧ c₀ • v 1 = bv + δ₀ ∧
      ‖WithLp.toLp 2 δ₀‖ ≤ u * ‖WithLp.toLp 2 bv‖) ∧
    |‖WithLp.toLp 2 (v 1)‖ ^ 2 - 1| ≤ roundingFactor (N + 4) u ∧
    (∀ i < q, LanczosStepErr H c (roundingFactor 2 u) (roundingFactor N u) u
      (roundingFactor (N + 4) u) (v i) (v (i + 1)) (β i) (uv (i + 1)) (w (i + 1)) (z (i + 1))
      (α (i + 1)) (β (i + 1)) (v (i + 2))) ∧
    (∀ k < q, DecCell s p dec La k (α (k + 1)) ∧ DecCell s p dec Lb k (β (k + 1))) ∧
    ∀ k ≤ q, DecVec s p dec LQ (N * k) (v (k + 1))

/-- The Lanczos program after its two allocations: the start, the loop and the last column. -/
theorem exec_lanczos_inner (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem) {N : ℕ} (hN : ((N + 4 : ℕ) : ℝ) * u p < 1)
    {mv : ℕ → IExp ℕ → IExp ℕ → Builder P ι ℕ ℕ Unit} {R : ℕ} {s₀ : Store P K}
    {H : Matrix (Fin N) (Fin N) ℝ} {c : ℝ} (hmv : LanczosMvSpec I mv p dec R s₀ H c)
    (st : St P K C) {S : Array (P × ℕ)} (hsh : st.store.shape = S)
    (hR₁ : ∀ i, st.store.read p R i = s₀.read p R i)
    {B W sb La Lb LQ q : ℕ} {bv : Fin N → ℝ} (hB : DecVec st.store p dec B 0 bv) (hb0 : bv ≠ 0)
    (hSW : S[W]? = some (p, 3 * N)) (hS : S[sb]? = some (p, 4))
    (hSa : S[La]? = some (p, q)) (hSb : S[Lb]? = some (p, q))
    (hSQ : S[LQ]? = some (p, N * (q + 1))) (hBW : B ≠ W) (hBs : B ≠ sb) (hWs : W ≠ sb)
    (haW : La ≠ W) (has : La ≠ sb)
    (hbW : Lb ≠ W) (hbs : Lb ≠ sb) (hab : La ≠ Lb) (hQW : LQ ≠ W) (hQs : LQ ≠ sb)
    (hQa : LQ ≠ La) (hQb : LQ ≠ Lb) (hRW : R ≠ W) (hRs : R ≠ sb) (hRa : R ≠ La) (hRb : R ≠ Lb)
    (hRQ : R ≠ LQ) :
    ∃ st' : St P K C, exec I (lanczosInit p (.const N) B W sb >>= fun _ =>
        forRange (.const q) (fun j => copyv p W (IExp.const N * (IExp.var j % 3)) LQ
          (IExp.const N * IExp.var j) (.const N) >>= fun _ => lanczosStepWith mv p (.const N) W
            (IExp.const N * (IExp.var j % 3)) (IExp.const N * ((IExp.var j + 2) % 3))
            (IExp.const N * ((IExp.var j + 1) % 3)) sb ⟨La, IExp.var j⟩ ⟨Lb, IExp.var j⟩) >>=
        fun _ => copyv p W (IExp.const N * (IExp.const q % 3)) LQ (IExp.const N * IExp.const q)
          (.const N)).run st = some st' ∧
      st'.store.shape = S ∧ LanczosRunFacts p dec La Lb LQ q H c (u p) bv st'.store := by
  obtain ⟨st₁, v₁, h₁, hf₁, hv₁, h0₁, hb1₁, h3₁, hst₁, hun₁⟩ := exec_lanczosInit I h hz hN st hsh
    hB hb0 hBW hBs hWs hSW hS
  have hinv₀ : LanczosLoopInv p dec st.store W sb La Lb LQ q H c (u p) bv 0 st₁.store := by
    refine ⟨hf₁.mono fun b i hb' => ?_, fun k => if k = 1 then v₁ else 0, 0, 0, 0, 0, 0, rfl,
      rfl, by simpa using hst₁, by simpa using hun₁, fun i hi => absurd hi (Nat.not_lt_zero _),
      by simpa using hv₁, by simpa using h0₁, by simpa using hb1₁, h3₁,
      fun k hk => absurd hk (Nat.not_lt_zero _)⟩
    rcases hb' with hb' | hb'
    · exact Or.inl hb'
    · exact Or.inr (Or.inl hb')
  obtain ⟨st₂, h₂, hinv⟩ := exists_exec_loop_eq_some_of_forall I (n := .const q)
    (fun j st' => LanczosLoopInv p dec st.store W sb La Lb LQ q H c (u p) bv j st'.store) hinv₀
    fun j hj st' hI => LanczosLoopInv.succ I h hz hN hmv hsh hR₁ hSW hS hSa hSb hSQ hWs haW has
      hbW hbs hab hQW hQs hQa hQb hRW hRs hRa hRb hRQ j hj st' hI
  obtain ⟨hf, v, uv, w, z, α, β, hv0, hβ0, hst, hun, hE, hcur, -, -, -, hout⟩ := hinv
  obtain ⟨st₃, h₃, hf₃, hq₃⟩ := exec_copyv_decVec I st₂ (hf.1.trans hsh) W
    (IExp.const N * (IExp.const q % 3)) LQ (IExp.const N * IExp.const q) hcur hSQ
    (by simp; nlinarith) fun h' => absurd h'.symm hQW
  refine ⟨st₃, ?_, hf₃.1.trans (hf.1.trans hsh), v, uv, w, z, α, β, hv0, hβ0, hst, hun, hE,
    fun k hk => ?_, fun k hk => ?_⟩
  · rw [h₁ _, exec_bind_of_exec_eq_some I (seqShape_forRange _ _)
      ((exec_seq_skip I _ _).trans h₂), h₃]
  · obtain ⟨ha, hb, -⟩ := hout k hk
    exact ⟨ha.frame hf₃ fun hb' => hQa hb'.1.symm, hb.frame hf₃ fun hb' => hQb hb'.1.symm⟩
  · rcases Nat.lt_or_ge k q with hk' | hk'
    · exact (hout k hk').2.2.frame hf₃ fun i hi hb' => by
        obtain ⟨-, h1, -⟩ := hb'; simp at h1; nlinarith
    · obtain rfl : k = q := le_antisymm hk hk'
      exact hq₃

theorem lanczosRunFacts_pop {La Lb LQ q : ℕ} {N : ℕ} {H : Matrix (Fin N) (Fin N) ℝ} {c u : ℝ}
    {bv : Fin N → ℝ} {s : Store P K} (ha : La + 1 < s.size) (hb : Lb + 1 < s.size)
    (hQ : LQ + 1 < s.size) (h' : LanczosRunFacts p dec La Lb LQ q H c u bv s) :
    LanczosRunFacts p dec La Lb LQ q H c u bv s.pop := by
  obtain ⟨v, uv, w, z, α, β, h1, h2, h3, h4, h5, h6, h7⟩ := h'
  refine ⟨v, uv, w, z, α, β, h1, h2, h3, h4, h5, fun k hk => ?_, fun k hk i => ?_⟩
  · obtain ⟨⟨wa, hwa, hda⟩, ⟨wb, hwb, hdb⟩⟩ := h6 k hk
    exact ⟨⟨wa, by rw [Store.read_pop_of_lt (by omega)]; exact hwa, hda⟩,
      ⟨wb, by rw [Store.read_pop_of_lt (by omega)]; exact hwb, hdb⟩⟩
  · obtain ⟨wq, hwq, hdq⟩ := h7 k hk i
    exact ⟨wq, by rw [Store.read_pop_of_lt (by omega)]; exact hwq, hdq⟩

/-- **The run of the Lanczos program in the standard model**, for any product meeting
`NLAlib.LanczosMvSpec` (with read-only buffer `R` as in the initial store): under
`NLAlib.Computation.IsRelErrSem` with every value in range and adding zero exactly, with
$(N + 4)u_p < 1$, a start vector $\mathbf{b} \ne \mathbf{0}$ in buffer `B` and writable output
buffers `La`, `Lb` ($q$ cells) and `LQ` ($N(q + 1)$ cells), the run succeeds and its outputs
satisfy `NLAlib.LanczosRunFacts`: the start facts and the local errors of every step, with the
product bound $c$, the update bound $\gamma_2$, the inner-product bound $\gamma_N$, the
normalisation bound $u_p$ and near unit length $\gamma_{N+4}$. [Higham2002, §§2.2, 3.1,
Lemma 3.3], [Chen, `sec:model`]. -/
theorem _root_.NLAlib.Computation.IsRelErrSem.exists_lanczosRunFacts_of_lanczosBasisProgWith
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem) {N q : ℕ} (hN : ((N + 4 : ℕ) : ℝ) * u p < 1)
    {mv : ℕ → IExp ℕ → IExp ℕ → Builder P ι ℕ ℕ Unit} {R : ℕ} {H : Matrix (Fin N) (Fin N) ℝ}
    {c : ℝ} (st : St P K C) (hmv : LanczosMvSpec I mv p dec R st.store H c)
    {B La Lb LQ : ℕ} {bv : Fin N → ℝ} (hB : DecVec st.store p dec B 0 bv) (hb0 : bv ≠ 0)
    (hBs : B < st.store.size) (hRs : R < st.store.size)
    (hSa : st.store.shape[La]? = some (p, q)) (hSb : st.store.shape[Lb]? = some (p, q))
    (hSQ : st.store.shape[LQ]? = some (p, N * (q + 1))) (hab : La ≠ Lb) (hQa : LQ ≠ La)
    (hQb : LQ ≠ Lb) (hRa : R ≠ La) (hRb : R ≠ Lb) (hRQ : R ≠ LQ) :
    ∃ st' : St P K C,
      exec I (lanczosBasisProgWith mv p (.const N) (.const q) B La Lb LQ).run st = some st' ∧
      LanczosRunFacts p dec La Lb LQ q H c (u p) bv st'.store := by
  have hlt : ∀ {b n}, st.store.shape[b]? = some (p, n) → b < st.store.size := fun hb' => by
    have := (Array.getElem?_eq_some_iff.mp hb').1
    rwa [Store.size_shape] at this
  have hLa := hlt hSa
  have hLb := hlt hSb
  have hLQ := hlt hSQ
  unfold lanczosBasisProgWith
  rw [run_alloc_bind]
  refine exec_alloc_of I fun st₁ hst₁ => ?_
  simp only [run_alloc_bind]
  refine exec_alloc_of I (p := p) (st := st₁) (len := 4)
    (Q := fun s => LanczosRunFacts p dec La Lb LQ q H c (u p) bv s.pop) fun st₃ hst₃ => ?_
  have hsz₁ : st₁.store.size = st.store.size + 1 := by rw [hst₁]; simp
  have hrd : ∀ b i, b < st.store.size → st₃.store.read p b i = st.store.read p b i :=
    fun b i hb' => by
      rw [hst₃, Store.read_push_of_lt (s := st₁.store) (by omega), hst₁,
        Store.read_push_of_lt hb']
  have hshp : ∀ b, b < st.store.size → st₃.store.shape[b]? = st.store.shape[b]? :=
    fun b hb' => by
      rw [hst₃, Store.getElem?_shape_push_of_lt (s := st₁.store) _ (by omega), hst₁,
        Store.getElem?_shape_push_of_lt _ hb']
  obtain ⟨st₄, h₄, hsh₄, hF⟩ := exec_lanczos_inner I h hz hN hmv st₃ rfl
    (fun i => hrd R i hRs) (W := st.store.size) (sb := st₁.store.size)
    (fun i => by rw [hrd B _ hBs]; exact hB i) hb0
    (by rw [hst₃, Store.getElem?_shape_push_of_lt (s := st₁.store) _ (by omega), hst₁,
      Store.getElem?_shape_push_size]; rfl)
    (by rw [hst₃]; exact Store.getElem?_shape_push_size _ _ _)
    (by rw [hshp _ hLa]; exact hSa) (by rw [hshp _ hLb]; exact hSb)
    (by rw [hshp _ hLQ]; exact hSQ) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) hab (by omega) (by omega) hQa hQb (by omega) (by omega) hRa hRb hRQ
  have hsz₄ : st₄.store.size = st.store.size + 2 := by
    rw [← Store.size_shape, hsh₄, Store.size_shape, hst₃]; simp [hsz₁]
  refine ⟨st₄, h₄, lanczosRunFacts_pop ?_ ?_ ?_ (lanczosRunFacts_pop ?_ ?_ ?_ hF)⟩ <;>
    simp [hsz₄] <;> omega

end Pieces

end NLAlib
