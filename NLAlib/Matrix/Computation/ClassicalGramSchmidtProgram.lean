/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Allocation
public import NLAlib.Computation.BLAS.RoundingErrors
public import NLAlib.Matrix.Computation.ClassicalGramSchmidtRoundingError
public import NLAlib.Matrix.Computation.OrthRoutine

/-!
# Runs of classical Gram–Schmidt with reorthogonalization

The runs of `NLAlib.cgsPass` and `NLAlib.cgs2` under the standard model of rounded arithmetic
(`NLAlib.Computation.IsRelErrSem`, adding zero exact). One pass succeeds, writes only the reduced
vector and the coefficients, and its decoded results satisfy the three error bounds of
`NLAlib.norm_sub_le_cgsPassBound_mul_norm_of_abs_sub_le` with `NLAlib.cgsPassBound`,
that is <!-- value cgsPassBound N j u \eta_0 -->$c_1 = 2(1+\eta_0)\sqrt{j+1}\,(N+j+2)\,u$.
Two passes with the coefficients summed meet `NLAlib.IsOrthErr` at
$(\eta_0, 2c_1, 3c_1, 2(\eta_0 + c_1)^2)$ (`NLAlib.isOrthErr_of_two_passes`), which makes
`NLAlib.cgs2` an orthogonalization routine (`NLAlib.Computation.IsOrthRoutine`). Exact real
arithmetic is the case $u = 0$, where the bounds force the exact values. Design:
`docs/design/Krylov-LanczosReorth.md` §2.2.

## Main results

* `NLAlib.Computation.IsRelErrSem.exec_cgsPass`: the rounded pass.
* `NLAlib.Computation.IsRelErrSem.isOrthRoutine_cgs2`: CGS2 is a certified orthogonalization
  routine.
* `NLAlib.Computation.exec_cgs2_exactSem`: the exact run.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Computation

open Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- The $j$ rounded dots of a pass write coefficients within the partial-sum bound of
$\mathbf{V}^{\mathsf{T}}\mathbf{w}$ as one block write into the coefficient block. -/
private theorem exec_cgsPass_dots {u : P → ℝ} {dec : P → K → ℝ} (I : Interp P ι K C)
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem) (tag : P)
    (NE jE : IExp ℕ) (Vb wb hb : ℕ) (wo ho : IExp ℕ) (st : St P K C)
    (V : Matrix (Fin NE.eval) (Fin jE.eval) ℝ) (w : Fin NE.eval → ℝ)
    (hV : HoldsDecoded st.store dec tag Vb 0 V) (hw : ReadsDecoded st.store dec tag wb wo.eval w)
    (hhlen : Writable st.store tag hb ho.eval jE.eval)
    (hne : 0 < NE.eval → 0 < jE.eval → hb ≠ wb ∧ hb ≠ Vb) :
    ∃ (s' : St P K C) (Hw : Fin jE.eval → K), exec I (.loop jE fun i =>
        (dot tag ⟨hb, ho + .var i⟩ Vb (NE * .var i) wb wo NE).run) st = some s' ∧
      st.store.writeBlock tag hb ho.eval (Array.ofFn Hw) = some s'.store ∧
      ∀ k : Fin jE.eval, |dec tag (Hw k) - (Vᵀ *ᵥ w) k| ≤ (1 + u tag) ^ NE.eval * u tag *
        ((Vᵀ.map abs *ᵥ fun r => |w r|) k + ∑ r ∈ Finset.range NE.eval,
          |(Vᵀ *ᵥ fun t : Fin NE.eval => if (t : ℕ) < r + 1 then w t else 0) k|) := by
  have hA := h.isArithErrSem fun _ => trivial
  obtain ⟨s', Hw, hrun, hst, hval⟩ := exists_exec_loop_writeBlock I (n := jE)
    (body := fun i => (dot tag ⟨hb, ho + .var i⟩ Vb (NE * .var i) wb wo NE).run) (st := st)
    tag hb ho.eval (fun k x => ∀ hk : k < jE.eval, |dec tag x - (Vᵀ *ᵥ w) ⟨k, hk⟩| ≤
      (1 + u tag) ^ NE.eval * u tag * ((Vᵀ.map abs *ᵥ fun r => |w r|) ⟨k, hk⟩ +
        ∑ r ∈ Finset.range NE.eval,
          |(Vᵀ *ᵥ fun t : Fin NE.eval => if (t : ℕ) < r + 1 then w t else 0) ⟨k, hk⟩|))
    fun k hk _ s _ _ hs => by
      have hrd : ∀ {b i}, b ≠ hb → s.store.read tag b i = st.store.read tag b i :=
        fun hb' => Store.read_of_writeBlock_eq_some_of_ne hs (Or.inl hb')
      obtain ⟨st', x, sv, hrun, hst, htr, hx⟩ := IsArithErrSem.exec_dot I tag s hA hz
        ⟨hb, ho + .var k⟩ Vb (NE * .var k) wb wo NE
        (fun r => if h : r < NE.eval then V ⟨r, h⟩ ⟨k, hk⟩ else 0)
        (fun r => if h : r < NE.eval then w ⟨r, h⟩ else 0)
        (fun r hr => by
          obtain ⟨x, hx, hdx⟩ := hV ⟨r, hr⟩ ⟨k, hk⟩
          refine ⟨x, ?_, by simp [hr, hdx]⟩
          rw [hrd (Ne.symm (hne (by omega) (by omega)).2)]
          simpa [IExp.eval, Nat.add_comm] using hx)
        (fun r hr => by
          obtain ⟨x, hx, hdx⟩ := hw ⟨r, hr⟩
          exact ⟨x, by rw [hrd (Ne.symm (hne (by omega) (by omega)).1)]; exact hx,
            by simp [hr, hdx]⟩)
        (fun e r hr => absurd e (hne (by omega) (by omega)).2)
        (fun e r hr => absurd e (hne (by omega) (by omega)).1) (by
          obtain ⟨len, hlen, hlt⟩ := hhlen k hk
          obtain ⟨z0, -⟩ := h.lit_ok tag 0 trivial
          exact ⟨z0, Store.exists_write_eq_some_of_getElem?_shape z0
            (by rw [Store.shape_of_writeBlock_eq_some hs]; exact hlen) hlt⟩)
        (fun _ _ _ _ => ⟨trivial, fun _ _ => trivial⟩)
      refine ⟨st', x, hrun, hst, fun hk' => ?_⟩
      rw [hx]
      exact IsDotTrace.abs_sub_mulVec_le Vᵀ w ⟨k, hk'⟩ (fun r hr => by simp [hr])
        (fun r hr => by simp [hr]) htr (h.nonneg trivial)
  exact ⟨s', Hw, hrun, hst, fun k => hval k k.2⟩

/-- The rounded `gemv` of a pass writes a block within the partial-sum bound of
$\mathbf{V}\mathbf{h}$ into the scratch buffer `S`. -/
private theorem exec_cgsPass_gemv {u : P → ℝ} {dec : P → K → ℝ} (I : Interp P ι K C)
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem) (tag : P)
    (NE jE : IExp ℕ) (Vb hb S : ℕ) (ho : IExp ℕ) (s : St P K C)
    (V : Matrix (Fin NE.eval) (Fin jE.eval) ℝ) (hh : Fin jE.eval → ℝ)
    (hV : HoldsDecoded s.store dec tag Vb 0 V)
    (hhd : ∀ k : Fin jE.eval, ∃ x, s.store.read tag hb (ho.eval + k) = some x ∧ dec tag x = hh k)
    (hS : s.store.shape[S]? = some (tag, NE.eval)) (hSV : S = Vb → NE.eval * jE.eval = 0)
    (hSh : S = hb → jE.eval = 0) :
    ∃ (s' : St P K C) (Y : ℕ → K), exec I (gemv tag NE jE Vb 0 hb ho S 0).run s = some s' ∧
      s.store.writeBlock tag S 0 ((List.range NE.eval).toArray.map Y) = some s'.store ∧
      ∀ i : Fin NE.eval, |dec tag (Y i) - (V *ᵥ hh) i| ≤ (1 + u tag) ^ jE.eval * u tag *
        ((V.map abs *ᵥ fun r => |hh r|) i + ∑ r ∈ Finset.range jE.eval,
          |(V *ᵥ fun t : Fin jE.eval => if (t : ℕ) < r + 1 then hh t else 0) i|) := by
  have hA := h.isArithErrSem fun _ => trivial
  have key : ∀ (x : ℕ) (xo : IExp ℕ), S ≠ x →
      (∀ k : Fin jE.eval, ∃ y, s.store.read tag x (xo.eval + k) = some y ∧ dec tag y = hh k) →
      ∃ (s' : St P K C) (Y : ℕ → K), exec I (gemv tag NE jE Vb 0 x xo S 0).run s = some s' ∧
        s.store.writeBlock tag S 0 ((List.range NE.eval).toArray.map Y) = some s'.store ∧
        ∀ i : Fin NE.eval, |dec tag (Y i) - (V *ᵥ hh) i| ≤ (1 + u tag) ^ jE.eval * u tag *
          ((V.map abs *ᵥ fun r => |hh r|) i + ∑ r ∈ Finset.range jE.eval,
            |(V *ᵥ fun t : Fin jE.eval => if (t : ℕ) < r + 1 then hh t else 0) i|) := by
    intro x xo hSx hx
    obtain ⟨z0, -⟩ := h.lit_ok tag 0 trivial
    obtain ⟨s', Y, sv, hrun, hst, hS'⟩ := IsArithErrSem.exec_gemv I tag s hA hz NE jE Vb 0 x xo
      S 0 (fun i k => if h : i < NE.eval ∧ k < jE.eval then V ⟨i, h.1⟩ ⟨k, h.2⟩ else 0)
      (fun k => if h : k < jE.eval then hh ⟨k, h⟩ else 0)
      (fun i hi k hk => by
        obtain ⟨y, hy, hdy⟩ := hV ⟨i, hi⟩ ⟨k, hk⟩
        exact ⟨y, by simpa using hy, by simp [hi, hk, hdy]⟩)
      (fun k hk => by
        obtain ⟨y, hy, hdy⟩ := hx ⟨k, hk⟩
        exact ⟨y, hy, by simp [hk, hdy]⟩)
      (fun e => Or.inr (by simp [hSV e])) (fun e => absurd e hSx)
      (fun i hi => ⟨z0, Store.exists_write_eq_some_of_getElem?_shape z0 hS (by simpa using hi)⟩)
      (fun _ _ _ _ _ _ => ⟨trivial, fun _ _ => trivial⟩)
    refine ⟨s', Y, hrun, hst, fun i => ?_⟩
    obtain ⟨htr, hY⟩ := hS' i i.2
    rw [hY]
    exact IsDotTrace.abs_sub_mulVec_le V hh i (fun r hr => by simp [hr]) (fun r hr => by simp [hr])
      htr (h.nonneg trivial)
  by_cases hj0 : jE.eval = 0
  · have heq : exec I (gemv tag NE jE Vb 0 hb ho S 0).run s =
        exec I (gemv tag NE jE Vb 0 (S + 1) 0 S 0).run s := by
      simp only [run_gemv, exec_named, exec_seq, exec_alloc, exec_loop, hj0,
        List.range_zero, List.foldlM_nil]
    rw [heq]
    exact key (S + 1) 0 (by omega) fun k => absurd k.2 (by omega)
  · exact key hb ho (fun e => hj0 (hSh e)) hhd

/-- The three error bounds of one rounded classical Gram–Schmidt pass of $\mathbf{w}$ against
$\mathbf{V}$, with decoded coefficients $\mathbf{h}$ and reduced vector $\mathbf{w}'$, under every
admissible precondition $\eta_0$. -/
private def IsPassErr {N j : ℕ} (u : ℝ) (V : Matrix (Fin N) (Fin j) ℝ) (w : Fin N → ℝ)
    (h : Fin j → ℝ) (w' : Fin N → ℝ) : Prop :=
  ∀ η₀ : ℝ, specNorm (Vᵀ * V - 1) ≤ η₀ → ((N + j + 2 : ℕ) : ℝ) * u ≤ 1 / 100 →
    ‖WithLp.toLp 2 (h - Vᵀ *ᵥ w)‖ ≤ cgsPassBound N j u η₀ * ‖WithLp.toLp 2 w‖ ∧
    ‖WithLp.toLp 2 (w - V *ᵥ h - w')‖ ≤ cgsPassBound N j u η₀ * ‖WithLp.toLp 2 w‖ ∧
    ‖WithLp.toLp 2 (w' - (w - V *ᵥ (Vᵀ *ᵥ w)))‖ ≤ cgsPassBound N j u η₀ * ‖WithLp.toLp 2 w‖

/-- The dots and the `gemv` of a rounded pass, followed by `f`: the run of `f` after the block
write of the coefficients at (`hb`, `ho`) and of the product into the scratch buffer `S`, with
their partial-product bounds. -/
private theorem exec_cgsPass_dots_gemv {u : P → ℝ} {dec : P → K → ℝ} (I : Interp P ι K C)
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem) (tag : P)
    (NE jE : IExp ℕ) (Vb wb hb S : ℕ) (wo ho : IExp ℕ) (st : St P K C)
    (V : Matrix (Fin NE.eval) (Fin jE.eval) ℝ) (w : Fin NE.eval → ℝ)
    (hV : HoldsDecoded st.store dec tag Vb 0 V) (hw : ReadsDecoded st.store dec tag wb wo.eval w)
    (hhlen : Writable st.store tag hb ho.eval jE.eval)
    (hne : 0 < NE.eval → 0 < jE.eval → hb ≠ wb ∧ hb ≠ Vb)
    (hsS : st.store.shape[S]? = some (tag, NE.eval)) (hVS : 0 < NE.eval * jE.eval → Vb < S)
    (hhS : 0 < jE.eval → hb < S) (f : Unit → Builder P ι ℕ ℕ Unit) :
    ∃ (σ₁ σ₂ : St P K C) (Hw : Fin jE.eval → K) (Y : ℕ → K),
      exec I ((forRange jE fun i => dot tag ⟨hb, ho + .var i⟩ Vb (NE * .var i) wb wo NE) >>=
        fun _ => gemv tag NE jE Vb 0 hb ho S 0 >>= f).run st = exec I (f ()).run σ₂ ∧
      st.store.writeBlock tag hb ho.eval (Array.ofFn Hw) = some σ₁.store ∧
      (∀ k : Fin jE.eval, |dec tag (Hw k) - (Vᵀ *ᵥ w) k| ≤ (1 + u tag) ^ NE.eval * u tag *
        ((Vᵀ.map abs *ᵥ fun r => |w r|) k + ∑ r ∈ Finset.range NE.eval,
          |(Vᵀ *ᵥ fun t : Fin NE.eval => if (t : ℕ) < r + 1 then w t else 0) k|)) ∧
      σ₁.store.writeBlock tag S 0 ((List.range NE.eval).toArray.map Y) = some σ₂.store ∧
      ∀ i : Fin NE.eval, |dec tag (Y i) - (V *ᵥ fun k => dec tag (Hw k)) i| ≤
        (1 + u tag) ^ jE.eval * u tag * ((V.map abs *ᵥ fun r => |dec tag (Hw r)|) i +
          ∑ r ∈ Finset.range jE.eval, |(V *ᵥ fun t : Fin jE.eval =>
            if (t : ℕ) < r + 1 then dec tag (Hw t) else 0) i|) := by
  rw [exec_run_bind I
    (b := forRange jE fun i => dot tag ⟨hb, ho + .var i⟩ Vb (NE * .var i) wb wo NE) (fun _ => rfl)]
  obtain ⟨σ₁, Hw, hrun₁, hst₁, hHb⟩ := exec_cgsPass_dots I h hz tag NE jE Vb wb hb wo ho
    st V w hV hw hhlen hne
  rw [show (forRange (ι := ι) jE fun i => dot tag ⟨hb, ho + .var i⟩ Vb (NE * .var i) wb wo NE).run
    = .seq (.loop jE fun i => (dot tag ⟨hb, ho + .var i⟩ Vb (NE * .var i) wb wo NE).run) .skip
    from rfl, exec_seq_skip, hrun₁, Option.bind_some,
    exec_run_bind I (b := gemv tag NE jE Vb 0 hb ho S 0) (fun _ => rfl)]
  obtain ⟨σ₂, Y, hrun₂, hst₂, hY⟩ := exec_cgsPass_gemv I h hz tag NE jE Vb hb S ho σ₁ V
    (fun k => dec tag (Hw k))
    (hV.of_writeBlock hst₁ fun h₁ h₂ =>
      blockDisjoint_iff.2 (Or.inl (hne (Nat.pos_of_mul_pos_right h₁) (by simpa using h₂)).2.symm))
    (fun k => ⟨Hw k, by simpa using Store.read_of_writeBlock_eq_some_of_lt hst₁ (j := k) (by simp),
      rfl⟩) (by rw [Store.shape_of_writeBlock_eq_some hst₁]; exact hsS)
    (fun e => by by_contra h; exact absurd (hVS (Nat.pos_of_ne_zero h)) (by omega))
    (fun e => by by_contra h; exact absurd (hhS (Nat.pos_of_ne_zero h)) (by omega))
  rw [hrun₂, Option.bind_some]
  exact ⟨σ₁, σ₂, Hw, Y, rfl, hst₁, hHb, hst₂, hY⟩

/-- The body of a rounded pass of `NLAlib.cgsPass`, on the store `s₀` with its two scratch
buffers `S` ($N$ cells) and `S + 1` (one cell) pushed: popping them gives the block writes of the
reduced vector and of the coefficients, with the bounds of the pass. -/
private theorem exec_cgsPass_body {u : P → ℝ} {dec : P → K → ℝ} (I : Interp P ι K C)
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem) (tag : P)
    (NE jE : IExp ℕ) (Vb wb hb : ℕ) (wo ho : IExp ℕ) (s₀ : Store P K) (st : St P K C)
    (V : Matrix (Fin NE.eval) (Fin jE.eval) ℝ) (w : Fin NE.eval → ℝ)
    (hV : HoldsDecoded s₀ dec tag Vb 0 V) (hw : ReadsDecoded s₀ dec tag wb wo.eval w)
    (hhlen : Writable s₀ tag hb ho.eval jE.eval)
    (hne : 0 < NE.eval → 0 < jE.eval → hb ≠ wb ∧ hb ≠ Vb) (hu : u tag < 1)
    (hst : st.store = (s₀.push (tag, .replicate NE.eval none)).push (tag, .replicate 1 none)) :
    ∃ (out : St P K C) (Wv : Fin NE.eval → K) (Hw : Fin jE.eval → K) (mid : Store P K),
      exec I ((forRange jE fun i =>
        dot tag ⟨hb, ho + .var i⟩ Vb (NE * .var i) wb wo NE) >>= fun _ =>
        gemv tag NE jE Vb 0 hb ho s₀.size 0 >>= fun _ =>
        ins (.lit tag ⟨s₀.size + 1, 0⟩ (-1)) >>= fun _ =>
        axpy (ι := ι) tag ⟨s₀.size + 1, 0⟩ s₀.size 0 wb wo NE).run st = some out ∧
      s₀.writeBlock tag wb wo.eval (Array.ofFn Wv) = some mid ∧
      mid.writeBlock tag hb ho.eval (Array.ofFn Hw) = some out.store.pop.pop ∧
      IsPassErr (u tag) V w (fun i => dec tag (Hw i)) (fun i => dec tag (Wv i)) := by
  set S := s₀.size
  have hwS : 0 < NE.eval → wb < S := fun h =>
    Store.lt_size_of_read_eq_some (hw ⟨0, h⟩).choose_spec.1
  have hhS : 0 < jE.eval → hb < S := hhlen.lt_size
  have hsz : st.store.size = S + 2 := by simp [hst, S]
  have hwσ : ReadsDecoded st.store dec tag wb wo.eval w := hst ▸ (hw.push _).push _
  obtain ⟨σ₁, σ₂, Hw, Y, hrun, hst₁, hHb, hst₂, hY⟩ := exec_cgsPass_dots_gemv I h hz tag NE jE Vb
    wb hb S wo ho st V w (hst ▸ (hV.push _).push _) hwσ (hst ▸ (hhlen.push _).push _) hne
    (by rw [hst, Store.getElem?_shape_push_of_lt _ (by simp [S]), Store.getElem?_shape_push_size])
    (fun h => Store.lt_size_of_read_eq_some (hV ⟨0, Nat.pos_of_mul_pos_right h⟩
      ⟨0, Nat.pos_of_mul_pos_left h⟩).choose_spec.1) hhS
    (fun _ => ins (.lit tag ⟨S + 1, 0⟩ (-1)) >>= fun _ => axpy tag ⟨S + 1, 0⟩ S 0 wb wo NE)
  rw [hrun, exec_run_bind I (b := ins (.lit tag ⟨S + 1, 0⟩ (-1))) (fun _ => rfl)]
  obtain ⟨z, hzl⟩ := h.lit_ok tag (-1) trivial
  obtain ⟨δ₀, hδ₀, hdz⟩ := h.lit_err tag (-1) z hzl
  have sz₁ := (Store.size_of_writeBlock_eq_some hst₁).trans hsz
  have sz₂ := (Store.size_of_writeBlock_eq_some hst₂).trans sz₁
  obtain ⟨s₃, hs₃⟩ := Store.exists_write_eq_some_of_getElem?_shape (b := S + 1)
    (i := (0 : IExp ℕ).eval) z (by
      rw [Store.shape_of_writeBlock_eq_some hst₂, Store.shape_of_writeBlock_eq_some hst₁, hst,
        show S + 1 = (s₀.push (tag, .replicate NE.eval none)).size by simp [S],
        Store.getElem?_shape_push_size]) (by simp)
  rw [show (ins (ι := ι) (.lit tag ⟨S + 1, 0⟩ (-1))).run = .seq (.instr (.lit tag ⟨S + 1, 0⟩ (-1)))
    .skip from rfl, exec_seq_instr_lit I hzl hs₃, exec_skip, Option.bind_some]
  obtain ⟨σ₄, Wa, hrun₄, hst₄, hW⟩ := IsRelErrSem.exec_axpy I tag
    { σ₂ with store := s₃, cnt := σ₂.cnt + I.charge (OpKind.lit tag) } h ⟨S + 1, 0⟩ S 0 wb wo NE
    (dec tag z) (fun i => if hi : i < NE.eval then dec tag (Y i) else 0)
    (fun i => if hi : i < NE.eval then w ⟨i, hi⟩ else 0) hu
    ⟨_, Store.read_of_write_eq_some hs₃, rfl⟩
    (fun i hi => ⟨Y i, by
      rw [IExp.eval_zero, Store.read_of_write_eq_some_of_ne hs₃ (Or.inl (by omega)),
        Store.read_of_writeBlock_eq_some_of_lt hst₂ (by simpa using hi)]
      simp [hi], by simp [hi]⟩)
    (fun i hi => by
      obtain ⟨x, hx, hdx⟩ := ((hwσ.of_writeBlock hst₁ fun hN hj => blockDisjoint_iff.2
        (Or.inl (hne hN (by simpa using hj)).1.symm)).of_writeBlock hst₂ fun hN _ =>
          blockDisjoint_iff.2 (Or.inl (by have := hwS hN; dsimp only; omega))) ⟨i, hi⟩
      have := hwS (by omega)
      exact ⟨x, by rw [Store.read_of_write_eq_some_of_ne hs₃ (Or.inl (by omega))]; exact hx,
        by simp [hi, hdx]⟩)
    (fun e i hi => by have := hwS (by omega); simp only at e; omega)
    (fun e i hi => by have := hwS (by omega); omega)
  have e₁ := Store.writeBlock_pop_of_lt (Store.writeBlock_pop_of_lt hst₁ fun h => by
    have := hhS (by simpa using h); omega) fun h => by
    have := hhS (by simpa using h); rw [Array.size_pop, hsz]; omega
  have e₂ : σ₂.store.pop.pop = σ₁.store.pop.pop := Store.pop_of_writeBlock_top
    (Store.writeBlock_pop_of_lt hst₂ fun _ => by omega) (by simp [sz₁])
  have e₄ := Store.writeBlock_pop_of_lt (Store.writeBlock_pop_of_lt hst₄ fun h => by
    have := hwS (by simpa using h); change wb + 1 < s₃.size
    rw [Store.size_of_write_eq_some hs₃]; omega) fun h => by
      have := hwS (by simpa using h); change wb + 1 < s₃.pop.size
      simp [Store.size_of_write_eq_some hs₃, sz₂]; omega
  change Store.writeBlock s₃.pop.pop _ _ _ _ = _ at e₄
  rw [Store.pop_of_write_top hs₃ (by omega), e₂] at e₄
  rw [show st.store.pop.pop = s₀ by simp [hst]] at e₁
  obtain ⟨mid, hm, hf⟩ := Store.writeBlock_comm e₁ e₄ fun hj hN =>
    blockDisjoint_iff.2 (Or.inl (hne (by simpa using hN) (by simpa using hj)).1)
  have harr : (List.range NE.eval).toArray.map Wa = Array.ofFn fun i : Fin NE.eval => Wa i :=
    Array.ext (by simp) fun i _ _ => by simp
  refine ⟨σ₄, fun i => Wa i, Hw, mid, hrun₄, harr ▸ hm, hf, fun η₀ hVη hM => ?_⟩
  have hW' : ∀ i : Fin NE.eval, ∃ θ δ : ℝ, |θ| ≤ roundingFactor 2 (u tag) ∧ |δ| ≤ u tag ∧
      dec tag (Wa i) = dec tag z * dec tag (Y i) * (1 + θ) + w i * (1 + δ) := fun i => by
    obtain ⟨θ, δ, hθ, hδ, he⟩ := hW i i.2
    exact ⟨θ, δ, hθ, hδ, by simpa [i.2] using he⟩
  choose θ δ hθ hδ hWe using hW'
  exact norm_sub_le_cgsPassBound_mul_norm_of_abs_sub_le (h.nonneg trivial) hVη hM hHb hY hδ₀
    hθ hδ fun i => by rw [hWe i, hdz]; push_cast; ring

/-- One rounded pass of `NLAlib.cgsPass`: its whole effect is the block write of the reduced
vector at (`wb`, `wo`), then of the coefficients at (`hb`, `ho`), with the bounds of the pass. -/
private theorem exec_cgsPass_run {u : P → ℝ} {dec : P → K → ℝ} (I : Interp P ι K C)
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem) (tag : P)
    (NE jE : IExp ℕ) (Vb wb hb : ℕ) (wo ho : IExp ℕ) (st : St P K C)
    (V : Matrix (Fin NE.eval) (Fin jE.eval) ℝ) (w : Fin NE.eval → ℝ)
    (hV : HoldsDecoded st.store dec tag Vb 0 V) (hw : ReadsDecoded st.store dec tag wb wo.eval w)
    (hhlen : Writable st.store tag hb ho.eval jE.eval)
    (hne : 0 < NE.eval → 0 < jE.eval → hb ≠ wb ∧ hb ≠ Vb) (hu : u tag < 1) :
    ∃ (out : St P K C) (Wv : Fin NE.eval → K) (Hw : Fin jE.eval → K) (mid : Store P K),
      exec I (cgsPass tag NE jE Vb wb wo hb ho).run st = some out ∧
      st.store.writeBlock tag wb wo.eval (Array.ofFn Wv) = some mid ∧
      mid.writeBlock tag hb ho.eval (Array.ofFn Hw) = some out.store ∧
      IsPassErr (u tag) V w (fun i => dec tag (Hw i)) (fun i => dec tag (Wv i)) := by
  have hrun : (cgsPass (ι := ι) tag NE jE Vb wb wo hb ho).run = .seq (.alloc tag NE fun s =>
      .alloc tag 1 fun t => ((forRange jE fun i =>
        dot tag ⟨hb, ho + .var i⟩ Vb (NE * .var i) wb wo NE) >>= fun _ =>
        gemv tag NE jE Vb 0 hb ho s 0 >>= fun _ => ins (.lit tag ⟨t, 0⟩ (-1)) >>= fun _ =>
        axpy tag ⟨t, 0⟩ s 0 wb wo NE).run) .skip := rfl
  let R : Store P K → Prop := fun s => ∃ (Wv : Fin NE.eval → K) (Hw : Fin jE.eval → K)
    (mid : Store P K), st.store.writeBlock tag wb wo.eval (Array.ofFn Wv) = some mid ∧
    mid.writeBlock tag hb ho.eval (Array.ofFn Hw) = some s ∧
    IsPassErr (u tag) V w (fun i => dec tag (Hw i)) (fun i => dec tag (Wv i))
  obtain ⟨out, hex, Wv, Hw, mid, hR⟩ : ∃ out : St P K C,
      exec I (cgsPass tag NE jE Vb wb wo hb ho).run st = some out ∧ R out.store := by
    rw [hrun, exec_seq_skip]
    refine exists_exec_alloc I tag NE _ st R fun σ₁ hσ₁ =>
      exists_exec_alloc I tag 1 _ σ₁ (fun s => R s.pop) fun σ₂ hσ₂ => ?_
    rw [show σ₁.store.size = st.store.size + 1 by simp [hσ₁]]
    obtain ⟨out, Wv, Hw, mid, hr, hR⟩ := exec_cgsPass_body I h hz tag NE jE Vb wb hb wo ho
      st.store σ₂ V w hV hw hhlen hne hu (by rw [hσ₂, hσ₁, IExp.eval_one])
    exact ⟨out, hr, Wv, Hw, mid, hR⟩
  exact ⟨out, Wv, Hw, mid, hex, hR⟩

/-- **One rounded classical Gram–Schmidt pass**: under the standard model, `NLAlib.cgsPass`
succeeds, writes only the reduced vector at (`wb`, `wo`) and the coefficients at (`hb`, `ho`),
and if $\|\mathbf{V}^{\mathsf{T}}\mathbf{V} - \mathbf{I}\|_2 \le \eta_0$ and
$(N + j + 2)u \le 1/100$, the decoded coefficients $\mathbf{h}_1$ and vector $\mathbf{w}_1$
satisfy, with $c_1$ =
`NLAlib.cgsPassBound`, <!-- value cgsPassBound N j u \eta_0 -->$2(1+\eta_0)\sqrt{j+1}\,(N+j+2)\,u$,
$\|\mathbf{h}_1 - \mathbf{V}^{\mathsf{T}}\mathbf{w}\|$,
$\|\mathbf{w} - \mathbf{V}\mathbf{h}_1 - \mathbf{w}_1\|$,
$\|\mathbf{w}_1 - (\mathbf{w} - \mathbf{V}\mathbf{V}^{\mathsf{T}}\mathbf{w})\| \le
c_1\|\mathbf{w}\|$. [Higham2002, §19.8] for the classical bounds. -/
theorem IsRelErrSem.exec_cgsPass {u : P → ℝ} {dec : P → K → ℝ} (I : Interp P ι K C)
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem) (tag : P)
    {N j : ℕ} (NE jE : IExp ℕ) (hN : NE.eval = N) (hj : jE.eval = j) (Vb wb hb : ℕ)
    (wo ho : IExp ℕ) (st : St P K C) (V : Matrix (Fin N) (Fin j) ℝ) (w : Fin N → ℝ)
    (hV : HoldsDecoded st.store dec tag Vb 0 V)
    (hw : ∀ i : Fin N, ∃ x, st.store.read tag wb (wo.eval + i) = some x ∧ dec tag x = w i)
    (hwlen : ∀ i < N, ∃ len, st.store.shape[wb]? = some (tag, len) ∧ wo.eval + i < len)
    (hhlen : ∀ i < j, ∃ len, st.store.shape[hb]? = some (tag, len) ∧ ho.eval + i < len)
    (hne : hb ≠ wb ∧ hb ≠ Vb) (hu : u tag < 1) :
    ∃ (out : St P K C) (W : Fin N → K) (Hw : Fin j → K) (mid : Store P K),
      exec I (cgsPass tag NE jE Vb wb wo hb ho).run st = some out ∧
      st.store.writeBlock tag wb wo.eval (Array.ofFn W) = some mid ∧
      mid.writeBlock tag hb ho.eval (Array.ofFn Hw) = some out.store ∧
      ∀ η₀ : ℝ, specNorm (Vᵀ * V - 1) ≤ η₀ →
        ((N + j + 2 : ℕ) : ℝ) * u tag ≤ 1 / 100 →
        ‖WithLp.toLp 2 ((fun i => dec tag (Hw i)) - Vᵀ *ᵥ w)‖ ≤
          cgsPassBound N j (u tag) η₀ * ‖WithLp.toLp 2 w‖ ∧
        ‖WithLp.toLp 2 (w - V *ᵥ (fun i => dec tag (Hw i)) - fun i => dec tag (W i))‖ ≤
          cgsPassBound N j (u tag) η₀ * ‖WithLp.toLp 2 w‖ ∧
        ‖WithLp.toLp 2 ((fun i => dec tag (W i)) - (w - V *ᵥ (Vᵀ *ᵥ w)))‖ ≤
          cgsPassBound N j (u tag) η₀ * ‖WithLp.toLp 2 w‖ := by
  subst hN hj
  clear hwlen
  obtain ⟨out, Wv, Hw, mid, hex, hmid, hfin, hbnd⟩ := exec_cgsPass_run I h hz tag NE jE Vb wb hb
    wo ho st V w hV hw hhlen (fun _ _ => hne) hu
  exact ⟨out, Wv, Hw, mid, hex, hmid, hfin, fun η₀ hV hM => hbnd η₀ hV hM⟩

/-- The $j$ rounded additions of `NLAlib.cgs2` write $\mathbf{h}_1 + \mathbf{h}_2$ to relative
error $u$ as one block write into the coefficient block. -/
private theorem exec_cgs2_add {u : P → ℝ} {dec : P → K → ℝ} (I : Interp P ι K C)
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (tag : P) (jE : IExp ℕ) (hb T : ℕ)
    (ho : IExp ℕ) (st : St P K C) (H₁ H₂ : Fin jE.eval → K)
    (hh₁ : ∀ k : Fin jE.eval, st.store.read tag hb (ho.eval + k) = some (H₁ k))
    (hh₂ : ∀ k : Fin jE.eval, st.store.read tag T k = some (H₂ k)) (hT : 0 < jE.eval → T ≠ hb) :
    ∃ (s' : St P K C) (Hs : Fin jE.eval → K), exec I (forRange jE fun i =>
        ins (ι := ι) (.bin tag .add ⟨hb, ho + .var i⟩ ⟨hb, ho + .var i⟩ ⟨T, .var i⟩)).run st =
        some s' ∧ st.store.writeBlock tag hb ho.eval (Array.ofFn Hs) = some s'.store ∧
      ∀ k : Fin jE.eval, |dec tag (Hs k) - (dec tag (H₁ k) + dec tag (H₂ k))| ≤
        u tag * |dec tag (H₁ k) + dec tag (H₂ k)| := by
  rw [show (forRange (ι := ι) jE fun i =>
      ins (.bin tag .add ⟨hb, ho + .var i⟩ ⟨hb, ho + .var i⟩ ⟨T, .var i⟩)).run = .seq (.loop jE
      fun i => (ins (.bin tag .add ⟨hb, ho + .var i⟩ ⟨hb, ho + .var i⟩ ⟨T, .var i⟩)).run) .skip
    from rfl, exec_seq_skip]
  obtain ⟨s', Hs, hrun, hst, hval⟩ := exists_exec_loop_writeBlock I (n := jE) (st := st)
    tag hb ho.eval (fun k v => ∀ hk : k < jE.eval,
      |dec tag v - (dec tag (H₁ ⟨k, hk⟩) + dec tag (H₂ ⟨k, hk⟩))| ≤
        u tag * |dec tag (H₁ ⟨k, hk⟩) + dec tag (H₂ ⟨k, hk⟩)|)
    fun k hk ys s hys _ hs => by
      obtain ⟨n, hn, hlt⟩ := Store.exists_getElem?_shape_of_read_eq_some (hh₁ ⟨k, hk⟩)
      have hx : s.store.read tag hb (ho.eval + k) = some (H₁ ⟨k, hk⟩) := by
        rw [Store.read_of_writeBlock_eq_some_of_ne hs (Or.inr (Or.inr (by omega)))]
        exact hh₁ ⟨k, hk⟩
      have hy : s.store.read tag T k = some (H₂ ⟨k, hk⟩) := by
        rw [Store.read_of_writeBlock_eq_some_of_ne hs (Or.inl (hT (by omega)))]
        exact hh₂ ⟨k, hk⟩
      obtain ⟨z, hzv⟩ := h.bin_ok tag .add (H₁ ⟨k, hk⟩) (H₂ ⟨k, hk⟩) trivial
        (fun e => by cases e) trivial
      obtain ⟨δ, hδ, hdz⟩ := h.bin_err tag .add _ _ z trivial hzv
      obtain ⟨s'', hs''⟩ := Store.exists_write_eq_some_of_getElem?_shape z
        (by rw [Store.shape_of_writeBlock_eq_some hs]; exact hn) hlt
      refine ⟨{ s with store := s'', cnt := s.cnt + I.charge (.bin tag .add) }, z, ?_, hs'',
        fun hk' => ?_⟩
      · rw [exec_seq_instr_bin I (dst := ⟨hb, ho + .var k⟩) (x := ⟨hb, ho + .var k⟩)
          (y := ⟨T, .var k⟩) hx hy hzv hs'', exec_skip]
      · simp only [BinOp.realOp] at hdz
        rw [hdz, show (dec tag (H₁ ⟨k, hk⟩) + dec tag (H₂ ⟨k, hk⟩)) * (1 + δ) -
          (dec tag (H₁ ⟨k, hk⟩) + dec tag (H₂ ⟨k, hk⟩)) =
          (dec tag (H₁ ⟨k, hk⟩) + dec tag (H₂ ⟨k, hk⟩)) * δ by ring, abs_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right hδ (abs_nonneg _)
  exact ⟨s', Hs, hrun, hst, fun k => hval k k.2⟩

/-- The error bounds of the two passes and of the summed coefficients of a rounded
`NLAlib.cgs2` of $\mathbf{w}$ against $\mathbf{V}$: the first pass gives $\mathbf{h}_1$,
$\mathbf{w}_1$, the second, of $\mathbf{w}_1$, gives $\mathbf{h}_2$, $\mathbf{w}_2$, and
$\mathbf{h}$ is $\mathbf{h}_1 + \mathbf{h}_2$ to relative error $u$. -/
private def IsCGS2Err {N j : ℕ} (u : ℝ) (V : Matrix (Fin N) (Fin j) ℝ) (w w₁ w₂ : Fin N → ℝ)
    (h₁ h₂ h : Fin j → ℝ) : Prop :=
  IsPassErr u V w h₁ w₁ ∧ IsPassErr u V w₁ h₂ w₂ ∧
    ∀ k, |h k - (h₁ k + h₂ k)| ≤ u * |h₁ k + h₂ k|

/-- The two passes and the summed coefficients of `NLAlib.cgs2` meet `NLAlib.IsOrthErr` at the
constants of `NLAlib.Computation.IsRelErrSem.isOrthRoutine_cgs2`. -/
private theorem isOrthErr_cgs2_of_passes {N j : ℕ} {V : Matrix (Fin N) (Fin j) ℝ}
    {w w₁ w₂ : Fin N → ℝ} {h₁ h₂ hs : Fin j → ℝ} {u η₀ : ℝ} (hu0 : 0 ≤ u) (hη₀ : 0 ≤ η₀)
    (hη : η₀ ≤ 1 / 100) (hM : ((N + j + 2 : ℕ) : ℝ) * u ≤ 1 / 100)
    (hc : cgsPassBound N j u η₀ ≤ 1 / 100) (P₁ : IsPassErr u V w h₁ w₁)
    (P₂ : IsPassErr u V w₁ h₂ w₂) (hsum : ∀ k, |hs k - (h₁ k + h₂ k)| ≤ u * |h₁ k + h₂ k|) :
    IsOrthErr η₀ (2 * cgsPassBound N j u η₀) (3 * cgsPassBound N j u η₀)
      (2 * (η₀ + cgsPassBound N j u η₀) ^ 2) V w hs w₂ := by
  have h4u : 4 * u ≤ cgsPassBound N j u η₀ := by
    rw [cgsPassBound_def]
    have hs1 : 1 ≤ Real.sqrt ((j : ℝ) + 1) := Real.one_le_sqrt.mpr (by
      have := Nat.cast_nonneg (α := ℝ) j; linarith)
    have hM2 : (2 : ℝ) ≤ ((N + j + 2 : ℕ) : ℝ) := by push_cast; linarith
    have h1 : (1 : ℝ) ≤ (1 + η₀) * Real.sqrt ((j : ℝ) + 1) := by nlinarith
    have h2 : 4 ≤ 2 * (1 + η₀) * Real.sqrt ((j : ℝ) + 1) * ((N + j + 2 : ℕ) : ℝ) := by nlinarith
    exact mul_le_mul_of_nonneg_right h2 hu0
  exact isOrthErr_of_two_passes hη hc hu0 h4u (fun hV => P₁ η₀ hV hM) (fun hV => P₂ η₀ hV hM)
    hsum

/-- The body of a rounded `NLAlib.cgs2`, on the store with the scratch buffer of the second
coefficients pushed: popping that buffer gives the two block writes, and the bounds of the two
passes and of the sum hold. -/
private theorem exec_cgs2_body {u : P → ℝ} {dec : P → K → ℝ} (I : Interp P ι K C)
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem) (tag : P)
    (NE jE : IExp ℕ) (Vb wb hb : ℕ) (wo ho : IExp ℕ) (st σ₀ : St P K C)
    (V : Matrix (Fin NE.eval) (Fin jE.eval) ℝ) (w : Fin NE.eval → ℝ)
    (hV : HoldsDecoded st.store dec tag Vb 0 V) (hw : ReadsDecoded st.store dec tag wb wo.eval w)
    (hhlen : Writable st.store tag hb ho.eval jE.eval)
    (hne : hb ≠ wb ∧ hb ≠ Vb ∧ wb ≠ Vb) (hu1 : u tag < 1)
    (hσ₀ : σ₀.store = st.store.push (tag, Array.replicate jE.eval none)) :
    ∃ (out : St P K C) (W₁ W₂ : Fin NE.eval → K) (H₁ H₂ Hs : Fin jE.eval → K) (mid : Store P K),
      exec I (cgsPass tag NE jE Vb wb wo hb ho >>= fun _ =>
        cgsPass tag NE jE Vb wb wo st.store.size 0 >>= fun _ => forRange jE fun i =>
          ins (.bin tag .add ⟨hb, ho + .var i⟩ ⟨hb, ho + .var i⟩
            ⟨st.store.size, .var i⟩)).run σ₀ = some out ∧
      st.store.writeBlock tag wb wo.eval (Array.ofFn W₂) = some mid ∧
      mid.writeBlock tag hb ho.eval (Array.ofFn Hs) = some out.store.pop ∧
      IsCGS2Err (u tag) V w (fun i => dec tag (W₁ i)) (fun i => dec tag (W₂ i))
        (fun i => dec tag (H₁ i)) (fun i => dec tag (H₂ i)) (fun i => dec tag (Hs i)) := by
  set T := st.store.size
  have hwlt : 0 < NE.eval → wb < T := fun h =>
    Store.lt_size_of_read_eq_some (hw ⟨0, h⟩).choose_spec.1
  have hhlt : 0 < jE.eval → hb < T := hhlen.lt_size
  have hVlt : 0 < NE.eval → 0 < jE.eval → Vb < T := fun h₁ h₂ =>
    Store.lt_size_of_read_eq_some (hV ⟨0, h₁⟩ ⟨0, h₂⟩).choose_spec.1
  rw [exec_run_bind I (b := cgsPass tag NE jE Vb wb wo hb ho) (fun _ => rfl)]
  obtain ⟨o₁, W₁, H₁, m₁, hrun₁, hm₁, ho₁, hb₁⟩ := exec_cgsPass_run I h hz tag NE jE Vb wb hb wo
    ho σ₀ V w (hσ₀ ▸ hV.push _) (hσ₀ ▸ hw.push _) (hσ₀ ▸ hhlen.push _)
    (fun _ _ => ⟨hne.1, hne.2.1⟩) hu1
  rw [hrun₁, Option.bind_some, exec_run_bind I (b := cgsPass tag NE jE Vb wb wo T 0)
    (fun _ => rfl)]
  have sz₀ : σ₀.store.size = T + 1 := by simp [hσ₀, T]
  have sz₁ := (Store.size_of_writeBlock_eq_some hm₁).trans sz₀
  have sz₂ := (Store.size_of_writeBlock_eq_some ho₁).trans sz₁
  obtain ⟨o₂, W₂, H₂, m₂, hrun₂, hm₂, ho₂, hb₂⟩ := exec_cgsPass_run I h hz tag NE jE Vb wb T wo 0
    o₁ V (fun i => dec tag (W₁ i))
    ((((hσ₀ ▸ hV.push _ : HoldsDecoded σ₀.store dec tag Vb 0 V).of_writeBlock hm₁ fun _ _ =>
      blockDisjoint_iff.2 (Or.inl hne.2.2.symm)).of_writeBlock ho₁ fun _ _ =>
        blockDisjoint_iff.2 (Or.inl hne.2.1.symm)))
    (fun i => ⟨W₁ i, by
      rw [Store.read_of_writeBlock_eq_some_of_ne ho₁ (Or.inl hne.1.symm),
        Store.read_of_writeBlock_eq_some_of_lt hm₁ (by simp)]
      simp, rfl⟩)
    (fun i hi => ⟨_, by rw [Store.shape_of_writeBlock_eq_some ho₁, Store.shape_of_writeBlock_eq_some
      hm₁, hσ₀, Store.getElem?_shape_push_size], by simpa using hi⟩)
    (fun h₁ h₂ => ⟨by have := hwlt h₁; omega, by have := hVlt h₁ h₂; omega⟩) hu1
  rw [hrun₂, Option.bind_some]
  have sz₃ := (Store.size_of_writeBlock_eq_some hm₂).trans sz₂
  obtain ⟨o₃, Hs, hrun₃, ho₃, hs₃⟩ := exec_cgs2_add I h tag jE hb T ho o₂ H₁ H₂
    (fun k => by
      have := hhlt (Fin.pos k)
      rw [Store.read_of_writeBlock_eq_some_of_ne ho₂ (Or.inl (by omega)),
        Store.read_of_writeBlock_eq_some_of_ne hm₂ (Or.inl hne.1),
        Store.read_of_writeBlock_eq_some_of_lt ho₁ (by simp)]
      simp)
    (fun k => by simpa using Store.read_of_writeBlock_eq_some_of_lt ho₂ (j := k) (by simp))
    fun h => by have := hhlt h; omega
  have e₀ := Store.writeBlock_pop_of_lt hm₁ fun h => by have := hwlt (by simpa using h); omega
  have e₁ := Store.writeBlock_pop_of_lt ho₁ fun h => by have := hhlt (by simpa using h); omega
  have e₂ := Store.writeBlock_pop_of_lt hm₂ fun h => by have := hwlt (by simpa using h); omega
  have e₃ := Store.writeBlock_pop_of_lt ho₃ fun h => by
    have := hhlt (by simpa using h); rw [Store.size_of_writeBlock_eq_some ho₂]; omega
  rw [hσ₀, Array.pop_push] at e₀
  rw [Store.pop_of_writeBlock_top ho₂ (by omega)] at e₃
  obtain ⟨m, hm, hm'⟩ := Store.writeBlock_comm e₁ e₂ fun _ _ => blockDisjoint_iff.2 (Or.inl hne.1)
  exact ⟨o₃, W₁, W₂, H₁, H₂, Hs, m, hrun₃, Store.writeBlock_writeBlock_self e₀ hm (by simp),
    Store.writeBlock_writeBlock_self hm' e₃ (by simp), hb₁, hb₂, hs₃⟩

/-- A rounded `NLAlib.cgs2` succeeds, writes only the reduced vector at (`wb`, `wo`) and the
summed coefficients at (`hb`, `ho`), and meets the bounds of its two passes and of the sum. -/
private theorem exists_exec_cgs2 {u : P → ℝ} {dec : P → K → ℝ} (I : Interp P ι K C)
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem) (tag : P)
    (NE jE : IExp ℕ) (Vb wb hb : ℕ) (wo ho : IExp ℕ) (st : St P K C)
    (V : Matrix (Fin NE.eval) (Fin jE.eval) ℝ) (w : Fin NE.eval → ℝ)
    (hV : HoldsDecoded st.store dec tag Vb 0 V) (hw : ReadsDecoded st.store dec tag wb wo.eval w)
    (hhlen : Writable st.store tag hb ho.eval jE.eval)
    (hne : hb ≠ wb ∧ hb ≠ Vb ∧ wb ≠ Vb) (hu1 : u tag < 1) :
    ∃ (out : St P K C) (W₁ W₂ : Fin NE.eval → K) (H₁ H₂ Hs : Fin jE.eval → K) (mid : Store P K),
      exec I (cgs2 tag NE jE Vb wb wo hb ho).run st = some out ∧
      st.store.writeBlock tag wb wo.eval (Array.ofFn W₂) = some mid ∧
      mid.writeBlock tag hb ho.eval (Array.ofFn Hs) = some out.store ∧
      IsCGS2Err (u tag) V w (fun i => dec tag (W₁ i)) (fun i => dec tag (W₂ i))
        (fun i => dec tag (H₁ i)) (fun i => dec tag (H₂ i)) (fun i => dec tag (Hs i)) := by
  have hrun : (cgs2 (ι := ι) tag NE jE Vb wb wo hb ho).run = .seq (.alloc tag jE fun h₂ =>
      (cgsPass tag NE jE Vb wb wo hb ho >>= fun _ => cgsPass tag NE jE Vb wb wo h₂ 0 >>= fun _ =>
        forRange jE fun i =>
          ins (.bin tag .add ⟨hb, ho + .var i⟩ ⟨hb, ho + .var i⟩ ⟨h₂, .var i⟩)).run) .skip := rfl
  let R : Store P K → Prop := fun s => ∃ (W₁ W₂ : Fin NE.eval → K) (H₁ H₂ Hs : Fin jE.eval → K)
    (mid : Store P K), st.store.writeBlock tag wb wo.eval (Array.ofFn W₂) = some mid ∧
      mid.writeBlock tag hb ho.eval (Array.ofFn Hs) = some s ∧
      IsCGS2Err (u tag) V w (fun i => dec tag (W₁ i)) (fun i => dec tag (W₂ i))
        (fun i => dec tag (H₁ i)) (fun i => dec tag (H₂ i)) (fun i => dec tag (Hs i))
  obtain ⟨out, hex, W₁, W₂, H₁, H₂, Hs, mid, hR⟩ : ∃ out : St P K C,
      exec I (cgs2 tag NE jE Vb wb wo hb ho).run st = some out ∧ R out.store := by
    rw [hrun, exec_seq_skip]
    refine exists_exec_alloc I tag jE _ st R fun σ₀ hσ₀ => ?_
    obtain ⟨o, W₁, W₂, H₁, H₂, Hs, mid, hrun', hR⟩ := exec_cgs2_body I h hz tag NE jE Vb wb hb
      wo ho st σ₀ V w hV hw hhlen hne hu1 hσ₀
    exact ⟨o, hrun', W₁, W₂, H₁, H₂, Hs, mid, hR⟩
  exact ⟨out, W₁, W₂, H₁, H₂, Hs, mid, hex, hR⟩

/-- CGS2 is a certified orthogonalization routine: under the standard model, for $0 \le \eta_0
\le 1/100$, $(N + j + 2)u \le 1/100$ and $c_1 =$ `NLAlib.cgsPassBound`, that
is <!-- value cgsPassBound N j u \eta_0 -->$2(1+\eta_0)\sqrt{j+1}\,(N+j+2)\,u \le 1/100$,
`NLAlib.cgs2` meets `NLAlib.Computation.IsOrthRoutine` at $(\eta_0, 2c_1, 3c_1, 2(\eta_0 +
c_1)^2)$ with `pre = True`. `docs/design/Krylov-LanczosReorth.md` §1.3. -/
theorem IsRelErrSem.isOrthRoutine_cgs2 {u : P → ℝ} {dec : P → K → ℝ} (I : Interp P ι K C)
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem) (tag : P)
    {N j : ℕ} (NE jE : IExp ℕ) (hN : NE.eval = N) (hj : jE.eval = j) (Vb wb hb : ℕ)
    (wo ho : IExp ℕ) {η₀ : ℝ} (hη₀ : 0 ≤ η₀) (hη : η₀ ≤ 1 / 100)
    (hu : ((N + j + 2 : ℕ) : ℝ) * u tag ≤ 1 / 100)
    (hc : cgsPassBound N j (u tag) η₀ ≤ 1 / 100) :
    IsOrthRoutine I dec tag N j η₀ (2 * cgsPassBound N j (u tag) η₀)
      (3 * cgsPassBound N j (u tag) η₀) (2 * (η₀ + cgsPassBound N j (u tag) η₀) ^ 2)
      (fun _ => True) Vb wb hb wo ho (cgs2 tag NE jE Vb wb wo hb ho) := by
  subst hN hj
  refine ⟨executionComposable_single I (fun _ => rfl), ?_⟩
  intro st V w _ hV hw _ hhlen hbw hbV hwV
  have hu1 : u tag < 1 := by
    have : (2 : ℝ) ≤ ((NE.eval + jE.eval + 2 : ℕ) : ℝ) := by push_cast; linarith
    nlinarith [h.nonneg (p := tag) trivial]
  obtain ⟨out, W₁, W₂, H₁, H₂, Hs, mid, hex, hmid, hfin, P₁, P₂, hsum⟩ := exists_exec_cgs2 I h hz
    tag NE jE Vb wb hb wo ho st V w hV hw hhlen ⟨hbw, hbV, hwV⟩ hu1
  exact ⟨out, W₂, Hs, mid, hex, hmid, hfin,
    isOrthErr_cgs2_of_passes (h.nonneg trivial) hη₀ hη hu hc P₁ P₂ hsum⟩

/-- CGS2 in exact arithmetic: under exact real arithmetic, from a state whose buffer `Vb`
holds $\mathbf{V}$ ($N \times j$) and `wb` holds $\mathbf{w}$ at `wo`, `NLAlib.cgs2` succeeds and
writes exactly $\mathbf{w}_2 = \mathbf{w}_1 - \mathbf{V}\mathbf{V}^{\mathsf{T}}\mathbf{w}_1$,
$\mathbf{w}_1 = \mathbf{w} - \mathbf{V}\mathbf{V}^{\mathsf{T}}\mathbf{w}$, at (`wb`, `wo`) and
$\mathbf{V}^{\mathsf{T}}\mathbf{w} + \mathbf{V}^{\mathsf{T}}\mathbf{w}_1$ at (`hb`, `ho`), and
nothing else, for every $\mathbf{V}$. -/
theorem exec_cgs2_exactSem (I : Interp P ι ℝ C) (hI : I.sem = exactSem) (tag : P) {N j : ℕ}
    (NE jE : IExp ℕ) (hN : NE.eval = N) (hj : jE.eval = j) (Vb wb hb : ℕ) (wo ho : IExp ℕ)
    (st : St P ℝ C) (V : Matrix (Fin N) (Fin j) ℝ) (w : Fin N → ℝ)
    (hV : Holds st.store tag Vb 0 V)
    (hw : ∀ i : Fin N, st.store.read tag wb (wo.eval + i) = some (w i))
    (hwlen : ∀ i < N, ∃ len, st.store.shape[wb]? = some (tag, len) ∧ wo.eval + i < len)
    (hhlen : ∀ i < j, ∃ len, st.store.shape[hb]? = some (tag, len) ∧ ho.eval + i < len)
    (hne : hb ≠ wb ∧ hb ≠ Vb ∧ wb ≠ Vb) :
    ∃ (out : St P ℝ C) (mid : Store P ℝ),
      exec I (cgs2 tag NE jE Vb wb wo hb ho).run st = some out ∧
      st.store.writeBlock tag wb wo.eval (Array.ofFn
        ((w - V *ᵥ (Vᵀ *ᵥ w)) - V *ᵥ (Vᵀ *ᵥ (w - V *ᵥ (Vᵀ *ᵥ w))))) = some mid ∧
      mid.writeBlock tag hb ho.eval
        (Array.ofFn (Vᵀ *ᵥ w + Vᵀ *ᵥ (w - V *ᵥ (Vᵀ *ᵥ w)))) = some out.store := by
  subst hN hj
  obtain ⟨out, W₁, W₂, H₁, H₂, Hs, mid, hex, hmid, hfin, P₁, P₂, hsum⟩ := exists_exec_cgs2 I
    (u := fun _ => 0) (hI ▸ isRelErrSem_exactSem) (hI ▸ addsZeroExactly_exactSem) tag NE jE Vb wb
    hb wo ho st V w (fun i k => ⟨_, hV i k, rfl⟩) (fun i => ⟨_, hw i, rfl⟩) hhlen hne
    zero_lt_one
  -- with `u = 0` the bounds of the passes and of the sum force the exact values
  have hexact : ∀ {n : ℕ} {x y : Fin n → ℝ}, ‖WithLp.toLp 2 (x - y)‖ ≤ 0 → x = y :=
    fun hle => sub_eq_zero.1 ((WithLp.toLp_eq_zero 2).1 (norm_le_zero_iff.1 hle))
  have hc0 : ∀ η, cgsPassBound NE.eval jE.eval 0 η = 0 := fun η => by rw [cgsPassBound_def]; ring
  obtain ⟨e₁, -, f₁⟩ := P₁ _ le_rfl (by simp)
  obtain ⟨e₂, -, f₂⟩ := P₂ _ le_rfl (by simp)
  simp only [hc0, zero_mul] at e₁ f₁ e₂ f₂
  have hW₁ : W₁ = w - V *ᵥ (Vᵀ *ᵥ w) := hexact f₁
  have hW₂ : W₂ = W₁ - V *ᵥ (Vᵀ *ᵥ W₁) := hexact f₂
  have hH₁ : H₁ = Vᵀ *ᵥ w := hexact e₁
  have hH₂ : H₂ = Vᵀ *ᵥ W₁ := hexact e₂
  have hHs : Hs = H₁ + H₂ := funext fun k => by
    have := hsum k
    simp only [zero_mul] at this
    exact sub_eq_zero.1 (abs_nonpos_iff.1 this)
  rw [hW₂, hW₁] at hmid
  rw [hHs, hH₁, hH₂, hW₁] at hfin
  exact ⟨out, mid, hex, hmid, hfin⟩

end NLAlib.Computation
