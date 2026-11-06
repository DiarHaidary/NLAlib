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
`NLAlib.norm_sub_le_cgsPassBound_mul_norm_of_abs_sub_le` with $c_1 =$ `NLAlib.cgsPassBound`.
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

/-- A store of the shape of `s` that holds `a` and `c` in two blocks of distinct buffers and reads
as `s` outside them is the result of the two block writes. -/
private theorem eq_of_read_writeBlock_writeBlock {s s' m f : Store P K} {p : P}
    {b₁ b₂ o₁ o₂ : ℕ} {a c : Array K} (hb : b₁ ≠ b₂) (hsh : s'.shape = s.shape)
    (hA : ∀ i < a.size, s'.read p b₁ (o₁ + i) = a[i]?)
    (hC : ∀ i < c.size, s'.read p b₂ (o₂ + i) = c[i]?)
    (hrest : ∀ q b i, ¬(b = b₁ ∧ o₁ ≤ i ∧ i < o₁ + a.size) →
      ¬(b = b₂ ∧ o₂ ≤ i ∧ i < o₂ + c.size) → s'.read q b i = s.read q b i)
    (hm : s.writeBlock p b₁ o₁ a = some m) (hf : m.writeBlock p b₂ o₂ c = some f) : s' = f := by
  have hshm := Store.shape_of_writeBlock_eq_some hm
  have hshf := Store.shape_of_writeBlock_eq_some hf
  refine Store.ext_of_shape_eq (by rw [hsh, hshf, hshm]) fun q b i => ?_
  by_cases h₁ : b = b₁ ∧ o₁ ≤ i ∧ i < o₁ + a.size
  · obtain ⟨rfl, hi, hi'⟩ := h₁
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi
    have hk : k < a.size := by omega
    rw [Store.read_of_writeBlock_eq_some_of_ne hf (Or.inl hb)]
    by_cases hq : q = p
    · subst hq
      rw [hA k hk, Store.read_of_writeBlock_eq_some_of_lt hm hk]
    · obtain ⟨n, hn, -⟩ := Store.exists_getElem?_shape_of_writeBlock_eq_some hm hk
      rw [Store.read_eq_none_of_getElem?_shape_of_ne (hsh ▸ hn) hq,
        Store.read_eq_none_of_getElem?_shape_of_ne (hshm ▸ hn) hq]
  by_cases h₂ : b = b₂ ∧ o₂ ≤ i ∧ i < o₂ + c.size
  · obtain ⟨rfl, hi, hi'⟩ := h₂
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi
    have hk : k < c.size := by omega
    by_cases hq : q = p
    · subst hq
      rw [hC k hk, Store.read_of_writeBlock_eq_some_of_lt hf hk]
    · obtain ⟨n, hn, -⟩ := Store.exists_getElem?_shape_of_writeBlock_eq_some hf hk
      rw [Store.read_eq_none_of_getElem?_shape_of_ne (hsh ▸ hshm ▸ hn) hq,
        Store.read_eq_none_of_getElem?_shape_of_ne (hshf ▸ hn) hq]
  have hout : ∀ {bb oo L : ℕ}, ¬(b = bb ∧ oo ≤ i ∧ i < oo + L) → b ≠ bb ∨ i < oo ∨ oo + L ≤ i :=
    fun {bb oo L} h => by
      by_cases hbb : b = bb
      · exact Or.inr (by omega)
      · exact Or.inl hbb
  rw [hrest q b i h₁ h₂, Store.read_of_writeBlock_eq_some_of_ne hf (hout h₂),
    Store.read_of_writeBlock_eq_some_of_ne hm (hout h₁)]

/-- An allocation whose body succeeds from the store with the fresh buffer pushed succeeds, with
the buffer popped. -/
private theorem exists_exec_alloc (I : Interp P ι K C) (p : P) (len : IExp ℕ)
    (body : ℕ → Stmt P ι ℕ ℕ) (st : St P K C) (Q : Store P K → Prop)
    (h : ∀ σ : St P K C, σ.store = st.store.push (p, Array.replicate len.eval none) →
      ∃ out, exec I (body st.store.size) σ = some out ∧ Q out.store.pop) :
    ∃ out, exec I (.alloc p len body) st = some out ∧ Q out.store := by
  obtain ⟨out, h₁, h₂⟩ := h (st.allocate p len.eval (I.width p)) rfl
  exact ⟨_, exec_alloc_of_exec_eq_some I p len body st out h₁, h₂⟩

/-- A loop whose $k$-th body writes one word satisfying `Q k` into cell $o + k$ of buffer `b`
and nothing else, from any store that reads as the start outside the cells written so far. -/
private theorem exists_exec_loop_write (I : Interp P ι K C) {n : IExp ℕ}
    {body : ℕ → Stmt P ι ℕ ℕ} {st : St P K C} (p : P) (b o : ℕ) (Q : ℕ → K → Prop)
    (hstep : ∀ k < n.eval, ∀ s : St P K C, s.store.shape = st.store.shape →
      (∀ q b' i, ¬(b' = b ∧ o ≤ i ∧ i < o + k) → s.store.read q b' i = st.store.read q b' i) →
      ∃ s' v, exec I (body k) s = some s' ∧ s.store.write p b (o + k) v = some s'.store ∧
        Q k v) :
    ∃ s', exec I (.loop n body) st = some s' ∧ s'.store.shape = st.store.shape ∧
      (∀ k < n.eval, ∃ v, s'.store.read p b (o + k) = some v ∧ Q k v) ∧
      ∀ q b' i, ¬(b' = b ∧ o ≤ i ∧ i < o + n.eval) →
        s'.store.read q b' i = st.store.read q b' i := by
  refine exists_exec_loop_eq_some_of_forall I (fun k s => s.store.shape = st.store.shape ∧
    (∀ k' < k, ∃ v, s.store.read p b (o + k') = some v ∧ Q k' v) ∧
    ∀ q b' i, ¬(b' = b ∧ o ≤ i ∧ i < o + k) → s.store.read q b' i = st.store.read q b' i)
    ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ => rfl⟩ ?_
  rintro k hk s ⟨hsh, hvals, hfr⟩
  obtain ⟨s', v, hrun, hw, hQ⟩ := hstep k hk s hsh hfr
  refine ⟨s', hrun, (Store.shape_of_write_eq_some hw).trans hsh, fun k' hk' => ?_,
    fun q b' i hi => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hk' with hk' | rfl
    · rw [Store.read_of_write_eq_some_of_ne hw (Or.inr (by omega))]
      exact hvals k' hk'
    · exact ⟨v, Store.read_of_write_eq_some hw, hQ⟩
  · have hne : b' ≠ b ∨ i ≠ o + k := by
      by_cases hb : b' = b
      · exact Or.inr fun h => hi ⟨hb, by omega, by omega⟩
      · exact Or.inl hb
    rw [Store.read_of_write_eq_some_of_ne hw hne,
      hfr q b' i fun h => hi ⟨h.1, h.2.1, by omega⟩]

/-- The $j$ rounded dots of a pass write coefficients within the partial-sum bound of
$\mathbf{V}^{\mathsf{T}}\mathbf{w}$ into the coefficient block and nothing else. -/
private theorem exec_cgsPass_dots {u : P → ℝ} {dec : P → K → ℝ} (I : Interp P ι K C)
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem) (tag : P)
    (NE jE : IExp ℕ) (Vb wb hb : ℕ) (wo ho : IExp ℕ) (st : St P K C)
    (V : Matrix (Fin NE.eval) (Fin jE.eval) ℝ) (w : Fin NE.eval → ℝ)
    (hV : HoldsDecoded st.store dec tag Vb 0 V)
    (hw : ∀ i : Fin NE.eval, ∃ x, st.store.read tag wb (wo.eval + i) = some x ∧ dec tag x = w i)
    (hhlen : ∀ i < jE.eval, ∃ len, st.store.shape[hb]? = some (tag, len) ∧ ho.eval + i < len)
    (hne : 0 < NE.eval → 0 < jE.eval → hb ≠ wb ∧ hb ≠ Vb) :
    ∃ s', exec I (.loop jE fun i =>
        (dot tag ⟨hb, ho + .var i⟩ Vb (NE * .var i) wb wo NE).run) st = some s' ∧
      s'.store.shape = st.store.shape ∧
      (∀ k : Fin jE.eval, ∃ x, s'.store.read tag hb (ho.eval + k) = some x ∧
        |dec tag x - (Vᵀ *ᵥ w) k| ≤ (1 + u tag) ^ NE.eval * u tag *
          ((Vᵀ.map abs *ᵥ fun r => |w r|) k + ∑ r ∈ Finset.range NE.eval,
            |(Vᵀ *ᵥ fun t : Fin NE.eval => if (t : ℕ) < r + 1 then w t else 0) k|)) ∧
      ∀ q b i, ¬(b = hb ∧ ho.eval ≤ i ∧ i < ho.eval + jE.eval) →
        s'.store.read q b i = st.store.read q b i := by
  have hA := h.isArithErrSem fun _ => trivial
  obtain ⟨s', hrun, hsh, hval, hfr⟩ := exists_exec_loop_write I (n := jE)
    (body := fun i => (dot tag ⟨hb, ho + .var i⟩ Vb (NE * .var i) wb wo NE).run) (st := st)
    tag hb ho.eval (fun k x => ∀ hk : k < jE.eval, |dec tag x - (Vᵀ *ᵥ w) ⟨k, hk⟩| ≤
      (1 + u tag) ^ NE.eval * u tag * ((Vᵀ.map abs *ᵥ fun r => |w r|) ⟨k, hk⟩ +
        ∑ r ∈ Finset.range NE.eval,
          |(Vᵀ *ᵥ fun t : Fin NE.eval => if (t : ℕ) < r + 1 then w t else 0) ⟨k, hk⟩|))
    fun k hk s hs hs' => by
      have hrd : ∀ {b i}, b ≠ hb → s.store.read tag b i = st.store.read tag b i :=
        fun hb' => hs' _ _ _ fun h => hb' h.1
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
          exact ⟨z0, Store.exists_write_eq_some_of_getElem?_shape z0 (hs ▸ hlen) hlt⟩)
        (fun _ _ _ _ => ⟨trivial, fun _ _ => trivial⟩)
      refine ⟨st', x, hrun, hst, fun hk' => ?_⟩
      rw [hx]
      exact IsDotTrace.abs_sub_mulVec_le Vᵀ w ⟨k, hk'⟩ (fun r hr => by simp [hr])
        (fun r hr => by simp [hr]) htr (h.nonneg trivial)
  exact ⟨s', hrun, hsh, fun k => by
    obtain ⟨x, hx, hb⟩ := hval k k.2
    exact ⟨x, hx, hb k.2⟩, hfr⟩

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

/-- The dots and the `gemv` of a rounded pass, followed by `f`: the run of `f` from the state
where the coefficients are written at (`hb`, `ho`) and the product into the scratch buffer `S`,
with their partial-product bounds. -/
private theorem exec_cgsPass_dots_gemv {u : P → ℝ} {dec : P → K → ℝ} (I : Interp P ι K C)
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem) (tag : P)
    (NE jE : IExp ℕ) (Vb wb hb S : ℕ) (wo ho : IExp ℕ) (st : St P K C)
    (V : Matrix (Fin NE.eval) (Fin jE.eval) ℝ) (w : Fin NE.eval → ℝ)
    (hV : HoldsDecoded st.store dec tag Vb 0 V)
    (hw : ∀ i : Fin NE.eval, ∃ x, st.store.read tag wb (wo.eval + i) = some x ∧ dec tag x = w i)
    (hhlen : ∀ i < jE.eval, ∃ len, st.store.shape[hb]? = some (tag, len) ∧ ho.eval + i < len)
    (hne : 0 < NE.eval → 0 < jE.eval → hb ≠ wb ∧ hb ≠ Vb)
    (hsS : st.store.shape[S]? = some (tag, NE.eval)) (hVS : 0 < NE.eval * jE.eval → Vb < S)
    (hhS : 0 < jE.eval → hb < S) (f : Unit → Builder P ι ℕ ℕ Unit) :
    ∃ (σ₁ σ₂ : St P K C) (Hw : Fin jE.eval → K) (Y : ℕ → K),
      exec I ((forRange jE fun i => dot tag ⟨hb, ho + .var i⟩ Vb (NE * .var i) wb wo NE) >>=
        fun _ => gemv tag NE jE Vb 0 hb ho S 0 >>= f).run st = exec I (f ()).run σ₂ ∧
      σ₁.store.shape = st.store.shape ∧
      (∀ k : Fin jE.eval, σ₁.store.read tag hb (ho.eval + k) = some (Hw k)) ∧
      (∀ k : Fin jE.eval, |dec tag (Hw k) - (Vᵀ *ᵥ w) k| ≤ (1 + u tag) ^ NE.eval * u tag *
        ((Vᵀ.map abs *ᵥ fun r => |w r|) k + ∑ r ∈ Finset.range NE.eval,
          |(Vᵀ *ᵥ fun t : Fin NE.eval => if (t : ℕ) < r + 1 then w t else 0) k|)) ∧
      (∀ q b i, ¬(b = hb ∧ ho.eval ≤ i ∧ i < ho.eval + jE.eval) →
        σ₁.store.read q b i = st.store.read q b i) ∧
      σ₁.store.writeBlock tag S 0 ((List.range NE.eval).toArray.map Y) = some σ₂.store ∧
      ∀ i : Fin NE.eval, |dec tag (Y i) - (V *ᵥ fun k => dec tag (Hw k)) i| ≤
        (1 + u tag) ^ jE.eval * u tag * ((V.map abs *ᵥ fun r => |dec tag (Hw r)|) i +
          ∑ r ∈ Finset.range jE.eval, |(V *ᵥ fun t : Fin jE.eval =>
            if (t : ℕ) < r + 1 then dec tag (Hw t) else 0) i|) := by
  rw [exec_run_bind I
    (b := forRange jE fun i => dot tag ⟨hb, ho + .var i⟩ Vb (NE * .var i) wb wo NE) (fun _ => rfl)]
  obtain ⟨σ₁, hrun₁, hsh₁, hh₁, hfr₁⟩ := exec_cgsPass_dots I h hz tag NE jE Vb wb hb wo ho
    st V w hV hw hhlen hne
  choose Hw hHw hHb using hh₁
  rw [show (forRange (ι := ι) jE fun i => dot tag ⟨hb, ho + .var i⟩ Vb (NE * .var i) wb wo NE).run
    = .seq (.loop jE fun i => (dot tag ⟨hb, ho + .var i⟩ Vb (NE * .var i) wb wo NE).run) .skip
    from rfl, exec_seq_skip, hrun₁, Option.bind_some,
    exec_run_bind I (b := gemv tag NE jE Vb 0 hb ho S 0) (fun _ => rfl)]
  have hrd₁ : ∀ {q b i}, b ≠ hb → σ₁.store.read q b i = st.store.read q b i :=
    fun hb' => hfr₁ _ _ _ fun h => hb' h.1
  obtain ⟨σ₂, Y, hrun₂, hst₂, hY⟩ := exec_cgsPass_gemv I h hz tag NE jE Vb hb S ho σ₁ V
    (fun k => dec tag (Hw k))
    (fun i k => by
      obtain ⟨x, hx, hdx⟩ := hV i k
      exact ⟨x, by rw [hrd₁ (Ne.symm (hne (Fin.pos i) (Fin.pos k)).2)]; exact hx, hdx⟩)
    (fun k => ⟨Hw k, hHw k, rfl⟩) (hsh₁ ▸ hsS)
    (fun e => by by_contra h; exact absurd (hVS (Nat.pos_of_ne_zero h)) (by omega))
    (fun e => by by_contra h; exact absurd (hhS (Nat.pos_of_ne_zero h)) (by omega))
  rw [hrun₂, Option.bind_some]
  exact ⟨σ₁, σ₂, Hw, Y, rfl, hsh₁, hHw, hHb, hfr₁, hst₂, hY⟩

/-- The body of a rounded pass of `NLAlib.cgsPass`, on a store with its two scratch buffers
`S` ($N$ cells) and `S + 1` (one cell) allocated, as a frame, with the bounds of the pass. -/
private theorem exec_cgsPass_body {u : P → ℝ} {dec : P → K → ℝ} (I : Interp P ι K C)
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem) (tag : P)
    (NE jE : IExp ℕ) (Vb wb hb S : ℕ) (wo ho : IExp ℕ) (st : St P K C)
    (V : Matrix (Fin NE.eval) (Fin jE.eval) ℝ) (w : Fin NE.eval → ℝ)
    (hV : HoldsDecoded st.store dec tag Vb 0 V)
    (hw : ∀ i : Fin NE.eval, ∃ x, st.store.read tag wb (wo.eval + i) = some x ∧ dec tag x = w i)
    (hhlen : ∀ i < jE.eval, ∃ len, st.store.shape[hb]? = some (tag, len) ∧ ho.eval + i < len)
    (hne : 0 < NE.eval → 0 < jE.eval → hb ≠ wb ∧ hb ≠ Vb)
    (hsS : st.store.shape[S]? = some (tag, NE.eval))
    (htS : st.store.shape[S + 1]? = some (tag, 1)) (hwS : 0 < NE.eval → wb < S)
    (hVS : 0 < NE.eval * jE.eval → Vb < S) (hhS : 0 < jE.eval → hb < S) (hu : u tag < 1) :
    ∃ (out : St P K C) (Wv : Fin NE.eval → K) (Hw : Fin jE.eval → K),
      exec I ((forRange jE fun i =>
        dot tag ⟨hb, ho + .var i⟩ Vb (NE * .var i) wb wo NE) >>= fun _ =>
        gemv tag NE jE Vb 0 hb ho S 0 >>= fun _ => ins (.lit tag ⟨S + 1, 0⟩ (-1)) >>= fun _ =>
        axpy (ι := ι) tag ⟨S + 1, 0⟩ S 0 wb wo NE).run st = some out ∧
      out.store.shape = st.store.shape ∧
      (∀ i : Fin NE.eval, out.store.read tag wb (wo.eval + i) = some (Wv i)) ∧
      (∀ k : Fin jE.eval, out.store.read tag hb (ho.eval + k) = some (Hw k)) ∧
      (∀ q b i, b ≠ S → b ≠ S + 1 → ¬(b = wb ∧ wo.eval ≤ i ∧ i < wo.eval + NE.eval) →
        ¬(b = hb ∧ ho.eval ≤ i ∧ i < ho.eval + jE.eval) →
        out.store.read q b i = st.store.read q b i) ∧
      IsPassErr (u tag) V w (fun i => dec tag (Hw i)) (fun i => dec tag (Wv i)) := by
  obtain ⟨σ₁, σ₂, Hw, Y, hrun, hsh₁, hHw, hHb, hfr₁, hst₂, hY⟩ := exec_cgsPass_dots_gemv I h hz
    tag NE jE Vb wb hb S wo ho st V w hV hw hhlen hne hsS hVS hhS
    (fun _ => ins (.lit tag ⟨S + 1, 0⟩ (-1)) >>= fun _ => axpy tag ⟨S + 1, 0⟩ S 0 wb wo NE)
  rw [hrun, exec_run_bind I (b := ins (.lit tag ⟨S + 1, 0⟩ (-1))) (fun _ => rfl)]
  obtain ⟨z, hzl⟩ := h.lit_ok tag (-1) trivial
  obtain ⟨δ₀, hδ₀, hdz⟩ := h.lit_err tag (-1) z hzl
  obtain ⟨s₃, hs₃⟩ := Store.exists_write_eq_some_of_getElem?_shape z
    ((Store.shape_of_writeBlock_eq_some hst₂).trans hsh₁ ▸ htS) Nat.one_pos
  rw [show (ins (ι := ι) (.lit tag ⟨S + 1, 0⟩ (-1))).run = .seq (.instr (.lit tag ⟨S + 1, 0⟩ (-1)))
    .skip from rfl, exec_seq_instr_lit I hzl hs₃, exec_skip, Option.bind_some]
  have hrd₃ : ∀ {q b i}, b ≠ S + 1 → b ≠ S → s₃.read q b i = σ₁.store.read q b i := fun h₁ h₂ => by
    rw [Store.read_of_write_eq_some_of_ne hs₃ (Or.inl h₁),
      Store.read_of_writeBlock_eq_some_of_ne hst₂ (Or.inl h₂)]
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
      obtain ⟨x, hx, hdx⟩ := hw ⟨i, hi⟩
      have := hwS (by omega)
      refine ⟨x, ?_, by simp [hi, hdx]⟩
      rw [hrd₃ (b := wb) (by omega) (by omega), hfr₁ _ _ _ fun h => by
        rcases Nat.eq_zero_or_pos jE.eval with hj | hj
        · omega
        · exact (hne (by omega) hj).1 h.1.symm]
      exact hx)
    (fun e i hi => by have := hwS (by omega); simp only at e; omega)
    (fun e i hi => by have := hwS (by omega); omega)
  refine ⟨σ₄, fun i => Wa i, Hw, hrun₄, ?_, fun i => ?_, fun k => ?_,
    fun q b i hbS hbS₁ hwb hhb => ?_, fun η₀ hVη hM => ?_⟩
  · rw [Store.shape_of_writeBlock_eq_some hst₄, Store.shape_of_write_eq_some hs₃,
      Store.shape_of_writeBlock_eq_some hst₂, hsh₁]
  · rw [Store.read_of_writeBlock_eq_some_of_lt hst₄ (by simp)]
    simp
  · have := hhS (Fin.pos k)
    rw [Store.read_of_writeBlock_eq_some_of_ne hst₄ (by
        rcases Nat.eq_zero_or_pos NE.eval with hN | hN
        · exact Or.inr (by
            simp only [Array.size_map, List.size_toArray, List.length_range, hN]; omega)
        · exact Or.inl (hne hN (Fin.pos k)).1), hrd₃ (by omega) (by omega), hHw k]
  · rw [Store.read_of_writeBlock_eq_some_of_ne hst₄ (by
        by_cases h : b = wb
        · exact Or.inr (by simp only [Array.size_map, List.size_toArray, List.length_range]; omega)
        · exact Or.inl h), hrd₃ hbS₁ hbS, hfr₁ q b i hhb]
  · have hW' : ∀ i : Fin NE.eval, ∃ θ δ : ℝ, |θ| ≤ roundingFactor 2 (u tag) ∧ |δ| ≤ u tag ∧
        dec tag (Wa i) = dec tag z * dec tag (Y i) * (1 + θ) + w i * (1 + δ) := fun i => by
      obtain ⟨θ, δ, hθ, hδ, he⟩ := hW i i.2
      exact ⟨θ, δ, hθ, hδ, by simpa [i.2] using he⟩
    choose θ δ hθ hδ hWe using hW'
    exact norm_sub_le_cgsPassBound_mul_norm_of_abs_sub_le (h.nonneg trivial) hVη hM hHb hY hδ₀
      hθ hδ fun i => by rw [hWe i, hdz]; push_cast; ring

/-- One rounded pass of `NLAlib.cgsPass`, as a frame: the reduced vector at (`wb`, `wo`), the
coefficients at (`hb`, `ho`), every other cell and the shape kept, with the bounds of the pass. -/
private theorem exec_cgsPass_frame {u : P → ℝ} {dec : P → K → ℝ} (I : Interp P ι K C)
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem) (tag : P)
    (NE jE : IExp ℕ) (Vb wb hb : ℕ) (wo ho : IExp ℕ) (st : St P K C)
    (V : Matrix (Fin NE.eval) (Fin jE.eval) ℝ) (w : Fin NE.eval → ℝ)
    (hV : HoldsDecoded st.store dec tag Vb 0 V)
    (hw : ∀ i : Fin NE.eval, ∃ x, st.store.read tag wb (wo.eval + i) = some x ∧ dec tag x = w i)
    (hhlen : ∀ i < jE.eval, ∃ len, st.store.shape[hb]? = some (tag, len) ∧ ho.eval + i < len)
    (hne : 0 < NE.eval → 0 < jE.eval → hb ≠ wb ∧ hb ≠ Vb) (hu : u tag < 1) :
    ∃ (out : St P K C) (Wv : Fin NE.eval → K) (Hw : Fin jE.eval → K),
      exec I (cgsPass tag NE jE Vb wb wo hb ho).run st = some out ∧
      out.store.shape = st.store.shape ∧
      (∀ i : Fin NE.eval, out.store.read tag wb (wo.eval + i) = some (Wv i)) ∧
      (∀ k : Fin jE.eval, out.store.read tag hb (ho.eval + k) = some (Hw k)) ∧
      (∀ q b i, ¬(b = wb ∧ wo.eval ≤ i ∧ i < wo.eval + NE.eval) →
        ¬(b = hb ∧ ho.eval ≤ i ∧ i < ho.eval + jE.eval) →
        out.store.read q b i = st.store.read q b i) ∧
      IsPassErr (u tag) V w (fun i => dec tag (Hw i)) (fun i => dec tag (Wv i)) := by
  have hrun : (cgsPass (ι := ι) tag NE jE Vb wb wo hb ho).run = .seq (.alloc tag NE fun s =>
      .alloc tag 1 fun t => ((forRange jE fun i =>
        dot tag ⟨hb, ho + .var i⟩ Vb (NE * .var i) wb wo NE) >>= fun _ =>
        gemv tag NE jE Vb 0 hb ho s 0 >>= fun _ => ins (.lit tag ⟨t, 0⟩ (-1)) >>= fun _ =>
        axpy tag ⟨t, 0⟩ s 0 wb wo NE).run) .skip := rfl
  set S := st.store.size
  have hlt : ∀ {b}, (∃ n, st.store.shape[b]? = some n) → b < S := fun ⟨n, hn⟩ => by
    simpa [Store.size_shape] using (Array.getElem?_eq_some_iff.mp hn).1
  have hVlt : ∀ (i : Fin NE.eval) (k : Fin jE.eval), Vb < S := fun i k =>
    let ⟨_, hx, _⟩ := hV i k
    Store.lt_size_of_read_eq_some hx
  have hwlt : ∀ i : Fin NE.eval, wb < S := fun i =>
    let ⟨_, hx, _⟩ := hw i
    Store.lt_size_of_read_eq_some hx
  have hhlt : ∀ k < jE.eval, hb < S := fun k hk =>
    let ⟨len, hl, _⟩ := hhlen k hk
    hlt ⟨_, hl⟩
  let R : Store P K → Prop := fun s => ∃ (Wv : Fin NE.eval → K) (Hw : Fin jE.eval → K),
    s.shape = st.store.shape ∧
    (∀ i : Fin NE.eval, s.read tag wb (wo.eval + i) = some (Wv i)) ∧
    (∀ k : Fin jE.eval, s.read tag hb (ho.eval + k) = some (Hw k)) ∧
    (∀ q b i, ¬(b = wb ∧ wo.eval ≤ i ∧ i < wo.eval + NE.eval) →
      ¬(b = hb ∧ ho.eval ≤ i ∧ i < ho.eval + jE.eval) → s.read q b i = st.store.read q b i) ∧
    IsPassErr (u tag) V w (fun i => dec tag (Hw i)) (fun i => dec tag (Wv i))
  obtain ⟨out, hex, Wv, Hw, hR⟩ : ∃ out : St P K C,
      exec I (cgsPass tag NE jE Vb wb wo hb ho).run st = some out ∧ R out.store := by
    rw [hrun, exec_seq_skip]
    refine exists_exec_alloc I tag NE _ st R fun σ₁ hσ₁ => ?_
    refine exists_exec_alloc I tag 1 _ σ₁ (fun s => R s.pop) fun σ₂ hσ₂ => ?_
    have hsz₁ : σ₁.store.size = S + 1 := by rw [hσ₁, Array.size_push]
    rw [hsz₁]
    have hrd₂ : ∀ {q b i}, b < S → σ₂.store.read q b i = st.store.read q b i := fun hb => by
      rw [hσ₂, Store.read_push_of_lt (by omega), hσ₁, Store.read_push_of_lt hb]
    have hsh₂ : ∀ {b}, b < S → σ₂.store.shape[b]? = st.store.shape[b]? := fun hb => by
      rw [hσ₂, Store.getElem?_shape_push_of_lt _ (by omega), hσ₁,
        Store.getElem?_shape_push_of_lt _ hb]
    obtain ⟨σ, Wv, Hw, hrunσ, hshσ, hwσ, hhσ, hfrσ, hbndσ⟩ := exec_cgsPass_body I h hz tag
      NE jE Vb wb hb S wo ho σ₂ V w
      (fun i k => by
        obtain ⟨x, hx, hdx⟩ := hV i k
        exact ⟨x, by rw [hrd₂ (hVlt i k)]; exact hx, hdx⟩)
      (fun i => by
        obtain ⟨x, hx, hdx⟩ := hw i
        exact ⟨x, by rw [hrd₂ (hwlt i)]; exact hx, hdx⟩)
      (fun i hi => by rw [hsh₂ (hhlt i hi)]; exact hhlen i hi) hne
      (by rw [hσ₂, Store.getElem?_shape_push_of_lt _ (by omega), hσ₁,
        Store.getElem?_shape_push_size])
      (by rw [hσ₂, ← hsz₁, Store.getElem?_shape_push_size, IExp.eval_one])
      (fun h => hwlt ⟨0, h⟩) (fun h => hVlt ⟨0, Nat.pos_of_mul_pos_right h⟩
        ⟨0, Nat.pos_of_mul_pos_left h⟩) (fun h => hhlt 0 h) hu
    have hszσ : σ.store.size = S + 2 := by
      rw [← Store.size_shape, hshσ, Store.size_shape, hσ₂, Array.size_push, hsz₁]
    have hpop : ∀ {q b i}, b < S → Store.read σ.store.pop.pop q b i = σ.store.read q b i :=
      fun hb => by
        rw [Store.read_pop_of_lt (by simp [hszσ]; omega), Store.read_pop_of_lt (by omega)]
    refine ⟨σ, hrunσ, Wv, Hw, ?_, fun i => (hpop (hwlt i)).trans (hwσ i),
      fun k => (hpop (hhlt k k.2)).trans (hhσ k), fun q b i h₁ h₂ => ?_, hbndσ⟩
    · rw [Store.shape_pop, Store.shape_pop, hshσ, hσ₂, hσ₁]
      simp [Store.shape]
    · by_cases hbS : b < S
      · rw [hpop hbS, hfrσ q b i (by omega) (by omega) h₁ h₂, hrd₂ hbS]
      · rw [Store.read_eq_none_of_size_le (by simp [hszσ]; omega),
          Store.read_eq_none_of_size_le (by omega)]
  exact ⟨out, Wv, Hw, hex, hR⟩

/-- **One rounded classical Gram–Schmidt pass**: under the standard model, `NLAlib.cgsPass`
succeeds, writes only the reduced vector at (`wb`, `wo`) and the coefficients at (`hb`, `ho`),
and if $\|\mathbf{V}^{\mathsf{T}}\mathbf{V} - \mathbf{I}\|_2 \le \eta_0 \le 1/100$ and
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
    (hne : hb ≠ wb ∧ hb ≠ Vb ∧ wb ≠ Vb) (hu : u tag < 1) :
    ∃ (out : St P K C) (W : Fin N → K) (Hw : Fin j → K) (mid : Store P K),
      exec I (cgsPass tag NE jE Vb wb wo hb ho).run st = some out ∧
      st.store.writeBlock tag wb wo.eval (Array.ofFn W) = some mid ∧
      mid.writeBlock tag hb ho.eval (Array.ofFn Hw) = some out.store ∧
      ∀ η₀ : ℝ, specNorm (Vᵀ * V - 1) ≤ η₀ → η₀ ≤ 1 / 100 →
        ((N + j + 2 : ℕ) : ℝ) * u tag ≤ 1 / 100 →
        ‖WithLp.toLp 2 ((fun i => dec tag (Hw i)) - Vᵀ *ᵥ w)‖ ≤
          cgsPassBound N j (u tag) η₀ * ‖WithLp.toLp 2 w‖ ∧
        ‖WithLp.toLp 2 (w - V *ᵥ (fun i => dec tag (Hw i)) - fun i => dec tag (W i))‖ ≤
          cgsPassBound N j (u tag) η₀ * ‖WithLp.toLp 2 w‖ ∧
        ‖WithLp.toLp 2 ((fun i => dec tag (W i)) - (w - V *ᵥ (Vᵀ *ᵥ w)))‖ ≤
          cgsPassBound N j (u tag) η₀ * ‖WithLp.toLp 2 w‖ := by
  subst hN hj
  obtain ⟨out, Wv, Hw, hex, hsh, hwr, hhr, hfr, hbnd⟩ := exec_cgsPass_frame I h hz tag NE jE
    Vb wb hb wo ho st V w hV hw hhlen (fun _ _ => ⟨hne.1, hne.2.1⟩) hu
  obtain ⟨mid, hmid⟩ := Store.exists_writeBlock_eq_some_of_getElem?_shape (s := st.store)
    (p := tag) (b := wb) (off := wo.eval) (xs := Array.ofFn Wv)
    fun i hi => hwlen i (by simpa using hi)
  obtain ⟨fin, hfin⟩ := Store.exists_writeBlock_eq_some_of_getElem?_shape (s := mid) (p := tag)
    (b := hb) (off := ho.eval) (xs := Array.ofFn Hw) fun i hi => by
      rw [Store.shape_of_writeBlock_eq_some hmid]; exact hhlen i (by simpa using hi)
  have heq : out.store = fin := by
    refine eq_of_read_writeBlock_writeBlock (Ne.symm hne.1) hsh (fun i hi => ?_)
      (fun k hk => ?_) (fun q b i h₁ h₂ => ?_) hmid hfin
    · rw [Array.size_ofFn] at hi
      rw [hwr ⟨i, hi⟩]
      simp [hi]
    · rw [Array.size_ofFn] at hk
      rw [hhr ⟨k, hk⟩]
      simp [hk]
    · simp only [Array.size_ofFn] at h₁ h₂
      exact hfr q b i h₁ h₂
  exact ⟨out, Wv, Hw, mid, hex, hmid, heq ▸ hfin, fun η₀ hV _ hM => hbnd η₀ hV hM⟩

/-- The $j$ rounded additions of `NLAlib.cgs2` write $\mathbf{h}_1 + \mathbf{h}_2$ to relative
error $u$ into the coefficient block and nothing else. -/
private theorem exec_cgs2_add {u : P → ℝ} {dec : P → K → ℝ} (I : Interp P ι K C)
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (tag : P) (jE : IExp ℕ) (hb T : ℕ)
    (ho : IExp ℕ) (st : St P K C) (H₁ H₂ : Fin jE.eval → K)
    (hh₁ : ∀ k : Fin jE.eval, st.store.read tag hb (ho.eval + k) = some (H₁ k))
    (hh₂ : ∀ k : Fin jE.eval, st.store.read tag T k = some (H₂ k)) (hT : 0 < jE.eval → T ≠ hb) :
    ∃ (s' : St P K C) (Hs : Fin jE.eval → K), exec I (forRange jE fun i =>
        ins (ι := ι) (.bin tag .add ⟨hb, ho + .var i⟩ ⟨hb, ho + .var i⟩ ⟨T, .var i⟩)).run st =
        some s' ∧ s'.store.shape = st.store.shape ∧
      (∀ k : Fin jE.eval, s'.store.read tag hb (ho.eval + k) = some (Hs k)) ∧
      (∀ k : Fin jE.eval, |dec tag (Hs k) - (dec tag (H₁ k) + dec tag (H₂ k))| ≤
        u tag * |dec tag (H₁ k) + dec tag (H₂ k)|) ∧
      ∀ q b i, ¬(b = hb ∧ ho.eval ≤ i ∧ i < ho.eval + jE.eval) →
        s'.store.read q b i = st.store.read q b i := by
  rw [show (forRange (ι := ι) jE fun i =>
      ins (.bin tag .add ⟨hb, ho + .var i⟩ ⟨hb, ho + .var i⟩ ⟨T, .var i⟩)).run = .seq (.loop jE
      fun i => (ins (.bin tag .add ⟨hb, ho + .var i⟩ ⟨hb, ho + .var i⟩ ⟨T, .var i⟩)).run) .skip
    from rfl, exec_seq_skip]
  obtain ⟨s', hrun, hsh, hval, hfr⟩ := exists_exec_loop_write I (n := jE) (st := st)
    tag hb ho.eval (fun k v => ∀ hk : k < jE.eval,
      |dec tag v - (dec tag (H₁ ⟨k, hk⟩) + dec tag (H₂ ⟨k, hk⟩))| ≤
        u tag * |dec tag (H₁ ⟨k, hk⟩) + dec tag (H₂ ⟨k, hk⟩)|)
    fun k hk s hs hs' => by
      obtain ⟨n, hn, hlt⟩ := Store.exists_getElem?_shape_of_read_eq_some (hh₁ ⟨k, hk⟩)
      have hx : s.store.read tag hb (ho.eval + k) = some (H₁ ⟨k, hk⟩) := by
        rw [hs' _ _ _ (by omega)]; exact hh₁ ⟨k, hk⟩
      have hy : s.store.read tag T k = some (H₂ ⟨k, hk⟩) := by
        rw [hs' _ _ _ fun h => hT (by omega) h.1]; exact hh₂ ⟨k, hk⟩
      obtain ⟨z, hzv⟩ := h.bin_ok tag .add (H₁ ⟨k, hk⟩) (H₂ ⟨k, hk⟩) trivial
        (fun e => by cases e) trivial
      obtain ⟨δ, hδ, hdz⟩ := h.bin_err tag .add _ _ z trivial hzv
      obtain ⟨s'', hs''⟩ := Store.exists_write_eq_some_of_getElem?_shape z (hs ▸ hn) hlt
      refine ⟨{ s with store := s'', cnt := s.cnt + I.charge (.bin tag .add) }, z, ?_, hs'',
        fun hk' => ?_⟩
      · rw [exec_seq_instr_bin I (dst := ⟨hb, ho + .var k⟩) (x := ⟨hb, ho + .var k⟩)
          (y := ⟨T, .var k⟩) hx hy hzv hs'', exec_skip]
      · simp only [BinOp.realOp] at hdz
        rw [hdz, show (dec tag (H₁ ⟨k, hk⟩) + dec tag (H₂ ⟨k, hk⟩)) * (1 + δ) -
          (dec tag (H₁ ⟨k, hk⟩) + dec tag (H₂ ⟨k, hk⟩)) =
          (dec tag (H₁ ⟨k, hk⟩) + dec tag (H₂ ⟨k, hk⟩)) * δ by ring, abs_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right hδ (abs_nonneg _)
  choose Hs hHs hHb using fun k : Fin jE.eval => hval k k.2
  exact ⟨s', Hs, hrun, hsh, hHs, fun k => hHb k k.2, hfr⟩

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
    (hV : HoldsDecoded st.store dec tag Vb 0 V)
    (hw : ∀ i : Fin NE.eval, ∃ x, st.store.read tag wb (wo.eval + i) = some x ∧ dec tag x = w i)
    (hwlen : ∀ i < NE.eval, ∃ len, st.store.shape[wb]? = some (tag, len) ∧ wo.eval + i < len)
    (hhlen : ∀ i < jE.eval, ∃ len, st.store.shape[hb]? = some (tag, len) ∧ ho.eval + i < len)
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
  have hlt : ∀ {b}, (∃ n, st.store.shape[b]? = some n) → b < T := fun ⟨n, hn⟩ => by
    simpa [Store.size_shape] using (Array.getElem?_eq_some_iff.mp hn).1
  have hwlt : 0 < NE.eval → wb < T := fun h => hlt ⟨_, (hwlen 0 h).choose_spec.1⟩
  have hhlt : 0 < jE.eval → hb < T := fun h => hlt ⟨_, (hhlen 0 h).choose_spec.1⟩
  have hVlt : 0 < NE.eval → 0 < jE.eval → Vb < T := fun h₁ h₂ =>
    let ⟨_, hx, _⟩ := hV ⟨0, h₁⟩ ⟨0, h₂⟩
    Store.lt_size_of_read_eq_some hx
  have hrd₀ : ∀ {q b i}, b < T → σ₀.store.read q b i = st.store.read q b i := fun hb => by
    rw [hσ₀, Store.read_push_of_lt hb]
  have hsh₀ : ∀ {b}, b < T → σ₀.store.shape[b]? = st.store.shape[b]? := fun hb => by
    rw [hσ₀, Store.getElem?_shape_push_of_lt _ hb]
  rw [exec_run_bind I (b := cgsPass tag NE jE Vb wb wo hb ho) (fun _ => rfl)]
  obtain ⟨o₁, W₁, H₁, hrun₁, hsh₁, hw₁, hh₁, hfr₁, hb₁⟩ := exec_cgsPass_frame I h hz tag NE
    jE Vb wb hb wo ho σ₀ V w
    (fun i k => by
      obtain ⟨x, hx, hdx⟩ := hV i k
      exact ⟨x, by rw [hrd₀ (Store.lt_size_of_read_eq_some hx)]; exact hx, hdx⟩)
    (fun i => by
      obtain ⟨x, hx, hdx⟩ := hw i
      exact ⟨x, by rw [hrd₀ (hwlt (Fin.pos i))]; exact hx, hdx⟩)
    (fun i hi => by rw [hsh₀ (hhlt (by omega))]; exact hhlen i hi)
    (fun _ _ => ⟨hne.1, hne.2.1⟩) hu1
  rw [hrun₁, Option.bind_some, exec_run_bind I (b := cgsPass tag NE jE Vb wb wo T 0)
    (fun _ => rfl)]
  have hTshape : o₁.store.shape[T]? = some (tag, jE.eval) := by
    rw [hsh₁, hσ₀, Store.getElem?_shape_push_size]
  obtain ⟨o₂, W₂, H₂, hrun₂, hsh₂, hw₂, hh₂, hfr₂, hb₂⟩ := exec_cgsPass_frame I h hz tag NE
    jE Vb wb T wo 0 o₁ V (fun i => dec tag (W₁ i))
    (fun i k => by
      obtain ⟨x, hx, hdx⟩ := hV i k
      refine ⟨x, ?_, hdx⟩
      rw [hfr₁ _ _ _ (fun h => hne.2.2 h.1.symm) (fun h => hne.2.1 h.1.symm),
        hrd₀ (Store.lt_size_of_read_eq_some hx)]
      exact hx)
    (fun i => ⟨W₁ i, hw₁ i, rfl⟩) (fun i hi => ⟨_, hTshape, by simpa using hi⟩)
    (fun h₁ h₂ => ⟨by have := hwlt h₁; omega, by have := hVlt h₁ h₂; omega⟩) hu1
  rw [hrun₂, Option.bind_some]
  obtain ⟨o₃, Hs, hrun₃, hsh₃, hh₃, hs₃, hfr₃⟩ := exec_cgs2_add I h tag jE hb T ho o₂ H₁ H₂
    (fun k => by
      have := hhlt (Fin.pos k)
      rw [hfr₂ _ _ _ (fun h => hne.1 h.1) (fun h => by omega), hh₁ k])
    (fun k => by simpa using hh₂ k) fun h => by have := hhlt h; omega
  obtain ⟨mid, hmid⟩ := Store.exists_writeBlock_eq_some_of_getElem?_shape (s := st.store)
    (p := tag) (b := wb) (off := wo.eval) (xs := Array.ofFn W₂)
    fun i hi => hwlen i (by simpa using hi)
  obtain ⟨fin, hfin⟩ := Store.exists_writeBlock_eq_some_of_getElem?_shape (s := mid) (p := tag)
    (b := hb) (off := ho.eval) (xs := Array.ofFn Hs) fun i hi => by
      rw [Store.shape_of_writeBlock_eq_some hmid]; exact hhlen i (by simpa using hi)
  have hsz₃ : o₃.store.size = T + 1 := by
    rw [← Store.size_shape, hsh₃, hsh₂, hsh₁, Store.size_shape, hσ₀, Array.size_push]
  have hpop : ∀ {q b i}, b < T → Store.read o₃.store.pop q b i = o₃.store.read q b i :=
    fun hb => Store.read_pop_of_lt (by omega)
  have heq : o₃.store.pop = fin := by
    refine eq_of_read_writeBlock_writeBlock (Ne.symm hne.1) ?_ (fun i hi => ?_)
      (fun k hk => ?_) (fun q b i h₁ h₂ => ?_) hmid hfin
    · rw [Store.shape_pop, hsh₃, hsh₂, hsh₁, hσ₀]
      simp [Store.shape]
    · rw [Array.size_ofFn] at hi
      rw [hpop (hwlt (by omega)), hfr₃ _ _ _ (fun h => hne.1 h.1.symm), hw₂ ⟨i, hi⟩]
      simp [hi]
    · rw [Array.size_ofFn] at hk
      rw [hpop (hhlt (by omega)), hh₃ ⟨k, hk⟩]
      simp [hk]
    · simp only [Array.size_ofFn] at h₁ h₂
      by_cases hbT : b < T
      · rw [hpop hbT, hfr₃ q b i h₂, hfr₂ q b i h₁ (fun h => by omega), hfr₁ q b i h₁ h₂,
          hrd₀ hbT]
      · rw [Store.read_eq_none_of_size_le (by simp [hsz₃]; omega),
          Store.read_eq_none_of_size_le (by omega)]
  exact ⟨o₃, W₁, W₂, H₁, H₂, Hs, mid, hrun₃, hmid, heq ▸ hfin, hb₁, hb₂, hs₃⟩

/-- A rounded `NLAlib.cgs2` succeeds, writes only the reduced vector at (`wb`, `wo`) and the
summed coefficients at (`hb`, `ho`), and meets the bounds of its two passes and of the sum. -/
private theorem exists_exec_cgs2 {u : P → ℝ} {dec : P → K → ℝ} (I : Interp P ι K C)
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem) (tag : P)
    (NE jE : IExp ℕ) (Vb wb hb : ℕ) (wo ho : IExp ℕ) (st : St P K C)
    (V : Matrix (Fin NE.eval) (Fin jE.eval) ℝ) (w : Fin NE.eval → ℝ)
    (hV : HoldsDecoded st.store dec tag Vb 0 V)
    (hw : ∀ i : Fin NE.eval, ∃ x, st.store.read tag wb (wo.eval + i) = some x ∧ dec tag x = w i)
    (hwlen : ∀ i < NE.eval, ∃ len, st.store.shape[wb]? = some (tag, len) ∧ wo.eval + i < len)
    (hhlen : ∀ i < jE.eval, ∃ len, st.store.shape[hb]? = some (tag, len) ∧ ho.eval + i < len)
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
    obtain ⟨o, W₁, W₂, H₁, H₂, Hs, mid, hrun', hR⟩ := exec_cgs2_body I h hz tag NE jE Vb wb hb wo
      ho st σ₀ V w hV hw hwlen hhlen hne hu1 hσ₀
    exact ⟨o, hrun', W₁, W₂, H₁, H₂, Hs, mid, hR⟩
  exact ⟨out, W₁, W₂, H₁, H₂, Hs, mid, hex, hR⟩

/-- CGS2 is a certified orthogonalization routine: under the standard model, for
$0 \le \eta_0 \le 1/100$, $(N + j + 2)u \le 1/100$ and $c_1 =$ `NLAlib.cgsPassBound`
$N\,j\,u\,\eta_0$ (that is,
<!-- value cgsPassBound N j u \eta_0 -->$2(1+\eta_0)\sqrt{j+1}\,(N+j+2)\,u$)
$\le 1/100$, `NLAlib.cgs2` meets `NLAlib.Computation.IsOrthRoutine` at
$(\eta_0, 2c_1, 3c_1, 2(\eta_0 + c_1)^2)$ with `pre = True`.
`docs/design/Krylov-LanczosReorth.md` §1.3. -/
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
  intro st V w _ hV hw hwlen hhlen hbw hbV hwV
  have hu1 : u tag < 1 := by
    have : (2 : ℝ) ≤ ((NE.eval + jE.eval + 2 : ℕ) : ℝ) := by push_cast; linarith
    nlinarith [h.nonneg (p := tag) trivial]
  obtain ⟨out, W₁, W₂, H₁, H₂, Hs, mid, hex, hmid, hfin, P₁, P₂, hsum⟩ := exists_exec_cgs2 I h hz
    tag NE jE Vb wb hb wo ho st V w hV hw hwlen hhlen ⟨hbw, hbV, hwV⟩ hu1
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
    hb wo ho st V w (fun i k => ⟨_, hV i k, rfl⟩) (fun i => ⟨_, hw i, rfl⟩) hwlen hhlen hne
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
