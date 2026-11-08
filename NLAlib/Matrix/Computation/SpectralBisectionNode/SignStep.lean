/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SpectralBisectionProgramTree
public import NLAlib.Matrix.Computation.SpectralBisectionTape
public import NLAlib.Matrix.Computation.NewtonSchulzSignProgram

/-!
# The sign step of the spectral bisection program

The sign block of the node step of `NLAlib.eighProg` (`NLAlib.eighSignBlock`) runs the Newton–Schulz
iteration with the shallow step limit, a bounded loop that stops at the first iterate that passes
the test: under kernels that are routines on pairs and a semantics that decides flags, a successful
run writes the sign `NLAlib.newtonSchulzSign` of the machine of the semantics, and under the
standard model it always succeeds (unlike the `whileFuel` loop of `NLAlib.newtonSchulzSignProg`, it
does not fail when no iterate passes the test).

## Main results

* `NLAlib.holds_of_exec_eighSignLoop`, `NLAlib.holds_of_exec_eighSignBlock`: what a successful run
  computes.
* `NLAlib.exists_exec_eighSignBlock`: the sign step succeeds.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {Su Sg : Type} {toNat : K → ℕ} {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}
  {unif : K → Su → K} {normal : Sg → K × K}

/-! ### The sign step with the shallow step limit -/

private theorem holds_of_exec_eighSignStep {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (p : P) (n : ℕ)
    {X W V t : ℕ} {xo : IExp ℕ} {η : K} {st st₁ : St P K C}
    {A : Matrix (Fin n) (Fin n) (K × K)} (hA : pairLayout.Holds st.store p X xo.eval A)
    (hW : pairLayout.Holds st.store p W 0 (mmR A A)) (hη : st.store.read p t 0 = some η)
    (hone : st.store.read p t 3 = some (I.sem.toFloatMachine p toNat mmR qrR unif normal).one)
    (hlo : st.store.read p t 4 =
      some ((I.sem.toFloatMachine p toNat mmR qrR unif normal).neg η))
    (hWX : W ≠ X) (hVX : V ≠ X) (hWV : W ≠ V) (htX : t ≠ X) (htW : t ≠ W) (htV : t ≠ V)
    (h : exec I (Builder.run do
      newtonSchulzStepBlock p mm (.const n) X xo W V ⟨t, 2⟩
      newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩) st =
        some st₁) :
    let M := I.sem.toFloatMachine p toNat mmR qrR unif normal
    pairLayout.Holds st₁.store p X xo.eval (newtonSchulzRounded M A) ∧
      pairLayout.Holds st₁.store p W 0 (mmR (newtonSchulzRounded M A) (newtonSchulzRounded M A)) ∧
      st₁.store.read p t 0 = some η ∧ st₁.store.read p t 3 = some M.one ∧
      st₁.store.read p t 4 = some (M.neg η) ∧
      st₁.store.read p t 1 = some
        (if newtonSchulzTest M η (newtonSchulzRounded M A) then M.zero else M.one) ∧
      (∀ q b i, b ≠ t → b ≠ W → b ≠ V →
        blockDisjoint (b, i, 1) (X, xo.eval, 2 * (n * n)) = true →
        st₁.store.read q b i = st.store.read q b i) ∧
      st₁.store.shape = st.store.shape ∧ st₁.pos = st.pos := by
  have hd : ∀ {b b' : ℕ} (o o' l l' : ℕ), b ≠ b' → blockDisjoint (b, o, l) (b', o', l') = true :=
    fun _ _ _ _ h => by simp [blockDisjoint, h]
  have hsingle : ∀ (b : Builder P ι ℕ ℕ Unit) (S : Stmt P ι ℕ ℕ),
      (∀ k, ContT.run b k = .seq S (k ())) → ∀ (f : Unit → Builder P ι ℕ ℕ Unit) (st : St P K C),
        exec I (b >>= f).run st = (exec I b.run st).bind (exec I (f ()).run) :=
    fun _ _ hb f st => exec_run_bind I hb f st
  have hstep : ∀ (f : Unit → Builder P ι ℕ ℕ Unit) (σ : St P K C),
      exec I (newtonSchulzStepBlock p mm (.const n) X xo W V ⟨t, 2⟩ >>= f).run σ =
        (exec I (newtonSchulzStepBlock p mm (.const n) X xo W V ⟨t, 2⟩).run σ).bind
          (exec I (f ()).run) := by
    unfold newtonSchulzStepBlock
    exact exec_run_bind_bind (hsingle _ _ fun _ => rfl)
      (exec_run_bind_bind (hsingle _ _ fun _ => rfl)
      (exec_run_bind_bind (hsingle _ _ fun _ => rfl)
      (exec_run_bind_bind (hsingle _ _ fun _ => rfl)
      (exec_run_bind_bind (hsingle _ _ fun _ => rfl) (hsingle _ _ fun _ => rfl)))))
  rw [hstep] at h
  obtain ⟨σ, hσ, h₁⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hXσ, hfrσ, hshσ, hposσ⟩ := holds_of_exec_newtonSchulzStepBlock (toNat := toNat)
    (qrR := qrR) (unif := unif) (normal := normal) hmm p n hA hW hWX hVX hWV htW htV
    (hd _ _ _ _ htX) hσ
  have hrσ : ∀ i, i ≠ 2 → σ.store.read p t i = st.store.read p t i := fun i hi =>
    hfrσ p t i htW htV (hd _ _ _ _ htX) (blockDisjoint_cell_of_ne hi)
  obtain ⟨hW₁, -, hf₁, hfr₁, hsh₁, hpos₁⟩ := holds_of_exec_newtonSchulzTestBlock (toNat := toNat)
    (qrR := qrR) (unif := unif) (normal := normal) hmm p n (one := ⟨t, 3⟩) (lo := ⟨t, 4⟩)
    (hi := ⟨t, 0⟩) (f := ⟨t, 1⟩) hXσ ((hrσ 3 (by omega)).trans hone)
    ((hrσ 4 (by omega)).trans hlo) ((hrσ 0 (by omega)).trans hη) hWX hVX hWV
    (by simp [htW, htV]) (hd _ _ _ _ htX) (by simp [blockDisjoint]) (by simp [blockDisjoint]) h₁
  have hr₁ : ∀ i, i ≠ 1 → i ≠ 2 → st₁.store.read p t i = st.store.read p t i := fun i h1 h2 =>
    (hfr₁ p t i htW htV (blockDisjoint_cell_of_ne h1)).trans (hrσ i h2)
  refine ⟨hXσ.of_forall_read_eq fun i _ _ => hfr₁ _ _ _ hWX.symm hVX.symm (hd _ _ _ _ htX.symm),
    hW₁, (hr₁ 0 (by omega) (by omega)).trans hη, (hr₁ 3 (by omega) (by omega)).trans hone,
    (hr₁ 4 (by omega) (by omega)).trans hlo, hf₁, fun q b i hbt hbW hbV hbX => ?_,
    hsh₁.trans hshσ, hpos₁.trans hposσ⟩
  exact (hfr₁ q b i hbW hbV (hd _ _ _ _ hbt)).trans (hfrσ q b i hbW hbV hbX (hd _ _ _ _ hbt))

/-- The bounded Newton–Schulz loop computes `NLAlib.newtonSchulzLoop`: if kernel `mm` of `I`
is the routine `mmR` on interleaved pairs and the semantics decides flags at `p`, a successful run
of the loop of `NLAlib.eighSignBlock` with $F$ iterations, from a state whose block at `X` holds
$\mathbf{A}$, whose scratch buffer `W` holds $\mathrm{mm}(\mathbf{A}, \mathbf{A})$, whose cells
$0$, $3$, $4$ of the scratch buffer `t` hold $\eta$, the machine's one and $-\eta$, and whose cell
$1$ holds the flag of the test of $\mathbf{A}$, ends with the block at `X` holding
`NLAlib.newtonSchulzLoop M η F A` ($M$ the machine of the semantics at `p` with product `mmR`);
every cell outside the block at `X` and the buffers `t`, `W`, `V` is unchanged, the store shape and
the tape positions too. No printed source. -/
theorem holds_of_exec_eighSignLoop {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (p : P) (hflag : I.sem.DecidesFlags p) (n F : ℕ) {X W V t : ℕ} {xo : IExp ℕ} {η : K}
    {st st' : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)}
    (hA : pairLayout.Holds st.store p X xo.eval A)
    (hW : pairLayout.Holds st.store p W 0 (mmR A A))
    (hη : st.store.read p t 0 = some η)
    (hone : st.store.read p t 3 = some (I.sem.toFloatMachine p toNat mmR qrR unif normal).one)
    (hlo : st.store.read p t 4 =
      some ((I.sem.toFloatMachine p toNat mmR qrR unif normal).neg η))
    (hf : st.store.read p t 1 = some (if newtonSchulzTest
      (I.sem.toFloatMachine p toNat mmR qrR unif normal) η A then
        (I.sem.toFloatMachine p toNat mmR qrR unif normal).zero else
        (I.sem.toFloatMachine p toNat mmR qrR unif normal).one))
    (hWX : W ≠ X) (hVX : V ≠ X) (hWV : W ≠ V) (htX : t ≠ X) (htW : t ≠ W) (htV : t ≠ V)
    (h : exec I (forRange (ι := ι) (.const F) fun _ => ifThenElse p .eq ⟨t, 1⟩ ⟨t, 3⟩
      (do
        newtonSchulzStepBlock p mm (.const n) X xo W V ⟨t, 2⟩
        newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩)
      (pure ())).run st = some st') :
    pairLayout.Holds st'.store p X xo.eval
        (newtonSchulzLoop (I.sem.toFloatMachine p toNat mmR qrR unif normal) η F A) ∧
      (∀ q b i, b ≠ t → b ≠ W → b ≠ V →
        blockDisjoint (b, i, 1) (X, xo.eval, 2 * (n * n)) = true →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  obtain ⟨z, o, hz, ho, hzo, hoo⟩ := hflag
  have hM0 : (I.sem.toFloatMachine p toNat mmR qrR unif normal).zero = z := by
    simp [ScalarSem.toFloatMachine, hz]
  have hM1 : (I.sem.toFloatMachine p toNat mmR qrR unif normal).one = o := by
    simp [ScalarSem.toFloatMachine, ho]
  change exec I (.seq (.loop (.const F) fun _ => (ifThenElse (ι := ι) p .eq ⟨t, 1⟩ ⟨t, 3⟩ (do
        newtonSchulzStepBlock p mm (.const n) X xo W V ⟨t, 2⟩
        newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩)
      (pure ())).run) .skip) st = some st' at h
  rw [exec_seq_skip] at h
  induction F generalizing st A with
  | zero =>
    simp only [exec_loop, IExp.eval, List.range_zero, List.foldlM_nil, Option.pure_def,
      Option.some.injEq] at h
    subst h
    exact ⟨hA, fun _ _ _ _ _ _ _ => rfl, rfl, rfl⟩
  | succ k ih =>
    rw [exec_loop] at h
    simp only [IExp.eval, List.range_succ_eq_map, List.foldlM_cons, List.foldlM_map] at h
    obtain ⟨st₁, h₁, h⟩ := Option.bind_eq_some_iff.mp h
    change exec I (.seq (.ite p .eq ⟨t, 1⟩ ⟨t, 3⟩ _ _) .skip) st = some st₁ at h₁
    rw [exec_seq_skip, exec_ite] at h₁
    cases ht : newtonSchulzTest (I.sem.toFloatMachine p toNat mmR qrR unif normal) η A
    · rw [ht, if_neg (by simp), hM1] at hf
      rw [hM1] at hone
      simp only [cmpStep, IExp.eval, hf, hone, hoo, Option.bind_some, Option.map_some,
        if_true] at h₁
      obtain ⟨hX₁, hW₁, hη₁, hone₁, hlo₁, hf₁, hfr₁, hsh₁, hpos₁⟩ :=
        holds_of_exec_eighSignStep hmm p n (st := { st with cnt := st.cnt + I.charge (.cmp p) })
          hA hW hη
          (by rw [hM1]; exact hone) hlo hWX hVX hWV htX htW htV h₁
      obtain ⟨hX', hfr', hsh', hpos'⟩ := ih hX₁ hW₁ hη₁ hone₁ hlo₁ hf₁
        (by rw [exec_loop]; exact h)
      refine ⟨by simpa [newtonSchulzLoop, ht] using hX', fun q b i h1 h2 h3 h4 =>
        (hfr' q b i h1 h2 h3 h4).trans (hfr₁ q b i h1 h2 h3 h4), hsh'.trans hsh₁,
        hpos'.trans hpos₁⟩
    · rw [ht, if_pos rfl, hM0] at hf
      rw [hM1] at hone
      simp only [cmpStep, IExp.eval, hf, hone, hzo, Option.bind_some, Option.map_some,
        Bool.false_eq_true, if_false] at h₁
      change exec I .skip _ = some st₁ at h₁
      rw [exec_skip, Option.some.injEq] at h₁
      subst h₁
      obtain ⟨hX', hfr', hsh', hpos'⟩ := ih (st := { st with cnt := st.cnt + I.charge (.cmp p) })
        hA hW hη (by rw [hM1]; exact hone) hlo
        (by rw [ht, if_pos rfl, hM0]; exact hf) (by rw [exec_loop]; exact h)
      have hL : ∀ N, newtonSchulzLoop (I.sem.toFloatMachine p toNat mmR qrR unif normal) η N
          A = A := fun N => by cases N <;> simp [newtonSchulzLoop, ht]
      exact ⟨by rw [hL]; rw [hL] at hX'; exact hX', hfr', hsh', hpos'⟩

omit [Inhabited K] in
private theorem exists_of_exec_seq_litIdx {p : P} {dst : Cell ℕ ℕ} {e : IExp ℕ} {t : Stmt P ι ℕ ℕ}
    {s s₂ : St P K C} (h : exec I (.seq (.instr (.litIdx p dst e)) t) s = some s₂) :
    ∃ v s', I.sem.lit p (e.eval : ℚ) = some v ∧ s.store.write p dst.buf dst.idx.eval v = some s' ∧
      exec I t { s with store := s', cnt := s.cnt + I.charge (.lit p) } = some s₂ := by
  rw [exec_seq, exec_instr] at h
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨_, ⟨v, hv, s', hw, rfl⟩, rfl⟩, h⟩ := h
  exact ⟨v, s', hv, hw, h⟩

omit [Inhabited K] in
private theorem exists_of_exec_seq_lit {p : P} {dst : Cell ℕ ℕ} {q : ℚ} {t : Stmt P ι ℕ ℕ}
    {s s₂ : St P K C} (h : exec I (.seq (.instr (.lit p dst q)) t) s = some s₂) :
    ∃ v s', I.sem.lit p q = some v ∧ s.store.write p dst.buf dst.idx.eval v = some s' ∧
      exec I t { s with store := s', cnt := s.cnt + I.charge (.lit p) } = some s₂ := by
  rw [exec_seq, exec_instr] at h
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨_, ⟨v, hv, s', hw, rfl⟩, rfl⟩, h⟩ := h
  exact ⟨v, s', hv, hw, h⟩

omit [Inhabited K] in
private theorem exists_of_exec_seq_bin {p : P} {op : BinOp} {dst x y : Cell ℕ ℕ} {t : Stmt P ι ℕ ℕ}
    {s s₂ : St P K C} (h : exec I (.seq (.instr (.bin p op dst x y)) t) s = some s₂) :
    ∃ a c v s', s.store.read p x.buf x.idx.eval = some a ∧
      s.store.read p y.buf y.idx.eval = some c ∧ I.sem.bin p op a c = some v ∧
      s.store.write p dst.buf dst.idx.eval v = some s' ∧
      exec I t { s with store := s', cnt := s.cnt + I.charge (.bin p op) } = some s₂ := by
  rw [exec_seq, exec_instr] at h
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨_, ⟨a, ha, c, hc, v, hv, s', hw, rfl⟩, rfl⟩, h⟩ := h
  exact ⟨a, c, v, s', ha, hc, hv, hw, h⟩

omit [Inhabited K] in
private theorem exists_of_exec_seq_un {p : P} {u : UnOp} {dst x : Cell ℕ ℕ} {t : Stmt P ι ℕ ℕ}
    {s s₂ : St P K C} (h : exec I (.seq (.instr (.un p u dst x)) t) s = some s₂) :
    ∃ a v s', s.store.read p x.buf x.idx.eval = some a ∧ I.sem.un p u a = some v ∧
      s.store.write p dst.buf dst.idx.eval v = some s' ∧
      exec I t { s with store := s', cnt := s.cnt + I.charge (.un p u) } = some s₂ := by
  rw [exec_seq, exec_instr] at h
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨_, ⟨a, ha, v, hv, s', hw, rfl⟩, rfl⟩, h⟩ := h
  exact ⟨a, v, s', ha, hv, hw, h⟩

omit [AddMonoid C] [Inhabited K] in
private theorem read_pop_pop_pop {s : Store P K} {q : P} {b i : ℕ} (hb : b + 3 < s.size) :
    Store.read (Array.pop (Array.pop (Array.pop s))) q b i = s.read q b i := by
  rw [Store.read_pop_of_lt (by simp; omega), Store.read_pop_of_lt (by simp; omega),
    Store.read_pop_of_lt (by omega)]

omit [AddMonoid C] [Inhabited K] in
private theorem read_push_push_push_and_shape {s : Store P K} {p q : P} {a b c β i : ℕ}
    (hβ : β < s.size) :
    Store.read (((s.push (p, Array.replicate a none)).push (p, Array.replicate b none)).push
      (p, Array.replicate c none)) q β i = s.read q β i ∧
    (Store.shape (((s.push (p, Array.replicate a none)).push (p, Array.replicate b none)).push
      (p, Array.replicate c none)))[β]? = s.shape[β]? := by
  refine ⟨?_, ?_⟩
  · rw [Store.read_push_of_lt (by simp; omega), Store.read_push_of_lt (by simp; omega),
      Store.read_push_of_lt hβ]
  · rw [Store.getElem?_shape_push_of_lt _ (by simp; omega),
      Store.getElem?_shape_push_of_lt _ (by simp; omega), Store.getElem?_shape_push_of_lt _ hβ]

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
private theorem getElem?_shape_push_push_push (s : Store P K) (p : P) (a b c : ℕ) :
    let s₁ := s.push (p, Array.replicate a none)
    let s₂ := s₁.push (p, Array.replicate b none)
    (Store.shape (s₂.push (p, Array.replicate c none)))[s.size]? = some (p, a) ∧
    (Store.shape (s₂.push (p, Array.replicate c none)))[s₁.size]? = some (p, b) ∧
    (Store.shape (s₂.push (p, Array.replicate c none)))[s₂.size]? = some (p, c) := by
  refine ⟨?_, ?_, Store.getElem?_shape_push_size _ _ _⟩
  · rw [Store.getElem?_shape_push_of_lt _ (by simp), Store.getElem?_shape_push_of_lt _ (by simp),
      Store.getElem?_shape_push_size]
  · rw [Store.getElem?_shape_push_of_lt _ (by simp), Store.getElem?_shape_push_size]

/-- The scaling, the first test and the loop of `NLAlib.eighSignBlock`, from the state after
the four instructions. -/
private theorem holds_of_exec_eighSignTail {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (p : P) (hflag : I.sem.DecidesFlags p) (n F : ℕ) {A par X t W V : ℕ} {ao po xo : IExp ℕ}
    {σ st' : St P K C} {A₀ : Matrix (Fin n) (Fin n) (K × K)} {b η : K}
    (hA : pairLayout.Holds σ.store p A ao.eval A₀)
    (hb : σ.store.read p par (po.eval + 1) = some b)
    (hXA : blockDisjoint (X, xo.eval, 2 * (n * n)) (A, ao.eval, 2 * (n * n)) = true)
    (hXp : blockDisjoint (X, xo.eval, 2 * (n * n)) (par, po.eval, 2) = true)
    (hη : σ.store.read p t 0 = some η)
    (hone : σ.store.read p t 3 = some (I.sem.toFloatMachine p toNat mmR qrR unif normal).one)
    (hlo : σ.store.read p t 4 =
      some ((I.sem.toFloatMachine p toNat mmR qrR unif normal).neg η))
    (hWX : W ≠ X) (hVX : V ≠ X) (hWV : W ≠ V) (htX : t ≠ X) (htW : t ≠ W) (htV : t ≠ V)
    (h : exec I (Builder.run do
      zhermScale p (.const n) A ao ⟨par, po + 1⟩ X xo
      newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩
      forRange (.const F) fun _ => ifThenElse p .eq ⟨t, 1⟩ ⟨t, 3⟩
        (do
          newtonSchulzStepBlock p mm (.const n) X xo W V ⟨t, 2⟩
          newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩)
        (pure ())) σ =
        some st') :
    let M := I.sem.toFloatMachine p toNat mmR qrR unif normal
    pairLayout.Holds st'.store p X xo.eval (newtonSchulzLoop M η F (M.hermScale A₀ b)) ∧
      (∀ q b' i, b' ≠ t → b' ≠ W → b' ≠ V →
        blockDisjoint (b', i, 1) (X, xo.eval, 2 * (n * n)) = true →
        st'.store.read q b' i = σ.store.read q b' i) ∧
      st'.store.shape = σ.store.shape ∧ st'.pos = σ.pos := by
  intro M
  have hd : ∀ {b b' : ℕ} (o o' l l' : ℕ), b ≠ b' → blockDisjoint (b, o, l) (b', o', l') = true :=
    fun _ _ _ _ h => by simp [blockDisjoint, h]
  have hcY : blockDisjoint (par, po.eval + 1, 1) (X, xo.eval, 2 * (n * n)) = true := by
    simp only [blockDisjoint, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hXp ⊢
    omega
  have htestc : ∀ (f : Unit → Builder P ι ℕ ℕ Unit) (σ' : St P K C),
      exec I (newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩
        >>= f).run σ' = (exec I (newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩
          ⟨t, 0⟩ ⟨t, 1⟩).run σ').bind (exec I (f ()).run) := by
    unfold newtonSchulzTestBlock
    exact exec_run_bind_bind (fun f st => exec_run_bind I (fun _ => rfl) f st) (exec_run_bind_bind
      (fun f st => exec_run_bind I (fun _ => rfl) f st)
      (fun f st => exec_run_bind I (fun _ => rfl) f st))
  rw [exec_run_bind I (b := zhermScale (ι := ι) p (.const n) A ao ⟨par, po + 1⟩ X xo)
    (fun _ => rfl)] at h
  obtain ⟨σ₅, h₅, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hX₅, hfr₅, hsh₅, hpos₅⟩ := holds_of_exec_zhermScale (toNat := toNat) (mmR := mmR)
    (qrR := qrR) (unif := unif) (normal := normal) p n hA hb hXA hcY h₅
  have hr₅ : ∀ i, σ₅.store.read p t i = σ.store.read p t i := fun i => hfr₅ p t i (hd _ _ _ _ htX)
  rw [htestc] at h
  obtain ⟨σ₆, h₆, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hW₆, -, hf₆, hfr₆, hsh₆, hpos₆⟩ := holds_of_exec_newtonSchulzTestBlock
    (toNat := toNat) (qrR := qrR) (unif := unif) (normal := normal) hmm p n (one := ⟨t, 3⟩)
    (lo := ⟨t, 4⟩) (hi := ⟨t, 0⟩) (f := ⟨t, 1⟩) hX₅ ((hr₅ 3).trans hone) ((hr₅ 4).trans hlo)
    ((hr₅ 0).trans hη) hWX hVX hWV (by simp [htW, htV]) (hd _ _ _ _ htX)
    (by simp [blockDisjoint]) (by simp [blockDisjoint]) h₆
  have hr₆ : ∀ i, i ≠ 1 → σ₆.store.read p t i = σ.store.read p t i := fun i h =>
    (hfr₆ p t i htW htV (blockDisjoint_cell_of_ne h)).trans (hr₅ i)
  obtain ⟨hX', hfr', hsh', hpos'⟩ := holds_of_exec_eighSignLoop hmm p hflag n F
    (hX₅.of_forall_read_eq fun i _ _ => hfr₆ _ _ _ hWX.symm hVX.symm (hd _ _ _ _ htX.symm))
    hW₆ ((hr₆ 0 (by omega)).trans hη) ((hr₆ 3 (by omega)).trans hone)
    ((hr₆ 4 (by omega)).trans hlo) hf₆ hWX hVX hWV htX htW htV h
  refine ⟨hX', fun q b' i hbt hbW hbV hbX => ?_, hsh'.trans (hsh₆.trans hsh₅),
    hpos'.trans (hpos₆.trans hpos₅)⟩
  exact (hfr' q b' i hbt hbW hbV hbX).trans ((hfr₆ q b' i hbW hbV (hd _ _ _ _ hbt)).trans
    (hfr₅ q b' i hbX))

/-- The body of `NLAlib.eighSignBlock` inside its allocations. -/
private theorem holds_of_exec_eighSignBody {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (p : P) (hflag : I.sem.DecidesFlags p) (n F : ℕ) {A par X t W V : ℕ} {ao po xo : IExp ℕ}
    {st st' : St P K C} {A₀ : Matrix (Fin n) (Fin n) (K × K)} {ε b : K}
    (hA : pairLayout.Holds st.store p A ao.eval A₀)
    (hε : st.store.read p par po.eval = some ε) (hb : st.store.read p par (po.eval + 1) = some b)
    (hXA : blockDisjoint (X, xo.eval, 2 * (n * n)) (A, ao.eval, 2 * (n * n)) = true)
    (hXp : blockDisjoint (X, xo.eval, 2 * (n * n)) (par, po.eval, 2) = true)
    (htA : n = 0 ∨ t ≠ A) (htp : t ≠ par)
    (hWX : W ≠ X) (hVX : V ≠ X) (hWV : W ≠ V) (htX : t ≠ X) (htW : t ≠ W) (htV : t ≠ V)
    (h : exec I (Builder.run do
      ins (.litIdx p ⟨t, 2⟩ (4 * .const n))
      ins (.bin p .div ⟨t, 0⟩ ⟨par, po⟩ ⟨t, 2⟩)
      ins (.un p .neg ⟨t, 4⟩ ⟨t, 0⟩)
      ins (.lit p ⟨t, 3⟩ 1)
      zhermScale p (.const n) A ao ⟨par, po + 1⟩ X xo
      newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩
      forRange (.const F) fun _ => ifThenElse p .eq ⟨t, 1⟩ ⟨t, 3⟩
        (do
          newtonSchulzStepBlock p mm (.const n) X xo W V ⟨t, 2⟩
          newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩)
        (pure ())) st =
        some st') :
    pairLayout.Holds st'.store p X xo.eval
        (newtonSchulzSign (I.sem.toFloatMachine p toNat mmR qrR unif normal) ε b F A₀) ∧
      (∀ q b' i, b' ≠ t → b' ≠ W → b' ≠ V →
        blockDisjoint (b', i, 1) (X, xo.eval, 2 * (n * n)) = true →
        st'.store.read q b' i = st.store.read q b' i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  change exec I (.seq (.instr _) (.seq (.instr _) (.seq (.instr _) (.seq (.instr _)
    (.seq (.named _ _ _) (newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩
      ⟨t, 1⟩ >>= fun _ => forRange (.const F) fun _ => ifThenElse p .eq ⟨t, 1⟩ ⟨t, 3⟩
        (do
          newtonSchulzStepBlock p mm (.const n) X xo W V ⟨t, 2⟩
          newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩)
        (pure ())).run)))))
    st = some st' at h
  obtain ⟨v, s₁, hv, hs₁, h⟩ := exists_of_exec_seq_litIdx h
  obtain ⟨a, c, w, s₂, ha, hc, hw, hs₂, h⟩ := exists_of_exec_seq_bin h
  obtain ⟨a', w', s₃, ha', hw', hs₃, h⟩ := exists_of_exec_seq_un h
  obtain ⟨o, s₄, ho, hs₄, h⟩ := exists_of_exec_seq_lit h
  change st.store.write p t 2 v = some s₁ at hs₁
  change s₁.write p t 0 w = some s₂ at hs₂
  change s₂.write p t 4 w' = some s₃ at hs₃
  change s₃.write p t 3 o = some s₄ at hs₄
  change s₁.read p par po.eval = some a at ha
  change s₁.read p t 2 = some c at hc
  change s₂.read p t 0 = some a' at ha'
  rw [Store.read_of_write_eq_some_of_ne hs₁ (Or.inl (Ne.symm htp)), hε, Option.some_inj] at ha
  rw [Store.read_of_write_eq_some hs₁, Option.some_inj] at hc
  rw [Store.read_of_write_eq_some hs₂, Option.some_inj] at ha'
  subst ha hc ha'
  have hMη : (I.sem.toFloatMachine p toNat mmR qrR unif normal).div ε
      ((I.sem.toFloatMachine p toNat mmR qrR unif normal).ofNat (4 * n)) = w := by
    change (I.sem.bin p .div ε ((I.sem.lit p (((4 * n : ℕ)) : ℚ)).getD default)).getD default = w
    have hv' : I.sem.lit p (((4 * n : ℕ)) : ℚ) = some v := hv
    rw [hv', Option.getD_some, hw, Option.getD_some]
  have hMneg : (I.sem.toFloatMachine p toNat mmR qrR unif normal).neg w = w' := by
    change (I.sem.un p .neg w).getD default = w'; rw [hw']; rfl
  have hMone : (I.sem.toFloatMachine p toNat mmR qrR unif normal).one = o := by
    change (I.sem.lit p 1).getD default = o; rw [ho]; rfl
  have hfr₄ : ∀ q b i, b ≠ t → s₄.read q b i = st.store.read q b i := fun q b i h => by
    rw [Store.read_of_write_eq_some_of_ne hs₄ (Or.inl h), Store.read_of_write_eq_some_of_ne hs₃
      (Or.inl h), Store.read_of_write_eq_some_of_ne hs₂ (Or.inl h),
      Store.read_of_write_eq_some_of_ne hs₁ (Or.inl h)]
  have hsh₄ : s₄.shape = st.store.shape := by
    rw [Store.shape_of_write_eq_some hs₄, Store.shape_of_write_eq_some hs₃,
      Store.shape_of_write_eq_some hs₂, Store.shape_of_write_eq_some hs₁]
  obtain ⟨hX', hfr', hsh', hpos'⟩ := holds_of_exec_eighSignTail (toNat := toNat) (qrR := qrR)
    (unif := unif) (normal := normal) hmm p hflag n F (η := w)
    (σ := { st with store := s₄, cnt := _ })
    (by
      rcases htA with rfl | htA
      · exact fun i => i.elim0
      · exact hA.of_forall_read_eq fun i _ _ => hfr₄ _ _ _ htA.symm)
    ((hfr₄ _ _ _ htp.symm).trans hb)
    hXA hXp (by
      change s₄.read p t 0 = some w
      rw [Store.read_of_write_eq_some_of_ne hs₄ (Or.inr (by norm_num)),
        Store.read_of_write_eq_some_of_ne hs₃ (Or.inr (by norm_num))]
      exact Store.read_of_write_eq_some hs₂)
    (by rw [hMone]; exact Store.read_of_write_eq_some hs₄)
    (by
      change s₄.read p t 4 = _
      rw [hMneg, Store.read_of_write_eq_some_of_ne hs₄ (Or.inr (by norm_num))]
      exact Store.read_of_write_eq_some hs₃) hWX hVX hWV htX htW htV h
  refine ⟨?_, fun q b' i hbt hbW hbV hbX => (hfr' q b' i hbt hbW hbV hbX).trans
    (hfr₄ q b' i hbt), hsh'.trans hsh₄, hpos'⟩
  unfold newtonSchulzSign
  rw [hMη]
  exact hX'

/-- The sign step computes `NLAlib.newtonSchulzSign`: if kernel `mm` of `I` is the routine
`mmR` on interleaved pairs and the semantics decides flags at `p`, a successful run of
`NLAlib.eighSignBlock` at size $n$ and step limit $F$, from a state whose block at `A` holds the
stored $\mathbf{A}$ and whose cells `po`, `po + 1` of `par` hold $\varepsilon$ and $b$, with the
output block at `X` disjoint from both and in an existing buffer at tag `p` of at least $2n^2$
cells from `xo` (so not one of the block's scratch buffers, which are popped at the end), ends
with the output block holding `NLAlib.newtonSchulzSign M ε b F A` (the machine of the semantics at
`p` with product `mmR`, for every choice of its other black boxes); every cell outside the output
block is unchanged, the store shape and the tape positions too. No printed source. -/
theorem holds_of_exec_eighSignBlock {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (p : P) (hflag : I.sem.DecidesFlags p) (n F : ℕ) {A par X : ℕ} {ao po xo : IExp ℕ}
    {st st' : St P K C} {A₀ : Matrix (Fin n) (Fin n) (K × K)} {ε b : K}
    (hA : pairLayout.Holds st.store p A ao.eval A₀)
    (hε : st.store.read p par po.eval = some ε) (hb : st.store.read p par (po.eval + 1) = some b)
    (hXA : blockDisjoint (X, xo.eval, 2 * (n * n)) (A, ao.eval, 2 * (n * n)) = true)
    (hXp : blockDisjoint (X, xo.eval, 2 * (n * n)) (par, po.eval, 2) = true)
    (hX : ∃ len, st.store.shape[X]? = some (p, len) ∧ xo.eval + 2 * (n * n) ≤ len)
    (h : exec I (eighSignBlock p mm (.const n) (.const F) A ao par po X xo).run st = some st') :
    pairLayout.Holds st'.store p X xo.eval
        (newtonSchulzSign (I.sem.toFloatMachine p toNat mmR qrR unif normal) ε b F A₀) ∧
      (∀ q b' i, blockDisjoint (b', i, 1) (X, xo.eval, 2 * (n * n)) = true →
        st'.store.read q b' i = st.store.read q b' i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  have hXlt : X < st.store.size := by
    obtain ⟨len, hXsh, -⟩ := hX
    have := (Array.getElem?_eq_some_iff.mp hXsh).1
    rwa [Store.size_shape] at this
  have hprog : (eighSignBlock p mm (.const n) (.const F) A ao par po X xo).run =
      .seq (.alloc p 5 fun t => .alloc p (2 * (.const n * .const n)) fun W =>
        .alloc p (2 * (.const n * .const n)) fun V => (Builder.run do
          ins (.litIdx p ⟨t, 2⟩ (4 * .const n))
          ins (.bin p .div ⟨t, 0⟩ ⟨par, po⟩ ⟨t, 2⟩)
          ins (.un p .neg ⟨t, 4⟩ ⟨t, 0⟩)
          ins (.lit p ⟨t, 3⟩ 1)
          zhermScale p (.const n) A ao ⟨par, po + 1⟩ X xo
          newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩
          forRange (.const F) fun _ => ifThenElse p .eq ⟨t, 1⟩ ⟨t, 3⟩
            (do
              newtonSchulzStepBlock p mm (.const n) X xo W V ⟨t, 2⟩
              newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩)
            (pure ()))) .skip :=
    rfl
  rw [hprog, exec_seq_skip, exec_alloc] at h
  obtain ⟨st₁, h, e₁⟩ := Option.map_eq_some_iff.mp h
  rw [exec_alloc] at h
  obtain ⟨st₂, h, e₂⟩ := Option.map_eq_some_iff.mp h
  rw [exec_alloc] at h
  obtain ⟨st₃, h₃, e₃⟩ := Option.map_eq_some_iff.mp h
  clear h
  subst e₁ e₂ e₃
  have hlt : ∀ {β i : ℕ} {v : K}, st.store.read p β i = some v → β < st.store.size :=
    fun h => Store.lt_size_of_read_eq_some h
  have hplt := hlt hε
  have hAn : n = 0 ∨ st.store.size ≠ A := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exact Or.inl hn
    · exact Or.inr (Nat.ne_of_gt (hlt (hA ⟨0, hn⟩ ⟨0, hn⟩ ⟨0, Nat.zero_lt_two⟩)))
  have hA0 : pairLayout.Holds (((st.store.push (p, Array.replicate (IExp.eval 5) none)).push
      (p, Array.replicate (2 * (IExp.const n * IExp.const n)).eval none)).push
      (p, Array.replicate (2 * (IExp.const n * IExp.const n)).eval none)) p A ao.eval A₀ := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; exact fun i => i.elim0
    · exact hA.of_forall_read_eq fun i _ _ =>
        (read_push_push_push_and_shape (hlt (hA ⟨0, hn⟩ ⟨0, hn⟩ ⟨0, Nat.zero_lt_two⟩))).1
  obtain ⟨hX', hfr', hsh', hpos'⟩ := holds_of_exec_eighSignBody (toNat := toNat) (qrR := qrR)
    (unif := unif) (normal := normal) hmm p hflag n F hA0
    ((read_push_push_push_and_shape hplt).1.trans hε)
    ((read_push_push_push_and_shape hplt).1.trans hb) hXA hXp hAn (by omega)
    (by simp only [Array.size_push]; omega)
    (by simp only [Array.size_push]; omega) (by simp only [Array.size_push]; omega)
    (by omega) (by simp only [Array.size_push]; omega) (by simp only [Array.size_push]; omega)
    (h := h₃)
  have hsz : st₃.store.size = st.store.size + 3 := by
    rw [Store.size_eq_of_shape_eq hsh']; simp
  refine ⟨hX'.of_forall_read_eq fun i _ _ => read_pop_pop_pop (by omega), fun q b' i hb' => ?_,
    ?_, ?_⟩
  · rcases Nat.lt_or_ge b' st.store.size with hb'' | hb''
    · rw [read_pop_pop_pop (by omega), hfr' q b' i (by omega)
        (by simp only [Array.size_push]; omega)
        (by simp only [Array.size_push]; omega) hb', (read_push_push_push_and_shape hb'').1]
    · rw [Store.read_eq_none_of_size_le (by simp; omega), Store.read_eq_none_of_size_le hb'']
  · change Store.shape (Array.pop (Array.pop (Array.pop st₃.store))) = _
    rw [Store.shape_pop, Store.shape_pop, Store.shape_pop, hsh']
    simp [Store.shape]
  · exact hpos'

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
private theorem exists_map_eq_some {α β : Type} {o : Option α} {f : α → β} (h : ∃ a, o = some a) :
    ∃ b, o.map f = some b := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨f a, rfl⟩

omit [Inhabited K] in
private theorem exec_bind_of_seq (b : Builder P ι ℕ ℕ Unit) (S : Stmt P ι ℕ ℕ)
    (hb : ∀ k, ContT.run b k = .seq S (k ())) (f : Unit → Builder P ι ℕ ℕ Unit)
    (st : St P K C) : exec I (b >>= f).run st = (exec I b.run st).bind (exec I (f ()).run) :=
  exec_run_bind I hb f st

private theorem exists_exec_eighSignStep {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    {u : P → ℝ} {dec : P → K → ℝ} (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P)
    (hu : u p < 1)
    (n : ℕ) {X W V t : ℕ} {xo : IExp ℕ} {η : K} {st : St P K C} {S : Array (P × ℕ)}
    {A : Matrix (Fin n) (Fin n) (K × K)} (hA : pairLayout.Holds st.store p X xo.eval A)
    (hW : pairLayout.Holds st.store p W 0 (mmR A A)) (hη : st.store.read p t 0 = some η)
    (hone : st.store.read p t 3 = some (I.sem.toFloatMachine p toNat mmR qrR unif normal).one)
    (hlo : st.store.read p t 4 =
      some ((I.sem.toFloatMachine p toNat mmR qrR unif normal).neg η))
    (hWX : W ≠ X) (hVX : V ≠ X) (hWV : W ≠ V) (htX : t ≠ X) (htW : t ≠ W) (htV : t ≠ V)
    (hS : st.store.shape = S) (hWS : S[W]? = some (p, 2 * (n * n)))
    (hVS : S[V]? = some (p, 2 * (n * n))) (htS : S[t]? = some (p, 5)) :
    let M := I.sem.toFloatMachine p toNat mmR qrR unif normal
    ∃ st₁, exec I (Builder.run do
      newtonSchulzStepBlock p mm (.const n) X xo W V ⟨t, 2⟩
      newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩) st =
        some st₁ ∧
      pairLayout.Holds st₁.store p X xo.eval (newtonSchulzRounded M A) ∧
      pairLayout.Holds st₁.store p W 0 (mmR (newtonSchulzRounded M A) (newtonSchulzRounded M A)) ∧
      st₁.store.read p t 0 = some η ∧ st₁.store.read p t 3 = some M.one ∧
      st₁.store.read p t 4 = some (M.neg η) ∧
      st₁.store.read p t 1 = some
        (if newtonSchulzTest M η (newtonSchulzRounded M A) then M.zero else M.one) ∧
      st₁.store.shape = S := by
  intro M
  have hd : ∀ {b b' : ℕ} (o o' l l' : ℕ), b ≠ b' → blockDisjoint (b, o, l) (b', o', l') = true :=
    fun _ _ _ _ h => by simp [blockDisjoint, h]
  have hstep : ∀ (f : Unit → Builder P ι ℕ ℕ Unit) (σ : St P K C),
      exec I (newtonSchulzStepBlock p mm (.const n) X xo W V ⟨t, 2⟩ >>= f).run σ =
        (exec I (newtonSchulzStepBlock p mm (.const n) X xo W V ⟨t, 2⟩).run σ).bind
          (exec I (f ()).run) := by
    unfold newtonSchulzStepBlock
    exact exec_run_bind_bind (exec_bind_of_seq _ _ fun _ => rfl) (exec_run_bind_bind
      (exec_bind_of_seq _ _ fun _ => rfl) (exec_run_bind_bind (exec_bind_of_seq _ _ fun _ => rfl)
        (exec_run_bind_bind (exec_bind_of_seq _ _ fun _ => rfl) (exec_run_bind_bind
          (exec_bind_of_seq _ _ fun _ => rfl) (exec_bind_of_seq _ _ fun _ => rfl)))))
  have hsh : ∀ {σ : St P K C} {b : ℕ} {l : ℕ}, σ.store.shape = S → S[b]? = some (p, l) →
      σ.store.shape[b]? = some (p, l) := fun h h' => by rw [h]; exact h'
  obtain ⟨σ, hσ⟩ := exists_exec_newtonSchulzStepBlock hmm hsem p hu n (c := ⟨t, 2⟩) hA hW hWX
    hVX hWV htW htV (hd _ _ _ _ htX) ⟨_, hsh hS hVS, le_rfl⟩
    (Store.exists_write_eq_some_of_getElem?_shape default (hsh hS htS) (by norm_num))
  obtain ⟨hXσ, hfrσ, hshσ, -⟩ := holds_of_exec_newtonSchulzStepBlock (toNat := toNat)
    (qrR := qrR) (unif := unif) (normal := normal) hmm p n hA hW hWX hVX hWV htW htV
    (hd _ _ _ _ htX) hσ
  have hrσ : ∀ i, i ≠ 2 → σ.store.read p t i = st.store.read p t i := fun i hi =>
    hfrσ p t i htW htV (hd _ _ _ _ htX) (blockDisjoint_cell_of_ne hi)
  have hSσ := hshσ.trans hS
  obtain ⟨σ₁, h₁⟩ := exists_exec_newtonSchulzTestBlock hmm hsem p n (one := ⟨t, 3⟩)
    (lo := ⟨t, 4⟩) (hi := ⟨t, 0⟩) (f := ⟨t, 1⟩) hXσ ((hrσ 3 (by omega)).trans hone)
    ((hrσ 4 (by omega)).trans hlo) ((hrσ 0 (by omega)).trans hη) hWX hVX hWV
    (by simp [htW, htV]) (hd _ _ _ _ htX) (by simp [blockDisjoint]) (by simp [blockDisjoint])
    ⟨_, hsh hSσ hWS, le_rfl⟩ ⟨_, hsh hSσ hVS, le_rfl⟩
    (Store.exists_write_eq_some_of_getElem?_shape default (hsh hSσ htS) (by norm_num))
  obtain ⟨hW₁, -, hf₁, hfr₁, hsh₁, -⟩ := holds_of_exec_newtonSchulzTestBlock (toNat := toNat)
    (qrR := qrR) (unif := unif) (normal := normal) hmm p n (one := ⟨t, 3⟩) (lo := ⟨t, 4⟩)
    (hi := ⟨t, 0⟩) (f := ⟨t, 1⟩) hXσ ((hrσ 3 (by omega)).trans hone)
    ((hrσ 4 (by omega)).trans hlo) ((hrσ 0 (by omega)).trans hη) hWX hVX hWV
    (by simp [htW, htV]) (hd _ _ _ _ htX) (by simp [blockDisjoint]) (by simp [blockDisjoint]) h₁
  have hr₁ : ∀ i, i ≠ 1 → i ≠ 2 → σ₁.store.read p t i = st.store.read p t i := fun i h1 h2 =>
    (hfr₁ p t i htW htV (blockDisjoint_cell_of_ne h1)).trans (hrσ i h2)
  exact ⟨σ₁, by rw [hstep, hσ, Option.bind_some]; exact h₁,
    hXσ.of_forall_read_eq fun i _ _ => hfr₁ _ _ _ hWX.symm hVX.symm (hd _ _ _ _ htX.symm),
    hW₁, (hr₁ 0 (by omega) (by omega)).trans hη, (hr₁ 3 (by omega) (by omega)).trans hone,
    (hr₁ 4 (by omega) (by omega)).trans hlo, hf₁, hsh₁.trans hSσ⟩

private theorem exists_exec_eighSignLoop {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    {u : P → ℝ} {dec : P → K → ℝ} (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P)
    (hu : u p < 1)
    (n : ℕ) {X W V t : ℕ} {xo : IExp ℕ} {η : K} {S : Array (P × ℕ)}
    (hz : dec p (I.sem.toFloatMachine p toNat mmR qrR unif normal).zero ≠
      dec p (I.sem.toFloatMachine p toNat mmR qrR unif normal).one)
    (hWX : W ≠ X) (hVX : V ≠ X) (hWV : W ≠ V) (htX : t ≠ X) (htW : t ≠ W) (htV : t ≠ V)
    (hWS : S[W]? = some (p, 2 * (n * n))) (hVS : S[V]? = some (p, 2 * (n * n)))
    (htS : S[t]? = some (p, 5)) (m : ℕ) :
    let M := I.sem.toFloatMachine p toNat mmR qrR unif normal
    ∀ (st : St P K C) (A : Matrix (Fin n) (Fin n) (K × K)),
      st.store.shape = S → pairLayout.Holds st.store p X xo.eval A →
      pairLayout.Holds st.store p W 0 (mmR A A) → st.store.read p t 0 = some η →
      st.store.read p t 3 = some M.one → st.store.read p t 4 = some (M.neg η) →
      st.store.read p t 1 = some (if newtonSchulzTest M η A then M.zero else M.one) →
      ∃ st', exec I (.loop (.const m) fun _ => (ifThenElse (ι := ι) p .eq ⟨t, 1⟩ ⟨t, 3⟩ (do
        newtonSchulzStepBlock p mm (.const n) X xo W V ⟨t, 2⟩
        newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩)
          (pure ())).run) st = some st' := by
  intro M
  induction m with
  | zero =>
    intro st _ _ _ _ _ _ _ _
    exact ⟨st, by simp [exec_loop, IExp.eval]⟩
  | succ m ih =>
    intro st A hS hA hW hη hone hlo hf
    rw [exec_loop]
    simp only [IExp.eval, List.range_succ_eq_map, List.foldlM_cons, List.foldlM_map]
    change ∃ st', (exec I (.seq (.ite p .eq ⟨t, 1⟩ ⟨t, 3⟩ _ _) .skip) st).bind _ = some st'
    rw [exec_seq_skip, exec_ite]
    by_cases ht : newtonSchulzTest M η A = true
    · have hz' : (dec p M.zero = dec p M.one) = False := eq_false hz
      simp only [cmpStep, IExp.eval, hf, if_pos ht, hone, Option.bind_some, hsem.cmp_eq,
        Option.map_some, hz', decide_false, Bool.false_eq_true, if_false]
      change ∃ st', (exec I .skip _).bind _ = some st'
      rw [exec_skip, Option.bind_some]
      obtain ⟨st', h'⟩ := ih { st with cnt := st.cnt + I.charge (.cmp p) } A hS hA hW hη hone
        hlo hf
      rw [exec_loop] at h'
      exact ⟨st', h'⟩
    · simp only [cmpStep, IExp.eval, hf, if_neg ht, hone, Option.bind_some, hsem.cmp_eq,
        Option.map_some, decide_true, if_true]
      obtain ⟨σ₁, h₁, hX₁, hW₁, hη₁, hone₁, hlo₁, hf₁, hsh₁⟩ :=
        exists_exec_eighSignStep hmm hsem p hu n
        (st := { st with cnt := st.cnt + I.charge (.cmp p) }) hA hW hη hone hlo hWX hVX hWV htX
        htW htV hS hWS hVS htS
      rw [h₁, Option.bind_some]
      obtain ⟨st', h'⟩ := ih σ₁ _ hsh₁ hX₁ hW₁ hη₁ hone₁ hlo₁ hf₁
      rw [exec_loop] at h'
      exact ⟨st', h'⟩

private theorem exists_exec_eighSignTail {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    {u : P → ℝ} {dec : P → K → ℝ} (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P)
    (hu : u p < 1)
    (n F : ℕ) {A par X t W V : ℕ} {ao po xo : IExp ℕ} {σ : St P K C} {S : Array (P × ℕ)}
    {A₀ : Matrix (Fin n) (Fin n) (K × K)} {b η : K}
    (hA : pairLayout.Holds σ.store p A ao.eval A₀)
    (hb : σ.store.read p par (po.eval + 1) = some b) (hb0 : dec p b ≠ 0)
    (hXA : blockDisjoint (X, xo.eval, 2 * (n * n)) (A, ao.eval, 2 * (n * n)) = true)
    (hXp : blockDisjoint (X, xo.eval, 2 * (n * n)) (par, po.eval, 2) = true)
    (hX : ∃ len, S[X]? = some (p, len) ∧ xo.eval + 2 * (n * n) ≤ len)
    (hη : σ.store.read p t 0 = some η)
    (hone : σ.store.read p t 3 = some (I.sem.toFloatMachine p toNat mmR qrR unif normal).one)
    (hlo : σ.store.read p t 4 =
      some ((I.sem.toFloatMachine p toNat mmR qrR unif normal).neg η))
    (hz : dec p (I.sem.toFloatMachine p toNat mmR qrR unif normal).zero ≠
      dec p (I.sem.toFloatMachine p toNat mmR qrR unif normal).one)
    (hWX : W ≠ X) (hVX : V ≠ X) (hWV : W ≠ V) (htX : t ≠ X) (htW : t ≠ W) (htV : t ≠ V)
    (hS : σ.store.shape = S) (hWS : S[W]? = some (p, 2 * (n * n)))
    (hVS : S[V]? = some (p, 2 * (n * n))) (htS : S[t]? = some (p, 5)) :
    ∃ st', exec I (Builder.run do
      zhermScale p (.const n) A ao ⟨par, po + 1⟩ X xo
      newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩
      forRange (.const F) fun _ => ifThenElse p .eq ⟨t, 1⟩ ⟨t, 3⟩
        (do
          newtonSchulzStepBlock p mm (.const n) X xo W V ⟨t, 2⟩
          newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩)
        (pure ())) σ =
        some st' := by
  have hd : ∀ {b b' : ℕ} (o o' l l' : ℕ), b ≠ b' → blockDisjoint (b, o, l) (b', o', l') = true :=
    fun _ _ _ _ h => by simp [blockDisjoint, h]
  have hsh : ∀ {σ' : St P K C} {b : ℕ} {l : ℕ}, σ'.store.shape = S → S[b]? = some (p, l) →
      σ'.store.shape[b]? = some (p, l) := fun h h' => by rw [h]; exact h'
  have hcY : blockDisjoint (par, po.eval + 1, 1) (X, xo.eval, 2 * (n * n)) = true := by
    simp only [blockDisjoint, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hXp ⊢
    omega
  obtain ⟨σ₅, h₅⟩ := exists_exec_zhermScale (I := I) (ι := ι) p n (X := A) (xo := ao)
    (c := ⟨par, po + 1⟩) (Y := X) (yo := xo) hA hb hXA hcY hsem hb0 (by rw [hS]; exact hX)
  obtain ⟨hX₅, hfr₅, hsh₅, -⟩ := holds_of_exec_zhermScale (toNat := toNat) (mmR := mmR)
    (qrR := qrR) (unif := unif) (normal := normal) p n hA hb hXA hcY h₅
  have htestc : ∀ (f : Unit → Builder P ι ℕ ℕ Unit) (σ' : St P K C),
      exec I (newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩
        >>= f).run σ' = (exec I (newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩
          ⟨t, 0⟩ ⟨t, 1⟩).run σ').bind (exec I (f ()).run) := by
    unfold newtonSchulzTestBlock
    exact exec_run_bind_bind (exec_bind_of_seq _ _ fun _ => rfl) (exec_run_bind_bind
      (exec_bind_of_seq _ _ fun _ => rfl) (exec_bind_of_seq _ _ fun _ => rfl))
  rw [exec_bind_of_seq (zhermScale (ι := ι) p (.const n) A ao ⟨par, po + 1⟩ X xo) _ (fun _ => rfl),
    h₅, Option.bind_some, htestc]
  have hr₅ : ∀ i, σ₅.store.read p t i = σ.store.read p t i := fun i => hfr₅ p t i (hd _ _ _ _ htX)
  have hS₅ := hsh₅.trans hS
  obtain ⟨σ₆, h₆⟩ := exists_exec_newtonSchulzTestBlock hmm hsem p n (one := ⟨t, 3⟩)
    (lo := ⟨t, 4⟩) (hi := ⟨t, 0⟩) (f := ⟨t, 1⟩) hX₅ ((hr₅ 3).trans hone) ((hr₅ 4).trans hlo)
    ((hr₅ 0).trans hη) hWX hVX hWV (by simp [htW, htV]) (hd _ _ _ _ htX)
    (by simp [blockDisjoint]) (by simp [blockDisjoint]) ⟨_, hsh hS₅ hWS, le_rfl⟩
    ⟨_, hsh hS₅ hVS, le_rfl⟩
    (Store.exists_write_eq_some_of_getElem?_shape default (hsh hS₅ htS) (by norm_num))
  obtain ⟨hW₆, -, hf₆, hfr₆, hsh₆, -⟩ := holds_of_exec_newtonSchulzTestBlock (toNat := toNat)
    (qrR := qrR) (unif := unif) (normal := normal) hmm p n (one := ⟨t, 3⟩) (lo := ⟨t, 4⟩)
    (hi := ⟨t, 0⟩) (f := ⟨t, 1⟩) hX₅ ((hr₅ 3).trans hone) ((hr₅ 4).trans hlo)
    ((hr₅ 0).trans hη) hWX hVX hWV (by simp [htW, htV]) (hd _ _ _ _ htX)
    (by simp [blockDisjoint]) (by simp [blockDisjoint]) h₆
  rw [h₆, Option.bind_some]
  change ∃ st', exec I (.seq (.loop _ _) .skip) σ₆ = some st'
  rw [exec_seq_skip]
  have hr₆ : ∀ i, i ≠ 1 → σ₆.store.read p t i = σ.store.read p t i := fun i h =>
    (hfr₆ p t i htW htV (blockDisjoint_cell_of_ne h)).trans (hr₅ i)
  exact exists_exec_eighSignLoop hmm hsem p hu n hz hWX hVX hWV htX htW htV hWS hVS htS F σ₆ _
    (hsh₆.trans hS₅)
    (hX₅.of_forall_read_eq fun i _ _ => hfr₆ _ _ _ hWX.symm hVX.symm (hd _ _ _ _ htX.symm))
    hW₆ ((hr₆ 0 (by omega)).trans hη) ((hr₆ 3 (by omega)).trans hone)
    ((hr₆ 4 (by omega)).trans hlo) hf₆

include toNat qrR unif normal in
private theorem exists_exec_eighSignBody {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    {u : P → ℝ} {dec : P → K → ℝ} (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hlit : IsExactIntLit dec I.sem 1) (p : P) (hu : u p < 1) (n F : ℕ) (hn : 0 < n)
    {A par X t W V : ℕ} {ao po xo : IExp ℕ} {st : St P K C} {A₀ : Matrix (Fin n) (Fin n) (K × K)}
    {ε b : K} (hA : pairLayout.Holds st.store p A ao.eval A₀)
    (hε : st.store.read p par po.eval = some ε) (hb : st.store.read p par (po.eval + 1) = some b)
    (hb0 : dec p b ≠ 0)
    (hXA : blockDisjoint (X, xo.eval, 2 * (n * n)) (A, ao.eval, 2 * (n * n)) = true)
    (hXp : blockDisjoint (X, xo.eval, 2 * (n * n)) (par, po.eval, 2) = true)
    (hX : ∃ len, st.store.shape[X]? = some (p, len) ∧ xo.eval + 2 * (n * n) ≤ len)
    (htA : t ≠ A) (htp : t ≠ par)
    (hWX : W ≠ X) (hVX : V ≠ X) (hWV : W ≠ V) (htX : t ≠ X) (htW : t ≠ W) (htV : t ≠ V)
    (hWS : st.store.shape[W]? = some (p, 2 * (n * n)))
    (hVS : st.store.shape[V]? = some (p, 2 * (n * n))) (htS : st.store.shape[t]? = some (p, 5)) :
    ∃ st', exec I (Builder.run do
      ins (.litIdx p ⟨t, 2⟩ (4 * .const n))
      ins (.bin p .div ⟨t, 0⟩ ⟨par, po⟩ ⟨t, 2⟩)
      ins (.un p .neg ⟨t, 4⟩ ⟨t, 0⟩)
      ins (.lit p ⟨t, 3⟩ 1)
      zhermScale p (.const n) A ao ⟨par, po + 1⟩ X xo
      newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩
      forRange (.const F) fun _ => ifThenElse p .eq ⟨t, 1⟩ ⟨t, 3⟩
        (do
          newtonSchulzStepBlock p mm (.const n) X xo W V ⟨t, 2⟩
          newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩)
        (pure ())) st =
        some st' := by
  have hd : ∀ {b b' : ℕ} (o o' l l' : ℕ), b ≠ b' → blockDisjoint (b, o, l) (b', o', l') = true :=
    fun _ _ _ _ h => by simp [blockDisjoint, h]
  change ∃ st', exec I (.seq (.instr _) (.seq (.instr _) (.seq (.instr _) (.seq (.instr _)
    (.seq (.named _ _ _) (newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩
      ⟨t, 1⟩ >>= fun _ => forRange (.const F) fun _ => ifThenElse p .eq ⟨t, 1⟩ ⟨t, 3⟩
        (do
          newtonSchulzStepBlock p mm (.const n) X xo W V ⟨t, 2⟩
          newtonSchulzTestBlock p mm (.const n) X xo W V ⟨t, 3⟩ ⟨t, 4⟩ ⟨t, 0⟩ ⟨t, 1⟩)
        (pure ())).run)))))
    st = some st'
  -- the literal `4n`, the threshold, its negation and the literal `1`
  obtain ⟨v, hv⟩ := hsem.lit_ok p (((4 * IExp.const n).eval : ℕ) : ℚ) trivial
  have hv0 : dec p v ≠ 0 := by
    obtain ⟨δ, hδ, hdec⟩ := hsem.lit_err p _ v hv
    rw [hdec]
    refine mul_ne_zero (by simp; omega) ?_
    linarith [(abs_lt.mp (hδ.trans_lt hu)).1]
  obtain ⟨s₁, hs₁⟩ := Store.exists_write_eq_some_of_getElem?_shape v htS (show 2 < 5 by norm_num)
  obtain ⟨w, hw⟩ := hsem.bin_ok p .div ε v trivial (fun _ => hv0) trivial
  obtain ⟨s₂, hs₂⟩ := Store.exists_write_eq_some_of_getElem?_shape w
    (by rw [Store.shape_of_write_eq_some hs₁]; exact htS) (show 0 < 5 by norm_num)
  obtain ⟨w', hw', -⟩ := hsem.neg p w
  obtain ⟨s₃, hs₃⟩ := Store.exists_write_eq_some_of_getElem?_shape w'
    (by rw [Store.shape_of_write_eq_some hs₂, Store.shape_of_write_eq_some hs₁]; exact htS)
    (show 4 < 5 by norm_num)
  obtain ⟨o, ho, ho1⟩ := hlit p 1 le_rfl
  have ho' : I.sem.lit p 1 = some o := by simpa using ho
  obtain ⟨s₄, hs₄⟩ := Store.exists_write_eq_some_of_getElem?_shape o
    (by rw [Store.shape_of_write_eq_some hs₃, Store.shape_of_write_eq_some hs₂,
      Store.shape_of_write_eq_some hs₁]; exact htS) (show 3 < 5 by norm_num)
  rw [exec_seq_instr_litIdx I (dst := ⟨t, 2⟩) hv hs₁,
    exec_seq_instr_bin I (dst := ⟨t, 0⟩) (x := ⟨par, po⟩) (y := ⟨t, 2⟩)
      ((Store.read_of_write_eq_some_of_ne hs₁ (Or.inl htp.symm)).trans hε)
      (Store.read_of_write_eq_some hs₁) hw hs₂,
    exec_seq_instr_un I (dst := ⟨t, 4⟩) (x := ⟨t, 0⟩) (Store.read_of_write_eq_some hs₂) hw' hs₃,
    exec_seq_instr_lit I (dst := ⟨t, 3⟩) ho' hs₄]
  -- the machine's values of the cells
  have hM4 : (I.sem.toFloatMachine p toNat mmR qrR unif normal).ofNat (4 * n) = v := by
    change (I.sem.lit p (((4 * IExp.const n).eval : ℕ) : ℚ)).getD default = v
    rw [hv]; rfl
  have hMη : (I.sem.toFloatMachine p toNat mmR qrR unif normal).div ε
      ((I.sem.toFloatMachine p toNat mmR qrR unif normal).ofNat (4 * n)) = w := by
    rw [hM4]; change (I.sem.bin p .div ε v).getD default = w; rw [hw]; rfl
  have hMneg : (I.sem.toFloatMachine p toNat mmR qrR unif normal).neg w = w' := by
    change (I.sem.un p .neg w).getD default = w'; rw [hw']; rfl
  have hMone : (I.sem.toFloatMachine p toNat mmR qrR unif normal).one = o := by
    change (I.sem.lit p 1).getD default = o; rw [ho']; rfl
  obtain ⟨z, hz⟩ := hsem.lit_ok p 0 trivial
  have hMzero : (I.sem.toFloatMachine p toNat mmR qrR unif normal).zero = z := by
    change (I.sem.lit p 0).getD default = z; rw [hz]; rfl
  have hdz : dec p z = 0 := by
    obtain ⟨δ, -, h⟩ := hsem.lit_err p 0 z hz
    simpa using h
  have hfr₄ : ∀ q b i, b ≠ t → s₄.read q b i = st.store.read q b i := fun q b i h => by
    rw [Store.read_of_write_eq_some_of_ne hs₄ (Or.inl h), Store.read_of_write_eq_some_of_ne hs₃
      (Or.inl h), Store.read_of_write_eq_some_of_ne hs₂ (Or.inl h),
      Store.read_of_write_eq_some_of_ne hs₁ (Or.inl h)]
  have hsh₄ : s₄.shape = st.store.shape := by
    rw [Store.shape_of_write_eq_some hs₄, Store.shape_of_write_eq_some hs₃,
      Store.shape_of_write_eq_some hs₂, Store.shape_of_write_eq_some hs₁]
  exact exists_exec_eighSignTail hmm hsem p hu n F (S := st.store.shape) (η := w)
    (hA.of_forall_read_eq fun i _ _ => hfr₄ _ _ _ htA.symm) ((hfr₄ _ _ _ htp.symm).trans hb) hb0
    hXA hXp hX (by
      rw [Store.read_of_write_eq_some_of_ne hs₄ (Or.inr (by norm_num)),
        Store.read_of_write_eq_some_of_ne hs₃ (Or.inr (by norm_num))]
      exact Store.read_of_write_eq_some hs₂)
    (by rw [hMone]; exact Store.read_of_write_eq_some hs₄)
    (by rw [hMneg, Store.read_of_write_eq_some_of_ne hs₄ (Or.inr (by norm_num))]
        exact Store.read_of_write_eq_some hs₃)
    (by rw [hMzero, hMone, hdz, ho1]; norm_num) hWX hVX hWV htX htW htV hsh₄ hWS hVS htS

/-- The sign step always succeeds under the standard model at $u$ with every value in range,
$u(p) < 1$ and an exact literal $1$, if kernel `mm` of `I` is the routine `mmR` on interleaved
pairs, $n \ge 1$, $b$ decodes to a nonzero value and the output block at `X` (tag `p`) has $2n^2$
cells (hypotheses on the inputs as `NLAlib.holds_of_exec_eighSignBlock`): unlike the pilot's
`whileFuel` loop, the bounded loop does not fail when no iterate passes the test. No printed
source. -/
theorem exists_exec_eighSignBlock {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    {u : P → ℝ} {dec : P → K → ℝ} (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hlit : IsExactIntLit dec I.sem 1) (p : P) (hu : u p < 1) (n F : ℕ) (hn : 0 < n)
    {A par X : ℕ} {ao po xo : IExp ℕ} {st : St P K C} {A₀ : Matrix (Fin n) (Fin n) (K × K)}
    {ε b : K} (hA : pairLayout.Holds st.store p A ao.eval A₀)
    (hε : st.store.read p par po.eval = some ε) (hb : st.store.read p par (po.eval + 1) = some b)
    (hb0 : dec p b ≠ 0)
    (hXA : blockDisjoint (X, xo.eval, 2 * (n * n)) (A, ao.eval, 2 * (n * n)) = true)
    (hXp : blockDisjoint (X, xo.eval, 2 * (n * n)) (par, po.eval, 2) = true)
    (hX : ∃ len, st.store.shape[X]? = some (p, len) ∧ xo.eval + 2 * (n * n) ≤ len) :
    ∃ st', exec I (eighSignBlock p mm (.const n) (.const F) A ao par po X xo).run st =
      some st' := by
  have hlt : ∀ {β i : ℕ} {v : K}, st.store.read p β i = some v → β < st.store.size :=
    fun h => Store.lt_size_of_read_eq_some h
  have hAlt := hlt (hA ⟨0, hn⟩ ⟨0, hn⟩ ⟨0, Nat.zero_lt_two⟩)
  have hplt := hlt hε
  have hXlt : X < st.store.size := by
    obtain ⟨len, hXsh, -⟩ := hX
    have := (Array.getElem?_eq_some_iff.mp hXsh).1
    rwa [Store.size_shape] at this
  change ∃ st', exec I (.seq (.alloc p 5 _) .skip) st = some st'
  rw [exec_seq_skip, exec_alloc]
  refine exists_map_eq_some ?_
  change ∃ a, exec I (.alloc p _ _) _ = some a
  rw [exec_alloc]
  refine exists_map_eq_some ?_
  change ∃ a, exec I (.alloc p _ _) _ = some a
  rw [exec_alloc]
  refine exists_map_eq_some ?_
  obtain ⟨htS, hWS, hVS⟩ := getElem?_shape_push_push_push st.store p (IExp.eval 5)
    (IExp.eval (2 * (.const n * .const n))) (IExp.eval (2 * (.const n * .const n)))
  have hP : ∀ {β : ℕ} (q : P) (i : ℕ), β < st.store.size → _ := fun {β} q i h =>
    read_push_push_push_and_shape (s := st.store) (p := p) (q := q) (a := IExp.eval 5)
      (b := (2 * (IExp.const n * .const n)).eval) (c := (2 * (IExp.const n * .const n)).eval)
      (i := i) (β := β) h
  exact exists_exec_eighSignBody (toNat := fun _ => 0) (Su := Unit) (unif := fun x _ => x)
    (Sg := Unit) (normal := fun _ => default) (qrR := fun A => (fun _ _ => default, A))
    hmm hsem hlit p hu n F
    hn
    (hA.of_forall_read_eq fun i _ _ => (hP p i hAlt).1) ((hP p _ hplt).1.trans hε)
    ((hP p _ hplt).1.trans hb) hb0 hXA hXp (by rw [(hP p 0 hXlt).2]; exact hX)
    (by omega) (by omega) (by simp only [Array.size_push]; omega)
    (by simp only [Array.size_push]; omega) (by simp only [Array.size_push]; omega)
    (by omega) (by simp only [Array.size_push]; omega) (by simp only [Array.size_push]; omega)
    (by simpa using hWS) (by simpa using hVS) (by simpa using htS)

end NLAlib
