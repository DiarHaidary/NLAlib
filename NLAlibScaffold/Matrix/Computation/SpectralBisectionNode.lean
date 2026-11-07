/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SpectralBisectionProgramTree
public import NLAlib.Matrix.Computation.SpectralBisectionTape
public import NLAlibScaffold.Computation.KernelCongr
public import NLAlibScaffold.Matrix.Computation.NewtonSchulzSignProgram
public import NLAlibScaffold.Matrix.Computation.PairKernels

/-!
# The node step of the spectral bisection program (scaffold)

Statements for a new file `NLAlib/Matrix/Computation/SpectralBisectionNode.lean` (stage COMPDYN
S2b, design note `docs/design/Computation-EighProgram.md`, §4): the blocks of the node step of
`NLAlib.eighProg` compute the matching operations of `NLAlib.eighStep` on the machine of the
semantics (`NLAlib.Computation.ScalarSem.toFloatMachine`, `NLAlib.eighTapeMachine`), and succeed
under the standard model. Each value statement is a partial equality: under kernels that are
routines on pairs and a semantics that decides flags, a successful run writes exactly the machine's
value, with no contract on the rounding. The pilot's statements of stage S1c/S1d
(`NLAlibScaffold/Matrix/Computation/{PairKernels,NewtonSchulzSignProgram}.lean`) are cited at
constant sizes and moved to index expressions by `NLAlibScaffold/Computation/KernelCongr.lean`.

## Main results

* `NLAlib.holds_of_exec_eighSignLoop`, `NLAlib.holds_of_exec_eighSignBlock`,
  `NLAlib.exists_exec_eighSignBlock`: the sign step with the shallow step limit.
* `NLAlib.holds_of_exec_eighLeafBlock`, `NLAlib.holds_of_exec_eighChildBlock`,
  `NLAlib.holds_of_exec_eighDeflateBlock`, `NLAlib.holds_of_exec_eighCompressBlock`,
  `NLAlib.holds_of_exec_eighSplitBlock`: the blocks.
* `NLAlib.holds_of_exec_eighNodeBlock`, `NLAlib.exists_exec_eighNodeBlock`: the node step computes
  `NLAlib.eighStep`, and succeeds.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {Su Sg : Type} {toNat : K → ℕ} {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}
  {unif : K → Su → K} {normal : Sg → K × K}

/-! ### The sign step with the shallow step limit -/

omit [Inhabited K] in
private theorem eighSign_comp {a b : Builder P ι ℕ ℕ Unit}
    (ha : ∀ (f : Unit → Builder P ι ℕ ℕ Unit) (st : St P K C),
      exec I (a >>= f).run st = (exec I a.run st).bind (exec I (f ()).run))
    (hb : ∀ (f : Unit → Builder P ι ℕ ℕ Unit) (st : St P K C),
      exec I (b >>= f).run st = (exec I b.run st).bind (exec I (f ()).run))
    (f : Unit → Builder P ι ℕ ℕ Unit) (st : St P K C) :
    exec I ((a >>= fun _ => b) >>= f).run st =
      (exec I (a >>= fun _ => b).run st).bind (exec I (f ()).run) := by
  change exec I (a >>= fun _ => b >>= f).run st = _
  rw [ha, ha]
  simp only [Option.bind_assoc]
  congr 1
  funext out
  exact hb f out

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
private theorem eighSign_disj {b i j : ℕ} (h : i ≠ j) :
    blockDisjoint (b, i, 1) (b, j, 1) = true := by
  unfold blockDisjoint
  rcases Nat.lt_or_gt_of_ne h with h | h
  · simp only [Bool.or_eq_true, decide_eq_true_eq]; exact Or.inl (Or.inr (by omega))
  · simp only [Bool.or_eq_true, decide_eq_true_eq]; exact Or.inr (by omega)

private theorem eighSign_body {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) (p : P) (n : ℕ)
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
    exact eighSign_comp (hsingle _ _ fun _ => rfl) (eighSign_comp (hsingle _ _ fun _ => rfl)
      (eighSign_comp (hsingle _ _ fun _ => rfl) (eighSign_comp (hsingle _ _ fun _ => rfl)
        (eighSign_comp (hsingle _ _ fun _ => rfl) (hsingle _ _ fun _ => rfl)))))
  rw [hstep] at h
  obtain ⟨σ, hσ, h₁⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hXσ, hfrσ, hshσ, hposσ⟩ := holds_of_exec_newtonSchulzStepBlock (toNat := toNat)
    (qrR := qrR) (unif := unif) (normal := normal) hmm p n hA hW hWX hVX hWV htW htV
    (hd _ _ _ _ htX) hσ
  have hrσ : ∀ i, i ≠ 2 → σ.store.read p t i = st.store.read p t i := fun i hi =>
    hfrσ p t i htW htV (hd _ _ _ _ htX) (eighSign_disj hi)
  obtain ⟨hW₁, -, hf₁, hfr₁, hsh₁, hpos₁⟩ := holds_of_exec_newtonSchulzTestBlock (toNat := toNat)
    (qrR := qrR) (unif := unif) (normal := normal) hmm p n (one := ⟨t, 3⟩) (lo := ⟨t, 4⟩)
    (hi := ⟨t, 0⟩) (f := ⟨t, 1⟩) hXσ ((hrσ 3 (by omega)).trans hone)
    ((hrσ 4 (by omega)).trans hlo) ((hrσ 0 (by omega)).trans hη) hWX hVX hWV
    (by simp [htW, htV]) (hd _ _ _ _ htX) (by simp [blockDisjoint]) (by simp [blockDisjoint]) h₁
  have hr₁ : ∀ i, i ≠ 1 → i ≠ 2 → st₁.store.read p t i = st.store.read p t i := fun i h1 h2 =>
    (hfr₁ p t i htW htV (eighSign_disj h1)).trans (hrσ i h2)
  refine ⟨hXσ.of_forall_read_eq fun i _ _ => hfr₁ _ _ _ hWX.symm hVX.symm (hd _ _ _ _ htX.symm),
    hW₁, (hr₁ 0 (by omega) (by omega)).trans hη, (hr₁ 3 (by omega) (by omega)).trans hone,
    (hr₁ 4 (by omega) (by omega)).trans hlo, hf₁, fun q b i hbt hbW hbV hbX => ?_,
    hsh₁.trans hshσ, hpos₁.trans hposσ⟩
  exact (hfr₁ q b i hbW hbV (hd _ _ _ _ hbt)).trans (hfrσ q b i hbW hbV hbX (hd _ _ _ _ hbt))

/-- **The bounded Newton–Schulz loop computes `NLAlib.newtonSchulzLoop`**: if kernel `mm` of `I`
is the routine `mmR` on interleaved pairs and the semantics decides flags at `p`, a successful run
of the loop of `NLAlib.eighSignBlock` with $F$ iterations, from a state whose block at `X` holds
$\mathbf{A}$, whose scratch buffer `W` holds $\mathrm{mm}(\mathbf{A}, \mathbf{A})$, whose cells
$0$, $3$, $4$ of the scratch buffer `t` hold $\eta$, the machine's one and $-\eta$, and whose cell
$1$ holds the flag of the test of $\mathbf{A}$, ends with the block at `X` holding
`NLAlib.newtonSchulzLoop M η F A` ($M$ the machine of the semantics at `p` with product `mmR`);
every cell outside the block at `X` and the buffers `t`, `W`, `V` is unchanged, the store shape and
the tape positions too. No printed source.
Proof: induction on $F$ generalizing the state and $\mathbf{A}$; `NLAlib.Computation.exec_run_bind`,
`NLAlib.Computation.exec_loop` and `List.range_succ_eq_map` peel the first iteration, whose
comparison (`NLAlib.Computation.exec_ite`, `NLAlib.Computation.cmpStep`) reads the flag and the
stored one: by `hflag` (`NLAlib.Computation.ScalarSem.DecidesFlags`) it is false exactly when the
flag is the machine's zero, that is when the test passes; then every later iteration skips too
(the state is unchanged, `NLAlib.newtonSchulzLoop` returns $\mathbf{A}$ at every step limit when the
test passes), and otherwise `NLAlib.holds_of_exec_newtonSchulzStepBlock` and
`NLAlib.holds_of_exec_newtonSchulzTestBlock` (pilot) re-establish the hypotheses for
`NLAlib.newtonSchulzRounded M A` and the induction hypothesis applies. M, about 70 lines. -/
theorem holds_of_exec_eighSignLoop {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) (p : P)
    (hflag : I.sem.DecidesFlags p) (n F : ℕ) {X W V t : ℕ} {xo : IExp ℕ} {η : K}
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
        eighSign_body hmm p n (st := { st with cnt := st.cnt + I.charge (.cmp p) }) hA hW hη
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
private theorem eighSignH_comp {a b : Builder P ι ℕ ℕ Unit}
    (ha : ∀ (f : Unit → Builder P ι ℕ ℕ Unit) (st : St P K C),
      exec I (a >>= f).run st = (exec I a.run st).bind (exec I (f ()).run))
    (hb : ∀ (f : Unit → Builder P ι ℕ ℕ Unit) (st : St P K C),
      exec I (b >>= f).run st = (exec I b.run st).bind (exec I (f ()).run))
    (f : Unit → Builder P ι ℕ ℕ Unit) (st : St P K C) :
    exec I ((a >>= fun _ => b) >>= f).run st =
      (exec I (a >>= fun _ => b).run st).bind (exec I (f ()).run) := by
  change exec I (a >>= fun _ => b >>= f).run st = _
  rw [ha, ha]
  simp only [Option.bind_assoc]
  congr 1
  funext out
  exact hb f out

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
private theorem eighSignH_disj {b i j : ℕ} (h : i ≠ j) :
    blockDisjoint (b, i, 1) (b, j, 1) = true := by
  unfold blockDisjoint
  rcases Nat.lt_or_gt_of_ne h with h | h
  · simp only [Bool.or_eq_true, decide_eq_true_eq]; exact Or.inl (Or.inr (by omega))
  · simp only [Bool.or_eq_true, decide_eq_true_eq]; exact Or.inr (by omega)

omit [Inhabited K] in
private theorem eighSignH_inv_litIdx {p : P} {dst : Cell ℕ ℕ} {e : IExp ℕ} {t : Stmt P ι ℕ ℕ}
    {s s₂ : St P K C} (h : exec I (.seq (.instr (.litIdx p dst e)) t) s = some s₂) :
    ∃ v s', I.sem.lit p (e.eval : ℚ) = some v ∧ s.store.write p dst.buf dst.idx.eval v = some s' ∧
      exec I t { s with store := s', cnt := s.cnt + I.charge (.lit p) } = some s₂ := by
  rw [exec_seq, exec_instr] at h
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨_, ⟨v, hv, s', hw, rfl⟩, rfl⟩, h⟩ := h
  exact ⟨v, s', hv, hw, h⟩

omit [Inhabited K] in
private theorem eighSignH_inv_lit {p : P} {dst : Cell ℕ ℕ} {q : ℚ} {t : Stmt P ι ℕ ℕ}
    {s s₂ : St P K C} (h : exec I (.seq (.instr (.lit p dst q)) t) s = some s₂) :
    ∃ v s', I.sem.lit p q = some v ∧ s.store.write p dst.buf dst.idx.eval v = some s' ∧
      exec I t { s with store := s', cnt := s.cnt + I.charge (.lit p) } = some s₂ := by
  rw [exec_seq, exec_instr] at h
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨_, ⟨v, hv, s', hw, rfl⟩, rfl⟩, h⟩ := h
  exact ⟨v, s', hv, hw, h⟩

omit [Inhabited K] in
private theorem eighSignH_inv_bin {p : P} {op : BinOp} {dst x y : Cell ℕ ℕ} {t : Stmt P ι ℕ ℕ}
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
private theorem eighSignH_inv_un {p : P} {u : UnOp} {dst x : Cell ℕ ℕ} {t : Stmt P ι ℕ ℕ}
    {s s₂ : St P K C} (h : exec I (.seq (.instr (.un p u dst x)) t) s = some s₂) :
    ∃ a v s', s.store.read p x.buf x.idx.eval = some a ∧ I.sem.un p u a = some v ∧
      s.store.write p dst.buf dst.idx.eval v = some s' ∧
      exec I t { s with store := s', cnt := s.cnt + I.charge (.un p u) } = some s₂ := by
  rw [exec_seq, exec_instr] at h
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨_, ⟨a, ha, v, hv, s', hw, rfl⟩, rfl⟩, h⟩ := h
  exact ⟨a, v, s', ha, hv, hw, h⟩

omit [AddMonoid C] [Inhabited K] in
private theorem eighSignH_pop3 {s : Store P K} {q : P} {b i : ℕ} (hb : b + 3 < s.size) :
    Store.read (Array.pop (Array.pop (Array.pop s))) q b i = s.read q b i := by
  rw [Store.read_pop_of_lt (by simp; omega), Store.read_pop_of_lt (by simp; omega),
    Store.read_pop_of_lt (by omega)]

omit [AddMonoid C] [Inhabited K] in
private theorem eighSignH_push3 {s : Store P K} {p q : P} {a b c β i : ℕ} (hβ : β < s.size) :
    Store.read (((s.push (p, Array.replicate a none)).push (p, Array.replicate b none)).push
      (p, Array.replicate c none)) q β i = s.read q β i := by
  rw [Store.read_push_of_lt (by simp; omega), Store.read_push_of_lt (by simp; omega),
    Store.read_push_of_lt hβ]

/-- The scaling, the first test and the loop of `NLAlib.eighSignBlock`, from the state after
the four instructions. -/
private theorem eighSignH_tail {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) (p : P)
    (hflag : I.sem.DecidesFlags p) (n F : ℕ) {A par X t W V : ℕ} {ao po xo : IExp ℕ}
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
    exact eighSignH_comp (fun f st => exec_run_bind I (fun _ => rfl) f st) (eighSignH_comp
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
    (hfr₆ p t i htW htV (eighSignH_disj h)).trans (hr₅ i)
  obtain ⟨hX', hfr', hsh', hpos'⟩ := holds_of_exec_eighSignLoop hmm p hflag n F
    (hX₅.of_forall_read_eq fun i _ _ => hfr₆ _ _ _ hWX.symm hVX.symm (hd _ _ _ _ htX.symm))
    hW₆ ((hr₆ 0 (by omega)).trans hη) ((hr₆ 3 (by omega)).trans hone)
    ((hr₆ 4 (by omega)).trans hlo) hf₆ hWX hVX hWV htX htW htV h
  refine ⟨hX', fun q b' i hbt hbW hbV hbX => ?_, hsh'.trans (hsh₆.trans hsh₅),
    hpos'.trans (hpos₆.trans hpos₅)⟩
  exact (hfr' q b' i hbt hbW hbV hbX).trans ((hfr₆ q b' i hbW hbV (hd _ _ _ _ hbt)).trans
    (hfr₅ q b' i hbX))

/-- The body of `NLAlib.eighSignBlock` inside its allocations. -/
private theorem eighSignH_setup {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) (p : P)
    (hflag : I.sem.DecidesFlags p) (n F : ℕ) {A par X t W V : ℕ} {ao po xo : IExp ℕ}
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
  obtain ⟨v, s₁, hv, hs₁, h⟩ := eighSignH_inv_litIdx h
  obtain ⟨a, c, w, s₂, ha, hc, hw, hs₂, h⟩ := eighSignH_inv_bin h
  obtain ⟨a', w', s₃, ha', hw', hs₃, h⟩ := eighSignH_inv_un h
  obtain ⟨o, s₄, ho, hs₄, h⟩ := eighSignH_inv_lit h
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
  obtain ⟨hX', hfr', hsh', hpos'⟩ := eighSignH_tail (toNat := toNat) (qrR := qrR) (unif := unif)
    (normal := normal) hmm p hflag n F (η := w)
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

/-- **The sign step computes `NLAlib.newtonSchulzSign`**: if kernel `mm` of `I` is the routine
`mmR` on interleaved pairs and the semantics decides flags at `p`, a successful run of
`NLAlib.eighSignBlock` at size $n$ and step limit $F$, from a state whose block at `A` holds the
stored $\mathbf{A}$ and whose cells `po`, `po + 1` of `par` hold $\varepsilon$ and $b$, with the
output block at `X` disjoint from both and in an existing buffer at tag `p` of at least $2n^2$
cells from `xo` (so not one of the block's scratch buffers, which are popped at the end), ends
with the output block holding `NLAlib.newtonSchulzSign M ε b F A` (the machine of the semantics at `p` with product `mmR`, for
every choice of its other black boxes); every cell outside the output block is unchanged, the store
shape and the tape positions too. No printed source.
Proof: as the pilot's `NLAlib.holds_of_exec_newtonSchulzSignProg` (scaffold), with the loop by
`NLAlib.holds_of_exec_eighSignLoop` in place of
`NLAlib.holds_of_exec_whileFuel_newtonSchulz`: the set-up (three
`NLAlib.Computation.exec_alloc`s, four instructions, `NLAlib.Computation.holds_of_exec_zhermScale`,
`NLAlib.holds_of_exec_newtonSchulzTestBlock`) gives its hypotheses, and its conclusion is
`NLAlib.newtonSchulzSign` by definition; the pops keep the output block and the frame
(`NLAlib.Computation.Store.read_pop_of_lt`, `NLAlib.Computation.Store.shape_pop`). M, about 80
lines. -/
theorem holds_of_exec_eighSignBlock {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) (p : P)
    (hflag : I.sem.DecidesFlags p) (n F : ℕ) {A par X : ℕ} {ao po xo : IExp ℕ}
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
        eighSignH_push3 (hlt (hA ⟨0, hn⟩ ⟨0, hn⟩ ⟨0, Nat.zero_lt_two⟩))
  obtain ⟨hX', hfr', hsh', hpos'⟩ := eighSignH_setup (toNat := toNat) (qrR := qrR) (unif := unif)
    (normal := normal) hmm p hflag n F hA0 ((eighSignH_push3 hplt).trans hε)
    ((eighSignH_push3 hplt).trans hb) hXA hXp hAn (by omega) (by simp only [Array.size_push]; omega)
    (by simp only [Array.size_push]; omega) (by simp only [Array.size_push]; omega)
    (by omega) (by simp only [Array.size_push]; omega) (by simp only [Array.size_push]; omega)
    (h := h₃)
  have hsz : st₃.store.size = st.store.size + 3 := by
    rw [Store.size_eq_of_shape_eq hsh']; simp
  refine ⟨hX'.of_forall_read_eq fun i _ _ => eighSignH_pop3 (by omega), fun q b' i hb' => ?_,
    ?_, ?_⟩
  · rcases Nat.lt_or_ge b' st.store.size with hb'' | hb''
    · rw [eighSignH_pop3 (by omega), hfr' q b' i (by omega) (by simp only [Array.size_push]; omega)
        (by simp only [Array.size_push]; omega) hb', eighSignH_push3 hb'']
    · rw [Store.read_eq_none_of_size_le (by simp; omega), Store.read_eq_none_of_size_le hb'']
  · change Store.shape (Array.pop (Array.pop (Array.pop st₃.store))) = _
    rw [Store.shape_pop, Store.shape_pop, Store.shape_pop, hsh']
    simp [Store.shape]
  · exact hpos'

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
private theorem eighSignE_map {α β : Type} {o : Option α} {f : α → β} (h : ∃ a, o = some a) :
    ∃ b, o.map f = some b := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨f a, rfl⟩

omit [Inhabited K] in
private theorem eighSignE_comp {a b : Builder P ι ℕ ℕ Unit}
    (ha : ∀ (f : Unit → Builder P ι ℕ ℕ Unit) (st : St P K C),
      exec I (a >>= f).run st = (exec I a.run st).bind (exec I (f ()).run))
    (hb : ∀ (f : Unit → Builder P ι ℕ ℕ Unit) (st : St P K C),
      exec I (b >>= f).run st = (exec I b.run st).bind (exec I (f ()).run))
    (f : Unit → Builder P ι ℕ ℕ Unit) (st : St P K C) :
    exec I ((a >>= fun _ => b) >>= f).run st =
      (exec I (a >>= fun _ => b).run st).bind (exec I (f ()).run) := by
  change exec I (a >>= fun _ => b >>= f).run st = _
  rw [ha, ha]
  simp only [Option.bind_assoc]
  congr 1
  funext out
  exact hb f out

omit [Inhabited K] in
private theorem eighSignE_single (b : Builder P ι ℕ ℕ Unit) (S : Stmt P ι ℕ ℕ)
    (hb : ∀ k, ContT.run b k = .seq S (k ())) (f : Unit → Builder P ι ℕ ℕ Unit)
    (st : St P K C) : exec I (b >>= f).run st = (exec I b.run st).bind (exec I (f ()).run) :=
  exec_run_bind I hb f st

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
private theorem eighSignE_disj {b i j : ℕ} (h : i ≠ j) :
    blockDisjoint (b, i, 1) (b, j, 1) = true := by
  unfold blockDisjoint
  rcases Nat.lt_or_gt_of_ne h with h | h
  · simp only [Bool.or_eq_true, decide_eq_true_eq]; exact Or.inl (Or.inr (by omega))
  · simp only [Bool.or_eq_true, decide_eq_true_eq]; exact Or.inr (by omega)

private theorem eighSignE_body {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) {u : P → ℝ}
    {dec : P → K → ℝ} (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (hu : u p < 1)
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
    exact eighSignE_comp (eighSignE_single _ _ fun _ => rfl) (eighSignE_comp
      (eighSignE_single _ _ fun _ => rfl) (eighSignE_comp (eighSignE_single _ _ fun _ => rfl)
        (eighSignE_comp (eighSignE_single _ _ fun _ => rfl) (eighSignE_comp
          (eighSignE_single _ _ fun _ => rfl) (eighSignE_single _ _ fun _ => rfl)))))
  have hsh : ∀ {σ : St P K C} {b : ℕ} {l : ℕ}, σ.store.shape = S → S[b]? = some (p, l) →
      σ.store.shape[b]? = some (p, l) := fun h h' => by rw [h]; exact h'
  obtain ⟨σ, hσ⟩ := exists_exec_newtonSchulzStepBlock hmm hsem p hu n (c := ⟨t, 2⟩) hA hW hWX
    hVX hWV htW htV (hd _ _ _ _ htX) ⟨_, hsh hS hVS, le_rfl⟩
    (Store.exists_write_eq_some_of_getElem?_shape default (hsh hS htS) (by norm_num))
  obtain ⟨hXσ, hfrσ, hshσ, -⟩ := holds_of_exec_newtonSchulzStepBlock (toNat := toNat)
    (qrR := qrR) (unif := unif) (normal := normal) hmm p n hA hW hWX hVX hWV htW htV
    (hd _ _ _ _ htX) hσ
  have hrσ : ∀ i, i ≠ 2 → σ.store.read p t i = st.store.read p t i := fun i hi =>
    hfrσ p t i htW htV (hd _ _ _ _ htX) (eighSignE_disj hi)
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
    (hfr₁ p t i htW htV (eighSignE_disj h1)).trans (hrσ i h2)
  exact ⟨σ₁, by rw [hstep, hσ, Option.bind_some]; exact h₁,
    hXσ.of_forall_read_eq fun i _ _ => hfr₁ _ _ _ hWX.symm hVX.symm (hd _ _ _ _ htX.symm),
    hW₁, (hr₁ 0 (by omega) (by omega)).trans hη, (hr₁ 3 (by omega) (by omega)).trans hone,
    (hr₁ 4 (by omega) (by omega)).trans hlo, hf₁, hsh₁.trans hSσ⟩

private theorem eighSignE_loop {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) {u : P → ℝ}
    {dec : P → K → ℝ} (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (hu : u p < 1)
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
      obtain ⟨σ₁, h₁, hX₁, hW₁, hη₁, hone₁, hlo₁, hf₁, hsh₁⟩ := eighSignE_body hmm hsem p hu n
        (st := { st with cnt := st.cnt + I.charge (.cmp p) }) hA hW hη hone hlo hWX hVX hWV htX
        htW htV hS hWS hVS htS
      rw [h₁, Option.bind_some]
      obtain ⟨st', h'⟩ := ih σ₁ _ hsh₁ hX₁ hW₁ hη₁ hone₁ hlo₁ hf₁
      rw [exec_loop] at h'
      exact ⟨st', h'⟩

private theorem eighSignE_tail {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) {u : P → ℝ}
    {dec : P → K → ℝ} (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (hu : u p < 1)
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
    exact eighSignE_comp (eighSignE_single _ _ fun _ => rfl) (eighSignE_comp
      (eighSignE_single _ _ fun _ => rfl) (eighSignE_single _ _ fun _ => rfl))
  rw [eighSignE_single (zhermScale (ι := ι) p (.const n) A ao ⟨par, po + 1⟩ X xo) _ (fun _ => rfl),
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
    (hfr₆ p t i htW htV (eighSignE_disj h)).trans (hr₅ i)
  exact eighSignE_loop hmm hsem p hu n hz hWX hVX hWV htX htW htV hWS hVS htS F σ₆ _
    (hsh₆.trans hS₅)
    (hX₅.of_forall_read_eq fun i _ _ => hfr₆ _ _ _ hWX.symm hVX.symm (hd _ _ _ _ htX.symm))
    hW₆ ((hr₆ 0 (by omega)).trans hη) ((hr₆ 3 (by omega)).trans hone)
    ((hr₆ 4 (by omega)).trans hlo) hf₆

include toNat qrR unif normal in
private theorem eighSignE_setup {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) {u : P → ℝ}
    {dec : P → K → ℝ} (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem)
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
  exact eighSignE_tail hmm hsem p hu n F (S := st.store.shape) (η := w)
    (hA.of_forall_read_eq fun i _ _ => hfr₄ _ _ _ htA.symm) ((hfr₄ _ _ _ htp.symm).trans hb) hb0
    hXA hXp hX (by
      rw [Store.read_of_write_eq_some_of_ne hs₄ (Or.inr (by norm_num)),
        Store.read_of_write_eq_some_of_ne hs₃ (Or.inr (by norm_num))]
      exact Store.read_of_write_eq_some hs₂)
    (by rw [hMone]; exact Store.read_of_write_eq_some hs₄)
    (by rw [hMneg, Store.read_of_write_eq_some_of_ne hs₄ (Or.inr (by norm_num))]
        exact Store.read_of_write_eq_some hs₃)
    (by rw [hMzero, hMone, hdz, ho1]; norm_num) hWX hVX hWV htX htW htV hsh₄ hWS hVS htS

omit [AddMonoid C] [Inhabited K] in
private theorem eighSignE_push {s : Store P K} {p q : P} {a b c β i : ℕ} (hβ : β < s.size) :
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
private theorem eighSignE_push_shape (s : Store P K) (p : P) (a b c : ℕ) :
    let s₁ := s.push (p, Array.replicate a none)
    let s₂ := s₁.push (p, Array.replicate b none)
    (Store.shape (s₂.push (p, Array.replicate c none)))[s.size]? = some (p, a) ∧
    (Store.shape (s₂.push (p, Array.replicate c none)))[s₁.size]? = some (p, b) ∧
    (Store.shape (s₂.push (p, Array.replicate c none)))[s₂.size]? = some (p, c) := by
  refine ⟨?_, ?_, Store.getElem?_shape_push_size _ _ _⟩
  · rw [Store.getElem?_shape_push_of_lt _ (by simp), Store.getElem?_shape_push_of_lt _ (by simp),
      Store.getElem?_shape_push_size]
  · rw [Store.getElem?_shape_push_of_lt _ (by simp), Store.getElem?_shape_push_size]
/-- **The sign step always succeeds** under the standard model at $u$ with every value in range,
$u(p) < 1$ and an exact literal $1$, if kernel `mm` of `I` is the routine `mmR` on interleaved
pairs, $n \ge 1$, $b$ decodes to a nonzero value and the output block at `X` (tag `p`) has $2n^2$
cells (hypotheses on the inputs as `NLAlib.holds_of_exec_eighSignBlock`): unlike the pilot's
`whileFuel` loop, the bounded loop does not fail when no iterate passes the test. No printed
source.
Proof: the set-up as in the pilot's `NLAlib.exists_exec_newtonSchulzSignProg` (scaffold); then
`NLAlib.Computation.exists_exec_loop_eq_some_of_forall` with the invariant of
`NLAlib.holds_of_exec_eighSignLoop` at the iterate reached: each iteration's comparison succeeds
(`NLAlib.Computation.IsRelErrSem.decidesFlags`, scaffold) and its body succeeds
(`NLAlib.exists_exec_newtonSchulzStepBlock`, `NLAlib.exists_exec_newtonSchulzTestBlock`, pilot);
the pops succeed. M, about 60 lines. -/
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
  refine eighSignE_map ?_
  change ∃ a, exec I (.alloc p _ _) _ = some a
  rw [exec_alloc]
  refine eighSignE_map ?_
  change ∃ a, exec I (.alloc p _ _) _ = some a
  rw [exec_alloc]
  refine eighSignE_map ?_
  obtain ⟨htS, hWS, hVS⟩ := eighSignE_push_shape st.store p (IExp.eval 5)
    (IExp.eval (2 * (.const n * .const n))) (IExp.eval (2 * (.const n * .const n)))
  have hP : ∀ {β : ℕ} (q : P) (i : ℕ), β < st.store.size → _ := fun {β} q i h =>
    eighSignE_push (s := st.store) (p := p) (q := q) (a := IExp.eval 5)
      (b := (2 * (IExp.const n * .const n)).eval) (c := (2 * (IExp.const n * .const n)).eval)
      (i := i) (β := β) h
  exact eighSignE_setup (toNat := fun _ => 0) (Su := Unit) (unif := fun x _ => x) (Sg := Unit)
    (normal := fun _ => default) (qrR := fun A => (fun _ _ => default, A)) hmm hsem hlit p hu n F
    hn
    (hA.of_forall_read_eq fun i _ _ => (hP p i hAlt).1) ((hP p _ hplt).1.trans hε)
    ((hP p _ hplt).1.trans hb) hb0 hXA hXp (by rw [(hP p 0 hXlt).2]; exact hX)
    (by omega) (by omega) (by simp only [Array.size_push]; omega)
    (by simp only [Array.size_push]; omega) (by simp only [Array.size_push]; omega)
    (by omega) (by simp only [Array.size_push]; omega) (by simp only [Array.size_push]; omega)
    (by simpa using hWS) (by simpa using hVS) (by simpa using htS)

/-! ### The blocks of a node -/

omit [Inhabited K] in
/-- A successful loop of literals into the cells `f w` of one buffer keeps the shape and the tape
positions, leaves the literal in every written cell and every other cell unchanged. -/
private theorem read_of_exec_loop_lit_leaf {p : P} {m : IExp ℕ} {Y : ℕ} {f : ℕ → IExp ℕ} {c : ℚ}
    {st st' : St P K C}
    (h : exec I (.loop m fun w => .seq (.instr (.lit p ⟨Y, f w⟩ c)) .skip) st = some st') :
    st'.store.shape = st.store.shape ∧ st'.pos = st.pos ∧
      (∀ w < m.eval, ∃ z, I.sem.lit p c = some z ∧ st'.store.read p Y (f w).eval = some z) ∧
      ∀ q b i, (b ≠ Y ∨ ∀ w < m.eval, (f w).eval ≠ i) →
        st'.store.read q b i = st.store.read q b i := by
  refine forall_of_exec_loop_eq_some I (fun w s => s.store.shape = st.store.shape ∧
      s.pos = st.pos ∧
      (∀ w' < w, ∃ z, I.sem.lit p c = some z ∧ s.store.read p Y (f w').eval = some z) ∧
      ∀ q b i, (b ≠ Y ∨ ∀ w' < w, (f w').eval ≠ i) → s.store.read q b i = st.store.read q b i)
    ⟨rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ => rfl⟩ ?_ h
  rintro w - s₁ s₂ ⟨hsh, hps, hrd, hfr⟩ hex
  rw [exec_seq_skip, exec_instr] at hex
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hex
  obtain ⟨_, ⟨v, hv, s', hw', rfl⟩, rfl⟩ := hex
  refine ⟨(Store.shape_of_write_eq_some hw').trans hsh, hps, fun w' hw => ?_,
    fun q b i hb => ?_⟩
  · by_cases hww : (f w').eval = (f w).eval
    · exact ⟨v, hv, hww ▸ Store.read_of_write_eq_some hw'⟩
    · have hlt : w' < w := lt_of_le_of_ne (Nat.lt_succ_iff.mp hw) (fun h => hww (h ▸ rfl))
      rw [Store.read_of_write_eq_some_of_ne hw' (Or.inr hww)]
      exact hrd w' hlt
  · rw [Store.read_of_write_eq_some_of_ne hw' ?_]
    · exact hfr q b i (hb.imp_right fun h w' hw => h w' (Nat.lt_succ_of_lt hw))
    · exact hb.imp_right fun h => (h w (Nat.lt_succ_self w)).symm

omit [Inhabited K] in
/-- A successful loop of copies from the cells `g i` of `X` into the distinct cells `f i` of `Y`,
no source among the targets, keeps the shape and the tape positions, copies every source and leaves
every other cell unchanged. -/
private theorem read_of_exec_loop_copy_leaf {p : P} {m : IExp ℕ} {X Y : ℕ} {f g : ℕ → IExp ℕ}
    {st st' : St P K C}
    (hf : ∀ i < m.eval, ∀ j < m.eval, (f i).eval = (f j).eval → i = j)
    (hfg : ∀ i < m.eval, ∀ j < m.eval, X ≠ Y ∨ (g i).eval ≠ (f j).eval)
    (h : exec I (.loop m fun i => .seq (.instr (.copy p ⟨Y, f i⟩ ⟨X, g i⟩)) .skip) st =
      some st') :
    st'.store.shape = st.store.shape ∧ st'.pos = st.pos ∧
      (∀ i < m.eval, st'.store.read p Y (f i).eval = st.store.read p X (g i).eval) ∧
      ∀ q b j, (b ≠ Y ∨ ∀ i < m.eval, (f i).eval ≠ j) →
        st'.store.read q b j = st.store.read q b j := by
  refine forall_of_exec_loop_eq_some I (fun w s => s.store.shape = st.store.shape ∧
      s.pos = st.pos ∧
      (∀ i < w, s.store.read p Y (f i).eval = st.store.read p X (g i).eval) ∧
      ∀ q b j, (b ≠ Y ∨ ∀ i < w, (f i).eval ≠ j) → s.store.read q b j = st.store.read q b j)
    ⟨rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ => rfl⟩ ?_ h
  rintro w hwm s₁ s₂ ⟨hsh, hps, hrd, hfr⟩ hex
  rw [exec_seq_skip, exec_instr] at hex
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hex
  obtain ⟨_, ⟨v, hv, s', hw', rfl⟩, rfl⟩ := hex
  refine ⟨(Store.shape_of_write_eq_some hw').trans hsh, hps, fun i hi => ?_,
    fun q b j hb => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Store.read_of_write_eq_some_of_ne hw' (Or.inr fun he =>
        absurd (hf i (hi.trans hwm) w hwm he) (Nat.ne_of_lt hi))]
      exact hrd i hi
    · rw [Store.read_of_write_eq_some hw', ← hv]
      refine hfr p X (g i).eval ?_
      by_cases hXY : X = Y
      · exact Or.inr fun j hj he =>
          ((hfg i hwm j (hj.trans hwm)).resolve_left (not_not.mpr hXY)) he.symm
      · exact Or.inl hXY
  · rw [Store.read_of_write_eq_some_of_ne hw' ?_]
    · exact hfr q b j (hb.imp_right fun h i hi => h i (Nat.lt_succ_of_lt hi))
    · exact hb.imp_right fun h => (h w (Nat.lt_succ_self w)).symm

/-- The diagonal loop of a leaf: from a block at `mo` of `Ma` holding $\mathbf{A}$, the cells
$eo + i$ of `Ea` get $\operatorname{Re} a_{ii}$ (`diag`) or the machine's zero; the shape, the
positions and every cell outside them are kept. -/
private theorem read_of_exec_leaf_diag (p : P) (diag : Bool) (k : ℕ) {Ma Ea : ℕ}
    {mo eo : IExp ℕ} {s₁ s₂ : St P K C} {A : Matrix (Fin k) (Fin k) (K × K)}
    (hA : pairLayout.Holds s₁.store p Ma mo.eval A)
    (hEA : (¬Ea = Ma ∨ eo.eval + k ≤ mo.eval) ∨ mo.eval + 2 * (k * k) ≤ eo.eval)
    (hl : exec I (.loop (.const k) fun i => (if diag then
        ins (.copy p ⟨Ea, eo + .var i⟩ ⟨Ma, mo + zidx (.const k) (.var i) (.var i)⟩)
      else ins (.lit p ⟨Ea, eo + .var i⟩ 0) : Builder P ι ℕ ℕ Unit).run) s₁ = some s₂) :
    let M := I.sem.toFloatMachine p toNat mmR qrR unif normal
    s₂.store.shape = s₁.store.shape ∧ s₂.pos = s₁.pos ∧
      (∀ i : Fin k, s₂.store.read p Ea (eo.eval + i) = some (if diag then (A i i).1 else M.zero)) ∧
      ∀ q b j, (b ≠ Ea ∨ j < eo.eval ∨ eo.eval + k ≤ j) →
        s₂.store.read q b j = s₁.store.read q b j := by
  intro M
  have hii : ∀ i < k, 2 * (i + k * i) + 2 ≤ 2 * (k * k) := fun i hi => by nlinarith
  cases diag
  · obtain ⟨hsh, hps, hE, hfr⟩ := read_of_exec_loop_lit_leaf hl
    refine ⟨hsh, hps, fun i => ?_, fun q b j hb => hfr q b j (hb.imp_right fun hb w hw => ?_)⟩
    · obtain ⟨z, hz, hr⟩ := hE i i.isLt
      simp only [IExp.eval_add, IExp.eval_var] at hr
      rw [hr]
      simp only [M, ScalarSem.toFloatMachine, hz, Option.getD_some, Bool.false_eq_true,
        if_false]
    · simp only [IExp.eval_add, IExp.eval_var, IExp.eval_const] at hw ⊢
      omega
  · obtain ⟨hsh, hps, hE, hfr⟩ := read_of_exec_loop_copy_leaf
      (f := fun i => eo + .var i) (g := fun i => mo + zidx (.const k) (.var i) (.var i))
      (fun i _ j _ he => by simpa using he) (fun i hi j hj => by
        simp only [zidx, IExp.eval_add, IExp.eval_mul, IExp.eval_var, IExp.eval_const,
          IExp.eval_ofNat] at hi hj ⊢
        have := hii i hi
        by_cases hMa : Ma = Ea
        · right; omega
        · left; exact hMa) hl
    refine ⟨hsh, hps, fun i => ?_, fun q b j hb => hfr q b j (hb.imp_right fun hb w hw => ?_)⟩
    · have := hE i i.isLt
      simp only [zidx, IExp.eval_add, IExp.eval_mul, IExp.eval_var, IExp.eval_const,
        IExp.eval_ofNat] at this
      rw [this]
      have := hA i i ⟨0, by simp [pairLayout]⟩
      simpa [pairLayout] using this
    · simp only [IExp.eval_add, IExp.eval_var, IExp.eval_const] at hw ⊢
      omega

/-- **A leaf writes its output**: a successful run of `NLAlib.eighLeafBlock` for a node of size
$k$ whose matrix $\mathbf{A}$ is held at `mo` of `Ma` ends with the block at `uo` of `Ua` holding
the machine's identity (`NLAlib.FloatMachine.identityMat`), the cells $eo + i$ of `Ea` the real
parts $\operatorname{Re} a_{ii}$ (`diag`) or the machine's zero, and the kind cell the literal
$1$; every cell outside these blocks and the kind cell is unchanged, the store shape and the tape
positions too. No printed source.
Proof: `NLAlib.Computation.exec_run_bind`; `NLAlib.Computation.exec_zidentity_congr` (scaffold)
and the pilot's `NLAlib.Computation.holds_of_exec_zidentity`; the loop of copies or literals by
`NLAlib.Computation.forall_of_exec_loop_eq_some` (pilot) with
`NLAlib.Computation.exec_seq_instr_copy` (the source cell is outside the written blocks) or
`NLAlib.Computation.exec_seq_instr_lit`; the literal $1$ by
`NLAlib.Computation.exec_seq_instr_litIdx`. M, about 40 lines. -/
theorem holds_of_exec_eighLeafBlock (p : P) (diag : Bool) (k : ℕ) {Ma Ua Ea : ℕ}
    {mo uo eo : IExp ℕ} {kd : Cell ℕ ℕ} {st st' : St P K C}
    {A : Matrix (Fin k) (Fin k) (K × K)} (hA : pairLayout.Holds st.store p Ma mo.eval A)
    (hUA : blockDisjoint (Ua, uo.eval, 2 * (k * k)) (Ma, mo.eval, 2 * (k * k)) = true)
    (hEA : blockDisjoint (Ea, eo.eval, k) (Ma, mo.eval, 2 * (k * k)) = true)
    (hUE : blockDisjoint (Ua, uo.eval, 2 * (k * k)) (Ea, eo.eval, k) = true)
    (hkd : ∀ x ∈ [(Ma, mo.eval, 2 * (k * k)), (Ua, uo.eval, 2 * (k * k)), (Ea, eo.eval, k)],
      blockDisjoint (kd.buf, kd.idx.eval, 1) x = true)
    (h : exec I (eighLeafBlock (ι := ι) p diag (.const k) Ma mo Ua uo Ea eo kd).run st =
      some st') :
    let M := I.sem.toFloatMachine p toNat mmR qrR unif normal
    pairLayout.Holds st'.store p Ua uo.eval (M.identityMat k) ∧
      (∀ i : Fin k, st'.store.read p Ea (eo.eval + i) = some (if diag then (A i i).1 else M.zero)) ∧
      st'.store.read p kd.buf kd.idx.eval = I.sem.lit p ((1 : ℕ) : ℚ) ∧
      (∀ q b i, blockDisjoint (b, i, 1) (Ua, uo.eval, 2 * (k * k)) = true →
        blockDisjoint (b, i, 1) (Ea, eo.eval, k) = true →
        blockDisjoint (b, i, 1) (kd.buf, kd.idx.eval, 1) = true →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  intro M
  change exec I (.seq (.named _ _ (.seq (.loop _ _) (.seq (.loop _ _) .skip)))
    (.seq (.loop _ _) (.seq (.instr _) .skip))) st = some st' at h
  rw [exec_seq] at h
  obtain ⟨s₁, hz, h⟩ := Option.bind_eq_some_iff.mp h
  rw [exec_seq] at h
  obtain ⟨s₂, hl, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hI, hIfr⟩ := holds_of_exec_zidentity (I := I) (toNat := toNat) (mmR := mmR)
    (qrR := qrR) (unif := unif) (normal := normal) p k ((exec_seq_skip I _ st).trans hz)
  rw [exec_named, exec_seq] at hz
  obtain ⟨σ, h₀, h₁⟩ := Option.bind_eq_some_iff.mp hz
  rw [exec_seq_skip] at h₁
  obtain ⟨hsh₀, hps₀, -, -⟩ := read_of_exec_loop_lit_leaf h₀
  obtain ⟨hsh₁, hps₁, -, -⟩ := read_of_exec_loop_lit_leaf h₁
  rw [exec_seq_skip, exec_instr] at h
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨v, hv, s₃, hw, rfl⟩, rfl⟩ := h
  simp only [blockDisjoint, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hUA hEA hUE hkd
  have hii : ∀ i < k, 2 * (i + k * i) + 2 ≤ 2 * (k * k) := fun i hi => by nlinarith
  obtain ⟨hsh₂, hps₂, hE, hfr₂⟩ := read_of_exec_leaf_diag (toNat := toNat) (mmR := mmR)
    (qrR := qrR) (unif := unif) (normal := normal) p diag k
    (hA.of_forall_read_eq fun i hi₁ hi₂ => hIfr p Ma i (by
      change i < mo.eval + k * k * 2 at hi₂
      simp only [blockDisjoint, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq]
      by_cases hb : Ma = Ua
      · omega
      · left; left; exact hb)) hEA hl
  have hkdE : ∀ i < k, kd.buf ≠ Ea ∨ kd.idx.eval ≠ eo.eval + i := fun i hi => by
    by_cases hb : kd.buf = Ea
    · right; omega
    · left; exact hb
  refine ⟨hI.of_forall_read_eq fun i hi₁ hi₂ => ?_, fun i => ?_, ?_, fun q b i h₁ h₂ h₃ => ?_,
    ?_, ?_⟩
  · change i < uo.eval + k * k * 2 at hi₂
    rw [Store.read_of_write_eq_some_of_ne hw ?_, hfr₂ p Ua i ?_]
    · by_cases hb : Ua = Ea
      · right; omega
      · left; exact hb
    · by_cases hb : Ua = kd.buf
      · right; omega
      · left; exact hb
  · rw [Store.read_of_write_eq_some_of_ne hw ((hkdE i i.isLt).imp Ne.symm Ne.symm)]
    exact hE i
  · exact (Store.read_of_write_eq_some hw).trans hv.symm
  · simp only [blockDisjoint, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq] at h₁ h₂ h₃
    rw [Store.read_of_write_eq_some_of_ne hw ?_, hfr₂ q b i ?_]
    · exact hIfr q b i (by simpa [blockDisjoint] using h₁)
    · rcases h₂ with (h₂ | h₂) | h₂
      · exact Or.inl h₂
      · right; left; omega
      · right; right; omega
    · rcases h₃ with (h₃ | h₃) | h₃
      · exact Or.inl h₃
      · right; omega
      · right; omega
  · exact (Store.shape_of_write_eq_some hw).trans (hsh₂.trans (hsh₁.trans hsh₀))
  · exact hps₂.trans (hps₁.trans hps₀)

/-- A successful index-literal instruction writes the literal and changes only its cell. -/
private theorem exec_ins_litIdx_read (p : P) (e : IExp ℕ) (c' : Cell ℕ ℕ) {σ₀ σ : St P K C}
    (hσ : exec I (ins (.litIdx p c' e) : Builder P ι ℕ ℕ Unit).run σ₀ = some σ) :
    σ.store.read p c'.buf c'.idx.eval = I.sem.lit p (e.eval : ℚ) ∧
      (∀ q b i, ¬(b = c'.buf ∧ i = c'.idx.eval) → σ.store.read q b i = σ₀.store.read q b i) ∧
      σ.store.shape = σ₀.store.shape ∧ σ.pos = σ₀.pos := by
  change exec I (.seq (.instr (.litIdx p c' e)) .skip) σ₀ = some σ at hσ
  rcases hv : I.sem.lit p (e.eval : ℚ) with _ | v
  · simp [exec_seq, exec_instr, Instr.run, hv] at hσ
  rcases hw : σ₀.store.write p c'.buf c'.idx.eval v with _ | s
  · simp [exec_seq, exec_instr, Instr.run, hv, hw] at hσ
  rw [exec_seq_instr_litIdx I hv hw, exec_skip] at hσ
  injection hσ with hσ
  subst hσ
  refine ⟨?_, fun q b i hne => ?_, Store.shape_of_write_eq_some hw, rfl⟩
  · exact Store.read_of_write_eq_some hw
  · exact Store.read_of_write_eq_some_of_ne hw (not_and_or.mp hne)

/-- **One child on the same slot**: a successful run of `NLAlib.eighChildBlock` for a node of size
$k$ whose matrix $\mathbf{A}$ is held at `mo` of `Ma`, the cell `sg` holding $\sigma$, ends with the
block at `mo'` of `Ma` (disjoint from the one at `mo`) holding `M.hermShift A σ`, the size cell the
literal $k$ and the kind cell the literal `code`; every other cell is unchanged, the store shape and
the tape positions too. No printed source.
Proof: `NLAlib.Computation.exec_run_bind`; `NLAlib.Computation.exec_zhermShift_congr` (scaffold)
and the pilot's `NLAlib.Computation.holds_of_exec_zhermShift`; two
`NLAlib.Computation.exec_seq_instr_litIdx`. S, about 25 lines. -/
theorem holds_of_exec_eighChildBlock (p : P) (k : ℕ) {Ma : ℕ} {mo mo' : IExp ℕ}
    {sg sz kd : Cell ℕ ℕ} (code : ℕ) {σ : K} {st st' : St P K C}
    {A : Matrix (Fin k) (Fin k) (K × K)} (hA : pairLayout.Holds st.store p Ma mo.eval A)
    (hσ : st.store.read p sg.buf sg.idx.eval = some σ)
    (hAA : blockDisjoint (Ma, mo'.eval, 2 * (k * k)) (Ma, mo.eval, 2 * (k * k)) = true)
    (hsg : blockDisjoint (sg.buf, sg.idx.eval, 1) (Ma, mo'.eval, 2 * (k * k)) = true)
    (hsz : blockDisjoint (sz.buf, sz.idx.eval, 1) (Ma, mo'.eval, 2 * (k * k)) = true)
    (hkd : blockDisjoint (kd.buf, kd.idx.eval, 1) (Ma, mo'.eval, 2 * (k * k)) = true)
    (hszkd : blockDisjoint (sz.buf, sz.idx.eval, 1) (kd.buf, kd.idx.eval, 1) = true)
    (h : exec I (eighChildBlock (ι := ι) p (.const k) Ma mo mo' sg sz kd code).run st =
      some st') :
    pairLayout.Holds st'.store p Ma mo'.eval
        ((I.sem.toFloatMachine p toNat mmR qrR unif normal).hermShift A σ) ∧
      st'.store.read p sz.buf sz.idx.eval = I.sem.lit p ((k : ℕ) : ℚ) ∧
      st'.store.read p kd.buf kd.idx.eval = I.sem.lit p ((code : ℕ) : ℚ) ∧
      (∀ q b i, blockDisjoint (b, i, 1) (Ma, mo'.eval, 2 * (k * k)) = true →
        blockDisjoint (b, i, 1) (sz.buf, sz.idx.eval, 1) = true →
        blockDisjoint (b, i, 1) (kd.buf, kd.idx.eval, 1) = true →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  unfold eighChildBlock at h
  rw [exec_run_bind I (b := zhermShift (ι := ι) p (.const k) Ma mo sg Ma mo') (fun _ => rfl)] at h
  obtain ⟨σ1, h1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hM, hf1, hsh1, hp1⟩ := holds_of_exec_zhermShift p k hA hσ hAA hsg h1
  rw [exec_run_bind I (b := ins (.litIdx p sz (.const k))) (fun _ => rfl)] at h
  obtain ⟨σ2, h2, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨rsz, hf2, hsh2, hp2⟩ := exec_ins_litIdx_read p _ _ h2
  obtain ⟨rkd, hf3, hsh3, hp3⟩ := exec_ins_litIdx_read p _ _ h
  have hszb : ∀ {b i : ℕ}, blockDisjoint (b, i, 1) (sz.buf, sz.idx.eval, 1) = true →
      ¬(b = sz.buf ∧ i = sz.idx.eval) := by
    intro b i hbs ⟨hb, hi⟩
    subst hb; subst hi
    simp [blockDisjoint] at hbs
  have hkdb : ∀ {b i : ℕ}, blockDisjoint (b, i, 1) (kd.buf, kd.idx.eval, 1) = true →
      ¬(b = kd.buf ∧ i = kd.idx.eval) := by
    intro b i hbs ⟨hb, hi⟩
    subst hb; subst hi
    simp [blockDisjoint] at hbs
  have hszkd' : ¬(sz.buf = kd.buf ∧ sz.idx.eval = kd.idx.eval) := fun ⟨h1, h2⟩ => by
    simp [blockDisjoint, h1, h2] at hszkd
  have hw : (pairLayout : EntryLayout K (K × K)).width = 2 := rfl
  have hMst : pairLayout.Holds st'.store p Ma mo'.eval
      ((I.sem.toFloatMachine p toNat mmR qrR unif normal).hermShift A σ) :=
    EntryLayout.Holds.of_forall_read_eq hM fun i _ h2 => by
      rw [hw] at h2
      rw [hf3 _ _ _ (fun ⟨hb, hi⟩ => by subst hb; subst hi; simp [blockDisjoint] at hkd; omega),
        hf2 _ _ _ (fun ⟨hb, hi⟩ => by subst hb; subst hi; simp [blockDisjoint] at hsz; omega)]
  refine ⟨hMst, ?_, ?_, fun q b i hb1 hb2 hb3 => ?_, ?_, ?_⟩
  · rw [hf3 _ _ _ hszkd']
    simpa using rsz
  · simpa using rkd
  · rw [hf3 q b i (hkdb hb3), hf2 q b i (hszb hb2), hf1 q b i hb1]
  · rw [hsh3, hsh2, hsh1]
  · rw [hp3, hp2, hp1]

/-- **Randomized deflation on stored samples computes `NLAlib.deflate`**: if kernels `mm`, `qr` of
`I` are the routines `mmR`, `qrR` on interleaved pairs, a successful run of
`NLAlib.eighDeflateBlock` for a node of size $k \le n$ at slot $lo$ of depth $d$ with rank
$r \le k$, side $b$, the stored projector $\mathbf{P}$ ($k \times k$) at offset $0$ of `Pm`, the
cell `sq` holding the stored $\sqrt{1/2}$ (`NLAlib.Computation.ScalarSem.sqrtHalf`) and the $4n^2$
Gaussian words of the level in `Sg` (word $w$ the tape value at position $4n^2 d + w$), ends with
the block at `qo` of `Qa` holding `NLAlib.deflate M r P G` for $\mathbf{G}$ the leading $k \times k$
block of the test matrix of side $b$ of the node's samples (`NLAlib.eighTapeSample`), $M$ the
machine of the interpretation (`NLAlib.eighTapeMachine`); every cell outside that block and the
scratch buffers `G`, `Y`, `Qf`, `Rf` is unchanged, the store shape and the tape positions too. No
printed source.
Proof: the loop writes the stored test matrix: entry $(i, j)$ is the pair
`NLAlib.Computation.ScalarSem.tapeNormal` of the tape at the sample of `NLAlib.eighTapeSample`
(two `NLAlib.Computation.exec_seq_instr_bin`, `NLAlib.Computation.forall_of_exec_loop_eq_some`,
pilot; the word $2(n(2(lo + j) + s) + i)$ of `Sg` is the tape at twice the sample, `mul_add`),
which is `NLAlib.leadingBlock` of the samples mapped by the machine's normal sampler; the two
kernel calls by the pilot's `NLAlib.Computation.IsMatMulKernel.holds_of_kcallStore_eq_some` and
`NLAlib.Computation.IsQRKernel.holds_of_kcallStore_eq_some`; the copy of the first $r$ columns by
`NLAlib.Computation.exec_zcopy_congr` (scaffold) and the pilot's
`NLAlib.Computation.holds_of_exec_zcopy`, column-major packed so the first $r$ columns of
$\mathbf{Q}$ are its first $2kr$ words; unfold `NLAlib.deflate` ($r \le k$, so no zero column). M,
about 80 lines. -/
theorem holds_of_exec_eighDeflateBlock {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) (p : P) (n k r d lo : ℕ) (hk : lo + k ≤ n)
    (hr : r ≤ k) (b : Bool) {Sg Pm G Y Qf Rf Qa : ℕ} {sq : Cell ℕ ℕ} {qo : IExp ℕ}
    {st st' : St P K C} {Pmat : Matrix (Fin k) (Fin k) (K × K)}
    (hP : pairLayout.Holds st.store p Pm 0 Pmat)
    (hsq : st.store.read p sq.buf sq.idx.eval = some (I.sem.sqrtHalf p))
    (hSg : ∀ w < 4 * (n * n), st.store.read p Sg w = some (I.tape .gaussian (4 * (n * n) * d + w)))
    (hbufs : [Sg, Pm, G, Y, Qf, Rf, Qa].Nodup) (hsqb : sq.buf ∉ [G, Y, Qf, Rf, Qa])
    (h : exec I (eighDeflateBlock p mm qr (.const n) (.const k) (.const r) (.const lo)
      (if b then 0 else 1) Sg sq Pm G Y Qf Rf Qa qo).run st = some st') :
    pairLayout.Holds st'.store p Qa qo.eval
        (deflate (eighTapeMachine I p mmR qrR) r Pmat
          (leadingBlock k ((eighTapeSample n d lo).2 b))) ∧
      (∀ q b' i, b' ∉ [G, Y, Qf, Rf] → blockDisjoint (b', i, 1) (Qa, qo.eval, 2 * (k * r)) = true →
        st'.store.read q b' i = st.store.read q b' i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  sorry

/-- **Deflation on stored samples succeeds** under the standard model with every value in range,
if the kernels are routines on pairs and the buffers `G`, `Y`, `Qf`, `Rf` have $2n^2$ cells and the
block at `qo` of `Qa` fits (hypotheses on the inputs as `NLAlib.holds_of_exec_eighDeflateBlock`).
No printed source.
Proof: each product succeeds (`bin_ok`, `trivial`); the kernel calls succeed by the pilot's
`NLAlib.Computation.IsMatMulKernel.kcallStore_eq`, `NLAlib.Computation.IsQRKernel.kcallStore_eq`
(the reads by `NLAlib.Computation.EntryLayout.holds_iff_readBlock_eq_some`, pilot); the copy by the
pilot's `NLAlib.Computation.exists_exec_zcopy` after `NLAlib.Computation.exec_zcopy_congr`. M,
about 50 lines. -/
theorem exists_exec_eighDeflateBlock {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (n k r d lo : ℕ)
    (hk : lo + k ≤ n) (hr : r ≤ k) (b : Bool) {Sg Pm G Y Qf Rf Qa : ℕ} {sq : Cell ℕ ℕ}
    {qo : IExp ℕ} {st : St P K C} {Pmat : Matrix (Fin k) (Fin k) (K × K)}
    (hP : pairLayout.Holds st.store p Pm 0 Pmat)
    (hsq : st.store.read p sq.buf sq.idx.eval = some (I.sem.sqrtHalf p))
    (hSg : ∀ w < 4 * (n * n), st.store.read p Sg w = some (I.tape .gaussian (4 * (n * n) * d + w)))
    (hbufs : [Sg, Pm, G, Y, Qf, Rf, Qa].Nodup) (hsqb : sq.buf ∉ [G, Y, Qf, Rf, Qa])
    (hscr : ∀ X ∈ [G, Y, Qf, Rf], ∃ len, st.store.shape[X]? = some (p, len) ∧ 2 * (n * n) ≤ len)
    (hQa : ∃ len, st.store.shape[Qa]? = some (p, len) ∧ qo.eval + 2 * (k * r) ≤ len) :
    ∃ st', exec I (eighDeflateBlock p mm qr (.const n) (.const k) (.const r) (.const lo)
      (if b then 0 else 1) Sg sq Pm G Y Qf Rf Qa qo).run st = some st' := by
  sorry

/-- **A compression computes the machine's compression**: if kernel `mm` of `I` is the routine `mmR`
on interleaved pairs, a successful run of `NLAlib.eighCompressBlock` for the stored $k \times r$
basis $\mathbf{Q}$ at `qo` of `Qa`, the node matrix $\mathbf{A}$ at `mo` of `Ma`, the cells `two`
and `sg` holding $c_2$ and $\sigma$, writing at `co` of `Ma` (disjoint from the block at `mo`), ends
with that block holding `M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Q) A) Q) c₂) σ`;
every cell outside it and the scratch buffers is unchanged, the store shape and the tape positions
too. No printed source.
Proof: `NLAlib.Computation.exec_run_bind` splits the block;
`NLAlib.Computation.exec_zconjTranspose_congr`, `NLAlib.Computation.exec_zhermAvg_congr`,
`NLAlib.Computation.exec_zhermShift_congr` (scaffold) and the pilot's
`NLAlib.Computation.holds_of_exec_zconjTranspose`, `NLAlib.Computation.holds_of_exec_zhermAvg`,
`NLAlib.Computation.holds_of_exec_zhermShift`; the two kernel calls by
`NLAlib.Computation.IsMatMulKernel.holds_of_kcallStore_eq_some` (pilot). M, about 50 lines. -/
theorem holds_of_exec_eighCompressBlock {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (p : P) (k r : ℕ) {Qa Ma Qh C1 C2 C3 : ℕ} {qo mo co : IExp ℕ} {two sg : Cell ℕ ℕ} {c₂ σ : K}
    {st st' : St P K C} {Q : Matrix (Fin k) (Fin r) (K × K)} {A : Matrix (Fin k) (Fin k) (K × K)}
    (hQ : pairLayout.Holds st.store p Qa qo.eval Q) (hA : pairLayout.Holds st.store p Ma mo.eval A)
    (htwo : st.store.read p two.buf two.idx.eval = some c₂)
    (hσ : st.store.read p sg.buf sg.idx.eval = some σ)
    (hbufs : [Qa, Ma, Qh, C1, C2, C3].Nodup) (hcells : two.buf ∉ [Qh, C1, C2, C3] ∧
      sg.buf ∉ [Qh, C1, C2, C3])
    (hco : blockDisjoint (Ma, co.eval, 2 * (r * r)) (Ma, mo.eval, 2 * (k * k)) = true)
    (hcocells : blockDisjoint (Ma, co.eval, 2 * (r * r)) (two.buf, two.idx.eval, 1) = true ∧
      blockDisjoint (Ma, co.eval, 2 * (r * r)) (sg.buf, sg.idx.eval, 1) = true)
    (h : exec I (eighCompressBlock p mm (.const k) (.const r) Qa qo Ma mo co two sg Qh C1 C2
      C3).run st = some st') :
    let M := I.sem.toFloatMachine p toNat mmR qrR unif normal
    pairLayout.Holds st'.store p Ma co.eval
        (M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Q) A) Q) c₂) σ) ∧
      (∀ q b i, b ∉ [Qh, C1, C2, C3] → blockDisjoint (b, i, 1) (Ma, co.eval, 2 * (r * r)) = true →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  sorry

/-- **A compression succeeds** under the standard model at $u$ with every value in range, the
cell `two` decoding to a nonzero value, if kernel `mm` is a routine on pairs and the scratch buffers
have $2n^2$ cells, $k, r \le n$ (hypotheses on the inputs as
`NLAlib.holds_of_exec_eighCompressBlock`). No printed source.
Proof: as `NLAlib.exists_exec_eighDeflateBlock`, with the pilot's
`NLAlib.Computation.exists_exec_zhermShift` and the existence statements of `zconjTranspose` and
`zhermAvg` in the pilot's `NLAlib/Matrix/Computation/PairKernels.lean` scaffold (divisions by the
nonzero `two`). M, about 50 lines. -/
theorem exists_exec_eighCompressBlock {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    {u : P → ℝ} {dec : P → K → ℝ} (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P)
    (n k r : ℕ) (hk : k ≤ n) (hr : r ≤ k) {Qa Ma Qh C1 C2 C3 : ℕ} {qo mo co : IExp ℕ}
    {two sg : Cell ℕ ℕ} {c₂ σ : K} {st : St P K C} {Q : Matrix (Fin k) (Fin r) (K × K)}
    {A : Matrix (Fin k) (Fin k) (K × K)} (hQ : pairLayout.Holds st.store p Qa qo.eval Q)
    (hA : pairLayout.Holds st.store p Ma mo.eval A)
    (htwo : st.store.read p two.buf two.idx.eval = some c₂) (htwo0 : dec p c₂ ≠ 0)
    (hσ : st.store.read p sg.buf sg.idx.eval = some σ)
    (hbufs : [Qa, Ma, Qh, C1, C2, C3].Nodup) (hcells : two.buf ∉ [Qh, C1, C2, C3] ∧
      sg.buf ∉ [Qh, C1, C2, C3])
    (hco : blockDisjoint (Ma, co.eval, 2 * (r * r)) (Ma, mo.eval, 2 * (k * k)) = true)
    (hcolen : ∃ len, st.store.shape[Ma]? = some (p, len) ∧ co.eval + 2 * (r * r) ≤ len)
    (hscr : ∀ X ∈ [Qh, C1, C2, C3], ∃ len, st.store.shape[X]? = some (p, len) ∧
      2 * (n * n) ≤ len) :
    ∃ st', exec I (eighCompressBlock p mm (.const k) (.const r) Qa qo Ma mo co two sg Qh C1 C2
      C3).run st = some st' := by
  sorry

/-- **A split writes the outcome of `NLAlib.eighStep`'s split**: if the kernels of `I` are the
routines `mmR`, `qrR` on interleaved pairs, a successful run of `NLAlib.eighSplitBlock` at the slot
$lo$ of depth $d$ for a node of size $k$ (with $lo + k \le n$) whose matrix $\mathbf{A}$ is held at
its block of `Ma`, with $0 < k_+ < k$, the projectors $\mathbf{P}_\pm$ at offset $0$ of `Pp`, `Pm`,
the level's Gaussian words in `Sg`, and the cells `one`, `two`, `sg`, `nsg` holding the machine's
one, $\mathrm{fl}(2)$, $\sigma$ and $-\sigma$, ends with: $\mathbf{Q}_+ =$
`NLAlib.deflate M kp Pp G₊` and $\mathbf{Q}_-$ packed at the node's block of `Qa`, the compressions
of `NLAlib.eighStep` at the blocks of the slots $lo$ and $lo + k_+$ of depth $d + 1$ in `Ma`, the
sizes $k_+$ and $k - k_+$ in their cells of `Sz`, the kind $4$ and $k_+$ in the node's cells of `Kd`
and `Kp`; every other cell of the arenas is unchanged ($M$ = `NLAlib.eighTapeMachine I p mmR qrR`,
the test matrices those of the node's samples, `NLAlib.eighTapeSample`). No printed source.
Proof: `NLAlib.Computation.exec_alloc` eight times and `NLAlib.Computation.exec_run_bind`; the
stored $\sqrt{1/2}$ by two instructions (`NLAlib.Computation.ScalarSem.sqrtHalf`, read off their
successful runs, `Option.getD_some`); `NLAlib.holds_of_exec_eighDeflateBlock` twice,
`NLAlib.holds_of_exec_eighCompressBlock` twice (the blocks of the slots $lo$, $lo + k_+$ of depth
$d + 1$ are disjoint from each other and from depth $d$, `NLAlib.eighBlockOff`, since
$k_+^2 \le k_+ n$), four `NLAlib.Computation.exec_seq_instr_litIdx`; the pops keep the frame. M,
about 90 lines. -/
theorem holds_of_exec_eighSplitBlock {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) (p : P) (n d lo k kp : ℕ) (hk : lo + k ≤ n)
    (hkp : 0 < kp) (hkpk : kp < k) (H : EighArenas) {Sg Pp Pm : ℕ} {one two sg nsg sq : Cell ℕ ℕ}
    {σ : K} {st st' : St P K C} {A : Matrix (Fin k) (Fin k) (K × K)}
    {Ppm Pmm : Matrix (Fin k) (Fin k) (K × K)}
    {D : ℕ} (hd : d < D) (hH : H.Shaped st.store p n D)
    (hbufs : (H.handles ++ [Sg, Pp, Pm]).Nodup)
    (hA : pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hPp : pairLayout.Holds st.store p Pp 0 Ppm) (hPm : pairLayout.Holds st.store p Pm 0 Pmm)
    (hSg : ∀ w < 4 * (n * n), st.store.read p Sg w = some (I.tape .gaussian (4 * (n * n) * d + w)))
    (hone : st.store.read p one.buf one.idx.eval = I.sem.lit p 1)
    (htwo : st.store.read p two.buf two.idx.eval = I.sem.lit p ((2 : ℕ) : ℚ))
    (hσ : st.store.read p sg.buf sg.idx.eval = some σ)
    (hnσ : st.store.read p nsg.buf nsg.idx.eval =
      some ((eighTapeMachine I p mmR qrR).neg σ))
    (hcells : ∀ c ∈ [one, two, sg, nsg, sq], c.buf ∉ H.handles ++ [Sg, Pp, Pm])
    (h : exec I (eighSplitBlock p mm qr (.const n) (.const d) (.const lo) (.const k) (.const kp) Sg
      Pp Pm H.Ma H.Qa H.Sz H.Kd H.Kp one two sg nsg sq).run st = some st') :
    let M := eighTapeMachine I p mmR qrR
    let s := eighTapeSample n d lo
    let Qp := deflate M kp Ppm (leadingBlock k (s.2 true))
    let Qm := deflate M (k - kp) Pmm (leadingBlock k (s.2 false))
    pairLayout.Holds st'.store p H.Qa (2 * (n * n) * d + 2 * n * lo) Qp ∧
      pairLayout.Holds st'.store p H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (k * kp)) Qm ∧
      pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * lo)
        (M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Qp) A) Qp) (M.ofNat 2)) σ) ∧
      pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * (lo + kp))
        (M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Qm) A) Qm) (M.ofNat 2))
          (M.neg σ)) ∧
      st'.store.read p H.Sz (n * (d + 1) + lo) = I.sem.lit p ((kp : ℕ) : ℚ) ∧
      st'.store.read p H.Sz (n * (d + 1) + (lo + kp)) = I.sem.lit p ((k - kp : ℕ) : ℚ) ∧
      st'.store.read p H.Kd (n * d + lo) = I.sem.lit p ((4 : ℕ) : ℚ) ∧
      st'.store.read p H.Kp (n * d + lo) = I.sem.lit p ((kp : ℕ) : ℚ) ∧
      (∀ q b i, ¬ H.LevelCell n d b i → ¬ H.LevelCell n (d + 1) b i →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  sorry

/-- **A split succeeds** under the standard model at $u$ with every value in range and $u(p) < 1$,
with an exact literal $2$, if the kernels are routines on pairs and the arenas are allocated
(hypotheses on the inputs as `NLAlib.holds_of_exec_eighSplitBlock`). No printed source.
Proof: the eight allocations, the division and the square root succeed (`bin_ok` with the exact
literal $2 \ne 0$; `sqrt_ok` for $\sqrt{\cdot}$ of $\mathrm{fl}(1/2) \ge 0$, `lit_err`); then
`NLAlib.exists_exec_eighDeflateBlock` twice, `NLAlib.exists_exec_eighCompressBlock` twice on the
states the value statements describe, and the four literals (`lit_ok`). M, about 70 lines. -/
theorem exists_exec_eighSplitBlock {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hlit : IsExactIntLit dec I.sem 2) (p : P)
    (hu : u p < 1) (n d lo k kp : ℕ) (hk : lo + k ≤ n) (hkp : 0 < kp) (hkpk : kp < k)
    (H : EighArenas) {Sg Pp Pm : ℕ} {one two sg nsg sq : Cell ℕ ℕ} {σ : K} {st : St P K C}
    {A : Matrix (Fin k) (Fin k) (K × K)} {Ppm Pmm : Matrix (Fin k) (Fin k) (K × K)}
    {D : ℕ} (hd : d < D) (hH : H.Shaped st.store p n D) (hbufs : (H.handles ++ [Sg, Pp, Pm]).Nodup)
    (hA : pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hPp : pairLayout.Holds st.store p Pp 0 Ppm) (hPm : pairLayout.Holds st.store p Pm 0 Pmm)
    (hSg : ∀ w < 4 * (n * n), st.store.read p Sg w = some (I.tape .gaussian (4 * (n * n) * d + w)))
    (hone : st.store.read p one.buf one.idx.eval = I.sem.lit p 1)
    (htwo : st.store.read p two.buf two.idx.eval = I.sem.lit p ((2 : ℕ) : ℚ))
    (hσ : st.store.read p sg.buf sg.idx.eval = some σ)
    (hnσ : st.store.read p nsg.buf nsg.idx.eval = some ((eighTapeMachine I p mmR qrR).neg σ))
    (hcells : ∀ c ∈ [one, two, sg, nsg, sq], c.buf ∉ H.handles ++ [Sg, Pp, Pm])
    (hsq : ∃ s, st.store.write p sq.buf sq.idx.eval default = some s) :
    ∃ st', exec I (eighSplitBlock p mm qr (.const n) (.const d) (.const lo) (.const k) (.const kp)
      Sg Pp Pm H.Ma H.Qa H.Sz H.Kd H.Kp one two sg nsg sq).run st = some st' := by
  sorry

/-! ### The node step -/

/-- **The node step computes `NLAlib.eighStep`**: let the kernels of `I` be the routines `mmR`,
`qrR` on interleaved pairs and the semantics decide flags at `p`; let $M$ be the machine of the
interpretation (`NLAlib.eighTapeMachine`). A successful run of `NLAlib.eighNodeBlock` at the slot
$lo$ of depth $d$ for a node of size $k \ge 2$, $lo + k \le n$, whose matrix $\mathbf{A}$ is held at
its block of `Ma`, whose window $R$ is in the cell $2d$ of `Lv`, whose seed is the cell $lo$ of `Su`
(the tape at uniform position $nd + lo$), with the level's Gaussian words in `Sg`, the stored
$\beta$ in cell $2$ of `par` and the constants (the machine's one, $\mathrm{fl}(2)$,
$\mathrm{fl}(1/2)$, $-1$) in the cells of `c`, ends with the outcome of `NLAlib.eighStep` at the
node's samples (`NLAlib.eighTapeSample`, depth counter $\ell_0 + d$), when it is not a leaf: for one
child on side $b$, the shifted matrix at the same slot of depth $d + 1$, the size $k$ there, and the
kind $2$ ($b$ true) or $3$; for a split into $k_+$, everything `NLAlib.holds_of_exec_eighSplitBlock`
writes. Every cell outside depths $d$ and $d + 1$ of the arenas (and outside `Su`, `Sg`, `c`, `par`,
which are only read) is unchanged, the store shape and the tape positions too. No printed source.
Proof: `NLAlib.Computation.exec_alloc` seven times, the instructions computing $\sigma$, $-\sigma$,
$\ell$, $R/\ell$ and the shift $c$ (`NLAlib.Computation.ScalarSem.tapeUnif`), then
`NLAlib.Computation.exec_zhermShift_congr` with the pilot's
`NLAlib.Computation.holds_of_exec_zhermShift`, `NLAlib.holds_of_exec_eighSignBlock` at
$(\beta, \mathrm{fl}(2R))$ (its `hX` from the allocation of `B`, $2k^2$ cells at tag `p`, the
shape kept by every earlier write), the projectors and the trace (the pilot's
`NLAlib.Computation.holds_of_exec_zhermScale`, `NLAlib.Computation.holds_of_exec_zneg`,
`NLAlib.Computation.read_of_exec_ztraceRe` after the congruences); the index binder by
`NLAlib.Computation.exec_bindIdx` reads $k_+ = \min(\lfloor\cdot\rfloor, k)$, the machine's `toNat`
(`Option.getD_some`), equal to `NLAlib.eighStep`'s `min k _` (`min_comm`); the three
`NLAlib.eighWhen` loops run exactly the branch of `NLAlib.eighStep` (trip counts by `omega`), each
by `NLAlib.holds_of_exec_eighChildBlock` or `NLAlib.holds_of_exec_eighSplitBlock`; unfold
`NLAlib.eighStep` with `hk2` and `hR` (the `if`s fall through to the shift). L, about 160 lines
(split the set-up up to the trace into a private lemma). -/
theorem holds_of_exec_eighNodeBlock {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) (p : P) (hflag : I.sem.DecidesFlags p)
    (n ℓ₀ F d lo k : ℕ) (hk : lo + k ≤ n) (hk2 : 2 ≤ k) (H : EighArenas)
    {par Su Sg c : ℕ} {st st' : St P K C} {A : Matrix (Fin k) (Fin k) (K × K)} {R R₀ ε β : K}
    {D : ℕ} (hd : d < D) (hH : H.Shaped st.store p n D)
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
        (eighTapeMachine I p mmR qrR).one))
    (h : exec I (eighNodeBlock p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) (.const lo)
      (.const k) par H.Lv Su Sg H.Ma H.Qa H.Sz H.Kd H.Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩).run st =
        some st') :
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
  sorry

/-- **The node step succeeds** under the standard model at $u$ with every value in range,
$u(p) < 1$, exact literals up to $2$ and the exact floor conversion, if the kernels are routines on
pairs, the window decodes to a positive value, the depth counter $\ell_0 + d$ is at least $1$ and
the arenas are allocated (hypotheses on the inputs as `NLAlib.holds_of_exec_eighNodeBlock`): no
operation fails (the divisions are by $\mathrm{fl}(2)$, $\ell$ and $b = \mathrm{fl}(2R) \ne 0$, the
sign step does not fail for want of steps, the conversion is total). No printed source.
Proof: the set-up instructions succeed (`bin_ok`, `lit_ok`; $\mathrm{fl}(\ell) \ne 0$ for
$\ell \ge 1$ and $u(p) < 1$, `lit_err`); `NLAlib.exists_exec_eighSignBlock` with
$\overline{\mathrm{fl}(2R)} = 2\bar R(1 + \delta) \ne 0$; the projectors, the trace and the binder
(`htn`, so `NLAlib.Computation.toNatStep` succeeds); then the branch taken
(`NLAlib.exists_exec_eighSplitBlock`, or the child block by the pilot's
`NLAlib.Computation.exists_exec_zhermShift` and two literals). M, about 90 lines. -/
theorem exists_exec_eighNodeBlock {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hlit : IsExactIntLit dec I.sem 2)
    (htn : IsExactToNat dec I.sem) (p : P) (hu : u p < 1) (n ℓ₀ F d lo k : ℕ) (hk : lo + k ≤ n)
    (hk2 : 2 ≤ k) (hℓ : 1 ≤ ℓ₀ + d) (H : EighArenas) {par Su Sg c : ℕ} {st : St P K C}
    {A : Matrix (Fin k) (Fin k) (K × K)} {R β : K}
    {D : ℕ} (hd : d < D) (hH : H.Shaped st.store p n D)
    (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup)
    (hA : pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hR : st.store.read p H.Lv (2 * d) = some R) (hR0 : 0 < dec p R)
    (hpar : st.store.read p par 2 = some β)
    (hSu : ∃ v, st.store.read p Su lo = some v)
    (hSg : ∀ w < 4 * (n * n), ∃ v, st.store.read p Sg w = some v)
    (hc : st.store.read p c 0 = I.sem.lit p 1 ∧ st.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
      (∃ v, st.store.read p c 2 = some v) ∧ ∃ v, st.store.read p c 3 = some v) :
    ∃ st', exec I (eighNodeBlock p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) (.const lo)
      (.const k) par H.Lv Su Sg H.Ma H.Qa H.Sz H.Kd H.Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩).run st =
        some st' := by
  sorry

end NLAlib
