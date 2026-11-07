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

/-- One entry of the test-matrix loop of a deflation: the two products of the words of `Sg` by the
stored $\sqrt{1/2}$ land in the words $2(i + kj)$ and $2(i + kj) + 1$ of `G`; the earlier entries,
every other buffer, the shape and the positions are kept. -/
private theorem deflate_testEntry (p : P) (n k lo s i j : ℕ) {Sg G : ℕ} {sq : Cell ℕ ℕ}
    {sv : K} {st s₁ s₂ : St P K C} (hi : i < k) (hsqG : sq.buf ≠ G) (hSgG : Sg ≠ G)
    (hsq : st.store.read p sq.buf sq.idx.eval = some sv)
    (hsh : s₁.store.shape = st.store.shape) (hps : s₁.pos = st.pos)
    (hfr : ∀ q b x, b ≠ G → s₁.store.read q b x = st.store.read q b x)
    (hent : ∀ i' j', i' < k → j' < k → i' + k * j' < i + k * j → ∃ a a',
      st.store.read p Sg (2 * (n * (2 * (lo + j') + s) + i')) = some a ∧
      st.store.read p Sg (2 * (n * (2 * (lo + j') + s) + i') + 1) = some a' ∧
      s₁.store.read p G (2 * (i' + k * j')) = some ((I.sem.bin p .mul a sv).getD default) ∧
      s₁.store.read p G (2 * (i' + k * j') + 1) = some ((I.sem.bin p .mul a' sv).getD default))
    (hex : exec I (.seq (.instr (.bin p .mul ⟨G, zidx (.const k) (.var i) (.var j)⟩
          ⟨Sg, 2 * (.const n * (2 * (.const lo + .var j) + .const s) + .var i)⟩ sq))
        (.seq (.instr (.bin p .mul ⟨G, zidx (.const k) (.var i) (.var j) + 1⟩
          ⟨Sg, 2 * (.const n * (2 * (.const lo + .var j) + .const s) + .var i) + 1⟩ sq))
        .skip)) s₁ = some s₂) :
    s₂.store.shape = st.store.shape ∧ s₂.pos = st.pos ∧
      (∀ q b x, b ≠ G → s₂.store.read q b x = st.store.read q b x) ∧
      ∀ i' j', i' < k → j' < k → i' + k * j' < i + k * j + 1 → ∃ a a',
        st.store.read p Sg (2 * (n * (2 * (lo + j') + s) + i')) = some a ∧
        st.store.read p Sg (2 * (n * (2 * (lo + j') + s) + i') + 1) = some a' ∧
        s₂.store.read p G (2 * (i' + k * j')) = some ((I.sem.bin p .mul a sv).getD default) ∧
        s₂.store.read p G (2 * (i' + k * j') + 1) =
          some ((I.sem.bin p .mul a' sv).getD default) := by
  rw [exec_seq, exec_instr] at hex
  obtain ⟨s₃, h₃, hex⟩ := Option.bind_eq_some_iff.mp hex
  rw [exec_seq_skip, exec_instr] at hex
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h₃ hex
  obtain ⟨_, ⟨a, ha, c, hc, v, hv, w₁, hw₁, rfl⟩, rfl⟩ := h₃
  obtain ⟨_, ⟨a', ha', c', hc', v', hv', w₂, hw₂, rfl⟩, rfl⟩ := hex
  simp only [zidx, IExp.eval_add, IExp.eval_mul, IExp.eval_var, IExp.eval_const,
    IExp.eval_ofNat] at ha hc hv hw₁ ha' hc' hv' hw₂
  have hsq₁ : s₁.store.read p sq.buf sq.idx.eval = some sv := (hfr _ _ _ hsqG).trans hsq
  rw [hsq₁, Option.some.injEq] at hc
  subst hc
  rw [Store.read_of_write_eq_some_of_ne hw₁ (Or.inl hsqG), hsq₁, Option.some.injEq] at hc'
  subst hc'
  rw [Store.read_of_write_eq_some_of_ne hw₁ (Or.inl hSgG)] at ha'
  have hfr₂ : ∀ q b x, b ≠ G → w₂.read q b x = st.store.read q b x := fun q b x hb => by
    rw [Store.read_of_write_eq_some_of_ne hw₂ (Or.inl hb),
      Store.read_of_write_eq_some_of_ne hw₁ (Or.inl hb), hfr q b x hb]
  refine ⟨(Store.shape_of_write_eq_some hw₂).trans ((Store.shape_of_write_eq_some hw₁).trans hsh),
    hps, hfr₂, fun i' j' hi' hj' hlt => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt | he
  · obtain ⟨b₁, b₂, hb₁, hb₂, hg₁, hg₂⟩ := hent i' j' hi' hj' hlt
    refine ⟨b₁, b₂, hb₁, hb₂, ?_, ?_⟩
    · rw [Store.read_of_write_eq_some_of_ne hw₂ (Or.inr (by omega)),
        Store.read_of_write_eq_some_of_ne hw₁ (Or.inr (by omega)), hg₁]
    · rw [Store.read_of_write_eq_some_of_ne hw₂ (Or.inr (by omega)),
        Store.read_of_write_eq_some_of_ne hw₁ (Or.inr (by omega)), hg₂]
  · obtain ⟨rfl, rfl⟩ : i' = i ∧ j' = j := by
      have hk : 0 < k := by omega
      have h1 : (i' + k * j') % k = (i + k * j) % k := by rw [he]
      simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hi'] at h1
      subst h1
      exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hk (by omega)⟩
    refine ⟨a, a', (hfr _ _ _ hSgG).symm.trans ha, (hfr _ _ _ hSgG).symm.trans ha', ?_, ?_⟩
    · rw [Store.read_of_write_eq_some_of_ne hw₂ (Or.inr (by omega)),
        Store.read_of_write_eq_some hw₁, hv]
      rfl
    · rw [Store.read_of_write_eq_some hw₂, hv']
      rfl

/-- The test-matrix loop of a deflation: entry $(i, j)$ of the block `G` is the pair of products of
the words $2(n(2(lo + j) + s) + i)$ and the next of `Sg` by the stored $\sqrt{1/2}$; every other
buffer, the shape and the positions are kept. -/
private theorem deflate_testLoop (p : P) (n k lo s : ℕ) {Sg G : ℕ} {sq : Cell ℕ ℕ}
    {sv : K} {st st' : St P K C} (hsqG : sq.buf ≠ G) (hSgG : Sg ≠ G)
    (hsq : st.store.read p sq.buf sq.idx.eval = some sv)
    (h : exec I (.loop (.const k) fun j => (forRange (ι := ι) (.const k) fun i => do
        ins (.bin p .mul ⟨G, zidx (.const k) (.var i) (.var j)⟩
          ⟨Sg, 2 * (.const n * (2 * (.const lo + .var j) + .const s) + .var i)⟩ sq)
        ins (.bin p .mul ⟨G, zidx (.const k) (.var i) (.var j) + 1⟩
          ⟨Sg, 2 * (.const n * (2 * (.const lo + .var j) + .const s) + .var i) + 1⟩ sq)).run)
      st = some st') :
    st'.store.shape = st.store.shape ∧ st'.pos = st.pos ∧
      (∀ q b x, b ≠ G → st'.store.read q b x = st.store.read q b x) ∧
      ∀ i j, i < k → j < k → ∃ a a',
        st.store.read p Sg (2 * (n * (2 * (lo + j) + s) + i)) = some a ∧
        st.store.read p Sg (2 * (n * (2 * (lo + j) + s) + i) + 1) = some a' ∧
        st'.store.read p G (2 * (i + k * j)) = some ((I.sem.bin p .mul a sv).getD default) ∧
        st'.store.read p G (2 * (i + k * j) + 1) =
          some ((I.sem.bin p .mul a' sv).getD default) := by
  let Ent : ℕ → St P K C → Prop := fun c s₁ => ∀ i' j', i' < k → j' < k → i' + k * j' < c →
    ∃ a a', st.store.read p Sg (2 * (n * (2 * (lo + j') + s) + i')) = some a ∧
      st.store.read p Sg (2 * (n * (2 * (lo + j') + s) + i') + 1) = some a' ∧
      s₁.store.read p G (2 * (i' + k * j')) = some ((I.sem.bin p .mul a sv).getD default) ∧
      s₁.store.read p G (2 * (i' + k * j') + 1) = some ((I.sem.bin p .mul a' sv).getD default)
  have hR := forall_of_exec_loop_eq_some I (n := .const k) (fun j s₁ => s₁.store.shape =
      st.store.shape ∧ s₁.pos = st.pos ∧
      (∀ q b x, b ≠ G → s₁.store.read q b x = st.store.read q b x) ∧ Ent (k * j) s₁)
    ⟨rfl, rfl, fun _ _ _ _ => rfl, fun _ _ _ _ h => absurd h (by omega)⟩ ?_ h
  · obtain ⟨hsh, hps, hfr, hent⟩ := hR
    exact ⟨hsh, hps, hfr, fun i j hi hj => hent i j hi hj (by
      simp only [IExp.eval_const]; nlinarith)⟩
  rintro j hj s₁ s₂ ⟨hsh, hps, hfr, hent⟩ hex
  change exec I (.seq (.loop _ _) .skip) s₁ = some s₂ at hex
  rw [exec_seq_skip] at hex
  have hR' := forall_of_exec_loop_eq_some I (n := .const k) (fun i s₃ => s₃.store.shape =
      st.store.shape ∧ s₃.pos = st.pos ∧
      (∀ q b x, b ≠ G → s₃.store.read q b x = st.store.read q b x) ∧ Ent (i + k * j) s₃)
    ⟨hsh, hps, hfr, by rwa [zero_add]⟩ (fun i hi s₃ s₄ ⟨hsh, hps, hfr, hent⟩ hex => by
      rw [show i + 1 + k * j = i + k * j + 1 by ring]
      exact deflate_testEntry p n k lo s i j hi hsqG hSgG hsq hsh hps hfr hent hex) hex
  obtain ⟨hsh, hps, hfr, hent⟩ := hR'
  refine ⟨hsh, hps, hfr, ?_⟩
  simp only [IExp.eval_const] at hent
  rwa [show k * (j + 1) = k + k * j by ring]

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
  set M := eighTapeMachine I p mmR qrR
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hbufs hsqb
  obtain ⟨⟨-, hSgG, -, -, -, -⟩, ⟨hPmG, hPmY, -, -, -⟩, ⟨hGY, -, -, -⟩, ⟨hYQf, hYRf, -⟩,
    ⟨hQfRf, hQfQa⟩, -, -⟩ := hbufs
  obtain ⟨hsG, -, -, -, -⟩ := hsqb
  have hne : ∀ {b b' i i' l l' : ℕ}, b ≠ b' → blockDisjoint (b, i, l) (b', i', l') = true :=
    fun h => by simp [blockDisjoint, h]
  change exec I (.seq (.loop _ _) (.seq (.kcall _ _ _ _ _) (.seq (.kcall _ _ _ _ _)
    (.seq (.named _ _ _) .skip)))) st = some st' at h
  rw [exec_seq] at h
  obtain ⟨s₁, h₁, h⟩ := Option.bind_eq_some_iff.mp h
  rw [exec_seq, exec_kcall] at h
  obtain ⟨s₂, h₂, h⟩ := Option.bind_eq_some_iff.mp h
  rw [exec_seq, exec_kcall] at h
  obtain ⟨s₃, h₃, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨c₂, hc₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
  obtain ⟨c₃, hc₃, rfl⟩ := Option.map_eq_some_iff.mp h₃
  -- the stored test matrix
  obtain ⟨hsh₁, hps₁, hfr₁, hent⟩ := deflate_testLoop p n k lo (if b then 0 else 1) hsG hSgG
    hsq h₁
  have hG : pairLayout.Holds s₁.store p G 0
      ((leadingBlock k ((eighTapeSample n d lo).2 b)).map M.normal) := by
    intro i j t
    obtain ⟨a, a', ha, ha', hg, hg'⟩ := hent i j i.isLt j.isLt
    have hw : 2 * (n * (2 * (lo + j) + (if b then 0 else 1)) + i) + 1 < 4 * (n * n) := by
      have h1 : 2 * (lo + j) + (if b then 0 else 1) + 1 ≤ 2 * n := by split <;> omega
      have h2 := Nat.mul_le_mul_left n h1
      have h3 : (i : ℕ) < n := by omega
      rw [Nat.mul_add, Nat.mul_one] at h2
      nlinarith
    rw [hSg _ (by omega)] at ha
    rw [hSg _ hw] at ha'
    cases ha
    cases ha'
    have hidx : 4 * (n * n) * d + 2 * (n * (2 * (lo + j) + (if b then 0 else 1)) + i) =
        2 * (2 * (n * n) * d + n * (2 * (lo + j) + (if b then 0 else 1)) + i) := by ring
    have hidx' : 4 * (n * n) * d + (2 * (n * (2 * (lo + j) + (if b then 0 else 1)) + i) + 1) =
        2 * (2 * (n * n) * d + (n * (2 * (lo + j) + (if b then 0 else 1)) + i)) + 1 := by ring
    have hi : (i : ℕ) < n ∧ (j : ℕ) < n := ⟨by omega, by omega⟩
    obtain ⟨t, ht⟩ := t
    change t < 2 at ht
    change s₁.store.read p G (0 + (2 * ((i : ℕ) + k * j) + t)) = _
    interval_cases t
    · rw [zero_add, add_zero, hg]
      simp [pairLayout, leadingBlock, hi, eighTapeSample, M, eighTapeMachine,
        ScalarSem.toFloatMachine, ScalarSem.tapeNormal, hidx]
    · rw [zero_add, hg']
      simp [pairLayout, leadingBlock, hi, eighTapeSample, M, eighTapeMachine,
        ScalarSem.toFloatMachine, ScalarSem.tapeNormal, hidx', add_assoc]
  -- the two kernel calls
  obtain ⟨hY, hfr₂⟩ := hmm.holds_of_kcallStore_eq_some (fun _ => rfl) p (l := k) (m := k)
    (n := k) (a := (Pm, 0)) (b := (G, 0)) (c := (Y, 0))
    (hP.of_forall_read_eq fun i _ _ => hfr₁ p Pm i hPmG) hG (hne (Ne.symm hPmY))
    (hne (Ne.symm hGY)) hc₂
  obtain ⟨hQf, -, hfr₃⟩ := hqr.holds_of_kcallStore_eq_some (fun _ => rfl) p (m := k) (n := k)
    (a := (Y, 0)) (q := (Qf, 0)) (r := (Rf, 0)) hY (hne hQfRf) (hne (Ne.symm hYQf))
    (hne (Ne.symm hYRf)) hc₃
  -- the copy of the first `r` columns
  rw [exec_seq_skip] at h
  obtain ⟨hQa, hfr₄, hsh₄, hps₄⟩ := holds_of_exec_zcopy (I := I) p k r
    (A := Matrix.of fun i (j : Fin r) => (qrR (mmR Pmat
      ((leadingBlock k ((eighTapeSample n d lo).2 b)).map M.normal))).1 i
        ⟨j, lt_of_lt_of_le j.isLt hr⟩)
    (fun i j t => hQf i ⟨j, lt_of_lt_of_le j.isLt hr⟩ t) (hne (Ne.symm hQfQa))
    ((exec_seq_skip I _ _).trans h)
  refine ⟨?_, fun q b' i hb' hbd => ?_, ?_, ?_⟩
  · convert hQa using 1
    refine Matrix.ext fun i j => ?_
    simp only [deflate, dif_pos (lt_of_lt_of_le j.isLt hr), Matrix.of_apply]
    rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hb'
    rw [hfr₄ q b' i hbd, hfr₃ q b' i (hne hb'.2.2.1) (hne hb'.2.2.2), hfr₂ q b' i (hne hb'.2.1),
      hfr₁ q b' i hb'.1]
  · rw [hsh₄]
    change c₃.shape = _
    rw [Interp.shape_of_kcallStore_eq_some hc₃, Interp.shape_of_kcallStore_eq_some hc₂, hsh₁]
  · rw [hps₄]
    exact hps₁

omit [Inhabited K] in
/-- The test-matrix loop of a deflation succeeds when the words of `Sg` it reads and the cell `sq`
are initialised and `G` is long enough; it keeps the shape and every other buffer, and initialises
the first $2k^2$ words of `G`. -/
private theorem exists_exec_deflate_testLoop {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (n k lo s : ℕ) {Sg G lenG : ℕ}
    {sq : Cell ℕ ℕ} {sv : K} {st : St P K C} (hsqG : sq.buf ≠ G) (hSgG : Sg ≠ G)
    (hsq : st.store.read p sq.buf sq.idx.eval = some sv)
    (hSg : ∀ i j, i < k → j < k → ∀ t < 2, ∃ a,
      st.store.read p Sg (2 * (n * (2 * (lo + j) + s) + i) + t) = some a)
    (hG : st.store.shape[G]? = some (p, lenG)) (hlen : 2 * (k * k) ≤ lenG) :
    ∃ st', exec I (.loop (.const k) fun j => (forRange (ι := ι) (.const k) fun i => do
        ins (.bin p .mul ⟨G, zidx (.const k) (.var i) (.var j)⟩
          ⟨Sg, 2 * (.const n * (2 * (.const lo + .var j) + .const s) + .var i)⟩ sq)
        ins (.bin p .mul ⟨G, zidx (.const k) (.var i) (.var j) + 1⟩
          ⟨Sg, 2 * (.const n * (2 * (.const lo + .var j) + .const s) + .var i) + 1⟩ sq)).run)
      st = some st' ∧ st'.store.shape = st.store.shape ∧
      (∀ q b x, b ≠ G → st'.store.read q b x = st.store.read q b x) ∧
      ∀ w < 2 * (k * k), ∃ v, st'.store.read p G w = some v := by
  let R : ℕ → St P K C → Prop := fun c s₁ => s₁.store.shape = st.store.shape ∧
    (∀ q b x, b ≠ G → s₁.store.read q b x = st.store.read q b x) ∧
    ∀ w < 2 * c, ∃ v, s₁.store.read p G w = some v
  have hkeep : ∀ {s s' : Store P K} {x : ℕ} {z : K}, s.write p G x z = some s' →
      ∀ w, (∃ v, s.read p G w = some v) → ∃ v, s'.read p G w = some v := by
    intro s s' x z hw w ⟨v, hv⟩
    by_cases hwx : w = x
    · subst hwx; exact ⟨z, Store.read_of_write_eq_some hw⟩
    · exact ⟨v, (Store.read_of_write_eq_some_of_ne hw (Or.inr hwx)).trans hv⟩
  refine (exists_exec_loop_eq_some_of_forall (I := I) (n := .const k) (fun j s₁ => R (k * j) s₁)
    ⟨rfl, fun _ _ _ _ => rfl, fun w hw => absurd hw (by simp)⟩ ?_).imp
    fun st' h => ⟨h.1, h.2⟩
  intro j hj s₁ ⟨hsh₁, hfr₁, hw₁⟩
  simp only [IExp.eval_const] at hj
  change ∃ st', exec I (.seq (.loop (.const k) _) .skip) s₁ = some st' ∧ _
  simp only [exec_seq_skip]
  refine (exists_exec_loop_eq_some_of_forall (I := I) (n := .const k)
    (fun i s₂ => R (i + k * j) s₂) ⟨hsh₁, hfr₁, by simpa using hw₁⟩ ?_).imp
    fun st' h => ⟨h.1, by
      have := h.2
      rwa [IExp.eval_const, show k + k * j = k * (j + 1) by ring] at this⟩
  intro i hi s₂ ⟨hsh₂, hfr₂, hw₂⟩
  simp only [IExp.eval_const] at hi
  obtain ⟨a, ha⟩ := hSg i j hi hj 0 (by norm_num)
  obtain ⟨a', ha'⟩ := hSg i j hi hj 1 (by norm_num)
  obtain ⟨z, hz⟩ := hsem.bin_ok p .mul a sv trivial (fun h => nomatch h) trivial
  obtain ⟨z', hz'⟩ := hsem.bin_ok p .mul a' sv trivial (fun h => nomatch h) trivial
  have hidx : 2 * (i + k * j) + 1 < lenG := by nlinarith
  obtain ⟨w₁, hw₁'⟩ := Store.exists_write_eq_some_of_getElem?_shape (s := s₂.store) z
    (hsh₂ ▸ hG) (show 2 * (i + k * j) < lenG by omega)
  obtain ⟨w₂, hw₂'⟩ := Store.exists_write_eq_some_of_getElem?_shape (s := w₁) z'
    ((Store.shape_of_write_eq_some hw₁').trans hsh₂ ▸ hG) hidx
  have hsq₂ : s₂.store.read p sq.buf sq.idx.eval = some sv := (hfr₂ _ _ _ hsqG).trans hsq
  change ∃ st', exec I (.seq (.instr _) (.seq (.instr _) .skip)) s₂ = some st' ∧ R _ st'
  rw [exec_seq_instr_bin I (a := a) (c := sv) (by
        simp only [IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var,
          IExp.eval_ofNat]
        rw [hfr₂ _ _ _ hSgG]; simpa using ha) hsq₂ hz (by
        simpa [zidx] using hw₁'),
      exec_seq_instr_bin I (a := a') (c := sv) (by
        simp only [IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var,
          IExp.eval_ofNat]
        rw [Store.read_of_write_eq_some_of_ne hw₁' (Or.inl hSgG), hfr₂ _ _ _ hSgG]
        exact ha')
        ((Store.read_of_write_eq_some_of_ne hw₁' (Or.inl hsqG)).trans hsq₂) hz' (by
        simpa [zidx] using hw₂'), exec_skip]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · exact (Store.shape_of_write_eq_some hw₂').trans ((Store.shape_of_write_eq_some hw₁').trans hsh₂)
  · intro q b x hb
    rw [Store.read_of_write_eq_some_of_ne hw₂' (Or.inl hb),
      Store.read_of_write_eq_some_of_ne hw₁' (Or.inl hb), hfr₂ q b x hb]
  · intro w hw
    by_cases hw' : w < 2 * (i + k * j)
    · exact hkeep hw₂' w (hkeep hw₁' w (hw₂ w hw'))
    · by_cases he : w = 2 * (i + k * j) + 1
      · subst he; exact ⟨z', Store.read_of_write_eq_some hw₂'⟩
      · have he' : w = 2 * (i + k * j) := by omega
        subst he'
        exact hkeep hw₂' _ ⟨z, Store.read_of_write_eq_some hw₁'⟩

/-- Deflation on stored samples succeeds, with what it writes: some matrix at the block `qo`
of `Qa`, every other cell outside the scratch buffers unchanged, the shape kept. -/
private theorem exists_exec_eighDeflateBlock_facts {mm qr : ι}
    (hmm : IsMatMulKernel I mm pairLayout mmR) (hqr : IsQRKernel I qr pairLayout qrR)
    {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (n k r d lo : ℕ)
    (hk : lo + k ≤ n) (hr : r ≤ k) (b : Bool) {Sg Pm G Y Qf Rf Qa : ℕ} {sq : Cell ℕ ℕ}
    {qo : IExp ℕ} {st : St P K C} {Pmat : Matrix (Fin k) (Fin k) (K × K)}
    (hP : pairLayout.Holds st.store p Pm 0 Pmat)
    (hsq : st.store.read p sq.buf sq.idx.eval = some (I.sem.sqrtHalf p))
    (hSg : ∀ w < 4 * (n * n), ∃ v, st.store.read p Sg w = some v)
    (hbufs : [Sg, Pm, G, Y, Qf, Rf, Qa].Nodup) (hsqb : sq.buf ∉ [G, Y, Qf, Rf, Qa])
    (hscr : ∀ X ∈ [G, Y, Qf, Rf], ∃ len, st.store.shape[X]? = some (p, len) ∧ 2 * (n * n) ≤ len)
    (hQa : ∃ len, st.store.shape[Qa]? = some (p, len) ∧ qo.eval + 2 * (k * r) ≤ len) :
    ∃ st', exec I (eighDeflateBlock p mm qr (.const n) (.const k) (.const r) (.const lo)
      (if b then 0 else 1) Sg sq Pm G Y Qf Rf Qa qo).run st = some st' ∧
      (∃ Q : Matrix (Fin k) (Fin r) (K × K), pairLayout.Holds st'.store p Qa qo.eval Q) ∧
      (∀ q b' i, b' ∉ [G, Y, Qf, Rf] → blockDisjoint (b', i, 1) (Qa, qo.eval, 2 * (k * r)) = true →
        st'.store.read q b' i = st.store.read q b' i) ∧
      st'.store.shape = st.store.shape := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hbufs hsqb
  obtain ⟨⟨-, hSgG, -, -, -, -⟩, ⟨hPmG, hPmY, -, -, -⟩, ⟨hGY, -, -, -⟩, ⟨hYQf, hYRf, -⟩,
    ⟨hQfRf, hQfQa⟩, -, -⟩ := hbufs
  obtain ⟨hsG, -, -, -, -⟩ := hsqb
  have hne : ∀ {b b' i i' l l' : ℕ}, b ≠ b' → blockDisjoint (b, i, l) (b', i', l') = true :=
    fun h => by simp [blockDisjoint, h]
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hscr
  obtain ⟨⟨lG, hG, hlG⟩, ⟨lY, hYs, hlY⟩, ⟨lQ, hQs, hlQ⟩, ⟨lR, hRs, hlR⟩⟩ := hscr
  obtain ⟨lA, hQas, hlA⟩ := hQa
  have hkk : k * k ≤ n * n := Nat.mul_le_mul (by omega) (by omega)
  -- the test loop
  obtain ⟨s₁, h₁, hsh₁, hfr₁, hG₁⟩ := exists_exec_deflate_testLoop (I := I) hsem p n k lo
    (if b then 0 else 1) hsG hSgG hsq (fun i j hi hj t ht => hSg _ (by
      have h1 : 2 * (lo + j) + (if b then 0 else 1) + 1 ≤ 2 * n := by split <;> omega
      have h2 := Nat.mul_le_mul_left n h1
      rw [Nat.mul_add, Nat.mul_one] at h2
      nlinarith)) hG (by omega)
  have hXG : s₁.store.readBlock p G 0 (k * k * 2) = some ((List.range (k * k * 2)).toArray.map
      fun w => (s₁.store.read p G (0 + w)).getD default) :=
    Store.readBlock_eq_some_map_range _ fun w hw => by
      obtain ⟨v, hv⟩ := hG₁ w (by omega)
      rw [zero_add, hv]
      rfl
  have hXP := (EntryLayout.holds_iff_readBlock_eq_some pairLayout s₁.store p Pm 0 Pmat).mp
    (hP.of_forall_read_eq fun i _ _ => hfr₁ p Pm i hPmG)
  -- the product
  have hk₁ := hmm.kcallStore_eq p (l := k) (m := k) (n := k) (a := (Pm, 0)) (b := (G, 0))
    (c := (Y, 0)) hXP hXG (hne (Ne.symm hPmY)) (hne (Ne.symm hGY))
  obtain ⟨c₂, hc₂⟩ : ∃ c₂, I.kcallStore mm p [k, k, k] [(Pm, 0), (G, 0)] [(Y, 0)] s₁.store =
      some c₂ := by
    rw [hk₁]
    exact Store.exists_writeBlock_eq_some_of_getElem?_shape fun i hi => ⟨lY, hsh₁ ▸ hYs, by
      rw [EntryLayout.size_toArray] at hi
      change i < k * k * 2 at hi
      omega⟩
  have hYh := EntryLayout.holds_of_writeBlock_eq_some pairLayout (hk₁.symm.trans hc₂)
  have hsh₂ := (Interp.shape_of_kcallStore_eq_some hc₂).trans hsh₁
  -- the QR factorization
  have hk₂ := hqr.kcallStore_eq p (m := k) (n := k) (a := (Y, 0)) (q := (Qf, 0)) (r := (Rf, 0))
    ((EntryLayout.holds_iff_readBlock_eq_some pairLayout c₂ p Y 0 _).mp hYh) (hne hQfRf)
    (hne (Ne.symm hYQf)) (hne (Ne.symm hYRf))
  obtain ⟨c₃, hc₃⟩ : ∃ c₃, I.kcallStore qr p [k, k] [(Y, 0)] [(Qf, 0), (Rf, 0)] c₂ =
      some c₃ := by
    rw [hk₂]
    obtain ⟨c, hc⟩ := Store.exists_writeBlock_eq_some_of_getElem?_shape (s := c₂) (b := Qf)
      (off := 0) (xs := pairLayout.toArray (qrR (pairLayout.toMatrix k k
        (pairLayout.toArray (mmR (pairLayout.toMatrix k k (pairLayout.toArray Pmat))
          (pairLayout.toMatrix k k ((List.range (k * k * 2)).toArray.map
            fun w => (s₁.store.read p G (0 + w)).getD default)))))).1)
      fun i hi => ⟨lQ, hsh₂ ▸ hQs, by
        rw [EntryLayout.size_toArray] at hi
        change i < k * k * 2 at hi
        omega⟩
    rw [hc, Option.bind_some]
    exact Store.exists_writeBlock_eq_some_of_getElem?_shape fun i hi =>
      ⟨lR, (Store.shape_of_writeBlock_eq_some hc).trans hsh₂ ▸ hRs, by
        rw [EntryLayout.size_toArray] at hi
        change i < k * k * 2 at hi
        omega⟩
  obtain ⟨hQf, -, hfr₃⟩ := hqr.holds_of_kcallStore_eq_some (fun _ => rfl) p (m := k) (n := k)
    (a := (Y, 0)) (q := (Qf, 0)) (r := (Rf, 0)) hYh (hne hQfRf) (hne (Ne.symm hYQf))
    (hne (Ne.symm hYRf)) hc₃
  have hsh₃ := (Interp.shape_of_kcallStore_eq_some hc₃).trans hsh₂
  -- the run
  change ∃ st', exec I (.seq (.loop _ _) (.seq (.kcall _ _ _ _ _) (.seq (.kcall _ _ _ _ _)
    (.seq (.named _ _ _) .skip)))) st = some st' ∧ _
  rw [exec_seq, h₁, Option.bind_some, exec_seq, exec_kcall]
  simp only [List.map_cons, List.map_nil, IExp.eval_const, IExp.eval_zero]
  rw [hc₂, Option.map_some, Option.bind_some, exec_seq, exec_kcall]
  simp only [List.map_cons, List.map_nil, IExp.eval_const, IExp.eval_zero]
  rw [hc₃, Option.map_some, Option.bind_some]
  have key : ∀ S : St P K C, S.store = c₃ → ∃ st', exec I (zcopy (ι := ι) p (.const k) (.const r)
      Qf 0 Qa qo).run S = some st' ∧
      (∃ Q : Matrix (Fin k) (Fin r) (K × K), pairLayout.Holds st'.store p Qa qo.eval Q) ∧
      (∀ q b' i, b' ∉ [G, Y, Qf, Rf] →
        blockDisjoint (b', i, 1) (Qa, qo.eval, 2 * (k * r)) = true →
        st'.store.read q b' i = st.store.read q b' i) ∧
      st'.store.shape = st.store.shape := by
    intro S hS
    subst hS
    obtain ⟨Qm, hQm⟩ : ∃ Q : Matrix (Fin k) (Fin r) (K × K),
        pairLayout.Holds S.store p Qf (0 : IExp ℕ).eval Q :=
      ⟨_, fun i (j : Fin r) t => hQf i ⟨j, lt_of_lt_of_le j.isLt hr⟩ t⟩
    obtain ⟨st', hst'⟩ := exists_exec_zcopy (I := I) p k r (st := S) (X := Qf) (xo := 0)
      (Y := Qa) (yo := qo) hQm (hne (Ne.symm hQfQa)) ⟨lA, hsh₃ ▸ hQas, hlA⟩
    obtain ⟨hQa', hfrc, hshc, -⟩ := holds_of_exec_zcopy (I := I) p k r hQm (hne (Ne.symm hQfQa))
      hst'
    refine ⟨st', hst', ⟨_, hQa'⟩, fun q b' i hb' hbd => ?_, hshc.trans hsh₃⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hb'
    rw [hfrc q b' i hbd, hfr₃ q b' i (hne hb'.2.2.1) (hne hb'.2.2.2),
      Store.read_of_writeBlock_eq_some_of_ne (hk₁.symm.trans hc₂) (Or.inl hb'.2.1),
      hfr₁ q b' i hb'.1]
  exact key _ rfl

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
  exact (exists_exec_eighDeflateBlock_facts hmm hqr hsem p n k r d lo hk hr b hP hsq
    (fun w hw => ⟨_, hSg w hw⟩) hbufs hsqb hscr hQa).imp fun _ h => h.1

omit [Inhabited K] in
/-- A conjugate transpose keeps the shape of the store and the tape positions. -/
private theorem shape_pos_of_exec_zconjTranspose_compress (p : P) (m n : ℕ) {X Y : ℕ}
    {xo yo : IExp ℕ} {st st' : St P K C}
    (h : exec I (zconjTranspose (ι := ι) p (.const m) (.const n) X xo Y yo).run st = some st') :
    st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  have hins : ∀ {i : Instr P ℕ ℕ} {s s' : St P K C}, (∀ q d x, i ≠ .draw q d x) →
      exec I (.instr i) s = some s' → s'.store.shape = s.store.shape ∧ s'.pos = s.pos := by
    intro i s s' hi hs
    rw [exec_instr] at hs
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hs
    refine ⟨Instr.shape_of_run_eq_some hr, ?_⟩
    cases i with
    | draw q d x => exact absurd rfl (hi q d x)
    | _ => simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr; aesop
  change exec I (.seq (.named _ _ (.seq (.loop _ _) .skip)) .skip) st = some st' at h
  rw [exec_seq_skip, exec_named, exec_seq_skip] at h
  refine forall_of_exec_loop_eq_some I
    (fun _ s => s.store.shape = st.store.shape ∧ s.pos = st.pos) ⟨rfl, rfl⟩ ?_ h
  rintro j - s₁ s₂ ⟨hsh, hps⟩ hex
  change exec I (.seq (.loop _ _) .skip) s₁ = some s₂ at hex
  rw [exec_seq_skip] at hex
  refine forall_of_exec_loop_eq_some I
    (fun _ s => s.store.shape = st.store.shape ∧ s.pos = st.pos) ⟨hsh, hps⟩ ?_ hex
  rintro i - s₃ s₄ ⟨hsh, hps⟩ hex
  change exec I (.seq (.instr (.copy _ _ _)) (.seq (.instr (.un _ _ _ _)) .skip)) s₃ =
    some s₄ at hex
  rw [exec_seq] at hex
  obtain ⟨s₅, h₅, hex⟩ := Option.bind_eq_some_iff.mp hex
  rw [exec_seq_skip] at hex
  obtain ⟨hsh₅, hps₅⟩ := hins (by intro _ _ _ h; cases h) h₅
  obtain ⟨hsh₄, hps₄⟩ := hins (by intro _ _ _ h; cases h) hex
  exact ⟨hsh₄.trans (hsh₅.trans hsh), hps₄.trans (hps₅.trans hps)⟩

omit [Inhabited K] in
/-- Blocks of distinct buffers are disjoint. -/
private theorem blockDisjoint_of_ne_compress {b b' i i' l l' : ℕ} (h : b ≠ b') :
    blockDisjoint (b, i, l) (b', i', l') = true := by
  simp [blockDisjoint, h]

omit [Inhabited K] in
/-- Disjointness of blocks is symmetric. -/
private theorem blockDisjoint_comm_compress {x y : ℕ × ℕ × ℕ} (h : blockDisjoint x y = true) :
    blockDisjoint y x = true := by
  simp only [blockDisjoint, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
  omega

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
  intro M
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hbufs hcells
  obtain ⟨⟨hQaMa, hQaQh, hQaC1, hQaC2, hQaC3⟩, ⟨hMaQh, hMaC1, hMaC2, hMaC3⟩, ⟨hQhC1, hQhC2, hQhC3⟩,
    ⟨hC1C2, hC1C3⟩, hC2C3, -⟩ := hbufs
  obtain ⟨⟨htQh, htC1, htC2, htC3⟩, hsQh, hsC1, hsC2, hsC3⟩ := hcells
  have hne := @blockDisjoint_of_ne_compress
  change exec I (.seq (.named _ _ _) (.seq (.kcall _ _ _ _ _) (.seq (.kcall _ _ _ _ _)
    (.seq (.named _ _ _) (.seq (.named _ _ _) .skip))))) st = some st' at h
  rw [exec_seq] at h
  obtain ⟨s₁, h₁, h⟩ := Option.bind_eq_some_iff.mp h
  rw [exec_seq] at h
  obtain ⟨s₂, h₂, h⟩ := Option.bind_eq_some_iff.mp h
  rw [exec_seq] at h
  obtain ⟨s₃, h₃, h⟩ := Option.bind_eq_some_iff.mp h
  rw [exec_seq] at h
  obtain ⟨s₄, h₄, h⟩ := Option.bind_eq_some_iff.mp h
  -- the conjugate transpose
  have h₁' := (exec_seq_skip I _ st).trans h₁
  obtain ⟨hQh, hfr₁⟩ := holds_of_exec_zconjTranspose (I := I) (toNat := toNat) (mmR := mmR)
    (qrR := qrR) (unif := unif) (normal := normal) p k r hQ (hne (Ne.symm hQaQh)) h₁'
  obtain ⟨hsh₁, hps₁⟩ := shape_pos_of_exec_zconjTranspose_compress p k r h₁'
  -- the two products
  rw [exec_kcall] at h₂ h₃
  obtain ⟨c₁, hc₁, hs₂⟩ := Option.map_eq_some_iff.mp h₂
  obtain ⟨c₂', hc₂, hs₃⟩ := Option.map_eq_some_iff.mp h₃
  have e₂ : s₂.store = c₁ := by rw [← hs₂]
  have e₃ : s₃.store = c₂' := by rw [← hs₃]
  have p₂ : s₂.pos = s₁.pos := by rw [← hs₂]
  have p₃ : s₃.pos = s₂.pos := by rw [← hs₃]
  rw [← e₂] at hc₁
  rw [← e₃] at hc₂
  obtain ⟨hC1, hfr₂⟩ := hmm.holds_of_kcallStore_eq_some (fun _ => rfl) p (l := r) (m := k)
    (n := k) (a := (Qh, 0)) (b := (Ma, mo.eval)) (c := (C1, 0)) hQh
    (hA.of_forall_read_eq fun i _ _ => hfr₁ p Ma i (hne hMaQh)) (hne (Ne.symm hQhC1))
    (hne (Ne.symm hMaC1)) hc₁
  obtain ⟨hC2, hfr₃⟩ := hmm.holds_of_kcallStore_eq_some (fun _ => rfl) p (l := r) (m := k)
    (n := r) (a := (C1, 0)) (b := (Qa, qo.eval)) (c := (C2, 0)) hC1
    (hQ.of_forall_read_eq fun i _ _ => (hfr₂ p Qa i (hne hQaC1)).trans
      (hfr₁ p Qa i (hne hQaQh))) (hne (Ne.symm hC1C2)) (hne (Ne.symm hQaC2)) hc₂
  -- the cells `two` and `sg` are kept so far
  have hkeep : ∀ c : Cell ℕ ℕ, c.buf ≠ Qh → c.buf ≠ C1 → c.buf ≠ C2 →
      s₃.store.read p c.buf c.idx.eval = st.store.read p c.buf c.idx.eval := fun c h1 h2 h3 =>
    (hfr₃ p _ _ (hne h3)).trans ((hfr₂ p _ _ (hne h2)).trans (hfr₁ p _ _ (hne h1)))
  -- the average and the shift
  have h₄' := (exec_seq_skip I _ s₃).trans h₄
  obtain ⟨hC3, hfr₄, hsh₄, hps₄⟩ := holds_of_exec_zhermAvg (I := I) (toNat := toNat)
    (mmR := mmR) (qrR := qrR) (unif := unif) (normal := normal) p r hC2
    ((hkeep two htQh htC1 htC2).trans htwo) (hne (Ne.symm hC2C3)) (hne htC3) h₄'
  rw [exec_seq_skip] at h
  have h' := (exec_seq_skip I _ s₄).trans h
  obtain ⟨hMa, hfr₅, hsh₅, hps₅⟩ := holds_of_exec_zhermShift (I := I) (toNat := toNat)
    (mmR := mmR) (qrR := qrR) (unif := unif) (normal := normal) p r hC3
    ((hfr₄ p _ _ (hne hsC3)).trans ((hkeep sg hsQh hsC1 hsC2).trans hσ)) (hne hMaC3)
    (blockDisjoint_comm_compress hcocells.2) h'
  refine ⟨hMa, fun q b i hb hbd => ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hb
    rw [hfr₅ q b i hbd, hfr₄ q b i (hne hb.2.2.2), hfr₃ q b i (hne hb.2.2.1),
      hfr₂ q b i (hne hb.2.1), hfr₁ q b i (hne hb.1)]
  · rw [hsh₅, hsh₄, Interp.shape_of_kcallStore_eq_some hc₂,
      Interp.shape_of_kcallStore_eq_some hc₁, hsh₁]
  · rw [hps₅, hps₄, p₃, p₂, hps₁]

omit [Inhabited K] in
/-- A write in a block of a buffer of a fixed shape: it succeeds, keeps the shape and every cell
outside the block, leaves the value at the written cell and keeps every initialised cell
initialised. -/
private theorem compress_zw {s₀ s : Store P K} {p : P} {Y yo len k N : ℕ}
    (hY : s₀.shape[Y]? = some (p, len)) (hlen : yo + N ≤ len) (hk : k < N)
    (hsh : s.shape = s₀.shape)
    (hfr : ∀ q b i, blockDisjoint (b, i, 1) (Y, yo, N) = true → s.read q b i = s₀.read q b i)
    (v : K) :
    ∃ s', s.write p Y (yo + k) v = some s' ∧ s'.shape = s₀.shape ∧
      (∀ q b i, blockDisjoint (b, i, 1) (Y, yo, N) = true → s'.read q b i = s₀.read q b i) ∧
      s'.read p Y (yo + k) = some v ∧
      (∀ b i, (∃ w, s.read p b i = some w) → ∃ w, s'.read p b i = some w) := by
  obtain ⟨s', hs'⟩ := Store.exists_write_eq_some_of_getElem?_shape v (by rw [hsh]; exact hY)
    (show yo + k < len by omega)
  refine ⟨s', hs', (Store.shape_of_write_eq_some hs').trans hsh, fun q b i hb => ?_,
    Store.read_of_write_eq_some hs', fun b i ⟨w, hw⟩ => ?_⟩
  · refine (Store.read_of_write_eq_some_of_ne hs' ?_).trans (hfr q b i hb)
    simp only [blockDisjoint, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hb
    by_cases hbY : b = Y
    · exact Or.inr (by omega)
    · exact Or.inl hbY
  · by_cases hbi : b = Y ∧ i = yo + k
    · obtain ⟨rfl, rfl⟩ := hbi
      exact ⟨v, Store.read_of_write_eq_some hs'⟩
    · exact ⟨w, (Store.read_of_write_eq_some_of_ne hs' (not_and_or.mp hbi)).trans hw⟩

omit [Inhabited K] in
private theorem compress_bind {α β : Type} {o : Option α} {f : α → Option β} (R : α → Prop)
    (h₁ : ∃ a, o = some a ∧ R a) (h₂ : ∀ a, R a → ∃ b, f a = some b) :
    ∃ b, o.bind f = some b := by
  obtain ⟨a, rfl, ha⟩ := h₁
  exact h₂ a ha

omit [Inhabited K] in
/-- **A conjugate transpose succeeds** under the standard model when the output block fits. -/
private theorem compress_exists_zconjTranspose {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (m n : ℕ) {X Y : ℕ}
    {xo yo : IExp ℕ} {st : St P K C} {A : Matrix (Fin m) (Fin n) (K × K)}
    (hA : pairLayout.Holds st.store p X xo.eval A)
    (hXY : blockDisjoint (Y, yo.eval, 2 * (n * m)) (X, xo.eval, 2 * (m * n)) = true)
    (hY : ∃ len, st.store.shape[Y]? = some (p, len) ∧ yo.eval + 2 * (n * m) ≤ len) :
    ∃ st', exec I (zconjTranspose (ι := ι) p (.const m) (.const n) X xo Y yo).run st =
      some st' := by
  obtain ⟨len, hYsh, hlen⟩ := hY
  let F : Store P K → Prop := fun s => s.shape = st.store.shape ∧
    ∀ q b i, blockDisjoint (b, i, 1) (Y, yo.eval, 2 * (n * m)) = true →
      s.read q b i = st.store.read q b i
  change ∃ st', exec I (.seq (.named _ _ (.seq (.loop _ _) .skip)) .skip) st = some st'
  rw [exec_seq_skip, exec_named, exec_seq_skip]
  refine (exists_exec_loop_eq_some_of_forall I (fun _ σ => F σ.store)
    ⟨rfl, fun _ _ _ _ => rfl⟩ fun j hj σ hσ => ?_).imp fun _ h => h.1
  have hj : j < m := hj
  change ∃ st', exec I (.seq (.loop _ _) .skip) σ = some st' ∧ _
  rw [exec_seq_skip]
  refine exists_exec_loop_eq_some_of_forall I (fun _ σ => F σ.store) hσ fun i hi σ' hσ' => ?_
  have hi : i < n := hi
  have hY1 : 2 * (i + n * j) + 1 < 2 * (n * m) := by nlinarith
  have hX1 : 2 * (j + m * i) + 1 < 2 * (m * n) := by nlinarith
  have hrX : ∀ t < 2, ∃ a, σ'.store.read p X (xo.eval + (2 * (j + m * i) + t)) = some a := by
    intro t ht
    rw [hσ'.2 _ _ _ ?_]
    · exact ⟨_, hA ⟨j, hj⟩ ⟨i, hi⟩ ⟨t, ht⟩⟩
    · simp only [blockDisjoint, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hXY ⊢
      omega
  obtain ⟨a, ha⟩ := hrX 0 (by norm_num)
  obtain ⟨a', ha'⟩ := hrX 1 (by norm_num)
  obtain ⟨s₁, hs₁, hsh₁, hfr₁, -, -⟩ := compress_zw (k := 2 * (i + n * j)) hYsh hlen
    (by omega) hσ'.1 hσ'.2 a
  obtain ⟨z, hz, -⟩ := hsem.neg p a'
  obtain ⟨s₂, hs₂, hsh₂, hfr₂, -, -⟩ := compress_zw (k := 2 * (i + n * j) + 1) hYsh hlen
    hY1 hsh₁ hfr₁ z
  have ha'₁ : s₁.read p X (xo.eval + (2 * (j + m * i) + 1)) = some a' := by
    rw [hfr₁ _ _ _ ?_, ← hσ'.2 _ _ _ ?_]
    · exact ha'
    all_goals simp only [blockDisjoint, Bool.or_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hXY ⊢
    all_goals omega
  change ∃ st', exec I (.seq (.instr (.copy _ _ _)) (.seq (.instr (.un _ _ _ _)) .skip)) σ' =
    some st' ∧ _
  rw [exec_seq_instr_copy I (by exact ha) (by exact hs₁),
    exec_seq_instr_un I (by exact ha'₁) hz (by exact hs₂), exec_skip]
  exact ⟨_, rfl, hsh₂, hfr₂⟩

/-- **`zhermShift` succeeds** under the standard model when the output block fits, wherever the
cell of the shift is (it may lie in the output block). -/
private theorem compress_exists_zhermShift {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (n : ℕ) {X Y : ℕ}
    {xo yo : IExp ℕ} {c : Cell ℕ ℕ} {st : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)}
    (hA : pairLayout.Holds st.store p X xo.eval A)
    (hc : ∃ cv, st.store.read p c.buf c.idx.eval = some cv)
    (hXY : blockDisjoint (Y, yo.eval, 2 * (n * n)) (X, xo.eval, 2 * (n * n)) = true)
    (hY : ∃ len, st.store.shape[Y]? = some (p, len) ∧ yo.eval + 2 * (n * n) ≤ len) :
    ∃ st', exec I (zhermShift (ι := ι) p (.const n) X xo c Y yo).run st = some st' := by
  obtain ⟨len, hYsh, hlen⟩ := hY
  have hn : ∀ i j : ℕ, i < n → j < n → 2 * (i + n * j) + 1 < 2 * (n * n) := by
    intro i j hi hj; nlinarith
  let G : Store P K → (ℕ → ℕ → Prop) → Prop := fun s S => s.shape = st.store.shape ∧
    (∀ q b i, blockDisjoint (b, i, 1) (Y, yo.eval, 2 * (n * n)) = true →
      s.read q b i = st.store.read q b i) ∧
    (∀ b i, (∃ w, st.store.read p b i = some w) → ∃ w, s.read p b i = some w) ∧
    ∀ i j, S i j → (∃ v, s.read p Y (yo.eval + 2 * (i + n * j)) = some v) ∧
      ∃ v, s.read p Y (yo.eval + 2 * (i + n * j) + 1) = some v
  have hXr : ∀ s S, G s S → ∀ i j, i < n → j < n → ∀ t < 2,
      ∃ a, s.read p X (xo.eval + (2 * (i + n * j) + t)) = some a := by
    intro s S hG i j hi hj t ht
    have := hn i j hi hj
    rw [hG.2.1 _ _ _ ?_]
    · exact ⟨_, hA ⟨i, hi⟩ ⟨j, hj⟩ ⟨t, ht⟩⟩
    · simp only [blockDisjoint, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hXY ⊢
      omega
  -- one write in the block keeps `G`
  have hw : ∀ s S, G s S → ∀ k < 2 * (n * n), ∀ v : K, ∃ s', s.write p Y (yo.eval + k) v =
      some s' ∧ G s' S ∧ s'.read p Y (yo.eval + k) = some v ∧
      ∀ b i, (∃ w, s.read p b i = some w) → ∃ w, s'.read p b i = some w := by
    intro s S hG k hk v
    obtain ⟨s', hs', hsh', hfr', hrd', hmo'⟩ := compress_zw hYsh hlen hk hG.1 hG.2.1 v
    exact ⟨s', hs', ⟨hsh', hfr', fun b i h => hmo' b i (hG.2.2.1 b i h), fun i j h =>
      ⟨hmo' _ _ (hG.2.2.2 i j h).1, hmo' _ _ (hG.2.2.2 i j h).2⟩⟩, hrd', hmo'⟩
  change ∃ st', exec I (.seq (.named _ _ (.seq (.loop _ _) (.seq (.loop _ _) _))) .skip) st =
    some st'
  rw [exec_seq_skip, exec_named, exec_seq]
  -- the strict upper triangle
  refine compress_bind (fun σ => G σ.store fun i' j' => i' < j' ∧ j' < n)
    ((exists_exec_loop_eq_some_of_forall I
    (fun j σ => G σ.store fun i' j' => i' < j' ∧ j' < j)
      ⟨rfl, fun _ _ _ _ => rfl, fun _ _ h => h, fun _ _ h => absurd h.2 (Nat.not_lt_zero _)⟩
      (fun j hj σ hσ => by
        have hj : j < n := hj
        change ∃ st', exec I (.seq (.loop _ _) .skip) σ = some st' ∧ _
        rw [exec_seq_skip]
        refine (exists_exec_loop_eq_some_of_forall I
          (fun i σ' => G σ'.store fun i' j' => i' < j' ∧ (j' < j ∨ j' = j ∧ i' < i))
          ⟨hσ.1, hσ.2.1, hσ.2.2.1, fun i' j' h => hσ.2.2.2 i' j' ⟨h.1, by omega⟩⟩
          (fun i hi σ' hσ' => by
            have hi : i < j := hi
            have hk := hn i j (by omega) hj
            obtain ⟨a, ha⟩ := hXr _ _ hσ' i j (by omega) hj 0 (by norm_num)
            obtain ⟨s₁, hs₁, hG₁, hr₁, hm₁⟩ := hw _ _ hσ' (2 * (i + n * j)) (by omega) a
            obtain ⟨a'', ha''⟩ := hXr _ _ hG₁ i j (by omega) hj 1 (by norm_num)
            change ∃ st', exec I (.seq (.instr (.copy _ _ _)) (.seq (.instr (.copy _ _ _))
              .skip)) σ' = some st' ∧ _
            rw [exec_seq_instr_copy I (by exact ha) (by exact hs₁)]
            obtain ⟨s₂', hs₂', hG₂', hr₂', hm₂'⟩ := hw _ _ hG₁ (2 * (i + n * j) + 1) hk a''
            rw [exec_seq_instr_copy I (by exact ha'') (by exact hs₂'), exec_skip]
            refine ⟨_, rfl, hG₂'.1, hG₂'.2.1, hG₂'.2.2.1, fun i' j' h => ?_⟩
            by_cases hij : i' = i ∧ j' = j
            · obtain ⟨rfl, rfl⟩ := hij
              exact ⟨hm₂' _ _ ⟨_, hr₁⟩, ⟨_, hr₂'⟩⟩
            · have := hσ'.2.2.2 i' j' ⟨h.1, by omega⟩
              exact ⟨hm₂' _ _ (hm₁ _ _ this.1), hm₂' _ _ (hm₁ _ _ this.2)⟩)).imp
          fun σ' ⟨h', hG'⟩ => ⟨h', hG'.1, hG'.2.1, hG'.2.2.1, fun i' j' h =>
            hG'.2.2.2 i' j' ⟨h.1, by simp only [IExp.eval_var]; omega⟩⟩))) fun σ₁ hσ₁ => ?_
  rw [exec_seq]
  -- the diagonal
  refine compress_bind (fun σ => G σ.store fun i' j' => i' < j' ∧ j' < n)
    (exists_exec_loop_eq_some_of_forall I
    (fun _ σ => G σ.store fun i' j' => i' < j' ∧ j' < n) hσ₁ (fun i hi σ hσ => by
        have hi : i < n := hi
        have hk := hn i i hi hi
        obtain ⟨a, ha⟩ := hXr _ _ hσ i i hi hi 0 (by norm_num)
        obtain ⟨cv, hcv⟩ := hσ.2.2.1 _ _ hc
        obtain ⟨v, hv⟩ := hsem.bin_ok p .sub a cv trivial nofun trivial
        obtain ⟨s₁, hs₁, hG₁, -, -⟩ := hw _ _ hσ (2 * (i + n * i)) (by omega) v
        obtain ⟨z, hz⟩ := hsem.lit_ok p 0 trivial
        obtain ⟨s₂, hs₂, hG₂, -, -⟩ := hw _ _ hG₁ (2 * (i + n * i) + 1) hk z
        change ∃ st', exec I (.seq (.instr (.bin _ _ _ _ _)) (.seq (.instr (.lit _ _ _))
          .skip)) σ = some st' ∧ _
        rw [exec_seq_instr_bin I (by exact ha) hcv hv (by exact hs₁),
          exec_seq_instr_lit I hz (by exact hs₂), exec_skip]
        exact ⟨_, rfl, hG₂⟩)) fun σ₂ hσ₂ => ?_
  -- the mirror
  refine exists_exec_zmirror p n (B := fun i j =>
    ((σ₂.store.read p Y (yo.eval + 2 * (i + n * j))).getD default,
      (σ₂.store.read p Y (yo.eval + 2 * (i + n * j) + 1)).getD default))
    (fun i j hij => ?_) hsem ⟨len, by rw [hσ₂.1]; exact hYsh, hlen⟩
  obtain ⟨⟨v, hv⟩, ⟨w, hw'⟩⟩ := hσ₂.2.2.2 i j ⟨hij, j.2⟩
  simp only [hv, hw', Option.getD_some, and_self]

omit [AddMonoid C] in
/-- **A product kernel call on held matrices succeeds** when the output block fits. -/
private theorem compress_exists_kcall {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
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
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hbufs hcells
  obtain ⟨⟨hQaMa, hQaQh, hQaC1, hQaC2, hQaC3⟩, ⟨hMaQh, hMaC1, hMaC2, hMaC3⟩, ⟨hQhC1, hQhC2, hQhC3⟩,
    ⟨hC1C2, hC1C3⟩, hC2C3, -⟩ := hbufs
  obtain ⟨⟨htQh, htC1, htC2, htC3⟩, hsQh, hsC1, hsC2, hsC3⟩ := hcells
  have hne := @blockDisjoint_of_ne_compress
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hscr
  obtain ⟨⟨lQh, hQhs, hlQh⟩, ⟨l1, h1s, hl1⟩, ⟨l2, h2s, hl2⟩, ⟨l3, h3s, hl3⟩⟩ := hscr
  obtain ⟨lM, hMs, hlM⟩ := hcolen
  have hrn : r ≤ n := hr.trans hk
  have hrk : r * k ≤ n * n := Nat.mul_le_mul hrn hk
  have hrr : r * r ≤ n * n := Nat.mul_le_mul hrn hrn
  -- the conjugate transpose
  obtain ⟨s₁, h₁⟩ := compress_exists_zconjTranspose (I := I) hsem p k r (X := Qa) (Y := Qh)
    (xo := qo) (yo := 0) hQ (hne (Ne.symm hQaQh))
    ⟨lQh, hQhs, by simp only [IExp.eval_zero]; nlinarith⟩
  obtain ⟨hQh, hfr₁⟩ := holds_of_exec_zconjTranspose (I := I) (toNat := fun _ => 0) (mmR := mmR)
    (qrR := @fun _ _ X => (Matrix.of fun _ _ => default, X)) (unif := fun x (_ : Unit) => x)
    (normal := fun (_ : Unit) => ((default : K), (default : K))) p k r hQ
    (hne (Ne.symm hQaQh)) h₁
  obtain ⟨hsh₁, -⟩ := shape_pos_of_exec_zconjTranspose_compress p k r h₁
  -- the first product
  obtain ⟨c₁, hc₁⟩ := compress_exists_kcall (I := I) hmm p (l := r) (m := k) (n := k)
    (a := (Qh, 0)) (b := (Ma, mo.eval)) (c := (C1, 0)) hQh
    (hA.of_forall_read_eq fun i _ _ => hfr₁ p Ma i (hne hMaQh)) (hne (Ne.symm hQhC1))
    (hne (Ne.symm hMaC1)) (by rw [hsh₁]; exact h1s) (by nlinarith)
  obtain ⟨hC1, hfr₂⟩ := hmm.holds_of_kcallStore_eq_some (fun _ => rfl) p (l := r) (m := k)
    (n := k) (a := (Qh, 0)) (b := (Ma, mo.eval)) (c := (C1, 0)) hQh
    (hA.of_forall_read_eq fun i _ _ => hfr₁ p Ma i (hne hMaQh)) (hne (Ne.symm hQhC1))
    (hne (Ne.symm hMaC1)) hc₁
  have hsh₂ := (Interp.shape_of_kcallStore_eq_some hc₁).trans hsh₁
  -- the second product
  have hQ₂ : pairLayout.Holds c₁ p Qa qo.eval Q := hQ.of_forall_read_eq fun i _ _ =>
    (hfr₂ p Qa i (hne hQaC1)).trans (hfr₁ p Qa i (hne hQaQh))
  obtain ⟨c₂', hc₂⟩ := compress_exists_kcall (I := I) hmm p (l := r) (m := k) (n := r)
    (a := (C1, 0)) (b := (Qa, qo.eval)) (c := (C2, 0)) hC1 hQ₂ (hne (Ne.symm hC1C2))
    (hne (Ne.symm hQaC2)) (by rw [hsh₂]; exact h2s) (by nlinarith)
  obtain ⟨hC2, hfr₃⟩ := hmm.holds_of_kcallStore_eq_some (fun _ => rfl) p (l := r) (m := k)
    (n := r) (a := (C1, 0)) (b := (Qa, qo.eval)) (c := (C2, 0)) hC1 hQ₂ (hne (Ne.symm hC1C2))
    (hne (Ne.symm hQaC2)) hc₂
  have hsh₃ := (Interp.shape_of_kcallStore_eq_some hc₂).trans hsh₂
  have hkeep : ∀ c : Cell ℕ ℕ, c.buf ≠ Qh → c.buf ≠ C1 → c.buf ≠ C2 →
      c₂'.read p c.buf c.idx.eval = st.store.read p c.buf c.idx.eval := fun c h1 h2 h3 =>
    (hfr₃ p _ _ (hne h3)).trans ((hfr₂ p _ _ (hne h2)).trans (hfr₁ p _ _ (hne h1)))
  -- the run
  change ∃ st', exec I (.seq (.named _ _ _) (.seq (.kcall _ _ _ _ _) (.seq (.kcall _ _ _ _ _)
    (.seq (.named _ _ _) (.seq (.named _ _ _) .skip))))) st = some st'
  change exec I (.seq (.named _ _ _) .skip) st = some s₁ at h₁
  rw [exec_seq_skip] at h₁
  rw [exec_seq, h₁, Option.bind_some, exec_seq]
  refine compress_bind (fun σ => σ.store = c₁) ⟨_, by
    rw [exec_kcall]
    simp only [List.map_cons, List.map_nil, IExp.eval_const, IExp.eval_zero]
    rw [hc₁]; rfl, rfl⟩ ?_
  rintro σ₂ hσ₂
  rw [exec_seq]
  refine compress_bind (fun σ => σ.store = c₂') ⟨_, by
    rw [exec_kcall]
    simp only [List.map_cons, List.map_nil, IExp.eval_const, IExp.eval_zero]
    rw [hσ₂, hc₂]; rfl, rfl⟩ ?_
  rintro σ₃ hσ₃
  -- the average
  have htwo₃ : σ₃.store.read p two.buf two.idx.eval = some c₂ := by
    rw [hσ₃, hkeep two htQh htC1 htC2]; exact htwo
  have hC2₃ : pairLayout.Holds σ₃.store p C2 (0 : IExp ℕ).eval
      (mmR (mmR ((I.sem.toFloatMachine p (fun _ => 0) mmR
        (@fun _ _ X => (Matrix.of fun _ _ => default, X)) (fun x (_ : Unit) => x)
        (fun (_ : Unit) => ((default : K), (default : K)))).conjTransposeMat Q) A) Q) := by
    rw [hσ₃]; exact hC2
  obtain ⟨s₄, h₄⟩ := exists_exec_zhermAvg (I := I) p r (st := σ₃) (Y := C3) (yo := 0) hsem htwo0
    hC2₃ htwo₃ (hne (Ne.symm hC2C3)) (hne htC3)
    ⟨l3, by rw [hσ₃, hsh₃]; exact h3s, by simp only [IExp.eval_zero]; nlinarith⟩
  obtain ⟨hC3, hfr₄, hsh₄, -⟩ := holds_of_exec_zhermAvg (I := I) (toNat := fun _ => 0)
    (mmR := mmR) (qrR := @fun _ _ X => (Matrix.of fun _ _ => default, X))
    (unif := fun x (_ : Unit) => x) (normal := fun (_ : Unit) => ((default : K), (default : K)))
    p r hC2₃ htwo₃ (hne (Ne.symm hC2C3)) (hne htC3) h₄
  change exec I (.seq (.named _ _ _) .skip) σ₃ = some s₄ at h₄
  rw [exec_seq_skip] at h₄
  rw [exec_seq, h₄, Option.bind_some, exec_seq_skip]
  -- the shift
  obtain ⟨s₅, h₅⟩ := compress_exists_zhermShift (I := I) hsem p r (st := s₄) (X := C3)
    (xo := 0) (Y := Ma) (yo := co) (c := sg) hC3
    ⟨σ, by rw [hfr₄ p _ _ (hne hsC3), hσ₃, hkeep sg hsQh hsC1 hsC2]; exact hσ⟩
    (hne hMaC3) ⟨lM, by rw [hsh₄, hσ₃, hsh₃]; exact hMs, hlM⟩
  change exec I (.seq (.named _ _ _) .skip) s₄ = some s₅ at h₅
  rw [exec_seq_skip] at h₅
  exact ⟨s₅, h₅⟩

omit [Inhabited K] in
/-- An allocation succeeds when its body succeeds on the allocated state. -/
private theorem exists_exec_alloc_of_exists_split {p : P} {len : IExp ℕ}
    {body : ℕ → Stmt P ι ℕ ℕ} {st : St P K C}
    (h : ∃ st', exec I (body st.store.size) { st with
          store := st.store.push (p, Array.replicate len.eval none),
          cur := Function.update st.cur p (st.cur p + len.eval),
          peak := Function.update st.peak p (max (st.peak p) (st.cur p + len.eval)),
          curW := st.curW + len.eval * I.width p,
          peakW := max st.peakW (st.curW + len.eval * I.width p) } = some st') :
    ∃ st', exec I (.alloc p len body) st = some st' := by
  obtain ⟨st', h⟩ := h
  exact ⟨_, by rw [exec_alloc, h]; rfl⟩

omit [Inhabited K] in
/-- A deflation block, then the rest: the run of the block, then the rest. -/
private theorem exec_eighDeflateBlock_bind_split (p : P) (mm qr : ι) (n k r lo : IExp ℕ)
    (side : ℕ) (Sg : ℕ) (sq : Cell ℕ ℕ) (Pm G Y Qf Rf Qa : ℕ) (qo : IExp ℕ)
    (f : Unit → Builder P ι ℕ ℕ Unit) (st : St P K C) :
    exec I (eighDeflateBlock p mm qr n k r lo side Sg sq Pm G Y Qf Rf Qa qo >>= f).run st =
      (exec I (eighDeflateBlock p mm qr n k r lo side Sg sq Pm G Y Qf Rf Qa qo).run st).bind
        (exec I (f ()).run) := by
  change exec I (.seq _ (.seq _ (.seq _ (.seq _ _)))) st =
    (exec I (.seq _ (.seq _ (.seq _ (.seq _ .skip)))) st).bind _
  simp only [exec_seq, Option.bind_assoc, exec_skip, Option.bind_some]
  rfl

omit [Inhabited K] in
/-- A compression block, then the rest: the run of the block, then the rest. -/
private theorem exec_eighCompressBlock_bind_split (p : P) (mm : ι) (k r : IExp ℕ) (Qa : ℕ)
    (qo : IExp ℕ) (Ma : ℕ) (mo co : IExp ℕ) (two sg : Cell ℕ ℕ) (Qh C1 C2 C3 : ℕ)
    (f : Unit → Builder P ι ℕ ℕ Unit) (st : St P K C) :
    exec I (eighCompressBlock p mm k r Qa qo Ma mo co two sg Qh C1 C2 C3 >>= f).run st =
      (exec I (eighCompressBlock p mm k r Qa qo Ma mo co two sg Qh C1 C2 C3).run st).bind
        (exec I (f ()).run) := by
  change exec I (.seq _ (.seq _ (.seq _ (.seq _ (.seq _ _))))) st =
    (exec I (.seq _ (.seq _ (.seq _ (.seq _ (.seq _ .skip))))) st).bind _
  simp only [exec_seq, Option.bind_assoc, exec_skip, Option.bind_some]
  rfl

omit [Inhabited K] in
/-- A deflation block at an index expression for the rank runs as at its value. -/
private theorem exec_eighDeflateBlock_congr_split (p : P) (mm qr : ι) (n k r lo : IExp ℕ)
    (side : ℕ) (Sg : ℕ) (sq : Cell ℕ ℕ) (Pm G Y Qf Rf Qa : ℕ) (qo : IExp ℕ) (st : St P K C) :
    exec I (eighDeflateBlock p mm qr n k r lo side Sg sq Pm G Y Qf Rf Qa qo).run st =
      exec I (eighDeflateBlock p mm qr n k (.const r.eval) lo side Sg sq Pm G Y Qf Rf Qa
        qo).run st :=
  exec_eq_of_normIdx_eq I rfl st

omit [Inhabited K] in
/-- A compression block at an index expression for the rank runs as at its value. -/
private theorem exec_eighCompressBlock_congr_split (p : P) (mm : ι) (k r : IExp ℕ) (Qa : ℕ)
    (qo : IExp ℕ) (Ma : ℕ) (mo co : IExp ℕ) (two sg : Cell ℕ ℕ) (Qh C1 C2 C3 : ℕ)
    (st : St P K C) :
    exec I (eighCompressBlock p mm k r Qa qo Ma mo co two sg Qh C1 C2 C3).run st =
      exec I (eighCompressBlock p mm k (.const r.eval) Qa qo Ma mo co two sg Qh C1 C2
        C3).run st :=
  exec_eq_of_normIdx_eq I rfl st

/-- A packed complex entry lies in its block. -/
private theorem pair_idx_lt_split {l m : ℕ} (i : Fin l) (j : Fin m) (t : Fin 2) :
    2 * ((i : ℕ) + l * j) + t < 2 * (l * m) := by
  have := i.2; have := j.2; have := t.2
  have : l * ((j : ℕ) + 1) ≤ l * m := Nat.mul_le_mul_left l j.2
  nlinarith

/-- The index arithmetic of a split: the blocks of the bases and of the compressions fit their
arenas, and the compressions lie past the node's block. -/
private theorem eighSplit_bounds_split {n d lo k kp D : ℕ} (hk : lo + k ≤ n) (hkpk : kp < k)
    (hd : d < D) :
    2 * (n * n) * d + 2 * n * lo + 2 * (k * kp) ≤ 2 * (n * n) * D ∧
      2 * (n * n) * d + 2 * n * lo + 2 * (k * kp) + 2 * (k * (k - kp)) ≤ 2 * (n * n) * D ∧
      2 * (n * n) * (d + 1) + 2 * n * (lo + kp) + 2 * ((k - kp) * (k - kp)) ≤
        2 * (n * n) * (D + 1) ∧
      2 * (n * n) * d + 2 * n * lo + 2 * (k * k) ≤ 2 * (n * n) * (d + 1) + 2 * n * (lo + kp) := by
  obtain ⟨r, rfl⟩ : ∃ r, k = kp + r := ⟨k - kp, by omega⟩
  rw [Nat.add_sub_cancel_left]
  have h1 : r * r ≤ n * r := Nat.mul_le_mul_right _ (by omega)
  have h2 : n * (lo + kp) + n * r ≤ n * n := by
    rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by omega)
  have h3 : n * n * (d + 1) ≤ n * n * D := Nat.mul_le_mul_left _ hd
  have h4 : n * lo + (kp + r) * (kp + r) ≤ n * n := by
    have : (kp + r) * (kp + r) ≤ n * (kp + r) := Nat.mul_le_mul_right _ (by omega)
    have : n * lo + n * (kp + r) ≤ n * n := by
      rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by omega)
    omega
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

-- The kernel call and the four writes unfold large index expressions of the run.
set_option maxHeartbeats 1000000 in
/-- The second compression and the records of a split succeed. -/
private theorem exists_exec_eighSplitTail₂ {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    {u : P → ℝ} {dec : P → K → ℝ} (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P)
    (n d lo k kp : ℕ) (hk : lo + k ≤ n) (hkpk : kp < k) (kpe : IExp ℕ) (hkpe : kpe.eval = kp) (H :
        EighArenas)
    {two nsg : Cell ℕ ℕ} {z2 σ' : K} {st : St P K C} {A : Matrix (Fin k) (Fin k) (K × K)}
    {Qm : Matrix (Fin k) (Fin (k - kp)) (K × K)}
    {D : ℕ} (hd : d < D) (hH : H.Shaped st.store p n D) (Qh C1 C2 C3 : ℕ)
    (hnd : [H.Qa, H.Ma, Qh, C1, C2, C3].Nodup)
    (hscr : ∀ X ∈ [Qh, C1, C2, C3], st.store.shape[X]? = some (p, 2 * (n * n)))
    (hA : pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hQm : pairLayout.Holds st.store p H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (k * kp)) Qm)
    (htwo : st.store.read p two.buf two.idx.eval = some z2) (htwo0 : dec p z2 ≠ 0)
    (hnσ : st.store.read p nsg.buf nsg.idx.eval = some σ')
    (hcells : ∀ c ∈ [two, nsg], c.buf ∉ [H.Ma, Qh, C1, C2, C3]) :
    ∃ st', exec I (do
      eighCompressBlock p mm (.const k) (.const k - kpe) H.Qa
        (eighBlockOff (.const n) (.const d) (.const lo) + 2 * (.const k * kpe)) H.Ma
        (eighBlockOff (.const n) (.const d) (.const lo))
        (eighBlockOff (.const n) (.const d + 1) (.const lo + kpe)) two nsg Qh C1 C2 C3
      ins (.litIdx p ⟨H.Sz, eighSlotOff (.const n) (.const d + 1) (.const lo)⟩ kpe)
      ins (.litIdx p ⟨H.Sz, eighSlotOff (.const n) (.const d + 1) (.const lo + kpe)⟩
        (.const k - kpe))
      ins (.litIdx p ⟨H.Kd, eighSlotOff (.const n) (.const d) (.const lo)⟩ 4)
      ins (.litIdx p ⟨H.Kp, eighSlotOff (.const n) (.const d) (.const lo)⟩ kpe) :
        Builder P ι ℕ ℕ Unit).run st = some st' := by
  subst hkpe
  obtain ⟨-, hMa, -, -, -, hSz, hKd, hKp, -⟩ := id hH
  have hr : ∀ (i : Instr P ℕ ℕ) (b : Builder P ι ℕ ℕ Unit),
      (ins i >>= fun _ => b).run = .seq (.instr i) b.run := fun _ _ => rfl
  have hkn : k ≤ n := by omega
  have hcM : ∀ c ∈ [two, nsg], c.buf ≠ H.Ma := fun c hc h => hcells c hc (by simp [h])
  have hcS : ∀ c ∈ [two, nsg], c.buf ∉ [Qh, C1, C2, C3] := fun c hc h =>
    hcells c hc (List.mem_cons_of_mem _ h)
  have hco2 : blockDisjoint
      (H.Ma, (eighBlockOff (.const n) (.const d + 1) (.const lo + kpe)).eval,
        2 * ((k - (kpe.eval)) * (k - (kpe.eval))))
      (H.Ma, (eighBlockOff (.const n) (.const d) (.const lo)).eval, 2 * (k * k)) = true := by
    simp only [blockDisjoint, eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const,
      IExp.eval_ofNat, bne_self_eq_false, Bool.false_or, Bool.or_eq_true]
    exact Or.inr (decide_eq_true (eighSplit_bounds_split hk hkpk hd).2.2.2)
  rw [exec_eighCompressBlock_bind_split, exec_eighCompressBlock_congr_split]
  simp only [IExp.eval_sub, IExp.eval_const]
  have hcolen2 : (eighBlockOff (.const n) (.const d + 1) (.const lo + kpe)).eval +
      2 * ((k - (kpe.eval)) * (k - (kpe.eval))) ≤ 2 * (n * n) * (D + 1) := by
    simp only [eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat]
    exact (eighSplit_bounds_split hk hkpk hd).2.2.1
  have hqo : pairLayout.Holds st.store p H.Qa
      (eighBlockOff (.const n) (.const d) (.const lo) + 2 * (IExp.const k * kpe)).eval
      Qm := by
    simp only [eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat]
    exact hQm
  have hmo : pairLayout.Holds st.store p H.Ma
      (eighBlockOff (.const n) (.const d) (.const lo)).eval A := by
    simp only [eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat]
    exact hA
  obtain ⟨st6, h6⟩ := exists_exec_eighCompressBlock hmm hsem p n k (k - (kpe.eval)) hkn
      (Nat.sub_le _ _)
    (Qh := Qh) (C1 := C1) (C2 := C2) (C3 := C3)
    (qo := eighBlockOff (.const n) (.const d) (.const lo) + 2 * (IExp.const k * kpe))
    (mo := eighBlockOff (.const n) (.const d) (.const lo))
    (co := eighBlockOff (.const n) (.const d + 1) (.const lo + kpe)) (Q := Qm)
    (A := A) (c₂ := z2) (σ := σ') (two := two) (sg := nsg) hqo hmo htwo htwo0 hnσ hnd
    ⟨hcS two (by simp), hcS nsg (by simp)⟩ hco2 ⟨_, hMa, hcolen2⟩
    (fun X hX => ⟨_, hscr X hX, le_rfl⟩)
  obtain ⟨-, -, hsh6, -⟩ := holds_of_exec_eighCompressBlock (toNat := fun _ => 0)
    (qrR := @fun _ _ X => (Matrix.of fun _ _ => default, X)) (unif := fun x (_ : Unit) => x)
    (normal := fun (_ : Unit) => ((default : K), (default : K))) hmm p k (k - (kpe.eval))
    (qo := eighBlockOff (.const n) (.const d) (.const lo) + 2 * (IExp.const k * kpe))
    (mo := eighBlockOff (.const n) (.const d) (.const lo))
    (co := eighBlockOff (.const n) (.const d + 1) (.const lo + kpe)) (st' := st6) hqo hmo
    htwo hnσ hnd ⟨hcS two (by simp), hcS nsg (by simp)⟩ hco2
    ⟨by simp [blockDisjoint, Ne.symm (hcM two (by simp))],
      by simp [blockDisjoint, Ne.symm (hcM nsg (by simp))]⟩ (by exact h6)
  rw [h6, Option.bind_some]
  have hlt1 : n * (d + 1) + n ≤ n * (D + 1) := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
  obtain ⟨v1, hv1⟩ := hsem.lit_ok p ((kpe).eval : ℚ) trivial
  obtain ⟨s7, hs7⟩ := Store.exists_write_eq_some_of_getElem?_shape v1 (by rw [hsh6]; exact hSz)
    (show (eighSlotOff (.const n) (.const d + 1) (.const lo)).eval < _ by
      simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat]
      omega)
  rw [hr, exec_seq_instr_litIdx I hv1 hs7]
  have hsh7 := (Store.shape_of_write_eq_some hs7).trans hsh6
  obtain ⟨v2, hv2⟩ := hsem.lit_ok p ((IExp.const k - kpe).eval : ℚ) trivial
  obtain ⟨s8, hs8⟩ := Store.exists_write_eq_some_of_getElem?_shape v2 (by rw [hsh7]; exact hSz)
    (show (eighSlotOff (.const n) (.const d + 1) (.const lo + kpe)).eval < _ by
      simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat]
      omega)
  rw [hr, exec_seq_instr_litIdx I hv2 hs8]
  have hsh8 := (Store.shape_of_write_eq_some hs8).trans hsh7
  have hlt2 : n * d + n ≤ n * D := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
  obtain ⟨v3, hv3⟩ := hsem.lit_ok p (((4 : IExp ℕ)).eval : ℚ) trivial
  obtain ⟨s9, hs9⟩ := Store.exists_write_eq_some_of_getElem?_shape v3 (by rw [hsh8]; exact hKd)
    (show (eighSlotOff (.const n) (.const d) (.const lo)).eval < _ by
      simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const]
      omega)
  rw [hr, exec_seq_instr_litIdx I hv3 hs9]
  have hsh9 := (Store.shape_of_write_eq_some hs9).trans hsh8
  obtain ⟨v4, hv4⟩ := hsem.lit_ok p ((kpe).eval : ℚ) trivial
  obtain ⟨s10, hs10⟩ := Store.exists_write_eq_some_of_getElem?_shape v4 (by rw [hsh9]; exact hKp)
    (show (eighSlotOff (.const n) (.const d) (.const lo)).eval < _ by
      simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const]
      omega)
  exact ⟨_, (exec_seq_instr_litIdx I hv4 hs10).trans (exec_skip I _)⟩


/-- The compressions and the records of a split succeed. -/
private theorem exists_exec_eighSplitTail {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    {u : P → ℝ} {dec : P → K → ℝ} (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P)
    (n d lo k kp : ℕ) (hk : lo + k ≤ n) (hkpk : kp < k) (kpe : IExp ℕ) (hkpe : kpe.eval = kp) (H :
        EighArenas)
    {two sg nsg : Cell ℕ ℕ} {z2 σ σ' : K} {st : St P K C} {A : Matrix (Fin k) (Fin k) (K × K)}
    {Qp : Matrix (Fin k) (Fin kp) (K × K)} {Qm : Matrix (Fin k) (Fin (k - kp)) (K × K)}
    {D : ℕ} (hd : d < D) (hH : H.Shaped st.store p n D) (Qh C1 C2 C3 : ℕ)
    (hnd : [H.Qa, H.Ma, Qh, C1, C2, C3].Nodup)
    (hscr : ∀ X ∈ [Qh, C1, C2, C3], st.store.shape[X]? = some (p, 2 * (n * n)))
    (hA : pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hQp : pairLayout.Holds st.store p H.Qa (2 * (n * n) * d + 2 * n * lo) Qp)
    (hQm : pairLayout.Holds st.store p H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (k * kp)) Qm)
    (htwo : st.store.read p two.buf two.idx.eval = some z2) (htwo0 : dec p z2 ≠ 0)
    (hσ : st.store.read p sg.buf sg.idx.eval = some σ)
    (hnσ : st.store.read p nsg.buf nsg.idx.eval = some σ')
    (hcells : ∀ c ∈ [two, sg, nsg], c.buf ∉ [H.Ma, Qh, C1, C2, C3]) :
    ∃ st', exec I (do
      eighCompressBlock p mm (.const k) kpe H.Qa
        (eighBlockOff (.const n) (.const d) (.const lo)) H.Ma
        (eighBlockOff (.const n) (.const d) (.const lo))
        (eighBlockOff (.const n) (.const d + 1) (.const lo)) two sg Qh C1 C2 C3
      eighCompressBlock p mm (.const k) (.const k - kpe) H.Qa
        (eighBlockOff (.const n) (.const d) (.const lo) + 2 * (.const k * kpe)) H.Ma
        (eighBlockOff (.const n) (.const d) (.const lo))
        (eighBlockOff (.const n) (.const d + 1) (.const lo + kpe)) two nsg Qh C1 C2 C3
      ins (.litIdx p ⟨H.Sz, eighSlotOff (.const n) (.const d + 1) (.const lo)⟩ kpe)
      ins (.litIdx p ⟨H.Sz, eighSlotOff (.const n) (.const d + 1) (.const lo + kpe)⟩
        (.const k - kpe))
      ins (.litIdx p ⟨H.Kd, eighSlotOff (.const n) (.const d) (.const lo)⟩ 4)
      ins (.litIdx p ⟨H.Kp, eighSlotOff (.const n) (.const d) (.const lo)⟩ kpe) :
        Builder P ι ℕ ℕ Unit).run st = some st' := by
  subst hkpe
  obtain ⟨-, hMa, -, -, -, hSz, hKd, hKp, -⟩ := id hH
  have hr : ∀ (i : Instr P ℕ ℕ) (b : Builder P ι ℕ ℕ Unit),
      (ins i >>= fun _ => b).run = .seq (.instr i) b.run := fun _ _ => rfl
  have hkn : k ≤ n := by omega
  have hkk : k * k ≤ n * n := Nat.mul_le_mul hkn hkn
  have hlok : n * lo + k * k ≤ n * n := by nlinarith
  have hdD : n * n * (d + 1) ≤ n * n * D := Nat.mul_le_mul_left _ hd
  -- the first compression
  rw [exec_eighCompressBlock_bind_split, exec_eighCompressBlock_congr_split]
  obtain ⟨st5, h5⟩ := exists_exec_eighCompressBlock hmm hsem p n k (kpe.eval) hkn hkpk.le (Qh := Qh)
    (C1 := C1) (C2 := C2) (C3 := C3) (qo := eighBlockOff (.const n) (.const d) (.const lo))
    (mo := eighBlockOff (.const n) (.const d) (.const lo))
    (co := eighBlockOff (.const n) (.const d + 1) (.const lo)) hQp hA htwo htwo0 hσ hnd
    ⟨fun h => hcells two (by simp) (List.mem_cons_of_mem _ h),
      fun h => hcells sg (by simp) (List.mem_cons_of_mem _ h)⟩
    (by
      simp only [blockDisjoint, eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const,
        IExp.eval_ofNat, bne_self_eq_false, Bool.false_or, Bool.or_eq_true]
      right
      exact decide_eq_true (by nlinarith))
    ⟨_, hMa, by simp only [eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const,
      IExp.eval_ofNat]; nlinarith⟩
    (fun X hX => ⟨_, hscr X hX, le_rfl⟩)
  have hQs : H.Qa ∉ [Qh, C1, C2, C3] := fun h => (List.nodup_cons.mp hnd).1
    (List.mem_cons_of_mem _ h)
  have hMs : H.Ma ∉ [Qh, C1, C2, C3] := (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1
  have hQaMa : H.Qa ≠ H.Ma := fun h => (List.nodup_cons.mp hnd).1 (by simp [h])
  have hcM : ∀ c ∈ [two, sg, nsg], c.buf ≠ H.Ma := fun c hc h => hcells c hc (by simp [h])
  have hcS : ∀ c ∈ [two, sg, nsg], c.buf ∉ [Qh, C1, C2, C3] := fun c hc h =>
    hcells c hc (List.mem_cons_of_mem _ h)
  obtain ⟨-, hfr5, hsh5, -⟩ := holds_of_exec_eighCompressBlock (toNat := fun _ => 0)
    (qrR := @fun _ _ X => (Matrix.of fun _ _ => default, X)) (unif := fun x (_ : Unit) => x)
    (normal := fun (_ : Unit) => ((default : K), (default : K))) hmm p k (kpe.eval)
    (qo := eighBlockOff (.const n) (.const d) (.const lo))
    (mo := eighBlockOff (.const n) (.const d) (.const lo))
    (co := eighBlockOff (.const n) (.const d + 1) (.const lo)) (st' := st5) hQp hA htwo hσ hnd
    ⟨hcS two (by simp), hcS sg (by simp)⟩
    (by
      simp only [blockDisjoint, eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const,
        IExp.eval_ofNat, bne_self_eq_false, Bool.false_or, Bool.or_eq_true]
      right
      exact decide_eq_true (by nlinarith)) ⟨by simp [blockDisjoint, Ne.symm (hcM two (by simp))],
      by simp [blockDisjoint, Ne.symm (hcM sg (by simp))]⟩ (by exact h5)
  have hcell5 : ∀ c ∈ [two, sg, nsg],
      st5.store.read p c.buf c.idx.eval = st.store.read p c.buf c.idx.eval := fun c hc =>
    hfr5 p _ _ (hcS c hc) (by simp [blockDisjoint, hcM c hc])
  have hQm5 : pairLayout.Holds st5.store p H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (k *
      (kpe.eval))) Qm :=
    fun i j t => (hfr5 p _ _ hQs (by simp [blockDisjoint, hQaMa])).trans (hQm i j t)
  have hA5 : pairLayout.Holds st5.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A :=
    fun i j t => (hfr5 p _ _ hMs (by
      have := pair_idx_lt_split i j t
      simp only [blockDisjoint, eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const,
        IExp.eval_ofNat, bne_self_eq_false, Bool.false_or, Bool.or_eq_true]
      left
      exact decide_eq_true (by change _ + (2 * _ + _) + 1 ≤ _; nlinarith))).trans (hA i j t)
  rw [h5, Option.bind_some]
  exact exists_exec_eighSplitTail₂ hmm hsem p n d lo k (kpe.eval) hk hkpk kpe rfl H hd
    (by unfold EighArenas.Shaped; rw [hsh5]; exact hH) Qh C1 C2 C3 hnd
    (fun X hX => by rw [hsh5]; exact hscr X hX) hA5 hQm5 ((hcell5 two (by simp)).trans htwo)
    htwo0 ((hcell5 nsg (by simp)).trans hnσ)
    (fun c hc => hcells c (by simp only [List.mem_cons] at hc ⊢; tauto))

/-- A handle outside five handles is outside the first four and is not the fifth. -/
private theorem not_mem_four_of_not_mem_five_split {x a b c e g : ℕ} (h : x ∉ [a, b, c, e, g]) :
    x ∉ [a, b, c, e] ∧ x ≠ g := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h ⊢
  exact ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩, h.2.2.2.2⟩

/-- The deflations, compressions and records of a split succeed. -/
private theorem exists_exec_eighSplitMid {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P)
    (n d lo k kp : ℕ) (hk : lo + k ≤ n) (hkpk : kp < k) (kpe : IExp ℕ) (hkpe : kpe.eval = kp)
    (H : EighArenas) {Sg Pp Pm : ℕ} {two sg nsg sq : Cell ℕ ℕ} {z2 σ σ' : K} {st : St P K C}
    {A : Matrix (Fin k) (Fin k) (K × K)} {Ppm Pmm : Matrix (Fin k) (Fin k) (K × K)}
    {D : ℕ} (hd : d < D) (hH : H.Shaped st.store p n D)
    (G Y Qf Rf Qh C1 C2 C3 : ℕ)
    (hb1 : [Sg, Pp, G, Y, Qf, Rf, H.Qa].Nodup) (hb2 : [Sg, Pm, G, Y, Qf, Rf, H.Qa].Nodup)
    (hb3 : [H.Qa, H.Ma, Qh, C1, C2, C3].Nodup) (hMaS : H.Ma ∉ [G, Y, Qf, Rf])
    (hnew : ∀ X ∈ [G, Y, Qf, Rf, Qh, C1, C2, C3], st.store.shape[X]? = some (p, 2 * (n * n)))
    (hA : pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hPp : pairLayout.Holds st.store p Pp 0 Ppm) (hPm : pairLayout.Holds st.store p Pm 0 Pmm)
    (hSg : ∀ w < 4 * (n * n), ∃ v, st.store.read p Sg w = some v)
    (hsq : st.store.read p sq.buf sq.idx.eval = some (I.sem.sqrtHalf p))
    (htwo : st.store.read p two.buf two.idx.eval = some z2) (htwo0 : dec p z2 ≠ 0)
    (hσ : st.store.read p sg.buf sg.idx.eval = some σ)
    (hnσ : st.store.read p nsg.buf nsg.idx.eval = some σ')
    (hc' : ∀ c ∈ [two, sg, nsg, sq], c.buf ≠ H.Ma ∧ c.buf ≠ H.Qa ∧ c.buf ∉ [G, Y, Qf, Rf] ∧
      c.buf ∉ [Qh, C1, C2, C3]) :
    ∃ st', exec I (do
      eighDeflateBlock p mm qr (.const n) (.const k) kpe (.const lo) 0 Sg sq Pp G Y Qf Rf
        H.Qa (eighBlockOff (.const n) (.const d) (.const lo))
      eighDeflateBlock p mm qr (.const n) (.const k) (.const k - kpe) (.const lo) 1 Sg sq Pm
        G Y Qf Rf H.Qa (eighBlockOff (.const n) (.const d) (.const lo) +
          2 * (.const k * kpe))
      eighCompressBlock p mm (.const k) kpe H.Qa
        (eighBlockOff (.const n) (.const d) (.const lo)) H.Ma
        (eighBlockOff (.const n) (.const d) (.const lo))
        (eighBlockOff (.const n) (.const d + 1) (.const lo)) two sg Qh C1 C2 C3
      eighCompressBlock p mm (.const k) (.const k - kpe) H.Qa
        (eighBlockOff (.const n) (.const d) (.const lo) + 2 * (.const k * kpe)) H.Ma
        (eighBlockOff (.const n) (.const d) (.const lo))
        (eighBlockOff (.const n) (.const d + 1) (.const lo + kpe)) two nsg Qh C1 C2 C3
      ins (.litIdx p ⟨H.Sz, eighSlotOff (.const n) (.const d + 1) (.const lo)⟩ kpe)
      ins (.litIdx p ⟨H.Sz, eighSlotOff (.const n) (.const d + 1) (.const lo + kpe)⟩
        (.const k - kpe))
      ins (.litIdx p ⟨H.Kd, eighSlotOff (.const n) (.const d) (.const lo)⟩ 4)
      ins (.litIdx p ⟨H.Kp, eighSlotOff (.const n) (.const d) (.const lo)⟩ kpe) :
        Builder P ι ℕ ℕ Unit).run st = some st' := by
  subst hkpe
  obtain ⟨-, hMa, -, hQa, -, -, -, -, -⟩ := id hH
  have hsqb : sq.buf ∉ [G, Y, Qf, Rf, H.Qa] := fun h =>
    (List.mem_append (s := [G, Y, Qf, Rf]) (t := [H.Qa])).mp h |>.elim (hc' sq (by simp)).2.2.1
      fun h' => (hc' sq (by simp)).2.1 (List.mem_singleton.mp h')
  have hMaQ : H.Ma ≠ H.Qa := fun h => (List.nodup_cons.mp hb3).1 (by simp [h])
  have hlen1 : (eighBlockOff (IExp.const n) (IExp.const d) (IExp.const lo)).eval + 2 * (k *
      (kpe.eval)) ≤
      2 * (n * n) * D := by
    simp only [eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat]
    exact (eighSplit_bounds_split hk hkpk hd).1
  have hlen2 : (eighBlockOff (IExp.const n) (IExp.const d) (IExp.const lo) +
      2 * (IExp.const k * kpe)).eval + 2 * (k * (k - (kpe.eval))) ≤ 2 * (n * n) * D := by
    simp only [eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat]
    exact (eighSplit_bounds_split hk hkpk hd).2.1
  -- the first deflation
  rw [exec_eighDeflateBlock_bind_split]
  obtain ⟨st3, h3, ⟨Qp3, hQp3⟩, hfr3, hsh3⟩ := exists_exec_eighDeflateBlock_facts hmm hqr hsem p
    n k (kpe.eval) d lo hk hkpk.le true
    (qo := eighBlockOff (IExp.const n) (IExp.const d) (IExp.const lo)) hPp hsq hSg hb1 hsqb
    (fun X hX => ⟨_, hnew X (List.mem_append_left [Qh, C1, C2, C3] hX), le_rfl⟩)
    ⟨_, hQa, hlen1⟩
  have h3' : exec I (eighDeflateBlock p mm qr (.const n) (.const k) kpe (.const lo) 0 Sg sq
      Pp G Y Qf Rf H.Qa (eighBlockOff (.const n) (.const d) (.const lo))).run st = some st3 := h3
  have hk3 : ∀ q b' i, b' ∉ [G, Y, Qf, Rf] → b' ≠ H.Qa →
      st3.store.read q b' i = st.store.read q b' i := fun q b' i h1 h2 =>
    hfr3 q b' i h1 (by simp [blockDisjoint, h2])
  obtain ⟨hPmS, hPmQ⟩ := not_mem_four_of_not_mem_five_split
    (List.nodup_cons.mp (List.nodup_cons.mp hb2).2).1
  obtain ⟨hSgS, hSgQ⟩ := not_mem_four_of_not_mem_five_split
    (fun h => (List.nodup_cons.mp hb1).1 (List.mem_cons_of_mem _ h))
  have hsq3 := (hk3 _ _ _ (hc' sq (by simp)).2.2.1 (hc' sq (by simp)).2.1).trans hsq
  have hPm3 : pairLayout.Holds st3.store p Pm 0 Pmm := fun i j t =>
    (hk3 _ _ _ hPmS hPmQ).trans (hPm i j t)
  have hSg3 : ∀ w < 4 * (n * n), ∃ v, st3.store.read p Sg w = some v := fun w hw =>
    (hSg w hw).imp fun _ hv => (hk3 _ _ _ hSgS hSgQ).trans hv
  rw [h3', Option.bind_some, exec_eighDeflateBlock_bind_split, exec_eighDeflateBlock_congr_split]
  simp only [IExp.eval_sub, IExp.eval_const]
  -- the second deflation
  obtain ⟨st4, h4, ⟨Qm4, hQm4⟩, hfr4, hsh4⟩ := exists_exec_eighDeflateBlock_facts hmm hqr hsem p
    n k (k - (kpe.eval)) d lo hk
    (Nat.sub_le _ _) false (qo := eighBlockOff (IExp.const n) (IExp.const d) (IExp.const lo) +
      2 * (IExp.const k * kpe)) hPm3 hsq3 hSg3 hb2 hsqb
    (fun X hX => ⟨_, by rw [hsh3]; exact hnew X (List.mem_append_left [Qh, C1, C2, C3] hX),
      le_rfl⟩)
    ⟨_, by rw [hsh3]; exact hQa, hlen2⟩
  have h4' : exec I (eighDeflateBlock p mm qr (.const n) (.const k) (.const (k - (kpe.eval)))
      (.const lo) 1
      Sg sq Pm G Y Qf Rf H.Qa (eighBlockOff (.const n) (.const d) (.const lo) +
        2 * (.const k * kpe))).run st3 = some st4 := h4
  have hk4 : ∀ q b' i, b' ∉ [G, Y, Qf, Rf] → b' ≠ H.Qa →
      st4.store.read q b' i = st.store.read q b' i := fun q b' i h1 h2 =>
    (hfr4 q b' i h1 (by simp [blockDisjoint, h2])).trans (hk3 q b' i h1 h2)
  have hQaS : H.Qa ∉ [G, Y, Qf, Rf] := fun h =>
    (List.nodup_append.mp (show ([G, Y, Qf, Rf] ++ [H.Qa]).Nodup from
      (List.nodup_cons.mp (List.nodup_cons.mp hb1).2).2)).2.2 _ h _ (List.mem_singleton_self _) rfl
  rw [h4', Option.bind_some]
  exact exists_exec_eighSplitTail hmm hsem p n d lo k (kpe.eval) hk hkpk kpe rfl H hd
    (by unfold EighArenas.Shaped; rw [hsh4, hsh3]; exact hH) Qh C1 C2 C3 hb3
    (fun X hX => by rw [hsh4, hsh3]; exact hnew X (List.mem_append_right [G, Y, Qf, Rf] hX))
    (fun i j t => (hk4 _ _ _ hMaS hMaQ).trans (hA i j t))
    (fun i j t => (hfr4 _ _ _ hQaS (by
      have := pair_idx_lt_split i j t
      simp only [blockDisjoint, eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const,
        IExp.eval_ofNat, bne_self_eq_false, Bool.false_or, Bool.or_eq_true]
      left
      exact decide_eq_true (by change _ + (2 * _ + _) + 1 ≤ _; nlinarith))).trans (by
        simpa only [eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const,
          IExp.eval_ofNat] using hQp3 i j t))
    (fun i j t => by simpa only [eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const,
      IExp.eval_ofNat] using hQm4 i j t)
    ((hk4 _ _ _ (hc' two (by simp)).2.2.1 (hc' two (by simp)).2.1).trans htwo) htwo0
    ((hk4 _ _ _ (hc' sg (by simp)).2.2.1 (hc' sg (by simp)).2.1).trans hσ)
    ((hk4 _ _ _ (hc' nsg (by simp)).2.2.1 (hc' nsg (by simp)).2.1).trans hnσ)
    (fun c hc h => by
      have := hc' c (by simp only [List.mem_cons] at hc ⊢; tauto)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h this
      tauto)

/-- The body of a split after its eight allocations succeeds. -/
private theorem exists_exec_eighSplitBody {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hlit : IsExactIntLit dec I.sem 2) (p : P)
    (n d lo k kp : ℕ) (hk : lo + k ≤ n) (hkpk : kp < k) (kpe : IExp ℕ) (hkpe :
        kpe.eval = kp)
    (H : EighArenas) {Sg Pp Pm : ℕ} {two sg nsg sq : Cell ℕ ℕ} {σ : K} {st : St P K C}
    {A : Matrix (Fin k) (Fin k) (K × K)} {Ppm Pmm : Matrix (Fin k) (Fin k) (K × K)}
    {D : ℕ} (hd : d < D) (hH : H.Shaped st.store p n D)
    (G Y Qf Rf Qh C1 C2 C3 : ℕ)
    (hb1 : [Sg, Pp, G, Y, Qf, Rf, H.Qa].Nodup) (hb2 : [Sg, Pm, G, Y, Qf, Rf, H.Qa].Nodup)
    (hb3 : [H.Qa, H.Ma, Qh, C1, C2, C3].Nodup) (hMaS : H.Ma ∉ [G, Y, Qf, Rf])
    (hnew : ∀ X ∈ [G, Y, Qf, Rf, Qh, C1, C2, C3], st.store.shape[X]? = some (p, 2 * (n * n)))
    (hA : pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hPp : pairLayout.Holds st.store p Pp 0 Ppm) (hPm : pairLayout.Holds st.store p Pm 0 Pmm)
    (hSg : ∀ w < 4 * (n * n), ∃ v, st.store.read p Sg w = some v)
    (htwo : st.store.read p two.buf two.idx.eval = I.sem.lit p ((2 : ℕ) : ℚ))
    (hσ : st.store.read p sg.buf sg.idx.eval = some σ)
    (hnσ : st.store.read p nsg.buf nsg.idx.eval = some ((eighTapeMachine I p mmR qrR).neg σ))
    (hc' : ∀ c ∈ [two, sg, nsg, sq], c.buf ≠ H.Ma ∧ c.buf ≠ H.Qa ∧ c.buf ∉ [G, Y, Qf, Rf] ∧
      c.buf ∉ [Qh, C1, C2, C3])
    (hsq : st.store.read p sq.buf sq.idx.eval = some (I.sem.sqrtHalf p)) :
    ∃ st', exec I (do
      eighDeflateBlock p mm qr (.const n) (.const k) kpe (.const lo) 0 Sg sq Pp G Y Qf Rf
        H.Qa (eighBlockOff (.const n) (.const d) (.const lo))
      eighDeflateBlock p mm qr (.const n) (.const k) (.const k - kpe) (.const lo) 1 Sg sq Pm
        G Y Qf Rf H.Qa (eighBlockOff (.const n) (.const d) (.const lo) +
          2 * (.const k * kpe))
      eighCompressBlock p mm (.const k) kpe H.Qa
        (eighBlockOff (.const n) (.const d) (.const lo)) H.Ma
        (eighBlockOff (.const n) (.const d) (.const lo))
        (eighBlockOff (.const n) (.const d + 1) (.const lo)) two sg Qh C1 C2 C3
      eighCompressBlock p mm (.const k) (.const k - kpe) H.Qa
        (eighBlockOff (.const n) (.const d) (.const lo) + 2 * (.const k * kpe)) H.Ma
        (eighBlockOff (.const n) (.const d) (.const lo))
        (eighBlockOff (.const n) (.const d + 1) (.const lo + kpe)) two nsg Qh C1 C2 C3
      ins (.litIdx p ⟨H.Sz, eighSlotOff (.const n) (.const d + 1) (.const lo)⟩ kpe)
      ins (.litIdx p ⟨H.Sz, eighSlotOff (.const n) (.const d + 1) (.const lo + kpe)⟩
        (.const k - kpe))
      ins (.litIdx p ⟨H.Kd, eighSlotOff (.const n) (.const d) (.const lo)⟩ 4)
      ins (.litIdx p ⟨H.Kp, eighSlotOff (.const n) (.const d) (.const lo)⟩ kpe) :
        Builder P ι ℕ ℕ Unit).run st = some st' := by
  obtain ⟨z2, hz2, hdz2⟩ := hlit p 2 le_rfl
  exact exists_exec_eighSplitMid hmm hqr hsem p n d lo k kp hk hkpk kpe hkpe H hd hH G Y Qf Rf Qh
    C1 C2 C3 hb1 hb2 hb3 hMaS hnew hA hPp hPm hSg hsq (htwo.trans hz2)
    (by rw [hdz2]; norm_num) hσ hnσ hc'

/-- A split succeeds, with the Gaussian words only initialised. -/
private theorem exists_exec_eighSplitBlock_ex {mm qr : ι}
    (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hlit : IsExactIntLit dec I.sem 2) (p : P)
    (hu : u p < 1) (n d lo k kp : ℕ) (hk : lo + k ≤ n) (hkp : 0 < kp) (hkpk : kp < k) (kpe : IExp
        ℕ) (hkpe : kpe.eval = kp)
    (H : EighArenas) {Sg Pp Pm : ℕ} {two sg nsg sq : Cell ℕ ℕ} {σ : K} {st : St P K C}
    {A : Matrix (Fin k) (Fin k) (K × K)} {Ppm Pmm : Matrix (Fin k) (Fin k) (K × K)}
    {D : ℕ} (hd : d < D) (hH : H.Shaped st.store p n D) (hbufs : (H.handles ++ [Sg, Pp, Pm]).Nodup)
    (hA : pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hPp : pairLayout.Holds st.store p Pp 0 Ppm) (hPm : pairLayout.Holds st.store p Pm 0 Pmm)
    (hSg : ∀ w < 4 * (n * n), ∃ v, st.store.read p Sg w = some v)
    (htwo : st.store.read p two.buf two.idx.eval = I.sem.lit p ((2 : ℕ) : ℚ))
    (hσ : st.store.read p sg.buf sg.idx.eval = some σ)
    (hnσ : st.store.read p nsg.buf nsg.idx.eval = some ((eighTapeMachine I p mmR qrR).neg σ))
    (hcells : ∀ c ∈ [two, sg, nsg, sq], c.buf ∉ H.handles ++ [Sg, Pp, Pm])
    (hsq : st.store.read p sq.buf sq.idx.eval = some (I.sem.sqrtHalf p)) :
    ∃ st', exec I (eighSplitBlock p mm qr (.const n) (.const d) (.const lo) (.const k) kpe
      Sg Pp Pm H.Ma H.Qa H.Sz H.Kd H.Kp two sg nsg sq).run st = some st' := by
  subst hkpe
  have hsz : ∀ {b : ℕ} {x : P × ℕ}, st.store.shape[b]? = some x → b < st.store.size :=
    fun h => by simpa [Store.size_shape] using (Array.getElem?_eq_some_iff.mp h).1
  have hk0 : 0 < k := by omega
  have hn2 : 0 < 4 * (n * n) := by have : 0 < n := (by omega); positivity
  obtain ⟨-, hMa, hUa, hQa, hEa, hSz, hKd, hKp, hLv⟩ := id hH
  have lMa := hsz hMa; have lUa := hsz hUa; have lQa := hsz hQa; have lEa := hsz hEa
  have lSz := hsz hSz; have lKd := hsz hKd; have lKp := hsz hKp; have lLv := hsz hLv
  have lSg := Store.lt_size_of_read_eq_some (hSg 0 hn2).choose_spec
  have lPp := Store.lt_size_of_read_eq_some (hPp ⟨0, hk0⟩ ⟨0, hk0⟩ ⟨0, two_pos⟩)
  have lPm := Store.lt_size_of_read_eq_some (hPm ⟨0, hk0⟩ ⟨0, hk0⟩ ⟨0, two_pos⟩)
  obtain ⟨z2, hz2, -⟩ := hlit p 2 le_rfl
  have ltwo := Store.lt_size_of_read_eq_some (htwo.trans hz2)
  have lsg := Store.lt_size_of_read_eq_some hσ
  have lnsg := Store.lt_size_of_read_eq_some hnσ
  have lsq := Store.lt_size_of_read_eq_some hsq
  have hall : ∀ a ∈ H.handles ++ [Sg, Pp, Pm], a < st.store.size := by
    simp only [EighArenas.handles, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro a (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> assumption
  change ∃ st', exec I (.seq _ .skip) st = some st'
  rw [exec_seq_skip]
  refine exists_exec_alloc_of_exists_split ?_
  refine exists_exec_alloc_of_exists_split ?_
  refine exists_exec_alloc_of_exists_split ?_
  refine exists_exec_alloc_of_exists_split ?_
  refine exists_exec_alloc_of_exists_split ?_
  refine exists_exec_alloc_of_exists_split ?_
  refine exists_exec_alloc_of_exists_split ?_
  refine exists_exec_alloc_of_exists_split ?_
  beta_reduce
  have nSgPp : Sg ≠ Pp := fun h => by simp [EighArenas.handles, h] at hbufs
  have nSgPm : Sg ≠ Pm := fun h => by simp [EighArenas.handles, h] at hbufs
  have nSgQa : Sg ≠ H.Qa := fun h => by simp [EighArenas.handles, h] at hbufs
  have nPpQa : Pp ≠ H.Qa := fun h => by simp [EighArenas.handles, h] at hbufs
  have nPmQa : Pm ≠ H.Qa := fun h => by simp [EighArenas.handles, h] at hbufs
  have nMaQa : H.Ma ≠ H.Qa := fun h => by simp [EighArenas.handles, h] at hbufs
  refine exists_exec_eighSplitBody hmm hqr hsem hlit p n d lo k (kpe.eval) hk hkpk kpe rfl H hd
    (A := A) (Ppm := Ppm) (Pmm := Pmm) (σ := σ) (hH := ?_) (hb1 := ?_) (hb2 := ?_) (hb3 := ?_)
    (hMaS := ?_) (hnew := ?_) (hA := ?_) (hPp := ?_) (hPm := ?_) (hSg := ?_)
    (htwo := ?_) (hσ := ?_) (hnσ := ?_) (hc' := ?_) (hsq := ?_) _ _ _ _ _ _ _ _
  all_goals try simp (disch := first | omega | (simp only [Array.size_push]; omega)) only
    [EighArenas.Shaped, EntryLayout.Holds, Store.getElem?_shape_push_of_lt,
      Store.read_push_of_lt, Store.write_push_of_lt, Array.size_push]
  · exact ⟨hH.1, hMa, hUa, hQa, hEa, hSz, hKd, hKp, hLv⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true]
    omega
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true]
    omega
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro X (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      simp [Store.shape, Array.getElem?_push, Array.getElem_push]
  · exact hA
  · exact hPp
  · exact hPm
  · exact hSg
  · exact htwo
  · exact hσ
  · exact hnσ
  · intro c hc
    have hlt : c.buf < st.store.size := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl <;> assumption
    have h1 := hcells c (by simp only [List.mem_cons] at hc ⊢; tauto)
    refine ⟨fun h => h1 (by simp [EighArenas.handles, h]),
      fun h => h1 (by simp [EighArenas.handles, h]), ?_, ?_⟩ <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] <;> omega
  · exact hsq

/-- **A split succeeds** under the standard model at $u$ with every value in range and $u(p) < 1$,
with an exact literal $2$, if the kernels are routines on pairs and the arenas are allocated
(hypotheses on the inputs as `NLAlib.holds_of_exec_eighSplitBlock`). No printed source.
(The stored $\sqrt{1/2}$ is read from the cell `sq`, which `NLAlib.eighProg` fills once; design
note §8, the hoist of $\sqrt{1/2}$.)
Proof: the eight allocations succeed; then `NLAlib.exists_exec_eighDeflateBlock` twice, `NLAlib.exists_exec_eighCompressBlock` twice on the
states the value statements describe, and the four literals (`lit_ok`). M, about 70 lines. -/
theorem exists_exec_eighSplitBlock {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hlit : IsExactIntLit dec I.sem 2) (p : P)
    (hu : u p < 1) (n d lo k kp : ℕ) (hk : lo + k ≤ n) (hkp : 0 < kp) (hkpk : kp < k)
    (H : EighArenas) {Sg Pp Pm : ℕ} {two sg nsg sq : Cell ℕ ℕ} {σ : K} {st : St P K C}
    {A : Matrix (Fin k) (Fin k) (K × K)} {Ppm Pmm : Matrix (Fin k) (Fin k) (K × K)}
    {D : ℕ} (hd : d < D) (hH : H.Shaped st.store p n D) (hbufs : (H.handles ++ [Sg, Pp, Pm]).Nodup)
    (hA : pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hPp : pairLayout.Holds st.store p Pp 0 Ppm) (hPm : pairLayout.Holds st.store p Pm 0 Pmm)
    (hSg : ∀ w < 4 * (n * n), st.store.read p Sg w = some (I.tape .gaussian (4 * (n * n) * d + w)))
    (htwo : st.store.read p two.buf two.idx.eval = I.sem.lit p ((2 : ℕ) : ℚ))
    (hσ : st.store.read p sg.buf sg.idx.eval = some σ)
    (hnσ : st.store.read p nsg.buf nsg.idx.eval = some ((eighTapeMachine I p mmR qrR).neg σ))
    (hcells : ∀ c ∈ [two, sg, nsg, sq], c.buf ∉ H.handles ++ [Sg, Pp, Pm])
    (hsq : st.store.read p sq.buf sq.idx.eval = some (I.sem.sqrtHalf p)) :
    ∃ st', exec I (eighSplitBlock p mm qr (.const n) (.const d) (.const lo) (.const k) (.const kp)
      Sg Pp Pm H.Ma H.Qa H.Sz H.Kd H.Kp two sg nsg sq).run st = some st' := by
  exact exists_exec_eighSplitBlock_ex hmm hqr hsem hlit p hu n d lo k kp hk hkp hkpk (.const kp)
      rfl H
    hd hH hbufs
    hA hPp hPm (fun w hw => ⟨_, hSg w hw⟩) htwo hσ hnσ hcells hsq

/-! ### The node step -/
/-- A packed complex entry lies in its block. -/
private theorem pair_idx_lt_node {l m : ℕ} (i : Fin l) (j : Fin m) (t : Fin 2) :
    2 * ((i : ℕ) + l * j) + t < 2 * (l * m) := by
  have := i.2; have := j.2; have := t.2
  have : l * ((j : ℕ) + 1) ≤ l * m := Nat.mul_le_mul_left l j.2
  nlinarith

/-- A cell is disjoint from a block inside a window it avoids. -/
private theorem bd_of_win_node {b i B off len lo' hi' : ℕ} (h : b = B → i < lo' ∨ hi' ≤ i)
    (h1 : lo' ≤ off) (h2 : off + len ≤ hi') : blockDisjoint (b, i, 1) (B, off, len) = true := by
  unfold blockDisjoint
  by_cases hb : b = B
  · rcases h hb with h | h
    · simp only [Bool.or_eq_true, decide_eq_true_eq]; exact Or.inl (Or.inr (by omega))
    · simp only [Bool.or_eq_true, decide_eq_true_eq]; exact Or.inr (by omega)
  · simp [hb]

omit [Inhabited K] in
/-- Name the state of a run. -/
private theorem name_state_node {X : Stmt P ι ℕ ℕ} {s s' : St P K C} (h : exec I X s = some s')
    {Q : Prop} (k : ∀ σ : St P K C, σ.store = s.store → σ.pos = s.pos → exec I X σ = some s' → Q) :
    Q := k s rfl rfl h

/-- Seven handles, three below `s₀` and four from `s₀` on, are distinct. -/
private theorem nodup_def_node {a b c s₀ G Y Qf Rf : ℕ} (hab : a = b → False) (hac : a = c → False)
    (hbc : b = c → False) (ha : a < s₀) (hb : b < s₀) (hc : c < s₀) (h4 : [G, Y, Qf, Rf].Nodup)
    (hG : s₀ ≤ G) (hY : s₀ ≤ Y) (hQ : s₀ ≤ Qf) (hR : s₀ ≤ Rf) : [a, b, G, Y, Qf, Rf, c].Nodup := by
  have : a ≠ b := hab; have : a ≠ c := hac; have : b ≠ c := hbc
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at h4 ⊢
  omega

/-- Six handles, two below `s₀` and four from `s₀` on, are distinct. -/
private theorem nodup_cmp_node {a b s₀ Qh C1 C2 C3 : ℕ} (hab : a = b → False) (ha : a < s₀)
    (hb : b < s₀) (h4 : [Qh, C1, C2, C3].Nodup) (h1 : s₀ ≤ Qh) (h2 : s₀ ≤ C1) (h3 : s₀ ≤ C2)
    (h5 : s₀ ≤ C3) : [a, b, Qh, C1, C2, C3].Nodup := by
  have : a ≠ b := hab
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at h4 ⊢
  omega

/-- A handle below `s₀` is not among four from `s₀` on and another. -/
private theorem notmem5_node {x s₀ G Y Qf Rf c : ℕ} (hx : x < s₀) (hG : s₀ ≤ G) (hY : s₀ ≤ Y)
    (hQ : s₀ ≤ Qf) (hR : s₀ ≤ Rf) (hc : x = c → False) : x ∉ [G, Y, Qf, Rf, c] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨by omega, by omega, by omega, by omega, hc⟩

/-- The index arithmetic of a split inside the window of its node. -/
private theorem split_arith_node {n d lo k kp : ℕ} (hk : lo + k ≤ n) (hkpk : kp < k) :
    2 * (n * n) * d + 2 * n * lo + 2 * (k * k) ≤ 2 * (n * n) * (d + 1) + 2 * n * lo ∧
    2 * (n * n) * (d + 1) + 2 * n * lo + 2 * (kp * kp) ≤
      2 * (n * n) * (d + 1) + 2 * n * (lo + kp) ∧
    2 * (n * n) * (d + 1) + 2 * n * (lo + kp) + 2 * ((k - kp) * (k - kp)) ≤
      2 * (n * n) * (d + 1) + 2 * n * (lo + k) ∧
    2 * (n * n) * d + 2 * n * lo + 2 * (k * kp) ≤ 2 * (n * n) * d + 2 * n * (lo + k) ∧
    2 * (n * n) * d + 2 * n * lo + 2 * (k * kp) + 2 * (k * (k - kp)) ≤
      2 * (n * n) * d + 2 * n * (lo + k) ∧
    2 * (n * n) * (d + 1) + 2 * n * lo ≤ 2 * (n * n) * (d + 1) + 2 * n * (lo + kp) := by
  obtain ⟨r, rfl⟩ : ∃ r, k = kp + r := ⟨k - kp, by omega⟩
  rw [Nat.add_sub_cancel_left]
  have h1 : kp * kp ≤ n * kp := Nat.mul_le_mul_right _ (by omega)
  have h2 : r * r ≤ n * r := Nat.mul_le_mul_right _ (by omega)
  have h3 : (kp + r) * (kp + r) ≤ n * (kp + r) := Nat.mul_le_mul_right _ (by omega)
  have h4 : n * lo + n * (kp + r) ≤ n * n := by rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ hk
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- The cells a node step at the slot $lo$ of depth $d$ for a node of size $k$ may write in the
arenas. -/
private def nodeWin (H : EighArenas) (n d lo k j b i : ℕ) : Prop :=
  (b = H.Qa ∧ 2 * (n * n) * d + 2 * n * lo ≤ i ∧ i < 2 * (n * n) * d + 2 * n * (lo + k)) ∨
    (b = H.Ma ∧ 2 * (n * n) * (d + 1) + 2 * n * lo ≤ i ∧
      i < 2 * (n * n) * (d + 1) + 2 * n * (lo + k)) ∨
    (b = H.Sz ∧ (i = n * (d + 1) + lo ∨ i = n * (d + 1) + j)) ∨
    ((b = H.Kd ∨ b = H.Kp) ∧ i = n * d + lo)

omit [Inhabited K] in
/-- A held block is kept if every read of its words is kept. -/
private theorem holds_keep_node {s s' : Store P K} {p : P} {b off l m : ℕ}
    {Y : Matrix (Fin l) (Fin m) (K × K)} (hY : pairLayout.Holds s p b off Y)
    (h : ∀ i, off ≤ i → i < off + 2 * (l * m) → s'.read p b i = s.read p b i) :
    pairLayout.Holds s' p b off Y :=
  hY.of_forall_read_eq fun i h1 h2 => h i h1 (by
    change i < off + m * l * 2 at h2
    linarith [Nat.mul_comm l m])

-- The split unfolds large index expressions.
set_option maxHeartbeats 4000000 in
/-- The body of a split after its eight allocations: the values of
`NLAlib.holds_of_exec_eighSplitBlock`, and every cell of a buffer below `s₀` outside the cell
`sq` and the node's window is kept. -/
private theorem split_body_holds {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) (p : P) (n d lo k kp : ℕ) (hk : lo + k ≤ n)
    (hkp : 0 < kp) (hkpk : kp < k) (kpe : IExp ℕ) (hkpe : kpe.eval = kp) (H : EighArenas) {Sg Pp Pm : ℕ} {two sg nsg sq : Cell ℕ ℕ}
    {σ : K} {st st' : St P K C} {A : Matrix (Fin k) (Fin k) (K × K)}
    {Ppm Pmm : Matrix (Fin k) (Fin k) (K × K)} {D : ℕ} (hd : d < D) (s₀ : ℕ)
    (hlt : ∀ b ∈ H.handles ++ [Sg, Pp, Pm, two.buf, sg.buf, nsg.buf, sq.buf], b < s₀)
    (G Y Qf Rf Qh C1 C2 C3 : ℕ) (hge : ∀ X ∈ [G, Y, Qf, Rf, Qh, C1, C2, C3], s₀ ≤ X)
    (hnd : [G, Y, Qf, Rf, Qh, C1, C2, C3].Nodup)
    (hbufs : (H.handles ++ [Sg, Pp, Pm]).Nodup)
    (hA : pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hPp : pairLayout.Holds st.store p Pp 0 Ppm) (hPm : pairLayout.Holds st.store p Pm 0 Pmm)
    (hSg : ∀ w < 4 * (n * n), st.store.read p Sg w = some (I.tape .gaussian (4 * (n * n) * d + w)))
    (htwo : st.store.read p two.buf two.idx.eval = some ((eighTapeMachine I p mmR qrR).ofNat 2))
    (hσ : st.store.read p sg.buf sg.idx.eval = some σ)
    (hnσ : st.store.read p nsg.buf nsg.idx.eval =
      some ((eighTapeMachine I p mmR qrR).neg σ))
    (hcells : ∀ c ∈ [two, sg, nsg, sq], c.buf ∉ H.handles ++ [Sg, Pp, Pm])
    (hsq : st.store.read p sq.buf sq.idx.eval = some (I.sem.sqrtHalf p))
    (h : exec I (do
      eighDeflateBlock p mm qr (.const n) (.const k) (kpe) (.const lo) 0 Sg sq Pp G Y Qf Rf
        H.Qa (eighBlockOff (.const n) (.const d) (.const lo))
      eighDeflateBlock p mm qr (.const n) (.const k) (.const k - kpe) (.const lo) 1 Sg sq Pm
        G Y Qf Rf H.Qa (eighBlockOff (.const n) (.const d) (.const lo) +
          2 * (.const k * kpe))
      eighCompressBlock p mm (.const k) (kpe) H.Qa
        (eighBlockOff (.const n) (.const d) (.const lo)) H.Ma
        (eighBlockOff (.const n) (.const d) (.const lo))
        (eighBlockOff (.const n) (.const d + 1) (.const lo)) two sg Qh C1 C2 C3
      eighCompressBlock p mm (.const k) (.const k - kpe) H.Qa
        (eighBlockOff (.const n) (.const d) (.const lo) + 2 * (.const k * kpe)) H.Ma
        (eighBlockOff (.const n) (.const d) (.const lo))
        (eighBlockOff (.const n) (.const d + 1) (.const lo + kpe)) two nsg Qh C1 C2 C3
      ins (.litIdx p ⟨H.Sz, eighSlotOff (.const n) (.const d + 1) (.const lo)⟩ (kpe))
      ins (.litIdx p ⟨H.Sz, eighSlotOff (.const n) (.const d + 1) (.const lo + kpe)⟩
        (.const k - kpe))
      ins (.litIdx p ⟨H.Kd, eighSlotOff (.const n) (.const d) (.const lo)⟩ 4)
      ins (.litIdx p ⟨H.Kp, eighSlotOff (.const n) (.const d) (.const lo)⟩ (kpe)) :
        Builder P ι ℕ ℕ Unit).run st = some st') :
    let M := eighTapeMachine I p mmR qrR
    let s := eighTapeSample n d lo
    let Qp := deflate M kp Ppm (leadingBlock k (s.2 true))
    let Qm := deflate M (k - kp) Pmm (leadingBlock k (s.2 false))
    (pairLayout.Holds st'.store p H.Qa (2 * (n * n) * d + 2 * n * lo) Qp ∧
      pairLayout.Holds st'.store p H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (k * kp)) Qm ∧
      pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * lo)
        (M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Qp) A) Qp) (M.ofNat 2)) σ) ∧
      pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * (lo + kp))
        (M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Qm) A) Qm) (M.ofNat 2))
          (M.neg σ)) ∧
      st'.store.read p H.Sz (n * (d + 1) + lo) = I.sem.lit p ((kp : ℕ) : ℚ) ∧
      st'.store.read p H.Sz (n * (d + 1) + (lo + kp)) = I.sem.lit p ((k - kp : ℕ) : ℚ) ∧
      st'.store.read p H.Kd (n * d + lo) = I.sem.lit p ((4 : ℕ) : ℚ) ∧
      st'.store.read p H.Kp (n * d + lo) = I.sem.lit p ((kp : ℕ) : ℚ)) ∧
      (∀ q b i, b < s₀ → ¬ nodeWin H n d lo k (lo + kp) b i →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  intro M s Qp Qm
  -- the handles (distinctness kept as implications, out of `omega`'s sight)
  simp only [EighArenas.handles, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hlt hge
  obtain ⟨lMa, lUa, lQa, lEa, lSz, lKd, lKp, lLv, lSg, lPp, lPm, ltwo, lsg, lnsg, lsq⟩ := hlt
  obtain ⟨gG, gY, gQf, gRf, gQh, gC1, gC2, gC3⟩ := hge
  have h4a : [G, Y, Qf, Rf].Nodup :=
    (List.nodup_append.mp (show ([G, Y, Qf, Rf] ++ [Qh, C1, C2, C3]).Nodup from hnd)).1
  have h4b : [Qh, C1, C2, C3].Nodup :=
    (List.nodup_append.mp (show ([G, Y, Qf, Rf] ++ [Qh, C1, C2, C3]).Nodup from hnd)).2.1
  have dSgPp : Sg = Pp → False := fun h => by simp [EighArenas.handles, h] at hbufs
  have dSgPm : Sg = Pm → False := fun h => by simp [EighArenas.handles, h] at hbufs
  have dSgQa : Sg = H.Qa → False := fun h => by simp [EighArenas.handles, h] at hbufs
  have dPpQa : Pp = H.Qa → False := fun h => by simp [EighArenas.handles, h] at hbufs
  have dPmQa : Pm = H.Qa → False := fun h => by simp [EighArenas.handles, h] at hbufs
  have dMaQa : H.Ma = H.Qa → False := fun h => by simp [EighArenas.handles, h] at hbufs
  have dSzKd : H.Sz = H.Kd → False := fun h => by simp [EighArenas.handles, h] at hbufs
  have dSzKp : H.Sz = H.Kp → False := fun h => by simp [EighArenas.handles, h] at hbufs
  have dKdKp : H.Kd = H.Kp → False := fun h => by simp [EighArenas.handles, h] at hbufs
  have dQaSz : H.Qa = H.Sz → False := fun h => by simp [EighArenas.handles, h] at hbufs
  have dQaKd : H.Qa = H.Kd → False := fun h => by simp [EighArenas.handles, h] at hbufs
  have dQaKp : H.Qa = H.Kp → False := fun h => by simp [EighArenas.handles, h] at hbufs
  have dMaSz : H.Ma = H.Sz → False := fun h => by simp [EighArenas.handles, h] at hbufs
  have dMaKd : H.Ma = H.Kd → False := fun h => by simp [EighArenas.handles, h] at hbufs
  have dMaKp : H.Ma = H.Kp → False := fun h => by simp [EighArenas.handles, h] at hbufs
  have cc : ∀ c ∈ [two, sg, nsg, sq], ∀ b ∈ H.handles ++ [Sg, Pp, Pm], c.buf = b → False :=
    fun c hc b hb h => hcells c hc (h ▸ hb)
  have sqPp : Pp = sq.buf → False := fun h => cc sq (by simp) Pp (by simp) h.symm
  have sqPm : Pm = sq.buf → False := fun h => cc sq (by simp) Pm (by simp) h.symm
  have sqSg : Sg = sq.buf → False := fun h => cc sq (by simp) Sg (by simp) h.symm
  have sqQa : sq.buf = H.Qa → False := cc sq (by simp) H.Qa (by simp [EighArenas.handles])
  have sqMa : H.Ma = sq.buf → False := fun h =>
    cc sq (by simp) H.Ma (by simp [EighArenas.handles]) h.symm
  have twoQa : two.buf = H.Qa → False := cc two (by simp) H.Qa (by simp [EighArenas.handles])
  have sgQa : sg.buf = H.Qa → False := cc sg (by simp) H.Qa (by simp [EighArenas.handles])
  have nsgQa : nsg.buf = H.Qa → False := cc nsg (by simp) H.Qa (by simp [EighArenas.handles])
  have twoMa : two.buf = H.Ma → False := cc two (by simp) H.Ma (by simp [EighArenas.handles])
  have sgMa : sg.buf = H.Ma → False := cc sg (by simp) H.Ma (by simp [EighArenas.handles])
  have nsgMa : nsg.buf = H.Ma → False := cc nsg (by simp) H.Ma (by simp [EighArenas.handles])
  have hkn : k ≤ n := by omega
  have nS4 : ∀ b, b < s₀ → b ∉ [G, Y, Qf, Rf] := fun b hb => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; omega
  have nC4 : ∀ b, b < s₀ → b ∉ [Qh, C1, C2, C3] := fun b hb => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; omega
  have hr : ∀ (i : Instr P ℕ ℕ) (b : Builder P ι ℕ ℕ Unit),
      (ins i >>= fun _ => b).run = .seq (.instr i) b.run := fun _ _ => rfl
  -- the stored √(1/2), read from `sq` (written once by `eighProg`)
  refine name_state_node h ?_
  clear h
  intro σ2 hσ2s hσ2p h
  obtain ⟨z2, hz2, hM2⟩ : ∃ z2, st.store.read p two.buf two.idx.eval = some z2 ∧ M.ofNat 2 = z2 :=
    ⟨_, htwo, rfl⟩
  have hf2 : ∀ q b i, σ2.store.read q b i = st.store.read q b i := fun q b i => by rw [hσ2s]
  have hsh2 : σ2.store.shape = st.store.shape := by rw [hσ2s]
  have hb2 : ∀ q b i, b ≠ sq.buf → σ2.store.read q b i = st.store.read q b i :=
    fun q b i _ => hf2 q b i
  have hsq2 : σ2.store.read p sq.buf sq.idx.eval = some (I.sem.sqrtHalf p) := (hf2 _ _ _).trans hsq
  -- the first deflation
  rw [exec_eighDeflateBlock_bind_split, exec_eighDeflateBlock_congr_split, hkpe] at h
  obtain ⟨σ3, h3, h⟩ := Option.bind_eq_some_iff.mp h
  have hbo : (eighBlockOff (IExp.const n) (IExp.const d) (IExp.const lo)).eval =
      2 * (n * n) * d + 2 * n * lo := by
    simp [eighBlockOff]
  obtain ⟨hQp3, hf3, hsh3, hp3⟩ := holds_of_exec_eighDeflateBlock hmm hqr p n k kp d lo hk
    hkpk.le true (qo := eighBlockOff (.const n) (.const d) (.const lo)) (st := σ2) (st' := σ3)
    (fun i j t => (hb2 _ _ _ sqPp).trans (hPp i j t)) hsq2
    (fun w hw => (hb2 _ _ _ sqSg).trans (hSg w hw))
    (nodup_def_node dSgPp dSgQa dPpQa lSg lPp lQa h4a gG gY gQf gRf)
    (notmem5_node lsq gG gY gQf gRf sqQa) (by exact h3)
  rw [hbo] at hQp3 hf3
  have hk3 : ∀ q b i, s₀ > b → b ≠ H.Qa → σ3.store.read q b i = σ2.store.read q b i :=
    fun q b i h1 h2 => hf3 q b i (nS4 _ (by omega)) (by simp [blockDisjoint, h2])
  -- the second deflation
  rw [exec_eighDeflateBlock_bind_split, exec_eighDeflateBlock_congr_split] at h
  simp only [IExp.eval_sub, IExp.eval_const, hkpe] at h
  obtain ⟨σ4, h4, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hQm4, hf4, hsh4, hp4⟩ := holds_of_exec_eighDeflateBlock hmm hqr p n k (k - kp) d lo hk
    (Nat.sub_le _ _) false
    (qo := eighBlockOff (.const n) (.const d) (.const lo) + 2 * (.const k * kpe))
    (st := σ3) (st' := σ4)
    (fun i j t => ((hk3 _ _ _ (by omega) dPmQa).trans (hb2 _ _ _ sqPm)).trans
      (hPm i j t))
    ((hk3 _ _ _ (by omega) sqQa).trans hsq2)
    (fun w hw => ((hk3 _ _ _ (by omega) dSgQa).trans (hb2 _ _ _ sqSg)).trans
      (hSg w hw))
    (nodup_def_node dSgPm dSgQa dPmQa lSg lPm lQa h4a gG gY gQf gRf)
    (notmem5_node lsq gG gY gQf gRf sqQa) (by exact h4)
  simp only [IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat, hbo, hkpe] at hQm4 hf4
  have hk4 : ∀ q b i, s₀ > b → b ≠ H.Qa → σ4.store.read q b i = σ3.store.read q b i :=
    fun q b i h1 h2 => hf4 q b i (nS4 _ (by omega)) (by simp [blockDisjoint, h2])
  obtain ⟨F1, F3, F4, F6, F7, F2⟩ := split_arith_node (d := d) hk hkpk
  have hkk : k * k ≤ n * n := Nat.mul_le_mul hkn hkn
  have hkpn : kp * kp ≤ n * kp := Nat.mul_le_mul_right _ (by omega)
  have hkmn : (k - kp) * (k - kp) ≤ n * (k - kp) := Nat.mul_le_mul_right _ (by omega)
  have hkkn : k * k ≤ n * k := Nat.mul_le_mul_right _ hkn
  have hkkp : k * kp + k * (k - kp) = k * k := by
    rw [← Nat.mul_add, Nat.add_sub_cancel' hkpk.le]
  have hlok : n * lo + n * k ≤ n * n := by rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ hk
  have hQp4 : pairLayout.Holds σ4.store p H.Qa (2 * (n * n) * d + 2 * n * lo) Qp :=
    holds_keep_node hQp3 fun i _ hi => hf4 p _ i (nS4 _ (by omega)) (by
        simp only [blockDisjoint, bne_self_eq_false, Bool.false_or, Bool.or_eq_true,
          decide_eq_true_eq]
        left; omega)
  have hst4 : ∀ q b i, s₀ > b → b ≠ H.Qa → b ≠ sq.buf →
      σ4.store.read q b i = st.store.read q b i := fun q b i h1 h2 h3 =>
    (hk4 q b i h1 h2).trans ((hk3 q b i h1 h2).trans (hb2 q b i h3))
  have hA4 : pairLayout.Holds σ4.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A :=
    fun i j t => (hst4 _ _ _ (by omega) dMaQa sqMa).trans (hA i j t)
  have hcst4 : ∀ c : Cell ℕ ℕ, c.buf < s₀ → c.buf ≠ H.Qa →
      σ4.store.read p c.buf c.idx.eval = st.store.read p c.buf c.idx.eval :=
    fun c h1 h2 => (hk4 _ _ _ h1 h2).trans ((hk3 _ _ _ h1 h2).trans (hf2 _ _ _))
  have htwo4 := (hcst4 two ltwo twoQa).trans hz2
  have hσ4 := (hcst4 sg lsg sgQa).trans hσ
  have hnσ4 := (hcst4 nsg lnsg nsgQa).trans hnσ
  -- the first compression
  rw [exec_eighCompressBlock_bind_split, exec_eighCompressBlock_congr_split, hkpe] at h
  obtain ⟨σ5, h5, h⟩ := Option.bind_eq_some_iff.mp h
  have hbo1 : (eighBlockOff (IExp.const n) (IExp.const d + 1) (IExp.const lo)).eval =
      2 * (n * n) * (d + 1) + 2 * n * lo := by
    simp [eighBlockOff]
  have hbo2 : (eighBlockOff (IExp.const n) (IExp.const d + 1)
      (IExp.const lo + kpe)).eval = 2 * (n * n) * (d + 1) + 2 * n * (lo + kp) := by
    simp [eighBlockOff, hkpe]
  obtain ⟨hAp5, hf5, hsh5, hp5⟩ := holds_of_exec_eighCompressBlock
    (toNat := fun x => (I.sem.toNat p x).getD 0) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    hmm p k kp (qo := eighBlockOff (.const n) (.const d) (.const lo))
    (mo := eighBlockOff (.const n) (.const d) (.const lo))
    (co := eighBlockOff (.const n) (.const d + 1) (.const lo)) (st := σ4) (st' := σ5)
    (by rw [hbo]; exact hQp4) (by rw [hbo]; exact hA4) htwo4 hσ4
    (nodup_cmp_node (fun h => dMaQa h.symm) lQa lMa h4b gQh gC1 gC2 gC3)
    ⟨nC4 _ ltwo, nC4 _ lsg⟩
    (by
      rw [hbo, hbo1]
      simp only [blockDisjoint, bne_self_eq_false, Bool.false_or, Bool.or_eq_true,
        decide_eq_true_eq]
      right; linarith)
    ⟨by simp [blockDisjoint, show H.Ma ≠ two.buf from fun h => twoMa h.symm],
      by simp [blockDisjoint, show H.Ma ≠ sg.buf from fun h => sgMa h.symm]⟩ (by exact h5)
  rw [hbo1, ← hM2] at hAp5
  rw [hbo1] at hf5
  have hk5 : ∀ q b i, s₀ > b → b ≠ H.Ma → σ5.store.read q b i = σ4.store.read q b i :=
    fun q b i h1 h2 => hf5 q b i (nC4 _ (by omega)) (by simp [blockDisjoint, h2])
  -- the second compression
  rw [exec_eighCompressBlock_bind_split, exec_eighCompressBlock_congr_split] at h
  simp only [IExp.eval_sub, IExp.eval_const, hkpe] at h
  obtain ⟨σ6, h6, h⟩ := Option.bind_eq_some_iff.mp h
  have hqo2 : (eighBlockOff (IExp.const n) (IExp.const d) (IExp.const lo) +
      2 * (IExp.const k * kpe)).eval = 2 * (n * n) * d + 2 * n * lo + 2 * (k * kp) := by
    simp [eighBlockOff, hkpe]
  obtain ⟨hAm6, hf6, hsh6, hp6⟩ := holds_of_exec_eighCompressBlock
    (toNat := fun x => (I.sem.toNat p x).getD 0) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    hmm p k (k - kp)
    (qo := eighBlockOff (.const n) (.const d) (.const lo) + 2 * (.const k * kpe))
    (mo := eighBlockOff (.const n) (.const d) (.const lo))
    (co := eighBlockOff (.const n) (.const d + 1) (.const lo + kpe)) (st := σ5)
    (st' := σ6)
    (by
      rw [hqo2]
      exact fun i j t => (hk5 _ _ _ (by omega) (fun h => dMaQa h.symm)).trans (hQm4 i j t))
    (by
      rw [hbo]
      exact holds_keep_node hA4 fun i _ hi => hf5 p _ i (nC4 _ (by omega)) (by
          simp only [blockDisjoint, bne_self_eq_false, Bool.false_or, Bool.or_eq_true,
            decide_eq_true_eq]
          left; linarith))
    ((hk5 _ _ _ ltwo twoMa).trans htwo4) ((hk5 _ _ _ lnsg nsgMa).trans hnσ4)
    (nodup_cmp_node (fun h => dMaQa h.symm) lQa lMa h4b gQh gC1 gC2 gC3)
    ⟨nC4 _ ltwo, nC4 _ lnsg⟩
    (by
      rw [hbo, hbo2]
      simp only [blockDisjoint, bne_self_eq_false, Bool.false_or, Bool.or_eq_true,
        decide_eq_true_eq]
      right; linarith)
    ⟨by simp [blockDisjoint, show H.Ma ≠ two.buf from fun h => twoMa h.symm],
      by simp [blockDisjoint, show H.Ma ≠ nsg.buf from fun h => nsgMa h.symm]⟩ (by exact h6)
  rw [hbo2, ← hM2] at hAm6
  rw [hbo2] at hf6
  have hk6 : ∀ q b i, s₀ > b → b ≠ H.Ma → σ6.store.read q b i = σ5.store.read q b i :=
    fun q b i h1 h2 => hf6 q b i (nC4 _ (by omega)) (by simp [blockDisjoint, h2])
  -- the records
  rw [hr] at h
  obtain ⟨v7, s7, hv7, hw7, h⟩ := eighSignH_inv_litIdx h
  rw [hr] at h
  obtain ⟨v8, s8, hv8, hw8, h⟩ := eighSignH_inv_litIdx h
  rw [hr] at h
  obtain ⟨v9, s9, hv9, hw9, h⟩ := eighSignH_inv_litIdx h
  change exec I (.seq (.instr _) .skip) _ = some st' at h
  obtain ⟨v10, s10, hv10, hw10, h⟩ := eighSignH_inv_litIdx h
  rw [exec_skip, Option.some_inj] at h
  subst h
  simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat,
    IExp.eval_sub, hkpe] at hv7 hw7 hv8 hw8 hv9 hw9 hv10 hw10
  have hrec : ∀ q b i, b ≠ H.Sz → b ≠ H.Kd → b ≠ H.Kp →
      s10.read q b i = σ6.store.read q b i := fun q b i h1 h2 h3 => by
    rw [Store.read_of_write_eq_some_of_ne hw10 (Or.inl h3),
      Store.read_of_write_eq_some_of_ne hw9 (Or.inl h2),
      Store.read_of_write_eq_some_of_ne hw8 (Or.inl h1),
      Store.read_of_write_eq_some_of_ne hw7 (Or.inl h1)]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact fun i j t => (hrec _ _ _ dQaSz dQaKd dQaKp).trans
      ((hk6 _ _ _ (by omega) (fun h => dMaQa h.symm)).trans
        ((hk5 _ _ _ (by omega) (fun h => dMaQa h.symm)).trans (hQp4 i j t)))
  · exact fun i j t => (hrec _ _ _ dQaSz dQaKd dQaKp).trans
      ((hk6 _ _ _ (by omega) (fun h => dMaQa h.symm)).trans
        ((hk5 _ _ _ (by omega) (fun h => dMaQa h.symm)).trans (hQm4 i j t)))
  · refine fun i j t => (hrec _ _ _ dMaSz dMaKd dMaKp).trans ?_
    refine (hf6 _ _ _ (nC4 _ (by omega)) ?_).trans (hAp5 i j t)
    have := pair_idx_lt_node i j t
    simp only [blockDisjoint, bne_self_eq_false, Bool.false_or, Bool.or_eq_true,
      decide_eq_true_eq]
    left
    change _ + (2 * _ + _) + 1 ≤ _
    linarith
  · exact fun i j t => (hrec _ _ _ dMaSz dMaKd dMaKp).trans (hAm6 i j t)
  · rw [Store.read_of_write_eq_some_of_ne hw10 (Or.inl dSzKp),
      Store.read_of_write_eq_some_of_ne hw9 (Or.inl dSzKd),
      Store.read_of_write_eq_some_of_ne hw8 (Or.inr (by omega)),
      Store.read_of_write_eq_some hw7, hv7]
  · rw [Store.read_of_write_eq_some_of_ne hw10 (Or.inl dSzKp),
      Store.read_of_write_eq_some_of_ne hw9 (Or.inl dSzKd),
      Store.read_of_write_eq_some hw8, hv8]
  · rw [Store.read_of_write_eq_some_of_ne hw10 (Or.inl dKdKp),
      Store.read_of_write_eq_some hw9, hv9]
  · rw [Store.read_of_write_eq_some hw10, hv10]
  · intro q b i hb hW
    simp only [nodeWin, not_or, not_and, not_lt] at hW
    obtain ⟨hWQ, hWM, hWS, hWK⟩ := hW
    rw [Store.read_of_write_eq_some_of_ne hw10 ?_, Store.read_of_write_eq_some_of_ne hw9 ?_,
      Store.read_of_write_eq_some_of_ne hw8 ?_, Store.read_of_write_eq_some_of_ne hw7 ?_]
    rotate_left
    · by_cases h1 : b = H.Sz
      · exact Or.inr (fun h2 => by have := hWS h1; omega)
      · exact Or.inl h1
    · by_cases h1 : b = H.Sz
      · exact Or.inr (fun h2 => by have := hWS h1; omega)
      · exact Or.inl h1
    · by_cases h1 : b = H.Kd
      · exact Or.inr (fun h2 => hWK (Or.inl h1) h2)
      · exact Or.inl h1
    · by_cases h1 : b = H.Kp
      · exact Or.inr (fun h2 => hWK (Or.inr h1) h2)
      · exact Or.inl h1
    have hbM : b = H.Ma → i < 2 * (n * n) * (d + 1) + 2 * n * lo ∨
        2 * (n * n) * (d + 1) + 2 * n * (lo + k) ≤ i := fun h1 => by
      by_contra hc
      push_neg at hc
      exact absurd (hWM h1 hc.1) (by omega)
    have hbQ : b = H.Qa → i < 2 * (n * n) * d + 2 * n * lo ∨
        2 * (n * n) * d + 2 * n * (lo + k) ≤ i := fun h1 => by
      by_contra hc
      push_neg at hc
      exact absurd (hWQ h1 hc.1) (by omega)
    rw [hf6 q b i (nC4 b hb) (bd_of_win_node hbM (by linarith) (by linarith)),
      hf5 q b i (nC4 b hb) (bd_of_win_node hbM (by linarith)
        (by linarith [Nat.zero_le ((k - kp) * (k - kp))])),
      hf4 q b i (nS4 b hb) (bd_of_win_node hbQ (by linarith [Nat.zero_le (k * kp)])
        (by linarith)),
      hf3 q b i (nS4 b hb) (bd_of_win_node hbQ (by linarith) (by linarith))]
    exact hf2 q b i
  · rw [Store.shape_of_write_eq_some hw10, Store.shape_of_write_eq_some hw9,
      Store.shape_of_write_eq_some hw8, Store.shape_of_write_eq_some hw7, hsh6, hsh5, hsh4, hsh3]
    exact hsh2
  · exact hp6.trans (hp5.trans (hp4.trans (hp3.trans hσ2p)))

omit [AddMonoid C] [Inhabited K] in
/-- Reads of a store below $m$ pops. -/
private theorem read_pops_node : ∀ (m : ℕ) {s : Store P K} {q : P} {b i : ℕ}, b + m < s.size →
    Store.read (Array.pop^[m] s) q b i = s.read q b i
  | 0, _, _, _, _, _ => rfl
  | m + 1, s, q, b, i, h => by
    rw [Function.iterate_succ_apply, read_pops_node m (by simp [Array.size_pop]; omega),
      Store.read_pop_of_lt (by omega)]

omit [AddMonoid C] [Inhabited K] in
/-- Reads of a store below $m$ pushes. -/
private theorem read_pushes_node (x : P × Array (Option K)) : ∀ (m : ℕ) {s : Store P K} {q : P}
    {b i : ℕ}, b < s.size → Store.read ((fun s : Store P K => s.push x)^[m] s) q b i = s.read q b i
  | 0, _, _, _, _, _ => rfl
  | m + 1, s, q, b, i, h => by
    rw [Function.iterate_succ_apply, read_pushes_node x m (by simp; omega),
      Store.read_push_of_lt h]

omit [AddMonoid C] [Inhabited K] in
/-- The size of a store after $m$ pushes. -/
private theorem size_pushes_node (x : P × Array (Option K)) : ∀ (m : ℕ) (s : Store P K),
    ((fun s : Store P K => s.push x)^[m] s).size = s.size + m
  | 0, _ => rfl
  | m + 1, s => by
    rw [Function.iterate_succ_apply, size_pushes_node x m]; simp; omega

omit [AddMonoid C] [Inhabited K] in
/-- The shape of a store after $m$ pushes, below the old size. -/
private theorem shape_pushes_node (x : P × Array (Option K)) : ∀ (m : ℕ) {s : Store P K} {b : ℕ},
    b < s.size → (Store.shape ((fun s : Store P K => s.push x)^[m] s))[b]? = s.shape[b]?
  | 0, _, _, _ => rfl
  | m + 1, s, b, h => by
    rw [Function.iterate_succ_apply, shape_pushes_node x m (by simp; omega),
      Store.getElem?_shape_push_of_lt _ h]

omit [Inhabited K] in
/-- The run of an allocation, inverted. -/
private theorem alloc_inv_node {p : P} {len : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ}
    {st st' : St P K C} (h : exec I (.alloc p len body) st = some st') :
    ∃ st₂, exec I (body st.store.size) { st with
          store := st.store.push (p, Array.replicate len.eval none),
          cur := Function.update st.cur p (st.cur p + len.eval),
          peak := Function.update st.peak p (max (st.peak p) (st.cur p + len.eval)),
          curW := st.curW + len.eval * I.width p,
          peakW := max st.peakW (st.curW + len.eval * I.width p) } = some st₂ ∧
      { st₂ with
          store := Array.pop st₂.store
          cur := Function.update st₂.cur p (st₂.cur p - len.eval)
          curW := st₂.curW - len.eval * I.width p } = st' := by
  rw [exec_alloc] at h
  exact Option.map_eq_some_iff.mp h

omit [Inhabited K] in
/-- The run of a scoped allocation, inverted. -/
private theorem alloc_inv_skip_node {p : P} {len : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ}
    {st st' : St P K C} (h : exec I (.seq (.alloc p len body) .skip) st = some st') :
    ∃ st₂, exec I (body st.store.size) { st with
          store := st.store.push (p, Array.replicate len.eval none),
          cur := Function.update st.cur p (st.cur p + len.eval),
          peak := Function.update st.peak p (max (st.peak p) (st.cur p + len.eval)),
          curW := st.curW + len.eval * I.width p,
          peakW := max st.peakW (st.curW + len.eval * I.width p) } = some st₂ ∧
      { st₂ with
          store := Array.pop st₂.store
          cur := Function.update st₂.cur p (st₂.cur p - len.eval)
          curW := st₂.curW - len.eval * I.width p } = st' :=
  alloc_inv_node ((exec_seq_skip I _ st).symm.trans h)

-- The eight allocations of a split.
set_option maxHeartbeats 4000000 in
/-- **A split writes the outcome of `NLAlib.eighStep`'s split**, with its precise frame: the values
of `NLAlib.holds_of_exec_eighSplitBlock`, and every cell outside the node's window (`nodeWin`)
unchanged; `NLAlib.holds_of_exec_eighSplitBlock` is its coarse form. -/
private theorem holds_of_exec_eighSplitBlock_frame {mm qr : ι}
    (hmm : IsMatMulKernel I mm pairLayout mmR) (hqr : IsQRKernel I qr pairLayout qrR) (p : P)
    (n d lo k kp : ℕ) (hk : lo + k ≤ n) (hkp : 0 < kp) (hkpk : kp < k) (kpe : IExp ℕ)
    (hkpe : kpe.eval = kp) (H : EighArenas)
    {Sg Pp Pm : ℕ} {two sg nsg sq : Cell ℕ ℕ} {σ : K} {st st' : St P K C}
    {A : Matrix (Fin k) (Fin k) (K × K)} {Ppm Pmm : Matrix (Fin k) (Fin k) (K × K)}
    {D : ℕ} (hd : d < D) (hH : H.Shaped st.store p n D)
    (hbufs : (H.handles ++ [Sg, Pp, Pm]).Nodup)
    (hA : pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hPp : pairLayout.Holds st.store p Pp 0 Ppm) (hPm : pairLayout.Holds st.store p Pm 0 Pmm)
    (hSg : ∀ w < 4 * (n * n), st.store.read p Sg w = some (I.tape .gaussian (4 * (n * n) * d + w)))
    (htwo : st.store.read p two.buf two.idx.eval = some ((eighTapeMachine I p mmR qrR).ofNat 2))
    (hσ : st.store.read p sg.buf sg.idx.eval = some σ)
    (hnσ : st.store.read p nsg.buf nsg.idx.eval =
      some ((eighTapeMachine I p mmR qrR).neg σ))
    (hcells : ∀ c ∈ [two, sg, nsg, sq], c.buf ∉ H.handles ++ [Sg, Pp, Pm])
    (hsq : st.store.read p sq.buf sq.idx.eval = some (I.sem.sqrtHalf p))
    (h : exec I (eighSplitBlock p mm qr (.const n) (.const d) (.const lo) (.const k) kpe Sg
      Pp Pm H.Ma H.Qa H.Sz H.Kd H.Kp two sg nsg sq).run st = some st') :
    let M := eighTapeMachine I p mmR qrR
    let s := eighTapeSample n d lo
    let Qp := deflate M kp Ppm (leadingBlock k (s.2 true))
    let Qm := deflate M (k - kp) Pmm (leadingBlock k (s.2 false))
    (pairLayout.Holds st'.store p H.Qa (2 * (n * n) * d + 2 * n * lo) Qp ∧
      pairLayout.Holds st'.store p H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (k * kp)) Qm ∧
      pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * lo)
        (M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Qp) A) Qp) (M.ofNat 2)) σ) ∧
      pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * (lo + kp))
        (M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Qm) A) Qm) (M.ofNat 2))
          (M.neg σ)) ∧
      st'.store.read p H.Sz (n * (d + 1) + lo) = I.sem.lit p ((kp : ℕ) : ℚ) ∧
      st'.store.read p H.Sz (n * (d + 1) + (lo + kp)) = I.sem.lit p ((k - kp : ℕ) : ℚ) ∧
      st'.store.read p H.Kd (n * d + lo) = I.sem.lit p ((4 : ℕ) : ℚ) ∧
      st'.store.read p H.Kp (n * d + lo) = I.sem.lit p ((kp : ℕ) : ℚ)) ∧
      (∀ q b i, ¬ nodeWin H n d lo k (lo + kp) b i →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  intro M s Qp Qm
  have hsz : ∀ {b : ℕ} {x : P × ℕ}, st.store.shape[b]? = some x → b < st.store.size :=
    fun h => by simpa [Store.size_shape] using (Array.getElem?_eq_some_iff.mp h).1
  obtain ⟨-, hMa, hUa, hQa, hEa, hSz, hKd, hKp, hLv⟩ := id hH
  have hk0 : 0 < k := by omega
  have hn2 : 0 < 4 * (n * n) := by have : 0 < n := (by omega); positivity
  have lSg := Store.lt_size_of_read_eq_some (hSg 0 hn2)
  have lPp := Store.lt_size_of_read_eq_some (hPp ⟨0, hk0⟩ ⟨0, hk0⟩ ⟨0, two_pos⟩)
  have lPm := Store.lt_size_of_read_eq_some (hPm ⟨0, hk0⟩ ⟨0, hk0⟩ ⟨0, two_pos⟩)
  have ltwo := Store.lt_size_of_read_eq_some htwo
  have lsg := Store.lt_size_of_read_eq_some hσ
  have lnsg := Store.lt_size_of_read_eq_some hnσ
  have lsq := Store.lt_size_of_read_eq_some hsq
  have hlt : ∀ b ∈ H.handles ++ [Sg, Pp, Pm, two.buf, sg.buf, nsg.buf, sq.buf],
      b < st.store.size := by
    simp only [EighArenas.handles, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro b (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl)
    exacts [hsz hMa, hsz hUa, hsz hQa, hsz hEa, hsz hSz, hsz hKd, hsz hKp, hsz hLv, lSg, lPp,
      lPm, ltwo, lsg, lnsg, lsq]
  set x : P × Array (Option K) := (p, Array.replicate (2 * (IExp.const n * IExp.const n)).eval none)
    with hx
  obtain ⟨s₁, h₁, e₁⟩ := alloc_inv_skip_node h
  obtain ⟨s₂, h₂, e₂⟩ := alloc_inv_node h₁
  obtain ⟨s₃, h₃, e₃⟩ := alloc_inv_node h₂
  obtain ⟨s₄, h₄, e₄⟩ := alloc_inv_node h₃
  obtain ⟨s₅, h₅, e₅⟩ := alloc_inv_node h₄
  obtain ⟨s₆, h₆, e₆⟩ := alloc_inv_node h₅
  obtain ⟨s₇, h₇, e₇⟩ := alloc_inv_node h₆
  obtain ⟨s₈, h₈, e₈⟩ := alloc_inv_node h₇
  clear h h₁ h₂ h₃ h₄ h₅ h₆ h₇
  subst e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈
  have key := split_body_holds hmm hqr p n d lo k kp hk hkp hkpk kpe hkpe H hd st.store.size hlt
    _ _ _ _ _ _ _ _ (by simp <;> omega) (by simp [List.nodup_cons] <;> omega) hbufs
    (fun i j t => (read_pushes_node x 8 (hlt _ (by simp [EighArenas.handles]))).trans (hA i j t))
    (fun i j t => (read_pushes_node x 8 lPp).trans (hPp i j t))
    (fun i j t => (read_pushes_node x 8 lPm).trans (hPm i j t))
    (fun w hw => (read_pushes_node x 8 lSg).trans (hSg w hw))
    ((read_pushes_node x 8 ltwo).trans htwo)
    ((read_pushes_node x 8 lsg).trans hσ) ((read_pushes_node x 8 lnsg).trans hnσ) hcells
    ((read_pushes_node x 8 lsq).trans hsq)
    (h := h₈)
  obtain ⟨⟨v1, v2, v3, v4, v5, v6, v7, v8⟩, hfr, hsh, hps⟩ := key
  have hsz8 : s₈.store.size = st.store.size + 8 := by
    rw [Store.size_eq_of_shape_eq hsh]
    exact size_pushes_node x 8 st.store
  have hpop : ∀ {q : P} {b i : ℕ}, b < st.store.size →
      Store.read (Array.pop^[8] s₈.store) q b i = s₈.store.read q b i :=
    fun hb => read_pops_node 8 (by omega)
  have lQa : H.Qa < st.store.size := hsz hQa
  have lMa : H.Ma < st.store.size := hsz hMa
  refine ⟨⟨fun i j t => (hpop lQa).trans (v1 i j t), fun i j t => (hpop lQa).trans (v2 i j t),
    fun i j t => (hpop lMa).trans (v3 i j t), fun i j t => (hpop lMa).trans (v4 i j t),
    (hpop (hsz hSz)).trans v5, (hpop (hsz hSz)).trans v6, (hpop (hsz hKd)).trans v7,
    (hpop (hsz hKp)).trans v8⟩, fun q b i hW => ?_, ?_, hps⟩
  · by_cases hb : b < st.store.size
    · exact (hpop hb).trans ((hfr q b i hb hW).trans (read_pushes_node x 8 hb))
    · have hsz' : (Array.pop^[8] s₈.store).size = st.store.size := by
        simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, Array.size_pop,
          hsz8]
        omega
      exact (show Store.read (Array.pop^[8] s₈.store) q b i = none from
        Store.read_eq_none_of_size_le (by omega)).trans
          (Store.read_eq_none_of_size_le (by omega)).symm
  · change Store.shape (Array.pop (Array.pop (Array.pop (Array.pop (Array.pop (Array.pop
      (Array.pop (Array.pop s₈.store)))))))) = _
    simp only [Store.shape_pop, hsh]
    simp [Store.shape, x]

-- The corrected frame lemma is applied to a large run.
set_option maxHeartbeats 1000000 in
/-- **A split writes the outcome of `NLAlib.eighStep`'s split**: if the kernels of `I` are the
routines `mmR`, `qrR` on interleaved pairs, a successful run of `NLAlib.eighSplitBlock` at the slot
$lo$ of depth $d$ for a node of size $k$ (with $lo + k \le n$) whose matrix $\mathbf{A}$ is held at
its block of `Ma`, with $0 < k_+ < k$, the projectors $\mathbf{P}_\pm$ at offset $0$ of `Pp`, `Pm`,
the level's Gaussian words in `Sg`, and the cells `two`, `sg`, `nsg`, `sq` (outside the arenas,
`Sg`, `Pp` and `Pm`) holding the machine's $\mathrm{fl}(2)$, $\sigma$, $-\sigma$ and the stored
$\sqrt{1/2}$ (`NLAlib.Computation.ScalarSem.sqrtHalf`, computed once by `NLAlib.eighProg`), ends
with: $\mathbf{Q}_+ =$
`NLAlib.deflate M kp Pp G₊` and $\mathbf{Q}_-$ packed at the node's block of `Qa`, the compressions
of `NLAlib.eighStep` at the blocks of the slots $lo$ and $lo + k_+$ of depth $d + 1$ in `Ma`, the
sizes $k_+$ and $k - k_+$ in their cells of `Sz`, the kind $4$ and $k_+$ in the node's cells of `Kd`
and `Kp`; every other cell of the arenas, and every cell outside them, is unchanged ($M$ = `NLAlib.eighTapeMachine I p mmR qrR`, the test matrices those of the node's
samples, `NLAlib.eighTapeSample`). No printed source.
(Design note §8: the hoist of $\sqrt{1/2}$ to `NLAlib.eighProg` made the split read `sq` only,
so the frame has no exemption and needs no distinctness of `sq`.)
Proof: the private `holds_of_exec_eighSplitBlock_frame`, whose window of the node lies in the
cells of depths $d$ and $d + 1$. -/
theorem holds_of_exec_eighSplitBlock {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) (p : P) (n d lo k kp : ℕ) (hk : lo + k ≤ n)
    (hkp : 0 < kp) (hkpk : kp < k) (H : EighArenas) {Sg Pp Pm : ℕ} {two sg nsg sq : Cell ℕ ℕ}
    {σ : K} {st st' : St P K C} {A : Matrix (Fin k) (Fin k) (K × K)}
    {Ppm Pmm : Matrix (Fin k) (Fin k) (K × K)}
    {D : ℕ} (hd : d < D) (hH : H.Shaped st.store p n D)
    (hbufs : (H.handles ++ [Sg, Pp, Pm]).Nodup)
    (hA : pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hPp : pairLayout.Holds st.store p Pp 0 Ppm) (hPm : pairLayout.Holds st.store p Pm 0 Pmm)
    (hSg : ∀ w < 4 * (n * n), st.store.read p Sg w = some (I.tape .gaussian (4 * (n * n) * d + w)))
    (htwo : st.store.read p two.buf two.idx.eval = some ((eighTapeMachine I p mmR qrR).ofNat 2))
    (hσ : st.store.read p sg.buf sg.idx.eval = some σ)
    (hnσ : st.store.read p nsg.buf nsg.idx.eval =
      some ((eighTapeMachine I p mmR qrR).neg σ))
    (hcells : ∀ c ∈ [two, sg, nsg, sq], c.buf ∉ H.handles ++ [Sg, Pp, Pm])
    (hsq : st.store.read p sq.buf sq.idx.eval = some (I.sem.sqrtHalf p))
    (h : exec I (eighSplitBlock p mm qr (.const n) (.const d) (.const lo) (.const k) (.const kp) Sg
      Pp Pm H.Ma H.Qa H.Sz H.Kd H.Kp two sg nsg sq).run st = some st') :
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
  intro M s Qp Qm
  have key := holds_of_exec_eighSplitBlock_frame (Sg := Sg) (Pp := Pp) (Pm := Pm)
    (two := two) (sg := sg) (nsg := nsg) (sq := sq) (σ := σ) (st := st) (st' := st') (A := A)
    (Ppm := Ppm) (Pmm := Pmm) hmm hqr p n d lo k kp hk hkp hkpk (.const kp) rfl H hd hH
    hbufs hA hPp hPm hSg htwo hσ hnσ hcells hsq h
  refine ⟨key.1.1, key.1.2.1, key.1.2.2.1, key.1.2.2.2.1, key.1.2.2.2.2.1, key.1.2.2.2.2.2.1,
    key.1.2.2.2.2.2.2.1, key.1.2.2.2.2.2.2.2, fun q b i h0 h1' => key.2.1 q b i ?_,
    key.2.2.1, key.2.2.2⟩
  intro hw
  have hnk : n * lo + n * k ≤ n * n := by rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ hk
  have e1 : 2 * (n * n) * d + 2 * n * (lo + k) ≤ 2 * (n * n) * (d + 1) := by nlinarith
  have e2 : 2 * (n * n) * (d + 1) + 2 * n * (lo + k) ≤ 2 * (n * n) * (d + 1 + 1) := by nlinarith
  have e3 : n * (d + 1) + lo + k ≤ n * (d + 1 + 1) := by nlinarith
  have e4 : n * d + lo < n * (d + 1) := by nlinarith
  unfold nodeWin at hw
  unfold EighArenas.LevelCell at h0 h1'
  rcases hw with ⟨rfl, a, b'⟩ | ⟨rfl, a, b'⟩ | ⟨rfl, hi⟩ | ⟨hb, rfl⟩
  · exact h0 (Or.inl ⟨Or.inr (Or.inr rfl), by omega, by omega⟩)
  · exact h1' (Or.inl ⟨Or.inl rfl, by omega, by omega⟩)
  · exact h1' (Or.inr (Or.inl ⟨Or.inr (Or.inl rfl), by rcases hi with rfl | rfl <;> omega,
      by rcases hi with rfl | rfl <;> omega⟩))
  · refine h0 (Or.inr (Or.inl ⟨?_, by omega, by omega⟩))
    rcases hb with hb | hb
    · exact Or.inr (Or.inr (Or.inl hb))
    · exact Or.inr (Or.inr (Or.inr hb))


omit [Inhabited K] in
private theorem node_inv_copy {p : P} {dst src : Cell ℕ ℕ} {t : Stmt P ι ℕ ℕ}
    {s s₂ : St P K C} (h : exec I (.seq (.instr (.copy p dst src)) t) s = some s₂) :
    ∃ a s', s.store.read p src.buf src.idx.eval = some a ∧
      s.store.write p dst.buf dst.idx.eval a = some s' ∧
      exec I t { s with store := s', cnt := s.cnt + I.charge (.copy p) } = some s₂ := by
  rw [exec_seq, exec_instr] at h
  simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨_, ⟨a, ha, s', hw, rfl⟩, rfl⟩, h⟩ := h
  exact ⟨a, s', ha, hw, h⟩

omit [Inhabited K] in
/-- A trace keeps the shape of the store and the tape positions. -/
private theorem shape_pos_of_exec_ztraceRe_node (p : P) (n : ℕ) {X : ℕ} {xo : IExp ℕ}
    {dst : Cell ℕ ℕ} {st st' : St P K C}
    (h : exec I (ztraceRe (ι := ι) p (.const n) X xo dst).run st = some st') :
    st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  have hins : ∀ {i : Instr P ℕ ℕ} {s s' : St P K C}, (∀ q d x, i ≠ .draw q d x) →
      exec I (.instr i) s = some s' → s'.store.shape = s.store.shape ∧ s'.pos = s.pos := by
    intro i s s' hi hs
    rw [exec_instr] at hs
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hs
    refine ⟨Instr.shape_of_run_eq_some hr, ?_⟩
    cases i with
    | draw q d x => exact absurd rfl (hi q d x)
    | _ => simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr; aesop
  change exec I (.seq (.named _ _ (.seq (.instr _) (.seq (.loop _ _) .skip))) .skip) st =
    some st' at h
  rw [exec_seq_skip, exec_named, exec_seq] at h
  obtain ⟨s₁, h₁, h⟩ := Option.bind_eq_some_iff.mp h
  rw [exec_seq_skip] at h
  obtain ⟨hsh₁, hps₁⟩ := hins (by intro _ _ _ h; cases h) h₁
  refine forall_of_exec_loop_eq_some I
    (fun _ s => s.store.shape = st.store.shape ∧ s.pos = st.pos) ⟨hsh₁, hps₁⟩ ?_ h
  rintro i - s₃ s₄ ⟨hsh, hps⟩ hex
  change exec I (.seq (.instr (.bin _ _ _ _ _)) .skip) s₃ = some s₄ at hex
  rw [exec_seq_skip] at hex
  obtain ⟨hsh₄, hps₄⟩ := hins (by intro _ _ _ h; cases h) hex
  exact ⟨hsh₄.trans hsh, hps₄.trans hps⟩

omit [Inhabited K] in
/-- A kernel block, then the rest. -/
private theorem node_bind {b : Builder P ι ℕ ℕ Unit} {X : Stmt P ι ℕ ℕ}
    (hb : ∀ k, ContT.run b k = .seq X (k ())) {f : Unit → Builder P ι ℕ ℕ Unit}
    {st st' : St P K C} (h : exec I (b >>= f).run st = some st') :
    ∃ σ, exec I b.run st = some σ ∧ exec I (f ()).run σ = some st' := by
  rw [exec_run_bind I hb] at h
  exact Option.bind_eq_some_iff.mp h

-- The set-up unfolds the instructions of the node step.
set_option maxHeartbeats 4000000 in
/-- The set-up of a node step, up to the index binder: the stored $\sigma$, $-\sigma$, the
projectors and $\mathrm{fl}(t + \mathrm{fl}(1/2))$; only scratch buffers (at handles from `s₀`)
are written. -/
private theorem node_setup_holds {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR) (p : P)
    (hflag : I.sem.DecidesFlags p) (n ℓ₀ F d lo k : ℕ) (hk : lo + k ≤ n) (H : EighArenas)
    {par Su c : ℕ} {st st' : St P K C} {A : Matrix (Fin k) (Fin k) (K × K)} {R β : K}
    (s₀ : ℕ) (hlt : ∀ b ∈ H.handles ++ [par, Su, c], b < s₀)
    (t sp W B T Pp Pm : ℕ) (hge : ∀ X ∈ [t, sp, W, B, T, Pp, Pm], s₀ ≤ X)
    (hnd : [t, sp, W, B, T, Pp, Pm].Nodup)
    (hB : st.store.shape[B]? = some (p, 2 * (n * n)))
    (hA : pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hR : st.store.read p H.Lv (2 * d) = some R)
    (hpar : st.store.read p par 2 = some β)
    (hSu : st.store.read p Su lo = some (I.tape .uniform (n * d + lo)))
    (hc : st.store.read p c 0 = I.sem.lit p 1 ∧ st.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
      st.store.read p c 2 = some ((eighTapeMachine I p mmR qrR).div
        (eighTapeMachine I p mmR qrR).one ((eighTapeMachine I p mmR qrR).ofNat 2)) ∧
      st.store.read p c 3 = some ((eighTapeMachine I p mmR qrR).neg
        (eighTapeMachine I p mmR qrR).one))
    (rest : Builder P ι ℕ ℕ Unit)
    (h : exec I (do
      ins (.bin p .div ⟨t, 0⟩ ⟨H.Lv, 2 * .const d⟩ ⟨c, 1⟩)
      ins (.un p .neg ⟨t, 1⟩ ⟨t, 0⟩)
      ins (.litIdx p ⟨t, 2⟩ (.const ℓ₀ + .const d))
      ins (.bin p .div ⟨t, 3⟩ ⟨H.Lv, 2 * .const d⟩ ⟨t, 2⟩)
      ins (.bin p .mul ⟨t, 4⟩ ⟨t, 3⟩ ⟨Su, .const lo⟩)
      zhermShift p (.const k) H.Ma (eighBlockOff (.const n) (.const d) (.const lo)) ⟨t, 4⟩ W 0
      ins (.copy p ⟨sp, 0⟩ ⟨par, 2⟩)
      ins (.bin p .mul ⟨sp, 1⟩ ⟨c, 1⟩ ⟨H.Lv, 2 * .const d⟩)
      eighSignBlock p mm (.const k) (.const F) W 0 sp 0 B 0
      zhermShift p (.const k) B 0 ⟨c, 3⟩ T 0
      zhermScale p (.const k) T 0 ⟨c, 1⟩ Pp 0
      zhermShift p (.const k) B 0 ⟨c, 0⟩ T 0
      zneg p (.const k) (.const k) T 0 T 0
      zhermScale p (.const k) T 0 ⟨c, 1⟩ Pm 0
      ztraceRe p (.const k) Pp 0 ⟨t, 5⟩
      ins (.bin p .add ⟨t, 6⟩ ⟨t, 5⟩ ⟨c, 2⟩)
      rest : Builder P ι ℕ ℕ Unit).run st = some st') :
    let M := eighTapeMachine I p mmR qrR
    let half := M.div R (M.ofNat 2)
    let B' := newtonSchulzSign M β (M.mul (M.ofNat 2) R) F
      (M.hermShift A (M.unif (M.div R (M.ofNat (ℓ₀ + d))) (eighTapeSample n d lo).1))
    let Pp' := M.hermScale (M.hermShift B' (M.neg M.one)) (M.ofNat 2)
    let Pm' := M.hermScale (M.negMat (M.hermShift B' M.one)) (M.ofNat 2)
    ∃ σ : St P K C, exec I rest.run σ = some st' ∧
      (∀ q b i, b < s₀ → σ.store.read q b i = st.store.read q b i) ∧
      σ.store.shape = st.store.shape ∧ σ.pos = st.pos ∧
      σ.store.read p t 0 = some half ∧ σ.store.read p t 1 = some (M.neg half) ∧
      σ.store.read p t 6 = some (M.add (M.traceRe Pp') (M.div M.one (M.ofNat 2))) ∧
      pairLayout.Holds σ.store p Pp 0 Pp' ∧ pairLayout.Holds σ.store p Pm 0 Pm' ∧
      st.store.read p c 1 = some (M.ofNat 2) := by
  intro M half B' Pp' Pm'
  simp only [EighArenas.handles, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hlt hge
  obtain ⟨lMa, lUa, lQa, lEa, lSz, lKd, lKp, lLv, lpar, lSu, lc⟩ := hlt
  obtain ⟨gt, gsp, gW, gB, gT, gPp, gPm⟩ := hge
  have dtsp : t = sp → False := fun h => by simp [h] at hnd
  have dtW : t = W → False := fun h => by simp [h] at hnd
  have dtB : t = B → False := fun h => by simp [h] at hnd
  have dtT : t = T → False := fun h => by simp [h] at hnd
  have dtPp : t = Pp → False := fun h => by simp [h] at hnd
  have dtPm : t = Pm → False := fun h => by simp [h] at hnd
  have dspW : sp = W → False := fun h => by simp [h] at hnd
  have dspB : sp = B → False := fun h => by simp [h] at hnd
  have dWB : W = B → False := fun h => by simp [h] at hnd
  have dBT : B = T → False := fun h => by simp [h] at hnd
  have dBPp : B = Pp → False := fun h => by simp [h] at hnd
  have dBPm : B = Pm → False := fun h => by simp [h] at hnd
  have dTPp : T = Pp → False := fun h => by simp [h] at hnd
  have dTPm : T = Pm → False := fun h => by simp [h] at hnd
  have dPpPm : Pp = Pm → False := fun h => by simp [h] at hnd
  have bdl : ∀ {b X i off len : ℕ}, b < s₀ → s₀ ≤ X →
      blockDisjoint (b, i, 1) (X, off, len) = true := fun h1 h2 => by
    simp only [blockDisjoint, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
    exact Or.inl (Or.inl (by omega))
  have bdn : ∀ {b X i i' off len : ℕ}, (b = X → False) →
      blockDisjoint (b, i, i') (X, off, len) = true := fun h => by
    simp only [blockDisjoint, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
    exact Or.inl (Or.inl h)
  obtain ⟨z0, o, -, hl1, -, -⟩ := id hflag
  obtain ⟨hc0, hc1, hc2, hc3⟩ := hc
  have hMone : M.one = o := by
    change (I.sem.lit p 1).getD default = o; rw [hl1, Option.getD_some]
  have hr : ∀ (i : Instr P ℕ ℕ) (b : Builder P ι ℕ ℕ Unit),
      (ins i >>= fun _ => b).run = .seq (.instr i) b.run := fun _ _ => rfl
  have hbo : (eighBlockOff (IExp.const n) (IExp.const d) (IExp.const lo)).eval =
      2 * (n * n) * d + 2 * n * lo := by
    simp [eighBlockOff]
  have hkk : k * k ≤ n * n := Nat.mul_le_mul (by omega) (by omega)
  -- 1. σ = R / fl(2)
  rw [hr] at h
  obtain ⟨aR, z2, v0, s1, haR, hz2, hv0, hw1, h⟩ := eighSignH_inv_bin h
  have eaR : aR = R := by
    change st.store.read p H.Lv (2 * d) = some aR at haR
    rw [hR] at haR; exact (Option.some_inj.mp haR).symm
  subst aR
  change st.store.read p c 1 = some z2 at hz2
  have hl2 : I.sem.lit p ((2 : ℕ) : ℚ) = some z2 := hc1.symm.trans hz2
  have hM2 : M.ofNat 2 = z2 := by
    change (I.sem.lit p ((2 : ℕ) : ℚ)).getD default = z2; rw [hl2, Option.getD_some]
  have hhalf : half = v0 := by
    change (I.sem.bin p .div R (M.ofNat 2)).getD default = v0; rw [hM2, hv0, Option.getD_some]
  refine name_state_node h ?_; clear h; intro σ1 e1s e1p h; simp only at e1s e1p; subst e1s
  have f1 : ∀ q b i, (b ≠ t ∨ i ≠ 0) → σ1.store.read q b i = st.store.read q b i :=
    fun q b i hb => Store.read_of_write_eq_some_of_ne hw1 hb
  -- 2. −σ
  rw [hr] at h
  obtain ⟨a1, v1, s2, ha1, hv1, hw2, h⟩ := eighSignH_inv_un h
  rw [Store.read_of_write_eq_some hw1, Option.some_inj] at ha1
  subst a1
  have hnhalf : M.neg half = v1 := by
    rw [hhalf]; change (I.sem.un p .neg _).getD default = v1; rw [hv1, Option.getD_some]
  refine name_state_node h ?_; clear h; intro σ2 e2s e2p h; simp only at e2s e2p; subst e2s
  have f2 : ∀ q b i, (b ≠ t ∨ i ≠ 1) → σ2.store.read q b i = σ1.store.read q b i :=
    fun q b i hb => Store.read_of_write_eq_some_of_ne hw2 hb
  -- 3. ℓ
  rw [hr] at h
  obtain ⟨v2, s3, hv2, hw3, h⟩ := eighSignH_inv_litIdx h
  have hMl : M.ofNat (ℓ₀ + d) = v2 := by
    change (I.sem.lit p ((ℓ₀ + d : ℕ) : ℚ)).getD default = v2
    change I.sem.lit p ((ℓ₀ + d : ℕ) : ℚ) = some v2 at hv2
    rw [hv2, Option.getD_some]
  refine name_state_node h ?_; clear h; intro σ3 e3s e3p h; simp only at e3s e3p; subst e3s
  have f3 : ∀ q b i, (b ≠ t ∨ i ≠ 2) → σ3.store.read q b i = σ2.store.read q b i :=
    fun q b i hb => Store.read_of_write_eq_some_of_ne hw3 hb
  -- 4. R / ℓ
  rw [hr] at h
  obtain ⟨aR', a2, v3, s4, haR', ha2, hv3, hw4, h⟩ := eighSignH_inv_bin h
  have eaR' : aR' = R := by
    change σ3.store.read p H.Lv (2 * d) = some aR' at haR'
    rw [f3 _ _ _ (Or.inl (by omega)), f2 _ _ _ (Or.inl (by omega)),
      f1 _ _ _ (Or.inl (by omega)), hR] at haR'
    exact (Option.some_inj.mp haR').symm
  subst aR'
  rw [Store.read_of_write_eq_some hw3, Option.some_inj] at ha2
  subst a2
  have hdiv3 : M.div R (M.ofNat (ℓ₀ + d)) = v3 := by
    rw [hMl]; change (I.sem.bin p .div R v2).getD default = v3; rw [hv3, Option.getD_some]
  refine name_state_node h ?_; clear h; intro σ4 e4s e4p h; simp only at e4s e4p; subst e4s
  have f4 : ∀ q b i, (b ≠ t ∨ i ≠ 3) → σ4.store.read q b i = σ3.store.read q b i :=
    fun q b i hb => Store.read_of_write_eq_some_of_ne hw4 hb
  -- 5. the shift c
  rw [hr] at h
  obtain ⟨a3, au, v4, s5, ha3, hau, hv4, hw5, h⟩ := eighSignH_inv_bin h
  rw [Store.read_of_write_eq_some hw4, Option.some_inj] at ha3
  subst a3
  have eau : au = I.tape .uniform (n * d + lo) := by
    change σ4.store.read p Su lo = some au at hau
    rw [f4 _ _ _ (Or.inl (by omega)), f3 _ _ _ (Or.inl (by omega)),
      f2 _ _ _ (Or.inl (by omega)), f1 _ _ _ (Or.inl (by omega)), hSu] at hau
    exact (Option.some_inj.mp hau).symm
  subst au
  have hunif : M.unif (M.div R (M.ofNat (ℓ₀ + d))) (eighTapeSample n d lo).1 = v4 := by
    rw [hdiv3]
    change (I.sem.bin p .mul v3 (I.tape .uniform (n * d + lo))).getD default = v4
    rw [hv4, Option.getD_some]
  refine name_state_node h ?_; clear h; intro σ5 e5s e5p h; simp only at e5s e5p; subst e5s
  have f5 : ∀ q b i, (b ≠ t ∨ i ≠ 4) → σ5.store.read q b i = σ4.store.read q b i :=
    fun q b i hb => Store.read_of_write_eq_some_of_ne hw5 hb
  have lo5 : ∀ q b i, b < s₀ → σ5.store.read q b i = st.store.read q b i := fun q b i hb => by
    rw [f5 _ _ _ (Or.inl (by omega)), f4 _ _ _ (Or.inl (by omega)),
      f3 _ _ _ (Or.inl (by omega)), f2 _ _ _ (Or.inl (by omega)), f1 _ _ _ (Or.inl (by omega))]
  -- 6. W = A − cI
  obtain ⟨σ6, h6, h⟩ := node_bind (fun _ => rfl) h
  obtain ⟨hW6, hf6, hsh6, hp6⟩ := holds_of_exec_zhermShift
    (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    p k (st := σ5) (st' := σ6)
    (by rw [hbo]; exact fun i j t => (lo5 _ _ _ (by omega)).trans (hA i j t))
    (Store.read_of_write_eq_some hw5) (bdn (fun h => by omega)) (bdn dtW) h6
  have f6 : ∀ q b i, (b = W → False) → σ6.store.read q b i = σ5.store.read q b i :=
    fun q b i hb => hf6 q b i (bdn hb)
  -- 7. β
  rw [hr] at h
  obtain ⟨aβ, s7, haβ, hw7, h⟩ := node_inv_copy h
  have eaβ : aβ = β := by
    change σ6.store.read p par 2 = some aβ at haβ
    rw [f6 _ _ _ (fun h => by omega), lo5 _ _ _ lpar, hpar] at haβ
    exact (Option.some_inj.mp haβ).symm
  subst aβ
  refine name_state_node h ?_; clear h; intro σ7 e7s e7p h; simp only at e7s e7p; subst e7s
  have f7 : ∀ q b i, (b ≠ sp ∨ i ≠ 0) → σ7.store.read q b i = σ6.store.read q b i :=
    fun q b i hb => Store.read_of_write_eq_some_of_ne hw7 hb
  -- 8. fl(2) R
  rw [hr] at h
  obtain ⟨a5, a6, vb, s8, ha5, ha6, hvb, hw8, h⟩ := eighSignH_inv_bin h
  have ea5 : a5 = z2 := by
    change σ7.store.read p c 1 = some a5 at ha5
    rw [f7 _ _ _ (Or.inl (by omega)), f6 _ _ _ (fun h => by omega), lo5 _ _ _ lc, hz2] at ha5
    exact (Option.some_inj.mp ha5).symm
  subst a5
  have ea6 : a6 = R := by
    change σ7.store.read p H.Lv (2 * d) = some a6 at ha6
    rw [f7 _ _ _ (Or.inl (by omega)), f6 _ _ _ (fun h => by omega), lo5 _ _ _ lLv, hR] at ha6
    exact (Option.some_inj.mp ha6).symm
  subst a6
  have hmul : M.mul (M.ofNat 2) R = vb := by
    rw [hM2]; change (I.sem.bin p .mul z2 R).getD default = vb; rw [hvb, Option.getD_some]
  refine name_state_node h ?_; clear h; intro σ8 e8s e8p h; simp only at e8s e8p; subst e8s
  have f8 : ∀ q b i, (b ≠ sp ∨ i ≠ 1) → σ8.store.read q b i = σ7.store.read q b i :=
    fun q b i hb => Store.read_of_write_eq_some_of_ne hw8 hb
  have hsh8 : σ8.store.shape = st.store.shape := by
    rw [Store.shape_of_write_eq_some hw8, Store.shape_of_write_eq_some hw7, hsh6,
      Store.shape_of_write_eq_some hw5, Store.shape_of_write_eq_some hw4,
      Store.shape_of_write_eq_some hw3, Store.shape_of_write_eq_some hw2,
      Store.shape_of_write_eq_some hw1]
  -- 9. the sign
  obtain ⟨σ9, h9, h⟩ := node_bind (fun _ => rfl) h
  obtain ⟨hB9, hf9, hsh9, hp9⟩ := holds_of_exec_eighSignBlock
    (toNat := fun x => (I.sem.toNat p x).getD 0) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    hmm p hflag k F (A := W) (ao := 0) (par := sp) (po := 0) (X := B) (xo := 0)
    (st := σ8) (st' := σ9)
    (fun i j t => (f8 _ _ _ (Or.inl (fun h => dspW h.symm))).trans
      ((f7 _ _ _ (Or.inl (fun h => dspW h.symm))).trans (hW6 i j t)))
    (show σ8.store.read p sp 0 = some β from
      (f8 _ _ _ (Or.inr (by omega))).trans (Store.read_of_write_eq_some hw7))
    (show σ8.store.read p sp 1 = some vb from Store.read_of_write_eq_some hw8)
    (bdn (fun h => dWB h.symm)) (bdn (fun h => dspB h.symm))
    ⟨2 * (n * n), by rw [hsh8]; exact hB, by simp only [IExp.eval_zero]; omega⟩ h9
  have f9 : ∀ q b i, (b = B → False) → σ9.store.read q b i = σ8.store.read q b i :=
    fun q b i hb => hf9 q b i (bdn hb)
  have lo9 : ∀ q b i, b < s₀ → σ9.store.read q b i = st.store.read q b i := fun q b i hb => by
    rw [f9 _ _ _ (fun h => by omega), f8 _ _ _ (Or.inl (by omega)),
      f7 _ _ _ (Or.inl (by omega)), f6 _ _ _ (fun h => by omega), lo5 _ _ _ hb]
  have hB' : B' = newtonSchulzSign M β vb F (M.hermShift A v4) := by
    show newtonSchulzSign M β (M.mul (M.ofNat 2) R) F
      (M.hermShift A (M.unif (M.div R (M.ofNat (ℓ₀ + d))) (eighTapeSample n d lo).1)) = _
    rw [hmul, hunif]
  -- 10. T = B + I
  obtain ⟨σ10, h10, h⟩ := node_bind (fun _ => rfl) h
  obtain ⟨hT10, hf10, hsh10, hp10⟩ := holds_of_exec_zhermShift
    (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    p k (st := σ9) (st' := σ10) hB9 (show σ9.store.read p c 3 = _ from (lo9 _ _ _ lc).trans hc3)
    (bdn (fun h => dBT h.symm)) (bdn (fun h => by simp only at h; omega)) h10
  have f10 : ∀ q b i, (b = T → False) → σ10.store.read q b i = σ9.store.read q b i :=
    fun q b i hb => hf10 q b i (bdn hb)
  -- 11. P₊
  obtain ⟨σ11, h11, h⟩ := node_bind (fun _ => rfl) h
  obtain ⟨hPp11, hf11, hsh11, hp11⟩ := holds_of_exec_zhermScale
    (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    p k (st := σ10) (st' := σ11) hT10
    (show σ10.store.read p c 1 = some z2 from
      (f10 _ _ _ (fun h => by omega)).trans ((lo9 _ _ _ lc).trans hz2))
    (bdn (fun h => dTPp h.symm)) (bdn (fun h => by simp only at h; omega)) h11
  have f11 : ∀ q b i, (b = Pp → False) → σ11.store.read q b i = σ10.store.read q b i :=
    fun q b i hb => hf11 q b i (bdn hb)
  -- 12. T = B − I
  obtain ⟨σ12, h12, h⟩ := node_bind (fun _ => rfl) h
  obtain ⟨hT12, hf12, hsh12, hp12⟩ := holds_of_exec_zhermShift
    (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    p k (st := σ11) (st' := σ12)
    (fun i j t => (f11 _ _ _ dBPp).trans ((f10 _ _ _ dBT).trans (hB9 i j t)))
    (show σ11.store.read p c 0 = some o from (f11 _ _ _ (fun h => by omega)).trans
      ((f10 _ _ _ (fun h => by omega)).trans ((lo9 _ _ _ lc).trans (hc0.trans hl1))))
    (bdn (fun h => dBT h.symm)) (bdn (fun h => by simp only at h; omega)) h12
  have f12 : ∀ q b i, (b = T → False) → σ12.store.read q b i = σ11.store.read q b i :=
    fun q b i hb => hf12 q b i (bdn hb)
  -- 13. T = −T
  obtain ⟨σ13, h13, h⟩ := node_bind (fun _ => rfl) h
  obtain ⟨hT13, hf13, hsh13, hp13⟩ := holds_of_exec_zneg
    (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    p k k (st := σ12) (st' := σ13) hT12 (Or.inr ⟨rfl, rfl⟩) h13
  have f13 : ∀ q b i, (b = T → False) → σ13.store.read q b i = σ12.store.read q b i :=
    fun q b i hb => hf13 q b i (bdn hb)
  -- 14. P₋
  obtain ⟨σ14, h14, h⟩ := node_bind (fun _ => rfl) h
  obtain ⟨hPm14, hf14, hsh14, hp14⟩ := holds_of_exec_zhermScale
    (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    p k (st := σ13) (st' := σ14) hT13
    (show σ13.store.read p c 1 = some z2 from (f13 _ _ _ (fun h => by omega)).trans
      ((f12 _ _ _ (fun h => by omega)).trans ((f11 _ _ _ (fun h => by omega)).trans
        ((f10 _ _ _ (fun h => by omega)).trans ((lo9 _ _ _ lc).trans hz2)))))
    (bdn (fun h => dTPm h.symm)) (bdn (fun h => by simp only at h; omega)) h14
  have f14 : ∀ q b i, (b = Pm → False) → σ14.store.read q b i = σ13.store.read q b i :=
    fun q b i hb => hf14 q b i (bdn hb)
  have hPp14 : pairLayout.Holds σ14.store p Pp 0
      ((I.sem.toFloatMachine p (fun x => (I.sem.toNat p x).getD 0) mmR qrR
        (I.sem.tapeUnif p (I.tape .uniform)) (I.sem.tapeNormal p (I.tape .gaussian))).hermScale
        ((I.sem.toFloatMachine p (fun x => (I.sem.toNat p x).getD 0) mmR qrR
          (I.sem.tapeUnif p (I.tape .uniform))
          (I.sem.tapeNormal p (I.tape .gaussian))).hermShift
          (newtonSchulzSign M β vb F (M.hermShift A v4)) (M.neg M.one)) z2) :=
    fun i j t => (f14 _ _ _ dPpPm).trans ((f13 _ _ _ (fun h => dTPp h.symm)).trans
      ((f12 _ _ _ (fun h => dTPp h.symm)).trans (hPp11 i j t)))
  -- 15. the trace
  obtain ⟨σ15, h15, h⟩ := node_bind (fun _ => rfl) h
  obtain ⟨htr15, hf15⟩ := read_of_exec_ztraceRe
    (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    p k (st := σ14) (st' := σ15) hPp14 (bdn dtPp) h15
  obtain ⟨hsh15, hp15⟩ := shape_pos_of_exec_ztraceRe_node p k h15
  have f15 : ∀ q b i, (b ≠ t ∨ i ≠ 5) → σ15.store.read q b i = σ14.store.read q b i := by
    intro q b i hb
    refine hf15 q b i ?_
    simp only [blockDisjoint, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
    change (b ≠ t ∨ i + 1 ≤ 5) ∨ 5 + 1 ≤ i
    omega
  -- 16. t + 1/2
  rw [hr] at h
  obtain ⟨a7, a8, v6, s16, ha7, ha8, hv6, hw16, h⟩ := eighSignH_inv_bin h
  have e : Pp' = M.hermScale (M.hermShift (newtonSchulzSign M β vb F (M.hermShift A v4))
      (M.neg M.one)) z2 := by
    show M.hermScale (M.hermShift B' (M.neg M.one)) (M.ofNat 2) = _
    rw [hB', hM2]
  have e' : Pm' = M.hermScale (M.negMat (M.hermShift (newtonSchulzSign M β vb F
      (M.hermShift A v4)) M.one)) z2 := by
    show M.hermScale (M.negMat (M.hermShift B' M.one)) (M.ofNat 2) = _
    rw [hB', hM2]
  have ea7 : a7 = (M.traceRe Pp') := by
    rw [e]
    exact (Option.some_inj.mp (ha7.symm.trans htr15))
  subst a7
  have ea8 : a8 = M.div M.one (M.ofNat 2) := by
    change σ15.store.read p c 2 = some a8 at ha8
    rw [f15 _ _ _ (Or.inl (by omega)), f14 _ _ _ (fun h => by omega),
      f13 _ _ _ (fun h => by omega), f12 _ _ _ (fun h => by omega),
      f11 _ _ _ (fun h => by omega), f10 _ _ _ (fun h => by omega), lo9 _ _ _ lc, hc2] at ha8
    exact (Option.some_inj.mp ha8).symm
  subst a8
  have f16 : ∀ q b i, (b ≠ t ∨ i ≠ 6) → s16.read q b i = σ15.store.read q b i :=
    fun q b i hb => Store.read_of_write_eq_some_of_ne hw16 hb
  refine ⟨_, h, fun q b i hb => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [hM2]; exact hz2⟩
  · change s16.read q b i = _
    rw [f16 _ _ _ (Or.inl (by omega)), f15 _ _ _ (Or.inl (by omega)),
      f14 _ _ _ (fun h => by omega), f13 _ _ _ (fun h => by omega),
      f12 _ _ _ (fun h => by omega), f11 _ _ _ (fun h => by omega),
      f10 _ _ _ (fun h => by omega), lo9 _ _ _ hb]
  · change s16.shape = _
    rw [Store.shape_of_write_eq_some hw16, hsh15, hsh14, hsh13, hsh12, hsh11, hsh10, hsh9, hsh8]
  · change σ15.pos = st.pos
    rw [hp15, hp14, hp13, hp12, hp11, hp10, hp9, e8p, e7p, hp6, e5p, e4p, e3p, e2p, e1p]
  · change s16.read p t 0 = _
    rw [f16 _ _ _ (Or.inr (by omega)), f15 _ _ _ (Or.inr (by omega)), f14 _ _ _ dtPm,
      f13 _ _ _ dtT, f12 _ _ _ dtT, f11 _ _ _ dtPp, f10 _ _ _ dtT, f9 _ _ _ dtB,
      f8 _ _ _ (Or.inl dtsp), f7 _ _ _ (Or.inl dtsp), f6 _ _ _ dtW,
      f5 _ _ _ (Or.inr (by omega)), f4 _ _ _ (Or.inr (by omega)), f3 _ _ _ (Or.inr (by omega)),
      f2 _ _ _ (Or.inr (by omega)), hhalf]
    exact Store.read_of_write_eq_some hw1
  · change s16.read p t 1 = _
    rw [f16 _ _ _ (Or.inr (by omega)), f15 _ _ _ (Or.inr (by omega)), f14 _ _ _ dtPm,
      f13 _ _ _ dtT, f12 _ _ _ dtT, f11 _ _ _ dtPp, f10 _ _ _ dtT, f9 _ _ _ dtB,
      f8 _ _ _ (Or.inl dtsp), f7 _ _ _ (Or.inl dtsp), f6 _ _ _ dtW,
      f5 _ _ _ (Or.inr (by omega)), f4 _ _ _ (Or.inr (by omega)), f3 _ _ _ (Or.inr (by omega)),
      hnhalf]
    exact Store.read_of_write_eq_some hw2
  · show s16.read p t 6 = some ((I.sem.bin p .add _ _).getD default)
    rw [hv6, Option.getD_some]
    exact Store.read_of_write_eq_some hw16
  · rw [e]
    exact fun i j t' => (f16 _ _ _ (Or.inl (fun h => dtPp h.symm))).trans
      ((f15 _ _ _ (Or.inl (fun h => dtPp h.symm))).trans (hPp14 i j t'))
  · rw [e', hMone]
    exact fun i j t' => (f16 _ _ _ (Or.inl (fun h => dtPm h.symm))).trans
      ((f15 _ _ _ (Or.inl (fun h => dtPm h.symm))).trans (hPm14 i j t'))

omit [Inhabited K] in
/-- A loop of no iterations. -/
private theorem loop_zero_node {e : IExp ℕ} {b : ℕ → Stmt P ι ℕ ℕ} {s s' : St P K C}
    (he : e.eval = 0) (h : exec I (.seq (.loop e b) .skip) s = some s') : s' = s := by
  rw [exec_seq_skip, exec_loop, he] at h
  simp only [List.range_zero, List.foldlM_nil] at h
  exact (Option.some_inj.mp h).symm

omit [Inhabited K] in
/-- A loop of one iteration. -/
private theorem loop_one_node {e : IExp ℕ} {b : ℕ → Stmt P ι ℕ ℕ} {s s' : St P K C}
    (he : e.eval = 1) (h : exec I (.seq (.loop e b) .skip) s = some s') :
    exec I (b 0) s = some s' := by
  rw [exec_seq_skip, exec_loop, he] at h
  simpa [List.range_one] using h

omit [Inhabited K] in
/-- A guarded block, then the rest. -/
private theorem when_bind_node {e : IExp ℕ} {b : Builder P ι ℕ ℕ Unit}
    {f : Unit → Builder P ι ℕ ℕ Unit} {st st' : St P K C}
    (h : exec I (eighWhen e b >>= f).run st = some st') :
    ∃ σ, exec I (.seq (.loop (1 - (1 - e)) fun _ => b.run) .skip) st = some σ ∧
      exec I (f ()).run σ = some st' := node_bind (fun _ => rfl) h

omit [Inhabited K] in
/-- A guarded block. -/
private theorem when_run_node {e : IExp ℕ} {b : Builder P ι ℕ ℕ Unit} {st st' : St P K C}
    (h : exec I (eighWhen e b).run st = some st') :
    exec I (.seq (.loop (1 - (1 - e)) fun _ => b.run) .skip) st = some st' := h

omit [Inhabited K] in
/-- The run of a scoped index binder, inverted. -/
private theorem bindIdx_inv_node {p : P} {x : Cell ℕ ℕ} {bound : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ}
    {st st' : St P K C} (h : exec I (.seq (.bindIdx p x bound body) .skip) st = some st') :
    ∃ v w, st.store.read p x.buf x.idx.eval = some w ∧ I.sem.toNat p w = some v ∧
      exec I (body (min v bound.eval)) { st with cnt := st.cnt + I.charge (.toNat p) } =
        some st' := by
  rw [exec_seq_skip, exec_bindIdx] at h
  obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
  unfold toNatStep at hr
  obtain ⟨w, hw, hr⟩ := Option.bind_eq_some_iff.mp hr
  obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hr
  exact ⟨v, w, hw, hv, h⟩

-- The branch of a node step unfolds its three loops.
set_option maxHeartbeats 4000000 in
/-- The branch of a node step after the index binder: one child or a split, with the frame of the
node's window. -/
private theorem node_branch_holds {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) (p : P) (n d lo k : ℕ) (hk : lo + k ≤ n)
    (hk2 : 2 ≤ k) (H : EighArenas) {Sg c t Pp Pm : ℕ} {st st' : St P K C}
    {A Ppv Pmv : Matrix (Fin k) (Fin k) (K × K)} {half w6 : K} {D : ℕ} (hd : d < D)
    (hH : H.Shaped st.store p n D) (s₀ : ℕ) (hbufs : (H.handles ++ [Sg, Pp, Pm]).Nodup)
    (hlt : ∀ b ∈ H.handles ++ [Sg, c], b < s₀) (hcS : c ∉ H.handles ++ [Sg])
    (hge : s₀ ≤ t ∧ s₀ ≤ Pp ∧ s₀ ≤ Pm) (htPp : t = Pp → False) (htPm : t = Pm → False)
    (htsz : t < st.store.size) (hs₀ : s₀ ≤ st.store.size)
    (hA : pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hPp : pairLayout.Holds st.store p Pp 0 Ppv) (hPm : pairLayout.Holds st.store p Pm 0 Pmv)
    (hSg : ∀ w < 4 * (n * n), st.store.read p Sg w = some (I.tape .gaussian (4 * (n * n) * d + w)))
    (htwo : st.store.read p c 1 = some ((eighTapeMachine I p mmR qrR).ofNat 2))
    (hsq : st.store.read p c 4 = some (I.sem.sqrtHalf p))
    (ht0 : st.store.read p t 0 = some half)
    (ht1 : st.store.read p t 1 = some ((eighTapeMachine I p mmR qrR).neg half))
    (ht6 : st.store.read p t 6 = some w6)
    (h : exec I (Builder.bindIdx p ⟨t, 6⟩ (.const k) fun kp => do
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
            H.Ma H.Qa H.Sz H.Kd H.Kp ⟨c, 1⟩ ⟨t, 0⟩ ⟨t, 1⟩ ⟨c, 4⟩) :
        Builder P ι ℕ ℕ Unit).run st = some st') :
    let M := eighTapeMachine I p mmR qrR
    let kp := min k (M.toNat w6)
    (kp = k → pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * lo)
        (M.hermShift A half) ∧
      st'.store.read p H.Sz (n * (d + 1) + lo) = I.sem.lit p ((k : ℕ) : ℚ) ∧
      st'.store.read p H.Kd (n * d + lo) = I.sem.lit p ((2 : ℕ) : ℚ)) ∧
    (kp = 0 → pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * lo)
        (M.hermShift A (M.neg half)) ∧
      st'.store.read p H.Sz (n * (d + 1) + lo) = I.sem.lit p ((k : ℕ) : ℚ) ∧
      st'.store.read p H.Kd (n * d + lo) = I.sem.lit p ((3 : ℕ) : ℚ)) ∧
    (0 < kp → kp < k →
      let s := eighTapeSample n d lo
      let Qp := deflate M kp Ppv (leadingBlock k (s.2 true))
      let Qm := deflate M (k - kp) Pmv (leadingBlock k (s.2 false))
      pairLayout.Holds st'.store p H.Qa (2 * (n * n) * d + 2 * n * lo) Qp ∧
      pairLayout.Holds st'.store p H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (k * kp)) Qm ∧
      pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * lo)
        (M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Qp) A) Qp) (M.ofNat 2)) half) ∧
      pairLayout.Holds st'.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * (lo + kp))
        (M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Qm) A) Qm) (M.ofNat 2))
          (M.neg half)) ∧
      st'.store.read p H.Sz (n * (d + 1) + lo) = I.sem.lit p ((kp : ℕ) : ℚ) ∧
      st'.store.read p H.Sz (n * (d + 1) + (lo + kp)) = I.sem.lit p ((k - kp : ℕ) : ℚ) ∧
      st'.store.read p H.Kd (n * d + lo) = I.sem.lit p ((4 : ℕ) : ℚ) ∧
      st'.store.read p H.Kp (n * d + lo) = I.sem.lit p ((kp : ℕ) : ℚ)) ∧
    (∀ q b i, b < s₀ → ¬ nodeWin H n d lo k (if 0 < kp ∧ kp < k then lo + kp else lo) b i →
      st'.store.read q b i = st.store.read q b i) ∧
    st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  intro M kp
  simp only [EighArenas.handles, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hlt
  obtain ⟨lMa, lUa, lQa, lEa, lSz, lKd, lKp, lLv, lSg, lc⟩ := hlt
  obtain ⟨gt, gPp, gPm⟩ := hge
  have dMaSz : H.Ma = H.Sz → False := fun h => by simp [EighArenas.handles, h] at hbufs
  have dMaKd : H.Ma = H.Kd → False := fun h => by simp [EighArenas.handles, h] at hbufs
  have dSzKd : H.Sz = H.Kd → False := fun h => by simp [EighArenas.handles, h] at hbufs
  have hn : k ≤ n := by omega
  have hkkn : k * k ≤ n * k := Nat.mul_le_mul_right _ hn
  have hnk : n * k ≤ n * n := Nat.mul_le_mul_left _ hn
  have hbo : (eighBlockOff (IExp.const n) (IExp.const d) (IExp.const lo)).eval =
      2 * (n * n) * d + 2 * n * lo := by simp [eighBlockOff]
  have hbo1 : (eighBlockOff (IExp.const n) (IExp.const d + 1) (IExp.const lo)).eval =
      2 * (n * n) * (d + 1) + 2 * n * lo := by simp [eighBlockOff]
  have hso1 : (eighSlotOff (IExp.const n) (IExp.const d + 1) (IExp.const lo)).eval =
      n * (d + 1) + lo := by simp [eighSlotOff]
  have hso : (eighSlotOff (IExp.const n) (IExp.const d) (IExp.const lo)).eval = n * d + lo := by
    simp [eighSlotOff]
  -- the binder
  obtain ⟨v, w, hw, hv, h⟩ := bindIdx_inv_node h
  rw [show (IExp.const k).eval = k from rfl] at h
  have ew : w = w6 := by
    change st.store.read p t 6 = some w at hw
    rw [ht6] at hw; exact (Option.some_inj.mp hw).symm
  subst w
  have hkp : kp = min v k := by
    change min k ((I.sem.toNat p w6).getD 0) = _
    rw [hv, Option.getD_some, min_comm]
  refine name_state_node h ?_; clear h; intro σ e1 e2 h; simp only at e1 e2
  beta_reduce at h
  obtain ⟨σa, ha, hra⟩ := when_bind_node h
  obtain ⟨σb, hb, hrb⟩ := when_bind_node hra
  have h' := when_run_node hrb
  clear h hra hrb
  -- the frame of a child block
  have hchild : ∀ (sg : Cell ℕ ℕ) (code : ℕ) {σ₁ σ₂ : St P K C}
      {sv : K}, σ₁.store = st.store → sg.buf = t →
      σ₁.store.read p sg.buf sg.idx.eval = some sv →
      exec I (eighChildBlock (ι := ι) p (.const k) H.Ma
        (eighBlockOff (.const n) (.const d) (.const lo))
        (eighBlockOff (.const n) (.const d + 1) (.const lo)) sg
        ⟨H.Sz, eighSlotOff (.const n) (.const d + 1) (.const lo)⟩
        ⟨H.Kd, eighSlotOff (.const n) (.const d) (.const lo)⟩ code).run σ₁ = some σ₂ →
      pairLayout.Holds σ₂.store p H.Ma (2 * (n * n) * (d + 1) + 2 * n * lo) (M.hermShift A sv) ∧
        σ₂.store.read p H.Sz (n * (d + 1) + lo) = I.sem.lit p ((k : ℕ) : ℚ) ∧
        σ₂.store.read p H.Kd (n * d + lo) = I.sem.lit p ((code : ℕ) : ℚ) ∧
        (∀ j q b i, b < s₀ → ¬ nodeWin H n d lo k j b i →
          σ₂.store.read q b i = st.store.read q b i) ∧
        σ₂.store.shape = st.store.shape ∧ σ₂.pos = σ₁.pos := by
    intro sg code σ₁ σ₂ sv hs hsg hsv hex
    obtain ⟨hM, hsz, hkd, hfr, hsh, hps⟩ := holds_of_exec_eighChildBlock
      (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR) (qrR := qrR)
      (unif := I.sem.tapeUnif p (I.tape .uniform))
      (normal := I.sem.tapeNormal p (I.tape .gaussian)) p k code (st := σ₁) (st' := σ₂)
      (by rw [hbo, hs]; exact hA) hsv
      (by
        rw [hbo, hbo1]
        simp only [blockDisjoint, bne_self_eq_false, Bool.false_or, Bool.or_eq_true,
          decide_eq_true_eq]
        right; linarith)
      (by simp only [blockDisjoint, hsg, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
          exact Or.inl (Or.inl (by omega)))
      (by simp only [blockDisjoint, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
          exact Or.inl (Or.inl (fun h => dMaSz h.symm)))
      (by simp only [blockDisjoint, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
          exact Or.inl (Or.inl (fun h => dMaKd h.symm)))
      (by simp only [blockDisjoint, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
          exact Or.inl (Or.inl dSzKd)) hex
    rw [hbo1] at hM
    rw [hso1] at hsz
    rw [hso] at hkd
    refine ⟨hM, hsz, hkd, fun j q b i hb hW => ?_, hsh.trans (by rw [hs]), hps⟩
    simp only [nodeWin, not_or, not_and, not_lt] at hW
    obtain ⟨-, hWM, hWS, hWK⟩ := hW
    rw [hfr q b i ?_ ?_ ?_, hs]
    · rw [hbo1]
      refine bd_of_win_node (lo' := 2 * (n * n) * (d + 1) + 2 * n * lo)
        (hi' := 2 * (n * n) * (d + 1) + 2 * n * (lo + k)) (fun h1 => ?_) le_rfl (by linarith)
      by_contra hc; push_neg at hc
      exact absurd (hWM h1 hc.1) (by omega)
    · rw [hso1]
      refine bd_of_win_node (lo' := n * (d + 1) + lo) (hi' := n * (d + 1) + lo + 1)
        (fun h1 => ?_) le_rfl le_rfl
      have := hWS h1
      by_contra hc; push_neg at hc
      omega
    · rw [hso]
      refine bd_of_win_node (lo' := n * d + lo) (hi' := n * d + lo + 1) (fun h1 => ?_) le_rfl le_rfl
      have := hWK (Or.inl h1)
      omega
  have E1 : ∀ x : ℕ, (1 - (1 - (1 - (IExp.const k - IExp.var x)))).eval =
      1 - (1 - (1 - (k - x))) := fun x => rfl
  have E2 : ∀ x : ℕ, (1 - (1 - (1 - IExp.var x))).eval = 1 - (1 - (1 - x)) := fun x => rfl
  have E3 : ∀ x : ℕ, (1 - (1 - IExp.var x * (IExp.const k - IExp.var x))).eval =
      1 - (1 - x * (k - x)) := fun x => rfl
  have hkv : min v k ≤ k := min_le_right _ _
  rcases Nat.eq_or_lt_of_le hkv with hkk | hlt'
  · -- one child on the positive side
    have h1 := loop_one_node (by rw [E1]; omega) ha
    have e2' := loop_zero_node (by rw [E2]; omega) hb
    have e3' := loop_zero_node (by rw [E3, hkk, Nat.sub_self, Nat.mul_zero]) h'
    subst e2' e3'
    obtain ⟨hM, hsz, hkd, hfr, hsh, hps⟩ := hchild ⟨t, 0⟩ 2 e1 rfl (by rw [e1]; exact ht0) h1
    refine ⟨fun _ => ⟨hM, hsz, hkd⟩, fun h0 => by omega, fun _ h' => by omega,
      fun q b i hb hW => hfr _ q b i hb hW, hsh, hps.trans e2⟩
  rcases Nat.eq_zero_or_pos (min v k) with hz | hpos
  · -- one child on the negative side
    have e1' := loop_zero_node (by rw [E1]; omega) ha
    have h2 := loop_one_node (by rw [E2]; omega) hb
    have e3' := loop_zero_node (by rw [E3, hz, Nat.zero_mul]) h'
    subst e1' e3'
    obtain ⟨hM, hsz, hkd, hfr, hsh, hps⟩ := hchild ⟨t, 1⟩ 3 e1 rfl (by rw [e1]; exact ht1) h2
    refine ⟨fun h' => by omega, fun _ => ⟨hM, hsz, hkd⟩, fun h' _ => by omega,
      fun q b i hb hW => hfr _ q b i hb hW, hsh, hps.trans e2⟩
  · -- a split
    have e1' := loop_zero_node (by rw [E1]; omega) ha
    have e2' := loop_zero_node (by rw [E2]; omega) hb
    subst σa; subst σb
    have hprod : 0 < min v k * (k - min v k) := Nat.mul_pos hpos (by omega)
    have he3 : (1 - (1 - IExp.var (min v k) * (IExp.const k - IExp.var (min v k)))).eval = 1 := by
      rw [E3]; generalize min v k * (k - min v k) = m at hprod ⊢; omega
    have h3 := loop_one_node he3 h'
    have hH' : H.Shaped σ.store p n D := by rw [e1]; exact hH
    obtain ⟨⟨q1, q2, q3, q4, q5, q6, q7, q8⟩, hfr, hsh, hps⟩ :=
      holds_of_exec_eighSplitBlock_frame hmm hqr p n d lo k (min v k) hk hpos hlt'
        (.var (min v k)) rfl H
        (two := ⟨c, 1⟩) (sg := ⟨t, 0⟩) (nsg := ⟨t, 1⟩) (sq := ⟨c, 4⟩) (σ := half)
        (st := σ) (st' := st') (A := A) (Ppm := Ppv) (Pmm := Pmv) hd hH' hbufs
        (by rw [e1]; exact hA) (by rw [e1]; exact hPp) (by rw [e1]; exact hPm)
        (by rw [e1]; exact hSg) (by rw [e1]; exact htwo)
        (by rw [e1]; exact ht0) (by rw [e1]; exact ht1)
        (by
          intro c' hc'
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
          have hcn : c ∉ H.handles ++ [Sg, Pp, Pm] := by
            intro hm
            rw [show H.handles ++ [Sg, Pp, Pm] = (H.handles ++ [Sg]) ++ [Pp, Pm] by simp] at hm
            rcases List.mem_append.mp hm with h | h
            · exact hcS h
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at h; omega
          have htn : t ∉ H.handles ++ [Sg, Pp, Pm] := by
            intro hm
            simp only [EighArenas.handles, List.cons_append, List.nil_append, List.mem_cons,
              List.not_mem_nil, or_false] at hm
            rcases hm with h | h | h | h | h | h | h | h | h | h | h <;>
              first | omega | exact htPp h | exact htPm h
          rcases hc' with rfl | rfl | rfl | rfl
          exacts [hcn, htn, htn, hcn])
        (by rw [e1]; exact hsq)
        h3
    refine ⟨fun h' => by omega, fun h' => by omega, fun _ _ => ?_, fun q b i hb hW => ?_,
      hsh.trans (by rw [e1]), hps.trans e2⟩
    · rw [hkp]
      exact ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩
    · rw [if_pos (by rw [hkp]; exact ⟨hpos, hlt'⟩), hkp] at hW
      rw [hfr q b i hW, e1]

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- The arenas stay allocated under a push. -/
private theorem shaped_push_node {H : EighArenas} {s : Store P K} {p : P} {n D : ℕ}
    (x : P × Array (Option K)) (hH : H.Shaped s p n D) (hlt : ∀ b ∈ H.handles, b < s.size) :
    H.Shaped (s.push x) p n D := by
  obtain ⟨hnd, hMa, hUa, hQa, hEa, hSz, hKd, hKp, hLv⟩ := hH
  simp only [EighArenas.handles, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hlt
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := hlt
  exact ⟨hnd, by rw [Store.getElem?_shape_push_of_lt _ l1]; exact hMa,
    by rw [Store.getElem?_shape_push_of_lt _ l2]; exact hUa,
    by rw [Store.getElem?_shape_push_of_lt _ l3]; exact hQa,
    by rw [Store.getElem?_shape_push_of_lt _ l4]; exact hEa,
    by rw [Store.getElem?_shape_push_of_lt _ l5]; exact hSz,
    by rw [Store.getElem?_shape_push_of_lt _ l6]; exact hKd,
    by rw [Store.getElem?_shape_push_of_lt _ l7]; exact hKp,
    by rw [Store.getElem?_shape_push_of_lt _ l8]; exact hLv⟩

/-- The handles of a split inside a node step are distinct, and the constants are not among the
arenas and the samples. -/
private theorem nodup_scratch_node {H : EighArenas} {par Su Sg c Pp Pm s₀ : ℕ}
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

-- The seven allocations and the branch of a node step.
set_option maxHeartbeats 4000000 in
/-- **The node step computes `NLAlib.eighStep`, with the window it writes**: under the hypotheses
of `NLAlib.holds_of_exec_eighNodeBlock`, its conclusion with the precise frame: every cell outside
the node's basis block at depth $d$, its matrix block and size cells at depth $d + 1$, and its kind
and split cells at depth $d$ (the window of the slots $[lo, lo + k)$) is unchanged. No printed
source. -/
theorem holds_of_exec_eighNodeBlock_frame {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
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
        (eighTapeMachine I p mmR qrR).one) ∧
      st.store.read p c 4 = some (I.sem.sqrtHalf p))
    (h : exec I (eighNodeBlock p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) (.const lo)
      (.const k) par H.Lv Su Sg H.Ma H.Qa H.Sz H.Kd H.Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩).run st =
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
  have hsz : ∀ {b : ℕ} {x : P × ℕ}, st.store.shape[b]? = some x → b < st.store.size :=
    fun h => by simpa [Store.size_shape] using (Array.getElem?_eq_some_iff.mp h).1
  obtain ⟨-, hMa, hUa, hQa, hEa, hSz, hKd, hKp, hLv⟩ := id hH
  obtain ⟨z0, o, -, hl1, -, -⟩ := id hflag
  have hn2 : 0 < 4 * (n * n) := by have : 0 < n := (by omega); positivity
  have lSg := Store.lt_size_of_read_eq_some (hSg 0 hn2)
  have lpar := Store.lt_size_of_read_eq_some hpar
  have lSu := Store.lt_size_of_read_eq_some hSu
  have lc := Store.lt_size_of_read_eq_some (hc.1.trans hl1)
  have hlt : ∀ b ∈ H.handles ++ [par, Su, Sg, c], b < st.store.size := by
    simp only [EighArenas.handles, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro b (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    exacts [hsz hMa, hsz hUa, hsz hQa, hsz hEa, hsz hSz, hsz hKd, hsz hKp, hsz hLv, lpar, lSu,
      lSg, lc]
  have hltH : ∀ b ∈ H.handles, b < st.store.size := fun b hb => hlt b (List.mem_append_left _ hb)
  obtain ⟨hbS, hcS⟩ := nodup_scratch_node (Pp := st.store.size + 5) (Pm := st.store.size + 6)
    hbufs hlt (by omega) (by omega) (by omega)
  -- the allocations
  obtain ⟨s₁, h₁, e₁⟩ := alloc_inv_skip_node h
  obtain ⟨s₂, h₂, e₂⟩ := alloc_inv_node h₁
  obtain ⟨s₃, h₃, e₃⟩ := alloc_inv_node h₂
  obtain ⟨s₄, h₄, e₄⟩ := alloc_inv_node h₃
  obtain ⟨s₅, h₅, e₅⟩ := alloc_inv_node h₄
  obtain ⟨s₆, h₆, e₆⟩ := alloc_inv_node h₅
  obtain ⟨s₇, h₇, e₇⟩ := alloc_inv_node h₆
  clear h h₁ h₂ h₃ h₄ h₅ h₆
  subst e₁ e₂ e₃ e₄ e₅ e₆ e₇
  refine name_state_node h₇ ?_
  clear h₇
  intro σ₇ hσs hσp h₇
  simp only at hσs hσp
  have hrd : ∀ {q : P} {b i : ℕ}, b < st.store.size →
      σ₇.store.read q b i = st.store.read q b i := fun hb => by
    rw [hσs]
    iterate 7 rw [Store.read_push_of_lt (by first | omega | (simp only [Array.size_push]; omega))]
  have hshp : ∀ {b : ℕ}, b < st.store.size → σ₇.store.shape[b]? = st.store.shape[b]? :=
    fun hb => by
      rw [hσs]
      iterate 7 rw [Store.getElem?_shape_push_of_lt _
        (by first | omega | (simp only [Array.size_push]; omega))]
  have hsz₇ : σ₇.store.size = st.store.size + 7 := by rw [hσs]; simp
  have hlt3 : ∀ b ∈ H.handles ++ [par, Su, c], b < st.store.size := fun b hb => by
    rcases List.mem_append.mp hb with hb | hb
    · exact hltH b hb
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl
      exacts [lpar, lSu, lc]
  have S := node_setup_holds hmm p hflag n ℓ₀ F d lo k hk H (par := par) (Su := Su) (c := c)
    (A := A) (R := R) (β := β) st.store.size hlt3 _ _ _ _ _ _ _ (by simp <;> omega)
    (by simp [List.nodup_cons] <;> omega) (by rw [hσs]; simp [Store.shape, Array.getElem?_push, Array.getElem_push])
    (fun i j t => (hrd (hsz hMa)).trans (hA i j t)) ((hrd (hsz hLv)).trans hR)
    ((hrd lpar).trans hpar) ((hrd lSu).trans hSu)
    ⟨(hrd lc).trans hc.1, (hrd lc).trans hc.2.1, (hrd lc).trans hc.2.2.1,
      (hrd lc).trans hc.2.2.2.1⟩ _ (h := h₇)
  obtain ⟨σ, hσ, hlo, hsh, hps, ht0, ht1, ht6, hPp, hPm, htwoM⟩ := S
  have hsz' : σ.store.size = st.store.size + 7 := by
    rw [Store.size_eq_of_shape_eq hsh, hsz₇]
  have hH' : H.Shaped σ.store p n D :=
    ⟨hH.1, by rw [hsh, hshp (hsz hMa)]; exact hMa, by rw [hsh, hshp (hsz hUa)]; exact hUa,
      by rw [hsh, hshp (hsz hQa)]; exact hQa, by rw [hsh, hshp (hsz hEa)]; exact hEa,
      by rw [hsh, hshp (hsz hSz)]; exact hSz, by rw [hsh, hshp (hsz hKd)]; exact hKd,
      by rw [hsh, hshp (hsz hKp)]; exact hKp, by rw [hsh, hshp (hsz hLv)]; exact hLv⟩
  have hlt2 : ∀ b ∈ H.handles ++ [Sg, c], b < st.store.size := fun b hb => by
    rcases List.mem_append.mp hb with hb | hb
    · exact hltH b hb
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      exacts [lSg, lc]
  have Bk := node_branch_holds hmm hqr p n d lo k hk hk2 H (Sg := Sg) (c := c) (st := σ)
    (st' := s₇) (A := A) hd hH' st.store.size
    (nodup_scratch_node hbufs hlt (by simp <;> omega) (by simp <;> omega) (by simp)).1 hlt2 hcS
    (by refine ⟨?_, ?_, ?_⟩ <;> simp <;> omega) (by intro h; simp at h; omega)
    (by intro h; simp at h; omega)
    (by rw [hsz']; simp) (by rw [hsz']; omega)
    (fun i j t => (hlo _ _ _ (hsz hMa)).trans ((hrd (hsz hMa)).trans (hA i j t))) hPp hPm
    (fun w hw => (hlo _ _ _ lSg).trans ((hrd lSg).trans (hSg w hw)))
    ((hlo _ _ _ lc).trans htwoM)
    ((hlo _ _ _ lc).trans ((hrd lc).trans hc.2.2.2.2)) ht0 ht1 ht6 (h := hσ)
  obtain ⟨B1, B2, B3, Bfr, Bsh, Bps⟩ := Bk
  have hs7 : s₇.store.size = st.store.size + 7 := by
    rw [Store.size_eq_of_shape_eq Bsh, hsz']
  have hpop : ∀ {q : P} {b i : ℕ}, b < st.store.size →
      Store.read (Array.pop^[7] s₇.store) q b i = s₇.store.read q b i :=
    fun hb => read_pops_node 7 (by omega)
  refine ⟨?_, fun q b i hW => ?_, ?_, ?_⟩
  · have hRt : M.le R (M.mul ε R₀) = false := hRtest
    unfold eighStep
    dsimp only
    split_ifs with h0 hle h1 h2
    · omega
    · exact absurd hle (by rw [hRt]; decide)
    · obtain ⟨x1, x2, x3⟩ := B1 h1
      exact ⟨fun i j t => (hpop (hsz hMa)).trans (x1 i j t), (hpop (hsz hSz)).trans x2,
        (hpop (hsz hKd)).trans x3⟩
    · obtain ⟨x1, x2, x3⟩ := B2 h2
      exact ⟨fun i j t => (hpop (hsz hMa)).trans (x1 i j t), (hpop (hsz hSz)).trans x2,
        (hpop (hsz hKd)).trans x3⟩
    · obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8⟩ := 
        B3 (Nat.pos_of_ne_zero h2) (lt_of_le_of_ne (min_le_left _ _) h1)
      exact ⟨fun i j t => (hpop (hsz hQa)).trans (x1 i j t),
        fun i j t => (hpop (hsz hQa)).trans (x2 i j t),
        fun i j t => (hpop (hsz hMa)).trans (x3 i j t),
        fun i j t => (hpop (hsz hMa)).trans (x4 i j t),
        (hpop (hsz hSz)).trans x5, (hpop (hsz hSz)).trans x6, (hpop (hsz hKd)).trans x7,
        (hpop (hsz hKp)).trans x8⟩
  · by_cases hb : b < st.store.size
    · refine (hpop hb).trans ((Bfr q b i hb ?_).trans ((hlo q b i hb).trans (hrd hb)))
      have hRt : M.le R (M.mul ε R₀) = false := hRtest
      intro hN
      apply hW
      unfold nodeWin at hN
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
    · have hsz'' : (Array.pop^[7] s₇.store).size = st.store.size := by
        simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, Array.size_pop,
          hs7]
        omega
      exact (show Store.read (Array.pop^[7] s₇.store) q b i = none from
        Store.read_eq_none_of_size_le (by omega)).trans
          (Store.read_eq_none_of_size_le (by omega)).symm
  · change Store.shape (Array.pop (Array.pop (Array.pop (Array.pop (Array.pop (Array.pop
      (Array.pop s₇.store))))))) = _
    simp only [Store.shape_pop, Bsh, hsh, hσs]
    simp [Store.shape]
  · exact Bps.trans (hps.trans hσp)


/-- **The node step computes `NLAlib.eighStep`**: let the kernels of `I` be the routines `mmR`,
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
        (eighTapeMachine I p mmR qrR).one) ∧
      st.store.read p c 4 = some (I.sem.sqrtHalf p))
    (h : exec I (eighNodeBlock p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) (.const lo)
      (.const k) par H.Lv Su Sg H.Ma H.Qa H.Sz H.Kd H.Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩).run st =
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
  obtain ⟨hstep, hfr, hsh, hps⟩ := holds_of_exec_eighNodeBlock_frame hmm hqr p hflag n ℓ₀ F d lo
    k hk hk2 H hd hH hbufs hA hR hRtest hpar hSu hSg hc h
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

omit [Inhabited K] in
/-- A goal on a state with a new store and count, by a named state. -/
private theorem ex_name_node {X : Stmt P ι ℕ ℕ} {s : St P K C} {s1 : Store P K} {c : C}
    (h : ∀ σ : St P K C, σ.store = s1 → σ.pos = s.pos → ∃ st', exec I X σ = some st') :
    ∃ st', exec I X { s with store := s1, cnt := c } = some st' := h _ rfl rfl

omit [Inhabited K] in
/-- A kernel block, then the rest, succeeds if both do. -/
private theorem ex_bind_node {b : Builder P ι ℕ ℕ Unit} {X : Stmt P ι ℕ ℕ}
    (hb : ∀ k, ContT.run b k = .seq X (k ())) {f : Unit → Builder P ι ℕ ℕ Unit} {st : St P K C}
    (h₁ : ∃ σ, exec I b.run st = some σ)
    (h₂ : ∀ σ, exec I b.run st = some σ → ∃ st', exec I (f ()).run σ = some st') :
    ∃ st', exec I (b >>= f).run st = some st' := by
  obtain ⟨σ, hσ⟩ := h₁
  rw [exec_run_bind I hb, hσ, Option.bind_some]
  exact h₂ σ hσ

/-- A real trace succeeds when its matrix is stored and its destination can be written. -/
private theorem exists_exec_ztraceRe_node {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (n : ℕ) {X : ℕ} {xo : IExp ℕ}
    {dst : Cell ℕ ℕ} {st : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)}
    (hA : pairLayout.Holds st.store p X xo.eval A) (hdX : dst.buf ≠ X)
    (hdst : ∃ s, st.store.write p dst.buf dst.idx.eval default = some s) :
    ∃ st', exec I (ztraceRe (ι := ι) p (.const n) X xo dst).run st = some st' := by
  change ∃ st', exec I (.seq (.named _ _ (.seq (.instr _) (.seq (.loop _ _) .skip))) .skip) st =
    some st'
  rw [exec_seq_skip, exec_named]
  obtain ⟨z0, hz0⟩ := hsem.lit_ok p 0 trivial
  obtain ⟨s0, hs0⟩ := hdst
  obtain ⟨s1, hs1⟩ := Store.exists_write_eq_some_of_write_eq_some hs0 z0
  rw [exec_seq_instr_lit I hz0 hs1, exec_seq_skip]
  refine (exists_exec_loop_eq_some_of_forall (I := I)
    (fun _ s => (∃ v, s.store.read p dst.buf dst.idx.eval = some v) ∧
      ∀ q b i, b ≠ dst.buf → s.store.read q b i = st.store.read q b i)
    ⟨⟨z0, Store.read_of_write_eq_some hs1⟩,
      fun q b i hb => Store.read_of_write_eq_some_of_ne hs1 (Or.inl hb)⟩ ?_).imp
    fun _ h => h.1
  rintro i hi s ⟨⟨v, hv⟩, hfr⟩
  simp only [IExp.eval_const] at hi
  have hx := hA ⟨i, hi⟩ ⟨i, hi⟩ ⟨0, two_pos⟩
  obtain ⟨z, hz⟩ := hsem.bin_ok p .add v (pairLayout.put (A ⟨i, hi⟩ ⟨i, hi⟩) ⟨0, two_pos⟩) trivial
    (fun h => nomatch h) trivial
  obtain ⟨s', hs'⟩ := Store.exists_write_eq_some_of_read_eq_some (v := z) hv
  change ∃ st', exec I (.seq (.instr (.bin p .add dst dst
    ⟨X, xo + zidx (.const n) (.var i) (.var i)⟩)) .skip) s = some st' ∧ _
  rw [exec_seq_instr_bin I hv (by
      rw [hfr _ _ _ (Ne.symm hdX)]
      simpa [zidx, show pairLayout.width = 2 from rfl] using hx) hz hs', exec_skip]
  exact ⟨_, rfl, ⟨z, Store.read_of_write_eq_some hs'⟩, fun q b i' hb =>
    (Store.read_of_write_eq_some_of_ne hs' (Or.inl hb)).trans (hfr q b i' hb)⟩

/-- A child block succeeds. -/
private theorem child_exists_node {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (n d lo k : ℕ) (hk : lo + k ≤ n)
    (hk2 : 2 ≤ k) {D : ℕ} (hd : d < D) (H : EighArenas) {sg : Cell ℕ ℕ} (code : ℕ)
    {st : St P K C} {A : Matrix (Fin k) (Fin k) (K × K)} (hH : H.Shaped st.store p n D)
    (hA : pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hsg : ∃ v, st.store.read p sg.buf sg.idx.eval = some v) (hsgM : sg.buf ≠ H.Ma) :
    ∃ st', exec I (eighChildBlock (ι := ι) p (.const k) H.Ma
        (eighBlockOff (.const n) (.const d) (.const lo))
        (eighBlockOff (.const n) (.const d + 1) (.const lo)) sg
        ⟨H.Sz, eighSlotOff (.const n) (.const d + 1) (.const lo)⟩
        ⟨H.Kd, eighSlotOff (.const n) (.const d) (.const lo)⟩ code).run st = some st' := by
  obtain ⟨-, hMa, -, -, -, hSz, hKd, -, -⟩ := hH
  have hr : ∀ (i : Instr P ℕ ℕ) (b : Builder P ι ℕ ℕ Unit),
      (ins i >>= fun _ => b).run = .seq (.instr i) b.run := fun _ _ => rfl
  have hkn : k ≤ n := by omega
  have hkk : k * k ≤ n * k := Nat.mul_le_mul_right _ hkn
  have hlok : n * lo + n * k ≤ n * n := by rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ hk
  have hdD : n * n * (d + 1) + n * n ≤ n * n * (D + 1) := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
  obtain ⟨cv, hcv⟩ := hsg
  have hXY : blockDisjoint (H.Ma, (eighBlockOff (.const n) (.const d + 1) (.const lo)).eval,
      2 * (k * k)) (H.Ma, (eighBlockOff (.const n) (.const d) (.const lo)).eval, 2 * (k * k)) =
      true := by
    simp only [blockDisjoint, eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const,
      IExp.eval_ofNat, IExp.eval_one, bne_self_eq_false, Bool.false_or, Bool.or_eq_true,
          decide_eq_true_eq]
    right
    have e1 : 2 * (n * n) * (d + 1) = 2 * (n * n) * d + 2 * (n * n) := by ring
    have hkk2 : k * k ≤ n * n := Nat.mul_le_mul hkn hkn
    exact decide_eq_true (by linarith)
  have hcY : blockDisjoint (sg.buf, sg.idx.eval, 1)
      (H.Ma, (eighBlockOff (.const n) (.const d + 1) (.const lo)).eval, 2 * (k * k)) = true := by
    simp [blockDisjoint, hsgM]
  have hAm : pairLayout.Holds st.store p H.Ma (eighBlockOff (.const n) (.const d) (.const lo)).eval
      A := by
    simp only [eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat]
    exact hA
  have hY : ∃ len, st.store.shape[H.Ma]? = some (p, len) ∧
      (eighBlockOff (.const n) (.const d + 1) (.const lo)).eval + 2 * (k * k) ≤ len :=
    ⟨_, hMa, by
      simp only [eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat,
        IExp.eval_one]
      linarith⟩
  refine ex_bind_node (fun _ => rfl)
    (exists_exec_zhermShift (I := I) p k (st := st) hAm hcv hXY hcY hsem hY) fun σ hσ => ?_
  obtain ⟨-, -, hsh, -⟩ := holds_of_exec_zhermShift (toNat := fun _ => 0)
    (mmR := @fun _ _ _ _ _ => Matrix.of fun _ _ => default)
    (qrR := @fun _ _ X => (Matrix.of fun _ _ => default, X)) (unif := fun x (_ : Unit) => x)
    (normal := fun (_ : Unit) => ((default : K), (default : K))) p k hAm hcv hXY hcY hσ
  obtain ⟨v1, hv1⟩ := hsem.lit_ok p ((IExp.const k).eval : ℚ) trivial
  obtain ⟨s1, hs1⟩ := Store.exists_write_eq_some_of_getElem?_shape (s := σ.store) v1
    (by rw [hsh]; exact hSz)
    (show (eighSlotOff (.const n) (.const d + 1) (.const lo)).eval < n * (D + 1) + 1 by
      simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_one]
      have : n * (d + 1) + n ≤ n * (D + 1) := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
      omega)
  rw [hr, exec_seq_instr_litIdx I hv1 hs1]
  obtain ⟨v2, hv2⟩ := hsem.lit_ok p ((IExp.const code).eval : ℚ) trivial
  obtain ⟨s2, hs2⟩ := Store.exists_write_eq_some_of_getElem?_shape (s := s1) v2
    (by rw [Store.shape_of_write_eq_some hs1, hsh]; exact hKd)
    (show (eighSlotOff (.const n) (.const d) (.const lo)).eval < n * D by
      simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const]
      have : n * d + n ≤ n * D := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hd
      omega)
  exact ⟨_, (exec_seq_instr_litIdx I hv2 hs2).trans (exec_skip I _)⟩

omit [Inhabited K] in
/-- A goal on a state with a new count, by a named state. -/
private theorem ex_cnt_node {X : Stmt P ι ℕ ℕ} {s : St P K C} {c : C}
    (h : ∀ σ : St P K C, σ.store = s.store → ∃ st', exec I X σ = some st') :
    ∃ st', exec I X { s with cnt := c } = some st' := h _ rfl

omit [Inhabited K] in
/-- A guarded block of no iterations, then the rest. -/
private theorem when_zero_ex_node {e : IExp ℕ} {b : Builder P ι ℕ ℕ Unit}
    {f : Unit → Builder P ι ℕ ℕ Unit} {s : St P K C} (he : (1 - (1 - e)).eval = 0) :
    exec I (eighWhen e b >>= f).run s = exec I (f ()).run s := by
  rw [exec_run_bind I (b := eighWhen e b) (fun _ => rfl)]
  change (exec I (.seq (.loop _ _) .skip) s).bind _ = _
  rw [exec_seq_skip, exec_loop, he]
  rfl

omit [Inhabited K] in
/-- A last guarded block of no iterations. -/
private theorem when_last_zero_ex_node {e : IExp ℕ} {b : Builder P ι ℕ ℕ Unit} {s : St P K C}
    (he : (1 - (1 - e)).eval = 0) : exec I (eighWhen e b).run s = some s := by
  change exec I (.seq (.loop _ _) .skip) s = _
  rw [exec_seq_skip, exec_loop, he]
  rfl

omit [Inhabited K] in
/-- A guarded block of one iteration, then the rest. -/
private theorem when_one_ex_node {e : IExp ℕ} {b : Builder P ι ℕ ℕ Unit}
    {f : Unit → Builder P ι ℕ ℕ Unit} {s : St P K C} (he : (1 - (1 - e)).eval = 1) :
    exec I (eighWhen e b >>= f).run s = (exec I b.run s).bind (exec I (f ()).run) := by
  rw [exec_run_bind I (b := eighWhen e b) (fun _ => rfl)]
  change (exec I (.seq (.loop _ _) .skip) s).bind _ = _
  rw [exec_seq_skip, exec_loop, he]
  simp [List.range_one]

omit [Inhabited K] in
/-- A last guarded block of one iteration. -/
private theorem when_last_one_ex_node {e : IExp ℕ} {b : Builder P ι ℕ ℕ Unit} {s : St P K C}
    (he : (1 - (1 - e)).eval = 1) : exec I (eighWhen e b).run s = exec I b.run s := by
  change exec I (.seq (.loop _ _) .skip) s = _
  rw [exec_seq_skip, exec_loop, he]
  simp [List.range_one]

-- The branch unfolds its three loops.
set_option maxHeartbeats 4000000 in
/-- The branch of a node step after the index binder succeeds. -/
private theorem node_branch_exists {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hlit : IsExactIntLit dec I.sem 2)
    (htn : IsExactToNat dec I.sem) (p : P) (hu : u p < 1) (n d lo k : ℕ) (hk : lo + k ≤ n)
    (hk2 : 2 ≤ k) (H : EighArenas) {Sg c t Pp Pm : ℕ} {st : St P K C}
    {A Ppv Pmv : Matrix (Fin k) (Fin k) (K × K)} {σ0 : K} {D : ℕ} (hd : d < D)
    (hH : H.Shaped st.store p n D) (hbufs : (H.handles ++ [Sg, Pp, Pm]).Nodup)
    (hcS : c ∉ H.handles ++ [Sg, Pp, Pm]) (htS : t ∉ H.handles ++ [Sg, Pp, Pm])
    (hA : pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hPp : pairLayout.Holds st.store p Pp 0 Ppv) (hPm : pairLayout.Holds st.store p Pm 0 Pmv)
    (hSg : ∀ w < 4 * (n * n), ∃ v, st.store.read p Sg w = some v)
    (htwo : st.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ))
    (hsq : st.store.read p c 4 = some (I.sem.sqrtHalf p))
    (ht0 : st.store.read p t 0 = some σ0)
    (ht1 : st.store.read p t 1 = some ((eighTapeMachine I p mmR qrR).neg σ0))
    (ht6 : ∃ v, st.store.read p t 6 = some v) :
    ∃ st', exec I (Builder.bindIdx p ⟨t, 6⟩ (.const k) fun kp => do
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
            H.Ma H.Qa H.Sz H.Kd H.Kp ⟨c, 1⟩ ⟨t, 0⟩ ⟨t, 1⟩ ⟨c, 4⟩) :
        Builder P ι ℕ ℕ Unit).run st = some st' := by
  have htM : t ≠ H.Ma := fun h => htS (by simp [EighArenas.handles, h])
  change ∃ st', exec I (.seq (.bindIdx p ⟨t, 6⟩ (.const k) _) .skip) st = some st'
  rw [exec_seq_skip, exec_bindIdx]
  obtain ⟨w6, hw6⟩ := ht6
  have hts : toNatStep I p ⟨t, 6⟩ st =
      some (⌊dec p w6⌋₊, { st with cnt := st.cnt + I.charge (.toNat p) }) := by
    unfold toNatStep
    rw [show st.store.read p (⟨t, 6⟩ : Cell ℕ ℕ).buf (⟨t, 6⟩ : Cell ℕ ℕ).idx.eval = some w6
      from hw6, Option.bind_some, htn p w6, Option.map_some]
  rw [hts, Option.bind_some]
  refine ex_cnt_node fun S hS => ?_
  beta_reduce
  generalize hx : min ⌊dec p w6⌋₊ (IExp.const k).eval = x
  have hxk : x ≤ k := by rw [← hx]; exact min_le_right _ _
  have hHS : H.Shaped S.store p n D := by rw [hS]; exact hH
  have hAS : pairLayout.Holds S.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A := by rw [hS]; exact
      hA
  have ev1 : (1 - (1 - (1 - (IExp.const k - IExp.var x)) : IExp ℕ)).eval = 1 - (1 - (1 - (k - x)))
      :=
    rfl
  have ev2 : (1 - (1 - (1 - IExp.var x)) : IExp ℕ).eval = 1 - (1 - (1 - x)) := rfl
  have ev3 : (1 - (1 - (IExp.var x * (IExp.const k - IExp.var x))) : IExp ℕ).eval =
      1 - (1 - x * (k - x)) := rfl
  by_cases h1 : x = k
  · subst h1
    have e1 : (1 - (1 - (1 - (IExp.const x - IExp.var x)) : IExp ℕ)).eval = 1 := by
      rw [ev1]; omega
    have e2 : (1 - (1 - (1 - IExp.var x)) : IExp ℕ).eval = 0 := by rw [ev2]; omega
    have e3 : (1 - (1 - (IExp.var x * (IExp.const x - IExp.var x))) : IExp ℕ).eval = 0 := by
      rw [ev3, Nat.sub_self, Nat.mul_zero]
    rw [when_one_ex_node e1]
    obtain ⟨σc, hc⟩ := child_exists_node (I := I) hsem p n d lo x hk hk2 hd H (sg := ⟨t, 0⟩) 2 hHS
        hAS
      ⟨σ0, by rw [hS]; exact ht0⟩ htM
    rw [hc, Option.bind_some, when_zero_ex_node e2, when_last_zero_ex_node e3]
    exact ⟨_, rfl⟩
  by_cases h0 : x = 0
  · subst h0
    have e1 : (1 - (1 - (1 - (IExp.const k - IExp.var 0)) : IExp ℕ)).eval = 0 := by
      rw [ev1]; omega
    have e2 : (1 - (1 - (1 - IExp.var 0)) : IExp ℕ).eval = 1 := by rw [ev2]
    have e3 : (1 - (1 - (IExp.var 0 * (IExp.const k - IExp.var 0))) : IExp ℕ).eval = 0 := by
      rw [ev3, Nat.zero_mul]
    rw [when_zero_ex_node e1, when_one_ex_node e2]
    obtain ⟨σc, hc⟩ := child_exists_node (I := I) hsem p n d lo k hk hk2 hd H (sg := ⟨t, 1⟩) 3 hHS
        hAS
      ⟨_, by rw [hS]; exact ht1⟩ htM
    rw [hc, Option.bind_some, when_last_zero_ex_node e3]
    exact ⟨_, rfl⟩
  have hpos : 1 ≤ x * (k - x) := Nat.mul_pos (by omega) (by omega)
  have e1 : (1 - (1 - (1 - (IExp.const k - IExp.var x)) : IExp ℕ)).eval = 0 := by
    rw [ev1]; omega
  have e2 : (1 - (1 - (1 - IExp.var x)) : IExp ℕ).eval = 0 := by rw [ev2]; omega
  have e3 : (1 - (1 - (IExp.var x * (IExp.const k - IExp.var x))) : IExp ℕ).eval = 1 := by
    rw [ev3]; omega
  rw [when_zero_ex_node e1, when_zero_ex_node e2, when_last_one_ex_node e3]
  refine exists_exec_eighSplitBlock_ex hmm hqr hsem hlit p hu n d lo k x hk (by omega) (by omega)
    (.var x) rfl H (two := ⟨c, 1⟩) (sg := ⟨t, 0⟩) (nsg := ⟨t, 1⟩) (sq := ⟨c, 4⟩)
    hd hHS hbufs hAS (by rw [hS]; exact hPp) (by rw [hS]; exact hPm)
    (by rw [hS]; exact hSg) (by rw [hS]; exact htwo)
    (by rw [hS]; exact ht0) (by rw [hS]; exact ht1) ?_ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hcS, htS, htS, hcS⟩
  · rw [hS]
    exact hsq

omit [Inhabited K] in
/-- A goal on a state, by a named state. -/
private theorem ex_gen_node {X : Stmt P ι ℕ ℕ} {s : St P K C}
    (h : ∀ σ : St P K C, σ = s → ∃ st', exec I X σ = some st') :
    ∃ st', exec I X s = some st' := h s rfl

-- The set-up runs sixteen steps.
set_option maxHeartbeats 4000000 in
/-- The set-up of a node step, up to the index binder, succeeds; only scratch buffers (at handles
from `s₀`) are written. -/
private theorem node_setup_exists {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    {u : P → ℝ} {dec : P → K → ℝ} (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hlit : IsExactIntLit dec I.sem 2) (p : P) (hu : u p < 1) (n ℓ₀ F d lo k : ℕ)
    (hk : lo + k ≤ n) (hk2 : 2 ≤ k) (hℓ : 1 ≤ ℓ₀ + d) (H : EighArenas) {par Su c : ℕ}
    {st : St P K C} {A : Matrix (Fin k) (Fin k) (K × K)} {R : K}
    (s₀ : ℕ) (hlt : ∀ b ∈ H.handles ++ [par, Su, c], b < s₀)
    (t sp W B T Pp Pm : ℕ) (hge : ∀ X ∈ [t, sp, W, B, T, Pp, Pm], s₀ ≤ X)
    (hnd : [t, sp, W, B, T, Pp, Pm].Nodup)
    (ht : st.store.shape[t]? = some (p, 7)) (hsp : st.store.shape[sp]? = some (p, 2))
    (hscr : ∀ X ∈ [W, B, T, Pp, Pm], st.store.shape[X]? = some (p, 2 * (n * n)))
    (hA : pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hR : st.store.read p H.Lv (2 * d) = some R) (hR0 : 0 < dec p R)
    (hpar : ∃ β, st.store.read p par 2 = some β)
    (hSu : ∃ v, st.store.read p Su lo = some v)
    (hc0 : st.store.read p c 0 = I.sem.lit p 1)
    (hc1 : st.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ))
    (hc2 : ∃ v, st.store.read p c 2 = some v) (hc3 : ∃ v, st.store.read p c 3 = some v)
    (rest : Builder P ι ℕ ℕ Unit)
    (hrest : ∀ σ : St P K C, (∀ q b i, b < s₀ → σ.store.read q b i = st.store.read q b i) →
      σ.store.shape = st.store.shape →
      (∃ v, σ.store.read p t 0 = some v ∧
        σ.store.read p t 1 = some ((eighTapeMachine I p mmR qrR).neg v)) →
      (∃ v, σ.store.read p t 6 = some v) →
      (∃ Q : Matrix (Fin k) (Fin k) (K × K), pairLayout.Holds σ.store p Pp 0 Q) →
      (∃ Q : Matrix (Fin k) (Fin k) (K × K), pairLayout.Holds σ.store p Pm 0 Q) →
      ∃ st', exec I rest.run σ = some st') :
    ∃ st', exec I (do
      ins (.bin p .div ⟨t, 0⟩ ⟨H.Lv, 2 * .const d⟩ ⟨c, 1⟩)
      ins (.un p .neg ⟨t, 1⟩ ⟨t, 0⟩)
      ins (.litIdx p ⟨t, 2⟩ (.const ℓ₀ + .const d))
      ins (.bin p .div ⟨t, 3⟩ ⟨H.Lv, 2 * .const d⟩ ⟨t, 2⟩)
      ins (.bin p .mul ⟨t, 4⟩ ⟨t, 3⟩ ⟨Su, .const lo⟩)
      zhermShift p (.const k) H.Ma (eighBlockOff (.const n) (.const d) (.const lo)) ⟨t, 4⟩ W 0
      ins (.copy p ⟨sp, 0⟩ ⟨par, 2⟩)
      ins (.bin p .mul ⟨sp, 1⟩ ⟨c, 1⟩ ⟨H.Lv, 2 * .const d⟩)
      eighSignBlock p mm (.const k) (.const F) W 0 sp 0 B 0
      zhermShift p (.const k) B 0 ⟨c, 3⟩ T 0
      zhermScale p (.const k) T 0 ⟨c, 1⟩ Pp 0
      zhermShift p (.const k) B 0 ⟨c, 0⟩ T 0
      zneg p (.const k) (.const k) T 0 T 0
      zhermScale p (.const k) T 0 ⟨c, 1⟩ Pm 0
      ztraceRe p (.const k) Pp 0 ⟨t, 5⟩
      ins (.bin p .add ⟨t, 6⟩ ⟨t, 5⟩ ⟨c, 2⟩)
      rest : Builder P ι ℕ ℕ Unit).run st = some st' := by
  simp only [EighArenas.handles, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hlt hge hscr
  obtain ⟨lMa, lUa, lQa, lEa, lSz, lKd, lKp, lLv, lpar, lSu, lc⟩ := hlt
  obtain ⟨gt, gsp, gW, gB, gT, gPp, gPm⟩ := hge
  obtain ⟨hWs, hBs, hTs, hPps, hPms⟩ := hscr
  have dtsp : t = sp → False := fun h => by simp [h] at hnd
  have dtW : t = W → False := fun h => by simp [h] at hnd
  have dtB : t = B → False := fun h => by simp [h] at hnd
  have dtT : t = T → False := fun h => by simp [h] at hnd
  have dtPp : t = Pp → False := fun h => by simp [h] at hnd
  have dtPm : t = Pm → False := fun h => by simp [h] at hnd
  have dspW : sp = W → False := fun h => by simp [h] at hnd
  have dspB : sp = B → False := fun h => by simp [h] at hnd
  have dWB : W = B → False := fun h => by simp [h] at hnd
  have dBT : B = T → False := fun h => by simp [h] at hnd
  have dBPp : B = Pp → False := fun h => by simp [h] at hnd
  have dTPp : T = Pp → False := fun h => by simp [h] at hnd
  have dTPm : T = Pm → False := fun h => by simp [h] at hnd
  have dPpPm : Pp = Pm → False := fun h => by simp [h] at hnd
  have bdn : ∀ {b X i i' off len : ℕ}, (b = X → False) →
      blockDisjoint (b, i, i') (X, off, len) = true := fun h => by
    simp only [blockDisjoint, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
    exact Or.inl (Or.inl h)
  have hR' : st.store.read p H.Lv (2 * IExp.const d : IExp ℕ).eval = some R := by
    simpa using hR
  have hr : ∀ (i : Instr P ℕ ℕ) (b : Builder P ι ℕ ℕ Unit),
      (ins i >>= fun _ => b).run = .seq (.instr i) b.run := fun _ _ => rfl
  have hbo : (eighBlockOff (IExp.const n) (IExp.const d) (IExp.const lo)).eval =
      2 * (n * n) * d + 2 * n * lo := by
    simp [eighBlockOff]
  have hkk : k * k ≤ n * n := Nat.mul_le_mul (by omega) (by omega)
  have hlit1 : IsExactIntLit dec I.sem 1 := fun q m hm => hlit q m (by omega)
  have hflag : I.sem.DecidesFlags p := by
    obtain ⟨z, hz, hdz⟩ := hlit p 0 (Nat.zero_le _)
    obtain ⟨o, ho, hdo⟩ := hlit p 1 (by norm_num)
    simp only [Nat.cast_zero, Nat.cast_one] at hz hdz ho hdo
    refine ⟨z, o, hz, ho, ?_, ?_⟩
    · rw [hsem.cmp_eq p z o, hdz, hdo]
      norm_num
    · rw [hsem.cmp_eq p o o]
      simp
  obtain ⟨z2, hz2, hdz2⟩ := hlit p 2 le_rfl
  have hc1' : st.store.read p c 1 = some z2 := hc1.trans hz2
  have hz20 : dec p z2 ≠ 0 := by rw [hdz2]; norm_num
  obtain ⟨o1, ho1⟩ := hsem.lit_ok p 1 trivial
  have hc0' : st.store.read p c 0 = some o1 := hc0.trans ho1
  obtain ⟨β, hβ⟩ := hpar
  obtain ⟨au, hau⟩ := hSu
  obtain ⟨c2v, hc2v⟩ := hc2
  obtain ⟨c3v, hc3v⟩ := hc3
  -- 1. σ = R / fl(2)
  obtain ⟨v0, hv0⟩ := hsem.bin_ok p .div R z2 trivial (fun _ => hz20) trivial
  obtain ⟨s1, hw1⟩ := Store.exists_write_eq_some_of_getElem?_shape (s := st.store) v0 ht
    (show 0 < 7 by norm_num)
  rw [hr, exec_seq_instr_bin I (x := ⟨H.Lv, (2 * IExp.const d : IExp ℕ)⟩) (y := ⟨c, 1⟩) (dst :=
      ⟨t, 0⟩) hR' hc1'
    hv0 hw1]
  refine ex_name_node fun σ1 e1 _ => ?_
  subst e1
  have sh1 : σ1.store.shape = st.store.shape := Store.shape_of_write_eq_some hw1
  have f1 : ∀ q b i, (b ≠ t ∨ i ≠ 0) → σ1.store.read q b i = st.store.read q b i :=
    fun q b i hb => Store.read_of_write_eq_some_of_ne hw1 hb
  -- 2. −σ
  obtain ⟨v1, hv1, -⟩ := hsem.neg p v0
  obtain ⟨s2, hw2⟩ := Store.exists_write_eq_some_of_getElem?_shape (s := σ1.store) v1
    (sh1 ▸ ht) (show 1 < 7 by norm_num)
  rw [hr, exec_seq_instr_un I (x := ⟨t, 0⟩) (dst := ⟨t, 1⟩) (Store.read_of_write_eq_some hw1) hv1
    hw2]
  refine ex_name_node fun σ2 e2 _ => ?_
  subst e2
  have hMneg : (eighTapeMachine I p mmR qrR).neg v0 = v1 := by
    change (I.sem.un p .neg v0).getD default = v1; rw [hv1, Option.getD_some]
  have sh2 : σ2.store.shape = st.store.shape := (Store.shape_of_write_eq_some hw2).trans sh1
  have f2 : ∀ q b i, (b ≠ t ∨ i ≠ 1) → σ2.store.read q b i = σ1.store.read q b i :=
    fun q b i hb => Store.read_of_write_eq_some_of_ne hw2 hb
  -- 3. ℓ
  obtain ⟨v2, hv2⟩ := hsem.lit_ok p ((ℓ₀ + d : ℕ) : ℚ) trivial
  obtain ⟨s3, hw3⟩ := Store.exists_write_eq_some_of_getElem?_shape (s := σ2.store) v2
    (sh2 ▸ ht) (show 2 < 7 by norm_num)
  rw [hr, exec_seq_instr_litIdx I (dst := ⟨t, 2⟩) (e := .const ℓ₀ + .const d) hv2 hw3]
  refine ex_name_node fun σ3 e3 _ => ?_
  subst e3
  have hv20 : dec p v2 ≠ 0 := by
    obtain ⟨δ, hδ, hd2⟩ := hsem.lit_err p _ v2 hv2
    rw [hd2]
    have := abs_le.mp hδ
    refine mul_ne_zero ?_ (by linarith)
    exact_mod_cast (by omega : ℓ₀ + d ≠ 0)
  have sh3 : σ3.store.shape = st.store.shape := (Store.shape_of_write_eq_some hw3).trans sh2
  have f3 : ∀ q b i, (b ≠ t ∨ i ≠ 2) → σ3.store.read q b i = σ2.store.read q b i :=
    fun q b i hb => Store.read_of_write_eq_some_of_ne hw3 hb
  have L3 : ∀ q b i, b < s₀ → σ3.store.read q b i = st.store.read q b i := fun q b i hb => by
    rw [f3 _ _ _ (Or.inl (by omega)), f2 _ _ _ (Or.inl (by omega)), f1 _ _ _ (Or.inl (by omega))]
  -- 4. R / ℓ
  obtain ⟨v3, hv3⟩ := hsem.bin_ok p .div R v2 trivial (fun _ => hv20) trivial
  obtain ⟨s4, hw4⟩ := Store.exists_write_eq_some_of_getElem?_shape (s := σ3.store) v3
    (sh3 ▸ ht) (show 3 < 7 by norm_num)
  rw [hr, exec_seq_instr_bin I (x := ⟨H.Lv, (2 * IExp.const d : IExp ℕ)⟩) (y := ⟨t, 2⟩) (dst :=
      ⟨t, 3⟩)
    ((L3 _ _ _ lLv).trans hR') (Store.read_of_write_eq_some hw3) hv3 hw4]
  refine ex_name_node fun σ4 e4 _ => ?_
  subst e4
  have sh4 : σ4.store.shape = st.store.shape := (Store.shape_of_write_eq_some hw4).trans sh3
  have f4 : ∀ q b i, (b ≠ t ∨ i ≠ 3) → σ4.store.read q b i = σ3.store.read q b i :=
    fun q b i hb => Store.read_of_write_eq_some_of_ne hw4 hb
  -- 5. the shift c
  obtain ⟨v4, hv4⟩ := hsem.bin_ok p .mul v3 au trivial (fun h => nomatch h) trivial
  obtain ⟨s5, hw5⟩ := Store.exists_write_eq_some_of_getElem?_shape (s := σ4.store) v4
    (sh4 ▸ ht) (show 4 < 7 by norm_num)
  rw [hr, exec_seq_instr_bin I (x := ⟨t, 3⟩) (y := ⟨Su, .const lo⟩) (dst := ⟨t, 4⟩)
    (Store.read_of_write_eq_some hw4)
    ((f4 p Su _ (Or.inl (by omega))).trans ((L3 _ _ _ lSu).trans hau)) hv4 hw5]
  refine ex_name_node fun σ5 e5 _ => ?_
  subst e5
  have sh5 : σ5.store.shape = st.store.shape := (Store.shape_of_write_eq_some hw5).trans sh4
  have f5 : ∀ q b i, (b ≠ t ∨ i ≠ 4) → σ5.store.read q b i = σ4.store.read q b i :=
    fun q b i hb => Store.read_of_write_eq_some_of_ne hw5 hb
  have L5 : ∀ q b i, b < s₀ → σ5.store.read q b i = st.store.read q b i := fun q b i hb => by
    rw [f5 _ _ _ (Or.inl (by omega)), f4 _ _ _ (Or.inl (by omega)), L3 _ _ _ hb]
  have t01_5 : σ5.store.read p t 0 = some v0 ∧ σ5.store.read p t 1 = some v1 := by
    refine ⟨?_, ?_⟩
    · rw [f5 _ _ _ (Or.inr (by omega)), f4 _ _ _ (Or.inr (by omega)),
        f3 _ _ _ (Or.inr (by omega)), f2 _ _ _ (Or.inr (by omega))]
      exact Store.read_of_write_eq_some hw1
    · rw [f5 _ _ _ (Or.inr (by omega)), f4 _ _ _ (Or.inr (by omega)),
        f3 _ _ _ (Or.inr (by omega))]
      exact Store.read_of_write_eq_some hw2
  -- 6. W = A − cI
  have hA5 : pairLayout.Holds σ5.store p H.Ma
      (eighBlockOff (IExp.const n) (IExp.const d) (IExp.const lo)).eval A := by
    rw [hbo]; exact fun i j t' => (L5 _ _ _ lMa).trans (hA i j t')
  have hc4 : σ5.store.read p (⟨t, 4⟩ : Cell ℕ ℕ).buf (⟨t, 4⟩ : Cell ℕ ℕ).idx.eval = some v4 :=
    Store.read_of_write_eq_some hw5
  have hXY6 : blockDisjoint (W, (0 : IExp ℕ).eval, 2 * (k * k)) (H.Ma,
      (eighBlockOff (IExp.const n) (IExp.const d) (IExp.const lo)).eval, 2 * (k * k)) = true :=
    bdn (fun h => by omega)
  have hcY6 : blockDisjoint ((⟨t, 4⟩ : Cell ℕ ℕ).buf, (⟨t, 4⟩ : Cell ℕ ℕ).idx.eval, 1)
      (W, (0 : IExp ℕ).eval, 2 * (k * k)) = true := bdn dtW
  refine ex_bind_node (fun _ => rfl) (exists_exec_zhermShift (I := I) p k (st := σ5) hA5 hc4
    hXY6 hcY6 hsem ⟨_, by rw [sh5]; exact hWs, by simp only [IExp.eval_zero]; omega⟩)
    fun σ6 h6 => ?_
  obtain ⟨hW6, hf6, hsh6, -⟩ := holds_of_exec_zhermShift
    (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    p k (st := σ5) (st' := σ6) hA5 hc4 hXY6 hcY6 h6
  have f6 : ∀ q b i, (b = W → False) → σ6.store.read q b i = σ5.store.read q b i :=
    fun q b i hb => hf6 q b i (bdn hb)
  have sh6 : σ6.store.shape = st.store.shape := hsh6.trans sh5
  -- 7. β
  obtain ⟨s7, hw7⟩ := Store.exists_write_eq_some_of_getElem?_shape (s := σ6.store) β
    (sh6 ▸ hsp) (show 0 < 2 by norm_num)
  rw [hr, exec_seq_instr_copy I (src := ⟨par, 2⟩) (dst := ⟨sp, 0⟩)
    ((f6 p par _ (fun h => by omega)).trans ((L5 _ _ _ lpar).trans hβ)) hw7]
  refine ex_name_node fun σ7 e7 _ => ?_
  subst e7
  have sh7 : σ7.store.shape = st.store.shape := (Store.shape_of_write_eq_some hw7).trans sh6
  have f7 : ∀ q b i, (b ≠ sp ∨ i ≠ 0) → σ7.store.read q b i = σ6.store.read q b i :=
    fun q b i hb => Store.read_of_write_eq_some_of_ne hw7 hb
  -- 8. fl(2) R
  obtain ⟨vb, hvb⟩ := hsem.bin_ok p .mul z2 R trivial (fun h => nomatch h) trivial
  have hvb0 : dec p vb ≠ 0 := by
    obtain ⟨δ, hδ, hdb⟩ := hsem.bin_err p .mul z2 R vb trivial hvb
    rw [hdb]
    simp only [BinOp.realOp]
    rw [hdz2]
    have := abs_le.mp hδ
    refine mul_ne_zero (mul_ne_zero (by norm_num) hR0.ne') (by linarith)
  obtain ⟨s8, hw8⟩ := Store.exists_write_eq_some_of_getElem?_shape (s := σ7.store) vb
    (sh7 ▸ hsp) (show 1 < 2 by norm_num)
  rw [hr, exec_seq_instr_bin I (x := ⟨c, 1⟩) (y := ⟨H.Lv, (2 * IExp.const d : IExp ℕ)⟩) (dst :=
      ⟨sp, 1⟩)
    ((f7 p c _ (Or.inl (by omega))).trans ((f6 p c _ (fun h => by omega)).trans
      ((L5 _ _ _ lc).trans hc1')))
    ((f7 p H.Lv _ (Or.inl (by omega))).trans ((f6 p H.Lv _ (fun h => by omega)).trans
      ((L5 _ _ _ lLv).trans hR'))) hvb hw8]
  refine ex_name_node fun σ8 e8 _ => ?_
  subst e8
  have sh8 : σ8.store.shape = st.store.shape := (Store.shape_of_write_eq_some hw8).trans sh7
  have f8 : ∀ q b i, (b ≠ sp ∨ i ≠ 1) → σ8.store.read q b i = σ7.store.read q b i :=
    fun q b i hb => Store.read_of_write_eq_some_of_ne hw8 hb
  have L8 : ∀ q b i, b < s₀ → σ8.store.read q b i = st.store.read q b i := fun q b i hb => by
    rw [f8 _ _ _ (Or.inl (by omega)), f7 _ _ _ (Or.inl (by omega)),
      f6 _ _ _ (fun h => by omega), L5 _ _ _ hb]
  have hW8 : pairLayout.Holds σ8.store p W (0 : IExp ℕ).eval
      ((I.sem.toFloatMachine p (fun x => (I.sem.toNat p x).getD 0) mmR qrR
        (I.sem.tapeUnif p (I.tape .uniform)) (I.sem.tapeNormal p (I.tape .gaussian))).hermShift
        A v4) := fun i j t' => (f8 _ _ _ (Or.inl (fun h => dspW h.symm))).trans
      ((f7 _ _ _ (Or.inl (fun h => dspW h.symm))).trans (hW6 i j t'))
  have hsp0 : σ8.store.read p sp (0 : IExp ℕ).eval = some β :=
    (f8 _ _ _ (Or.inr (by simp))).trans (Store.read_of_write_eq_some hw7)
  have hsp1 : σ8.store.read p sp ((0 : IExp ℕ).eval + 1) = some vb :=
    Store.read_of_write_eq_some hw8
  have hXA9 : blockDisjoint (B, (0 : IExp ℕ).eval, 2 * (k * k)) (W, (0 : IExp ℕ).eval,
      2 * (k * k)) = true := bdn (fun h => dWB h.symm)
  have hXp9 : blockDisjoint (B, (0 : IExp ℕ).eval, 2 * (k * k)) (sp, (0 : IExp ℕ).eval, 2) =
      true := bdn (fun h => dspB h.symm)
  -- 9. the sign
  refine ex_bind_node (fun _ => rfl) (exists_exec_eighSignBlock hmm hsem hlit1 p hu k F
    (by omega) (st := σ8) hW8 hsp0 hsp1 hvb0 hXA9 hXp9
    ⟨_, by rw [sh8]; exact hBs, by simp only [IExp.eval_zero]; omega⟩) fun σ9 h9 => ?_
  obtain ⟨hB9, hf9, hsh9, -⟩ := holds_of_exec_eighSignBlock
    (toNat := fun x => (I.sem.toNat p x).getD 0) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    hmm p hflag k F (st := σ8) (st' := σ9) hW8 hsp0 hsp1 hXA9 hXp9
    ⟨_, by rw [sh8]; exact hBs, by simp only [IExp.eval_zero]; omega⟩ h9
  have f9 : ∀ q b i, (b = B → False) → σ9.store.read q b i = σ8.store.read q b i :=
    fun q b i hb => hf9 q b i (bdn hb)
  have sh9 : σ9.store.shape = st.store.shape := hsh9.trans sh8
  have L9 : ∀ q b i, b < s₀ → σ9.store.read q b i = st.store.read q b i := fun q b i hb => by
    rw [f9 _ _ _ (fun h => by omega), L8 _ _ _ hb]
  -- 10. T = B + I
  have hc3' : σ9.store.read p (⟨c, 3⟩ : Cell ℕ ℕ).buf (⟨c, 3⟩ : Cell ℕ ℕ).idx.eval = some c3v :=
    (L9 _ _ _ lc).trans hc3v
  have hXY10 : blockDisjoint (T, (0 : IExp ℕ).eval, 2 * (k * k)) (B, (0 : IExp ℕ).eval,
      2 * (k * k)) = true := bdn (fun h => dBT h.symm)
  have hcY10 : ∀ i : ℕ, blockDisjoint (c, i, 1) (T, (0 : IExp ℕ).eval, 2 * (k * k)) = true :=
    fun _ => bdn (fun h => by omega)
  refine ex_bind_node (fun _ => rfl) (exists_exec_zhermShift (I := I) p k (st := σ9) hB9 hc3'
    hXY10 (hcY10 _) hsem ⟨_, by rw [sh9]; exact hTs, by simp only [IExp.eval_zero]; omega⟩)
    fun σ10 h10 => ?_
  obtain ⟨hT10, hf10, hsh10, -⟩ := holds_of_exec_zhermShift
    (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    p k (st := σ9) (st' := σ10) hB9 hc3' hXY10 (hcY10 _) h10
  have f10 : ∀ q b i, (b = T → False) → σ10.store.read q b i = σ9.store.read q b i :=
    fun q b i hb => hf10 q b i (bdn hb)
  have sh10 : σ10.store.shape = st.store.shape := hsh10.trans sh9
  -- 11. P₊
  have hc1_10 : σ10.store.read p (⟨c, 1⟩ : Cell ℕ ℕ).buf (⟨c, 1⟩ : Cell ℕ ℕ).idx.eval =
      some z2 := (f10 p c _ (fun h => by omega)).trans ((L9 _ _ _ lc).trans hc1')
  have hXY11 : blockDisjoint (Pp, (0 : IExp ℕ).eval, 2 * (k * k)) (T, (0 : IExp ℕ).eval,
      2 * (k * k)) = true := bdn (fun h => dTPp h.symm)
  have hcY11 : blockDisjoint (c, 1, 1) (Pp, (0 : IExp ℕ).eval, 2 * (k * k)) = true :=
    bdn (fun h => by omega)
  refine ex_bind_node (fun _ => rfl) (exists_exec_zhermScale (I := I) p k (st := σ10) hT10
    hc1_10 hXY11 hcY11 hsem hz20
    ⟨_, by rw [sh10]; exact hPps, by simp only [IExp.eval_zero]; omega⟩) fun σ11 h11 => ?_
  obtain ⟨hPp11, hf11, hsh11, -⟩ := holds_of_exec_zhermScale
    (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    p k (st := σ10) (st' := σ11) hT10 hc1_10 hXY11 hcY11 h11
  have f11 : ∀ q b i, (b = Pp → False) → σ11.store.read q b i = σ10.store.read q b i :=
    fun q b i hb => hf11 q b i (bdn hb)
  have sh11 : σ11.store.shape = st.store.shape := hsh11.trans sh10
  -- 12. T = B − I
  have hB11 : pairLayout.Holds σ11.store p B (0 : IExp ℕ).eval
      (newtonSchulzSign (I.sem.toFloatMachine p (fun x => (I.sem.toNat p x).getD 0) mmR qrR
        (I.sem.tapeUnif p (I.tape .uniform)) (I.sem.tapeNormal p (I.tape .gaussian))) β vb F
        ((I.sem.toFloatMachine p (fun x => (I.sem.toNat p x).getD 0) mmR qrR
        (I.sem.tapeUnif p (I.tape .uniform)) (I.sem.tapeNormal p (I.tape .gaussian))).hermShift
        A v4)) :=
    fun i j t' => (f11 _ _ _ dBPp).trans ((f10 _ _ _ dBT).trans (hB9 i j t'))
  have hc0_11 : σ11.store.read p (⟨c, 0⟩ : Cell ℕ ℕ).buf (⟨c, 0⟩ : Cell ℕ ℕ).idx.eval =
      some o1 := (f11 p c _ (fun h => by omega)).trans
      ((f10 p c _ (fun h => by omega)).trans ((L9 _ _ _ lc).trans hc0'))
  refine ex_bind_node (fun _ => rfl) (exists_exec_zhermShift (I := I) p k (st := σ11) hB11
    hc0_11 hXY10 (hcY10 _) hsem
    ⟨_, by rw [sh11]; exact hTs, by simp only [IExp.eval_zero]; omega⟩) fun σ12 h12 => ?_
  obtain ⟨hT12, hf12, hsh12, -⟩ := holds_of_exec_zhermShift
    (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    p k (st := σ11) (st' := σ12) hB11 hc0_11 hXY10 (hcY10 _) h12
  have f12 : ∀ q b i, (b = T → False) → σ12.store.read q b i = σ11.store.read q b i :=
    fun q b i hb => hf12 q b i (bdn hb)
  have sh12 : σ12.store.shape = st.store.shape := hsh12.trans sh11
  -- 13. T = −T
  refine ex_bind_node (fun _ => rfl) (exists_exec_zneg (I := I) p k k (st := σ12) hT12
    (Or.inr ⟨rfl, rfl⟩) hsem
    ⟨_, by rw [sh12]; exact hTs, by simp only [IExp.eval_zero]; omega⟩) fun σ13 h13 => ?_
  obtain ⟨hT13, hf13, hsh13, -⟩ := holds_of_exec_zneg
    (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    p k k (st := σ12) (st' := σ13) hT12 (Or.inr ⟨rfl, rfl⟩) h13
  have f13 : ∀ q b i, (b = T → False) → σ13.store.read q b i = σ12.store.read q b i :=
    fun q b i hb => hf13 q b i (bdn hb)
  have sh13 : σ13.store.shape = st.store.shape := hsh13.trans sh12
  -- 14. P₋
  have hc1_13 : σ13.store.read p (⟨c, 1⟩ : Cell ℕ ℕ).buf (⟨c, 1⟩ : Cell ℕ ℕ).idx.eval =
      some z2 := (f13 p c _ (fun h => by omega)).trans ((f12 p c _ (fun h => by omega)).trans
        ((f11 p c _ (fun h => by omega)).trans hc1_10))
  have hXY14 : blockDisjoint (Pm, (0 : IExp ℕ).eval, 2 * (k * k)) (T, (0 : IExp ℕ).eval,
      2 * (k * k)) = true := bdn (fun h => dTPm h.symm)
  have hcY14 : blockDisjoint (c, 1, 1) (Pm, (0 : IExp ℕ).eval, 2 * (k * k)) = true :=
    bdn (fun h => by omega)
  refine ex_bind_node (fun _ => rfl) (exists_exec_zhermScale (I := I) p k (st := σ13) hT13
    hc1_13 hXY14 hcY14 hsem hz20
    ⟨_, by rw [sh13]; exact hPms, by simp only [IExp.eval_zero]; omega⟩) fun σ14 h14 => ?_
  obtain ⟨hPm14, hf14, hsh14, -⟩ := holds_of_exec_zhermScale
    (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    p k (st := σ13) (st' := σ14) hT13 hc1_13 hXY14 hcY14 h14
  have f14 : ∀ q b i, (b = Pm → False) → σ14.store.read q b i = σ13.store.read q b i :=
    fun q b i hb => hf14 q b i (bdn hb)
  have sh14 : σ14.store.shape = st.store.shape := hsh14.trans sh13
  have hPp14 : pairLayout.Holds σ14.store p Pp (0 : IExp ℕ).eval
      ((I.sem.toFloatMachine p (fun x => (I.sem.toNat p x).getD 0) mmR qrR
        (I.sem.tapeUnif p (I.tape .uniform)) (I.sem.tapeNormal p (I.tape .gaussian))).hermScale
        ((I.sem.toFloatMachine p (fun x => (I.sem.toNat p x).getD 0) mmR qrR
        (I.sem.tapeUnif p (I.tape .uniform)) (I.sem.tapeNormal p (I.tape .gaussian))).hermShift
        (newtonSchulzSign (I.sem.toFloatMachine p (fun x => (I.sem.toNat p x).getD 0) mmR qrR
          (I.sem.tapeUnif p (I.tape .uniform)) (I.sem.tapeNormal p (I.tape .gaussian))) β vb F
          ((I.sem.toFloatMachine p (fun x => (I.sem.toNat p x).getD 0) mmR qrR
          (I.sem.tapeUnif p (I.tape .uniform)) (I.sem.tapeNormal p (I.tape .gaussian))).hermShift
          A v4)) c3v) z2) :=
    fun i j t' => (f14 _ _ _ dPpPm).trans ((f13 _ _ _ (fun h => dTPp h.symm)).trans
      ((f12 _ _ _ (fun h => dTPp h.symm)).trans (hPp11 i j t')))
  -- 15. the trace
  have L14t : ∀ i, σ14.store.read p t i = σ9.store.read p t i := fun i => by
    rw [f14 _ _ _ dtPm, f13 _ _ _ dtT, f12 _ _ _ dtT, f11 _ _ _ dtPp, f10 _ _ _ dtT]
  have L9t : ∀ i, σ9.store.read p t i = σ5.store.read p t i := fun i => by
    rw [f9 _ _ _ dtB, f8 _ _ _ (Or.inl dtsp), f7 _ _ _ (Or.inl dtsp), f6 _ _ _ dtW]
  refine ex_bind_node (fun _ => rfl) (exists_exec_ztraceRe_node (I := I) hsem p k (st := σ14)
    (dst := ⟨t, 5⟩) hPp14 dtPp (Store.exists_write_eq_some_of_getElem?_shape default
      (sh14 ▸ ht) (show 5 < 7 by norm_num))) fun σ15 h15 => ?_
  obtain ⟨htr15, hf15⟩ := read_of_exec_ztraceRe
    (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    p k (st := σ14) (st' := σ15) hPp14 (bdn dtPp) h15
  obtain ⟨hsh15, -⟩ := shape_pos_of_exec_ztraceRe_node p k h15
  have f15 : ∀ q b i, (b ≠ t ∨ i ≠ 5) → σ15.store.read q b i = σ14.store.read q b i := by
    intro q b i hb
    refine hf15 q b i ?_
    simp only [blockDisjoint, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
    change (b ≠ t ∨ i + 1 ≤ 5) ∨ 5 + 1 ≤ i
    omega
  have sh15 : σ15.store.shape = st.store.shape := hsh15.trans sh14
  -- 16. t + 1/2
  obtain ⟨v6, hv6⟩ := hsem.bin_ok p .add _ c2v trivial (fun h => nomatch h) trivial
  obtain ⟨s16, hw16⟩ := Store.exists_write_eq_some_of_getElem?_shape (s := σ15.store) v6
    (sh15 ▸ ht) (show 6 < 7 by norm_num)
  rw [hr, exec_seq_instr_bin I (x := ⟨t, 5⟩) (y := ⟨c, 2⟩) (dst := ⟨t, 6⟩) htr15
    ((f15 p c _ (Or.inl (by omega))).trans ((f14 p c _ (fun h => by omega)).trans
      ((f13 p c _ (fun h => by omega)).trans ((f12 p c _ (fun h => by omega)).trans
        ((f11 p c _ (fun h => by omega)).trans ((f10 p c _ (fun h => by omega)).trans
          ((L9 _ _ _ lc).trans hc2v))))))) hv6 hw16]
  refine ex_name_node fun σ16 e16 _ => ?_
  subst e16
  have f16 : ∀ q b i, (b ≠ t ∨ i ≠ 6) → σ16.store.read q b i = σ15.store.read q b i :=
    fun q b i hb => Store.read_of_write_eq_some_of_ne hw16 hb
  refine hrest σ16 (fun q b i hb => ?_) ((Store.shape_of_write_eq_some hw16).trans sh15)
    ⟨v0, ?_, ?_⟩ ⟨v6, Store.read_of_write_eq_some hw16⟩
    ⟨_, fun i j t' => (f16 _ _ _ (Or.inl (fun h => dtPp h.symm))).trans
      ((f15 _ _ _ (Or.inl (fun h => dtPp h.symm))).trans (hPp14 i j t'))⟩
    ⟨_, fun i j t' => (f16 _ _ _ (Or.inl (fun h => dtPm h.symm))).trans
      ((f15 _ _ _ (Or.inl (fun h => dtPm h.symm))).trans (hPm14 i j t'))⟩
  · rw [f16 _ _ _ (Or.inl (by omega)), f15 _ _ _ (Or.inl (by omega)),
      f14 _ _ _ (fun h => by omega), f13 _ _ _ (fun h => by omega),
      f12 _ _ _ (fun h => by omega), f11 _ _ _ (fun h => by omega),
      f10 _ _ _ (fun h => by omega), L9 _ _ _ hb]
  · rw [f16 _ _ _ (Or.inr (by omega)), f15 _ _ _ (Or.inr (by omega)), L14t, L9t]
    exact t01_5.1
  · rw [f16 _ _ _ (Or.inr (by omega)), f15 _ _ _ (Or.inr (by omega)), L14t, L9t, hMneg]
    exact t01_5.2

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
      (∃ v, st.store.read p c 2 = some v) ∧ (∃ v, st.store.read p c 3 = some v) ∧
      st.store.read p c 4 = some (I.sem.sqrtHalf p)) :
    ∃ st', exec I (eighNodeBlock p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) (.const lo)
      (.const k) par H.Lv Su Sg H.Ma H.Qa H.Sz H.Kd H.Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩).run st =
        some st' := by
  have hsz : ∀ {b : ℕ} {x : P × ℕ}, st.store.shape[b]? = some x → b < st.store.size :=
    fun h => by simpa [Store.size_shape] using (Array.getElem?_eq_some_iff.mp h).1
  obtain ⟨-, hMa, hUa, hQa, hEa, hSz, hKd, hKp, hLv⟩ := id hH
  have hn2 : 0 < 4 * (n * n) := by have : 0 < n := (by omega); positivity
  obtain ⟨_, hSg0⟩ := hSg 0 hn2
  have lSg := Store.lt_size_of_read_eq_some hSg0
  have lpar := Store.lt_size_of_read_eq_some hpar
  obtain ⟨_, hSu'⟩ := hSu
  have lSu := Store.lt_size_of_read_eq_some hSu'
  obtain ⟨o1, ho1⟩ := hsem.lit_ok p 1 trivial
  have lc := Store.lt_size_of_read_eq_some (hc.1.trans ho1)
  obtain ⟨hc0, hc1, ⟨c2v, hc2⟩, ⟨c3v, hc3⟩, hc4⟩ := hc
  have hlt : ∀ b ∈ H.handles ++ [par, Su, Sg, c], b < st.store.size := by
    simp only [EighArenas.handles, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro b (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    exacts [hsz hMa, hsz hUa, hsz hQa, hsz hEa, hsz hSz, hsz hKd, hsz hKp, hsz hLv, lpar, lSu,
      lSg, lc]
  have hltH : ∀ b ∈ H.handles, b < st.store.size := fun b hb => hlt b (List.mem_append_left _ hb)
  have hlt3 : ∀ b ∈ H.handles ++ [par, Su, c], b < st.store.size := fun b hb => by
    rcases List.mem_append.mp hb with hb | hb
    · exact hltH b hb
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl
      exacts [lpar, lSu, lc]
  have hout : ∀ x, st.store.size ≤ x → x ∉ H.handles ++ [Sg] := fun x hx hm => by
    rcases List.mem_append.mp hm with hm | hm
    · exact absurd (hltH x hm) (by omega)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      subst hm; omega
  have hcS3 : c ∉ H.handles ++ [Sg] := fun hm => by
    rcases List.mem_append.mp hm with hm | hm
    · have := (List.nodup_append.mp hbufs).2.2 c hm c (by simp) rfl
      exact this
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      subst hm
      have hb := (List.nodup_append.mp hbufs).2.1
      simp at hb
  change ∃ st', exec I (.seq _ .skip) st = some st'
  rw [exec_seq_skip]
  refine exists_exec_alloc_of_exists_split ?_
  refine exists_exec_alloc_of_exists_split ?_
  refine exists_exec_alloc_of_exists_split ?_
  refine exists_exec_alloc_of_exists_split ?_
  refine exists_exec_alloc_of_exists_split ?_
  refine exists_exec_alloc_of_exists_split ?_
  refine exists_exec_alloc_of_exists_split ?_
  beta_reduce
  refine ex_gen_node fun σ₇ hσ₇ => ?_
  have hσs := congrArg St.store hσ₇
  simp only at hσs
  simp only [Array.size_push]
  have hrd : ∀ {q : P} {b i : ℕ}, b < st.store.size →
      σ₇.store.read q b i = st.store.read q b i := fun hb => by
    rw [hσs]
    iterate 7 rw [Store.read_push_of_lt (by first | omega | (simp only [Array.size_push]; omega))]
  have hshp : ∀ {b : ℕ}, b < st.store.size → σ₇.store.shape[b]? = st.store.shape[b]? :=
    fun hb => by
      rw [hσs]
      iterate 7 rw [Store.getElem?_shape_push_of_lt _
        (by first | omega | (simp only [Array.size_push]; omega))]
  refine node_setup_exists (qrR := qrR) hmm hsem hlit p hu n ℓ₀ F d lo k hk hk2 hℓ H (par := par)
    (Su := Su)
    (c := c) (A := A) (R := R) (st := σ₇) st.store.size hlt3 _ _ _ _ _ _ _ (by simp <;> omega)
    (by simp [List.nodup_cons] <;> omega)
    (by rw [hσs]; simp [Store.shape, Array.getElem?_push, Array.getElem_push, Nat.add_assoc])
    (by rw [hσs]; simp [Store.shape, Array.getElem?_push, Array.getElem_push, Nat.add_assoc])
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro X (rfl | rfl | rfl | rfl | rfl) <;> rw [hσs] <;>
        simp [Store.shape, Array.getElem?_push, Array.getElem_push, Nat.add_assoc])
    (fun i j t => (hrd (hsz hMa)).trans (hA i j t)) ((hrd (hsz hLv)).trans hR) hR0
    ⟨_, (hrd lpar).trans hpar⟩ ⟨_, (hrd lSu).trans hSu'⟩ ((hrd lc).trans hc0)
    ((hrd lc).trans hc1) ⟨_, (hrd lc).trans hc2⟩ ⟨_, (hrd lc).trans hc3⟩ _ ?_
  intro σ hlo hsh ht01 ht6 hPpQ hPmQ
  obtain ⟨v, h0, h1⟩ := ht01
  obtain ⟨Q1, hQ1⟩ := hPpQ
  obtain ⟨Q2, hQ2⟩ := hPmQ
  have hshσ : ∀ {b : ℕ}, b < st.store.size → σ.store.shape[b]? = st.store.shape[b]? :=
    fun hb => by rw [hsh, hshp hb]
  have hHσ : H.Shaped σ.store p n D :=
    ⟨hH.1, by rw [hshσ (hsz hMa)]; exact hMa, by rw [hshσ (hsz hUa)]; exact hUa,
      by rw [hshσ (hsz hQa)]; exact hQa, by rw [hshσ (hsz hEa)]; exact hEa,
      by rw [hshσ (hsz hSz)]; exact hSz, by rw [hshσ (hsz hKd)]; exact hKd,
      by rw [hshσ (hsz hKp)]; exact hKp, by rw [hshσ (hsz hLv)]; exact hLv⟩
  have hrσ : ∀ {q : P} {b i : ℕ}, b < st.store.size →
      σ.store.read q b i = st.store.read q b i := fun hb => (hlo _ _ _ hb).trans (hrd hb)
  obtain ⟨hbS, -⟩ := nodup_scratch_node (Pp := st.store.size + 1 + 1 + 1 + 1 + 1)
    (Pm := st.store.size + 1 + 1 + 1 + 1 + 1 + 1) hbufs hlt (by omega) (by omega) (by omega)
  refine node_branch_exists hmm hqr hsem hlit htn p hu n d lo k hk hk2 H (st := σ) (A := A) hd hHσ
    hbS ?_ ?_ (fun i j t => (hrσ (hsz hMa)).trans (hA i j t)) hQ1 hQ2
    (fun w hw => (hSg w hw).imp fun _ h => (hrσ lSg).trans h)
    ((hrσ lc).trans hc1) ((hrσ lc).trans hc4) h0 h1 ht6
  · intro hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hcS3 (List.mem_append_left _ hm)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with hm | hm | hm
      · exact hcS3 (by simp [hm])
      · omega
      · omega
  · intro hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hout _ le_rfl (List.mem_append_left _ hm)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with hm | hm | hm
      · exact hout _ le_rfl (by simp [hm])
      · omega
      · omega

end NLAlib
