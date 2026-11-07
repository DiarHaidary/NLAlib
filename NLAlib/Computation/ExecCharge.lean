/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Exec

/-!
# Runs that differ only in their charges

The run of a statement never reads the counts: the store, the tape positions and the memory
ledgers evolve the same way under two interpretations that differ only in their charges, from
two states that differ only in their counts. So a run lemma proved under unit charges transfers
to any charge.

## Main results

* `NLAlib.Computation.exists_exec_withCharge_eq_some`: the transfer of a successful run to
  another charge and another start count.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- Two folds whose steps carry a relation between their states: if the first fold succeeds,
so does the second, in a related state. -/
private theorem exists_foldlM_eq_some {α σ σ' : Type} (R : σ → σ' → Prop)
    {f : σ → α → Option σ} {g : σ' → α → Option σ'}
    (hfg : ∀ x a a' b, R a a' → f a x = some b → ∃ b', g a' x = some b' ∧ R b b') :
    ∀ (l : List α) {a : σ} {a' : σ'} {b : σ}, R a a' → l.foldlM f a = some b →
      ∃ b', l.foldlM g a' = some b' ∧ R b b'
  | [], _, a', _, hR, h => by cases h; exact ⟨a', rfl, hR⟩
  | x :: l, _, _, _, hR, h => by
    rw [List.foldlM_cons] at h ⊢
    obtain ⟨c, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨c', h1', hR'⟩ := hfg x _ _ _ hR h1
    rw [h1']
    exact exists_foldlM_eq_some R hfg l hR' h2

variable (I : Interp P ι K C) (ch : OpKind P ι → C)

/-- A comparison under another charge, from another count: the same outcome, the same state up
to its count. -/
private theorem exists_cmpStep_eq_some {p : P} {c : CmpOp} {x y : Cell ℕ ℕ} {a a₁ : St P K C}
    {r : Bool} (h : cmpStep I p c x y a = some (r, a₁)) (c₀ : C) :
    ∃ c₁, cmpStep { I with charge := ch } p c x y { a with cnt := c₀ } =
      some (r, { a₁ with cnt := c₁ }) := by
  simp only [cmpStep, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨va, hva, vb, hvb, rr, hrr, he⟩ := h
  cases he
  exact ⟨c₀ + ch (.cmp p), by simp only [cmpStep, hva, hvb, Option.bind_some, hrr,
    Option.map_some]⟩

/-- The run lemma of `NLAlib.Computation.exists_exec_withCharge_eq_some` for a fueled
loop, given the transfer of its body. -/
private theorem exists_exec_whileFuel_eq_some (fuel : IExp ℕ) (p : P) (c : CmpOp)
    (x y : Cell ℕ ℕ) (body : Stmt P ι ℕ ℕ)
    (ih : ∀ {a b : St P K C}, exec I body a = some b → ∀ c₀, ∃ c₁,
      exec { I with charge := ch } body { a with cnt := c₀ } = some { b with cnt := c₁ })
    {a b : St P K C} (h : exec I (.whileFuel fuel p c x y body) a = some b) (c₀ : C) :
    ∃ c₁, exec { I with charge := ch } (.whileFuel fuel p c x y body) { a with cnt := c₀ } =
      some { b with cnt := c₁ } := by
  rw [exec] at h ⊢
  obtain ⟨r, hr, hfin⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨r', hr', c₁, rfl⟩ := exists_foldlM_eq_some
    (f := fun (s : St P K C × Bool) (_ : ℕ) => if s.2 = true then
      (cmpStep I p c x y s.1).bind fun r =>
        if r.1 = true then Option.map (fun st' => (st', true)) (exec I body r.2)
        else some (r.2, false)
      else some s)
    (g := fun (s : St P K C × Bool) (_ : ℕ) => if s.2 = true then
      (cmpStep { I with charge := ch } p c x y s.1).bind fun r =>
        if r.1 = true then Option.map (fun st' => (st', true))
          (exec { I with charge := ch } body r.2)
        else some (r.2, false)
      else some s)
    (fun (s : St P K C × Bool) (s' : St P K C × Bool) => ∃ c₁, s' = ({ s.1 with cnt := c₁ }, s.2))
    (fun _ s s' z ⟨c₁, hs'⟩ hz => by
      subst hs'
      rcases s with ⟨s, _ | _⟩
      · simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hz ⊢
        exact ⟨_, rfl, c₁, by rw [← hz]⟩
      · simp only [↓reduceIte] at hz ⊢
        obtain ⟨⟨rr, s₁⟩, hq, hz⟩ := Option.bind_eq_some_iff.mp hz
        obtain ⟨c₂, hq'⟩ := exists_cmpStep_eq_some I ch hq c₁
        rw [hq', Option.bind_some]
        rcases rr with _ | _
        · simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hz ⊢
          exact ⟨_, rfl, c₂, by rw [← hz]⟩
        · simp only [↓reduceIte, Option.map_eq_some_iff] at hz ⊢
          obtain ⟨st', hst', rfl⟩ := hz
          obtain ⟨c₃, h₃⟩ := ih hst' c₂
          exact ⟨_, ⟨_, h₃, rfl⟩, c₃, rfl⟩)
    (List.range fuel.eval) (a := (a, true)) ⟨c₀, rfl⟩ hr
  rw [hr', Option.bind_some]
  rcases r with ⟨rs, _ | _⟩
  · simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hfin ⊢
    exact ⟨c₁, by rw [hfin]⟩
  · simp at hfin

/-- A run under another charge, from another count: if the run of $s$ under `I` from $a$ ends
in $b$, then for every start count $c_0$ the run of $s$ under `I` with the charge replaced by
`ch`, from $a$ with count $c_0$, ends in $b$ with some count $c_1$: the store, the tape
positions and the current and peak memory do not depend on the charges. -/
theorem exists_exec_withCharge_eq_some :
    ∀ (s : Stmt P ι ℕ ℕ) {a b : St P K C}, exec I s a = some b → ∀ c₀, ∃ c₁,
      exec { I with charge := ch } s { a with cnt := c₀ } = some { b with cnt := c₁ }
  | .skip, _, _, h, c₀ => by
    rw [exec_skip] at h
    cases h
    exact ⟨c₀, rfl⟩
  | .seq s t, _, _, h, c₀ => by
    rw [exec_seq] at h ⊢
    obtain ⟨m, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨c₁, h₁'⟩ := exists_exec_withCharge_eq_some s h₁ c₀
    obtain ⟨c₂, h₂'⟩ := exists_exec_withCharge_eq_some t h₂ c₁
    exact ⟨c₂, by rw [h₁', Option.bind_some, h₂']⟩
  | .instr i, a, _, h, c₀ => by
    rw [exec_instr] at h ⊢
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨c₀ + ch i.kind, by simp only [hr, Option.map_some]⟩
  | .apply o p dst dOff src sOff cols, a, _, h, c₀ => by
    rw [exec] at h ⊢
    dsimp only
    split_ifs at h ⊢ with hif
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨X, hX, Y, hY, s, hs, rfl⟩ := h
    exact ⟨c₀ + (ch (.load p o) + cols.eval • ch (.matvec p o)), by
      simp only [hX, Option.bind_some, hY, hs, Option.map_some]⟩
  | .rom p dst i, a, _, h, c₀ => by
    rw [exec] at h ⊢
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, s, hs, rfl⟩ := h
    exact ⟨c₀ + ch (.rom p), by simp only [hv, Option.bind_some, hs, Option.map_some]⟩
  | .alloc p len body, a, _, h, c₀ => by
    rw [exec_alloc] at h ⊢
    obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨c₁, hm'⟩ := exists_exec_withCharge_eq_some (body a.store.size) hm c₀
    exact ⟨c₁, congrArg (Option.map _) hm'⟩
  | .loop n body, _, _, h, c₀ => by
    rw [exec_loop] at h ⊢
    obtain ⟨_, hb', c₁, rfl⟩ := exists_foldlM_eq_some
      (f := fun st i => exec I (body i) st)
      (g := fun st i => exec { I with charge := ch } (body i) st)
      (fun (x : St P K C) (y : St P K C) => ∃ c₁, y = { x with cnt := c₁ })
      (fun i x y z ⟨c₁, hy⟩ hz => by
        subst hy
        obtain ⟨c₂, h₂⟩ := exists_exec_withCharge_eq_some (body i) hz c₁
        exact ⟨_, h₂, c₂, rfl⟩)
      (List.range n.eval) ⟨c₀, rfl⟩ h
    exact ⟨c₁, hb'⟩
  | .whileFuel fuel p c x y body, _, _, h, c₀ =>
    exists_exec_whileFuel_eq_some I ch fuel p c x y body
      (fun hb => exists_exec_withCharge_eq_some body hb) h c₀
  | .ite p c x y t e, _, _, h, c₀ => by
    rw [exec_ite] at h ⊢
    obtain ⟨⟨rr, a₁⟩, hq, hz⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨c₁, hq'⟩ := exists_cmpStep_eq_some I ch hq c₀
    rw [hq', Option.bind_some]
    rcases rr with _ | _
    · simp only [Bool.false_eq_true, ↓reduceIte] at hz ⊢
      exact exists_exec_withCharge_eq_some e hz c₁
    · exact exists_exec_withCharge_eq_some t hz c₁
  | .named _ _ body, _, _, h, c₀ => by
    rw [exec_named] at h ⊢
    exact exists_exec_withCharge_eq_some body h c₀
  | .kcall o p dims ins outs, a, _, h, c₀ => by
    rw [exec] at h ⊢
    obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨c₀ + ch (.kcall p o (dims.map IExp.eval)), by
      change (I.kcallStore o p _ _ _ a.store).map _ = _
      rw [hs]
      rfl⟩

end NLAlib.Computation
