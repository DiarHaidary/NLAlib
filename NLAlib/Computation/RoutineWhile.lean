/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.RoutineSpec

/-!
# Fueled loops of specifications

The specification rule of `NLAlib.Computation.Stmt.whileFuel` (a loop that runs its body while a
comparison of two cells holds, and fails when it has tested `fuel` times and every test held),
with an invariant and one footprint for every iteration: the routine-specification form of
`NLAlib.Computation.Triple.whileFuel`. The invariant `Inv st₀ j st` holds of the state before the
$j$-th test. The total mode needs, at each such state, the comparison to succeed and, when it
holds, fuel for one more test; it then concludes that the loop succeeds. The liberal mode needs
nothing beyond the body's specification and concludes the postcondition of a successful run: the
invariant at a state whose test failed.

## Main results

* `NLAlib.Computation.Spec.whileFuel`, `NLAlib.Computation.RoutineSpec.whileFuel`: the loop rule.
* `NLAlib.Computation.Mode.sat_of_needs`: an outcome satisfies a predicate in a mode, from what
  every successful outcome satisfies and, in the total mode, success.
-/

@[expose] public section

namespace NLAlib.Computation

/-- An outcome satisfies `Q` in mode `m` when every successful outcome does and, in the total
mode, the outcome is a success. -/
theorem Mode.sat_of_needs {α : Type} {m : Mode} {Q : α → Prop} {o : Option α}
    (hex : m.Needs (∃ x, o = some x)) (hall : ∀ x, o = some x → Q x) : m.Sat Q o := by
  cases m
  · obtain ⟨x, hx⟩ := hex
    exact ⟨x, hx, hall x hx⟩
  · exact hall

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] {m : Mode} {I : Interp P ι K C}
  {pre : St P K C → Prop} {fp : List (ℕ × ℕ × ℕ)}

/-- **A fueled loop of specifications** with an invariant and one footprint for every
iteration: `Inv st₀ j st` holds of the state `st` before the $j$-th test of a run from `st₀`
(`h0`); a test that holds leads to the body, specified from the state after the test to
`Inv st₀ (j + 1)` (`hbody`). The total mode needs fuel for the first test (`hf0`), the
comparison to succeed at every such state (`hcmp`) and, when it holds, fuel for the next test
(`hfuel`). The loop modifies `fp` and ends at the state after a test that failed, of a state
satisfying the invariant. -/
theorem Spec.whileFuel {fuel : IExp ℕ} {p : P} {c : CmpOp} {x y : Cell ℕ ℕ} {body : Stmt P ι ℕ ℕ}
    (Inv : St P K C → ℕ → St P K C → Prop) (h0 : ∀ st, pre st → Inv st 0 st)
    (hf0 : m.Needs (0 < fuel.eval))
    (hcmp : ∀ st₀, pre st₀ → ∀ j st, Inv st₀ j st → m.Needs (∃ a b r,
      st.store.read p x.buf x.idx.eval = some a ∧ st.store.read p y.buf y.idx.eval = some b ∧
        I.sem.cmp p c a b = some r))
    (hfuel : ∀ st₀, pre st₀ → ∀ j st st₁, Inv st₀ j st →
      cmpStep I p c x y st = some (true, st₁) → m.Needs (j + 1 < fuel.eval))
    (hbody : ∀ st₀, pre st₀ → ∀ j, Spec m I (fun st₁ => ∃ st, Inv st₀ j st ∧
      cmpStep I p c x y st = some (true, st₁)) body fp fun _ st' => Inv st₀ (j + 1) st') :
    Spec m I pre (.whileFuel fuel p c x y body) fp fun st₀ st' =>
      ∃ j st, Inv st₀ j st ∧ cmpStep I p c x y st = some (false, st') := by
  have hstore : ∀ {st : St P K C} {r : Bool × St P K C}, cmpStep I p c x y st = some r →
      r.2.store = st.store := fun h => by rw [snd_of_cmpStep_eq_some h]
  refine Triple.conseq (Triple.whileFuel (fun st₀ j st => Inv st₀ j st ∧
      Modifies fp st₀.store st.store) (fun st hst => ⟨hf0, h0 st hst, .refl _ _⟩)
    fun st₀ hst j st ⟨hinv, hm⟩ => Mode.sat_of_needs ((hcmp st₀ hst j st hinv).mono ?_)
      fun ⟨r, st₁⟩ heq hr => ?_) (fun _ h => h) fun st₀ st' _ ⟨j, stj, ⟨hinv, hm⟩, heq⟩ =>
    ⟨by rw [hstore heq] at *; exact hm, j, stj, hinv, heq⟩
  · rintro ⟨a, b, r, hx, hy, hr⟩
    exact ⟨(r, { st with cnt := st.cnt + I.charge (.cmp p) }), by
      simp only [cmpStep, hx, hy, hr, Option.bind_some, Option.map_some]⟩
  · dsimp only at hr ⊢
    subst hr
    refine ⟨hfuel st₀ hst j st st₁ hinv heq, wp_mono (hbody st₀ hst j st₁ ⟨st, hinv, heq⟩)
      fun st' ⟨hm', hinv'⟩ => ⟨hinv', ?_⟩⟩
    rw [hstore heq] at hm'
    exact (hm.trans hm').mono fun _ h => (List.mem_append.mp h).elim id id

/-- **A fueled loop in a builder**, of specifications: `NLAlib.Computation.Spec.whileFuel` for a
builder body run inside the loop statement. -/
theorem RoutineSpec.whileFuel {fuel : IExp ℕ} {p : P} {c : CmpOp} {x y : Cell ℕ ℕ}
    {body : Builder P ι ℕ ℕ Unit} (Inv : St P K C → ℕ → St P K C → Prop)
    (h0 : ∀ st, pre st → Inv st 0 st) (hf0 : m.Needs (0 < fuel.eval))
    (hcmp : ∀ st₀, pre st₀ → ∀ j st, Inv st₀ j st → m.Needs (∃ a b r,
      st.store.read p x.buf x.idx.eval = some a ∧ st.store.read p y.buf y.idx.eval = some b ∧
        I.sem.cmp p c a b = some r))
    (hfuel : ∀ st₀, pre st₀ → ∀ j st st₁, Inv st₀ j st →
      cmpStep I p c x y st = some (true, st₁) → m.Needs (j + 1 < fuel.eval))
    (hbody : ∀ st₀, pre st₀ → ∀ j, Spec m I (fun st₁ => ∃ st, Inv st₀ j st ∧
      cmpStep I p c x y st = some (true, st₁)) body.run fp fun _ st' => Inv st₀ (j + 1) st') :
    RoutineSpec m I pre (Builder.stmt (.whileFuel fuel p c x y body.run)) fp fun st₀ st' =>
      ∃ j st, Inv st₀ j st ∧ cmpStep I p c x y st = some (false, st') :=
  RoutineSpec.stmt (Spec.whileFuel Inv h0 hf0 hcmp hfuel hbody)

end NLAlib.Computation
