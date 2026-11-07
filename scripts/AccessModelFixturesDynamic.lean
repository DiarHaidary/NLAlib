import NLAlib

/-! # Access-model fixtures for the index binder (data-dependent sizes)

The cheats of `docs/design/Computation-DynamicPrograms.md` §3 and
`docs/design/Computation-Hardening.md` §2.1 against `bindIdx` and the conversion of a stored value
to an index (`ScalarSem.toNat`). Each theorem proves that the model form of a cheating program is
false, or that a cheating semantics is outside the model.

* `not_matrixFree_prodTree` (B1): a product of two data computed through two index binders and an
  index literal is charged two `toNat` and one literal; a budget of one `toNat` is false (the
  fixture promised by `Computation-DynamicPrograms.md` §3).
* `not_matrixFree_idxCopyTree` (B2): a value above the binder's static bound fails the run (the
  binder does not clamp), so copying every natural input through an index is false; false by
  failure.
* `exec_idxCopyTree_eq_none` (B2, run level): the same run is `none`; a clamping binder would
  make this statement false, not only break a proof.
* `exec_negIdxTree_eq_none` (`toNat` below 0, run level): a binder on a stored `-1` fails the run
  under the exact interpretation; a conversion flooring negatives to `0` makes it false.
* `not_isExactToNat_lowToNatSem` (B3b): a conversion that is one too small is outside the model,
  whose `IsIndexExactSem` clause requires the exact floor. This replaces B3 (a rounded target
  without the exactness clauses, false by failure), which the model's bundled clause made true.
* `not_matrixFreeRoundedProb_litSizedTree` (B3'): the exactness bound `B` of the model must cover
  the sizes the program writes; with exact literals only up to `B = 0`, a size `2` written by
  `litIdx` reads back as `1` and the buffer of that size is too short; false by failure.

Run with `lake env lean scripts/AccessModelFixturesDynamic.lean` after `lake build NLAlib`. -/

namespace AccessModelFixturesDynamic

open NLAlib.Computation MeasureTheory ProbabilityTheory

/-- A probability measure gives the whole space measure one, so a bound $0$ on the measure of a
set that contains every point is false. -/
theorem false_of_forall_mem {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {S : Set Ω} (hS : ∀ ω, ω ∈ S) (h : μ.real S ≤ 0) : False := by
  rw [Set.eq_univ_of_forall hS] at h
  simp [measureReal_def] at h
  exact absurd h (by norm_num)

/-- Two stored values become indices and their product is written back as a literal. -/
def prodTree : Prog Unit Unit 1 2 :=
  .bindIdx () ⟨0, .const 0⟩ (.var 1) <| .bindIdx () ⟨0, .const 1⟩ (.var 1) <|
    .instr (.litIdx () ⟨1, .const 0⟩ (.mul (.var 2) (.var 3)))

/-- B1: each index binder is charged a `toNat`: a budget that charges one is false. -/
theorem not_matrixFree_prodTree :
    ¬ MatrixFree (𝕜 := ℝ) () prodTree (fun _ _ => True) (fun _ _ => Unit)
      (fun _ _ _ => ![#[some 2, some 3], Array.replicate 1 none])
      (fun _ _ => Finsupp.single (.toNat ()) 1 + Finsupp.single (.lit ()) 1) (fun _ _ _ => 3)
      (fun _ _ _ _ _ _ => True) := by
  intro h
  obtain ⟨-, st, hrun, hcnt, -, -⟩ := h 1 (fun _ => 6) trivial () 0 (fun _ _ => 0)
  simp [prodTree, Prog.exec, FStmt.exec, toNatStep, Instr.subst, Cell.subst, IExp.subst,
    IExp.eval, IExp.evalIn, Instr.run, exactInterp, exactSem, inputState, Store.write, Store.read,
    Instr.kind, Fin.snoc] at hrun
  subst hrun
  have := hcnt (OpKind.toNat ())
  simp [inputState] at this

/-- A stored value copied through an index. -/
def idxCopyTree : Prog Unit Unit 1 2 :=
  .bindIdx () ⟨0, .const 0⟩ (.var 1) (.instr (.litIdx () ⟨1, .const 0⟩ (.var 2)))

/-- B2, at the run level: the binder of `idxCopyTree` at bound $0$ on a stored $1$ fails the run.
A clamping binder would run it (writing $0$), so this statement, not only its proof, is false if the
clamp came back. -/
theorem exec_idxCopyTree_eq_none :
    idxCopyTree.exec (exactInterp (P := Unit) (ι := Unit)
        (fun _ => (0 : Matrix (Fin 0) (Fin 0) ℝ)) (fun _ _ => 0)) 0 (fun _ => 0)
      (inputState () [#[some (1 : ℝ)], Array.replicate 1 none]) = none := by
  simp [idxCopyTree, Prog.exec, FStmt.exec, toNatStep, Instr.subst, Cell.subst, IExp.subst,
    IExp.eval, IExp.evalIn, Instr.run, exactInterp, exactSem, inputState, Store.write,
    Store.read, Fin.snoc]

/-- B2: a value above the binder's static bound fails the run (no clamping), so a copy of every
natural input through an index is false: at input $1$ and bound $0$ the run fails. -/
theorem not_matrixFree_idxCopyTree :
    ¬ MatrixFree (𝕜 := ℝ) () idxCopyTree (fun _ _ => True) (fun _ _ => ℕ)
      (fun _ _ x => ![#[some (x : ℝ)], Array.replicate 1 none])
      (fun _ _ => Finsupp.single (.toNat ()) 1 + Finsupp.single (.lit ()) 1) (fun _ _ _ => 2)
      (fun _ _ x _ _ st => st.store.read () 1 0 = some (x : ℝ)) := by
  intro h
  obtain ⟨-, st, hrun, -, -, -⟩ := h 1 (fun _ => 0) trivial 1 0 (fun _ _ => 0)
  simp [idxCopyTree, Prog.exec, FStmt.exec, toNatStep, Instr.subst, Cell.subst, IExp.subst,
    IExp.eval, IExp.evalIn, Instr.run, exactInterp, exactSem, inputState, Store.write,
    Store.read, Fin.snoc] at hrun

/-- A stored value used as an index under a generous bound. -/
def negIdxTree : Prog Unit Unit 1 1 :=
  .bindIdx () ⟨0, .const 0⟩ (.const 5) .skip

/-- `toNat` below $0$, at the run level: the binder on a stored $-1$ fails the run under the
exact interpretation, though $\lfloor -1 \rfloor_+ = 0$ is within the bound. A semantics or a
binder that floored negative values to $0$ would run it, so this statement is false if the
conversion stopped failing below zero. -/
theorem exec_negIdxTree_eq_none :
    negIdxTree.exec (exactInterp (P := Unit) (ι := Unit)
        (fun _ => (0 : Matrix (Fin 0) (Fin 0) ℝ)) (fun _ _ => 0)) 0 (fun _ => 0)
      (inputState () [#[some (-1 : ℝ)]]) = none := by
  simp [negIdxTree, Prog.exec, FStmt.exec, toNatStep, Cell.subst, IExp.subst,
    IExp.evalIn, exactInterp, exactSem, inputState, Store.read]

/-- A semantics exact on arithmetic whose conversion to an index is one too small. -/
noncomputable def lowToNatSem : ScalarSem Unit ℝ :=
  { (exactSem (𝕜 := ℝ) : ScalarSem Unit ℝ) with toNat := fun _ x => some (⌊x⌋₊ - 1) }

/-- B3b (replaces B3, a rounded target without the exactness clauses, which the model's bundled
`IsIndexExactSem` clause made true): the semantics B3 uses is outside the model. -/
theorem not_isExactToNat_lowToNatSem : ¬ IsExactToNat (fun _ x => x) lowToNatSem := by
  intro h
  have := h () 1
  simp [lowToNatSem] at this

/-- A semantics exact on arithmetic and on the conversion, whose literals of nonzero rationals
are halved (relative error `1/2`): exact integer literals up to `0` only. -/
noncomputable def halfLitSem : ScalarSem Unit ℝ :=
  { (exactSem (𝕜 := ℝ) : ScalarSem Unit ℝ) with lit := fun _ q => some ((q : ℝ) * (1 / 2)) }

/-- A size written by `litIdx` into scratch, read back by a binder, sizes a buffer whose cell
`n − 1` (by the size parameter) is written. -/
def litSizedTree : Prog Unit Unit 1 0 :=
  .alloc () (.const 1) <| .seq (.instr (.litIdx () ⟨0, .const 0⟩ (.var 1))) <|
    .bindIdx () ⟨0, .const 0⟩ (.var 1) <|
      .alloc () (.var 2) (.instr (.lit () ⟨1, .sub (.var 1) (.const 1)⟩ 1))

/-- B3': the exactness bound of the model must cover the sizes the program writes. With the
model's index exactness only up to `B = 0` and an exact conversion, a size `2` written by
`litIdx` can read back as `1`, and the write into the buffer of that size fails. -/
theorem not_matrixFreeRoundedProb_litSizedTree :
    ¬ MatrixFreeRoundedProb (P := Unit) (ι := Unit) (K := ℝ) () litSizedTree (fun _ n => 1 ≤ n 0)
      (fun _ _ => Unit) (fun _ _ _ => ![]) (fun _ x => x) (fun _ _ => 0) (fun _ _ => 0)
      (fun _ _ _ => 0)
      (fun _ _ I => IsRelErrSem (fun _ => (1 / 2 : ℝ)) (fun _ x => x) (fun _ _ => True) I.sem)
      (fun _ => True) (fun _ _ _ => True) (fun _ _ _ _ => True) (fun _ _ _ => 0) := by
  intro h
  have hI : IsRelErrSem (fun _ => (1 / 2 : ℝ)) (fun _ x => x) (fun _ _ => True) halfLitSem := by
    have h := (isRelErrSem_exactSem (P := Unit)).mono (v := fun _ => (1 / 2 : ℝ))
      (fun _ => by norm_num)
    exact ⟨h.bin_err, h.bin_ok, fun _ q z hz => ⟨-(1 / 2), by norm_num, by
        simp only [halfLitSem, Option.some.injEq] at hz; rw [← hz]; ring⟩,
      fun _ q _ => ⟨_, rfl⟩, h.neg, h.conj, h.re, h.sqrt_err, h.sqrt_ok, h.cmp_eq, h.cmp_lt,
      h.cmp_le, h.convert_err, h.convert_ok⟩
  have hL : IsExactIntLit (fun _ x => x) halfLitSem 0 := fun _ k hk => by
    obtain rfl : k = 0 := Nat.le_zero.mp hk
    exact ⟨0, by simp [halfLitSem], by simp⟩
  have hT : IsExactToNat (fun _ x => x) halfLitSem := fun _ x => by simp [halfLitSem, exactSem]
  refine false_of_forall_mem (fun ω => ?_) (h 1 (fun _ => 2) (by simp) () trivial
    { exactInterp (P := Unit) (ι := Unit) (fun _ => (0 : Matrix (Fin 1) (Fin 1) ℝ))
        (fun _ _ => 0) with sem := halfLitSem } (fun _ _ x => x) ⟨hL, hT⟩ hI trivial
    (Dist → ℕ → ℝ) _ tapeLaw id ⟨aemeasurable_id, Measure.map_id⟩)
  rintro ⟨-, st, hrun, -⟩
  simp [litSizedTree, Prog.exec, FStmt.exec, toNatStep, Instr.subst, Cell.subst, IExp.subst,
    IExp.eval, IExp.evalIn, Instr.run, halfLitSem, exactSem, inputState, Store.write,
    Store.read, Fin.snoc] at hrun

end AccessModelFixturesDynamic
