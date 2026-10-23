import NLAlib
open Lean Meta Elab Command

/-! # Program checks (rules E1 to E4 and E9, docs/rules/rules.toml)

The guarantees of a result about a program (no dependence on the data, counts and memory as
functions of the sizes, the law of the tape) hold by the definition of the access model it is an
instance of (`NLAlib/Computation/Model.lean`, `NLAlib.Computation.MatrixFreeProb`), and Lean's
kernel checks them; `docs/design/Computation.md`, "Guarantees", lists what is proved and what is
trusted. These checks are what is left, on every declaration reachable through `import NLAlib`:

* E1 (hygiene): a program (a definition whose type ends in `Builder` or `Stmt`, or is a
  `ProgFamily`, outside the Computation core) is generic in its two
  variable sorts, no instance mentions them, and every argument is a type, a tag or oracle name (a
  value of a type parameter), a `Dist`, a handle, an index expression, a cell, a program, or a
  family of handles or index expressions over `Fin _`. Host data (`ℕ` sizes, lists, functions) is
  rejected outside the implementation files (`implFiles`). The guarantees do not rest on it: it
  keeps programs size-generic, so that the emitted code is the program the result is about.
* E2 (hygiene): programs, kernels and implementations are computable: not `noncomputable`, not
  opaque (`partial`, `opaque`), not `unsafe`, no `implemented_by` (each runs code other than its
  definition). An opaque or unsafe constant of program type is a program for E1, E2 and E4.
* E3 (the lint): a public theorem outside the Computation core whose statement mentions
  `RunsWithin`, or mentions a run (`exec`, `Stmt`, `ProgFamily.inst`) and a measure, is an
  instance of an access model: its conclusion is `MatrixFree`, `MatrixFreeProb` or
  `StoredEntries`. Results must be instances; private lemmas are proof steps.
* E4: every `<spec>Prog` has a public result in an access model whose statement mentions it.
* E9 (hygiene): a `Builder` program that another program calls closes its allocations: run
  against a fresh continuation, its statement does not reach the continuation under an `alloc`
  (D11: a buffer is freed at the end of the enclosing block, so an open `alloc` stays live, and
  counted, for the rest of the caller's block). `scope`, `named`, loops and branches close them.

Then the fixtures of the end of this file, which break each rule, must be rejected; the cheating
realisations of the old E3 are flagged by the lint, and `scripts/AccessModelFixtures.lean` proves
that their instance forms are false. Run with `lake env lean scripts/Programs.lean` after
`lake build NLAlib`; a nonzero exit code means a violation. False positives go in `allowE1` with
a reason. -/

namespace ProgramChecks

/-- The theory of the Computation core: syntax, semantics, budgets, substitution, exact
arithmetic and contracts. -/
def theoryModules : List Name :=
  [`NLAlib.Computation.Syntax, `NLAlib.Computation.Store, `NLAlib.Computation.Exec,
   `NLAlib.Computation.RunsWithin,
   `NLAlib.Computation.Subst, `NLAlib.Computation.Exact, `NLAlib.Computation.Contract]

/-- The Computation core: the theory and the access models, whose combinators (`ProgFamily.inst`,
`ProgFamily.substOracle`) are not programs. Its theorems are general facts about every program
and interpretation, so the lint (E3) skips the theory modules only. -/
def coreModules : List Name := theoryModules ++ [`NLAlib.Computation.Model]

/-- Implementation files: an implementation may take host data (E1, D11). -/
def implFiles : List Name := [`NLAlib.Computation.Dense, `NLAlib.Computation.Sparse]

/-- The access models: a result about a program concludes one of them (E3, E4). -/
def models : List Name :=
  [`NLAlib.Computation.MatrixFree, `NLAlib.Computation.MatrixFreeProb,
   `NLAlib.Computation.StoredEntries]

/-- The two variable sorts of a program type, if it is one: `Builder P ι VB VI β`,
`Stmt P ι VB VI`, or the unfolded `ContT (Stmt P ι VB VI) Id β`. -/
partial def progSorts? (e : Expr) : Option (Expr × Expr) :=
  let e := e.consumeMData
  if e.isAppOfArity ``NLAlib.Computation.Builder 5 || e.isAppOfArity ``NLAlib.Computation.Stmt 4
  then some (e.getArg! 2, e.getArg! 3)
  else if e.isAppOfArity ``ContT 3 then progSorts? (e.getArg! 0)
  else none

/-- The sorts of the conclusion of a type, before and after reducible unfolding. -/
def conclSorts? (t : Expr) : MetaM (Option (Expr × Expr)) := do
  match progSorts? t with
  | some r => return some r
  | none => return progSorts? (← whnfR t)

/-- The telescope of a program type: its binders and conclusion, through a `ProgFamily`
abbreviation (whose binders are the sorts, the sizes and the handles). -/
def progTelescope {α : Type} (t : Expr) (k : Array Expr → Expr → MetaM α) : MetaM α :=
  forallTelescope t fun xs concl => do
    if concl.isAppOf ``NLAlib.Computation.ProgFamily then
      forallTelescope (← whnfR concl) fun ys c => k (xs ++ ys) c
    else k xs concl

/-- E1: the offending binders of a program (or `notGenericInVariables`). -/
def checkE1 (c : Name) : MetaM (List Name) := do
  let info ← getConstInfo c
  progTelescope info.type fun xs concl => do
    let some (vb, vi) ← conclSorts? (← instantiateMVars concl) | return [`notAProgram]
    unless vb.isFVar && vi.isFVar && vb != vi do return [`notGenericInVariables]
    let vbId := vb.fvarId!
    let viId := vi.fvarId!
    let mut bad := []
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.fvarId == vbId || d.fvarId == viId then continue
      let t ← instantiateMVars d.type
      let mentions := t.containsFVar vbId || t.containsFVar viId
      if d.binderInfo.isInstImplicit then
        if mentions then bad := d.userName :: bad
        continue
      let ok ← (do
        if t.isSort then return true
        if t.isFVarOf vbId then return true
        if t.isFVar && !mentions then return true
        if t.isConstOf ``NLAlib.Computation.Dist then return true
        if t.isAppOfArity ``NLAlib.Computation.IExp 1 && t.appArg!.isFVarOf viId then return true
        if t.isAppOfArity ``NLAlib.Computation.Cell 2 && (t.getArg! 0).isFVarOf vbId &&
            (t.getArg! 1).isFVarOf viId then return true
        if let some (vb', vi') ← conclSorts? t then
          if !t.isForall && vb'.isFVarOf vbId && vi'.isFVarOf viId then return true
        -- a family of handles or index expressions over `Fin _` (the arguments of `ProgFamily`)
        if t.isForall && t.bindingDomain!.isAppOfArity ``Fin 1 && !t.bindingBody!.hasLooseBVars then
          let u := t.bindingBody!
          if u.isFVarOf vbId then return true
          if u.isAppOfArity ``NLAlib.Computation.IExp 1 && u.appArg!.isFVarOf viId then return true
        return false : MetaM Bool)
      unless ok do bad := d.userName :: bad
    return bad.reverse

/-- Whether a theorem's statement is about a program's runs: it mentions `RunsWithin`, or a run
(`exec`, `Stmt`, `ProgFamily.inst`) together with a measure. -/
def isAboutRuns (t : Expr) : Bool :=
  let has (n : Name) := (t.find? fun e => e.isConstOf n).isSome
  has ``NLAlib.Computation.RunsWithin ||
    ((has ``NLAlib.Computation.exec || has ``NLAlib.Computation.Stmt ||
        has ``NLAlib.Computation.ProgFamily.inst) && has ``MeasureTheory.Measure)

/-- Whether a theorem's conclusion is an instance of an access model. -/
def isInstanceType (t : Expr) : MetaM Bool :=
  forallTelescope t fun _ concl => do
    let concl ← instantiateMVars concl
    return models.any concl.isAppOf

/-- E3: whether a theorem is about a program's runs without being an instance of an access
model. -/
def checkE3 (t : Expr) : MetaM Bool := do
  return isAboutRuns t && !(← isInstanceType t)

/-- E2: why a constant of program type does not run as its definition, if it does not. -/
def checkE2 (env : Environment) (c : Name) : Option String :=
  match env.find? c with
  | some (.opaqueInfo _) => some "opaque (`partial` or `opaque`): its definition is not its code"
  | some (.defnInfo d) =>
    if d.safety != .safe then some "unsafe or partial"
    else if (Compiler.implementedByAttr.getParam? env c).isSome then
      some "`implemented_by`: its compiled code is not its definition"
    else if isNoncomputable env c then some "noncomputable"
    else none
  | _ => none

/-- E9: follow the spine of a statement (the second part of each `seq`) to the continuation `K`;
`some true` if an `alloc` on the spine has `K` in its body, `none` if the spine is stuck (a
program argument run in place). -/
partial def spineLeaks (K : FVarId) (e : Expr) (fuel : Nat) : MetaM (Option Bool) := do
  if fuel = 0 then return none
  let e ← whnf e
  if e.isFVarOf K then return some false
  if e.isAppOfArity ``NLAlib.Computation.Stmt.seq 6 then return ← spineLeaks K e.appArg! (fuel - 1)
  if e.isAppOfArity ``NLAlib.Computation.Stmt.alloc 7 then return some (e.appArg!.containsFVar K)
  match e.getAppFn.constName? with
  | some n => return if (← getEnv).isConstructor n then some false else none
  | none => return none

/-- E9: whether a `Builder` program leaves an allocation open for its caller (`none`: cannot
tell). A program of type `Stmt` is closed by construction. -/
def checkE9 (c : Name) : MetaM (Option Bool) := do
  let info ← getConstInfo c
  forallTelescope info.type fun xs concl => do
    let concl ← whnfR (← instantiateMVars concl)
    unless concl.isAppOfArity ``ContT 3 do return some false
    withLocalDeclD `K (concl.getArg! 0) fun K => do
      let k ← withLocalDeclD `x (concl.getArg! 2) fun x => mkLambdaFVars #[x] K
      let prog := mkAppN (mkConst c (info.levelParams.map mkLevelParam)) xs
      spineLeaks K.fvarId! (mkApp prog k) 100000

/-- Whether a constant is an internal or generated declaration. -/
def isAux (env : Environment) (c : Name) : Bool :=
  c.isInternalDetail || isAuxRecursor env c || isNoConfusion env c || isMatcherCore env c ||
    (c.components.getLast?.map fun s => s.toString.startsWith "eq_" ||
      s.toString.startsWith "proof_" || s.toString == "eq_def").getD false

/-- The module of a constant. -/
def moduleOf (env : Environment) (c : Name) : Option Name :=
  (env.getModuleIdxFor? c).map fun i => env.header.moduleNames[i.toNat]!

/-- Whether a type is a program type. -/
def isProgType (t : Expr) : MetaM Bool :=
  progTelescope t fun _ concl => do return (← conclSorts? (← instantiateMVars concl)).isSome

/-- E4: whether a `<spec>Prog` has no public result in an access model whose statement mentions
it (`instances`: the public instances). -/
def checkE4 (env : Environment) (instances : Array Name) (c : Name) : Bool :=
  match c with
  | .str _ s =>
    s.endsWith "Prog" && !instances.any fun r =>
      ((env.find? r).map fun i => (i.type.find? fun e => e.isConstOf c).isSome).getD false
  | _ => false

end ProgramChecks

open ProgramChecks in
run_cmd do
  let env ← getEnv
  let mut progs : Array Name := #[]
  let mut instances : Array Name := #[]
  let mut flagged : Array Name := #[]
  let mut bad : Nat := 0
  for (c, info) in env.constants.map₁.toList do
    let some m := moduleOf env c | continue
    unless (`NLAlib).isPrefixOf m do continue
    if isAux env c then continue
    match info with
    | .defnInfo _ | .opaqueInfo _ =>
      if coreModules.contains m then continue
      if ← liftTermElabM (isProgType info.type) then progs := progs.push c
    | .thmInfo _ =>
      if isPrivateName c || theoryModules.contains m then continue
      if ← liftTermElabM (isInstanceType info.type) then instances := instances.push c
      else if ← liftTermElabM (checkE3 info.type) then flagged := flagged.push c
    | _ => pure ()
  for c in progs do
    let m := (moduleOf env c).get!
    let e1 ← liftTermElabM (checkE1 c)
    unless e1.isEmpty || implFiles.contains m do
      bad := bad + 1
      logError m!"E1 {c}: not generic in its handles and indices, or takes host data, at {e1}"
    if let some why := checkE2 env c then
      bad := bad + 1
      logError m!"E2 {c}: a program, kernel or implementation is computable; this one is {why}"
    if checkE4 env instances c then
      bad := bad + 1
      logError m!"E4 {c}: a `<spec>Prog` has a result in an access model ({""
        }`MatrixFree`, `MatrixFreeProb` or `StoredEntries`) that mentions it"
  -- E9 on the callees: the programs that occur in another program's definition
  let mut callees : NameSet := {}
  for c in progs do
    if let some v := (env.find? c).bind (·.value?) then
      for d in v.getUsedConstants do
        if d != c && progs.contains d then callees := callees.insert d
  for c in progs do
    unless callees.contains c do continue
    match ← liftTermElabM (checkE9 c) with
    | some true =>
      bad := bad + 1
      logError m!"E9 {c}: a program called by another program frees its allocations; wrap {""
        }them in `scope`"
    | some false => pure ()
    | none => logWarning m!"E9 {c}: the spine of this callee cannot be followed; not checked"
  for c in flagged do
    bad := bad + 1
    logError m!"E3 {c}: a result about a program's runs is an instance of an access model {""
      }(`MatrixFree`, `MatrixFreeProb` or `StoredEntries`); make it one, or make it private"
  logInfo m!"programs: {progs.size} programs and kernels ({callees.size} called by others), {""
    }{instances.size} results in an access model; {bad} violations"

/-! ## Fixtures: each breaks a rule and must be rejected -/

namespace ProgramChecksFixtures

open NLAlib.Computation MeasureTheory ProbabilityTheory

/-- Not generic: a handle forged from a number. -/
def forgeNat (n : ℕ) : Builder Unit Unit ℕ ℕ Unit := Builder.ins (.lit () ⟨n, .const 0⟩ 0)

/-- Generic, but turns index variables into handles through a host function. -/
def forgeFun {VB VI : Type} (f : VI → VB) (n : IExp VI) : Builder Unit Unit VB VI Unit :=
  Builder.forRange n fun i => Builder.ins (.lit () ⟨f i, .var i⟩ 0)

/-- Generic, but takes a host size. -/
def hostSize {VB VI : Type} (b : VB) (n : ℕ) : Builder Unit Unit VB VI Unit :=
  Builder.forRange (.const n) fun i => Builder.ins (.lit () ⟨b, .var i⟩ 0)

/-- A program family (accepted by E1): sizes and handles as `Fin`-families. -/
def familyProg : ProgFamily Unit Unit 1 1 := fun _ _ _ n h =>
  (Builder.forRange (n 0) fun i => Builder.ins (.lit () ⟨h 0, .var i⟩ 0)).run

/-- A program that cannot run. -/
noncomputable def choiceProg {VB VI : Type} (b : VB) : Builder Unit Unit VB VI Unit :=
  Builder.ins (.lit () ⟨b, .const 0⟩ (Classical.choice ⟨0⟩))

/-- A `<spec>Prog` with no result in an access model. -/
def orphanProg {VB VI : Type} (b : VB) : Builder Unit Unit VB VI Unit :=
  Builder.ins (.lit () ⟨b, .const 0⟩ 0)

/-- A cheating realisation: `A` is handed to the program in its initial store. Not an instance
of an access model: the lint flags it, and its instance form is false
(`scripts/AccessModelFixtures.lean`, `not_matrixFree_copyProg`). -/
theorem runsWithin_cheat {N k ℓ : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (ξ : Dist → ℕ → ℝ) :
    RunsWithin (exactInterp (P := Unit) (ι := Unit) (fun _ => A) ξ)
      ((NLAlib.hutchppProg () () .gaussian (.const N) (.const k) (.const ℓ)
        ⟨0, .const 0⟩).run)
      (inputState () [Array.replicate 1 none, (flatten A).map some]) 0 (fun _ => 0)
      (fun _ => True) := by
  sorry

/-- A cheating realisation through the tape: the program reads `A` from the tape of every
distribution while the oracle holds it too. Flagged by the lint; its instance form is false
(`not_matrixFree_drawProg`). -/
theorem runsWithin_cheatTape {N k ℓ : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) :
    RunsWithin (exactInterp (P := Unit) (ι := Unit) (fun _ => A)
        (fun _ i => (flatten A).getD i 0))
      ((NLAlib.hutchppProg () () .gaussian (.const N) (.const k) (.const ℓ)
        ⟨0, .const 0⟩).run)
      (inputState () [Array.replicate 1 none]) 0 (fun _ => 0) (fun _ => True) := by
  sorry

/-- Gap 1 of the old E3: a tail whose conclusion is not `RunsWithin`, about a program with `A` in
its initial store. Flagged by the lint. -/
theorem measureReal_not_runsWithin_cheat_le {Ω : Type} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {N k ℓ : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (ξ : Ω → Dist → ℕ → ℝ) :
    μ.real {ω | ¬ RunsWithin (exactInterp (P := Unit) (ι := Unit) (fun _ => A) (ξ ω))
      ((NLAlib.hutchppProg () () .gaussian (.const N) (.const k) (.const ℓ)
        ⟨0, .const 0⟩).run)
      (inputState () [Array.replicate 1 none, (flatten A).map some]) 0 (fun _ => 0)
      (fun _ => True)} ≤ 0 := by
  sorry

/-- Gap 2 of the old E3: a tape law that depends on the matrix (here a Gaussian centred at an
entry of `A`, standing for leverage-score sampling). Flagged by the lint; in
`MatrixFreeProb` the law is `tapeLaw`, fixed by the definition. -/
theorem measureReal_not_runsWithin_le_of_hasLaw_iidSequence {Ω : Type} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} (A : Matrix (Fin 1) (Fin 1) ℝ) {ξ : Ω → Dist → ℕ → ℝ}
    (hξ : HasLaw (fun ω => ξ ω .gaussian) (NLAlib.iidSequence (gaussianReal (A 0 0) 1)) μ) :
    μ.real {ω | ¬ RunsWithin (exactInterp (P := Unit) (ι := Unit) (fun _ => A) (ξ ω))
      (.instr (.draw () .gaussian ⟨0, .const 0⟩)) (inputState () [Array.replicate 1 none]) 0
      (fun _ => 1) (fun st => st.store.read () 0 0 = some (A 0 0))} ≤ 1 := by
  sorry

/-- A class that reads an entry out of a value of a type parameter (gap 3 of the old E3). -/
class Entries (M : Type) where
  /-- The entry. -/
  entry : M → ℚ

instance : Entries (Matrix (Fin 1) (Fin 1) ℚ) := ⟨fun A => A 0 0⟩

/-- Gap 3: a program that takes a value of a type parameter and writes its entry as a literal.
E1 accepts it (it is generic, and E1 is hygiene); the access models make its use harmless:
`not_matrixFree_leakProg` in `scripts/AccessModelFixtures.lean`. -/
def leakProg {VB VI : Type} {M : Type} [Entries M] (x : M) (out : Cell VB VI) :
    Builder Unit Unit VB VI Unit :=
  Builder.ins (.lit () out (Entries.entry x))

/-- Gap 3: the cheating realisation with `leakProg`, which the old E3 accepted. Flagged by the
lint. -/
theorem runsWithin_leakProg (A : Matrix (Fin 1) (Fin 1) ℚ) (ξ : Dist → ℕ → ℝ) :
    RunsWithin (exactInterp (P := Unit) (ι := Unit) (fun _ => A.map ((↑) : ℚ → ℝ)) ξ)
      (leakProg A ⟨0, .const 0⟩).run (inputState () [Array.replicate 1 none])
      (Finsupp.single (.lit ()) 1) (fun _ => 1)
      (fun st => st.store.read () 0 0 = some ((A 0 0 : ℚ) : ℝ)) := by
  sorry

/-- A program that is opaque: `partial`, so its definition is not the code that runs. -/
partial def partialProg {VB VI : Type} (b : VB) : Builder Unit Unit VB VI Unit := do
  Builder.ins (.lit () ⟨b, .const 0⟩ 0)
  partialProg b

/-- A callee that leaves its scratch buffer live for the rest of its caller's block. -/
def leakyCallee {VB VI : Type} (b : VB) : Builder Unit Unit VB VI Unit := do
  let t ← Builder.alloc () 1
  Builder.ins (.lit () ⟨t, .const 0⟩ 0)
  Builder.ins (.copy () ⟨b, .const 0⟩ ⟨t, .const 0⟩)

/-- The same callee, closed by `scope`. -/
def closedCallee {VB VI : Type} (b : VB) : Builder Unit Unit VB VI Unit := Builder.scope do
  let t ← Builder.alloc () 1
  Builder.ins (.lit () ⟨t, .const 0⟩ 0)
  Builder.ins (.copy () ⟨b, .const 0⟩ ⟨t, .const 0⟩)

end ProgramChecksFixtures

open ProgramChecks in
run_cmd do
  let env ← getEnv
  let expect (rule : String) (c : Name) (got : List Name) (want : List Name) : CommandElabM Unit := do
    if got == want then
      logInfo (if want.isEmpty then m!"{rule} accepts {c}" else m!"{rule} rejects {c} at {got}")
    else logError m!"{rule} fixture {c}: expected {want}, got {got}"
  expect "E1" ``ProgramChecksFixtures.forgeNat (← liftTermElabM (checkE1 ``ProgramChecksFixtures.forgeNat))
    [`notGenericInVariables]
  expect "E1" ``ProgramChecksFixtures.forgeFun (← liftTermElabM (checkE1 ``ProgramChecksFixtures.forgeFun))
    [`f]
  expect "E1" ``ProgramChecksFixtures.hostSize (← liftTermElabM (checkE1 ``ProgramChecksFixtures.hostSize))
    [`n]
  expect "E1" ``NLAlib.Computation.cooImpl (← liftTermElabM (checkE1 ``NLAlib.Computation.cooImpl))
    [`pattern]
  expect "E1" ``NLAlib.hutchppProg (← liftTermElabM (checkE1 ``NLAlib.hutchppProg)) []
  expect "E1" ``ProgramChecksFixtures.familyProg
    (← liftTermElabM (checkE1 ``ProgramChecksFixtures.familyProg)) []
  expect "E1" ``ProgramChecksFixtures.leakProg
    (← liftTermElabM (checkE1 ``ProgramChecksFixtures.leakProg)) []
  for c in [``ProgramChecksFixtures.choiceProg, ``ProgramChecksFixtures.partialProg] do
    match checkE2 env c with
    | some why => logInfo m!"E2 rejects {c}: {why}"
    | none => logError m!"E2 fixture {c} passes"
  if (← liftTermElabM (isProgType (← getConstInfo ``ProgramChecksFixtures.partialProg).type)) then
    logInfo m!"{``ProgramChecksFixtures.partialProg} is a program for E1, E2 and E4"
  else logError m!"E2 fixture {``ProgramChecksFixtures.partialProg} is not seen as a program"
  if checkE2 env ``NLAlib.hutchppProg |>.isSome then
    logError m!"E2 rejects {``NLAlib.hutchppProg}"
  let e3 (c : Name) (want : Bool) : CommandElabM Unit := do
    let got ← liftTermElabM (checkE3 (← getConstInfo c).type)
    if got == want then
      logInfo (if want then m!"E3 flags {c}" else m!"E3 accepts {c}")
    else logError m!"E3 fixture {c}: expected {want}, got {got}"
  e3 ``ProgramChecksFixtures.runsWithin_cheat true
  e3 ``ProgramChecksFixtures.runsWithin_cheatTape true
  e3 ``ProgramChecksFixtures.measureReal_not_runsWithin_cheat_le true
  e3 ``ProgramChecksFixtures.measureReal_not_runsWithin_le_of_hasLaw_iidSequence true
  e3 ``ProgramChecksFixtures.runsWithin_leakProg true
  e3 ``NLAlib.matrixFree_hutchppProg false
  e3 ``NLAlib.matrixFreeProb_hutchppProg false
  e3 ``NLAlib.storedEntries_substOracle_hutchppProg_cooImpl false
  e3 ``NLAlib.Computation.RunsWithin.subst true
  let mut instances : Array Name := #[]
  for (c, info) in env.constants.map₁.toList do
    if let .thmInfo _ := info then
      if (moduleOf env c).any (`NLAlib).isPrefixOf && !isPrivateName c then
        if ← liftTermElabM (isInstanceType info.type) then instances := instances.push c
  if checkE4 env instances ``ProgramChecksFixtures.orphanProg then
    logInfo m!"E4 rejects {``ProgramChecksFixtures.orphanProg}: no result in an access model"
  else logError m!"E4 fixture {``ProgramChecksFixtures.orphanProg} passes"
  for c in [``NLAlib.hutchppProg, ``NLAlib.gramSchmidtProg] do
    if checkE4 env instances c then logError m!"E4 rejects {c}"
    else logInfo m!"E4 accepts {c}"
  let e9 (c : Name) (want : Bool) : CommandElabM Unit := do
    let got ← liftTermElabM (checkE9 c)
    if got == some want then
      logInfo (if want then m!"E9 rejects {c}" else m!"E9 accepts {c}")
    else logError m!"E9 fixture {c}: expected {want}, got {got}"
  e9 ``ProgramChecksFixtures.leakyCallee true
  e9 ``ProgramChecksFixtures.closedCallee false
  e9 ``NLAlib.gramSchmidtProg false
  e9 ``NLAlib.orthAgainst false
  e9 ``NLAlib.Computation.dot false
  e9 ``NLAlib.hutchppProg true
