import NLAlib
open Lean Meta Elab Command

/-! # Program checks (rules E1 to E4 and E9, docs/rules/rules.toml)

The rules of `docs/design/Computation.md` §10 that need Lean's types, checked on every
declaration reachable through `import NLAlib`:

* E1: a program (a definition whose type ends in `Builder` or `Stmt`, outside the Computation
  core) is generic in its two variable sorts, no instance mentions them, and every argument is a
  type, a tag or oracle name (a value of a type parameter), a `Dist`, a handle, an index
  expression, a cell or a program. Host data (`ℕ` sizes, lists, functions) is rejected outside the
  implementation files (`implFiles`).
* E2: programs, kernels and implementations are computable: not `noncomputable`, not opaque
  (`partial`, `opaque`), not `unsafe`, no `implemented_by` (each runs code other than its
  definition). An opaque or unsafe constant of program type is a program for E1, E2 and E4.
* E3: in a realisation `RunsWithin I s st₀ c m Q`, no data variable of `I` occurs in `s` or in
  `st₀` (dimensions in `ℕ`, tags and oracle names excepted), and no data variable of the oracle
  or read-only fields of `I` (unfolded to `Interp.mk`) occurs in its tape field, which the
  program reads.
* E4: every `<spec>Prog` has `runsWithin_<spec>Prog` in its namespace.
* E9: a `Builder` program that another program calls closes its allocations: run against a fresh
  continuation, its statement does not reach the continuation under an `alloc` (D11: a buffer is
  freed at the end of the enclosing block, so an open `alloc` stays live for the rest of the
  caller's block). `scope`, `named`, loops and branches close them.

Then the fixtures of the end of this file, which break each rule, must be rejected. Run with
`lake env lean scripts/Programs.lean` after `lake build NLAlib`; a nonzero exit code means a
violation. False positives go in `allowE1`/`allowE3` with a reason. -/

namespace ProgramChecks

/-- The Computation core: syntax and semantics, whose combinators are not programs. -/
def coreModules : List Name :=
  [`NLAlib.Computation.Syntax, `NLAlib.Computation.Exec, `NLAlib.Computation.RunsWithin,
   `NLAlib.Computation.Subst, `NLAlib.Computation.Exact, `NLAlib.Computation.Contract]

/-- Implementation files: an implementation may take host data (E1, D11). -/
def implFiles : List Name := [`NLAlib.Computation.Dense, `NLAlib.Computation.Sparse]

/-- E3 allowlist: (realisation, variable, reason). -/
def allowE3 : List (Name × Name × String) :=
  [(`NLAlib.runsWithin_substOracle_hutchppProg_cooImpl, `pattern,
    "the COO pattern is unrolled into the implementation by design (D14); the values are the oracle's data and do not occur in the program")]

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

/-- E1: the offending binders of a program (or `notGenericInVariables`). -/
def checkE1 (c : Name) : MetaM (List Name) := do
  let info ← getConstInfo c
  forallTelescope info.type fun xs concl => do
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
        return false : MetaM Bool)
      unless ok do bad := d.userName :: bad
    return bad.reverse

/-- Whether a variable of a realisation is data of its interpretation: not a proof, a type, an
instance, a dimension (`ℕ`, shared legitimately), a tag or oracle name (a value of a type
parameter: a name, not data) or a `Dist`. -/
def isDataVar (fv : FVarId) : MetaM Bool := do
  let d ← fv.getDecl
  if (← inferType d.type).isProp || (← isType (.fvar fv)) || d.binderInfo.isInstImplicit then
    return false
  if (← isClass? d.type).isSome then return false
  let t ← whnfR d.type
  return !(t.isConstOf ``Nat || t.isFVar || t.isConstOf ``NLAlib.Computation.Dist)

/-- The tape, oracle and read-only fields of an interpretation, if it unfolds to `Interp.mk`. -/
def interpFields? (I : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let I ← whnf I
  unless I.isAppOf ``NLAlib.Computation.Interp.mk do return none
  let fields := getStructureFields (← getEnv) ``NLAlib.Computation.Interp
  let nParams := I.getAppNumArgs - fields.size
  let field (n : Name) : MetaM Expr := do
    let some i := fields.findIdx? (· == n) | throwError "Interp has no field {n}"
    -- `whnf`: a structure update `{ exactInterp A ξ with rom := … }` keeps the other fields as
    -- projections of `exactInterp A ξ`, which mention all of its arguments
    Core.betaReduce (← whnf (← instantiateMVars I.getAppArgs[nParams + i]!))
  return some (← field `tape, ← field `oracle, ← field `rom)

/-- E3: the data variables of the interpretation of a realisation that occur in its program or
its initial state, or both in its tape and in its oracles or read-only data (or
`notARealisation`). -/
def checkE3 (c : Name) : MetaM (List Name) := do
  let info ← getConstInfo c
  forallTelescope info.type fun _ concl => do
    let concl ← instantiateMVars concl
    unless concl.isAppOf ``NLAlib.Computation.RunsWithin do return [`notARealisation]
    let args := concl.getAppArgs
    let I := args[args.size - 6]!
    let s := args[args.size - 5]!
    let st₀ := args[args.size - 4]!
    let data ← (collectFVars {} I).fvarIds.filterM isDataVar
    let mut bad := []
    for fv in data do
      if s.containsFVar fv || st₀.containsFVar fv then bad := (← fv.getDecl).userName :: bad
    -- the program reads the tape: the oracles' matrices and the read-only data may not be on it
    if let some (tape, oracle, rom) ← interpFields? I then
      for fv in data do
        let n := (← fv.getDecl).userName
        if !bad.contains n && tape.containsFVar fv &&
            (oracle.containsFVar fv || rom.containsFVar fv) then
          bad := n :: bad
    return bad

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
  forallTelescope t fun _ concl => do return (← conclSorts? (← instantiateMVars concl)).isSome

/-- Whether a type concludes `RunsWithin`. -/
def isRealisationType (t : Expr) : MetaM Bool :=
  forallTelescope t fun _ concl => do
    return (← instantiateMVars concl).isAppOf ``NLAlib.Computation.RunsWithin

/-- E4: the name of the missing realisation of a `<spec>Prog`, if any. -/
def checkE4 (env : Environment) (c : Name) : Option Name :=
  match c with
  | .str ns s =>
    if s.endsWith "Prog" && !env.contains (.str ns ("runsWithin_" ++ s)) then
      some (.str ns ("runsWithin_" ++ s)) else none
  | _ => none

end ProgramChecks

open ProgramChecks in
run_cmd do
  let env ← getEnv
  let mut progs : Array Name := #[]
  let mut reals : Array Name := #[]
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
      if ← liftTermElabM (isRealisationType info.type) then reals := reals.push c
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
    if let some r := checkE4 env c then
      bad := bad + 1
      logError m!"E4 {c}: a `<spec>Prog` has its realisation `{r}`"
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
  for c in reals do
    let e3 ← liftTermElabM (checkE3 c)
    let e3 := e3.filter fun v => !allowE3.any fun (c', v', _) => c' == c && v' == v
    unless e3.isEmpty do
      bad := bad + 1
      logError m!"E3 {c}: the program or the initial state uses the oracle's data {e3}"
  logInfo m!"programs: {progs.size} programs and kernels ({callees.size} called by others), {""
    }{reals.size} realisations; {bad} violations"

/-! ## Fixtures: each breaks a rule and must be rejected -/

namespace ProgramChecksFixtures

open NLAlib.Computation

/-- Not generic: a handle forged from a number. -/
def forgeNat (n : ℕ) : Builder Unit Unit ℕ ℕ Unit := Builder.ins (.lit () ⟨n, .const 0⟩ 0)

/-- Generic, but turns index variables into handles through a host function. -/
def forgeFun {VB VI : Type} (f : VI → VB) (n : IExp VI) : Builder Unit Unit VB VI Unit :=
  Builder.forRange n fun i => Builder.ins (.lit () ⟨f i, .var i⟩ 0)

/-- Generic, but takes a host size. -/
def hostSize {VB VI : Type} (b : VB) (n : ℕ) : Builder Unit Unit VB VI Unit :=
  Builder.forRange (.const n) fun i => Builder.ins (.lit () ⟨b, .var i⟩ 0)

/-- A program that cannot run. -/
noncomputable def choiceProg {VB VI : Type} (b : VB) : Builder Unit Unit VB VI Unit :=
  Builder.ins (.lit () ⟨b, .const 0⟩ (Classical.choice ⟨0⟩))

/-- A `<spec>Prog` with no realisation. -/
def orphanProg {VB VI : Type} (b : VB) : Builder Unit Unit VB VI Unit :=
  Builder.ins (.lit () ⟨b, .const 0⟩ 0)

/-- A cheating realisation: `A` is handed to the program in its initial store. -/
theorem runsWithin_cheat {N k ℓ : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (ξ : Dist → ℕ → ℝ) :
    RunsWithin (exactInterp (P := Unit) (ι := Unit) (fun _ => A) ξ)
      ((NLAlib.hutchppProg () () .gaussian (.const N) (.const k) (.const ℓ)
        ⟨0, .const 0⟩).run)
      (inputState () [Array.replicate 1 none, (flatten A).map some]) 0 (fun _ => 0)
      (fun _ => True) := by
  sorry

/-- A cheating realisation through the tape: the program reads `A` from the tape of every
distribution while the oracle holds it too. -/
theorem runsWithin_cheatTape {N k ℓ : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) :
    RunsWithin (exactInterp (P := Unit) (ι := Unit) (fun _ => A)
        (fun _ i => (flatten A).getD i 0))
      ((NLAlib.hutchppProg () () .gaussian (.const N) (.const k) (.const ℓ)
        ⟨0, .const 0⟩).run)
      (inputState () [Array.replicate 1 none]) 0 (fun _ => 0) (fun _ => True) := by
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
  for c in [``ProgramChecksFixtures.choiceProg, ``ProgramChecksFixtures.partialProg] do
    match checkE2 env c with
    | some why => logInfo m!"E2 rejects {c}: {why}"
    | none => logError m!"E2 fixture {c} passes"
  if (← liftTermElabM (isProgType (← getConstInfo ``ProgramChecksFixtures.partialProg).type)) then
    logInfo m!"{``ProgramChecksFixtures.partialProg} is a program for E1, E2 and E4"
  else logError m!"E2 fixture {``ProgramChecksFixtures.partialProg} is not seen as a program"
  if checkE2 env ``NLAlib.hutchppProg |>.isSome then
    logError m!"E2 rejects {``NLAlib.hutchppProg}"
  expect "E3" ``ProgramChecksFixtures.runsWithin_cheat
    (← liftTermElabM (checkE3 ``ProgramChecksFixtures.runsWithin_cheat)) [`A]
  expect "E3" ``ProgramChecksFixtures.runsWithin_cheatTape
    (← liftTermElabM (checkE3 ``ProgramChecksFixtures.runsWithin_cheatTape)) [`A]
  expect "E3" ``NLAlib.runsWithin_hutchppProg
    (← liftTermElabM (checkE3 ``NLAlib.runsWithin_hutchppProg)) []
  match checkE4 env ``ProgramChecksFixtures.orphanProg with
  | some r => logInfo m!"E4 rejects {``ProgramChecksFixtures.orphanProg}: no {r}"
  | none => logError m!"E4 fixture {``ProgramChecksFixtures.orphanProg} passes"
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
