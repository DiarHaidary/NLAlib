import NLAlib
open Lean Meta Elab Command

/-! # Program checks (rules E1 to E4, docs/rules/rules.toml)

The rules of `docs/design/Computation.md` §10 that need Lean's types, checked on every
declaration reachable through `import NLAlib`:

* E1: a program (a definition whose type ends in `Builder` or `Stmt`, outside the Computation
  core) is generic in its two variable sorts, no instance mentions them, and every argument is a
  type, a tag or oracle name (a value of a type parameter), a `Dist`, a handle, an index
  expression, a cell or a program. Host data (`ℕ` sizes, lists, functions) is rejected outside the
  implementation files (`implFiles`).
* E2: programs, kernels and implementations are computable.
* E3: in a realisation `RunsWithin I s st₀ c m Q`, no data variable of `I` occurs in `s` or in
  `st₀` (dimensions in `ℕ`, tags and oracle names excepted).
* E4: every `<spec>Prog` has `runsWithin_<spec>Prog` in its namespace.

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

/-- E3: the data variables of the interpretation of a realisation that occur in its program or
its initial state (or `notARealisation`). -/
def checkE3 (c : Name) : MetaM (List Name) := do
  let info ← getConstInfo c
  forallTelescope info.type fun _ concl => do
    let concl ← instantiateMVars concl
    unless concl.isAppOf ``NLAlib.Computation.RunsWithin do return [`notARealisation]
    let args := concl.getAppArgs
    let I := args[args.size - 6]!
    let s := args[args.size - 5]!
    let st₀ := args[args.size - 4]!
    let mut bad := []
    for fv in (collectFVars {} I).fvarIds do
      let d ← fv.getDecl
      if (← inferType d.type).isProp || (← isType (.fvar fv)) || d.binderInfo.isInstImplicit then
        continue
      if (← isClass? d.type).isSome then continue
      let t ← whnfR d.type
      -- dimensions are shared legitimately; tags and oracle names are names, not data
      if t.isConstOf ``Nat || t.isFVar || t.isConstOf ``NLAlib.Computation.Dist then continue
      if s.containsFVar fv || st₀.containsFVar fv then bad := d.userName :: bad
    return bad

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
    | .defnInfo _ =>
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
    if isNoncomputable env c then
      bad := bad + 1
      logError m!"E2 {c}: a program, kernel or implementation is computable; this one is not"
    if let some r := checkE4 env c then
      bad := bad + 1
      logError m!"E4 {c}: a `<spec>Prog` has its realisation `{r}`"
  for c in reals do
    let e3 ← liftTermElabM (checkE3 c)
    let e3 := e3.filter fun v => !allowE3.any fun (c', v', _) => c' == c && v' == v
    unless e3.isEmpty do
      bad := bad + 1
      logError m!"E3 {c}: the program or the initial state uses the oracle's data {e3}"
  logInfo m!"programs: {progs.size} programs and kernels, {reals.size} realisations; {bad} violations"

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
  if isNoncomputable env ``ProgramChecksFixtures.choiceProg then
    logInfo m!"E2 rejects {``ProgramChecksFixtures.choiceProg}"
  else logError m!"E2 fixture {``ProgramChecksFixtures.choiceProg} passes"
  expect "E3" ``ProgramChecksFixtures.runsWithin_cheat
    (← liftTermElabM (checkE3 ``ProgramChecksFixtures.runsWithin_cheat)) [`A]
  expect "E3" ``NLAlib.runsWithin_hutchppProg
    (← liftTermElabM (checkE3 ``NLAlib.runsWithin_hutchppProg)) []
  match checkE4 env ``ProgramChecksFixtures.orphanProg with
  | some r => logInfo m!"E4 rejects {``ProgramChecksFixtures.orphanProg}: no {r}"
  | none => logError m!"E4 fixture {``ProgramChecksFixtures.orphanProg} passes"
