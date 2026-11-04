import NLAlib
open Lean Meta Elab Command

/-! # Program checks (rules E2, E4 and E9, docs/rules/rules.toml)

A published cost result is the proof of a registered target (`docs/targets.toml`), checked by
`scripts/Targets.lean` (rule E3): a theorem whose type is a library `Prop` about a registered
first-order tree, so the program is fixed, scoped by its type and frozen with the statement
(`docs/design/Computation.md`, "First-order programs and target statements", F1 and F9). The
checks here are what is left, on every declaration reachable through `import NLAlib`:

* E2 (hygiene): programs, kernels, implementations and compiled trees are computable: not
  `noncomputable`, not opaque (`partial`, `opaque`), not `unsafe`, no `implemented_by` (each runs
  code other than its definition). An opaque or unsafe constant of program type is a program for
  E2 and E4. It matters for the emitter and the `Float` runner only.
* E4 (completeness, not soundness): every `<spec>Prog` has a registered tree, named by a
  registered target in `docs/targets.toml`, whose definition calls it. That every registered
  target is proved is E3.
* E9 (a warning): a `Builder` program that another program calls closes its allocations: run
  against a fresh continuation, its statement does not reach the continuation under an `alloc`
  (D11: a buffer is freed at the end of the enclosing block, so an open `alloc` stays live, and
  counted, for the rest of the caller's block). `scope`, `named`, loops and branches close them.
  Memory is the target's `mem`, so a leaking callee makes a proof fail or a target larger, never a
  claim false.

E1 (programs generic in their variable sorts) is retired: the witness is a first-order tree, and
a builder that is not generic still compiles to one tree, which is what the theorem is about. A
forged handle does not compile (the fixture `forgeNat` below). Then the fixtures of the end of
this file, which break each rule, must be rejected. Run with `lake env lean scripts/Programs.lean`
after `lake build NLAlib`; a nonzero exit code means a violation. -/

namespace ProgramChecks

/-- The Computation core: syntax, semantics, budgets, substitution, compilation, exact
arithmetic, contracts and the access models, whose combinators (`ProgFamily.inst`,
`ProgFamily.substOracle`, `ProgFamily.compile`) are not programs. -/
def coreModules : List Name :=
  [`NLAlib.Computation.Syntax, `NLAlib.Computation.Store, `NLAlib.Computation.Exec,
   `NLAlib.Computation.RunsWithin, `NLAlib.Computation.Compile, `NLAlib.Computation.FirstOrder,
   `NLAlib.Computation.Subst, `NLAlib.Computation.Exact, `NLAlib.Computation.Contract,
   `NLAlib.Computation.Model]

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

/-- Whether a type is a first-order program type (`FStmt`, `Prog`): a compiled tree. -/
def isTreeType (t : Expr) : MetaM Bool :=
  forallTelescope t fun _ concl => do
    return (← whnfR (← instantiateMVars concl)).isAppOfArity ``NLAlib.Computation.FStmt 4

/-- Whether a type is a program type: a builder, a statement, a program family, or a
first-order program (`FStmt`, `Prog`). -/
def isProgType (t : Expr) : MetaM Bool := do
  if ← isTreeType t then return true
  progTelescope t fun _ concl => do return (← conclSorts? (← instantiateMVars concl)).isSome

/-- The registered trees: those that a registered target of `docs/targets.toml` names (its
`trees = [...]` lists). -/
def registeredTrees (path : System.FilePath := "docs/targets.toml") : IO (List Name) := do
  let text ← IO.FS.readFile path
  return List.eraseDups <| (text.splitOn "\n").flatMap fun l =>
    if l.startsWith "trees = [" then
      ((l.splitOn "\"").toArray.toList.zipIdx.filterMap fun (x, i) =>
        if i % 2 == 1 then some x.toName else none)
    else []

/-- E4: whether a `<spec>Prog` has no registered tree whose definition calls it. -/
def checkE4 (env : Environment) (trees : List Name) (c : Name) : Bool :=
  match c with
  | .str _ s =>
    s.endsWith "Prog" && !trees.any fun t =>
      ((env.find? t).bind (·.value?) |>.map (·.getUsedConstants.contains c)).getD false
  | _ => false

end ProgramChecks

open ProgramChecks in
run_cmd do
  let env ← getEnv
  let trees ← registeredTrees
  let mut progs : Array Name := #[]
  let mut bad : Nat := 0
  for (c, info) in env.constants.map₁.toList do
    let some m := moduleOf env c | continue
    unless (`NLAlib).isPrefixOf m do continue
    if isAux env c || coreModules.contains m then continue
    match info with
    | .defnInfo _ | .opaqueInfo _ =>
      if ← liftTermElabM (isProgType info.type) then progs := progs.push c
    | _ => pure ()
  for c in progs do
    if let some why := checkE2 env c then
      bad := bad + 1
      logError m!"E2 {c}: a program, kernel, implementation or tree is computable; {""
        }this one is {why}"
    if checkE4 env trees c then
      bad := bad + 1
      logError m!"E4 {c}: a `<spec>Prog` has a registered tree in docs/targets.toml, named by a {""
        }registered target, whose definition calls it"
  -- E9 on the callees: the programs that occur in another program's definition (a compiled
  -- tree runs its builder once, at the top, so it is not a caller)
  let mut callees : NameSet := {}
  for c in progs do
    if ← liftTermElabM (isTreeType (← getConstInfo c).type) then continue
    if let some v := (env.find? c).bind (·.value?) then
      for d in v.getUsedConstants do
        if d != c && progs.contains d then callees := callees.insert d
  let mut leaks : Nat := 0
  for c in progs do
    unless callees.contains c do continue
    match ← liftTermElabM (checkE9 c) with
    | some true =>
      leaks := leaks + 1
      logWarning m!"E9 {c}: a program called by another program frees its allocations; wrap {""
        }them in `scope` (a warning: memory is the target's `mem`)"
    | some false => pure ()
    | none => logWarning m!"E9 {c}: the spine of this callee cannot be followed; not checked"
  logInfo m!"programs: {progs.size} programs, kernels and trees ({callees.size} called by {""
    }others), {trees.length} registered trees; {bad} violations, {leaks} E9 warnings"

/-! ## Fixtures: each breaks a rule and must be rejected -/

namespace ProgramChecksFixtures

open NLAlib.Computation

/-- A handle forged from a number: it does not compile (E1 is retired; the compiler rejects a
handle out of scope). -/
def forgeNat (n : ℕ) : Stmt Unit Unit ℕ ℕ := (Builder.ins (.lit () ⟨n, .const 0⟩ 0)).run

example : (forgeNat 5).compile 1 1 = none := rfl
example : ((forgeNat 0).compile 1 1).isSome = true := rfl

/-- A program that cannot run. -/
noncomputable def choiceProg {VB VI : Type} (b : VB) : Builder Unit Unit VB VI Unit :=
  Builder.ins (.lit () ⟨b, .const 0⟩ (Classical.choice ⟨0⟩))

/-- A `<spec>Prog` with no registered tree. -/
def orphanProg {VB VI : Type} (b : VB) : Builder Unit Unit VB VI Unit :=
  Builder.ins (.lit () ⟨b, .const 0⟩ 0)

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
  for c in [``ProgramChecksFixtures.choiceProg, ``ProgramChecksFixtures.partialProg] do
    match checkE2 env c with
    | some why => logInfo m!"E2 rejects {c}: {why}"
    | none => logError m!"E2 fixture {c} passes"
  if (← liftTermElabM (isProgType (← getConstInfo ``ProgramChecksFixtures.partialProg).type)) then
    logInfo m!"{``ProgramChecksFixtures.partialProg} is a program for E2 and E4"
  else logError m!"E2 fixture {``ProgramChecksFixtures.partialProg} is not seen as a program"
  if checkE2 env ``NLAlib.hutchppProg |>.isSome then
    logError m!"E2 rejects {``NLAlib.hutchppProg}"
  let trees ← registeredTrees
  if checkE4 env trees ``ProgramChecksFixtures.orphanProg then
    logInfo m!"E4 rejects {``ProgramChecksFixtures.orphanProg}: no registered tree"
  else logError m!"E4 fixture {``ProgramChecksFixtures.orphanProg} passes"
  for c in [``NLAlib.hutchppProg, ``NLAlib.gramSchmidtProg] do
    if checkE4 env trees c then logError m!"E4 rejects {c}"
    else logInfo m!"E4 accepts {c}"
  let e9 (c : Name) (want : Bool) : CommandElabM Unit := do
    let got ← liftTermElabM (checkE9 c)
    if got == some want then
      logInfo (if want then m!"E9 flags {c}" else m!"E9 accepts {c}")
    else logError m!"E9 fixture {c}: expected {want}, got {got}"
  e9 ``ProgramChecksFixtures.leakyCallee true
  e9 ``ProgramChecksFixtures.closedCallee false
  e9 ``NLAlib.gramSchmidtProg false
  e9 ``NLAlib.orthAgainst false
  e9 ``NLAlib.Computation.dot false
  e9 ``NLAlib.hutchppProg true
