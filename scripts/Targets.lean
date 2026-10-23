import NLAlib
open Lean Meta Elab Command

/-! # Target checks (rule E3, docs/rules/rules.toml)

A published cost result is a theorem whose type is a **target**, a library definition of type
`Prop` registered in `docs/targets.toml` (`docs/design/Computation.md`, "First-order programs and
target statements", F1 and F12). This script checks, on the library built by `lake build NLAlib`:

1. every registered target is a `Prop` definition in its registered `*Targets.lean` file, and has
   exactly one proof: a theorem (not an axiom, not an opaque) whose type is the target constant
   itself, syntactically, with no binder;
2. every theorem outside `NLAlib/Computation` with a `Result:` id whose statement reaches a run or
   a budget (the models, `Prog.exec`, `FStmt.exec`, `Prog.RunsWithin`, `RunsWithin`, `exec`,
   `Stmt`, `ProgFamily.inst`), through the library definitions it unfolds to, is the proof of a
   registered target;
3. the **closure hash** of each target matches the registry: SHA-256 of a canonical serialisation
   of every library constant the target's statement reaches (a constant is a library constant if
   its module is an `NLAlib` module), of every kind: definitions and opaques (type and value),
   theorems, axioms and quotients (type), inductive types (type, parameters, indices, mutual
   block, constructors), constructors and recursors (type). A registered tree is a leaf, hashed by
   its constructor normal form (`Meta.reduce`), which must contain no library definition; the
   printed statement (the target unfolded one level) matches the registry too;
4. the Lean toolchain and the Mathlib revision of `lake-manifest.json` are the registry's;
5. (Q5) a target whose declared inputs are not `Array.replicate _ none` or built from the declared
   data carries the registry flag `precomputed` and the docstring marker `Precomputed:`;
6. (Q3) `docs/targets.approved` holds the SHA-256 of `docs/targets.toml`
   (`sha256sum docs/targets.toml > docs/targets.approved`, by the maintainer only).

Then the fixtures at the end of this file, on copies of a target, must be rejected or detected.

Run with `lake env lean scripts/Targets.lean` after `lake build NLAlib`; a nonzero exit code
means a violation. `TARGETS_UPDATE=1 lake env lean scripts/Targets.lean` (the `--update` mode)
rewrites the hashes, the printed statements and the pins of the registry for review; it never
writes `docs/targets.approved`. Agents never edit the registry or a `*Targets.lean` file
(CONTRIBUTING §11). `TARGETS_REGISTRY` and `TARGETS_APPROVED` name other files (for tests). -/

namespace TargetChecks

/-! ## Hashing -/

/-- The SHA-256 of a file, in hex, by `sha256sum` or `shasum -a 256`. -/
def sha256File (p : System.FilePath) : IO String := do
  for (cmd, args) in [("sha256sum", #[p.toString]), ("shasum", #["-a", "256", p.toString])] do
    try
      let out ← IO.Process.output { cmd, args }
      if out.exitCode == 0 then
        if let some h := (out.stdout.splitOn " ").head? then return h.trimAscii.toString
    catch _ => pure ()
  throw <| IO.userError "neither sha256sum nor shasum is available"

/-- The SHA-256 of a string, in hex. -/
def sha256 (s : String) : IO String := do
  let (h, path) ← IO.FS.createTempFile
  h.putStr s
  h.flush
  let r ← sha256File path
  IO.FS.removeFile path
  return r

/-- The state of a canonical serialisation: each distinct subterm once, as a line naming its
children by number, so that a term with sharing is serialised in linear size. Binder names and
binder annotations are left out (alpha-equivalent terms serialise alike), as is metadata. -/
structure Ser where
  ids : Std.HashMap Expr Nat := {}
  lines : Array String := #[]

/-- Append a line; its number. -/
def emit (line : String) : StateM Ser Nat :=
  modifyGet fun s => (s.lines.size, { s with lines := s.lines.push line })

/-- Serialise an expression whose equal subterms are shared; the number of its line. -/
partial def serShared (e : Expr) : StateM Ser Nat := do
  if let some i := (← get).ids[e]? then return i
  let i ← match e with
    | .bvar k => emit s!"b {k}"
    | .fvar f => emit s!"f {f.name}"
    | .mvar m => emit s!"m {m.name}"
    | .sort u => emit s!"s {u}"
    | .const n us => emit s!"c {n} {us}"
    | .app f a => do let f ← serShared f; let a ← serShared a; emit s!"a {f} {a}"
    | .lam _ t b _ => do let t ← serShared t; let b ← serShared b; emit s!"l {t} {b}"
    | .forallE _ t b _ => do let t ← serShared t; let b ← serShared b; emit s!"p {t} {b}"
    | .letE _ t v b _ => do
      let t ← serShared t; let v ← serShared v; let b ← serShared b; emit s!"z {t} {v} {b}"
    | .lit (.natVal n) => emit s!"n {n}"
    | .lit (.strVal s) => emit s!"t {s.quote}"
    | .mdata _ b => serShared b
    | .proj s k b => do let b ← serShared b; emit s!"j {s} {k} {b}"
  modify fun s => { s with ids := s.ids.insert e i }
  return i

/-- Serialise an expression; the number of its line. Equal subterms are made pointer-equal
first, so that the table's comparisons stop at the pointer. -/
def serExpr (e : Expr) : StateM Ser Nat := serShared (ShareCommon.shareCommon' e)

/-- Serialise one constant of a closure: its kind, name, universe parameters, type, and what
else its kind carries (a registered tree: its normal form instead of its value). -/
def serConst (c : Name) (info : ConstantInfo) (tree : Option Expr) : StateM Ser Unit := do
  let ty ← serExpr info.type
  let head := s!"{c} {info.levelParams} {ty} {info.isUnsafe} {info.isPartial}"
  let line ← match tree, info with
    | some nf, _ => do pure s!"# tree {head} {← serExpr nf}"
    | none, .defnInfo d => do pure s!"# def {head} {← serExpr d.value}"
    | none, .opaqueInfo d => do pure s!"# opaque {head} {← serExpr d.value}"
    | none, .thmInfo _ => pure s!"# theorem {head}"
    | none, .axiomInfo _ => pure s!"# axiom {head}"
    | none, .quotInfo _ => pure s!"# quot {head}"
    | none, .inductInfo d =>
      pure s!"# inductive {head} {d.numParams} {d.numIndices} {d.all} {d.ctors} {d.isRec}"
    | none, .ctorInfo d =>
      pure s!"# ctor {head} {d.induct} {d.cidx} {d.numParams} {d.numFields}"
    | none, .recInfo _ => pure s!"# rec {head}"
  discard <| emit line

/-! ## Library constants and the closure walk -/

/-- The module of a constant. -/
def moduleOf (env : Environment) (c : Name) : Option Name :=
  (env.getModuleIdxFor? c).map fun i => env.header.moduleNames[i.toNat]!

/-- A library constant: its module is an `NLAlib` module (ForMathlib included, whatever its
namespace), or it is declared in the current file (the fixtures). -/
def isLibConst (env : Environment) (c : Name) : Bool :=
  match moduleOf env c with
  | some m => (`NLAlib).isPrefixOf m
  | none => (env.find? c).isSome

/-- The closure of a target: every library constant its statement reaches, sorted by name, and
the names reached that the environment does not know (an error). The walk follows the type of
every constant, the value of definitions and opaques (an `irreducible_def` is an opaque whose
type names the definition holding the value), the mutual block and the constructors of inductive
types. A registered tree (`trees`) is a leaf: the walk follows its type and its normal form, not
its definition. `override` replaces a constant's information, for the fixtures. -/
def closure (env : Environment) (override : Name → Option ConstantInfo)
    (trees : Name → Option Expr) (root : Name) : Array Name × Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut out : Array Name := #[]
  let mut missing : Array Name := #[]
  let mut todo : List Name := [root]
  while !todo.isEmpty do
    let c := todo.head!
    todo := todo.tail!
    if seen.contains c then continue
    seen := seen.insert c
    let some info := (override c).orElse fun _ => env.find? c
      | missing := missing.push c; continue
    unless isLibConst env c do continue
    out := out.push c
    let mut next := info.type.getUsedConstants.toList
    if let some nf := trees c then
      next := next ++ nf.getUsedConstants.toList
    else match info with
      | .defnInfo d => next := next ++ d.value.getUsedConstants.toList
      | .opaqueInfo d => next := next ++ d.value.getUsedConstants.toList
      | .inductInfo d => next := next ++ d.all ++ d.ctors
      | _ => pure ()
    todo := next ++ todo
  return (out.qsort (toString · < toString ·), missing)

/-- The closure hash: SHA-256 of the serialisation of the closure's constants, in name order. -/
def closureHash (env : Environment) (override : Name → Option ConstantInfo)
    (trees : Name → Option Expr) (names : Array Name) : IO String := do
  let ser : StateM Ser Unit := names.forM fun c =>
    match (override c).orElse fun _ => env.find? c with
    | some info => serConst c info (trees c)
    | none => pure ()
  sha256 ("\n".intercalate (ser.run {}).2.lines.toList)

/-- The library definitions and opaques a term contains outside its types and proofs. -/
partial def valueDefs (e : Expr) : MetaM (Array Name) := do
  let env ← getEnv
  let rec go (e : Expr) (acc : Array Name) : MetaM (Array Name) := do
    if !e.hasLooseBVars && !e.hasMVar then
      if (← isProof e) || (← isType e) then return acc
    match e with
    | .const n _ =>
      return match env.find? n with
        | some (.defnInfo _) | some (.opaqueInfo _) =>
          if isLibConst env n && !acc.contains n then acc.push n else acc
        | _ => acc
    | .app f a => go a (← go f acc)
    | .lam _ t b _ | .forallE _ t b _ => go b (← go t acc)
    | .letE _ t v b _ => go b (← go v (← go t acc))
    | .mdata _ b | .proj _ _ b => go b acc
    | _ => return acc
  go e #[]

/-- **The constructor normal form of a registered tree**: its value fully reduced (types and
proofs kept as they are), and the library definitions it still contains outside types and proofs
(none, for a tree built from constructors). -/
def treeNF (c : Name) : MetaM (Expr × Array Name) := do
  let some (.defnInfo d) := (← getEnv).find? c | throwError "{c} is not a definition"
  let v ← Meta.reduce d.value (explicitOnly := false) (skipTypes := true) (skipProofs := true)
  let v ← instantiateMVars v
  let defs ← lambdaTelescope v fun _ body => valueDefs body
  return (v, defs)

/-- The hash of a registered tree: its type and its normal form. -/
def treeHash (c : Name) (nf : Expr) : MetaM String := do
  let some info := (← getEnv).find? c | throwError "{c} is unknown"
  sha256 ("\n".intercalate ((serConst c info (some nf)).run {}).2.lines.toList)

/-! ## The lint -/

/-- Lint item 1: `thm` is a theorem (not an axiom, not an opaque) whose type is the target
constant, syntactically, with no binder. -/
def provesTarget (env : Environment) (thm tgt : Name) : Bool :=
  match env.find? thm with
  | some (.thmInfo t) => t.type == .const tgt []
  | _ => false

/-- The constants whose type is the target constant, with their kind (`theorem`, `axiom`, …). -/
def candidates (consts : Array (Name × ConstantInfo)) (tgt : Name) : Array (Name × String) :=
  consts.filterMap fun (c, info) =>
    if info.type == .const tgt [] then
      some (c, match info with
        | .thmInfo _ => "theorem" | .axiomInfo _ => "axiom" | .opaqueInfo _ => "opaque"
        | .defnInfo _ => "definition" | _ => "constant")
    else none

/-- The constants that make a statement about a program's runs or budgets (lint item 2). -/
def runConsts : List Name :=
  [``NLAlib.Computation.MatrixFree, ``NLAlib.Computation.StoredEntries,
   ``NLAlib.Computation.MatrixFreeProb, ``NLAlib.Computation.Prog.exec,
   ``NLAlib.Computation.FStmt.exec, ``NLAlib.Computation.Prog.RunsWithin,
   ``NLAlib.Computation.RunsWithin, ``NLAlib.Computation.exec, ``NLAlib.Computation.Stmt,
   ``NLAlib.Computation.ProgFamily.inst, ``NLAlib.Computation.ProgFamily.MatrixFree,
   ``NLAlib.Computation.ProgFamily.StoredEntries, ``NLAlib.Computation.ProgFamily.MatrixFreeProb]

/-- Whether a constant reaches a run or a budget through the library constants it unfolds to
(memoised; Mathlib constants reach none). -/
partial def reachesRun (env : Environment) (c : Name) : StateM (Std.HashMap Name Bool) Bool := do
  if runConsts.contains c then return true
  if let some b := (← get)[c]? then return b
  modify (·.insert c false)
  let some info := env.find? c | return false
  unless isLibConst env c do return false
  let mut next := info.type.getUsedConstants
  match info with
  | .defnInfo d => next := next ++ d.value.getUsedConstants
  | .opaqueInfo d => next := next ++ d.value.getUsedConstants
  | _ => pure ()
  let mut r := false
  for d in next do
    if ← reachesRun env d then r := true; break
  modify (·.insert c r)
  return r

/-- Lint item 2: the theorems in `scope` outside `NLAlib/Computation` with a `Result:` id whose
statement reaches a run or a budget and that prove no registered target. -/
def unregisteredResults (env : Environment) (scope : Array (Name × ConstantInfo))
    (proofs : NameSet) : IO (Array Name) := do
  let mut memo : Std.HashMap Name Bool := {}
  let mut out := #[]
  for (c, info) in scope do
    let .thmInfo _ := info | continue
    if proofs.contains c then continue
    if (moduleOf env c).any (`NLAlib.Computation).isPrefixOf then continue
    let some doc ← findDocString? env c | continue
    unless (doc.splitOn "Result:").length > 1 do continue
    let (r, m) := (info.type.getUsedConstants.anyM (reachesRun env)).run memo
    memo := m
    if r then out := out.push c
  return out

/-- The models on `Prog` a target concludes. -/
def models : List Name :=
  [``NLAlib.Computation.MatrixFree, ``NLAlib.Computation.StoredEntries,
   ``NLAlib.Computation.MatrixFreeProb]

/-- The entries of a vector literal `![a, b, …]`, or the term itself. -/
partial def vecEntries (e : Expr) : List Expr :=
  if e.isAppOfArity ``Matrix.vecCons 4 then e.getArg! 2 :: vecEntries (e.getArg! 3)
  else if e.isAppOf ``Matrix.vecEmpty then []
  else [e]

/-- Q5: whether a target's declared inputs are computed from the sizes: an entry that is
neither `Array.replicate _ none` nor built from the declared data. `none` if the target does
not conclude a model on `Prog`. -/
def precomputedInputs (tgt : Name) : MetaM (Option Bool) := do
  let some (.defnInfo d) := (← getEnv).find? tgt | return none
  forallTelescope d.value fun _ concl => do
    let concl ← instantiateMVars concl
    let some m := models.find? concl.isAppOf | return none
    let idx ← forallTelescope (← getConstInfo m).type fun xs _ => do
      xs.findIdxM? fun x => return (← x.fvarId!.getDecl).userName == `inputs
    let some idx := idx | return none
    let some inputs := concl.getAppArgs[idx]? | return none
    lambdaTelescope inputs fun xs body => do
      let data := xs[2]?
      let ok (e : Expr) : Bool :=
        (e.isAppOf ``Array.replicate && e.appArg!.isAppOf ``Option.none) ||
          data.any fun x => e.containsFVar x.fvarId!
      return some !((vecEntries (← instantiateMVars body)).all ok)

/-- The statement of a target, printed: its value (the target unfolded one level). -/
def printStatement (tgt : Name) : MetaM String := do
  let some (.defnInfo d) := (← getEnv).find? tgt | throwError "{tgt} is not a definition"
  let f ← ppExpr d.value
  return "\n".intercalate ((f.pretty 100).splitOn "\n" |>.map fun l => l.trimAsciiEnd.toString)

/-! ## The registry -/

/-- A value of the registry: a string, a list of strings, a multi-line literal. -/
inductive Val where
  | str (s : String)
  | list (xs : List String)
  | multi (s : String)
  deriving BEq, Inhabited

/-- A `[[tree]]` or `[[target]]` table. -/
structure Table where
  kind : String
  fields : Array (String × Val) := #[]
  deriving Inhabited

/-- The registry: its leading comment, its top-level keys and its tables, in order. -/
structure Registry where
  header : Array String := #[]
  top : Array (String × Val) := #[]
  tables : Array Table := #[]
  deriving Inhabited

/-- A field of a table, or a top-level key. -/
def getField (fs : Array (String × Val)) (k : String) : Option Val :=
  (fs.find? (·.1 == k)).map (·.2)

/-- A string field (empty if absent). -/
def getStr (fs : Array (String × Val)) (k : String) : String :=
  match getField fs k with | some (.str s) | some (.multi s) => s | _ => ""

/-- A list field (empty if absent). -/
def getList (fs : Array (String × Val)) (k : String) : List String :=
  match getField fs k with | some (.list xs) => xs | _ => []

/-- Set a field, in place or at the end. -/
def setField (fs : Array (String × Val)) (k : String) (v : Val) : Array (String × Val) :=
  if fs.any (·.1 == k) then fs.map fun (k', v') => (k', if k' == k then v else v')
  else fs.push (k, v)

/-- A double-quoted string with no escapes. -/
def unquote (s : String) : Option String :=
  if s.length ≥ 2 && s.startsWith "\"" && s.endsWith "\"" then
    let t := ((s.drop 1).dropEnd 1).toString
    if t.any (fun c => c == '"' || c == '\\') then none else some t
  else none

/-- Parse the registry (the subset of TOML it is written in: comments, `key = "string"`,
`key = ["a", "b"]`, `key = '''` multi-line literals, `[[table]]` headers). -/
def parseRegistry (text : String) : Except String Registry := do
  let lines := (text.splitOn "\n").toArray
  let mut reg : Registry := {}
  let mut cur : Option Table := none
  let mut inHeader := true
  let mut i := 0
  while i < lines.size do
    let l := lines[i]!
    i := i + 1
    let t := l.trimAscii.toString
    if t.isEmpty || t.startsWith "#" then
      if inHeader && !t.isEmpty then reg := { reg with header := reg.header.push l }
      continue
    inHeader := false
    if t.startsWith "[[" && t.endsWith "]]" then
      if let some tb := cur then reg := { reg with tables := reg.tables.push tb }
      cur := some { kind := ((t.drop 2).dropEnd 2).trimAscii.toString }
      continue
    let kv := t.splitOn " = "
    let some k := kv.head? | throw s!"line {i}: expected `key = value`"
    let v := " = ".intercalate kv.tail
    if kv.length < 2 then throw s!"line {i}: expected `key = value`"
    let val ← if v == "'''" then do
        let mut body : Array String := #[]
        let mut closed := false
        while i < lines.size && !closed do
          let m := lines[i]!
          i := i + 1
          if m.endsWith "'''" then body := body.push (m.dropEnd 3).toString; closed := true
          else body := body.push m
        unless closed do throw s!"line {i}: unterminated '''"
        pure (Val.multi ("\n".intercalate body.toList))
      else if v.startsWith "[" && v.endsWith "]" then do
        let inner := ((v.drop 1).dropEnd 1).trimAscii.toString
        let items := if inner.isEmpty then [] else
          (inner.splitOn ",").map fun x => x.trimAscii.toString
        let xs ← items.mapM fun x => match unquote x with
          | some s => pure s | none => throw s!"line {i}: expected a quoted string, got {x}"
        pure (Val.list xs)
      else match unquote v with
        | some s => pure (Val.str s)
        | none => throw s!"line {i}: expected a quoted string, a list or '''"
    match cur with
    | some tb => cur := some { tb with fields := tb.fields.push (k, val) }
    | none => reg := { reg with top := reg.top.push (k, val) }
  if let some tb := cur then reg := { reg with tables := reg.tables.push tb }
  return reg

/-- A value, as written. -/
def Val.render : Val → String
  | .str s => "\"" ++ s ++ "\""
  | .list xs => "[" ++ ", ".intercalate (xs.map fun x => "\"" ++ x ++ "\"") ++ "]"
  | .multi s => "'''\n" ++ s ++ "'''"

/-- The registry, as written. -/
def Registry.render (reg : Registry) : String :=
  let kv (fs : Array (String × Val)) := fs.toList.map fun (k, v) => s!"{k} = {v.render}"
  "\n".intercalate (reg.header.toList ++ kv reg.top ++
    reg.tables.toList.flatMap fun tb => [""] ++ [s!"[[{tb.kind}]]"] ++ kv tb.fields) ++ "\n"

/-! ## Checking the registry -/

/-- The toolchain and the Mathlib revision of the build. -/
def buildPins : IO (String × String) := do
  let toolchain := "leanprover/lean4:v" ++ Lean.versionString
  let file := (← IO.FS.readFile "lean-toolchain").trimAscii.toString
  if file != toolchain then
    throw <| IO.userError s!"lean-toolchain says {file}, the running Lean is {toolchain}"
  let manifest ← IO.ofExcept <| Json.parse (← IO.FS.readFile "lake-manifest.json")
  let pkgs ← IO.ofExcept <| manifest.getObjValAs? (Array Json) "packages"
  let some m := pkgs.find? fun p => (p.getObjValAs? String "name").toOption == some "mathlib"
    | throw <| IO.userError "lake-manifest.json has no mathlib"
  return (toolchain, ← IO.ofExcept (m.getObjValAs? String "rev"))

/-- Item 4: the registry's pins against the build's. -/
def pinErrors (reg : Registry) (toolchain mathlib : String) : Array String :=
  (if getStr reg.top "toolchain" == toolchain then #[] else
    #[s!"the registry pins toolchain {getStr reg.top "toolchain"}, the build is {toolchain}"]) ++
  (if getStr reg.top "mathlib" == mathlib then #[] else
    #[s!"the registry pins Mathlib {getStr reg.top "mathlib"}, lake-manifest.json has {mathlib}"])

/-- Check the registry against the environment. `proofScope`: the constants that may prove a
target; `resultScope`: the theorems lint item 2 reads. Returns the violations and the registry
with its hashes, printed statements and pins recomputed (written by `--update`). -/
def checkRegistry (reg : Registry) (proofScope resultScope : Array (Name × ConstantInfo))
    (pins : String × String) (override : Name → Option ConstantInfo := fun _ => none) :
    MetaM (Array String × Registry) := do
  let env ← getEnv
  let mut errs : Array String := (pinErrors reg pins.1 pins.2).map ("E3 " ++ ·)
  let mut out := { reg with
    top := setField (setField reg.top "toolchain" (.str pins.1)) "mathlib" (.str pins.2) }
  -- the registered trees, by their normal forms
  let mut nfs : Std.HashMap Name Expr := {}
  let mut tables : Array Table := #[]
  for tb in reg.tables do
    let name := (getStr tb.fields "name").toName
    if tb.kind == "tree" then
      unless env.contains name do
        errs := errs.push s!"E3 registered tree {name} is not in the library"
        tables := tables.push tb; continue
      let (nf, defs) ← treeNF name
      unless defs.isEmpty do
        errs := errs.push s!"E3 registered tree {name}: its normal form still contains the {""
          }library definitions {defs}; a registered tree is built from constructors"
      nfs := nfs.insert name nf
      let h ← treeHash name nf
      if h != getStr tb.fields "hash" then
        errs := errs.push s!"E3 registered tree {name}: normal-form hash {h}, the registry has {""
          }{getStr tb.fields "hash"}; a change of a tree needs the maintainer's approval"
      tables := tables.push { tb with fields := setField tb.fields "hash" (.str h) }
    else tables := tables.push tb
  let mut proofs : NameSet := {}
  let mut used : NameSet := {}
  let mut tables' : Array Table := #[]
  for tb in tables do
    if tb.kind != "target" then tables' := tables'.push tb; continue
    let tgt := (getStr tb.fields "name").toName
    let some info := env.find? tgt
      | errs := errs.push s!"E3 registered target {tgt} is not in the library"
        tables' := tables'.push tb; continue
    -- item 1: a `Prop` definition in its `*Targets.lean` file, with exactly one proof
    unless info matches .defnInfo _ && info.type == .sort 0 && info.levelParams.isEmpty do
      errs := errs.push s!"E3 target {tgt} is not a definition of type `Prop`"
    let file := getStr tb.fields "file"
    if let some m := moduleOf env tgt then
      let path := "/".intercalate (m.components.map toString) ++ ".lean"
      unless path == file && file.endsWith "Targets.lean" do
        errs := errs.push s!"E3 target {tgt} is in {path}; the registry says {file} {""
          }(a target lives in a `<Topic>/<Spec>Targets.lean` file)"
    match candidates proofScope tgt with
    | #[(thm, "theorem")] =>
      proofs := proofs.insert thm
    | #[] => errs := errs.push s!"E3 target {tgt} has no proof (a theorem whose type is {tgt})"
    | cs => errs := errs.push s!"E3 target {tgt} must have exactly one proof, a theorem; {""
        }found {cs.toList}"
    -- its trees
    let trees := getList tb.fields "trees"
    for t in trees do
      used := used.insert t.toName
      unless nfs.contains t.toName do
        errs := errs.push s!"E3 target {tgt} names {t}, which is not a registered tree"
      unless (info.value?.map (·.getUsedConstants.contains t.toName)).getD false do
        errs := errs.push s!"E3 target {tgt} lists the tree {t}, which its statement does not name"
    -- item 3: the closure hash and the printed statement
    let (names, missing) := closure env override (nfs.get? ·) tgt
    unless missing.isEmpty do
      errs := errs.push s!"E3 target {tgt}: its closure reaches the unknown constants {missing}"
    let h ← closureHash env override (nfs.get? ·) names
    if h != getStr tb.fields "hash" then
      errs := errs.push s!"E3 target {tgt}: closure hash {h} ({names.size} constants), the {""
        }registry has {getStr tb.fields "hash"}; the target or a definition it unfolds to changed"
    let stmt ← printStatement tgt
    if stmt != getStr tb.fields "statement" then
      errs := errs.push s!"E3 target {tgt}: its printed statement differs from the registry's"
    -- item 5 (Q5): precomputed inputs carry the flag and the marker
    match ← precomputedInputs tgt with
    | none => errs := errs.push s!"E3 target {tgt} does not conclude a model on `Prog` {""
        }({models})"
    | some pre =>
      let flag := !(getList tb.fields "precomputed").isEmpty
      let marker := ((← findDocString? env tgt).getD "" |>.splitOn "Precomputed:").length > 1
      if pre && !(flag && marker) then
        errs := errs.push s!"E3 target {tgt} has declared inputs computed from the sizes: {""
          }it needs `precomputed = [...]` in the registry and a `Precomputed:` docstring sentence"
      if !pre && (flag || marker) then
        errs := errs.push s!"E3 target {tgt} carries the precomputed flag or marker, but its {""
          }declared inputs are not computed from the sizes"
    let fs := setField (setField tb.fields "hash" (.str h)) "statement" (.multi stmt)
    tables' := tables'.push { tb with fields := fs }
  for tb in tables' do
    if tb.kind == "tree" && !used.contains (getStr tb.fields "name").toName then
      errs := errs.push s!"E3 registered tree {getStr tb.fields "name"} is named by no target"
    unless tb.kind == "tree" || tb.kind == "target" do
      errs := errs.push s!"E3 the registry has a table [[{tb.kind}]]"
  -- item 2: results about runs prove registered targets
  for c in ← unregisteredResults env resultScope proofs do
    errs := errs.push s!"E3 {c}: a `Result:` theorem about a program's runs or budget is the {""
      }proof of a registered target (`theorem t : T`, T in docs/targets.toml); remove its id or {""
      }state it as a target, with the maintainer's approval"
  return (errs, { out with tables := tables' })

/-- The library's constants (imported from `NLAlib` modules). -/
def libConsts (env : Environment) : Array (Name × ConstantInfo) := Id.run do
  let mut out := #[]
  for h : i in [0:env.header.moduleNames.size] do
    unless (`NLAlib).isPrefixOf env.header.moduleNames[i] do continue
    for c in env.header.moduleData[i]!.constNames do
      if let some info := env.find? c then out := out.push (c, info)
  return out

end TargetChecks

open TargetChecks in
run_cmd do
  let env ← getEnv
  let path := (← IO.getEnv "TARGETS_REGISTRY").getD "docs/targets.toml"
  let approved := (← IO.getEnv "TARGETS_APPROVED").getD "docs/targets.approved"
  let update := (← IO.getEnv "TARGETS_UPDATE").isSome
  let text ← IO.FS.readFile path
  let reg ← match parseRegistry text with
    | .ok r => pure r
    | .error e => throwError "E3 {path}: {e}"
  let lib := libConsts env
  let (errs, reg') ← liftTermElabM <| checkRegistry reg lib lib (← buildPins)
  if update then
    IO.FS.writeFile path reg'.render
    logInfo m!"{path} rewritten; the maintainer reviews the diff and approves with {""
      }`sha256sum {path} > {approved}`"
  let errs := if update then errs.filter fun e =>
      !(e.splitOn "hash").length > 1 && !(e.splitOn "printed statement").length > 1 &&
        !(e.splitOn "the registry pins").length > 1
    else errs
  for e in errs do logError e
  -- item 6 (Q3): the registry is the approved one
  let sha ← sha256File path
  let ok ← try
      pure (((← IO.FS.readFile approved).splitOn " ").head?.map (·.trimAscii.toString) == some sha)
    catch _ => pure false
  unless ok do
    logError m!"E3 {path} (SHA-256 {sha}) is not the approved registry: {approved} differs; {""
      }only the maintainer approves a registry change (CONTRIBUTING §11)"
  let targets := reg'.tables.filter (·.kind == "target")
  logInfo m!"targets: {targets.size} registered targets, {reg'.tables.size - targets.size} {""
    }registered trees; {errs.size + (if ok then 0 else 1)} violations"

/-! ## Fixtures: copies of a target, and the cheats against it -/

namespace TargetFixtures

open NLAlib NLAlib.Computation MeasureTheory ProbabilityTheory

variable {P ι : Type}

/-- Hutch++'s family. -/
def hppF (p : P) (o : ι) (d : Dist) : ProgFamily P ι 2 1 :=
  fun _ _ N n h => (hutchppProg p o d N (n 0) (n 1) ⟨h 0, 0⟩).run

theorem hpp_isSome (p : P) (o : ι) (d : Dist) :
    (ProgFamily.compile (hppF p o d)).isSome = true := rfl

/-- A copy of the registered tree `hutchppProg.compiled`. -/
def hppC (p : P) (o : ι) (d : Dist) : Prog P ι 2 1 :=
  (ProgFamily.compile (hppF p o d)).get (hpp_isSome p o d)

theorem hppC_toStmt (p : P) (o : ι) (d : Dist) (N : ℕ) (n : Fin 2 → ℕ) :
    (hppC p o d).toStmt N n = (hppF p o d).inst N n := rfl

/-- A copy of the target `MatrixFreeHutchpp`. -/
def FixHutchpp : Prop :=
  ∀ (P ι : Type) [DecidableEq P] (p : P) (o : ι) (d : Dist) (𝕜 : Type) [RCLike 𝕜],
    MatrixFree (𝕜 := 𝕜) p (hppC p o d) (fun _ n => 0 < n 1) (fun _ _ => Unit)
      (fun _ _ _ => ![Array.replicate 1 none]) (fun N n => hutchppCount p o d N (n 0) (n 1))
      (fun N n q => if q = p then 2 * N * (n 0 + n 1) + 4 else 0)
      (fun N n _ A ξ st => st.store.read p 0 0 = some
        (hutchpp A (tapeMatrix (ξ d) 0 N (n 0)) (tapeMatrix (ξ d) (N * n 0) N (n 1))))

/-- Its proof. -/
theorem fixHutchpp : FixHutchpp :=
  fun _ _ _ p o d _ _ => (matrixFree_hutchppProg p o d).prog _ (hppC_toStmt p o d)

/-- A copy of the target `MatrixFreeProbHutchpp` (for the `irreducible_def` fixture). -/
def FixHutchppTail : Prop :=
  ∀ (P ι : Type) [DecidableEq P] (p : P) (o : ι) (r : ℕ) (δ : ℝ), 0 < δ → ∀ τ : ℝ, 0 ≤ τ →
    MatrixFreeProb (𝕜 := ℝ) p (hppC p o .gaussian)
      (fun _ n => 0 < n 0 ∧ 0 < n 1 ∧ subgaussianEmbeddingDim 1 r (1 / 2) (δ / 2) ≤ n 0)
      (fun _ _ => Unit) (fun _ _ _ => ![Array.replicate 1 none])
      (fun N n => hutchppCount p o .gaussian N (n 0) (n 1))
      (fun N n q => if q = p then 2 * N * (n 0 + n 1) + 4 else 0)
      (fun _ _ _ A st => ∃ v, st.store.read p 0 0 = some v ∧ |A.trace - v| < τ)
      (fun _ n _ A => δ + 2 * Real.exp (-(hansonWrightConstant *
        min (n 1 * τ ^ 2 / (subgaussianRangeFinderFactor 1 * frobNorm (A - truncatedSVD A r) ^ 2))
          (n 1 * τ / (√(subgaussianRangeFinderFactor 1) * frobNorm (A - truncatedSVD A r))))))

/-- The nodes of a quadrature rule of size `q`, computed by the host (a precomputed input). -/
def nodes (q : ℕ) : Array (Option ℝ) := Array.replicate q (some 0)

/-- Q5: a target whose declared input is computed from the sizes, with neither the registry
flag nor the docstring marker. -/
def FixPrecomputed : Prop :=
  ∀ (P ι : Type) [DecidableEq P] (p : P) (o : ι) (d : Dist),
    MatrixFree (𝕜 := ℝ) p (hppC p o d) (fun _ n => 0 < n 1) (fun _ _ => Unit)
      (fun _ n _ => ![nodes (n 0)]) (fun N n => hutchppCount p o d N (n 0) (n 1))
      (fun _ _ _ => 0) (fun _ _ _ _ _ _ => True)

/-- An axiom whose type is the target. -/
axiom axHutchpp : FixHutchpp

/-- Audit 1, a vacuous outer hypothesis (`matrixFree_vacuous`). -/
theorem vacuousHutchpp (hall : ∀ (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ), A.trace = 0) :
    FixHutchpp := absurd (hall 1 1) (by simp)

/-- Audit 1, an outer parameter unrolled into a literal (`matrixFree_literalTraceProg`). -/
theorem outerHutchpp (_A₀ : Matrix (Fin 1) (Fin 1) ℚ) : FixHutchpp := fixHutchpp

/-- Audit 1, a postcondition of the prover's (`matrixFree_sizeTraceProg`): an implication from
a size that encodes the datum. A model statement, not a registered target.

Result: fixture-size-trace -/
theorem matrixFree_sizeTraceProg :
    MatrixFree (𝕜 := ℝ) (ι := Unit) () (.skip : Prog Unit Unit 1 1) (fun _ _ => True)
      (fun _ _ => Unit) (fun _ _ _ => ![Array.replicate 1 none]) (fun _ _ => 0)
      (fun _ _ _ => 1) (fun N n _ A _ st => n 0 = N → A.trace = 0 → st = st) := by
  intro N n _ x A ξ
  refine ⟨_, rfl, le_rfl, fun _ => ?_, fun _ _ => rfl⟩
  simp [inputState, exactInterp]

/-- Audit 2, a claim phrased through `exec` (`exec_copyTrace`).

Result: fixture-copy-trace -/
theorem exec_copyTrace (A : Matrix (Fin 1) (Fin 1) ℝ) (ξ : Dist → ℕ → ℝ) :
    exec (exactInterp (P := Unit) (ι := Unit) (fun _ => A) ξ) .skip
      (inputState () [#[some A.trace]]) =
      some (inputState () [#[some A.trace]]) := rfl

/-- A target of the prover's: a `Prop` that unfolds to a model, not in the registry. -/
def FixUnregistered : Prop := FixHutchpp

/-- Its proof, with a result id: its type is a constant, but not a registered one.

Result: fixture-unregistered -/
theorem fixUnregistered : FixUnregistered := fixHutchpp

/-- A ForMathlib definition (in a Mathlib namespace) under a fixture. -/
noncomputable def usesCompound (A : Matrix (Fin 2) (Fin 2) ℝ) := Matrix.compound 1 A

end TargetFixtures

open TargetChecks in
run_cmd do
  let env ← getEnv
  let F := ``TargetFixtures.FixHutchpp
  let fail (m : MessageData) : CommandElabM Unit := logError m!"E3 fixture: {m}"
  -- item 1
  unless provesTarget env ``TargetFixtures.fixHutchpp F do fail m!"the proof is rejected"
  for c in [``TargetFixtures.axHutchpp, ``TargetFixtures.vacuousHutchpp,
      ``TargetFixtures.outerHutchpp] do
    if provesTarget env c F then fail m!"{c} passes the lint"
  logInfo "item 1: axHutchpp (an axiom), vacuousHutchpp, outerHutchpp rejected"
  -- item 2
  let here := env.constants.map₂.toArray
  let flagged ← unregisteredResults env here (NameSet.empty.insert ``TargetFixtures.fixHutchpp)
  for c in [``TargetFixtures.matrixFree_sizeTraceProg, ``TargetFixtures.exec_copyTrace,
      ``TargetFixtures.fixUnregistered] do
    unless flagged.contains c do fail m!"{c} is not flagged"
  if flagged.size != 3 then fail m!"item 2 flags {flagged}"
  logInfo m!"item 2: {flagged} flagged"
  -- item 3: the registered tree is a leaf; edits under the closure change the hash
  let (nf, defs) ← liftTermElabM <| treeNF ``TargetFixtures.hppC
  unless defs.isEmpty do fail m!"the tree's normal form contains {defs}"
  let trees := fun n => if n == ``TargetFixtures.hppC then some nf else none
  let (cl, _) := closure env (fun _ => none) trees F
  if cl.contains ``NLAlib.hutchppProg || cl.contains ``NLAlib.Computation.Stmt.compile then
    fail m!"the builder or the compiler is in the closure of a target with its tree as a leaf"
  let h₀ ← closureHash env (fun _ => none) trees cl
  unless h₀ == (← closureHash env (fun _ => none) trees cl) do fail m!"the hash is not stable"
  let edit (root c : Name) (f : Expr → Expr) : CommandElabM (Bool × String) := do
    let some (.defnInfo d) := env.find? c | throwError "{c} is not a definition"
    let o := fun n => if n == c then some (ConstantInfo.defnInfo { d with value := f d.value })
      else none
    let (cl', _) := closure env (fun _ => none) trees root
    let (cl₁, _) := closure env o trees root
    return (cl'.contains c,
      if (← closureHash env (fun _ => none) trees cl') == (← closureHash env o trees cl₁) then
        "unchanged" else "changed")
  -- the count
  let r ← edit F ``NLAlib.hutchppCount fun v => .lam `x (.const ``Nat []) v .default
  unless r == (true, "changed") do fail m!"an edit of hutchppCount: {r}"
  -- the value under an `irreducible_def`
  let some hw := env.find? ``NLAlib.hansonWrightConstant | throwError "no hansonWrightConstant"
  let under := (hw.value!.getUsedConstants.toList.flatMap fun w =>
    ((env.find? w).map (·.type.getUsedConstants.toList)).getD []).filter fun n =>
      match env.find? n with | some (.defnInfo _) => isLibConst env n | _ => false
  let some u := under.head? | throwError "no definition under the irreducible_def"
  let some (.defnInfo du) := env.find? u | throwError "not a definition"
  let v₁ ← liftTermElabM do instantiateMVars (← Term.elabTerm (← `((1 / 197 : ℝ))) du.type)
  let r ← edit ``TargetFixtures.FixHutchppTail u fun _ => v₁
  unless r == (true, "changed") do fail m!"an edit of {u} := 1/197: {r}"
  -- a ForMathlib definition in a Mathlib namespace
  let r ← edit ``TargetFixtures.usesCompound ``Matrix.compound
    fun v => .lam `k (.const ``Nat []) v .default
  unless r == (true, "changed") do fail m!"an edit of Matrix.compound: {r}"
  logInfo m!"item 3: {cl.size} constants, builder outside; edits of hutchppCount, of {u} {""
    }(under hansonWrightConstant) and of Matrix.compound (ForMathlib) change the hash"
  -- item 4: a toolchain mismatch
  let reg : Registry := { top := #[("toolchain", .str "leanprover/lean4:v4.0.0"),
    ("mathlib", .str "0df444a")] }
  if (pinErrors reg ("leanprover/lean4:v" ++ Lean.versionString) "0df444a").size != 1 then
    fail m!"a toolchain mismatch is not detected"
  logInfo "item 4: a toolchain mismatch detected"
  -- item 5 (Q5)
  unless (← liftTermElabM (precomputedInputs ``TargetFixtures.FixPrecomputed)) == some true do
    fail m!"FixPrecomputed: precomputed input not detected"
  unless (← liftTermElabM (precomputedInputs F)) == some false do
    fail m!"FixHutchpp: an input of `Array.replicate` is seen as precomputed"
  logInfo "item 5: a declared input computed from the sizes detected"
  -- the registry, round trip: written by `--update`, then checked, then tampered with
  let text := "# fixture\ntoolchain = \"\"\nmathlib = \"\"\n\n[[tree]]\nname = \
    \"TargetFixtures.hppC\"\nhash = \"\"\n\n[[target]]\nname = \"TargetFixtures.FixHutchpp\"\n\
    file = \"\"\ntrees = [\"TargetFixtures.hppC\"]\nprecomputed = []\nreviewed = \"2026-10-23\"\n\
    hash = \"\"\nstatement = '''\n'''\n"
  let .ok reg := parseRegistry text | throwError "the fixture registry does not parse"
  let pins ← buildPins
  let (_, reg₁) ← liftTermElabM <| checkRegistry reg here here pins
  let .ok reg₂ := parseRegistry reg₁.render | throwError "the written registry does not parse"
  let (errs, _) ← liftTermElabM <| checkRegistry reg₂ here here pins
  let errs := errs.filter fun e => !(e.splitOn "Result:").length > 1
  unless errs.size == 1 && (errs[0]!.splitOn "axHutchpp").length > 1 do
    fail m!"an axiom of the target's type beside its proof is not rejected: {errs}"
  let here := here.filter (·.1 != ``TargetFixtures.axHutchpp)
  let (errs, _) ← liftTermElabM <| checkRegistry reg₂ here here pins
  let errs := errs.filter fun e => !(e.splitOn "Result:").length > 1
  unless errs.isEmpty do fail m!"the updated fixture registry fails: {errs}"
  let reg₃ := { reg₂ with tables := reg₂.tables.map fun tb =>
    { tb with fields := setField tb.fields "hash" (.str "0") } }
  let (errs, _) ← liftTermElabM <| checkRegistry reg₃ here here pins
  unless (errs.filter fun e => (e.splitOn "hash").length > 1).size == 2 do
    fail m!"a tampered registry passes: {errs}"
  logInfo m!"registry: --update round trip checks; an axiom beside the proof, a tampered tree {""
    }hash and a tampered target hash detected"
