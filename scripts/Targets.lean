import NLAlib
open Lean Meta Elab Command

/-! # Target checks (rule E3, docs/rules/rules.toml)

A published cost result is a theorem whose type is a **target**, a library definition of type
`Prop` registered in `docs/targets.toml` (`docs/design/Computation.md`, "First-order programs and
target statements", F1 and F12). This script checks, on the library built by `lake build NLAlib`:

1. every registered target is a `Prop` definition in its registered `*Targets.lean` file, and has
   exactly one proof: a theorem (not an axiom, not an opaque) whose type is the target constant
   itself, syntactically, with no binder;
2. every constant outside `NLAlib/Computation` with a `Result:` id that claims something about a
   run or a budget (the models, `Prog.exec`, `FStmt.exec`, `Prog.RunsWithin`, `RunsWithin`,
   `exec`, `Stmt`, `ProgFamily.inst`), through the library constants it unfolds to (the values of
   definitions and opaques, the constructors of structures, classes and inductive types), is a
   registered target or its proof: a theorem, an instance of a `Prop` class, any constant whose
   type is a proposition, or a definition of type `Prop`;
3. the **closure hash** of each target matches the registry: SHA-256 of a canonical serialisation
   of every library constant the target's statement reaches (a constant is a library constant if
   its module is an `NLAlib` module), of every kind: definitions and opaques (type and value),
   theorems, axioms and quotients (type), inductive types (type, parameters, indices, mutual
   block, constructors), constructors and recursors (type). Every proof is erased (serialised as
   one token, sound by proof irrelevance), and hygienic names are numbered in the order of the
   walk (final audit, 2026-10-24). A registered tree is a leaf, hashed by its constructor normal
   form (`Meta.reduce`), which must contain no library definition, and the kernel checks that the
   tree is its normal form (`theorem _ : tree = nf := Eq.refl _`); the printed statement (the
   target unfolded one level) and the printed normal form of each tree (the tree hash's input)
   match the registry too;
4. the pins: the Lean toolchain, the Mathlib revision of `lake-manifest.json`, and the SHA-256 of
   `lake-manifest.json` and of `lakefile.toml`, are the registry's;
5. (Q5) a target whose declared inputs are not `Array.replicate _ none` or built from the declared
   data carries the registry flag `precomputed` and the docstring marker `Precomputed:`;
6. (Q3) `docs/targets.approved` holds the SHA-256 of `docs/targets.toml`
   (`sha256sum docs/targets.toml > docs/targets.approved`, by the maintainer only).

What is left trusted between a target and the code it is about: the emitter of the tree
(`NLAlibTools/NumPy.lean`), which the guarantees do not cover (`docs/design/Computation.md`,
"Final audits").

Then the fixtures at the end of this file, on copies of a target, must be rejected or detected.

Run with `lake env lean scripts/Targets.lean` after `lake build NLAlib`; a nonzero exit code
means a violation. `TARGETS_UPDATE=1 lake env lean scripts/Targets.lean` (the `--update` mode)
rewrites the hashes, the printed statements and normal forms, the pins and the leading comment
of the registry for review; it never writes `docs/targets.approved`. Agents never edit the registry or a `*Targets.lean` file
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

/-- **The token that stands for every proof** in the closure walk and the serialisation (final
audit, 2026-10-24). Two terms that differ only in proofs are definitionally equal (proof
irrelevance), and the proposition a proof proves is fixed by its position in the rest of the term,
so a hash that reads the token in place of each proof freezes the same meaning, and an edit of a
proof (a `Fin` bound, the proof inside a `ℚ` literal, a renumbered `_proof_` auxiliary) leaves it
unchanged. A constant used only inside proofs is outside the closure. Never used in a proof. -/
axiom proofToken {p : Prop} : p

/-- A term with every proof replaced by `proofToken` (a subterm whose type cannot be inferred is
kept, and visited). -/
def eraseProofs (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun s => do
    let pf ← try isProof s catch _ => pure false
    return if pf then .done (mkConst ``proofToken) else .continue)

/-- The state of a canonical serialisation: each distinct subterm once, as a line naming its
children by number, so that a term with sharing is serialised in linear size. Binder names and
binder annotations are left out (alpha-equivalent terms serialise alike), as is metadata. A
constant is written by its name, or by its canonical name in `canon` (the hygienic names of a
closure). -/
structure Ser where
  ids : Std.HashMap Expr Nat := {}
  lines : Array String := #[]
  canon : Std.HashMap Name String := {}

/-- Append a line; its number. -/
def emit (line : String) : StateM Ser Nat :=
  modifyGet fun s => (s.lines.size, { s with lines := s.lines.push line })

/-- A constant's name as serialised. -/
def nameStr (n : Name) : StateM Ser String := return ((← get).canon[n]?).getD n.toString

/-- Serialise an expression whose equal subterms are shared; the number of its line. -/
partial def serShared (e : Expr) : StateM Ser Nat := do
  if let some i := (← get).ids[e]? then return i
  let i ← match e with
    | .bvar k => emit s!"b {k}"
    | .fvar f => emit s!"f {f.name}"
    | .mvar m => emit s!"m {m.name}"
    | .sort u => emit s!"s {u}"
    | .const n us => do emit s!"c {← nameStr n} {us}"
    | .app f a => do let f ← serShared f; let a ← serShared a; emit s!"a {f} {a}"
    | .lam _ t b _ => do let t ← serShared t; let b ← serShared b; emit s!"l {t} {b}"
    | .forallE _ t b _ => do let t ← serShared t; let b ← serShared b; emit s!"p {t} {b}"
    | .letE _ t v b _ => do
      let t ← serShared t; let v ← serShared v; let b ← serShared b; emit s!"z {t} {v} {b}"
    | .lit (.natVal n) => emit s!"n {n}"
    | .lit (.strVal s) => emit s!"t {s.quote}"
    | .mdata _ b => serShared b
    | .proj s k b => do let b ← serShared b; emit s!"j {← nameStr s} {k} {b}"
  modify fun s => { s with ids := s.ids.insert e i }
  return i

/-- Serialise an expression; the number of its line. Equal subterms are made pointer-equal
first, so that the table's comparisons stop at the pointer. -/
def serExpr (e : Expr) : StateM Ser Nat := serShared (ShareCommon.shareCommon' e)

/-- A constant of a closure as it is hashed: its information, its type and the term its kind
carries (a definition's or an opaque's value; a registered tree's normal form), proofs erased. -/
structure Entry where
  info : ConstantInfo
  type : Expr
  body : Option Expr := none
  tree : Bool := false

/-- Serialise one constant of a closure: its kind, name, universe parameters, type, and what
else its kind carries (a registered tree: its normal form instead of its value). -/
def serEntry (c : Name) (x : Entry) : StateM Ser Unit := do
  let ty ← serExpr x.type
  let names (ns : List Name) : StateM Ser String := return s!"{← ns.mapM nameStr}"
  let head := s!"{← nameStr c} {x.info.levelParams} {ty} {x.info.isUnsafe} {x.info.isPartial}"
  let line ← match x.tree, x.info, x.body with
    | true, _, some nf => do pure s!"# tree {head} {← serExpr nf}"
    | _, .defnInfo _, some v => do pure s!"# def {head} {← serExpr v}"
    | _, .opaqueInfo _, some v => do pure s!"# opaque {head} {← serExpr v}"
    | _, .thmInfo _, _ => pure s!"# theorem {head}"
    | _, .axiomInfo _, _ => pure s!"# axiom {head}"
    | _, .quotInfo _, _ => pure s!"# quot {head}"
    | _, .inductInfo d, _ => do
      pure s!"# inductive {head} {d.numParams} {d.numIndices} {← names d.all} {""
        }{← names d.ctors} {d.isRec}"
    | _, .ctorInfo d, _ => do
      pure s!"# ctor {head} {← nameStr d.induct} {d.cidx} {d.numParams} {d.numFields}"
    | _, .recInfo _, _ => pure s!"# rec {head}"
    | _, _, _ => pure s!"# other {head}"
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
  | none => (env.find? c).isSome && c != ``proofToken

/-- The closure of a target: every library constant its statement reaches, in the hash's order,
the names reached that the environment does not know (an error), each constant as it is hashed,
and the canonical names of the hygienic ones. -/
structure Closure where
  names : Array Name := #[]
  missing : Array Name := #[]
  entries : Std.HashMap Name Entry := {}
  canon : Std.HashMap Name String := {}

/-- **The closure walk.** It follows the type of every constant, the value of definitions and
opaques (an `irreducible_def` is an opaque whose type names the definition holding the value), the
mutual block and the constructors of inductive types, each with its proofs erased
(`eraseProofs`), so that a constant used only in proofs is not reached. A registered tree
(`trees`) is a leaf: the walk follows its type and its normal form, not its definition.
`override` replaces a constant's information, for the fixtures.

A hygienic name (with macro scopes, `NLAlib.definition._@.<module>.<hash>._hygCtx._hyg.2` of an
`irreducible_def`) is written as its name without macro scopes and its number among the hygienic
names in the order the walk meets them (final audit, 2026-10-24). The walk's order depends on the
terms only, so the renaming is a bijection of the closure determined by its structure: the hash is
that of the closure up to a renaming of its hygienic constants, which changes no meaning, and an
unrelated edit of a file no longer changes it. The constants are hashed in the order of their
serialised names. -/
def closure (override : Name → Option ConstantInfo) (trees : Name → Option Expr) (root : Name) :
    MetaM Closure := do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut out : Array Name := #[]
  let mut missing : Array Name := #[]
  let mut entries : Std.HashMap Name Entry := {}
  let mut todo : List Name := [root]
  while !todo.isEmpty do
    let c := todo.head!
    todo := todo.tail!
    if seen.contains c || c == ``proofToken then continue
    seen := seen.insert c
    let some info := (override c).orElse fun _ => env.find? c
      | missing := missing.push c; continue
    unless isLibConst env c do continue
    out := out.push c
    let type ← eraseProofs info.type
    let x : Entry ← match trees c, info with
      | some nf, _ => pure { info, type, body := some (← eraseProofs nf), tree := true }
      | none, .defnInfo d => pure { info, type, body := some (← eraseProofs d.value) }
      | none, .opaqueInfo d => pure { info, type, body := some (← eraseProofs d.value) }
      | none, _ => pure { info, type }
    entries := entries.insert c x
    let mut next := type.getUsedConstants.toList ++
      ((x.body.map (·.getUsedConstants.toList)).getD [])
    if let (.inductInfo d, false) := (info, x.tree) then next := next ++ d.all ++ d.ctors
    todo := next ++ todo
  let mut canon : Std.HashMap Name String := {}
  for c in out do
    if c.hasMacroScopes then canon := canon.insert c s!"{c.eraseMacroScopes}._hyg#{canon.size}"
  let key (c : Name) : String := (canon[c]?).getD c.toString
  return { names := out.qsort (key · < key ·), missing, entries, canon }

/-- The closure hash: SHA-256 of the serialisation of the closure's constants, in order. -/
def closureHash (cl : Closure) : IO String := do
  let ser : StateM Ser Unit := cl.names.forM fun c =>
    match cl.entries[c]? with
    | some x => serEntry c x
    | none => pure ()
  sha256 ("\n".intercalate (ser.run { canon := cl.canon }).2.lines.toList)

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
(none, for a tree built from constructors). The kernel checks that the tree is its normal form
(`kernelTreeEq`). -/
def treeNF (c : Name) : MetaM (Expr × Array Name) := do
  let some (.defnInfo d) := (← getEnv).find? c | throwError "{c} is not a definition"
  let v ← Meta.reduce d.value (explicitOnly := false) (skipTypes := true) (skipProofs := true)
  let v ← instantiateMVars v
  let defs ← lambdaTelescope v fun _ body => valueDefs body
  return (v, defs)

/-- **The kernel's check of a tree's normal form** (final audit, 2026-10-24): the declaration
`theorem _ : c = nf := Eq.refl _`, sent to the kernel (`Environment.addDeclCore`, not added to
the environment). So the link between the definition a target names and the normal form the hash
and the printed form read is the kernel's, not `Meta.reduce`'s. `none` if the kernel accepts it,
else its error. -/
def kernelTreeEq (c : Name) (nf : Expr) : MetaM (Option String) := do
  let env ← getEnv
  let some info := env.find? c | return some s!"{c} is unknown"
  let lhs := mkConst c (info.levelParams.map mkLevelParam)
  let u ← getLevel info.type
  let decl := Declaration.thmDecl {
    name := `TargetChecks.kernelTreeEq ++ c, levelParams := info.levelParams
    type := mkApp3 (mkConst ``Eq [u]) info.type lhs nf
    value := mkApp2 (mkConst ``Eq.refl [u]) info.type lhs }
  match env.addDeclCore 0 0 decl none with
  | .ok _ => return none
  | .error ex => return some (← (ex.toMessageData {}).toString)

/-- The hash of a registered tree: its type and its normal form, proofs erased. -/
def treeHash (c : Name) (nf : Expr) : MetaM String := do
  let some info := (← getEnv).find? c | throwError "{c} is unknown"
  let type ← eraseProofs info.type
  let body ← eraseProofs nf
  let x : Entry := { info, type, body := some body, tree := true }
  sha256 ("\n".intercalate ((serEntry c x).run {}).2.lines.toList)

/-- The inputs of a tree's hash, printed for review: its type and its normal form, each proof
printed as `proofToken`, with `NLAlib`, `NLAlib.Computation` and `TargetChecks` open. -/
def printTree (c : Name) (nf : Expr) : MetaM String := do
  let some info := (← getEnv).find? c | throwError "{c} is unknown"
  let opens := [`NLAlib, `NLAlib.Computation, `TargetChecks].map (OpenDecl.simple · [])
  let pp (e : Expr) : MetaM Std.Format := do
    let e ← eraseProofs e
    withTheReader Core.Context (fun ctx => { ctx with openDecls := opens ++ ctx.openDecls }) do
      ppExpr e
  let t ← pp info.type
  let v ← pp nf
  let f := f!"{c} :{Std.Format.nest 2 (Std.Format.line ++ t)} :={Std.Format.line}{v}"
  return "\n".intercalate ((f.pretty 100).splitOn "\n" |>.map fun l => l.trimAsciiEnd.toString)

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

/-- Whether a constant reaches a run or a budget through the library constants it unfolds to:
the type of every constant, the value of definitions and opaques, and the mutual block and the
constructors of inductive types, so that a statement wrapped in a structure, a class or an
inductive `Prop` is followed into its fields (final audit, 2026-10-24). Memoised; Mathlib
constants reach none. -/
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
  | .inductInfo d => next := next ++ d.all.toArray ++ d.ctors.toArray
  | _ => pure ()
  let mut r := false
  for d in next do
    if ← reachesRun env d then r := true; break
  modify (·.insert c r)
  return r

/-- Lint item 2: the constants in `scope` outside `NLAlib/Computation` with a `Result:` id that
make a claim about a program's runs or budget and are neither a registered target nor its proof
(`exempt`). A claim is a constant whose type is a proposition (a theorem, an instance of a `Prop`
class, a definition or an axiom of a proposition), when its type reaches a run or a budget, or a
definition of type `Prop` (a target of the prover's), when its value does (final audit,
2026-10-24). -/
def unregisteredResults (env : Environment) (scope : Array (Name × ConstantInfo))
    (exempt : NameSet) : MetaM (Array Name) := do
  let mut memo : Std.HashMap Name Bool := {}
  let mut out := #[]
  for (c, info) in scope do
    if exempt.contains c then continue
    if (moduleOf env c).any (`NLAlib.Computation).isPrefixOf then continue
    let some doc ← findDocString? env c | continue
    unless (doc.splitOn "Result:").length > 1 do continue
    let claim ← try isProp info.type catch _ => pure false
    let propDef := info matches .defnInfo _ && info.type == .sort 0
    unless claim || propDef do continue
    let consts := if propDef then #[c] else info.type.getUsedConstants
    let (r, m) := (consts.anyM (reachesRun env)).run memo
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

/-- The pins of the build (item 4): the toolchain, the Mathlib revision of `lake-manifest.json`,
and the SHA-256 of `lake-manifest.json` and of `lakefile.toml` (final audit, 2026-10-24), so that
a change of any dependency, of the Lake configuration or of the options every file is built with
needs the maintainer's approval. -/
structure Pins where
  toolchain : String
  mathlib : String
  manifest : String
  lakefile : String

/-- The pins of the build. -/
def buildPins : IO Pins := do
  let toolchain := "leanprover/lean4:v" ++ Lean.versionString
  let file := (← IO.FS.readFile "lean-toolchain").trimAscii.toString
  if file != toolchain then
    throw <| IO.userError s!"lean-toolchain says {file}, the running Lean is {toolchain}"
  let manifest ← IO.ofExcept <| Json.parse (← IO.FS.readFile "lake-manifest.json")
  let pkgs ← IO.ofExcept <| manifest.getObjValAs? (Array Json) "packages"
  let some m := pkgs.find? fun p => (p.getObjValAs? String "name").toOption == some "mathlib"
    | throw <| IO.userError "lake-manifest.json has no mathlib"
  return { toolchain, mathlib := ← IO.ofExcept (m.getObjValAs? String "rev"),
           manifest := ← sha256File "lake-manifest.json", lakefile := ← sha256File "lakefile.toml" }

/-- The registry keys of the pins, with their values in `p`. -/
def Pins.fields (p : Pins) : List (String × String × String) :=
  [("toolchain", "toolchain", p.toolchain), ("mathlib", "Mathlib", p.mathlib),
   ("lake_manifest_sha256", "lake-manifest.json (SHA-256)", p.manifest),
   ("lakefile_sha256", "lakefile.toml (SHA-256)", p.lakefile)]

/-- Item 4: the registry's pins against the build's. -/
def pinErrors (reg : Registry) (p : Pins) : Array String :=
  p.fields.toArray.filterMap fun (k, what, v) =>
    if getStr reg.top k == v then none
    else some s!"the registry pins {what} {getStr reg.top k}, the build has {v}"

/-- The leading comment of the registry, written by `--update`. -/
def registryHeader : Array String := #[
  "# The registry of target statements (docs/design/Computation.md, \"First-order programs and target",
  "# statements\", F1 and F12, and \"Final audits\"). A published cost result is a theorem whose type is",
  "# one of these targets; scripts/Targets.lean (rule E3) checks that each has exactly one proof, that",
  "# the closure hash of each (every library constant its statement reaches, proofs erased, hygienic",
  "# names numbered, the registered trees as leaves hashed by their constructor normal forms) and its",
  "# printed statement match this file, that each tree is its normal form (checked by the kernel) and",
  "# its printed normal form matches this file, that the pins (the toolchain, the Mathlib revision,",
  "# the SHA-256 of lake-manifest.json and of lakefile.toml) are the build's, and that",
  "# docs/targets.approved holds the SHA-256 of this file.",
  "#",
  "# Changes need the maintainer's approval (Q3): agents never edit this file or a *Targets.lean",
  "# file. After an approved change of a target, `TARGETS_UPDATE=1 lake env lean scripts/Targets.lean`",
  "# rewrites the hashes, the printed statements and normal forms, the pins and this comment; the",
  "# maintainer reviews the diff and approves it with `sha256sum docs/targets.toml >",
  "# docs/targets.approved`.",
  "#",
  "# [[tree]]    a registered tree: name, hash (of its type and constructor normal form, proofs",
  "#             erased), normal_form (the hash's input, printed: proofs as TargetChecks.proofToken)",
  "# [[target]]  name, file (its *Targets.lean file), trees (the registered trees it names),",
  "#             precomputed (declared inputs computed from the sizes, Q5), reviewed (the date of",
  "#             the maintainer's review), hash (the closure hash), statement (the target unfolded",
  "#             one level, printed)"]

/-- Check the registry against the environment. `proofScope`: the constants that may prove a
target; `resultScope`: the theorems lint item 2 reads. Returns the violations and the registry
with its hashes, printed statements and pins recomputed (written by `--update`). -/
def checkRegistry (reg : Registry) (proofScope resultScope : Array (Name × ConstantInfo))
    (pins : Pins) (override : Name → Option ConstantInfo := fun _ => none) :
    MetaM (Array String × Registry) := do
  let env ← getEnv
  let mut errs : Array String := (pinErrors reg pins).map ("E3 " ++ ·)
  let mut out := { reg with
    header := registryHeader
    top := pins.fields.foldl (fun fs (x : String × String × String) =>
      setField fs x.1 (.str x.2.2)) reg.top }
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
      if let some e ← kernelTreeEq name nf then
        errs := errs.push s!"E3 registered tree {name}: the kernel does not accept that it is {""
          }its normal form: {e}"
      nfs := nfs.insert name nf
      let h ← treeHash name nf
      if h != getStr tb.fields "hash" then
        errs := errs.push s!"E3 registered tree {name}: normal-form hash {h}, the registry has {""
          }{getStr tb.fields "hash"}; a change of a tree needs the maintainer's approval"
      let pnf ← printTree name nf
      if pnf != getStr tb.fields "normal_form" then
        errs := errs.push s!"E3 registered tree {name}: its printed normal form differs from {""
          }the registry's"
      let fs := setField (setField tb.fields "hash" (.str h)) "normal_form" (.multi pnf)
      tables := tables.push { tb with fields := fs }
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
    let cl ← closure override (nfs.get? ·) tgt
    unless cl.missing.isEmpty do
      errs := errs.push s!"E3 target {tgt}: its closure reaches the unknown constants {cl.missing}"
    let h ← closureHash cl
    if h != getStr tb.fields "hash" then
      errs := errs.push s!"E3 target {tgt}: closure hash {h} ({cl.names.size} constants), the {""
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
  let targets := tables'.filterMap fun tb =>
    if tb.kind == "target" then some (getStr tb.fields "name").toName else none
  for c in ← unregisteredResults env resultScope (targets.foldl NameSet.insert proofs) do
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
      !(e.splitOn "hash").length > 1 && !(e.splitOn "its printed").length > 1 &&
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

/-- Final audit, 2026-10-24: a result about runs hidden in a structure. -/
structure Wrapped : Prop where
  h : FixHutchpp

/-- Through a structure.

Result: fixture-wrapped -/
theorem wrapped : Wrapped := ⟨fixHutchpp⟩

/-- Through `Nonempty` of a structure.

Result: fixture-nonempty -/
theorem viaNonempty : Nonempty Wrapped := ⟨wrapped⟩

/-- An inductive `Prop` whose constructor carries a run. -/
inductive IndRun : Prop where
  | mk : FixHutchpp → IndRun

/-- Through an inductive `Prop`.

Result: fixture-inductive -/
theorem indRun : IndRun := ⟨fixHutchpp⟩

/-- A result about runs hidden in a class. -/
class RunsFast (prog : Prog Unit Unit 1 1) : Prop where
  h : MatrixFree (𝕜 := ℝ) () prog (fun _ _ => True) (fun _ _ => Unit)
    (fun _ _ _ => ![Array.replicate 1 none]) (fun _ _ => 0) (fun _ _ _ => 1)
    (fun _ _ _ _ _ _ => True)

/-- Through a class instance.

Result: fixture-instance -/
instance runsFastSkip : RunsFast (.skip : Prog Unit Unit 1 1) := ⟨by
  intro N n _ x A ξ
  refine ⟨_, rfl, le_rfl, fun _ => ?_, trivial⟩
  simp [inputState, exactInterp]⟩

/-- A target of the prover's with a result id: a definition of type `Prop` that unfolds to a
model.

Result: fixture-prop-def -/
def FixPropDef : Prop := FixHutchpp

/-- A definition with a proof inside (item 3: an edit of the proof leaves the hash). -/
def finOne : Fin 2 := ⟨1, by decide⟩

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
  let flagged ← liftTermElabM <|
    unregisteredResults env here (NameSet.empty.insert ``TargetFixtures.fixHutchpp)
  let expected := [``TargetFixtures.matrixFree_sizeTraceProg, ``TargetFixtures.exec_copyTrace,
      ``TargetFixtures.fixUnregistered, ``TargetFixtures.wrapped, ``TargetFixtures.viaNonempty,
      ``TargetFixtures.indRun, ``TargetFixtures.runsFastSkip, ``TargetFixtures.FixPropDef]
  for c in expected do
    unless flagged.contains c do fail m!"{c} is not flagged"
  if flagged.size != expected.length then fail m!"item 2 flags {flagged}"
  logInfo m!"item 2: {flagged} flagged"
  -- item 3: the registered tree is a leaf, and the kernel checks that it is its normal form
  let (nf, defs) ← liftTermElabM <| treeNF ``TargetFixtures.hppC
  unless defs.isEmpty do fail m!"the tree's normal form contains {defs}"
  if let some e ← liftTermElabM (kernelTreeEq ``TargetFixtures.hppC nf) then
    fail m!"the kernel rejects the tree's normal form: {e}"
  let wrong ← liftTermElabM <| lambdaTelescope nf fun xs body => do
    let ty ← whnf (← inferType body)
    let skip ← mkAppOptM ``NLAlib.Computation.FStmt.skip (ty.getAppArgs.map some)
    mkLambdaFVars xs (← mkAppM ``NLAlib.Computation.FStmt.seq #[skip, body])
  if (← liftTermElabM (kernelTreeEq ``TargetFixtures.hppC wrong)).isNone then
    fail m!"the kernel accepts a term that is not the tree's normal form"
  let trees := fun n => if n == ``TargetFixtures.hppC then some nf else none
  let cl ← liftTermElabM <| closure (fun _ => none) trees F
  if cl.names.contains ``NLAlib.hutchppProg || cl.names.contains ``NLAlib.Computation.Stmt.compile
  then fail m!"the builder or the compiler is in the closure of a target with its tree as a leaf"
  let h₀ ← closureHash cl
  unless h₀ == (← closureHash (← liftTermElabM <| closure (fun _ => none) trees F)) do
    fail m!"the hash is not stable"
  let edit (root c : Name) (f : Expr → Expr) : CommandElabM (Bool × String) := do
    let some (.defnInfo d) := env.find? c | throwError "{c} is not a definition"
    let o := fun n => if n == c then some (ConstantInfo.defnInfo { d with value := f d.value })
      else none
    let cl' ← liftTermElabM <| closure (fun _ => none) trees root
    let cl₁ ← liftTermElabM <| closure o trees root
    return (cl'.names.contains c,
      if (← closureHash cl') == (← closureHash cl₁) then "unchanged" else "changed")
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
  -- an edit of a proof leaves the hash (proofs are erased)
  let some (.defnInfo dOne) := env.find? ``TargetFixtures.finOne | throwError "no finOne"
  let v₂ ← liftTermElabM do instantiateMVars (← Term.elabTerm (← `(⟨1, Nat.one_lt_two⟩)) dOne.type)
  if v₂ == dOne.value then fail m!"the proof edit of finOne is not an edit"
  let r ← edit ``TargetFixtures.finOne ``TargetFixtures.finOne fun _ => v₂
  unless r == (true, "unchanged") do fail m!"an edit of the proof in finOne: {r}"
  -- the hygienic names of a closure are numbered, one canonical name each
  let clTail ← liftTermElabM <| closure (fun _ => none) trees ``TargetFixtures.FixHutchppTail
  let hyg := clTail.names.filter (·.hasMacroScopes)
  let canon := hyg.filterMap (clTail.canon[·]?)
  if hyg.isEmpty || canon.size != hyg.size || (canon.toList.eraseDups.length != canon.size) ||
      canon.any fun c => (c.splitOn "_hygCtx").length > 1 then
    fail m!"the hygienic names of the tail's closure are not renamed one to one: {hyg}"
  logInfo m!"item 3: {cl.names.size} constants, builder outside; the kernel checks the tree's {""
    }normal form and rejects another; edits of hutchppCount, of {u} (under {""
    }hansonWrightConstant) and of Matrix.compound (ForMathlib) change the hash, an edit of a {""
    }proof does not; {hyg.size} hygienic names renamed one to one"
  -- item 4: a toolchain mismatch, a manifest mismatch
  let pins ← buildPins
  let reg : Registry := { top := (pins.fields.map fun (k, _, v) => (k, Val.str v)).toArray }
  unless (pinErrors reg pins).isEmpty do fail m!"the build's own pins are rejected"
  if (pinErrors reg { pins with toolchain := "leanprover/lean4:v4.0.0" }).size != 1 then
    fail m!"a toolchain mismatch is not detected"
  if (pinErrors reg { pins with manifest := "0" }).size != 1 ||
      (pinErrors reg { pins with lakefile := "0" }).size != 1 then
    fail m!"a lake-manifest.json or lakefile.toml mismatch is not detected"
  logInfo "item 4: a toolchain, a lake-manifest.json and a lakefile.toml mismatch detected"
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
