import Lean
open Lean Elab Command

/-! # Kernel replay

Every constant of the package's `.olean` files is sent to Lean's kernel again, by Lean core's
`Lean.Environment.replay` (the function `lean4checker` is built on), so that what the library
contains is what the kernel accepts, whatever the elaborator was told. A proof elaborated under
`set_option debug.skipKernelTC true`, a declaration added by meta code without checking (for
example `env.addDeclCore … (doCheck := false)`), or an `.olean` edited after the build is rejected
here; `scripts/Audit.lean` cannot see them, since it reads the axioms a constant uses, not whether
the kernel checked it. Final audits, 2026-10-24 (`docs/design/Computation.md`, "Final audits").

How it works. The roots are every `lean_lib` of `lakefile.toml` (`NLAlib`, `NLAlibScaffold`,
`NLAlibTools`). The script reads the `.olean` files of the replayed modules (the roots and every
module they import whose name has a root as a prefix: `NLAlib` and `NLAlib.*`, and so on), every
part of each, so that private declarations and proofs are included, and imports, as the base, the
other modules those modules import (Lean, Batteries, Mathlib and their dependencies). The base is
trusted as the builds of other projects, so it must be one: every module of the base (its whole
import closure) must resolve, through the search path, to an `.olean` under `.lake/packages/` of
the working directory (the package's dependencies) or under the `lib/lean` of the running
toolchain; any other location, the package's own `.lake/build` first of all, fails the script.
It checks that no replayed module is reachable from the base, then replays every replayed
constant into the base, in dependency order, through the kernel (`Kernel.Environment.addDeclCore`):
definitions, theorems, opaques and axioms are type checked, inductive types are re-added and
their constructors and recursors compared with the kernel's.

Strict libraries. `NLAlib` (or the roots in `REPLAY_STRICT`) and every library one of its modules
imports, recursively, are strict. In a module of a strict library the script fails on
* an `unsafe` or `partial` constant (`replay` skips both: the kernel does not check their bodies),
  except the auxiliaries `f._unsafe_rec` of safe definitions `f` (`isUnsafeRecAux`). A safe
  constant that uses a skipped one fails the replay, as an unknown constant; that is why the
  exception is sound, even for a hand-named `partial` constant `f._unsafe_rec` beside a safe `f`,
  which is counted as an auxiliary and is harmless: any use of it fails;
* an axiom, and a constant whose type or value uses `sorryAx`, `Lean.ofReduceBool`,
  `Lean.ofReduceNat` or `Lean.trustCompiler` (defence in depth beside `scripts/Audit.lean`,
  which follows axioms through every dependency).
In the other libraries (`NLAlibScaffold` and `NLAlibTools`, which may contain `sorry`) these are
only counted.

Run with `lake env lean scripts/Replay.lean` from the repository root, after
`lake build NLAlib NLAlibScaffold NLAlibTools` and `lake build --no-build --rehash` of the same
targets (the freshness check: the `.olean` files are those of the current sources;
`scripts/stage_check.sh` and CI do both). A nonzero exit code means a violation.
`REPLAY_ROOTS` (space-separated module names) replaces the roots, for fixtures; CI and the stage
check pass none. -/

namespace KernelReplay

/-- A space-separated list of module names from an environment variable. -/
def namesOfEnv (var : String) : IO (Option (List Name)) := do
  match ← IO.getEnv var with
  | some s => return some <| (s.splitOn " ").filterMap fun w =>
      let w := w.trimAscii.toString
      if w.isEmpty then none else some w.toName
  | none => return none

/-- The names of the `lean_lib` targets of `lakefile.toml` in the working directory. A library
setting `roots` or `globs` is refused: its modules would not all be found from its name. -/
def lakefileLibs : IO (List Name) := do
  let f : System.FilePath := "lakefile.toml"
  unless ← f.pathExists do
    throw <| IO.userError "replay: no lakefile.toml; run from the repository root"
  let mut libs : Array Name := #[]
  let mut inLib := false
  for l in (← IO.FS.readFile f).splitOn "\n" do
    let l := ((l.splitOn "#").headD "").trimAscii.toString
    if l.startsWith "[" then inLib := l == "[[lean_lib]]"
    else if inLib then
      match l.splitOn "=" with
      | [k, v] =>
        let k := k.trimAscii.toString
        if k == "name" then libs := libs.push (v.trimAscii.toString.replace "\"" "").toName
        else if k == "roots" || k == "globs" then
          throw <| IO.userError s!"replay: a lean_lib of lakefile.toml sets `{k}`; {""
            }the replay finds a library's modules from its name only"
      | _ => pure ()
  if libs.isEmpty then throw <| IO.userError "replay: no lean_lib in lakefile.toml"
  return libs.toList

/-- The data of a module, read from its `.olean` files: for a `module` file every part, the last
(`.olean.private`) holding every constant with its value, proofs included. -/
def readModule (m : Name) : IO ModuleData := do
  let f ← findOLean m
  unless ← f.pathExists do
    throw <| IO.userError s!"replay: {m} has no .olean ({f}); build it first"
  let priv := OLeanLevel.private.adjustFileName f
  if ← priv.pathExists then
    let parts ← readModuleDataParts #[f, OLeanLevel.server.adjustFileName f, priv]
    let some (data, _) := parts.back? | throw <| IO.userError s!"replay: {m}: no module data"
    return data
  return (← readModuleData f).1

/-- **A compiler auxiliary**: `f._unsafe_rec`, the `partial` copy of a safe definition `f` by
well-founded or structural recursion that Lean adds for the code generator. The kernel never
checks it, and a safe constant cannot use it (the replay skips it, so a use fails the replay as an
unknown constant); it is the one `partial` constant a strict module may contain. A hand-named
`partial` `f._unsafe_rec` beside a safe `f` is counted here too, and is harmless for the same
reason: any use of it fails. -/
def isUnsafeRecAux (find? : Name → Option ConstantInfo) (c : ConstantInfo) : Bool :=
  match c.name with
  | .str p "_unsafe_rec" => c.isPartial && match find? p with
    | some (.defnInfo d) => d.safety == .safe
    | _ => false
  | _ => false

/-- The constants of Lean core through which a proof can rest on something other than the kernel:
`sorry`, the compiler (`native_decide`) and the trusted-compiler marker. -/
def untrusted : List Name := [``sorryAx, ``Lean.ofReduceBool, ``Lean.ofReduceNat,
  ``Lean.trustCompiler]

/-- Whether `p` lies in the directory `dir` (both resolved). -/
def isUnder (dir p : System.FilePath) : Bool :=
  p.toString.startsWith (dir.toString ++ System.FilePath.pathSeparator.toString)

end KernelReplay

open KernelReplay in
run_cmd do
  let envRoots ← namesOfEnv "REPLAY_ROOTS"
  let roots ← match envRoots with
    | some r => pure r
    | none => lakefileLibs
  let strict0 := (← namesOfEnv "REPLAY_STRICT").getD
    (if roots.contains `NLAlib then [`NLAlib] else roots)
  let rootOf? (m : Name) : Option Name := roots.find? (·.isPrefixOf m)
  -- the replayed modules, from the roots through their imports, each read whole
  let mut todo := roots
  let mut seen : NameSet := {}
  let mut importsOf : Std.HashMap Name (Array Name) := {}
  let mut moduleConstants : Array (Name × ConstantInfo) := #[]
  let mut newConstants : Std.HashMap Name ConstantInfo := {}
  let mut base : NameSet := {}
  while !todo.isEmpty do
    let m := todo.head!
    todo := todo.tail!
    if seen.contains m then continue
    seen := seen.insert m
    let data ← readModule m
    let mut imps := #[]
    for imp in data.imports do
      if (rootOf? imp.module).isSome then
        todo := imp.module :: todo
        imps := imps.push imp.module
      else base := base.insert imp.module
    importsOf := importsOf.insert m imps
    for c in data.constants do
      newConstants := newConstants.insert c.name c
      moduleConstants := moduleConstants.push (m, c)
  -- strict libraries: the strict roots and, recursively, every library one of their modules imports
  let mut strictLibs := strict0
  let mut changed := true
  while changed do
    changed := false
    for (m, imps) in importsOf do
      if (rootOf? m).any strictLibs.contains then
        for i in imps do
          if let some r := rootOf? i then
            unless strictLibs.contains r do
              strictLibs := strictLibs ++ [r]
              changed := true
  let isStrict (m : Name) : Bool := (rootOf? m).any strictLibs.contains
  -- the base: only the builds of other projects, never this package's own
  let baseEnv ← importModules (base.toArray.map fun m => { module := m }) {} (loadExts := false)
  let trusted := [← realPathNormalized ((← IO.currentDir) / ".lake" / "packages"),
    ← realPathNormalized (← getLibDir (← getBuildDir))]
  let mut bad : Nat := 0
  let mut untrustedBase : Array (Name × System.FilePath) := #[]
  for m in baseEnv.header.moduleNames do
    let f ← realPathNormalized (← findOLean m)
    unless trusted.any (isUnder · f) do untrustedBase := untrustedBase.push (m, f)
  unless untrustedBase.isEmpty do
    bad := bad + untrustedBase.size
    let shown := (untrustedBase.extract 0 10).toList.map fun (m, f) => s!"{m} (read from {f})"
    logError m!"replay: {untrustedBase.size} base modules are read from outside the {""
      }dependencies ({trusted[0]!}) and the toolchain ({trusted[1]!}), so would be trusted {""
      }unchecked: {", ".intercalate shown}{if untrustedBase.size > 10 then ", …" else ""}"
  let reached := baseEnv.header.moduleNames.filter (rootOf? · |>.isSome)
  unless reached.isEmpty do
    throwError "replay: the base (the imports of the replayed modules outside the roots) {""
      }reaches the replayed modules {reached}"
  let mut aux : Nat := 0
  let mut skipped : Nat := 0
  let mut lax : Nat := 0
  for (m, c) in moduleConstants do
    let strictM := isStrict m
    if c.isUnsafe || c.isPartial then
      if isUnsafeRecAux (newConstants.get? ·) c then aux := aux + 1
      else
        skipped := skipped + 1
        if strictM then
          bad := bad + 1
          logError m!"replay: {c.name} (in {m}) is `unsafe` or `partial`: the kernel does not {""
            }check it"
        else lax := lax + 1
    if c matches .axiomInfo _ then
      if strictM then
        bad := bad + 1
        logError m!"replay: {c.name} (in {m}) is an axiom"
      else lax := lax + 1
    let used := c.getUsedConstantsAsSet
    let hits := untrusted.filter used.contains
    unless hits.isEmpty do
      if strictM then
        bad := bad + 1
        logError m!"replay: {c.name} (in {m}) uses {hits}"
      else lax := lax + 1
  try
    discard <| baseEnv.replay newConstants
  catch e =>
    bad := bad + 1
    logError m!"replay: the kernel rejects the library: {e.toMessageData}"
  logInfo m!"replay: {newConstants.size} constants of {seen.size} modules under {roots} {""
    }(strict: {strictLibs}) replayed through the kernel onto {base.size} base imports {""
    }({baseEnv.header.moduleNames.size} modules, all from the dependencies or the toolchain {""
    }unless reported); {aux} compiler auxiliaries `_unsafe_rec` and {skipped} other unsafe {""
    }or partial constants not replayed; {lax} findings in non-strict libraries; {bad} violations"
