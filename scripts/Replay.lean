import Lean
open Lean Elab Command

/-! # Kernel replay

Every constant of the library's `.olean` files is sent to Lean's kernel again, by Lean core's
`Lean.Environment.replay` (the function `lean4checker` is built on), so that what the library
contains is what the kernel accepts, whatever the elaborator was told. A proof elaborated under
`set_option debug.skipKernelTC true`, a declaration added by meta code without checking, or an
`.olean` edited after the build is rejected here; `scripts/Audit.lean` cannot see them, since it
reads the axioms a constant uses, not whether the kernel checked it. Final audit, 2026-10-24
(`docs/design/Computation.md`, "Final audits").

How it works. The script reads the `.olean` files of the replayed modules (the roots, default
`NLAlib`, and every module they import whose name has a root as a prefix: `NLAlib` and
`NLAlib.*`, not `NLAlibScaffold` or `NLAlibTools`), every part of each, so that private
declarations and proofs are included, and imports, as the base, the other modules those modules
import (Lean, Batteries, Mathlib and their dependencies, trusted as their own
projects' builds). It checks that no replayed module is reachable from the base, then replays
every replayed constant into the base, in dependency order, through the kernel
(`Kernel.Environment.addDeclCore`): definitions, theorems, opaques and axioms are type checked,
inductive types are re-added and their constructors and recursors compared with the kernel's.
`replay` skips `unsafe` and `partial` constants (the kernel does not check their bodies), so the
script fails on any such constant in a replayed module of a root listed in `REPLAY_STRICT`
(default: every root), except the compiler's auxiliaries `f._unsafe_rec` of safe definitions `f`
(`isUnsafeRecAux`); and a safe constant that uses a skipped one fails the replay, as an unknown
constant.

Run with `lake env lean scripts/Replay.lean` after `lake build NLAlib`; a nonzero exit code means
a violation. `REPLAY_ROOTS="NLAlib NLAlibTools"` replays the tools library as well (`NLAlibTools`
may contain `sorry`, which the kernel accepts as the axiom it is; `scripts/Audit.lean` is the
check on axioms). `REPLAY_STRICT` (a sublist of the roots) names the roots on which an `unsafe` or
`partial` constant fails the script; the others only report it. -/

namespace KernelReplay

/-- A space-separated list of module names from an environment variable. -/
def namesOfEnv (var : String) (default : List Name) : IO (List Name) := do
  match ← IO.getEnv var with
  | some s => return (s.splitOn " ").filterMap fun w =>
      let w := w.trimAscii.toString
      if w.isEmpty then none else some w.toName
  | none => return default

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
unknown constant); it is the one `partial` constant a library module may contain. -/
def isUnsafeRecAux (find? : Name → Option ConstantInfo) (c : ConstantInfo) : Bool :=
  match c.name with
  | .str p "_unsafe_rec" => c.isPartial && match find? p with
    | some (.defnInfo d) => d.safety == .safe
    | _ => false
  | _ => false

end KernelReplay

open KernelReplay in
run_cmd do
  let roots ← namesOfEnv "REPLAY_ROOTS" [`NLAlib]
  let strict ← namesOfEnv "REPLAY_STRICT" roots
  let inScope (m : Name) : Bool := roots.any (·.isPrefixOf m)
  -- the replayed modules, from the roots through their imports, each read whole
  let mut todo := roots
  let mut seen : NameSet := {}
  let mut newConstants : Std.HashMap Name ConstantInfo := {}
  let mut base : NameSet := {}
  let mut modules : Nat := 0
  let mut skipped : Array (Name × Name) := #[]
  let mut aux : Nat := 0
  while !todo.isEmpty do
    let m := todo.head!
    todo := todo.tail!
    if seen.contains m then continue
    seen := seen.insert m
    modules := modules + 1
    let data ← readModule m
    for imp in data.imports do
      if inScope imp.module then todo := imp.module :: todo else base := base.insert imp.module
    for c in data.constants do
      newConstants := newConstants.insert c.name c
    for c in data.constants do
      if c.isUnsafe || c.isPartial then
        if isUnsafeRecAux (newConstants.get? ·) c then aux := aux + 1
        else skipped := skipped.push (m, c.name)
  let baseEnv ← importModules (base.toArray.map fun m => { module := m }) {} (loadExts := false)
  let reached := baseEnv.header.moduleNames.filter inScope
  unless reached.isEmpty do
    throwError "replay: the base (the imports of the replayed modules outside the roots) {""
      }reaches the replayed modules {reached}"
  let mut bad : Nat := 0
  for (m, c) in skipped do
    if strict.any (·.isPrefixOf m) then
      bad := bad + 1
      logError m!"replay: {c} (in {m}) is `unsafe` or `partial`: the kernel does not check it"
    else logInfo m!"replay: {c} (in {m}) is `unsafe` or `partial`, not replayed"
  try
    discard <| baseEnv.replay newConstants
  catch e =>
    bad := bad + 1
    logError m!"replay: the kernel rejects the library: {e.toMessageData}"
  logInfo m!"replay: {newConstants.size} constants of {modules} modules under {roots} {""
    }replayed through the kernel onto {base.size} base imports; {aux} compiler auxiliaries {""
    }`_unsafe_rec` and {skipped.size} other unsafe or partial constants not replayed; {""
    }{bad} violations"
