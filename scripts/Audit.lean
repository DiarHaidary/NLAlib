import NLAlib
open Lean Elab Command

/-! # Axiom audit

Every declaration reachable through `import NLAlib` (public and private, theorems, definitions
and instances) may depend only on `propext`, `Classical.choice` and `Quot.sound`. In particular
nothing depends on `sorryAx`. No constant of an `NLAlib` module is `unsafe` or `partial`: the
kernel does not check the body of either, and a theorem elaborated through one under
`set_option debug.skipKernelTC true` uses no axiom (final audit, 2026-10-24). The one exception
is the compiler's `f._unsafe_rec`, the `partial` copy of a safe recursive definition `f` that
Lean adds for the code generator, which no safe constant can use. The kernel itself
re-checks every constant in `scripts/Replay.lean`, and rule S9 forbids the keywords in the
sources. Run with `lake env lean scripts/Audit.lean`; a nonzero exit code means a violation. -/

run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  let mut bad : Nat := 0
  for (name, info) in env.constants.map₁.toList do
    let inLibrary := match env.getModuleIdxFor? name with
      | some i => (`NLAlib).isPrefixOf env.header.moduleNames[i.toNat]!
      | none => false
    if inLibrary then
      count := count + 1
      -- the compiler's `f._unsafe_rec` of a safe recursive definition `f` is the one exception
      let aux := match name with
        | .str p "_unsafe_rec" => info.isPartial && match env.find? p with
          | some (.defnInfo d) => d.safety == .safe
          | _ => false
        | _ => false
      if (info.isUnsafe || info.isPartial) && !aux then
        bad := bad + 1
        logError m!"{name} is {if info.isUnsafe then "unsafe" else "partial"}: the kernel does not {""
          }check its body"
      let extra := (← collectAxioms name).filter (fun a => !allowed.contains a)
      unless extra.isEmpty do
        bad := bad + 1
        logError m!"{name} depends on forbidden axioms {extra}"
  logInfo m!"audited {count} declarations reachable through import NLAlib (axioms, unsafe and {""
    }partial constants); {bad} violations"
