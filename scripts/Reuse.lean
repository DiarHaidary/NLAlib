import NLAlib
open Lean Meta Elab Command

/-! # Reuse report

For each target declaration, the constants its proof term uses directly, grouped by module, NLAlib
modules first: a reviewer can see at a glance whether a headline theorem is proved from the
library's API for its topic or from scratch. Omitted: the constants of the statement itself,
everything from core `Init` (logic, `Eq.mpr`, `congrArg`, notation classes), the lemmas tactics
such as `ring` and `norm_num` insert (modules `Mathlib.Tactic.*`) and instances; the omitted ones
are counted in the header line. Auxiliary declarations generated for the proof (`proof_`,
`match_`, `_auxLemma` and other internal names) are expanded into the constants they use.

Targets are read from `scripts/reuse_targets.txt` (or the file named by the environment variable
`NLALIB_REUSE_TARGETS`), one per line: a declaration name, or `module M` for every public theorem
of module `M`; `#` starts a comment. Run from the repository root with
`lake env lean scripts/Reuse.lean`; replace the first line by imports of the targets' modules to
avoid loading the whole library. -/

/-- The constants the value of `n` uses, with internal auxiliary declarations expanded. -/
partial def reuseConstants (env : Environment) (n : Name) : NameSet := Id.run do
  let mut out : NameSet := {}
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[n]
  while h : todo.size > 0 do
    let c := todo.back
    todo := todo.pop
    let some ci := env.find? c | continue
    let some v := ci.value? (allowOpaque := true) | continue
    for d in v.getUsedConstants do
      if seen.contains d then continue
      seen := seen.insert d
      if (privateToUserName d).isInternalDetail then todo := todo.push d
      else out := out.insert d
  return out

run_cmd do
  let env ← getEnv
  let mods := env.header.moduleNames
  let modOf (n : Name) : Name := match env.getModuleIdxFor? n with
    | some i => mods[i.toNat]!
    | none => env.mainModule
  let fmt (n : Name) : String := s!"{privateToUserName n}{if isPrivateName n then " (private)" else ""}"
  let path := (← IO.getEnv "NLALIB_REUSE_TARGETS").getD "scripts/reuse_targets.txt"
  let lines ← try IO.FS.lines path catch _ => do
    logError m!"cannot read {path}"; pure #[]
  -- User names of private declarations, so that targets can name them.
  let mut privates : Std.HashMap Name Name := {}
  for (n, _) in env.constants.map₁ do
    if isPrivateName n then privates := privates.insert (privateToUserName n) n
  let mut targets : Array Name := #[]
  for l in lines do
    let l := l.trimAscii.toString
    if l.isEmpty || l.startsWith "#" then continue
    if l.startsWith "module " then
      let m := (l.drop 7).trimAscii.toString.toName
      let mut ts : Array Name := #[]
      for (n, ci) in env.constants.map₁ do
        if let .thmInfo _ := ci then
          if modOf n == m && !isPrivateName n && !n.isInternalDetail &&
              !env.isProjectionFn n && !isInstanceCore env n then
            ts := ts.push n
      if ts.isEmpty then logWarning m!"no public theorems of module {m} in the environment"
      targets := targets ++ ts.qsort (·.toString < ·.toString)
    else
      let n := l.toName
      match (if env.contains n then some n else privates.get? n) with
      | some n => targets := targets.push n
      | none => logWarning m!"unknown declaration {n}"
  let mut out : Array String := #[]
  for t in targets do
    let some ci := env.find? t | continue
    let stmt := ci.type.getUsedConstants
    let mut core : Nat := 0
    let mut insts : Nat := 0
    let mut tactic : Nat := 0
    let mut groups : Std.HashMap Name (Array Name) := {}
    for c in reuseConstants env t do
      if stmt.contains c || c == t then continue
      let m := modOf c
      if (`Init).isPrefixOf m then core := core + 1
      else if (`Mathlib.Tactic).isPrefixOf m then tactic := tactic + 1
      else if isInstanceCore env c then insts := insts + 1
      else groups := groups.alter m fun l? => some ((l?.getD #[]).push c)
    let lib := groups.fold (fun s m cs => if (`NLAlib).isPrefixOf m then s + cs.size else s) 0
    let total := groups.fold (fun s _ cs => s + cs.size) 0
    out := out.push s!"{fmt t} [{modOf t}]: {lib} NLAlib and {total - lib} other constants \
      (omitted: {core} core, {tactic} tactic internals, {insts} instances)"
    let sorted := groups.toArray.qsort fun (m₁, c₁) (m₂, c₂) =>
      let l₁ := (`NLAlib).isPrefixOf m₁
      let l₂ := (`NLAlib).isPrefixOf m₂
      (l₁ && !l₂) || (l₁ == l₂ && (c₁.size > c₂.size ||
        (c₁.size == c₂.size && m₁.toString < m₂.toString)))
    for (m, cs) in sorted do
      let names := ", ".intercalate ((cs.qsort (·.toString < ·.toString)).toList.map fmt)
      out := out.push s!"  {m} ({cs.size}): {names}"
  logInfo ("\n".intercalate out.toList)
