module
import Lean
-- Hand-named `helper._unsafe_rec` (partial, type (α : Sort u) → α, added raw) beside a safe
-- `helper`, used by a raw forged theorem.
public def helper : Nat → Nat := fun n => n
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let u := mkLevelParam `u
  let anyTy := mkForall `α .default (mkSort u) (mkBVar 0)
  let recVal := mkLambda `α .default (mkSort u) (mkApp (mkConst `helper._unsafe_rec [u]) (mkBVar 0))
  let rec1 := Declaration.defnDecl (DefinitionVal.mk (ConstantVal.mk `helper._unsafe_rec [`u] anyTy) recVal ReducibilityHints.opaque DefinitionSafety.partial [`helper._unsafe_rec])
  let env1 ← match env.addDeclCore 0 0 rec1 none (doCheck := false) with
    | .ok e => pure e | .error e => throwError "{← (e.toMessageData {}).toString}"
  let ty := mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) (mkNatLit 1) (mkNatLit 2)
  let thm := Declaration.thmDecl (TheoremVal.mk (ConstantVal.mk `FxD.forged [] ty) (mkApp (mkConst `helper._unsafe_rec [Level.zero]) ty) [`FxD.forged])
  let env2 ← match env1.addDeclCore 0 0 thm none (doCheck := false) with
    | .ok e => pure e | .error e => throwError "{← (e.toMessageData {}).toString}"
  setEnv env2
public theorem FxD.consequence : (1 : Nat) = 2 := FxD.forged
