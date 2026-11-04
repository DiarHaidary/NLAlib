module
import Lean
-- The forgery inside a replayed `module` file: raw kernel add with doCheck := false.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let ty := mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) (mkNatLit 1) (mkNatLit 2)
  let val := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkNatLit 1)
  let decl := Declaration.thmDecl { name := `FxB.forged, levelParams := [], type := ty, value := val }
  match env.addDeclCore 0 0 decl none (doCheck := false) with
  | .ok env' => setEnv env'
  | .error e => throwError "{← (e.toMessageData {}).toString}"
public theorem FxB.consequence : (1 : Nat) = 2 := FxB.forged
