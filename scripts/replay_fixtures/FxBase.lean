import Lean
-- A "base" module (not under any replay root): a theorem added to the kernel with no check, no
-- `set_option`, no `unsafe`, no axiom. Mimics a forged lemma in NLAlibScaffold or a redirected
-- dependency.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let ty := mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) (mkNatLit 1) (mkNatLit 2)
  let val := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkNatLit 1)
  let decl := Declaration.thmDecl { name := `FxBase.forged, levelParams := [], type := ty, value := val }
  match env.addDeclCore 0 0 decl none (doCheck := false) with
  | .ok env' => setEnv env'
  | .error e => throwError "{← (e.toMessageData {}).toString}"
#check @FxBase.forged
