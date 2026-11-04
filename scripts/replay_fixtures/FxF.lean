module
-- An axiom, and private / mutual / nested / match / quotient content that must pass.
axiom FxF.ax : (1 : Nat) = 2
public theorem FxF.fromAx : (1 : Nat) = 2 := FxF.ax
private theorem FxF.priv : (3 : Nat) = 3 := rfl
public theorem FxF.usesPriv : (3 : Nat) = 3 := FxF.priv
mutual
  inductive FxF.Ev : Nat → Prop | zero : FxF.Ev 0 | succ : FxF.Od n → FxF.Ev (n+1)
  inductive FxF.Od : Nat → Prop | succ : FxF.Ev n → FxF.Od (n+1)
end
inductive FxF.Tree | node : List FxF.Tree → FxF.Tree
def FxF.Tree.size : FxF.Tree → Nat | .node ts => 1 + (ts.map FxF.Tree.size).sum
public def FxF.fib : Nat → Nat | 0 => 0 | 1 => 1 | n+2 => FxF.fib n + FxF.fib (n+1)
public theorem FxF.fib5 : FxF.fib 5 = 5 := by decide
@[expose] public def FxF.Q := Quot (fun (a b : Nat) => a % 2 = b % 2)
public theorem FxF.q : (Quot.mk _ 0 : FxF.Q) = Quot.mk _ 2 := Quot.sound rfl
