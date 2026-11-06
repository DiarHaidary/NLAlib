/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.StaticCost
public import NLAlibScaffold.Matrix.Computation.SpectralBisectionNode

/-!
# The spectral bisection program computes `eigh` (scaffold)

Statements for a new file `NLAlib/Matrix/Computation/SpectralBisectionProgram.lean` (stage COMPDYN
S2b, design note `docs/design/Computation-EighProgram.md`, §4 to §5): the refinement of the program
`NLAlib.eighProg` to the shallow `NLAlib.eigh`.

* **The recursion by levels.** The nodes of the shallow recursion at depth $d$, with their slots
  (`NLAlib.eighLoc`), have the window, tolerance and depth counter of their depth, lie in $[0, n)$,
  and have disjoint ranges; the tree of samples at the slots (`NLAlib.eighSlotTree`) restricts to
  subtrees, and the nodes `NLAlib.eighNodeAt` reaches with it are those of `NLAlib.eighLoc`.
* **The levels.** One level of the downward pass takes the arenas from holding the nodes of depth
  $d$ to holding those of depth $d + 1$ and the records of depth $d$; the spent level writes the
  junk outputs; one level of the upward pass takes the outputs of depth $d + 1$ to those of depth
  $d$ (`NLAlib.EighArenas.LevelHolds`, `NLAlib.EighArenas.RecordHolds`,
  `NLAlib.EighArenas.OutHolds`).
* **The refinement** (§7.1 of `docs/design/Computation-DynamicPrograms.md`): (a) under kernels
  that are routines on pairs, a semantics that decides flags, exact integer literals up to $n + 4$
  and the exact floor conversion, **every successful run writes exactly `NLAlib.eigh`** on the
  machine of the interpretation (`NLAlib.eighTapeMachine`) with the tree of samples at the slots;
  (b) under the standard model with every value in range, $u < 1$, $\ell_0 \ge 1$ and
  $\varepsilon, R_0 \ge 0$, **every run succeeds** (the sign step has the shallow step limit, so no
  run fails for want of steps).
* **Counts**: the static bound `NLAlib.eighCount` and the memory, and the weighted kernel bound of
  [Shah2024, Section 4] for a superadditive cost.

## Main results

* `NLAlib.eighNodeAt_eighSlotTree`, `NLAlib.eighSlotTree_append_of_eighLoc`,
  `NLAlib.eighLoc_params`, `NLAlib.eighLoc_bounds`, `NLAlib.eighLoc_disjoint`,
  `NLAlib.eighLoc_append_singleton`: the recursion by levels.
* `NLAlib.holds_of_exec_eighDownLevel`, `NLAlib.exists_exec_eighDownLevel`,
  `NLAlib.holds_of_exec_eighBottomLevel`, `NLAlib.exists_exec_eighBottomLevel`,
  `NLAlib.holds_of_exec_eighUpLevel`, `NLAlib.exists_exec_eighUpLevel`: the levels.
* `NLAlib.holds_of_exec_eighProg`, `NLAlib.exists_exec_eighProg`: the refinement for the builder.
* `NLAlib.eighProg.toStmt_compiled`, `NLAlib.eighProg.holds_of_exec_compiled`,
  `NLAlib.eighProg.exists_exec_compiled`, `NLAlib.eighProg.cnt_le_of_exec_compiled`,
  `NLAlib.eighProg.weight_le_of_exec_compiled`: the registered tree.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

/-! ### The recursion by levels -/

section Levels

variable {F : Type*} {M : FloatMachine F ℕ ℕ} {N signFuel : ℕ} {R₀ β : F}

/-- **The nodes at the slots are the nodes of the tree of samples at the slots**: at every path,
`NLAlib.eighNodeAt` with the samples `NLAlib.eighSlotTree` (from the node $x$ at slot $lo$ of depth
$d$) reaches the node that `NLAlib.eighLoc` reaches. No printed source.
Proof: induction on the path generalizing $d$, $lo$, $x$; unfold `NLAlib.eighNodeAt`,
`NLAlib.eighChild`, `NLAlib.eighLoc` and `NLAlib.eighSlotTree`: at the empty path both give $x$; at
$b :: a$ the sample at the empty path is `NLAlib.eighTapeSample N d lo` on both sides, and the
subtree of the samples below the child is the tree at the child's slot (`split` on
`NLAlib.eighStep`, the side test as in `NLAlib.eighChild`). M, about 30 lines. -/
theorem eighNodeAt_eighSlotTree :
    ∀ (a : List Bool) (d lo : ℕ) (x : EighNode F),
      eighNodeAt M N signFuel R₀ β a x (eighSlotTree M N signFuel R₀ β d lo x) =
        (eighLoc M N signFuel R₀ β d lo x a).map Prod.snd := by
  sorry

/-- **The tree of samples at the slots restricts to subtrees**: below a path that reaches the node
$y$ at slot $lo'$, the tree of samples is the tree from $y$ at slot $lo'$ of the depth of the path.
No printed source.
Proof: induction on the path generalizing $d$, $lo$, $x$, unfolding `NLAlib.eighLoc` and
`NLAlib.eighSlotTree` at $b :: a$ (`List.cons_append`); the cases of `NLAlib.eighStep` match; at a
leaf or on the absent side `h` is `none`. M, about 25 lines. -/
theorem eighSlotTree_append_of_eighLoc :
    ∀ {a : List Bool} {d lo lo' : ℕ} {x y : EighNode F},
      eighLoc M N signFuel R₀ β d lo x a = some (lo', y) →
        (fun a' => eighSlotTree M N signFuel R₀ β d lo x (a ++ a')) =
          eighSlotTree M N signFuel R₀ β (d + a.length) lo' y := by
  sorry

/-- **The nodes at a depth have the parameters of the depth**: a node that `NLAlib.eighLoc` reaches
from the root $(N, \mathbf{A}, R_0, \varepsilon, \ell_0)$ at a path of length $d$ has the window and
tolerance `NLAlib.eighLevelParams` at $d$ and the depth counter $\ell_0 + d$. No printed source.
Proof: induction on the path from the end (`List.reverseRecOn`) with
`NLAlib.eighLoc_append_singleton`: a child has `NLAlib.eighNextParams` of its parent's window,
tolerance and depth counter, which is `NLAlib.eighLevelParams` at $d + 1$ by definition. M, about
30 lines. -/
theorem eighLoc_params {A : Matrix (Fin N) (Fin N) (F × F)} {ε : F} {ℓ₀ : ℕ} {a : List Bool}
    {lo : ℕ} {y : EighNode F}
    (h : eighLoc M N signFuel R₀ β 0 0 ⟨N, A, R₀, ε, ℓ₀⟩ a = some (lo, y)) :
    y.R = (eighLevelParams M R₀ ε ℓ₀ a.length).1 ∧ y.ε = (eighLevelParams M R₀ ε ℓ₀ a.length).2 ∧
      y.ℓ = ℓ₀ + a.length := by
  sorry

/-- **A child's slot**: the slot and node at the path $a ++ [b]$ are those of the child on side $b$
of the node at $a$, at the slot $lo$ (one child, or the positive side of a split) or $lo + k_+$
(the negative side of a split). No printed source.
Proof: induction on $a$ generalizing $d$, $lo$, $x$; unfold `NLAlib.eighLoc` (`List.cons_append`,
`List.nil_append`). M, about 25 lines. -/
theorem eighLoc_append_singleton :
    ∀ (a : List Bool) (b : Bool) (d lo : ℕ) (x : EighNode F),
      eighLoc M N signFuel R₀ β d lo x (a ++ [b]) =
        (eighLoc M N signFuel R₀ β d lo x a).bind fun z =>
          eighLoc M N signFuel R₀ β (d + a.length) z.1 z.2 [b] := by
  sorry

/-- **The nodes at a depth lie in $[0, N)$ and are not empty**: a node that `NLAlib.eighLoc` reaches
from a root of size $N \ge 1$ at slot $0$ has size at least $1$ and its range $[lo, lo + k)$ inside
$[0, N)$. No printed source.
Proof: induction on the path with `NLAlib.eighLoc_append_singleton`: a one-child node keeps the
size and slot; a split has $0 < k_+ < k$ (`NLAlib.eighStep`: the cases $k_+ = k$ and $k_+ = 0$ are
one-child nodes), so both children are nonempty and $[lo, lo + k_+)$, $[lo + k_+, lo + k)$ cover
$[lo, lo + k)$; `omega`. M, about 30 lines. -/
theorem eighLoc_bounds {A : Matrix (Fin N) (Fin N) (F × F)} {ε : F} {ℓ₀ : ℕ} (hN : 1 ≤ N)
    {a : List Bool} {lo : ℕ} {y : EighNode F}
    (h : eighLoc M N signFuel R₀ β 0 0 ⟨N, A, R₀, ε, ℓ₀⟩ a = some (lo, y)) :
    1 ≤ y.k ∧ lo + y.k ≤ N := by
  sorry

/-- **The nodes at one depth have disjoint ranges**: two distinct paths of the same length that
`NLAlib.eighLoc` follows from the root reach nodes whose ranges $[lo, lo + k)$ do not meet. So the
nodes of one level partition a part of $[0, N)$, and their packed blocks in the arenas are disjoint.
No printed source.
Proof: induction on the common length with `NLAlib.eighLoc_append_singleton`: paths with distinct
parents have disjoint parent ranges (induction hypothesis) containing the children's ranges
(`NLAlib.eighLoc_bounds`' argument); siblings of a split have the disjoint ranges
$[lo, lo + k_+)$ and $[lo + k_+, lo + k)$; a one-child node has one child. M, about 40 lines. -/
theorem eighLoc_disjoint {A : Matrix (Fin N) (Fin N) (F × F)} {ε : F} {ℓ₀ : ℕ}
    {a a' : List Bool} (hlen : a.length = a'.length) (hne : a ≠ a') {lo lo' : ℕ}
    {y y' : EighNode F} (h : eighLoc M N signFuel R₀ β 0 0 ⟨N, A, R₀, ε, ℓ₀⟩ a = some (lo, y))
    (h' : eighLoc M N signFuel R₀ β 0 0 ⟨N, A, R₀, ε, ℓ₀⟩ a' = some (lo', y')) :
    lo + y.k ≤ lo' ∨ lo' + y'.k ≤ lo := by
  sorry

end Levels

/-! ### The levels -/

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}

/-- **One level of the downward pass**: let the kernels of `I` be the routines `mmR`, `qrR` on
interleaved pairs, the semantics decide flags, with exact integer literals up to $n + 4$ and the
exact floor conversion; $M$ = `NLAlib.eighTapeMachine I p mmR qrR` and the root
$(n, \mathbf{A}, R_0, \varepsilon, \ell_0)$. A successful run of `NLAlib.eighDownLevel` at depth
$d < D$ from a state whose arenas hold the nodes of depth $d$ (`NLAlib.EighArenas.LevelHolds`), with
the tape positions $nd$ (uniform) and $4n^2 d$ (Gaussian), the stored $R_0$, $\varepsilon$, $\beta$
in `par` and the constants in `c`, ends with the arenas holding the nodes of depth $d + 1$ and the
records of depth $d$ (`NLAlib.EighArenas.RecordHolds`); every cell outside depths $d$ and $d + 1$ of
the arenas and the sample buffers `Su`, `Sg` is unchanged, the store shape too, and the tape
positions advance by $n$ and $4n^2$. No printed source.
Proof: the parameters of depth $d + 1$ by seven instructions (`NLAlib.eighNextParams` at
$\ell_0 + d$, `NLAlib.eighLevelParams`); the draws by `NLAlib.Computation.exec_forRange_draw` (cell
$i$ of `Su` is the tape at $nd + i$, cell $w$ of `Sg` at $4n^2 d + w$); then the loop over the slots
by `NLAlib.Computation.forall_of_exec_loop_eq_some` (pilot) with the invariant "the slots below $lo$
are done": at slot $lo$ the binder reads the stored size (`hlev`, `NLAlib.ReadsIdx`, the clamp to
$n - lo$ is harmless by `NLAlib.eighLoc_bounds`), a slot that starts no node reads $0$ and skips
(`NLAlib.eighWhen`), and a node of size $k$ runs a leaf (`NLAlib.holds_of_exec_eighLeafBlock`, for
$k \le 1$ or $R \le \mathrm{fl}(\varepsilon R_0)$, one comparison) or
`NLAlib.holds_of_exec_eighNodeBlock`, whose window, tolerance and depth counter are the depth's
(`NLAlib.eighLoc_params`); its writes stay in its own range of depths $d$ and $d + 1$
(`NLAlib.eighLoc_disjoint`), so the other nodes' cells are kept, and the children of the nodes of
depth $d$ are the nodes of depth $d + 1$ (`NLAlib.eighLoc_append_singleton`); the sizes of the
children read back by `NLAlib.Computation.IsExactIntLit.toNat_eq_of_lit_eq_some` (scaffold,
$k \le n$), and every other slot of depth $d + 1$ keeps its $0$. L, about 200 lines (split the
per-slot step into a private lemma). -/
theorem holds_of_exec_eighDownLevel {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {dec : P → K → ℝ} (p : P) (hflag : I.sem.DecidesFlags p)
    (n ℓ₀ F d D : ℕ) (hd : d < D) (hlit : IsExactIntLit dec I.sem (n + 4))
    (htn : IsExactToNat dec I.sem) (H : EighArenas) {par Su Sg c : ℕ} {st st' : St P K C}
    {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hH : H.Shaped st.store p n D) (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup)
    (hlev : H.LevelHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d)
    (hpos : st.pos .uniform = n * d ∧ st.pos .gaussian = 4 * (n * n) * d)
    (hpar : st.store.read p par 0 = some R₀ ∧ st.store.read p par 2 = some β)
    (hc : st.store.read p c 0 = I.sem.lit p 1 ∧ st.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
      st.store.read p c 2 = some ((eighTapeMachine I p mmR qrR).div
        (eighTapeMachine I p mmR qrR).one ((eighTapeMachine I p mmR qrR).ofNat 2)) ∧
      st.store.read p c 3 = some ((eighTapeMachine I p mmR qrR).neg
        (eighTapeMachine I p mmR qrR).one))
    (h : exec I (eighDownLevel p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) par H.Lv Su Sg
      H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩).run st = some st') :
    H.LevelHolds I.sem st'.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
        ⟨n, A, R₀, ε, ℓ₀⟩ (d + 1) ∧
      H.RecordHolds I.sem st'.store p (eighTapeMachine I p mmR qrR) n F R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ d ∧
      (∀ q b i, b ≠ Su → b ≠ Sg → ¬ H.LevelCell n d b i → ¬ H.LevelCell n (d + 1) b i →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos .uniform = st.pos .uniform + n ∧
      st'.pos .gaussian = st.pos .gaussian + 4 * (n * n) := by
  sorry

/-- **One level of the downward pass succeeds** under the standard model at $u$ with every value in
range, $u(p) < 1$, exact integer literals up to $n + 4$ and the exact floor conversion, if the
kernels are routines on pairs, $\ell_0 \ge 1$, $\varepsilon$ and $R_0$ decode to nonnegative values
and the arenas hold the nodes of depth $d$ (hypotheses as `NLAlib.holds_of_exec_eighDownLevel`). No
printed source.
Proof: the parameters (divisions by $\mathrm{fl}(\ell) \ne 0$, `lit_err`, $u(p) < 1$), the draws,
and the loop over the slots by `NLAlib.Computation.exists_exec_loop_eq_some_of_forall` with the
invariant of `NLAlib.holds_of_exec_eighDownLevel`: each binder succeeds (`htn`), each leaf
(`lit_ok`, copies of initialised cells), and each node by `NLAlib.exists_exec_eighNodeBlock`, whose
window is positive: the comparison $R \le \mathrm{fl}(\varepsilon R_0)$ failed and
$\mathrm{fl}(\varepsilon R_0)$ decodes to $\bar\varepsilon\bar R_0(1 + \delta) \ge 0$ (`bin_err`,
`cmp_le`). L, about 120 lines. -/
theorem exists_exec_eighDownLevel {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (hu : u p < 1)
    (n ℓ₀ F d D : ℕ) (hd : d < D) (hℓ : 1 ≤ ℓ₀) (hlit : IsExactIntLit dec I.sem (n + 4))
    (htn : IsExactToNat dec I.sem) (H : EighArenas) {par Su Sg c : ℕ} {st : St P K C}
    {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K} (hε : 0 ≤ dec p ε) (hR₀ : 0 ≤ dec p R₀)
    (hH : H.Shaped st.store p n D) (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup)
    (hlev : H.LevelHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d)
    (hpar : st.store.read p par 0 = some R₀ ∧ st.store.read p par 2 = some β)
    (hSu : ∃ len, st.store.shape[Su]? = some (p, len) ∧ n ≤ len)
    (hSg : ∃ len, st.store.shape[Sg]? = some (p, len) ∧ 4 * (n * n) ≤ len)
    (hc : st.store.read p c 0 = I.sem.lit p 1 ∧ st.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
      (∃ v, st.store.read p c 2 = some v) ∧ ∃ v, st.store.read p c 3 = some v) :
    ∃ st', exec I (eighDownLevel p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) par H.Lv Su
      Sg H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩).run st = some st' := by
  sorry

/-- **The spent level writes the junk outputs**: under exact integer literals up to $n + 4$ and the
exact floor conversion, a successful run of `NLAlib.eighBottomLevel` at depth $D$ from a state whose
arenas hold the nodes of depth $D$ ends with the outputs of depth $D$ holding `NLAlib.eighAux` at
budget $0$ (`NLAlib.EighArenas.OutHolds` at $D$: the machine's identity and zeros); every cell
outside the output and eigenvalue arenas at depth $D$ is unchanged, the store shape and the tape
positions too. No printed source.
Proof: the loop over the slots as in `NLAlib.holds_of_exec_eighDownLevel`, each node by the pilot's
`NLAlib.Computation.holds_of_exec_zidentity` (after `NLAlib.Computation.exec_zidentity_congr`) and a
loop of literals; `NLAlib.eighAux` at budget $0$ is the identity and zeros by definition
(`Nat.sub_self`). M, about 60 lines. -/
theorem holds_of_exec_eighBottomLevel {dec : P → K → ℝ} (p : P) (n ℓ₀ F D : ℕ)
    (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem) (H : EighArenas)
    {st st' : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hH : H.Shaped st.store p n D)
    (hlev : H.LevelHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ D)
    (h : exec I (eighBottomLevel (ι := ι) p (.const n) (.const D) H.Ua H.Ea H.Sz).run st =
      some st') :
    H.OutHolds st'.store p (eighTapeMachine I p mmR qrR) n F D R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ D ∧
      (∀ q b i, ¬ ((b = H.Ua ∨ b = H.Ea) ∧ H.LevelCell n D b i) →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  sorry

/-- **The spent level succeeds** under the standard model with every value in range and the exact
floor conversion, when the arenas are allocated and their size cells of depth $D$ are initialised.
No printed source.
Proof: `NLAlib.Computation.exists_exec_loop_eq_some_of_forall`; each binder succeeds (`htn`), each
literal (`lit_ok`) and each write (the blocks fit, `NLAlib.eighLoc_bounds`, `hH`). S, about 30
lines. -/
theorem exists_exec_eighBottomLevel {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (htn : IsExactToNat dec I.sem) (p : P)
    (n ℓ₀ F D : ℕ) (H : EighArenas) {st : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)}
    {R₀ ε β : K} (hH : H.Shaped st.store p n D)
    (hlev : H.LevelHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ D) :
    ∃ st', exec I (eighBottomLevel (ι := ι) p (.const n) (.const D) H.Ua H.Ea H.Sz).run st =
      some st' := by
  sorry

/-- **One level of the upward pass**: if kernel `mm` of `I` is the routine `mmR` on interleaved
pairs, under exact integer literals up to $n + 4$ and the exact floor conversion, a successful run
of `NLAlib.eighUpLevel` at depth $d < D$ from a state whose arenas hold the nodes of depth $d$
(their sizes), the records of depth $d$ and the outputs of depth $d + 1$, with the window of depth
$d$ in its cell and the stored $\mathrm{fl}(2)$ in `two`, ends with the outputs of depth $d$
(`NLAlib.EighArenas.OutHolds` at $d$, budget $D - d$); every cell outside the output and eigenvalue
arenas at depth $d$ is unchanged, the store shape and the tape positions too. No printed source.
Proof: the loop over the slots with the invariant "the slots below $lo$ are done"; at a node $y$ the
binder reads its kind (`NLAlib.EighArenas.RecordHolds`), and `NLAlib.eighAux` at budget
$D - d = (D - d - 1) + 1$ unfolds at the node (`Nat.sub_add_cancel`): a leaf's output is already
stored; a one-child node copies its child's $\mathbf{U}$ (the pilot's
`NLAlib.Computation.holds_of_exec_zcopy` after `NLAlib.Computation.exec_zcopy_congr`) and adds
$\pm\sigma$; a split reads $k_+$ and runs the two kernel calls into the column blocks of the node's
output (`NLAlib.Computation.IsMatMulKernel.holds_of_kcallStore_eq_some`, pilot), which is
`Matrix.fromCols` reindexed by `finSumFinEquiv` packed column-major (the first $k_+$ columns are the
first $2kk_+$ words), and the eigenvalues by the two loops; the children's outputs are those of
`NLAlib.EighArenas.OutHolds` at $d + 1$ through `NLAlib.eighSlotTree_append_of_eighLoc` and
`NLAlib.eighLoc_append_singleton`. L, about 180 lines (split the split case into a private lemma).
-/
theorem holds_of_exec_eighUpLevel {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    {dec : P → K → ℝ} (p : P) (n ℓ₀ F d D : ℕ) (hd : d < D)
    (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem) (H : EighArenas)
    {two : Cell ℕ ℕ} {st st' : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hH : H.Shaped st.store p n D) (htwo : two.buf ∉ H.handles)
    (htwov : st.store.read p two.buf two.idx.eval = I.sem.lit p ((2 : ℕ) : ℚ))
    (hlev : H.LevelHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d)
    (hrec : H.RecordHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d)
    (hout : H.OutHolds st.store p (eighTapeMachine I p mmR qrR) n F D R₀ β ⟨n, A, R₀, ε, ℓ₀⟩
      (d + 1))
    (h : exec I (eighUpLevel p mm (.const n) (.const d) H.Lv H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp
      two).run st = some st') :
    H.OutHolds st'.store p (eighTapeMachine I p mmR qrR) n F D R₀ β ⟨n, A, R₀, ε, ℓ₀⟩ d ∧
      (∀ q b i, ¬ ((b = H.Ua ∨ b = H.Ea) ∧ H.LevelCell n d b i) →
        st'.store.read q b i = st.store.read q b i) ∧
      st'.store.shape = st.store.shape ∧ st'.pos = st.pos := by
  sorry

/-- **One level of the upward pass succeeds** under the standard model with every value in range,
the exact floor conversion and an exact literal $2$, if kernel `mm` is a routine on pairs, with the
hypotheses of `NLAlib.holds_of_exec_eighUpLevel`. No printed source.
Proof: as `NLAlib.holds_of_exec_eighUpLevel`, each operation by its success clause: the binders
(`htn`), the kernel calls (`NLAlib.Computation.IsMatMulKernel.kcallStore_eq`, pilot; the output
block of depth $d$ does not overlap the inputs of depth $d + 1$ and the bases), the copies, sums and
differences (`bin_ok`). M, about 80 lines. -/
theorem exists_exec_eighUpLevel {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    {u : P → ℝ} {dec : P → K → ℝ} (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P)
    (n ℓ₀ F d D : ℕ) (hd : d < D) (hlit : IsExactIntLit dec I.sem (n + 4))
    (htn : IsExactToNat dec I.sem) (H : EighArenas) {two : Cell ℕ ℕ} {st : St P K C}
    {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hH : H.Shaped st.store p n D) (htwo : two.buf ∉ H.handles)
    (htwov : st.store.read p two.buf two.idx.eval = I.sem.lit p ((2 : ℕ) : ℚ))
    (hlev : H.LevelHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d)
    (hrec : H.RecordHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d)
    (hout : H.OutHolds st.store p (eighTapeMachine I p mmR qrR) n F D R₀ β ⟨n, A, R₀, ε, ℓ₀⟩
      (d + 1)) :
    ∃ st', exec I (eighUpLevel p mm (.const n) (.const d) H.Lv H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp
      two).run st = some st' := by
  sorry

/-! ### The program -/

/-- **The refinement of the spectral bisection program, partial equality**: let the kernels `mm`,
`qr` of `I` be the routines `mmR`, `qrR` on interleaved pairs, and the semantics decide flags at
`p`, with exact integer literals up to $n + 4$ and the exact floor conversion. A successful run of
`NLAlib.eighProg` at size $n$, depth counter $\ell_0$ and step limit $F$, from a state with the tape
positions at $0$, whose block at offset $0$ of `A` holds the stored $\mathbf{A}$ and whose cells
$0$, $1$, $2$ of `par` hold $R_0$, $\varepsilon$, $\beta$, ends with the block at offset $0$ of `U`
and the cells $0, \ldots, n - 1$ of `dv` holding exactly
$$\mathsf{eigh}(\mathbf{A}, R_0, \varepsilon, \beta)$$
computed by `NLAlib.eigh` with step limit $F$ and depth counter $\ell_0$ on the machine of the
interpretation (`NLAlib.eighTapeMachine`), with the tree of samples at the slots
(`NLAlib.eighSlotTree`). [Shah2024, Algorithm 3], for the program. No printed source.
Proof: the scope allocates the constants and the arenas at handles `st.store.size + j`
(`NLAlib.Computation.exec_alloc`), distinct from `A`, `par`, `U`, `dv` (`NLAlib.EighArenas.Shaped`);
the initialisation gives `NLAlib.EighArenas.LevelHolds` at depth $0$ (the root at slot $0$, its size
the literal $n$ read back by `NLAlib.Computation.IsExactIntLit.toNat_eq_of_lit_eq_some`, every
other size $0$, $\mathbf{A}$ by the pilot's `NLAlib.Computation.holds_of_exec_zcopy`); the
downward loop by `NLAlib.Computation.forall_of_exec_loop_eq_some` (pilot) with
`NLAlib.holds_of_exec_eighDownLevel` (the records of depths below $d$ are kept by its frame); then
`NLAlib.holds_of_exec_eighBottomLevel`, and the upward loop with `NLAlib.holds_of_exec_eighUpLevel`
at $d = \ell_0 - d'$; at depth $0$ `NLAlib.EighArenas.OutHolds` is `NLAlib.eighAux` at budget
$\ell_0 + 1$ on the root, which is `NLAlib.eigh`, with the samples
`NLAlib.eighSlotTree M n F R₀ β 0 0 root`; the final copies and the pops. L, about 160 lines. -/
theorem holds_of_exec_eighProg {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {dec : P → K → ℝ} (p : P) (hflag : I.sem.DecidesFlags p)
    (n ℓ₀ F : ℕ) (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem)
    {A par U dv : ℕ} {st st' : St P K C} {A₀ : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hbufs : [A, par, U, dv].Nodup) (hsize : ∀ j ∈ [A, par, U, dv], j < st.store.size)
    (hA : pairLayout.Holds st.store p A 0 A₀)
    (hpar : st.store.read p par 0 = some R₀ ∧ st.store.read p par 1 = some ε ∧
      st.store.read p par 2 = some β)
    (hpos : st.pos .uniform = 0 ∧ st.pos .gaussian = 0)
    (h : exec I (eighProg p mm qr (.const n) (.const ℓ₀) (.const F) A par U dv).run st =
      some st') :
    let M := eighTapeMachine I p mmR qrR
    let r := eigh M F ℓ₀ A₀ R₀ ε β (eighSlotTree M n F R₀ β 0 0 ⟨n, A₀, R₀, ε, ℓ₀⟩)
    pairLayout.Holds st'.store p U 0 r.1 ∧ ∀ i : Fin n, st'.store.read p dv i = some (r.2 i) := by
  sorry

/-- **The refinement of the spectral bisection program, success**: under the standard model at $u$
with every value in range, $u(p) < 1$, exact integer literals up to $n + 4$ and the exact floor
conversion, if the kernels `mm`, `qr` of `I` are routines on interleaved pairs, $\ell_0 \ge 1$,
$\varepsilon$ and $R_0$ decode to nonnegative values, and the buffers `U`, `dv` at tag `p` have
$2n^2$ and $n$ cells (hypotheses on the inputs as `NLAlib.holds_of_exec_eighProg`), then every run
of `NLAlib.eighProg` succeeds. No printed source.
Proof: the allocations succeed; the initialisation (`lit_ok`, copies of initialised cells, the
pilot's `NLAlib.Computation.exists_exec_zcopy`); the downward loop by
`NLAlib.Computation.exists_exec_loop_eq_some_of_forall` with `NLAlib.exists_exec_eighDownLevel` and
the invariant `NLAlib.holds_of_exec_eighDownLevel` gives; `NLAlib.exists_exec_eighBottomLevel`; the
upward loop with `NLAlib.exists_exec_eighUpLevel`; the final copies and the pops. L, about 100
lines. -/
theorem exists_exec_eighProg {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (hu : u p < 1) (n ℓ₀ F : ℕ)
    (hlit : IsExactIntLit dec I.sem (n + 4)) (htn : IsExactToNat dec I.sem)
    (hℓ : 1 ≤ ℓ₀) {A par U dv : ℕ} {st : St P K C} {A₀ : Matrix (Fin n) (Fin n) (K × K)}
    {R₀ ε β : K} (hε : 0 ≤ dec p ε) (hR₀ : 0 ≤ dec p R₀)
    (hbufs : [A, par, U, dv].Nodup) (hsize : ∀ j ∈ [A, par, U, dv], j < st.store.size)
    (hA : pairLayout.Holds st.store p A 0 A₀)
    (hpar : st.store.read p par 0 = some R₀ ∧ st.store.read p par 1 = some ε ∧
      st.store.read p par 2 = some β)
    (hU : ∃ len, st.store.shape[U]? = some (p, len) ∧ 2 * (n * n) ≤ len)
    (hdv : ∃ len, st.store.shape[dv]? = some (p, len) ∧ n ≤ len) :
    ∃ st', exec I (eighProg p mm qr (.const n) (.const ℓ₀) (.const F) A par U dv).run st =
      some st' := by
  sorry

omit [DecidableEq P] [AddMonoid C] [Inhabited K] in
/-- **The registered tree instantiates to the builder**: at the sizes $N$ and $(\ell_0, F)$ the tree
`NLAlib.eighProg.compiled` is `NLAlib.eighProg` on the declared buffers $0$ to $3$. No printed
source.
Proof: `rfl`, the instantiation equation of a compiled family (as the pilot's
`NLAlib.newtonSchulzSignProg.toStmt_compiled`). S, 1 line. -/
theorem eighProg.toStmt_compiled (p : P) (mm qr : ι) (N : ℕ) (n : Fin 2 → ℕ) :
    (eighProg.compiled p mm qr).toStmt N n =
      ProgFamily.inst (r := 2) (b := 4) (fun _ _ N n h =>
        (eighProg p mm qr N (n 0) (n 1) (h 0) (h 1) (h 2) (h 3)).run) N n := by
  sorry

/-- **The registered tree computes `NLAlib.eigh`**: under the hypotheses of
`NLAlib.holds_of_exec_eighProg`, a successful run of `NLAlib.eighProg.compiled` at the sizes $N$ and
$(\ell_0, F)$ from the initial state with the stored $\mathbf{A}$, the stored $R_0$, $\varepsilon$,
$\beta$, and $2N^2$ and $N$ empty cells as declared buffers ends with declared buffers $2$ and $3$
holding `NLAlib.eigh` on the machine of the interpretation with the tree of samples at the slots.
No printed source.
Proof: `NLAlib.Computation.Prog.exec_eq_exec_toStmt`, `NLAlib.eighProg.toStmt_compiled`, then
`NLAlib.holds_of_exec_eighProg` with the pilot's `NLAlib.Computation.EntryLayout.holds_inputState`
and the reads of declared buffer $1$ (`NLAlib.Computation.inputState`, tape positions $0$). S,
about 15 lines. -/
theorem eighProg.holds_of_exec_compiled {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {dec : P → K → ℝ} (p : P) (hflag : I.sem.DecidesFlags p)
    (N ℓ₀ F : ℕ) (hlit : IsExactIntLit dec I.sem (N + 4)) (htn : IsExactToNat dec I.sem)
    (A₀ : Matrix (Fin N) (Fin N) (K × K)) (R₀ ε β : K) {st' : St P K C}
    (h : (eighProg.compiled p mm qr).exec I N ![ℓ₀, F]
      (inputState p [(pairLayout.toArray A₀).map some, #[some R₀, some ε, some β],
        Array.replicate (2 * (N * N)) none, Array.replicate N none]) = some st') :
    let M := eighTapeMachine I p mmR qrR
    let r := eigh M F ℓ₀ A₀ R₀ ε β (eighSlotTree M N F R₀ β 0 0 ⟨N, A₀, R₀, ε, ℓ₀⟩)
    pairLayout.Holds st'.store p 2 0 r.1 ∧ ∀ i : Fin N, st'.store.read p 3 i = some (r.2 i) := by
  sorry

/-- **The registered tree succeeds** under the hypotheses of `NLAlib.exists_exec_eighProg`, from the
initial state of `NLAlib.eighProg.holds_of_exec_compiled`. No printed source.
Proof: as `NLAlib.eighProg.holds_of_exec_compiled`, with `NLAlib.exists_exec_eighProg`; declared
buffers $2$ and $3$ have $2N^2$ and $N$ cells at tag `p` (`NLAlib.Computation.inputState`,
`Array.size_replicate`). S, about 15 lines. -/
theorem eighProg.exists_exec_compiled {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (hu : u p < 1) (N ℓ₀ F : ℕ)
    (hℓ : 1 ≤ ℓ₀) (hlit : IsExactIntLit dec I.sem (N + 4)) (htn : IsExactToNat dec I.sem)
    (A₀ : Matrix (Fin N) (Fin N) (K × K)) (R₀ ε β : K) (hε : 0 ≤ dec p ε) (hR₀ : 0 ≤ dec p R₀) :
    ∃ st' : St P K C, (eighProg.compiled p mm qr).exec I N ![ℓ₀, F]
      (inputState p [(pairLayout.toArray A₀).map some, #[some R₀, some ε, some β],
        Array.replicate (2 * (N * N)) none, Array.replicate N none]) = some st' := by
  sorry

/-- **The counts and the memory of the registered tree**: under the standard charge (one per
operation), every successful run of `NLAlib.eighProg.compiled` at the sizes $N$ and $(\ell_0, F)$
adds at most `NLAlib.eighCount p mm qr N ℓ₀ F` to the counts and raises the peak memory at tag `p`
by at most $64(N + 1)^2(\ell_0 + 3)$ cells above the current memory (by nothing at any other tag):
the arenas of $D + 1 = \ell_0 + 2$ levels and the scratch of one node, $O(N^2 \ell_0)$. No printed
source.
Proof: `NLAlib.Computation.Prog.bounds_staticCost_of_exec_eq_some`; the static cost of the tree is
computed by `NLAlib.Computation.FStmt.staticCost` (`simp` with
`NLAlib.Computation.StaticCost.seq`, `NLAlib.Computation.StaticCost.sequence`,
`NLAlib.Computation.StaticCost.branch`, `NLAlib.Computation.StaticCost.supRange`,
`NLAlib.Computation.StaticCost.alloc`): each slot visit is bounded by the supremum over the node
sizes $k \le N$ and splits $k_+ \le k$, which is at most their sum (`Finset.sum_le_sum`,
`le_sup_iff`-style bounds of `NLAlib.Computation.StaticCost.supRange` by a sum of nonnegative
terms); the scalar kinds are at most $1024(F + 2)(\ell_0 + 2)(N + 1)^3$ each; compare kind by kind
(`Finsupp.le_def`). M, about 120 lines. -/
theorem eighProg.cnt_le_of_exec_compiled {mm qr : ι} {I : Interp P ι K (OpCount P ι)}
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (p : P) (N ℓ₀ F : ℕ)
    {st st' : St P K (OpCount P ι)}
    (h : (eighProg.compiled p mm qr).exec I N ![ℓ₀, F] st = some st') :
    st'.cnt ≤ st.cnt + eighCount p mm qr N ℓ₀ F ∧
      ∀ q, st'.peak q ≤ max (st.peak q)
        (st.cur q + if q = p then 64 * (N + 1) ^ 2 * (ℓ₀ + 3) else 0) := by
  sorry

/-- **The kernel cost of the registered tree, weighted** ([Shah2024, Section 4], the operation count
of Theorem 4.2): for a cost $T$ of a kernel call by its largest dimension that is monotone and
superadditive ($T(a) + T(b) \le T(a + b)$, as a convex $T$ with $T(0) = 0$ is), under the standard
charge, every successful run of `NLAlib.eighProg.compiled` at the sizes $N$ and $(\ell_0, F)$ adds
at most $(\ell_0 + 1)(2F + 12)\,T(N)$ to the weighted kernel count: per level, the nodes have sizes
summing to at most $N$, each with at most $2F + 12$ kernel calls of largest dimension at most its
size. The static bound `NLAlib.eighCount` charges every size at every slot, a factor of about $N^2$
more. No printed source.
Proof: an invariant of the run (not of `NLAlib.Computation.FStmt.staticCost`): by the shapes of
`NLAlib.holds_of_exec_eighDownLevel` and `NLAlib.holds_of_exec_eighUpLevel`, the calls of a level
are those of its nodes (`NLAlib.Computation.exec_kcall`, the kind records its dimensions, and every
dimension list of a node of size $k$ has entries at most $k$); the sizes at one depth are the
disjoint ranges of `NLAlib.eighLoc_disjoint` inside $[0, N)$, so $\sum_y T(k_y) \le T(N)$ by
superadditivity and monotonicity (`Finset.sum_le_sum`, induction on the number of nodes); sum over
the $\ell_0 + 1$ levels (`Finsupp.weight_apply`, `map_add`). L, about 150 lines. -/
theorem eighProg.weight_le_of_exec_compiled {mm qr : ι} {I : Interp P ι K (OpCount P ι)}
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (p : P) (N ℓ₀ F : ℕ) (T : ℕ → ℕ)
    (hT : Monotone T) (hTsup : ∀ a b, T a + T b ≤ T (a + b)) {st st' : St P K (OpCount P ι)}
    (h : (eighProg.compiled p mm qr).exec I N ![ℓ₀, F] st = some st') :
    Finsupp.weight (fun κ : OpKind P ι => match κ with
        | .kcall _ _ ds => T (ds.foldr max 0)
        | _ => 0) st'.cnt ≤
      Finsupp.weight (fun κ : OpKind P ι => match κ with
        | .kcall _ _ ds => T (ds.foldr max 0)
        | _ => 0) st.cnt + (ℓ₀ + 1) * (2 * F + 12) * T N := by
  sorry

end NLAlib
