/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.InterpMachine
public import NLAlib.Matrix.Computation.SpectralBisection

/-!
# Randomized spectral bisection as a program: samples, slots and the level encoding

The vocabulary of the refinement of the program `NLAlib.eighProg` to the shallow `NLAlib.eigh`
(design note `docs/design/Computation-EighProgram.md`).

**The machine of an interpretation.** `NLAlib.eighTapeMachine I p mmR qrR` is the floating-point
machine of the semantics of `I` at tag `p` (`NLAlib.Computation.ScalarSem.toFloatMachine`) whose
conversion to a natural number is the semantics' (`none` read as $0$), whose black boxes are the
kernel routines, and whose samplers read the stored tape of `I` at a position: the uniform seed
$i$ gives the shift $\mathrm{fl}(s\,x_i)$ (`NLAlib.Computation.ScalarSem.tapeUnif`) and the
Gaussian sample $z$ the stored pair from the words $2z$, $2z + 1$
(`NLAlib.Computation.ScalarSem.tapeNormal`). Ideal samples are tape positions (`Su = Sg = ℕ`).

**Slots and samples.** The program stores the node at depth $d$ of the range $[lo, lo + k)$ at
slot $lo$ of level $d$ and reads its samples at fixed positions (`NLAlib.eighTapeSample`): the
seed at $nd + lo$, and entry $(i, j)$ of the test matrix of side $s$ at the complex sample
$2n^2 d + n(2(lo + j) + s) + i$. `NLAlib.eighLoc` follows a path of the shallow recursion and
returns the slot and the node, and `NLAlib.eighSlotTree` is the tree of samples of the nodes at
their slots, the tree that `NLAlib.eigh` receives in the refinement.

**The level encoding.** `NLAlib.EighArenas` names the handles of the program's level arenas, and
`NLAlib.EighArenas.LevelHolds`, `NLAlib.EighArenas.RecordHolds`, `NLAlib.EighArenas.OutHolds`
state that the arenas of one level hold the nodes of that depth, the outcome of their steps, and
their outputs.

**Ideal samples.** `NLAlib.eighIdealTree` is the tree of ideal samples of law
`NLAlib.eighSampleLaw` that a run on the ideal tape $\xi$ reads: the static positions of a node
that exists at a depth below $D$, entries inside its $k \times k$ block, and positions beyond the
program's draws, indexed by the path, everywhere else.

## Main definitions

* `NLAlib.Computation.ScalarSem.tapeUnif`, `NLAlib.Computation.ScalarSem.uniformUnif`: the uniform
  shift of a program.
* `NLAlib.eighTapeMachine`: the machine of an interpretation.
* `NLAlib.eighTapeSample`, `NLAlib.eighLoc`, `NLAlib.eighSlotTree`, `NLAlib.eighLevelParams`.
* `NLAlib.EighArenas`, `NLAlib.EighArenas.LevelHolds`, `NLAlib.EighArenas.RecordHolds`,
  `NLAlib.EighArenas.OutHolds`.
* `NLAlib.eighIdealSample`, `NLAlib.eighIdealTree`.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P K : Type} [Inhabited K]

/-- **The uniform shift of a tape** of stored uniform draws $x$: at scale $s$ and seed position
$i$, the rounded product $\mathrm{fl}(s\,x_i)$, as the program computes the shift of a node. -/
def ScalarSem.tapeUnif (sem : ScalarSem P K) (p : P) (x : ℕ → K) : K → ℕ → K := fun s i =>
  (sem.bin p .mul s (x i)).getD default

/-- **The uniform shift of a tape rounding** $\rho$ on an ideal seed $v$: the rounded product
$\mathrm{fl}(s\,\rho(v))$. With $v$ the ideal draw $\xi_i$ it is
`NLAlib.Computation.ScalarSem.tapeUnif` on the stored tape $\rho \circ \xi$. -/
def ScalarSem.uniformUnif (sem : ScalarSem P K) (p : P) (ρ : ℝ → K) : K → ℝ → K := fun s v =>
  (sem.bin p .mul s (ρ v)).getD default

end NLAlib.Computation

namespace NLAlib

open Computation

section Machine

variable {P ι K C : Type} [Inhabited K]

/-- **The machine of an interpretation** at tag `p`, with the kernel routines `mmR`, `qrR`: the
machine of its semantics (`NLAlib.Computation.ScalarSem.toFloatMachine`) whose conversion to a
natural number is the semantics' conversion (`none` read as $0$) and whose samplers read the
stored tape at a position (`NLAlib.Computation.ScalarSem.tapeUnif`,
`NLAlib.Computation.ScalarSem.tapeNormal`). -/
def eighTapeMachine (I : Interp P ι K C) (p : P) (mmR : MatMulMap (K × K)) (qrR : QRMap (K × K)) :
    FloatMachine K ℕ ℕ :=
  I.sem.toFloatMachine p (fun x => (I.sem.toNat p x).getD 0) mmR qrR
    (I.sem.tapeUnif p (I.tape .uniform)) (I.sem.tapeNormal p (I.tape .gaussian))

end Machine

/-! ### Slots and samples -/

/-- **The sample positions of the node at slot $lo$ of depth $d$** (root size $N$): the seed at
uniform position $Nd + lo$, and entry $(i, j)$ of the test matrix of side $b$ at the complex
sample $2N^2 d + N(2(lo + j) + s) + i$, $s = 0$ for the positive side and $1$ for the negative
(its real draws at the Gaussian positions twice that and the next). -/
def eighTapeSample (N d lo : ℕ) : EighSample ℕ ℕ N :=
  (N * d + lo, fun b => Matrix.of fun i j =>
    2 * (N * N) * d + N * (2 * (lo + j) + if b then 0 else 1) + i)

variable {F Su Sg : Type*} [Inhabited Sg]

/-- **The slot and node at a path** of the shallow recursion from the node $x$ at slot $lo$ of
depth $d$, each node with the samples of its slot (`NLAlib.eighTapeSample`): $(lo, x)$ at the
empty path; along $b :: a$ none at a leaf and on the absent side of a one-child node, the same slot
for a one-child node, and the slots $lo$ (positive side) and $lo + k_+$ (negative side) of a
split, with the children of `NLAlib.eighStep`, the next window and tolerance
(`NLAlib.eighNextParams`) and the next depth counter. -/
def eighLoc (M : FloatMachine F ℕ ℕ) (N signFuel : ℕ) (R₀ β : F) :
    ℕ → ℕ → EighNode F → List Bool → Option (ℕ × EighNode F)
  | _, lo, x, [] => some (lo, x)
  | d, lo, x, b :: a =>
    let q := eighNextParams M x.R x.ε x.ℓ
    match eighStep M N signFuel R₀ β x.A x.R x.ε x.ℓ (eighTapeSample N d lo) with
    | .leaf _ _ => none
    | .shift b' A' _ =>
      if b = b' then eighLoc M N signFuel R₀ β (d + 1) lo ⟨x.k, A', q.1, q.2, x.ℓ + 1⟩ a else none
    | .split kp _ _ _ Ap Am _ =>
      if b then eighLoc M N signFuel R₀ β (d + 1) lo ⟨kp, Ap, q.1, q.2, x.ℓ + 1⟩ a
      else eighLoc M N signFuel R₀ β (d + 1) (lo + kp) ⟨x.k - kp, Am, q.1, q.2, x.ℓ + 1⟩ a

/-- **The tree of samples at the slots** of the shallow recursion from the node $x$ at slot $lo$ of
depth $d$: at a path, the sample positions (`NLAlib.eighTapeSample`) of the slot that
`NLAlib.eighLoc` reaches, and below a leaf or on the absent side of a one-child node (unused by
`NLAlib.eigh`) those of the slot of the parent at the next depth. -/
def eighSlotTree (M : FloatMachine F ℕ ℕ) (N signFuel : ℕ) (R₀ β : F) :
    ℕ → ℕ → EighNode F → List Bool → EighSample ℕ ℕ N
  | d, lo, _, [] => eighTapeSample N d lo
  | d, lo, x, b :: a =>
    let q := eighNextParams M x.R x.ε x.ℓ
    match eighStep M N signFuel R₀ β x.A x.R x.ε x.ℓ (eighTapeSample N d lo) with
    | .leaf _ _ => eighTapeSample N (d + 1) lo
    | .shift _ A' _ => eighSlotTree M N signFuel R₀ β (d + 1) lo ⟨x.k, A', q.1, q.2, x.ℓ + 1⟩ a
    | .split kp _ _ _ Ap Am _ =>
      if b then eighSlotTree M N signFuel R₀ β (d + 1) lo ⟨kp, Ap, q.1, q.2, x.ℓ + 1⟩ a
      else eighSlotTree M N signFuel R₀ β (d + 1) (lo + kp) ⟨x.k - kp, Am, q.1, q.2, x.ℓ + 1⟩ a

/-- **The window and tolerance of depth $d$**: $(R_0, \varepsilon)$ at depth $0$, and the next
window and tolerance (`NLAlib.eighNextParams`) with depth counter $\ell_0 + d$ below; every node at
depth $d$ has them. -/
def eighLevelParams (M : FloatMachine F Su Sg) (R₀ ε : F) (ℓ₀ : ℕ) : ℕ → F × F
  | 0 => (R₀, ε)
  | d + 1 =>
    eighNextParams M (eighLevelParams M R₀ ε ℓ₀ d).1 (eighLevelParams M R₀ ε ℓ₀ d).2 (ℓ₀ + d)

/-! ### The level encoding -/

/-- **The handles of the level arenas** of `NLAlib.eighProg`: node matrices, outputs, bases,
eigenvalues, sizes, kinds, splits $k_+$, and windows and tolerances. -/
structure EighArenas where
  /-- The node matrices, a complex $n \times n$ block per level. -/
  Ma : ℕ
  /-- The outputs $\mathbf{U}$, a complex $n \times n$ block per level. -/
  Ua : ℕ
  /-- The bases $[\mathbf{Q}_+\ \mathbf{Q}_-]$, a complex $n \times n$ block per level. -/
  Qa : ℕ
  /-- The eigenvalues, $n$ cells per level. -/
  Ea : ℕ
  /-- The sizes, $n$ cells per level. -/
  Sz : ℕ
  /-- The kinds, $n$ cells per level. -/
  Kd : ℕ
  /-- The splits $k_+$, $n$ cells per level. -/
  Kp : ℕ
  /-- The window and tolerance of each level, two cells per level. -/
  Lv : ℕ

/-- The eight handles of the arenas. -/
def EighArenas.handles (H : EighArenas) : List ℕ := [H.Ma, H.Ua, H.Qa, H.Ea, H.Sz, H.Kd, H.Kp, H.Lv]

/-- **The cells of depth $d$ of the arenas**: the complex block $[2n^2 d, 2n^2(d + 1))$ of the
node, output and basis arenas, the cells $[nd, n(d + 1))$ of the eigenvalue, size, kind and split
arenas, and the window and tolerance cells $2d$, $2d + 1$. -/
def EighArenas.LevelCell (H : EighArenas) (n d b i : ℕ) : Prop :=
  ((b = H.Ma ∨ b = H.Ua ∨ b = H.Qa) ∧ 2 * (n * n) * d ≤ i ∧ i < 2 * (n * n) * (d + 1)) ∨
    ((b = H.Ea ∨ b = H.Sz ∨ b = H.Kd ∨ b = H.Kp) ∧ n * d ≤ i ∧ i < n * (d + 1)) ∨
    (b = H.Lv ∧ (i = 2 * d ∨ i = 2 * d + 1))

variable {P K : Type} [DecidableEq P] [Inhabited K]

/-- **The arenas are allocated** at tag `p` for size $n$ and depth budget $D$ in the store `s`:
the eight handles are distinct, and the buffers have the lengths `NLAlib.eighProg` allocates
($2n^2(D + 1)$ words for the node matrices and outputs, $2n^2 D$ for the bases, $n(D + 1)$ for the
eigenvalues, $n(D + 1) + 1$ for the sizes, $nD$ for the kinds and splits, $2(D + 1)$ for the
windows and tolerances). -/
def EighArenas.Shaped (H : EighArenas) (s : Store P K) (p : P) (n D : ℕ) : Prop :=
  H.handles.Nodup ∧ s.shape[H.Ma]? = some (p, 2 * (n * n) * (D + 1)) ∧
    s.shape[H.Ua]? = some (p, 2 * (n * n) * (D + 1)) ∧ s.shape[H.Qa]? = some (p, 2 * (n * n) * D) ∧
    s.shape[H.Ea]? = some (p, n * (D + 1)) ∧ s.shape[H.Sz]? = some (p, n * (D + 1) + 1) ∧
    s.shape[H.Kd]? = some (p, n * D) ∧ s.shape[H.Kp]? = some (p, n * D) ∧
    s.shape[H.Lv]? = some (p, 2 * (D + 1))

/-- The cell `i` of buffer `b`, read at tag `p` and converted to an index by the semantics, is
$k$: what an index binder on it reads before clamping. -/
def ReadsIdx (sem : ScalarSem P K) (s : Store P K) (p : P) (b i k : ℕ) : Prop :=
  (s.read p b i).bind (sem.toNat p) = some k

/-- **The arenas of depth $d$ hold its nodes**: for the machine `M` with root `root` (size $n$,
depth counter $\ell_0$): every node $y$ that `NLAlib.eighLoc` reaches at a path of length $d$, at
slot $lo$, has its size in the size cell $nd + lo$ (read back as an index) and its matrix packed
at offset $2n^2 d + 2n\,lo$ of the node arena; every other slot below $n$ reads $0$; and the window
and tolerance cells of depth $d$ hold `NLAlib.eighLevelParams` at $d$. -/
def EighArenas.LevelHolds (H : EighArenas) (sem : ScalarSem P K) (s : Store P K) (p : P)
    (M : FloatMachine K ℕ ℕ) (n signFuel ℓ₀ : ℕ) (R₀ β : K) (root : EighNode K) (d : ℕ) :
    Prop :=
  (∀ (a : List Bool) (lo : ℕ) (y : EighNode K), a.length = d →
    eighLoc M n signFuel R₀ β 0 0 root a = some (lo, y) →
      ReadsIdx sem s p H.Sz (n * d + lo) y.k ∧
        pairLayout.Holds s p H.Ma (2 * (n * n) * d + 2 * n * lo) y.A) ∧
  (∀ lo < n, (∀ (a : List Bool) (y : EighNode K), a.length = d →
    eighLoc M n signFuel R₀ β 0 0 root a ≠ some (lo, y)) → ReadsIdx sem s p H.Sz (n * d + lo) 0) ∧
  s.read p H.Lv (2 * d) = some (eighLevelParams M R₀ root.ε ℓ₀ d).1 ∧
  s.read p H.Lv (2 * d + 1) = some (eighLevelParams M R₀ root.ε ℓ₀ d).2

/-- **The records of depth $d$ hold the outcome of its node steps**: for every node $y$ at a path of
length $d$ and slot $lo$ with $y.k \ge 1$: a leaf (`NLAlib.eighStep` returns `leaf U e`) has kind
$1$, its $\mathbf{U}$ at offset $2n^2 d + 2n\,lo$ of the output arena and its eigenvalues at the
cells $nd + lo + i$; a one-child node has kind $2$ (positive side) or $3$; a split into $k_+$ has
kind $4$, $k_+$ in its split cell, and $\mathbf{Q}_+$, then $\mathbf{Q}_-$, packed at offset
$2n^2 d + 2n\,lo$ of the basis arena. -/
def EighArenas.RecordHolds (H : EighArenas) (sem : ScalarSem P K) (s : Store P K) (p : P)
    (M : FloatMachine K ℕ ℕ) (n signFuel : ℕ) (R₀ β : K) (root : EighNode K) (d : ℕ) : Prop :=
  ∀ (a : List Bool) (lo : ℕ) (y : EighNode K), a.length = d →
    eighLoc M n signFuel R₀ β 0 0 root a = some (lo, y) → 1 ≤ y.k →
      match eighStep M n signFuel R₀ β y.A y.R y.ε y.ℓ (eighTapeSample n d lo) with
      | .leaf U e => ReadsIdx sem s p H.Kd (n * d + lo) 1 ∧
          pairLayout.Holds s p H.Ua (2 * (n * n) * d + 2 * n * lo) U ∧
          ∀ i : Fin y.k, s.read p H.Ea (n * d + lo + i) = some (e i)
      | .shift b _ _ => ReadsIdx sem s p H.Kd (n * d + lo) (if b then 2 else 3)
      | .split kp _ Qp Qm _ _ _ => ReadsIdx sem s p H.Kd (n * d + lo) 4 ∧
          ReadsIdx sem s p H.Kp (n * d + lo) kp ∧
          pairLayout.Holds s p H.Qa (2 * (n * n) * d + 2 * n * lo) Qp ∧
          pairLayout.Holds s p H.Qa (2 * (n * n) * d + 2 * n * lo + 2 * (y.k * kp)) Qm

/-- **The outputs of depth $d$ hold**: every node $y$ at a path of length $d$ and slot $lo$ has the
output of `NLAlib.eighAux` with the remaining budget $D - d$, on the samples of its slot subtree
(`NLAlib.eighSlotTree`), stored: its $\mathbf{U}$ at offset $2n^2 d + 2n\,lo$ of the output arena
and its eigenvalues at the cells $nd + lo + i$. -/
def EighArenas.OutHolds (H : EighArenas) (s : Store P K) (p : P) (M : FloatMachine K ℕ ℕ)
    (n signFuel D : ℕ) (R₀ β : K) (root : EighNode K) (d : ℕ) : Prop :=
  ∀ (a : List Bool) (lo : ℕ) (y : EighNode K), a.length = d →
    eighLoc M n signFuel R₀ β 0 0 root a = some (lo, y) →
      pairLayout.Holds s p H.Ua (2 * (n * n) * d + 2 * n * lo)
          (eighAux M n signFuel R₀ β (D - d) y.A y.R y.ε y.ℓ
            (eighSlotTree M n signFuel R₀ β d lo y)).1 ∧
        ∀ i : Fin y.k, s.read p H.Ea (n * d + lo + i) = some
          ((eighAux M n signFuel R₀ β (D - d) y.A y.R y.ε y.ℓ
            (eighSlotTree M n signFuel R₀ β d lo y)).2 i)

/-! ### Ideal samples -/

/-- **The ideal complex sample** $(\xi_{2z} + i\,\xi_{2z+1})/\sqrt2$ of the Gaussian draws of an
ideal tape at the complex sample $z$. -/
noncomputable def eighIdealComplex (ξ : Dist → ℕ → ℝ) (z : ℕ) : ℂ :=
  ⟨ξ .gaussian (2 * z) / √2, ξ .gaussian (2 * z + 1) / √2⟩

/-- **The ideal sample of a node** of root size $N$ and depth budget $D$, on the ideal tape $\xi$,
at the path `a`: for a node of size $k$ at slot $lo$ of depth $d < D$ (`ko = some k`), the seed at
uniform position $Nd + lo$ and the entries $(i, j)$, $i, j < k$, of the test matrices at the
static positions of `NLAlib.eighTapeSample`; every other seed and entry at a position beyond the
$N D$ uniform and $4N^2 D$ Gaussian draws of the program, indexed by the path, the side and the
entry (`Encodable.encode`). -/
noncomputable def eighIdealSample (ξ : Dist → ℕ → ℝ) (N D d lo : ℕ) (ko : Option ℕ)
    (a : List Bool) : EighSample ℝ ℂ N :=
  let fresh : Bool → Fin N → Fin N → ℂ := fun b i j =>
    eighIdealComplex ξ (2 * (N * N) * D + Encodable.encode (a, b, (i : ℕ), (j : ℕ)))
  match ko with
  | some k =>
    if d < D then
      (ξ .uniform (N * d + lo), fun b => Matrix.of fun i j =>
        if (i : ℕ) < k ∧ (j : ℕ) < k then
          eighIdealComplex ξ (2 * (N * N) * d + N * (2 * (lo + j) + if b then 0 else 1) + i)
        else fresh b i j)
    else (ξ .uniform (N * D + Encodable.encode a), fun b => Matrix.of (fresh b))
  | none => (ξ .uniform (N * D + Encodable.encode a), fun b => Matrix.of (fresh b))

/-- **The tree of ideal samples** that a run of `NLAlib.eighProg` on the ideal tape $\xi$ reads, for
the machine `M` over ideal samples: from the node $x$ (if any) at slot $lo$ of depth $d$, reached
by the path `pre`, the sample `NLAlib.eighIdealSample` at the empty path, and along $b :: a$ the
child that `NLAlib.eighStep` on that sample gives (none below a leaf and on the absent side of a
one-child node), at its slot. -/
noncomputable def eighIdealTree (M : FloatMachine F ℝ ℂ) (N signFuel D : ℕ) (R₀ β : F)
    (ξ : Dist → ℕ → ℝ) : ℕ → ℕ → Option (EighNode F) → List Bool → List Bool → EighSample ℝ ℂ N
  | d, lo, x, pre, [] => eighIdealSample ξ N D d lo (x.map EighNode.k) pre
  | d, lo, none, pre, b :: a => eighIdealTree M N signFuel D R₀ β ξ (d + 1) lo none (pre ++ [b]) a
  | d, lo, some x, pre, b :: a =>
    let q := eighNextParams M x.R x.ε x.ℓ
    match eighStep M N signFuel R₀ β x.A x.R x.ε x.ℓ (eighIdealSample ξ N D d lo (some x.k) pre)
    with
    | .leaf _ _ => eighIdealTree M N signFuel D R₀ β ξ (d + 1) lo none (pre ++ [b]) a
    | .shift b' A' _ =>
      eighIdealTree M N signFuel D R₀ β ξ (d + 1) lo
        (if b = b' then some ⟨x.k, A', q.1, q.2, x.ℓ + 1⟩ else none) (pre ++ [b]) a
    | .split kp _ _ _ Ap Am _ =>
      if b then eighIdealTree M N signFuel D R₀ β ξ (d + 1) lo (some ⟨kp, Ap, q.1, q.2, x.ℓ + 1⟩)
        (pre ++ [b]) a
      else eighIdealTree M N signFuel D R₀ β ξ (d + 1) (lo + kp)
        (some ⟨x.k - kp, Am, q.1, q.2, x.ℓ + 1⟩) (pre ++ [b]) a

end NLAlib
