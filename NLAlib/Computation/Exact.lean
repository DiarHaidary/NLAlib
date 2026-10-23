/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Matrix.Mul
public import NLAlib.Computation.RunsWithin
public import NLAlib.ForMathlib.Data.Nat.Init

/-!
# Exact arithmetic and the matrix layout

The exact interpretation of programs over an `RCLike` field $\Bbbk$: `NLAlib.Computation.exactSem`
is exact field arithmetic (division by zero, the square root of a number that is not
nonnegative, and the word operations fail), and `NLAlib.Computation.exactInterp A ξ` gives each
oracle name `o` the matrix `A o`, reads the tape of each distribution from `ξ`, charges one per
operation and has no read-only data. Matrices are stored column-major from an offset:
`NLAlib.Computation.flatten`, `NLAlib.Computation.unflatten`, and
`NLAlib.Computation.Holds s p b off M` (buffer `b` holds `M` from `off`). A test matrix drawn
from the tape is `NLAlib.Computation.tapeMatrix x off N k`, entry $(i, j)$ the tape value at
$\mathit{off} + i + Nj$. Realisations are stated at `Fin N` (D9). Design:
`docs/design/Computation.md` (D9, D12).

## Main definitions

* `NLAlib.Computation.exactSem`, `NLAlib.Computation.exactInterp`.
* `NLAlib.Computation.flatten`, `NLAlib.Computation.unflatten`, `NLAlib.Computation.matOracle`.
* `NLAlib.Computation.inputState`, `NLAlib.Computation.tapeMatrix`, `NLAlib.Computation.Holds`.

## Main results

* `NLAlib.Computation.Holds.write`: a write outside the block keeps `Holds`.
* `NLAlib.Computation.getElem?_flatten`, `NLAlib.Computation.unflatten_flatten`: the layout.
* `NLAlib.Computation.exec_apply_exactInterp`: an oracle call under exact arithmetic.
-/

@[expose] public section

open scoped Matrix ComplexOrder

namespace NLAlib.Computation

variable {𝕜 : Type} [RCLike 𝕜] {P ι : Type} [DecidableEq P]

open Classical in
/-- **Exact arithmetic** over $\Bbbk$: the field operations, with division by zero failing;
`conj` and `re` as in $\Bbbk$; the square root of a nonnegative element (in the order of
$\Bbbk$, so of a real number) and failing otherwise; comparisons in the order of $\Bbbk$;
conversions the identity; integer and bitwise operations failing. -/
noncomputable def exactSem : ScalarSem P 𝕜 where
  lit _ q := some (q : 𝕜)
  bin _ b x y := match b with
    | .add => some (x + y) | .sub => some (x - y) | .mul => some (x * y)
    | .div => if y = 0 then none else some (x / y)
    | _ => none
  un _ u x := match u with
    | .neg => some (-x) | .conj => some (star x) | .re => some (RCLike.re x : 𝕜)
    | .sqrt => if 0 ≤ x then some ((√(RCLike.re x) : ℝ) : 𝕜) else none
    | .bnot => none
  cmp _ c x y := match c with
    | .eq => some (decide (x = y)) | .lt => some (decide (x < y)) | .le => some (decide (x ≤ y))
  convert _ _ x := some x

/-- An $N \times \ell$ matrix as a column-major array of length $N\ell$: entry $(i, j)$ at
$i + Nj$. -/
def flatten {N ℓ : ℕ} (X : Matrix (Fin N) (Fin ℓ) 𝕜) : Array 𝕜 :=
  (List.range (N * ℓ)).toArray.map fun t =>
    if h : t % N < N ∧ t / N < ℓ then X ⟨t % N, h.1⟩ ⟨t / N, h.2⟩ else 0

/-- A column-major array as an $N \times \ell$ matrix; entries past the end are $0$. -/
def unflatten (N ℓ : ℕ) (xs : Array 𝕜) : Matrix (Fin N) (Fin ℓ) 𝕜 :=
  Matrix.of fun i j => xs.getD (i + N * j) 0

/-- The oracle of a square matrix: a block of `cols` columns, stored column-major, to its product;
`none` if the block has the wrong length. -/
def matOracle {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜) (cols : ℕ) (xs : Array 𝕜) :
    Option (Array 𝕜) :=
  if xs.size = N * cols then some (flatten (A * unflatten N cols xs)) else none

/-- **The exact interpretation**: one matrix per oracle name (so $\mathbf{A}^{\mathsf{H}}$ is
another name with its own matrix), the tape `ξ` cast into $\Bbbk$, the standard charge (one per
operation), no read-only data, and width $0$. -/
noncomputable def exactInterp {N : ℕ} (A : ι → Matrix (Fin N) (Fin N) 𝕜) (ξ : Dist → ℕ → ℝ) :
    Interp P ι 𝕜 (OpCount P ι) where
  sem := exactSem
  charge k := Finsupp.single k 1
  tape d i := (ξ d i : 𝕜)
  oracle o cols xs := matOracle (A o) cols xs
  height _ := N
  rom _ := none
  romSize _ := 0
  width _ := 0

/-- The initial state with the input and output buffers `bufs` at tag `p`, counted from the
start: zero counts, tape positions $0$, current and peak memory the total length of the
buffers. -/
def inputState {K C : Type} [Zero C] (p : P) (bufs : List (Array (Option K))) : St P K C where
  store := (bufs.map fun b => (p, b)).toArray
  pos _ := 0
  cnt := 0
  cur q := if q = p then (bufs.map Array.size).sum else 0
  peak q := if q = p then (bufs.map Array.size).sum else 0
  curW := 0
  peakW := 0

/-- The $N \times k$ matrix drawn from the tape `x` from position `off`, column-major: entry
$(i, j)$ is the tape value at $\mathit{off} + i + Nj$. -/
def tapeMatrix (x : ℕ → ℝ) (off N k : ℕ) : Matrix (Fin N) (Fin k) 𝕜 :=
  Matrix.of fun i j => (x (off + i + N * j) : 𝕜)

/-- Buffer `b` holds the $N \times k$ matrix $\mathbf{M}$ at tag `p`, column-major from offset
`off`. -/
def Holds {N k : ℕ} (s : Store P 𝕜) (p : P) (b off : ℕ) (M : Matrix (Fin N) (Fin k) 𝕜) : Prop :=
  ∀ (i : Fin N) (j : Fin k), s.read p b (off + i + N * j) = some (M i j)

/-- The length of a flattened matrix. -/
theorem size_flatten {N ℓ : ℕ} (X : Matrix (Fin N) (Fin ℓ) 𝕜) : (flatten X).size = N * ℓ := by
  simp [flatten]

/-- Entry $(i, j)$ of a flattened matrix is at $i + Nj$. -/
theorem getElem?_flatten {N ℓ : ℕ} (X : Matrix (Fin N) (Fin ℓ) 𝕜) (i : Fin N) (j : Fin ℓ) :
    (flatten X)[(i : ℕ) + N * j]? = some (X i j) := by
  have hlt : (i : ℕ) + N * j < N * ℓ := Nat.add_mul_lt_mul_of_lt_of_lt i.2 j.2
  have hN : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le _) i.2
  have hmod : ((i : ℕ) + N * j) % N = i := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.2]
  have hdiv : ((i : ℕ) + N * j) / N = j := by
    rw [Nat.add_mul_div_left _ _ hN, Nat.div_eq_of_lt i.2, zero_add]
  simp [flatten, hlt, hmod, hdiv]

/-- Unflattening inverts flattening. -/
theorem unflatten_flatten {N ℓ : ℕ} (X : Matrix (Fin N) (Fin ℓ) 𝕜) :
    unflatten N ℓ (flatten X) = X := by
  ext i j
  simp only [unflatten, Matrix.of_apply]
  rw [Array.getD_eq_getD_getElem?, getElem?_flatten]
  rfl

omit [RCLike 𝕜] in
/-- A write outside the block of $\mathbf{M}$ keeps `Holds`. The side condition on flat indices
$i + Nj$ is nonlinear; `Nat.add_mul_lt_mul_of_lt_of_lt` and
`Nat.add_mul_eq_add_mul_iff_of_lt` discharge it. -/
theorem Holds.write {N k : ℕ} {s s' : Store P 𝕜} {p p' : P} {b off b' i' : ℕ} {v : 𝕜}
    {M : Matrix (Fin N) (Fin k) 𝕜} (h : Holds s p b off M) (hw : s.write p' b' i' v = some s')
    (hout : b' = b → i' < off ∨ off + N * k ≤ i') : Holds s' p b off M := by
  intro i j
  rw [Store.read_of_write_eq_some_of_ne hw, h i j]
  by_cases hb : b = b'
  · subst hb
    right
    have := Nat.add_mul_lt_mul_of_lt_of_lt i.2 j.2
    rcases hout rfl with h1 | h1 <;> omega
  · exact Or.inl hb

/-- An oracle call under the exact interpretation of $\mathbf{A}$, from offset $0$ of buffer
`src` into offset $0$ of another buffer `dst`, with $m$ columns: if `src` holds the
$N \times m$ matrix $\mathbf{W}$ column-major and the block write of $\mathbf{A}\mathbf{W}$
into `dst` succeeds, the call writes it and counts one load and $m$ matrix-vector products at
tag `p`. -/
theorem exec_apply_exactInterp {N m : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜)
    (ξ : Dist → ℕ → ℝ) (o : ι) (p : P) (dst src : ℕ) (cols : IExp ℕ) (hm : cols.eval = m)
    (st : St P 𝕜 (OpCount P ι)) (W : Matrix (Fin N) (Fin m) 𝕜) (hne : dst ≠ src)
    (hsrc : ∀ (a : Fin N) (c : Fin m), st.store.read p src (N * c + a) = some (W a c))
    {s' : Store P 𝕜} (hw : st.store.writeBlock p dst 0 (flatten (A * W)) = some s') :
    exec (exactInterp (fun _ => A) ξ) (.apply o p dst 0 src 0 cols) st =
      some { st with
        store := s'
        cnt := st.cnt + (Finsupp.single (OpKind.load p o) 1 +
          m • Finsupp.single (OpKind.matvec p o) 1) } := by
  subst hm
  rw [exec, if_pos (Or.inl hne)]
  have hrb : st.store.readBlock p src (IExp.eval 0)
      ((exactInterp (P := P) (fun _ => A) ξ).height o * cols.eval) = some (flatten W) :=
    Store.readBlock_eq_some_map_range _ fun i hi => by
      change i < N * cols.eval at hi
      have hN : 0 < N := Nat.pos_of_ne_zero (by rintro rfl; simp at hi)
      have hc : i / N < cols.eval := Nat.div_lt_of_lt_mul hi
      rw [IExp.eval_zero, zero_add, ← Nat.div_add_mod i N,
        hsrc ⟨i % N, Nat.mod_lt _ hN⟩ ⟨i / N, hc⟩, Nat.div_add_mod i N]
      simp [Nat.mod_lt _ hN, hc]
  rw [hrb]
  simp only [Option.bind_some]
  have hor : (exactInterp (P := P) (fun _ => A) ξ).oracle o cols.eval (flatten W) =
      some (flatten (A * W)) := by
    change matOracle A cols.eval (flatten W) = _
    rw [matOracle, if_pos (size_flatten W), unflatten_flatten]
  rw [hor, Option.bind_some, IExp.eval_zero, hw]
  rfl

end NLAlib.Computation
