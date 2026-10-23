/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Subst
public import NLAlib.Computation.Exact

/-!
# The coordinate (COO) implementation of an oracle

A sparse matrix in coordinate form: a pattern of `nnz` positions $(i, j)$, unrolled into the
implementation as host data, and the values `vals`, held as read-only data of size `nnz` at a tag
and counted as constant memory (D14). `NLAlib.Computation.cooImpl` serves an oracle call column
by column: it zeroes the destination column and, for each stored entry, reads its value, multiplies
it by the source entry and adds it into the destination. Each matrix-vector product costs `nnz`
multiplications, additions and reads and $N$ literals (`NLAlib.Computation.cooCost`), with one
scratch cell. The certificate `NLAlib.Computation.implementsOracle_cooImpl` makes it a valid
substitution for the exact oracle of `NLAlib.Computation.cooMatrix` (through
`NLAlib.Computation.RunsWithin.substOracle`). The index storage of the pattern is host data and
is not counted. Design: `docs/design/Computation.md` (D4, D14).

## Main definitions

* `NLAlib.Computation.cooImpl`, `NLAlib.Computation.cooMatrix`, `NLAlib.Computation.cooInterp`,
  `NLAlib.Computation.cooCost`.

## Main results

* `NLAlib.Computation.implementsOracle_cooImpl`: the certificate.
-/

@[expose] public section

namespace NLAlib.Computation

variable {𝕜 : Type} [RCLike 𝕜] {P ι : Type} [DecidableEq P]

/-- **The COO implementation of an oracle call**: for each of the `cols` columns, zero the
destination column, then for each entry $e$ of the pattern at position $(i, j)$ read value $e$ of
the read-only data, multiply it by source entry $j$ and add it into destination entry $i$. One
scratch cell. The pattern is host data, unrolled into the program. -/
def cooImpl {VB VI : Type} (N : IExp VI) (pattern : List (ℕ × ℕ)) (_o : ι) (p : P) (dst : VB)
    (dOff : IExp VI) (src : VB) (sOff : IExp VI) (cols : IExp VI) : Stmt P ι VB VI :=
  Builder.run <| Builder.named "coo_apply"
      [.idx N, .buf dst, .idx dOff, .buf src, .idx sOff, .idx cols] do
    let t ← Builder.alloc p 1
    Builder.forRange cols fun c => do
      Builder.forRange N fun i => Builder.ins (.lit p ⟨dst, dOff + .var i + N * .var c⟩ 0)
      pattern.zipIdx.forM fun ((i, j), e) => do
        Builder.stmt (.rom p ⟨t, 0⟩ (.const e))
        Builder.ins (.bin p .mul ⟨t, 0⟩ ⟨t, 0⟩ ⟨src, sOff + .const j + N * .var c⟩)
        Builder.ins (.bin p .add ⟨dst, dOff + .const i + N * .var c⟩
          ⟨dst, dOff + .const i + N * .var c⟩ ⟨t, 0⟩)

/-- The $N \times N$ matrix of a pattern and values: entry $(i, j)$ is the sum of the values of
the pattern entries at position $(i, j)$ (repeated positions add up). -/
def cooMatrix {N : ℕ} (pattern : List (ℕ × ℕ)) (vals : ℕ → 𝕜) : Matrix (Fin N) (Fin N) 𝕜 :=
  Matrix.of fun i j => ∑ e ∈ Finset.range pattern.length,
    if pattern[e]? = some (i.1, j.1) then vals e else 0

/-- The interpretation with the COO values as read-only data of size `nnz` at tag `p₀`, the
oracle the exact one of `NLAlib.Computation.cooMatrix`. -/
noncomputable def cooInterp {N : ℕ} (pattern : List (ℕ × ℕ)) (vals : ℕ → 𝕜)
    (ξ : Dist → ℕ → ℝ) (p₀ : P) : Interp P ι 𝕜 (OpCount P ι) :=
  { exactInterp (fun _ => cooMatrix (N := N) pattern vals) ξ with
    rom := fun e => if e < pattern.length then some (vals e) else none
    romSize := fun q => if q = p₀ then pattern.length else 0 }

/-- The cost of the COO implementation: a matrix-vector product at tag $p$ is `nnz`
multiplications, additions and read-only reads and $N$ literals at $p$; a load costs nothing. -/
noncomputable def cooCost (N nnz : ℕ) : OpKind P ι → OpCount P ι
  | .matvec p _ => Finsupp.single (.bin p .mul) nnz + Finsupp.single (.bin p .add) nnz +
      Finsupp.single (.rom p) nnz + Finsupp.single (.lit p) N
  | _ => 0

/-- **The COO certificate**: for a pattern with positions in $[0, N)^2$, `cooImpl` implements the
exact oracle of `cooMatrix pattern vals` under `cooInterp`, at the cost `cooCost` of each
matrix-vector product, every other kind kept, with one scratch cell and no bit scratch.
No printed source.
Result: coo-oracle-certificate -/
theorem implementsOracle_cooImpl {N : ℕ} (pattern : List (ℕ × ℕ))
    (hpat : ∀ ij ∈ pattern, ij.1 < N ∧ ij.2 < N) (vals : ℕ → 𝕜) (ξ : Dist → ℕ → ℝ) (p₀ : P) :
    ImplementsOracle (exactInterp (P := P) (ι := ι) (fun _ => cooMatrix (N := N) pattern vals) ξ)
      (cooInterp (N := N) pattern vals ξ p₀)
      (fun o p dst dOff src sOff cols => cooImpl (.const N) pattern o p dst dOff src sOff cols)
      (substKind (cooCost N pattern.length)) (fun _ => 1) 0 := by
  sorry

end NLAlib.Computation
