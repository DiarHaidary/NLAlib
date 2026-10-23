/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Subst
public import NLAlib.Computation.Exact

/-!
# The dense implementation of an oracle

A dense $N \times N$ matrix held as read-only data of size $N^2$ at a tag, column-major, and
counted as constant memory (D14). `NLAlib.Computation.denseImpl` serves an oracle call column by
column, as `gemm` on read-only data: it zeroes the destination column and, for each entry
$(i, j)$, reads $\mathbf{A}_{i,j}$, multiplies it by source entry $j$ and adds it into destination
entry $i$. Each matrix-vector product costs $N^2$ multiplications, additions and reads and $N$
literals (`NLAlib.Computation.denseCost`), with one scratch cell. The certificate
`NLAlib.Computation.implementsOracle_denseImpl` makes it a valid substitution for the exact
oracle (through `NLAlib.Computation.RunsWithin.substOracle`). The implementation is generic in its
sizes: it takes no host data. Design: `docs/design/Computation.md` (D4, D14).

## Main definitions

* `NLAlib.Computation.denseImpl`, `NLAlib.Computation.denseInterp`,
  `NLAlib.Computation.denseCost`.

## Main results

* `NLAlib.Computation.implementsOracle_denseImpl`: the certificate.
-/

@[expose] public section

namespace NLAlib.Computation

variable {𝕜 : Type} [RCLike 𝕜] {P ι : Type} [DecidableEq P]

/-- **The dense implementation of an oracle call**: for each of the `cols` columns, zero the
destination column, then for each $j$ and $i$ read entry $i + Nj$ of the read-only data, multiply
it by source entry $j$ and add it into destination entry $i$. One scratch cell. -/
def denseImpl {VB VI : Type} (N : IExp VI) (_o : ι) (p : P) (dst : VB) (dOff : IExp VI)
    (src : VB) (sOff : IExp VI) (cols : IExp VI) : Stmt P ι VB VI :=
  Builder.run <| Builder.named "dense_apply"
      [.idx N, .buf dst, .idx dOff, .buf src, .idx sOff, .idx cols] do
    let t ← Builder.alloc p 1
    Builder.forRange cols fun c => do
      Builder.forRange N fun i => Builder.ins (.lit p ⟨dst, dOff + .var i + N * .var c⟩ 0)
      Builder.forRange N fun j => Builder.forRange N fun i => do
        Builder.stmt (.rom p ⟨t, 0⟩ (.var i + N * .var j))
        Builder.ins (.bin p .mul ⟨t, 0⟩ ⟨t, 0⟩ ⟨src, sOff + .var j + N * .var c⟩)
        Builder.ins (.bin p .add ⟨dst, dOff + .var i + N * .var c⟩
          ⟨dst, dOff + .var i + N * .var c⟩ ⟨t, 0⟩)

/-- The interpretation with $\mathbf{A}$ as read-only data of size $N^2$ at tag `p₀`,
column-major, the oracle the exact one of $\mathbf{A}$. -/
noncomputable def denseInterp {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜) (ξ : Dist → ℕ → ℝ)
    (p₀ : P) : Interp P ι 𝕜 (OpCount P ι) :=
  { exactInterp (fun _ => A) ξ with
    rom := fun e => (flatten A)[e]?
    romSize := fun q => if q = p₀ then N * N else 0 }

/-- The cost of the dense implementation: a matrix-vector product at tag $p$ is $N^2$
multiplications, additions and read-only reads and $N$ literals at $p$; a load costs nothing. -/
noncomputable def denseCost (N : ℕ) : OpKind P ι → OpCount P ι
  | .matvec p _ => Finsupp.single (.bin p .mul) (N * N) + Finsupp.single (.bin p .add) (N * N) +
      Finsupp.single (.rom p) (N * N) + Finsupp.single (.lit p) N
  | _ => 0

/-- **The dense certificate**: `denseImpl` implements the exact oracle of $\mathbf{A}$ under
`denseInterp`, at the cost `denseCost` of each matrix-vector product, every other kind kept, with
one scratch cell and no bit scratch. No printed source.
Result: dense-oracle-certificate -/
theorem implementsOracle_denseImpl {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜) (ξ : Dist → ℕ → ℝ)
    (p₀ : P) :
    ImplementsOracle (exactInterp (P := P) (ι := ι) (fun _ => A) ξ) (denseInterp A ξ p₀)
      (fun o p dst dOff src sOff cols => denseImpl (.const N) o p dst dOff src sOff cols)
      (substKind (denseCost N)) (fun _ => 1) 0 := by
  sorry

end NLAlib.Computation
