/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.EntrywiseRounding

/-!
# Deflation: an orthonormal basis of the range of a near-low-rank matrix

`NLAlib.deflate M r P G` returns the first $r$ columns of the $\mathbf{Q}$ factor of the
machine's QR factorization of $\mathrm{mm}(\mathbf{P}, \widetilde{\mathbf{G}})$, where
$\widetilde{\mathbf{G}}$ is the stored version (the machine's normal sampler, entrywise) of an
ideal sample $\mathbf{G}$ ([Shah2024, Algorithm 2]). For $\mathbf{P}$ close to a matrix of rank
$r$ and $\mathbf{G}$ a standard complex Gaussian matrix the output is, with high probability,
close to an orthonormal basis of the range ([Shah2024, Theorem 3.3]). It is the randomized range
finder without oversampling, as in [BanksGarzaVargasKulkarniSrivastava2020], here with a
Gaussian rather than a Haar test matrix. The definition is computable and written over a
`NLAlib.FloatMachine`.

## Main definitions

* `NLAlib.deflate`.

## Main results

The deterministic error bound and its Gaussian tail are in the design note
`docs/design/Eigensolvers-HermitianDiagonalization.md` (stage HDIAG).
-/

@[expose] public section

namespace NLAlib

/-- **Randomized deflation** $\mathsf{deflate}(\mathbf{P}, r)$ with ideal sample $\mathbf{G}$, on
the machine `M`: the first $r$ columns of $\mathbf{Q}$, where $(\mathbf{Q}, \mathbf{R}) =
\mathrm{qr}(\mathrm{mm}(\mathbf{P}, \widetilde{\mathbf{G}}))$ and $\widetilde{\mathbf{G}}$ is
$\mathbf{G}$ with every entry replaced by its stored version $\mathrm{normal}(\mathbf{G}_{i,j})$.
Junk value: the columns beyond the $n$-th are stored zeros when $r > n$. [Shah2024, Algorithm 2].
Algorithm: deflate -/
def deflate {F Su Sg : Type*} (M : FloatMachine F Su Sg) {n : ℕ} (r : ℕ)
    (P : Matrix (Fin n) (Fin n) (F × F)) (G : Matrix (Fin n) (Fin n) Sg) :
    Matrix (Fin n) (Fin r) (F × F) :=
  Matrix.of fun i j =>
    if h : (j : ℕ) < n then (M.qr (M.mm P (G.map M.normal))).1 i ⟨j, h⟩ else (M.zero, M.zero)

end NLAlib
