/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.Primitives

/-!
# Deflation: an orthonormal basis of the range of a near-low-rank matrix

`NLAlib.deflate mm qr normal r P G` returns the first $r$ columns of the computed $\mathbf{Q}$
of a QR factorization of the computed product $\mathbf{P}\widetilde{\mathbf{G}}$, where
$\widetilde{\mathbf{G}}$ is the computed version (`normal` entrywise) of a sample
$\mathbf{G}$ ([Shah2024, Algorithm 2]). For $\mathbf{P}$ close to a matrix of rank $r$ and
$\mathbf{G}$ a standard complex Gaussian matrix the output is, with high probability, close to an
orthonormal basis of the range ([Shah2024, Theorem 3.3]); the matrix multiplication and the QR
factorization are black boxes (`NLAlib.IsMatMulErr`, `NLAlib.IsQRErr`). It is the randomized
range finder without oversampling, as in [BanksGarzaVargasKulkarniSrivastava2020], here with a
Gaussian rather than a Haar test matrix.

## Main definitions

* `NLAlib.deflate`.

## Main results

The deterministic error bound and its Gaussian tail are in the design note
`docs/design/Eigensolvers-HermitianDiagonalization.md` (stage HDIAG).
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

/-- **Randomized deflation** $\mathsf{deflate}(\mathbf{P}, r)$ with sample $\mathbf{G}$: the first
$r$ columns of $\mathbf{Q}$, where $(\mathbf{Q}, \mathbf{R}) =
\mathrm{qr}(\mathrm{mm}(\mathbf{P}, \widetilde{\mathbf{G}}))$ and $\widetilde{\mathbf{G}}$ is
$\mathbf{G}$ with every entry replaced by its computed version $\mathrm{normal}(\mathbf{G}_{i,j})$.
Junk value: the columns beyond the $n$-th are zero when $r > n$. [Shah2024, Algorithm 2].
Algorithm: deflate -/
noncomputable def deflate (mm : MatMulMap ℂ) (qr : QRMap ℂ) (normal : ℂ → ℂ) {n : ℕ} (r : ℕ)
    (P G : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin r) ℂ :=
  Matrix.of fun i j =>
    if h : (j : ℕ) < n then (qr (mm P (G.map normal))).1 i ⟨j, h⟩ else 0

end NLAlib
