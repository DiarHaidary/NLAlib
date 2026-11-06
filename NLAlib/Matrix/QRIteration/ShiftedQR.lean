/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Algebra.Polynomial.Roots
public import NLAlib.Matrix.Factorizations.GivensHessenberg
public import NLAlib.Matrix.Norms.Spectral

/-!
# The Hessenberg shifted QR step and its potential

The objects of the exact-arithmetic analysis of the Hessenberg shifted QR algorithm
[BanksGarzaVargasSrivastava2021]. A square matrix is indexed by `Fin (n + 1)`, so that its last
row $\mathbf{e}_n^{\mathsf{H}}\mathbf{H}$ is `H (Fin.last n)` and its $n$ subdiagonal entries are
$\mathbf{H}_{i+1,i}$ for `i : Fin n`.

* `NLAlib.IsDecoupled δ H`: some subdiagonal entry has modulus at most $\delta\|\mathbf{H}\|_2$
  (with $\delta = 0$: $\mathbf{H}$ is reduced).
* `NLAlib.hessenbergPotential k H`: the geometric mean $\psi_k(\mathbf{H})$ of the last $k$
  subdiagonal moduli, the potential that tracks convergence.
* `NLAlib.shiftPoly ss`: the monic polynomial $\prod_{s}(z - s)$ with roots the list `ss`.
* `NLAlib.shiftedQRStep H s`: one single-shift QR step
  $\mathbf{Q}^{\mathsf{H}}\mathbf{H}\mathbf{Q}$, $\mathbf{Q}$ the unitary factor of Givens QR of
  $\mathbf{H} - s\mathbf{I}$; `NLAlib.multiShiftedQRStep H ss` composes them, which is the degree
  $k$ step with shift polynomial `shiftPoly ss` (the implicit QR step of the paper, in exact
  arithmetic).
* `NLAlib.trailingBlock k H`, `NLAlib.ritzValues k H`: the trailing $k \times k$ block and its
  eigenvalues, the Ritz values.

These are mathematical objects, not implementations: Givens coefficients take square roots and
the definitions are noncomputable. The finite-precision implementation is a separate stage
(design note `docs/design/Eigensolvers-ShiftedQR.md`, §9).

## Main definitions

* `NLAlib.IsDecoupled`, `NLAlib.hessenbergPotential`, `NLAlib.shiftPoly`,
  `NLAlib.shiftedQRStep`, `NLAlib.multiShiftedQRStep`, `NLAlib.trailingBlock`,
  `NLAlib.ritzValues`.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {n : ℕ}

/-- A square matrix is **$\delta$-decoupled** if some subdiagonal entry is small relative to
the norm: $\lvert\mathbf{H}_{i+1,i}\rvert \le \delta\|\mathbf{H}\|_2$ for some $i < n$. With
$\delta = 0$ this says that $\mathbf{H}$ is reduced (a subdiagonal entry vanishes).
[BanksGarzaVargasSrivastava2021, §1], where the decoupling time is the first QR step at which
this holds. -/
def IsDecoupled (δ : ℝ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : Prop :=
  ∃ i : Fin n, ‖H i.succ i.castSucc‖ ≤ δ * specNorm H

/-- The **potential** $\psi_k(\mathbf{H})$: the geometric mean of the moduli of the last $k$
subdiagonal entries, $\psi_k(\mathbf{H}) = \bigl(\prod_{n - k \le i < n}
\lvert\mathbf{H}_{i+1,i}\rvert\bigr)^{1/k}$ (indices from $0$; for $k > n$ all $n$ entries
enter). [BanksGarzaVargasSrivastava2021, Definition 2.2], where the product is printed with
$k + 1$ factors; $k$ is meant (the proof of Lemma 2.3 there uses $k$). -/
noncomputable def hessenbergPotential (k : ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : ℝ :=
  (∏ i ∈ Finset.univ.filter (fun i : Fin n => n ≤ (i : ℕ) + k), ‖H i.succ i.castSucc‖) ^
    ((k : ℝ)⁻¹)

/-- The monic **shift polynomial** $\prod_{s \in \mathrm{ss}} (z - s)$ of a list of shifts. -/
noncomputable def shiftPoly (ss : List ℂ) : Polynomial ℂ :=
  (ss.map fun s => Polynomial.X - Polynomial.C s).prod

/-- One **single-shift QR step** with shift $s$: with $\mathbf{Q}$ the unitary factor of Givens
QR of $\mathbf{H} - s\mathbf{I}$ (`NLAlib.givensHessenbergQ`), the matrix
$\mathbf{Q}^{\mathsf{H}}\mathbf{H}\mathbf{Q} = \mathbf{R}\mathbf{Q} + s\mathbf{I}$. On an upper
Hessenberg matrix it is the exact-arithmetic implicit QR step of
[BanksGarzaVargasSrivastava2021, Definition 2.1]. Givens QR never breaks down, so the step is
defined also when $\mathbf{H} - s\mathbf{I}$ is singular, and it keeps the Hessenberg form then.
[GolubVanLoan2013, §7.5.2].
Algorithm: shifted-qr (specification) -/
noncomputable def shiftedQRStep (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (s : ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  (givensHessenbergQ (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)))ᴴ * H *
    givensHessenbergQ (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))

/-- The **multi-shift QR step**: the single-shift steps with the shifts of `ss` in order,
$\mathsf{multiShiftedQRStep}(\mathbf{H}, [s_1, \dots, s_k]) =
\mathsf{shiftedQRStep}(\cdots\mathsf{shiftedQRStep}(\mathbf{H}, s_1)\cdots, s_k)$. It is a QR
step with shift polynomial $\prod_i (z - s_i)$ (composition, [BanksGarzaVargasSrivastava2022,
Lemma 3.2]), and the degree $k$ implicit QR step of the paper in exact arithmetic. -/
noncomputable def multiShiftedQRStep (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (ss : List ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  ss.foldl shiftedQRStep H

/-- The **trailing $k \times k$ block** $\mathbf{H}_{(k)}$: the principal submatrix on the last
$k$ indices $n + 1 - k, \dots, n$ (for $k > n + 1$ the indices are clamped at $n$, a junk value
no statement uses). -/
def trailingBlock (k : ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  H.submatrix (fun i : Fin k => ⟨min (n + 1 - k + i) n, Nat.lt_succ_of_le (min_le_right _ _)⟩)
    (fun i : Fin k => ⟨min (n + 1 - k + i) n, Nat.lt_succ_of_le (min_le_right _ _)⟩)

/-- The **Ritz values** of order $k$: the eigenvalues of the trailing block
$\mathbf{H}_{(k)}$, with multiplicity, as a list (the roots of the characteristic polynomial
$\chi_k$ of $\mathbf{H}_{(k)}$, in an unspecified order).
[BanksGarzaVargasSrivastava2021, §1.1]. -/
noncomputable def ritzValues (k : ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : List ℂ :=
  (trailingBlock k H).charpoly.roots.toList

end NLAlib
