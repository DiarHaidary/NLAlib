/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.GivensHessenberg

/-!
# The Givens unitary factor is Hessenberg (scaffold)

An addition to `NLAlib/Matrix/Factorizations/GivensHessenberg.lean` (stage SHIFTED-QR, wave W0,
design note `docs/design/Eigensolvers-ShiftedQR.md` §3.2, id Q0): the accumulated unitary factor
of Givens QR is upper Hessenberg, for any input. It makes the shifted QR step of
`NLAlib.shiftedQRStep` keep the Hessenberg form also when the shifted matrix is singular.

## Main results

* `NLAlib.isUpperHessenberg_givensHessenbergQ`.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m p : ℕ}

/-- **The unitary factor of Givens QR is upper Hessenberg**: for every
$\mathbf{H} \in \Bbbk^{m \times p}$, the factor $\mathbf{G}_0^{\mathsf{H}} \cdots
\mathbf{G}_{p-1}^{\mathsf{H}}$ (`NLAlib.givensHessenbergQ`), a product of rotations in the planes
$(k, k+1)$ in increasing order, vanishes below the first subdiagonal. No hypothesis on
$\mathbf{H}$: the planes, not the coefficients, give the pattern. [GolubVanLoan2013, §5.2.5].
Proof: induction on the number $k$ of steps in `NLAlib.givensHessenbergState`, with the
invariant that the first component $\mathbf{S}$ has $\mathbf{S}_{i,j} = 0$ for $j + 1 < i$ and
agrees with the identity in the columns $j > k$; right multiplication by
$\mathbf{G}_k^{\mathsf{H}}$ (`NLAlib.givensHessenbergStep`) mixes only the columns $k$ and $k+1$,
and column $k + 1$ of $\mathbf{S}$ is $\mathbf{e}_{k+1}$, so the new columns $k$, $k+1$ are
supported on rows $\le k + 1$ (`NLAlib.mul_givens_apply_left`, `NLAlib.mul_givens_apply_right`,
`NLAlib.mul_givens_apply_of_ne`; the identity case is trivial). M, about 40 lines. -/
theorem isUpperHessenberg_givensHessenbergQ (H : Matrix (Fin m) (Fin p) 𝕜) :
    IsUpperHessenberg (givensHessenbergQ H) := by
  sorry

end NLAlib
