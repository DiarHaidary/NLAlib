/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.Primitives
public import NLAlib.Matrix.Factorizations.QR

/-!
# Witnesses and a bridge for the primitive contracts (scaffold)

Statements for `NLAlib/Matrix/Computation/Primitives.lean` (stage HDIAG, wave W1, design note
`docs/design/Eigensolvers-HermitianDiagonalization.md` §3.3): exact multiplication and an exact
QR factorization meet the contracts (so they are satisfiable for every $u \ge 0$), and a mixed
absolute–relative product bound, the form a bounded-exponent model gives, implies the contract
with a floor (§12 of the note, item (b)).

## Main results

* `NLAlib.isMatMulErr_mul`, `NLAlib.exists_isQRErr`: exact arithmetic meets the contracts.
* `NLAlib.IsMatMulErr.of_specNorm_mul_sub_le_add`: from a mixed bound to the floor form.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **Exact multiplication meets the product contract**: for $u \ge 0$ and $\mu \ge 0$, the
product $(\mathbf{A}, \mathbf{B}) \mapsto \mathbf{A}\mathbf{B}$ satisfies `NLAlib.IsMatMulErr`
$u$ $\tau$ $\Omega$ $\mu$ for every floor and range. No printed source.
Proof: the error is $0 \le \mu(d)\,u\max(\cdot, \tau)$ since the maximum is at least the
nonnegative product of norms (`NLAlib.specNorm_nonneg`, `le_max_left`);
$\mathbf{A}\mathbf{A}^{\mathsf{H}}$
is Hermitian (`Matrix.isHermitian_mul_conjTranspose_self`). S, about 8 lines. -/
theorem isMatMulErr_mul {u τ Ω : ℝ} {μ : ℕ → ℝ} (hu : 0 ≤ u) (hμ : ∀ d, 0 ≤ μ d) :
    IsMatMulErr (𝕜 := 𝕜) u τ Ω μ fun A B => A * B := by
  sorry

/-- **An exact QR factorization meets the QR contract**: for $u \ge 0$ and $\mu \ge 0$ there is a
routine satisfying `NLAlib.IsQRErr` $u$ $\tau$ $\Omega$ $\mu$, for every floor and range. No
printed source.
Proof: choose, for each $\mathbf{A}$, the factors of
`NLAlib.exists_hasOrthonormalCols_mul_isUpperTrapezoidal`; take $\mathbf{Q}' = \mathbf{Q}$, so
both errors are $0$. S, about 10 lines. -/
theorem exists_isQRErr {u τ Ω : ℝ} {μ : ℕ → ℝ} (hu : 0 ≤ u) (hμ : ∀ d, 0 ≤ μ d) :
    ∃ qr : QRMap 𝕜, IsQRErr u τ Ω μ qr := by
  sorry

/-- **From a mixed absolute–relative product bound to the contract with a floor**: if a routine
satisfies $\|\mathbf{A}\mathbf{B} - \mathrm{mm}(\mathbf{A}, \mathbf{B})\|_2 \le
\mu(d)\,u\,\|\mathbf{A}\|_2\|\mathbf{B}\|_2 + \eta$ whenever $\|\mathbf{A}\|_2\|\mathbf{B}\|_2
\le \Omega$, computes $\mathrm{mm}(\mathbf{A}, \mathbf{A}^{\mathsf{H}})$ exactly Hermitian, and
$\eta \le \mu(d)\,u\,\tau$ for every $d$, then it satisfies `NLAlib.IsMatMulErr` $u$ $\tau$
$\Omega$ $2\mu$. A bounded-exponent product bound (underflow as an absolute $\eta$) therefore
gives the contract with floor $\tau = \eta/(\mu u)$. No printed source.
Proof: $\mu u x + \eta \le \mu u x + \mu u \tau \le 2\mu u\max(x, \tau)$ (`add_le_add`,
`le_max_left`, `le_max_right`, `two_mul`); the Hermitian field is the hypothesis. S, about
12 lines. -/
theorem IsMatMulErr.of_specNorm_mul_sub_le_add {u τ Ω η : ℝ} {μ : ℕ → ℝ} {mm : MatMulMap 𝕜}
    (hmix : ∀ {l m n : ℕ} (A : Matrix (Fin l) (Fin m) 𝕜) (B : Matrix (Fin m) (Fin n) 𝕜),
      specNorm A * specNorm B ≤ Ω →
        specNorm (A * B - mm A B) ≤ μ (max l (max m n)) * u * (specNorm A * specNorm B) + η)
    (hherm : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) 𝕜), Matrix.IsHermitian (mm A Aᴴ))
    (hμu : ∀ d, 0 ≤ μ d * u) (hη : ∀ d, η ≤ μ d * u * τ) :
    IsMatMulErr u τ Ω (fun d => 2 * μ d) mm := by
  sorry

end NLAlib
