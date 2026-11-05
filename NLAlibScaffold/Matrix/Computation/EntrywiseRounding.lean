/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.EntrywiseRounding
public import NLAlib.Computation.Grid
public import NLAlib.Matrix.Norms.Compare

/-!
# Bounds for entrywise rounding (scaffold)

Statements for `NLAlib/Matrix/Computation/EntrywiseRounding.lean` (stage HDIAG, wave W1, design
note `docs/design/Eigensolvers-HermitianDiagonalization.md` §3.3): rounding to nearest on a
$t$-bit grid meets `NLAlib.IsRoundingFn` (the bridge to the contract layer, whose
`NLAlib.Computation.gridSem` rounds with the same function), and the normwise errors of the
Hermitian rounding operations and of rounded summation.

## Main results

* `NLAlib.isRoundingFn_roundNearest`: the witness from `Real.roundNearest`.
* `NLAlib.IsRoundingFn.norm_sub_roundScalar_le`.
* `NLAlib.isHermitian_roundHermitian`, `Matrix.IsHermitian.isHermitian_roundDiag`.
* `NLAlib.IsRoundingFn.specNorm_sub_roundHermitian_le`,
  `NLAlib.IsRoundingFn.specNorm_sub_roundDiag_le`.
* `NLAlib.IsRoundingFn.abs_sum_sub_roundedSum_le`.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*}

/-- **Rounding to nearest meets the rounding contract**: rounding to nearest on the grid of
$t$-bit binary numbers with unbounded exponent (`Real.roundNearest`) satisfies
`NLAlib.IsRoundingFn` with unit roundoff $2^{-t}$, floor $0$ and every range $\Omega$. It is the
rounding of `NLAlib.Computation.gridSem`, which meets the standard-model contract
`NLAlib.Computation.IsRelErrSem`. [Higham2002, Theorem 2.2].
Proof: `Real.abs_sub_roundNearest_le`, `abs_sub_comm`, and $\max(\lvert x \rvert, 0) =
\lvert x \rvert$. S, about 5 lines. -/
theorem isRoundingFn_roundNearest (t : ℕ) (Ω : ℝ) :
    IsRoundingFn (2⁻¹ ^ t) 0 Ω (Real.roundNearest t) := by
  sorry

/-- **Error of scalar rounding**: under `NLAlib.IsRoundingFn` $u$ $\tau$ $\Omega$ with
$\tau \ge 0$, every $z$ with $\lvert z \rvert \le \Omega$ satisfies
$\lvert z - \mathrm{fl}(z) \rvert \le u(\lvert z \rvert + 2\tau)$, $\mathrm{fl}(z)$ its rounded
real and imaginary parts (`NLAlib.roundScalar`).
Proof: `RCLike.re_add_im` for $z$; the two part errors are at most $u\max(\lvert \operatorname{Re}
z \rvert, \tau)$ and $u\max(\lvert \operatorname{Im} z \rvert, \tau)$ (`RCLike.abs_re_le_norm`,
`RCLike.abs_im_le_norm`); $\lvert a + bi \rvert \le \lvert a \rvert + \lvert b \rvert$
(`norm_add_le`, `RCLike.norm_ofReal`, `RCLike.norm_I_le_one`-type bounds), then
$\max(x, \tau) \le x + \tau$. Careful over $\mathbb{R}$
($\operatorname{Im} = 0$, `RCLike.I = 0`). S, about 20 lines. -/
theorem IsRoundingFn.norm_sub_roundScalar_le {u τ Ω : ℝ} {fl : ℝ → ℝ} (h : IsRoundingFn u τ Ω fl)
    (hτ : 0 ≤ τ) {z : 𝕜} (hz : ‖z‖ ≤ Ω) : ‖z - roundScalar fl z‖ ≤ u * (‖z‖ + 2 * τ) := by
  sorry

/-- The rounded Hermitian matrix is Hermitian, for every matrix and every rounding function.
Proof: `Matrix.IsHermitian.ext`; unfold `NLAlib.roundHermitian` and split the three cases of
`lt_trichotomy`; the diagonal is the coercion of a real, fixed by `star`. S, about 12 lines. -/
theorem isHermitian_roundHermitian [LinearOrder n] (fl : ℝ → ℝ) (X : Matrix n n 𝕜) :
    (roundHermitian fl X).IsHermitian := by
  sorry

/-- Rounding the diagonal of a Hermitian matrix keeps it Hermitian.
Proof: `Matrix.IsHermitian.ext`; off the diagonal the entries are those of $\mathbf{X}$, on it the
coercion of a real. S, about 8 lines. -/
theorem _root_.Matrix.IsHermitian.isHermitian_roundDiag [DecidableEq n] {X : Matrix n n 𝕜}
    (hX : X.IsHermitian) (fl : ℝ → ℝ) : (roundDiag fl X).IsHermitian := by
  sorry

/-- **Error of the rounded Hermitian matrix**: under `NLAlib.IsRoundingFn` $u$ $\tau$ $\Omega$ with
$\tau \ge 0$, a Hermitian $\mathbf{X}$ with $\|\mathbf{X}\|_2 \le \Omega$ satisfies
$$\|\mathbf{X} - \mathrm{fl}_{\mathrm{H}}(\mathbf{X})\|_2 \le
u\bigl(\sqrt{\lvert n \rvert}\,\|\mathbf{X}\|_2 + 2\lvert n \rvert\tau\bigr) \,,$$
$\mathrm{fl}_{\mathrm{H}}$ the rounding `NLAlib.roundHermitian`; the entrywise errors are
summed in Frobenius norm.
Proof: each entry error is at most $u(\lvert \mathbf{X}_{i,j} \rvert + 2\tau)$
(`NLAlib.IsRoundingFn.norm_sub_roundScalar_le` above the diagonal and its conjugate below; on the
diagonal $\mathbf{X}_{i,i}$ is real since $\mathbf{X}$ is Hermitian), entries are at most
$\|\mathbf{X}\|_2 \le \Omega$ (`NLAlib.norm_apply_le_specNorm`);
`NLAlib.specNorm_le_frobNorm`, the triangle inequality in Frobenius norm and
$\|\mathbf{X}\|_{\mathsf{F}} \le \sqrt{\lvert n \rvert}\|\mathbf{X}\|_2$
(`NLAlib.frobNorm_le_sqrt_card_mul_specNorm`). M, about 45 lines. -/
theorem IsRoundingFn.specNorm_sub_roundHermitian_le [Fintype n] [LinearOrder n] {u τ Ω : ℝ}
    {fl : ℝ → ℝ} (h : IsRoundingFn u τ Ω fl) (hτ : 0 ≤ τ) {X : Matrix n n 𝕜} (hX : X.IsHermitian)
    (hXΩ : specNorm X ≤ Ω) :
    specNorm (X - roundHermitian fl X) ≤
      u * (√(Fintype.card n : ℝ) * specNorm X + 2 * Fintype.card n * τ) := by
  sorry

/-- **Error of rounding the diagonal**: under `NLAlib.IsRoundingFn` $u$ $\tau$ $\Omega$, a
Hermitian $\mathbf{X}$ with $\|\mathbf{X}\|_2 \le \Omega$ satisfies
$\|\mathbf{X} - \mathrm{fl}_{\mathrm{D}}(\mathbf{X})\|_2 \le u\max(\|\mathbf{X}\|_2, \tau)$,
$\mathrm{fl}_{\mathrm{D}}$ the rounding of the diagonal `NLAlib.roundDiag`. The error is
diagonal, so its norm is its largest entry, as [Shah2024, proof of Lemma 2.1] notes.
Proof: the difference is `Matrix.diagonal` of the diagonal errors (real since $\mathbf{X}$ is
Hermitian), each at most $u\max(\lvert \mathbf{X}_{i,i} \rvert, \tau) \le
u\max(\|\mathbf{X}\|_2, \tau)$; the spectral norm of a diagonal matrix is its largest modulus
(`NLAlib.specNorm_diagonal_le`). Mind the degenerate case $u < 0$, in which
the hypotheses force $\mathbf{X} = \mathbf{0}$ or are contradictory. S, about 25 lines. -/
theorem IsRoundingFn.specNorm_sub_roundDiag_le [Fintype n] [DecidableEq n] {u τ Ω : ℝ} {fl : ℝ → ℝ}
    (h : IsRoundingFn u τ Ω fl) {X : Matrix n n 𝕜} (hX : X.IsHermitian)
    (hXΩ : specNorm X ≤ Ω) : specNorm (X - roundDiag fl X) ≤ u * max (specNorm X) τ := by
  sorry

/-- **Error of rounded summation**: under `NLAlib.IsRoundingFn` $u$ $\tau$ $\Omega$ with
$0 \le u$, $0 \le \tau$ and $ku \le 1/2$, for $x \in \mathbb{R}^k$ with
$2(\sum_i \lvert x_i \rvert + k\tau) \le \Omega$,
$$\Bigl\lvert \sum_i x_i - \hat s \Bigr\rvert \le 2ku\Bigl(\sum_i \lvert x_i \rvert + k\tau\Bigr)
\,,$$
$\hat s$ the left-to-right rounded sum (`NLAlib.roundedSum`). [Higham2002, (4.4)], there with
$\gamma_{k-1}$ and $\tau = 0$.
Proof: induction over the prefix sums with the invariant $E_i \le ((1 + u)^i - 1)(S + \tau)$ for
the accumulated error $E_i$ and $S = \sum_i \lvert x_i \rvert$ (each step errs by at most
$u(\lvert \hat s_i + x_i \rvert + \tau)$, and the partial sums stay below $2(S + k\tau) \le
\Omega$); then $(1 + u)^k - 1 \le e^{ku} - 1 \le 2ku$ for $ku \le 1/2$ (`Real.add_one_le_exp`,
`Real.exp_le_one_add_mul`-type bound or `Real.exp_bound`). M, about 50 lines. -/
theorem IsRoundingFn.abs_sum_sub_roundedSum_le {u τ Ω : ℝ} {fl : ℝ → ℝ}
    (h : IsRoundingFn u τ Ω fl) (hu : 0 ≤ u) (hτ : 0 ≤ τ) {k : ℕ} (hku : k * u ≤ 1 / 2)
    {x : Fin k → ℝ} (hΩ : 2 * (∑ i, |x i| + k * τ) ≤ Ω) :
    |∑ i, x i - roundedSum fl x| ≤ 2 * k * u * (∑ i, |x i| + k * τ) := by
  sorry

end NLAlib
