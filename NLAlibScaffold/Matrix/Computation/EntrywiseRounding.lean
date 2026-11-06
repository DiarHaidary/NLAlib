/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.EntrywiseRounding
public import NLAlib.Computation.Grid
public import NLAlib.Computation.BinaryFloat
public import NLAlib.Matrix.Norms.Compare

/-!
# Bounds for the entrywise operations of a floating-point machine (scaffold)

Statements for `NLAlib/Matrix/Computation/EntrywiseRounding.lean` (stage HDIAG, wave W1, design
note `docs/design/Eigensolvers-HermitianDiagonalization.md` §3.3): rounding to nearest on a
$t$-bit grid is a rounding in the sense of `NLAlib.IsRoundingOf` (the bridge to the contract
layer, whose `NLAlib.Computation.gridSem` rounds with the same function); the exact operations
decode exactly; the rounded entrywise operations, built from the machine's scalar operations,
have the normwise errors that the analyses use.

## Main results

* `NLAlib.isRoundingOf_roundNearest`, `NLAlib.isRoundingOf_binaryFloatRound`.
* `NLAlib.FloatMachine.IsAccurate.isHermitian_decodeMatrix_hermFrom`,
  `NLAlib.FloatMachine.IsAccurate.decodeMatrix_negMat`,
  `NLAlib.FloatMachine.IsAccurate.decodeMatrix_conjTransposeMat`,
  `NLAlib.FloatMachine.IsAccurate.decodeMatrix_identityMat`.
* `NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_hermShift_le`,
  `NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_hermScale_le`,
  `NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_hermAvg_le`,
  `NLAlib.FloatMachine.IsAccurate.abs_sum_sub_traceRe_le`.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

/-- **Rounding to nearest is a rounding**: rounding to nearest on the grid of $t$-bit binary
numbers with unbounded exponent (`Real.roundNearest`) returns a rounding of every real $a$ in the
sense of `NLAlib.IsRoundingOf`, with unit roundoff $2^{-t}$, floor $0$ and every range $\Omega$.
It is the rounding of `NLAlib.Computation.gridSem`, which meets the standard-model contract
`NLAlib.Computation.IsRelErrSem`, applied to real and imaginary parts as IEEE complex arithmetic
does. [Higham2002, Theorem 2.2].
Proof: `Real.abs_sub_roundNearest_le` and $\max(\lvert a \rvert, 0) = \lvert a \rvert$. S, about
5 lines. -/
theorem isRoundingOf_roundNearest (t : ℕ) (Ω a : ℝ) :
    IsRoundingOf (2⁻¹ ^ t) 0 Ω a (Real.roundNearest t a) := by
  intro _
  rw [max_eq_left (abs_nonneg a)]
  exact Real.abs_sub_roundNearest_le t a

/-- The local error of binary rounding: at most half the spacing $2^{e}$ of the target exponent
(private helper; the proof of `NLAlib.Computation.local_error`). -/
private theorem local_error_binaryFloatRound (fmt : Float.Model.Format) {r : ℝ → ℤ}
    (hr : ∀ x, Computation.AbsRelErr 0 (1 / 2) x (r x : ℝ)) (x : ℝ) :
    |x - Computation.binaryFloatRound fmt r x| ≤
      (1 / 2 : ℝ) * 2 ^ fmt.targetExponent (Int.log 2 |x| + 1) := by
  set e := fmt.targetExponent (Int.log 2 |x| + 1)
  have he : (0 : ℝ) < 2 ^ e := zpow_pos two_pos _
  have hq : |x / (2 : ℝ) ^ e - (r (x / (2 : ℝ) ^ e) : ℝ)| ≤ 1 / 2 := by
    simpa only [Computation.AbsRelErr, zero_mul, zero_add] using hr (x / (2 : ℝ) ^ e)
  have heq : x - Computation.binaryFloatRound fmt r x =
      (x / (2 : ℝ) ^ e - (r (x / (2 : ℝ) ^ e) : ℝ)) * 2 ^ e := by
    dsimp only [Computation.binaryFloatRound, e]
    field_simp
  rw [heq, abs_mul, abs_of_pos he]
  exact mul_le_mul_of_nonneg_right hq he.le

/-- **Bounded-format rounding is a rounding with floor**: rounding to the binary format `fmt`
with gradual underflow (`NLAlib.Computation.binaryFloatRound`, any nearest tie rule) returns a
rounding of every real $a$ in the sense of `NLAlib.IsRoundingOf` with unit roundoff $2^{-p}$,
floor $\tau = 2^{e_{\min} + p - 1}$ (the smallest normal number) and range the largest finite
number, $p$ the precision and $e_{\min}$ the smallest exponent. In the normal range the error is
relative; below it, half the subnormal spacing, $2^{e_{\min}}/2 = 2^{-p}\tau$, so no factor is
lost against the mixed form `NLAlib.Computation.AbsRelErr`. [Higham2002, §2.2], with gradual
underflow.
Proof: if $\lvert a\rvert \ge \tau$, `NLAlib.Computation.relErr_binaryFloatRound_of_minExponent_le`
(the normal condition is $e_{\min} \le \lfloor\log_2\lvert a\rvert\rfloor + 1 - p$, from
`Int.zpow_le_iff_le_log`-type bounds); otherwise
`NLAlib.Computation.absRelErr_binaryFloatRound` gives $u\lvert a\rvert + 2^{e_{\min}}/2$, and the
subnormal branch needs only half the subnormal spacing, $2^{e_{\min}}/2 = u\tau$ (main's
private lemma local_error; re-derive, about 10 lines). M, about 35
lines. -/
theorem isRoundingOf_binaryFloatRound (fmt : Float.Model.Format) {r : ℝ → ℤ}
    (hr : ∀ x, Computation.AbsRelErr 0 (1 / 2) x (r x : ℝ)) (a : ℝ) :
    IsRoundingOf ((2 : ℝ)⁻¹ ^ fmt.mantissaBits)
      ((2 : ℝ) ^ (fmt.minExponent + fmt.mantissaBits - 1)) fmt.maxFinite a
      (Computation.binaryFloatRound fmt r a) := by
  intro _
  have hut : (2 : ℝ)⁻¹ ^ fmt.mantissaBits * (2 : ℝ) ^ (fmt.minExponent + fmt.mantissaBits - 1) =
      1 / 2 * (2 : ℝ) ^ fmt.minExponent := by
    rw [zpow_sub₀ two_ne_zero, zpow_add₀ two_ne_zero, zpow_natCast, zpow_one, inv_pow]
    field_simp
  rcases eq_or_ne a 0 with rfl | ha
  · rw [Computation.binaryFloatRound_zero fmt hr]
    simp
  rcases le_total ((2 : ℝ) ^ (fmt.minExponent + fmt.mantissaBits - 1)) |a| with h | h
  · obtain ⟨δ, hδ, hz⟩ := Computation.relErr_binaryFloatRound_of_minExponent_le fmt hr a
      (by
        have := (Int.zpow_le_iff_le_log one_lt_two (abs_pos.2 ha)).1 h
        omega)
    rw [max_eq_left h, hz, show a - a * (1 + δ) = -(a * δ) by ring, abs_neg, abs_mul,
      mul_comm]
    exact mul_le_mul_of_nonneg_right hδ (abs_nonneg a)
  · rw [max_eq_right h]
    have hlog : (2 : ℝ) ^ Int.log 2 |a| ≤ |a| := by
      exact_mod_cast Int.zpow_log_le_self (b := 2) one_lt_two (abs_pos.mpr ha)
    have hL : Int.log 2 |a| ≤ fmt.minExponent + fmt.mantissaBits - 1 :=
      (zpow_le_zpow_iff_right₀ one_lt_two).1 (hlog.trans h)
    have he : fmt.targetExponent (Int.log 2 |a| + 1) = fmt.minExponent := by
      apply max_eq_right
      omega
    have herr := local_error_binaryFloatRound fmt hr a
    rw [he] at herr
    rw [← hut] at herr
    rw [mul_comm] at hut
    linarith

namespace FloatMachine.IsAccurate

variable {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}

/-- A matrix built by `NLAlib.FloatMachine.hermFrom` decodes to a Hermitian matrix, under the
contract `NLAlib.FloatMachine.IsAccurate` (zero and negation exact).
Proof: `Matrix.IsHermitian.ext`; unfold `NLAlib.FloatMachine.hermFrom`, `NLAlib.decodeMatrix`,
`NLAlib.decodeComplex`, split by `lt_trichotomy`, and use `dec_zero`, `dec_neg`. S, about 15
lines. -/
theorem isHermitian_decodeMatrix_hermFrom (hM : M.IsAccurate dec u τ Ω μM μQ cN) {k : ℕ}
    (up : Fin k → Fin k → F × F) (dg : Fin k → F) :
    (decodeMatrix dec (M.hermFrom up dg)).IsHermitian := by
  sorry

/-- Entrywise negation is exact: the decoding of `NLAlib.FloatMachine.negMat` $\mathbf{X}$ is
$-\bar{\mathbf{X}}$.
Proof: `Matrix.ext`, `dec_neg`, `Complex.ext`. S, about 5 lines. -/
theorem decodeMatrix_negMat (hM : M.IsAccurate dec u τ Ω μM μQ cN) {m n : Type*}
    (X : Matrix m n (F × F)) : decodeMatrix dec (M.negMat X) = -decodeMatrix dec X := by
  sorry

/-- The stored conjugate transpose is exact: the decoding of
`NLAlib.FloatMachine.conjTransposeMat` $\mathbf{X}$ is $\bar{\mathbf{X}}^{\mathsf{H}}$.
Proof: `Matrix.ext`, `dec_neg`, `Complex.ext`, `Complex.conj_re`, `Complex.conj_im`. S, about
6 lines. -/
theorem decodeMatrix_conjTransposeMat (hM : M.IsAccurate dec u τ Ω μM μQ cN) {m n : Type*}
    (X : Matrix m n (F × F)) :
    decodeMatrix dec (M.conjTransposeMat X) = (decodeMatrix dec X)ᴴ := by
  sorry

/-- The stored identity decodes to the identity.
Proof: `Matrix.ext`, `dec_one`, `dec_zero`, `Matrix.one_apply`. S, about 5 lines. -/
theorem decodeMatrix_identityMat (hM : M.IsAccurate dec u τ Ω μM μQ cN) (k : ℕ) :
    decodeMatrix dec (M.identityMat k) = 1 := by
  sorry

/-- **Error of the stored shift**: under `NLAlib.FloatMachine.IsAccurate` with $u \ge 0$, for a
stored $\mathbf{X}$ with Hermitian decoding $\bar{\mathbf{X}}$ and a stored $c$ with
$\|\bar{\mathbf{X}} - \bar c\mathbf{I}\|_2 \le \Omega$,
$$\|(\bar{\mathbf{X}} - \bar c\mathbf{I}) - \overline{\mathrm{hermShift}(\mathbf{X}, c)}\|_2 \le
u\max(\|\bar{\mathbf{X}} - \bar c\mathbf{I}\|_2, \tau) \,.$$
The error is diagonal, so its norm is its largest entry, as [Shah2024, proof of Lemma 2.1]
notes; the mirrored entries are exact because $\bar{\mathbf{X}}$ is Hermitian.
Proof: the difference is `Matrix.diagonal` of the diagonal errors of `sub` (the diagonal of
$\bar{\mathbf{X}}$ is real), each a rounding of an entry of modulus at most the norm
(`NLAlib.norm_apply_le_specNorm`); `NLAlib.specNorm_diagonal_le`. M, about 30 lines. -/
theorem specNorm_sub_decodeMatrix_hermShift_le (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hu : 0 ≤ u) {k : ℕ} {X : Matrix (Fin k) (Fin k) (F × F)}
    (hX : (decodeMatrix dec X).IsHermitian) (c : F)
    (hΩ : specNorm (decodeMatrix dec X - dec c • (1 : Matrix (Fin k) (Fin k) ℂ)) ≤ Ω) :
    specNorm ((decodeMatrix dec X - dec c • (1 : Matrix (Fin k) (Fin k) ℂ)) -
      decodeMatrix dec (M.hermShift X c)) ≤
        u * max (specNorm (decodeMatrix dec X - dec c • (1 : Matrix (Fin k) (Fin k) ℂ))) τ := by
  sorry

/-- **Error of the stored division by a scalar**: under `NLAlib.FloatMachine.IsAccurate` with
$u, \tau \ge 0$, for a stored $\mathbf{X}$ with Hermitian decoding and a stored $c$ with
$\bar c \ne 0$ and $\|\bar{\mathbf{X}}\|_2/\lvert\bar c\rvert \le \Omega$, with
$\mathbf{Z} = \bar{\mathbf{X}}/\bar c$,
$$\|\mathbf{Z} - \overline{\mathrm{hermScale}(\mathbf{X}, c)}\|_2 \le
u\bigl(\sqrt k\,\|\mathbf{Z}\|_2 + 2k\tau\bigr) \,.$$
Proof: each part errs by $u\max(\lvert\cdot\rvert, \tau)$ (`div`), so each entry by
$u\sqrt{\lvert z \rvert^2 + 2\tau^2} \le u(\lvert z \rvert + 2\tau)$ (compare squares; the route
through $\lvert \operatorname{Re} \rvert + \lvert \operatorname{Im} \rvert$ loses $\sqrt2$); the
mirrored entries are conjugates; sum in Frobenius norm (`NLAlib.specNorm_le_frobNorm`, triangle
inequality, `NLAlib.frobNorm_le_sqrt_card_mul_specNorm`, `NLAlib.norm_apply_le_specNorm`). M,
about 50 lines. -/
theorem specNorm_sub_decodeMatrix_hermScale_le (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hu : 0 ≤ u) (hτ : 0 ≤ τ) {k : ℕ} {X : Matrix (Fin k) (Fin k) (F × F)}
    (hX : (decodeMatrix dec X).IsHermitian) {c : F} (hc : dec c ≠ 0)
    (hΩ : specNorm (decodeMatrix dec X) / |dec c| ≤ Ω) :
    specNorm ((dec c)⁻¹ • decodeMatrix dec X - decodeMatrix dec (M.hermScale X c)) ≤
      u * (√(k : ℝ) * specNorm ((dec c)⁻¹ • decodeMatrix dec X) + 2 * k * τ) := by
  sorry

/-- **Error of the stored scaled Hermitian part**: under `NLAlib.FloatMachine.IsAccurate` with
$0 \le u \le 1/2$, $\tau \ge 0$, for a stored $\mathbf{X}$ and a stored $c$ with
$\lvert \bar c \rvert \ge 1$ and $3\|\bar{\mathbf{X}}\|_2 + \tau \le \Omega$, with
$\mathbf{Z} = (\bar{\mathbf{X}} + \bar{\mathbf{X}}^{\mathsf{H}})/\bar c$,
$$\|\mathbf{Z} - \overline{\mathrm{hermAvg}(\mathbf{X}, c)}\|_2 \le
3u\bigl(\sqrt k\,\|\mathbf{Z}\|_2 + 2k\tau\bigr) \,.$$
Proof: per part, the sum errs by $u(\lvert s \rvert + \tau)$ and the division by
$u(\lvert \tilde s/c \rvert + \tau)$; with $\lvert c \rvert \ge 1$ the total is at most
$u(2 + u)(\lvert s/c \rvert + \tau) \le \tfrac52u(\lvert s/c \rvert + \tau)$; then as
`NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_hermScale_le`. M, about 60 lines. -/
theorem specNorm_sub_decodeMatrix_hermAvg_le (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hu : 0 ≤ u) (hu₁ : u ≤ 1 / 2) (hτ : 0 ≤ τ) {k : ℕ} (X : Matrix (Fin k) (Fin k) (F × F))
    {c : F} (hc : 1 ≤ |dec c|) (hΩ : 3 * specNorm (decodeMatrix dec X) + τ ≤ Ω) :
    specNorm ((dec c)⁻¹ • (decodeMatrix dec X + (decodeMatrix dec X)ᴴ) -
      decodeMatrix dec (M.hermAvg X c)) ≤
        3 * u * (√(k : ℝ) * specNorm ((dec c)⁻¹ • (decodeMatrix dec X + (decodeMatrix dec X)ᴴ)) +
          2 * k * τ) := by
  sorry

/-- **Error of the rounded trace**: under `NLAlib.FloatMachine.IsAccurate` with $u, \tau \ge 0$
and $ku \le 1/2$, for a stored $k \times k$ $\mathbf{X}$ with real parts of the diagonal
$x_i$ and $2(\sum_i \lvert x_i \rvert + k\tau) \le \Omega$,
$$\Bigl\lvert \sum_i x_i - \overline{\mathrm{traceRe}(\mathbf{X})} \Bigr\rvert \le
2ku\Bigl(\sum_i \lvert x_i \rvert + k\tau\Bigr) \,.$$
[Higham2002, (4.4)], there with $\gamma_{k-1}$ and $\tau = 0$.
Proof: induction over `List.finRange` with the invariant $E_i \le ((1 + u)^i - 1)(S + \tau)$
(`add` errs by $u(\lvert \hat s_i + x_i \rvert + \tau)$, partial sums below $2(S + k\tau)$),
then $(1 + u)^k - 1 \le 2ku$ for $ku \le 1/2$ (`Real.add_one_le_exp`). M, about 50 lines. -/
theorem abs_sum_sub_traceRe_le (hM : M.IsAccurate dec u τ Ω μM μQ cN) (hu : 0 ≤ u)
    (hτ : 0 ≤ τ) {k : ℕ} (hku : k * u ≤ 1 / 2) (X : Matrix (Fin k) (Fin k) (F × F))
    (hΩ : 2 * (∑ i, |dec (X i i).1| + k * τ) ≤ Ω) :
    |∑ i, dec (X i i).1 - dec (M.traceRe X)| ≤ 2 * k * u * (∑ i, |dec (X i i).1| + k * τ) := by
  sorry

end FloatMachine.IsAccurate

end NLAlib
