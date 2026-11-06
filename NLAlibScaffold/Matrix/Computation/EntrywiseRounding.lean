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
  refine Matrix.IsHermitian.ext fun i j => ?_
  unfold FloatMachine.hermFrom decodeMatrix decodeComplex
  rcases lt_trichotomy i j with h | rfl | h
  · have h' : ¬ j < i := not_lt.2 h.le
    simp [h, h', hM.dec_neg]
    all_goals apply Complex.ext <;> simp [hM.dec_neg]
  · simp [hM.dec_zero]
    all_goals apply Complex.ext <;> simp [hM.dec_zero]
  · have h' : ¬ i < j := not_lt.2 h.le
    simp [h, h', hM.dec_neg]
    all_goals apply Complex.ext <;> simp [hM.dec_neg]

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
  ext i j : 2
  simp [decodeMatrix, FloatMachine.conjTransposeMat, decodeComplex, hM.dec_neg]
  all_goals apply Complex.ext <;> simp [hM.dec_neg]

/-- The stored identity decodes to the identity.
Proof: `Matrix.ext`, `dec_one`, `dec_zero`, `Matrix.one_apply`. S, about 5 lines. -/
theorem decodeMatrix_identityMat (hM : M.IsAccurate dec u τ Ω μM μQ cN) (k : ℕ) :
    decodeMatrix dec (M.identityMat k) = 1 := by
  ext i j : 2
  by_cases h : i = j
  · subst h
    simp [decodeMatrix, FloatMachine.identityMat, decodeComplex, hM.dec_one, hM.dec_zero]
    all_goals apply Complex.ext <;> simp [hM.dec_one, hM.dec_zero]
  · simp [decodeMatrix, FloatMachine.identityMat, decodeComplex, hM.dec_zero, h]
    all_goals apply Complex.ext <;> simp [hM.dec_zero]

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
  set D := decodeMatrix dec X - dec c • (1 : Matrix (Fin k) (Fin k) ℂ) with hD
  have hS := specNorm_nonneg D
  have hre : ∀ i, (D i i).re = dec (X i i).1 - dec c := by
    intro i
    simp [hD, Matrix.one_apply, decodeMatrix, decodeComplex, Complex.real_smul]
  have hE : D - decodeMatrix dec (M.hermShift X c) =
      Matrix.diagonal fun i => (((dec (X i i).1 - dec c) - dec (M.sub (X i i).1 c) : ℝ) : ℂ) := by
    ext i j
    rcases eq_or_ne i j with rfl | hij
    · have hi : dec (X i i).2 = 0 := by
        have h := congrArg Complex.im (hX.apply i i)
        simp [decodeMatrix, decodeComplex] at h
        linarith
      apply Complex.ext <;> simp [hD, decodeMatrix, FloatMachine.hermShift,
        FloatMachine.hermFrom, decodeComplex, Matrix.one_apply, hM.dec_zero, hi]
    · rcases lt_or_gt_of_ne hij with h | h
      · simp [hD, decodeMatrix, FloatMachine.hermShift, FloatMachine.hermFrom,
          decodeComplex, Matrix.one_apply, hij, h]
      · have h' : ¬ i < j := not_lt.2 h.le
        have h2 := congrArg Complex.re (hX.apply i j)
        have h3 := congrArg Complex.im (hX.apply i j)
        simp [decodeMatrix, decodeComplex] at h2 h3
        simp [hD, decodeMatrix, FloatMachine.hermShift, FloatMachine.hermFrom,
          decodeComplex, Matrix.one_apply, hij, h', h, hM.dec_neg]
        apply Complex.ext <;> simp <;> linarith
  rw [hE]
  refine specNorm_diagonal_le (mul_nonneg hu (le_max_of_le_left hS)) fun i => ?_
  have ha : |dec (X i i).1 - dec c| ≤ specNorm D := by
    rw [← hre i]
    exact (Complex.abs_re_le_norm _).trans (norm_apply_le_specNorm D i i)
  have h2 := hM.sub (X i i).1 c (ha.trans hΩ)
  rw [Complex.norm_real, Real.norm_eq_abs]
  refine h2.trans (mul_le_mul_of_nonneg_left (max_le_max ha le_rfl) hu)

/-- Entrywise moduli are dominated in Frobenius norm (private helper). -/
private theorem frobNorm_le_of_norm_le_entries {m n : Type*} [Fintype m] [Fintype n]
    {A B : Matrix m n ℂ} (h : ∀ i j, ‖A i j‖ ≤ ‖B i j‖) : frobNorm A ≤ frobNorm B := by
  unfold frobNorm
  exact Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
    pow_le_pow_left₀ (norm_nonneg _) (h i j) 2)

/-- Entrywise bound on the real and imaginary errors gives the modulus bound with the factor
$\sqrt{\lvert z \rvert^2 + 2\tau^2} \le \lvert z \rvert + 2\tau$ (private helper). -/
private theorem norm_entry_le_of_errors (u τ p q e₁ e₂ : ℝ) (hu : 0 ≤ u) (hτ : 0 ≤ τ)
    (h₁ : |e₁| ≤ u * max |p| τ) (h₂ : |e₂| ≤ u * max |q| τ) :
    √(e₁ ^ 2 + e₂ ^ 2) ≤ u * (√(p ^ 2 + q ^ 2) + 2 * τ) := by
  have hmax : ∀ x : ℝ, max |x| τ ^ 2 ≤ x ^ 2 + τ ^ 2 := fun x => by
    rcases le_total |x| τ with h | h
    · rw [max_eq_right h]; nlinarith [sq_abs x]
    · rw [max_eq_left h]; nlinarith [sq_abs x]
  have hsq : ∀ e p : ℝ, |e| ≤ u * max |p| τ → e ^ 2 ≤ u ^ 2 * (p ^ 2 + τ ^ 2) := by
    intro e p h
    calc e ^ 2 = |e| ^ 2 := (sq_abs e).symm
      _ ≤ (u * max |p| τ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = u ^ 2 * (max |p| τ) ^ 2 := by ring
      _ ≤ u ^ 2 * (p ^ 2 + τ ^ 2) := mul_le_mul_of_nonneg_left (hmax p) (sq_nonneg u)
  have hr := Real.sq_sqrt (add_nonneg (sq_nonneg p) (sq_nonneg q))
  have hr' : u ^ 2 * √(p ^ 2 + q ^ 2) ^ 2 = u ^ 2 * (p ^ 2 + q ^ 2) := by rw [hr]
  have hr0 := Real.sqrt_nonneg (p ^ 2 + q ^ 2)
  have hkey : e₁ ^ 2 + e₂ ^ 2 ≤ (u * (√(p ^ 2 + q ^ 2) + 2 * τ)) ^ 2 := by
    have := hsq e₁ p h₁
    have := hsq e₂ q h₂
    nlinarith [mul_nonneg (sq_nonneg u) (mul_nonneg hr0 hτ), mul_nonneg (sq_nonneg u) (sq_nonneg τ)]
  calc √(e₁ ^ 2 + e₂ ^ 2) ≤ √((u * (√(p ^ 2 + q ^ 2) + 2 * τ)) ^ 2) := Real.sqrt_le_sqrt hkey
    _ = u * (√(p ^ 2 + q ^ 2) + 2 * τ) := Real.sqrt_sq (mul_nonneg hu (by positivity))

/-- A complex entry error with bounded real and imaginary parts has modulus at most
$u(\lvert z\rvert + 2\tau)$ (private helper). -/
private theorem norm_sub_le_of_re_im (z w : ℂ) {u τ : ℝ} (hu : 0 ≤ u) (hτ : 0 ≤ τ)
    (h₁ : |(z - w).re| ≤ u * max |z.re| τ) (h₂ : |(z - w).im| ≤ u * max |z.im| τ) :
    ‖z - w‖ ≤ u * (‖z‖ + 2 * τ) := by
  have := norm_entry_le_of_errors u τ z.re z.im (z - w).re (z - w).im hu hτ h₁ h₂
  simpa [Complex.norm_def, Complex.normSq_apply, sq] using this

/-- A square-matrix bound from entrywise moduli: the spectral norm is at most
$u(\sqrt k\,\|\mathbf{Z}\|_2 + 2k\tau)$ (private helper, via the Frobenius norm). -/
private theorem specNorm_le_of_norm_entry_le {k : ℕ} (Z E : Matrix (Fin k) (Fin k) ℂ) {u τ : ℝ}
    (hu : 0 ≤ u) (hτ : 0 ≤ τ) (h : ∀ i j, ‖E i j‖ ≤ u * (‖Z i j‖ + 2 * τ)) :
    specNorm E ≤ u * (√(k : ℝ) * specNorm Z + 2 * k * τ) := by
  have hW : frobNorm (Matrix.of fun i j => ((‖Z i j‖ : ℝ) : ℂ)) = frobNorm Z := by
    unfold frobNorm; simp
  have hJ : frobNorm (Matrix.of fun (_ _ : Fin k) => (1 : ℂ)) = k := by
    have h2 : frobNorm (Matrix.of fun (_ _ : Fin k) => (1 : ℂ)) ^ 2 = (k : ℝ) ^ 2 := by
      rw [frobNorm_sq_eq_sum]; simp; ring
    exact (pow_left_inj₀ (frobNorm_nonneg _) (Nat.cast_nonneg _) two_ne_zero).1 h2
  have hE : frobNorm E ≤ u * frobNorm Z + 2 * u * τ * k := by
    calc frobNorm E ≤ frobNorm (u • (Matrix.of fun i j => ((‖Z i j‖ : ℝ) : ℂ)) +
          (2 * u * τ) • (Matrix.of fun (_ _ : Fin k) => (1 : ℂ))) := by
          refine frobNorm_le_of_norm_le_entries fun i j => ?_
          have hc : (u • (Matrix.of fun i j => ((‖Z i j‖ : ℝ) : ℂ)) +
              (2 * u * τ) • (Matrix.of fun (_ _ : Fin k) => (1 : ℂ))) i j =
              (((u * ‖Z i j‖ + 2 * u * τ : ℝ)) : ℂ) := by
            simp
          rw [hc, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
          nlinarith [h i j]
      _ ≤ frobNorm (u • (Matrix.of fun i j => ((‖Z i j‖ : ℝ) : ℂ))) +
          frobNorm ((2 * u * τ) • (Matrix.of fun (_ _ : Fin k) => (1 : ℂ))) :=
          frobNorm_add_le _ _
      _ = u * frobNorm Z + 2 * u * τ * k := by
          rw [frobNorm_real_smul, frobNorm_real_smul, hW, hJ, abs_of_nonneg hu,
            abs_of_nonneg (by positivity)]
  have hZ := frobNorm_le_sqrt_card_mul_specNorm Z
  rw [Fintype.card_fin] at hZ
  calc specNorm E ≤ frobNorm E := specNorm_le_frobNorm E
    _ ≤ u * frobNorm Z + 2 * u * τ * k := hE
    _ ≤ u * (√(k : ℝ) * specNorm Z + 2 * k * τ) := by
        nlinarith [mul_le_mul_of_nonneg_left hZ hu]

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
  have hdiag : ∀ i, dec (X i i).2 = 0 := fun i => by
    have h := congrArg Complex.im (hX.apply i i)
    simp [decodeMatrix, decodeComplex] at h
    linarith
  have hbound : ∀ i j, |dec (X i j).1 / dec c| ≤ Ω ∧ |dec (X i j).2 / dec c| ≤ Ω := by
    intro i j
    have hS' : specNorm (decodeMatrix dec X) ≤ Ω * |dec c| := (div_le_iff₀ (abs_pos.2 hc)).1 hΩ
    have h1 : |dec (X i j).1| ≤ specNorm (decodeMatrix dec X) :=
      (Complex.abs_re_le_norm (decodeMatrix dec X i j)).trans
        (norm_apply_le_specNorm (decodeMatrix dec X) i j)
    have h2 : |dec (X i j).2| ≤ specNorm (decodeMatrix dec X) :=
      (Complex.abs_im_le_norm (decodeMatrix dec X i j)).trans
        (norm_apply_le_specNorm (decodeMatrix dec X) i j)
    constructor <;> rw [abs_div, div_le_iff₀ (abs_pos.2 hc)] <;> linarith
  set Z : Matrix (Fin k) (Fin k) ℂ := (dec c)⁻¹ • decodeMatrix dec X with hZdef
  set E : Matrix (Fin k) (Fin k) ℂ := Z - decodeMatrix dec (M.hermScale X c) with hEdef
  have hZre : ∀ i j, (Z i j).re = dec (X i j).1 / dec c := fun i j => by
    rw [hZdef, Matrix.smul_apply, Complex.smul_re, smul_eq_mul, div_eq_inv_mul]; rfl
  have hZim : ∀ i j, (Z i j).im = dec (X i j).2 / dec c := fun i j => by
    rw [hZdef, Matrix.smul_apply, Complex.smul_im, smul_eq_mul, div_eq_inv_mul]; rfl
  have hWre : ∀ i j, i ≤ j →
      (decodeMatrix dec (M.hermScale X c) i j).re = dec (M.div (X i j).1 c) := by
    intro i j h
    rcases eq_or_lt_of_le h with rfl | hlt
    · simp [FloatMachine.hermScale, FloatMachine.hermFrom, decodeMatrix, decodeComplex]
    · simp [FloatMachine.hermScale, FloatMachine.hermFrom, decodeMatrix, decodeComplex, hlt]
  have hWim : ∀ i j, i < j →
      (decodeMatrix dec (M.hermScale X c) i j).im = dec (M.div (X i j).2 c) := by
    intro i j hlt
    simp [FloatMachine.hermScale, FloatMachine.hermFrom, decodeMatrix, decodeComplex, hlt]
  have hWim_diag : ∀ i, (decodeMatrix dec (M.hermScale X c) i i).im = 0 := fun i => by
    simp [FloatMachine.hermScale, FloatMachine.hermFrom, decodeMatrix, decodeComplex, hM.dec_zero]
  have hE_le : ∀ i j, i ≤ j → ‖E i j‖ ≤ u * (‖Z i j‖ + 2 * τ) := by
    intro i j hij
    refine norm_sub_le_of_re_im (Z i j) (decodeMatrix dec (M.hermScale X c) i j) hu hτ ?_ ?_
    · rw [Complex.sub_re, hZre, hWre i j hij]
      exact (hM.div (X i j).1 c hc) (hbound i j).1
    · rcases eq_or_lt_of_le hij with rfl | hlt
      · rw [Complex.sub_im, hWim_diag, sub_zero, hZim, hdiag i, zero_div, abs_zero]
        exact mul_nonneg hu (le_max_of_le_right hτ)
      · rw [Complex.sub_im, hZim, hWim i j hlt]
        exact (hM.div (X i j).2 c hc) (hbound i j).2
  have hEH : (decodeMatrix dec (M.hermScale X c)).IsHermitian :=
    isHermitian_decodeMatrix_hermFrom hM (fun i j => (M.div (X i j).1 c, M.div (X i j).2 c))
      (fun i => M.div (X i i).1 c)
  have hZH : Z.IsHermitian := by
    rw [hZdef]
    exact hX.smul (star_trivial _)
  have hE_all : ∀ i j, ‖E i j‖ ≤ u * (‖Z i j‖ + 2 * τ) := by
    intro i j
    rcases le_total i j with h | h
    · exact hE_le i j h
    · have hEH' : E.IsHermitian := hZH.sub hEH
      have hEsym : ‖E i j‖ = ‖E j i‖ := by
        rw [← hEH'.apply i j, norm_star]
      have hZsym : ‖Z i j‖ = ‖Z j i‖ := by
        rw [← hZH.apply i j, norm_star]
      rw [hEsym, hZsym]
      exact hE_le j i h
  exact specNorm_le_of_norm_entry_le Z E hu hτ hE_all

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
