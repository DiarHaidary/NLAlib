/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.BinaryFloatMachine
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# A floating-point machine on the grid with unbounded exponent

`NLAlib.gridMachine t` is a `NLAlib.FloatMachine` on stored reals that **decodes a word by
rounding it to nearest onto the $t$-bit grid with unbounded exponent** (`Real.roundNearest t`),
as `NLAlib.Computation.gridSem` does, and rounds every result to that grid: the scalar
operations round the exact result on the decoded operands, the uniform sampler clamps the rounded
$\bar s v$ to $[-\bar s, \bar s]$, the normal sampler rounds both parts, and the two black boxes
`NLAlib.gridMM t`, `NLAlib.gridQR t` compute the exact product (an exact QR factorization, chosen)
of the decoded inputs and round each entry, real and imaginary parts separately, with the odd
rounding `NLAlib.gridRoundOdd` (so that the rounded $\mathbf{A}\mathbf{A}^{\mathsf{H}}$ is exactly
Hermitian: `Real.roundNearest` rounds ties upward and is not odd). It meets the contract
`NLAlib.FloatMachine.IsAccurate` at the decoding `Real.roundNearest t`, with $u = 2^{-t}$, floor
$\tau = 0$, every range $\Omega$, $\mu_{\mathrm{MM}}(d) = \mu_{\mathrm{QR}}(d) = 2d$ and
$c_{\mathrm N} = \sqrt2$, for $t \ge 1$: the companion, on the decoding of the grid semantics, of
`NLAlib.binaryFloatMachine` (bounded exponent, floor $\tau > 0$), which cannot meet a contract
at floor $0$.

The file also gives the parts of a rounded witness on the grid: rounding to nearest does not
leave the modulus of a grid point (`NLAlib.abs_roundNearest_le_of_mem_floatGrid`), and rounding
the tape meets `NLAlib.Computation.IsTapeRounding` with countable range and measurable fibres.

## Main definitions

* `NLAlib.gridRoundOdd`: odd rounding to nearest onto the grid.
* `NLAlib.gridMM`, `NLAlib.gridQR`: the correctly rounded black boxes on stored pairs.
* `NLAlib.gridMachine`: the machine.

## Main results

* `NLAlib.isMatMulErr_gridMM`, `NLAlib.isQRErr_gridQR`, `NLAlib.isAccurate_gridMachine`: the
  contracts.
* `NLAlib.abs_roundNearest_le_of_mem_floatGrid`.
* `NLAlib.isTapeRounding_roundNearest`, `NLAlib.countable_range_roundNearest`,
  `NLAlib.measurable_roundNearest`: rounding the tape.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

namespace NLAlib

/-! ### Rounding onto the grid -/

/-- **Odd rounding to nearest** onto the $t$-bit grid with unbounded exponent: $\mathrm{fl}(x)$
for $x \ge 0$ and $-\mathrm{fl}(-x)$ below, `Real.roundNearest` with ties away from zero. -/
noncomputable def gridRoundOdd (t : ℕ) (x : ℝ) : ℝ :=
  if 0 ≤ x then Real.roundNearest t x else -Real.roundNearest t (-x)

/-- Rounding fixes zero. No printed source. -/
theorem roundNearest_zero (t : ℕ) : Real.roundNearest t 0 = 0 := by
  simp [Real.roundNearest]

/-- One is on the grid of $t \ge 1$ bits, so rounding fixes it. No printed source. -/
theorem roundNearest_one {t : ℕ} (ht : 0 < t) : Real.roundNearest t 1 = 1 :=
  Real.roundNearest_eq_self_of_mem_floatGrid
    ⟨1, 0, by simpa using one_lt_pow₀ (one_lt_two (α := ℤ)) ht.ne', by simp⟩

/-- A power $2^{-k}$ is on the grid of $t \ge 1$ bits, so rounding fixes it.
No printed source. -/
theorem roundNearest_two_inv_pow {t : ℕ} (ht : 0 < t) (k : ℕ) :
    Real.roundNearest t (2⁻¹ ^ k) = 2⁻¹ ^ k :=
  Real.roundNearest_eq_self_of_mem_floatGrid
    ⟨1, -k, by simpa using one_lt_pow₀ (one_lt_two (α := ℤ)) ht.ne', by simp [zpow_neg]⟩

/-- Odd rounding is odd: $\mathrm{fl}_{\mathrm{odd}}(-x) = -\mathrm{fl}_{\mathrm{odd}}(x)$.
No printed source. -/
theorem gridRoundOdd_neg (t : ℕ) (x : ℝ) : gridRoundOdd t (-x) = -gridRoundOdd t x := by
  unfold gridRoundOdd
  rcases lt_trichotomy x 0 with h | rfl | h
  · rw [if_pos (by linarith), if_neg (by linarith), neg_neg]
  · simp [roundNearest_zero]
  · rw [if_neg (by linarith), if_pos h.le, neg_neg]

/-- Odd rounding has relative error at most $2^{-t}$. No printed source. -/
theorem abs_sub_gridRoundOdd_le (t : ℕ) (x : ℝ) :
    |x - gridRoundOdd t x| ≤ 2⁻¹ ^ t * |x| := by
  unfold gridRoundOdd
  split_ifs with h
  · exact Real.abs_sub_roundNearest_le t x
  · have e := Real.abs_sub_roundNearest_le t (-x)
    rw [abs_neg] at e
    rwa [sub_neg_eq_add, ← abs_neg, neg_add, ← sub_eq_add_neg]

/-- Odd rounding lands on the grid, for $t \ge 1$. No printed source. -/
theorem gridRoundOdd_mem_floatGrid {t : ℕ} (ht : 0 < t) (x : ℝ) :
    gridRoundOdd t x ∈ Real.floatGrid t := by
  unfold gridRoundOdd
  split_ifs
  · exact Real.roundNearest_mem_floatGrid ht x
  · exact Real.neg_mem_floatGrid (Real.roundNearest_mem_floatGrid ht _)

/-- **Rounding to nearest does not leave the modulus of a grid point**: if $\beta$ is on the
$t$-bit grid and $\lvert a \rvert \le \lvert \beta \rvert$, then
$\lvert \mathrm{fl}(a) \rvert \le \lvert \beta \rvert$. No printed source.
Proof: in the binade of $\beta$ the rounding step is the one of $\beta$, a multiple of it, and
`round` is monotone; below it, $\lvert\mathrm{fl}(a)\rvert$ is at most the top of the binade of
$a$. -/
theorem abs_roundNearest_le_of_mem_floatGrid {t : ℕ} {a β : ℝ} (hβ : β ∈ Real.floatGrid t)
    (ha : |a| ≤ |β|) : |Real.roundNearest t a| ≤ |β| := by
  rcases eq_or_ne a 0 with rfl | ha0
  · simp [Real.roundNearest]
  have hapos : 0 < |a| := abs_pos.mpr ha0
  have hβpos : 0 < |β| := hapos.trans_le ha
  have hfix : Real.roundNearest t β = β := Real.roundNearest_eq_self_of_mem_floatGrid hβ
  have hσκ : Int.log 2 |a| ≤ Int.log 2 |β| := Int.log_mono_right hapos ha
  have hκle : (2:ℝ) ^ Int.log 2 |β| ≤ |β| := by
    exact_mod_cast Int.zpow_log_le_self (b := 2) one_lt_two hβpos
  have hσlt : |a| < (2:ℝ) ^ (Int.log 2 |a| + 1) := by
    exact_mod_cast Int.lt_zpow_succ_log_self (b := 2) one_lt_two |a|
  have hmono : ∀ u v : ℝ, u ≤ v → round u ≤ round v := fun u v h => by
    rw [round_eq, round_eq]; exact Int.floor_mono (by linarith)
  rcases eq_or_lt_of_le hσκ with h | h
  · -- same binade as `β`: the rounding step is the one of `β`, which is a multiple of it
    have hfix' := hfix
    rw [Real.roundNearest] at hfix'
    rw [Real.roundNearest, h]
    set e : ℤ := Int.log 2 |β| + 1 - t with he
    have hpos : (0:ℝ) < 2 ^ e := zpow_pos two_pos _
    set N : ℤ := round (β / 2 ^ e) with hN
    have hβN : β = (N:ℝ) * 2 ^ e := hfix'.symm
    have hr : |a / 2 ^ e| ≤ ((|N| : ℤ) : ℝ) := by
      rw [Int.cast_abs, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
      have := ha
      rw [hβN, abs_mul, abs_of_pos hpos] at this
      exact this
    obtain ⟨hl, hu⟩ := abs_le.mp hr
    have h1 := hmono _ _ hl
    have h2 := hmono _ _ hu
    rw [← Int.cast_neg, round_intCast] at h1
    rw [round_intCast] at h2
    have hz : |round (a / 2 ^ e)| ≤ |N| := abs_le.mpr ⟨h1, h2⟩
    have hβabs : |β| = ((|N| : ℤ) : ℝ) * 2 ^ e := by
      rw [hβN, abs_mul, abs_of_pos hpos, Int.cast_abs]
    rw [abs_mul, abs_of_pos hpos, ← Int.cast_abs, hβabs]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hz) hpos.le
  · -- `a` lies in a lower binade: its rounding is at most the top of that binade
    rw [Real.roundNearest]
    set f : ℤ := Int.log 2 |a| + 1 - t with hf
    have hfpos : (0:ℝ) < 2 ^ f := zpow_pos two_pos _
    have hid : (2:ℝ) ^ t * 2 ^ f = 2 ^ (Int.log 2 |a| + 1) := by
      rw [hf, ← zpow_natCast, ← zpow_add₀ two_ne_zero]; congr 1; ring
    have hz : |a / 2 ^ f| ≤ (2:ℝ) ^ t := by
      rw [abs_div, abs_of_pos hfpos, div_le_iff₀ hfpos, hid]; exact hσlt.le
    obtain ⟨hl, hu⟩ := abs_le.mp hz
    have hMr : ((2 ^ t : ℤ) : ℝ) = (2:ℝ) ^ t := by push_cast; rfl
    have h1 := hmono _ _ hl
    have h2 := hmono _ _ hu
    rw [← hMr, ← Int.cast_neg, round_intCast] at h1
    rw [← hMr, round_intCast] at h2
    have hz2 : |round (a / 2 ^ f)| ≤ 2 ^ t := abs_le.mpr ⟨h1, h2⟩
    have hrt : ((|round (a / 2 ^ f)| : ℤ) : ℝ) ≤ (2:ℝ) ^ t := by
      rw [← hMr]; exact_mod_cast hz2
    have hchain : (2:ℝ) ^ (Int.log 2 |a| + 1) ≤ (2:ℝ) ^ Int.log 2 |β| :=
      zpow_le_zpow_right₀ one_le_two (by omega)
    rw [abs_mul, abs_of_pos hfpos, ← Int.cast_abs]
    calc ((|round (a / 2 ^ f)| : ℤ) : ℝ) * 2 ^ f ≤ (2:ℝ) ^ t * 2 ^ f :=
          mul_le_mul_of_nonneg_right hrt hfpos.le
      _ = (2:ℝ) ^ (Int.log 2 |a| + 1) := hid
      _ ≤ (2:ℝ) ^ Int.log 2 |β| := hchain
      _ ≤ |β| := hκle

/-! ### The black boxes -/

/-- A complex number rounded part by part, oddly, onto the grid: a stored pair. -/
noncomputable def gridRoundPair (t : ℕ) (z : ℂ) : ℝ × ℝ :=
  (gridRoundOdd t z.re, gridRoundOdd t z.im)

/-- **The correctly rounded product on the grid**: the exact product of the decoded inputs
(decoding `Real.roundNearest t`), each entry rounded part by part with `NLAlib.gridRoundOdd`. -/
noncomputable def gridMM (t : ℕ) : MatMulMap (ℝ × ℝ) := fun {_ _ _} A B =>
  (A.map (decodeComplex (Real.roundNearest t)) * B.map (decodeComplex (Real.roundNearest t))).map
    (gridRoundPair t)

/-- **The correctly rounded QR factorization on the grid**: an exact QR factorization of the
decoded input (chosen), each entry of both factors rounded part by part with
`NLAlib.gridRoundOdd`. -/
noncomputable def gridQR (t : ℕ) : QRMap (ℝ × ℝ) := fun {_ _} A =>
  ((Classical.choose (exists_hasOrthonormalCols_mul_isUpperTrapezoidal
      (A.map (decodeComplex (Real.roundNearest t))))).map (gridRoundPair t),
    (Classical.choose (Classical.choose_spec (exists_hasOrthonormalCols_mul_isUpperTrapezoidal
      (A.map (decodeComplex (Real.roundNearest t)))))).map (gridRoundPair t))

/-- The decoding of an oddly rounded complex matrix is the odd rounding of its parts: the
rounded values are on the grid, which the decoding fixes. No printed source. -/
theorem map_decodeComplex_map_gridRoundPair {t : ℕ} (ht : 0 < t) {m n : Type*}
    (X : Matrix m n ℂ) :
    (X.map (gridRoundPair t)).map (decodeComplex (Real.roundNearest t)) =
      X.map fun z => (⟨gridRoundOdd t z.re, gridRoundOdd t z.im⟩ : ℂ) := by
  ext i j
  simp [gridRoundPair, decodeComplex,
    Real.roundNearest_eq_self_of_mem_floatGrid (gridRoundOdd_mem_floatGrid ht _)]

/-- Odd rounding in the form of the entrywise bound, floor $0$. -/
private theorem abs_sub_gridRoundOdd_le_mul_max (t : ℕ) (x : ℝ) :
    |x - gridRoundOdd t x| ≤ 2⁻¹ ^ t * max |x| 0 := by
  rw [max_eq_left (abs_nonneg x)]
  exact abs_sub_gridRoundOdd_le t x

/-- **The grid product meets the product contract**: for $t \ge 1$ and every range $\Omega$,
`NLAlib.gridMM t` meets `NLAlib.IsMatMulErr` at the decoding `Real.roundNearest t`, with
$u = 2^{-t}$, floor $0$ and $\mu(d) = 2d$, and computes a product with a conjugate transpose
exactly Hermitian (the odd rounding commutes with conjugation). No printed source. -/
theorem isMatMulErr_gridMM {t : ℕ} (ht : 0 < t) (Ω : ℝ) :
    IsMatMulErr (decodeComplex (Real.roundNearest t)) (2⁻¹ ^ t) 0 Ω (fun d => 2 * d)
      (gridMM t) where
  specNorm_mul_sub_le {l m n} A B _ := by
    rw [gridMM, map_decodeComplex_map_gridRoundPair ht]
    refine (specNorm_sub_map_le (by positivity) le_rfl (abs_sub_gridRoundOdd_le_mul_max t)
      (le_max_left l (max m n)) ((le_max_right m n).trans (le_max_right _ _)) _).trans ?_
    gcongr
    exact specNorm_mul_le _ _
  isHermitian_of_map_eq_conjTranspose {m n} A B hB := by
    rw [gridMM, map_decodeComplex_map_gridRoundPair ht, hB]
    set P := A.map (decodeComplex (Real.roundNearest t)) *
      (A.map (decodeComplex (Real.roundNearest t)))ᴴ
    have hP : P.IsHermitian := Matrix.isHermitian_mul_conjTranspose_self _
    refine Matrix.IsHermitian.ext fun i j => ?_
    have h := hP.apply j i
    have hre : (P j i).re = (P i j).re := by rw [← h, Complex.star_def, Complex.conj_re]
    have him : (P j i).im = -(P i j).im := by rw [← h, Complex.star_def, Complex.conj_im]
    apply Complex.ext
    · simp only [Matrix.map_apply, Complex.star_def, Complex.conj_re, hre]
    · simp only [Matrix.map_apply, Complex.star_def, Complex.conj_im, him, gridRoundOdd_neg,
        neg_neg]

/-- **The grid QR factorization meets the QR contract**: for $t \ge 1$ and every range $\Omega$,
`NLAlib.gridQR t` meets `NLAlib.IsQRErr` at the decoding `Real.roundNearest t`, with $u = 2^{-t}$,
floor $0$ and $\mu(d) = 2d$: the exact unitary factor is the $\mathbf{Q}'$ of the contract.
No printed source. -/
theorem isQRErr_gridQR {t : ℕ} (ht : 0 < t) (Ω : ℝ) :
    IsQRErr (decodeComplex (Real.roundNearest t)) (2⁻¹ ^ t) 0 Ω (fun d => 2 * d) (gridQR t) := by
  intro m n A _
  set D := A.map (decodeComplex (Real.roundNearest t))
  obtain ⟨hQ, hRt, hA⟩ := Classical.choose_spec (Classical.choose_spec
    (exists_hasOrthonormalCols_mul_isUpperTrapezoidal D))
  set Q := Classical.choose (exists_hasOrthonormalCols_mul_isUpperTrapezoidal D)
  set Rm := Classical.choose (Classical.choose_spec
    (exists_hasOrthonormalCols_mul_isUpperTrapezoidal D))
  set F : ℂ → ℂ := fun z => ⟨gridRoundOdd t z.re, gridRoundOdd t z.im⟩
  have h1 : (gridQR t A).1.map (decodeComplex (Real.roundNearest t)) = Q.map F :=
    map_decodeComplex_map_gridRoundPair ht Q
  have h2 : (gridQR t A).2.map (decodeComplex (Real.roundNearest t)) = Rm.map F :=
    map_decodeComplex_map_gridRoundPair ht Rm
  have hu : (0 : ℝ) ≤ 2⁻¹ ^ t := by positivity
  have hround := abs_sub_gridRoundOdd_le_mul_max t
  have hmn := le_max_left m n
  rw [h1, h2]
  refine ⟨fun i j hij => ?_, Q, hQ, ?_, ?_⟩
  · have h0 : gridRoundOdd t 0 = 0 := by simp [gridRoundOdd, roundNearest_zero]
    rw [Matrix.map_apply, hRt i j hij]
    exact Complex.ext h0 h0
  · refine (specNorm_sub_map_le hu le_rfl hround hmn hmn Q).trans ?_
    have : max (specNorm Q) 0 ≤ 1 := max_le hQ.specNorm_le_one zero_le_one
    calc _ ≤ 2 * ((max m n : ℕ) : ℝ) * 2⁻¹ ^ t * 1 := by gcongr
      _ = _ := mul_one _
  · have hR : specNorm Rm = specNorm D := by rw [hA, hQ.specNorm_mul_left]
    have hsub : D - Q * Rm.map F = Q * (Rm - Rm.map F) := by
      conv_lhs => rw [hA]
      rw [Matrix.mul_sub]
    rw [hsub, hQ.specNorm_mul_left, ← hR]
    exact specNorm_sub_map_le hu le_rfl hround hmn (le_max_right m n) Rm

/-! ### The machine -/

/-- The **floating-point machine of the grid** with $t$ bits and unbounded exponent, on stored
reals decoded by $\mathrm{fl}(x)$ (`Real.roundNearest t`): $0$ and $1$, negation (of the decoded
value), comparison and the floor conversion of decoded values are exact; conversion, addition,
subtraction, multiplication and division round the exact result on the decoded operands; the
black boxes are `NLAlib.gridMM t` and `NLAlib.gridQR t`; the uniform sampler clamps the rounded
$\bar s v$ to $[-\bar s, \bar s]$ and the normal sampler rounds both parts. -/
noncomputable def gridMachine (t : ℕ) : FloatMachine ℝ ℝ ℂ where
  zero := 0
  one := 1
  ofNat k := Real.roundNearest t k
  add x y := Real.roundNearest t (Real.roundNearest t x + Real.roundNearest t y)
  sub x y := Real.roundNearest t (Real.roundNearest t x - Real.roundNearest t y)
  mul x y := Real.roundNearest t (Real.roundNearest t x * Real.roundNearest t y)
  div x y := Real.roundNearest t (Real.roundNearest t x / Real.roundNearest t y)
  neg x := -Real.roundNearest t x
  le x y := if Real.roundNearest t x ≤ Real.roundNearest t y then true else false
  toNat x := ⌊Real.roundNearest t x⌋₊
  mm := gridMM t
  qr := gridQR t
  unif s v := max (-Real.roundNearest t s)
    (min (Real.roundNearest t s) (Real.roundNearest t (Real.roundNearest t s * v)))
  normal z := (Real.roundNearest t z.re, Real.roundNearest t z.im)

/-- A rounded value is a rounding of the exact one at the decoding: $\mathrm{fl}(\mathrm{fl}(a))
= \mathrm{fl}(a)$ for $t \ge 1$. -/
private theorem isRoundingOf_roundNearest_roundNearest {t : ℕ} (ht : 0 < t) (Ω a : ℝ) :
    IsRoundingOf (2⁻¹ ^ t) 0 Ω a (Real.roundNearest t (Real.roundNearest t a)) := by
  rw [Real.roundNearest_roundNearest ht]
  exact isRoundingOf_roundNearest t Ω a

/-- The uniform sampler of the grid machine meets its contract, floor $0$. -/
private theorem isUnifSampler_gridMachine {t : ℕ} (ht : 0 < t) :
    IsUnifSampler (Real.roundNearest t) (2⁻¹ ^ t) 0 (gridMachine t).unif := by
  intro s v hs hv
  set R := Real.roundNearest t
  set a := R s
  have hfix : ∀ x ∈ Real.floatGrid t, R x = x := fun x hx =>
    Real.roundNearest_eq_self_of_mem_floatGrid hx
  have ha : a ∈ Real.floatGrid t := Real.roundNearest_mem_floatGrid ht s
  have hw : R (a * v) ∈ Real.floatGrid t := Real.roundNearest_mem_floatGrid ht _
  have hmin : min a (R (a * v)) ∈ Real.floatGrid t := by
    rcases min_choice a (R (a * v)) with h | h <;> (rw [h]; assumption)
  have hmax : max (-a) (min a (R (a * v))) ∈ Real.floatGrid t := by
    rcases max_choice (-a) (min a (R (a * v))) with h | h <;> rw [h]
    · exact Real.neg_mem_floatGrid ha
    · exact hmin
  change |R (max (-a) (min a (R (a * v))))| ≤ a ∧
    |a * v - R (max (-a) (min a (R (a * v))))| ≤ 2⁻¹ ^ t * max a 0
  rw [hfix _ hmax, max_eq_left hs]
  have hsv : |a * v| ≤ a := by
    rw [abs_mul, abs_of_nonneg hs]
    exact mul_le_of_le_one_right hs (abs_le.mpr ⟨hv.1, hv.2⟩)
  obtain ⟨hl, hh⟩ := abs_le.mp hsv
  have hr := Real.abs_sub_roundNearest_le t (a * v)
  refine ⟨abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩, ?_⟩
  refine le_trans ?_ (hr.trans (by gcongr))
  rcases le_total a (R (a * v)) with h | h
  · rw [min_eq_left h, max_eq_right (by linarith), abs_of_nonpos (by linarith),
      abs_of_nonpos (by linarith)]
    linarith
  · rw [min_eq_right h]
    rcases le_total (-a) (R (a * v)) with h' | h'
    · rw [max_eq_right h']
    · rw [max_eq_left h', abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith

/-- The normal sampler of the grid machine meets its contract, constant $\sqrt2$, floor $0$. -/
private theorem isNormalSampler_gridMachine {t : ℕ} (ht : 0 < t) (Ω : ℝ) :
    IsNormalSampler (decodeComplex (Real.roundNearest t)) (2⁻¹ ^ t) √2 0 Ω
      (gridMachine t).normal := by
  intro z _
  set R := Real.roundNearest t
  have hre := Real.abs_sub_roundNearest_le t z.re
  have him := Real.abs_sub_roundNearest_le t z.im
  have hRe : |z.re| ≤ max ‖z‖ 0 := (Complex.abs_re_le_norm z).trans (le_max_left _ _)
  have hIm : |z.im| ≤ max ‖z‖ 0 := (Complex.abs_im_le_norm z).trans (le_max_left _ _)
  have e1 : (z - decodeComplex R (R z.re, R z.im)).re = z.re - R z.re := by
    simp [decodeComplex, R, Real.roundNearest_roundNearest ht]
  have e2 : (z - decodeComplex R (R z.re, R z.im)).im = z.im - R z.im := by
    simp [decodeComplex, R, Real.roundNearest_roundNearest ht]
  change ‖z - decodeComplex R (R z.re, R z.im)‖ ≤ _
  apply le_of_pow_le_pow_left₀ two_ne_zero (by positivity)
  rw [Complex.sq_norm, Complex.normSq_apply, mul_pow, mul_pow, Real.sq_sqrt zero_le_two, e1, e2,
    ← sq, ← sq]
  have a1 := sq_le_sq' (abs_le.mp hre).1 (abs_le.mp hre).2
  have a2 := sq_le_sq' (abs_le.mp him).1 (abs_le.mp him).2
  have hu : (0 : ℝ) ≤ 2⁻¹ ^ t := by positivity
  have b1 : (2⁻¹ ^ t * |z.re|) ^ 2 ≤ (2⁻¹ ^ t * max ‖z‖ 0) ^ 2 := by gcongr
  have b2 : (2⁻¹ ^ t * |z.im|) ^ 2 ≤ (2⁻¹ ^ t * max ‖z‖ 0) ^ 2 := by gcongr
  nlinarith

/-- **The grid machine meets the machine contract** (`NLAlib.FloatMachine.IsAccurate`): for
$t \ge 1$ and every range $\Omega$, `NLAlib.gridMachine t` meets the contract at the decoding
`Real.roundNearest t`, unit roundoff $u = 2^{-t}$, floor $0$, range $\Omega$,
$\mu_{\mathrm{MM}}(d) = \mu_{\mathrm{QR}}(d) = 2d$ and $c_{\mathrm N} = \sqrt2$. A machine with
$u > 0$ and floor $0$, on the decoding of `NLAlib.Computation.gridSem`. No printed source. -/
theorem isAccurate_gridMachine {t : ℕ} (ht : 0 < t) (Ω : ℝ) :
    (gridMachine t).IsAccurate (Real.roundNearest t) (2⁻¹ ^ t) 0 Ω (fun d => 2 * d)
      (fun d => 2 * d) √2 := by
  have hr := isRoundingOf_roundNearest_roundNearest ht Ω
  refine ⟨roundNearest_zero t, roundNearest_one ht, fun k => hr _, fun x y => hr _,
    fun x y => hr _, fun x y => hr _, fun x y _ => hr _, fun x => ?_, fun x y => ?_,
    fun x => rfl, isMatMulErr_gridMM ht Ω, isQRErr_gridQR ht Ω, isUnifSampler_gridMachine ht,
    isNormalSampler_gridMachine ht Ω⟩
  · exact Real.roundNearest_eq_self_of_mem_floatGrid
      (Real.neg_mem_floatGrid (Real.roundNearest_mem_floatGrid ht x))
  · change (if Real.roundNearest t x ≤ Real.roundNearest t y then true else false) = true ↔ _
    split_ifs with h <;> simp [h]

/-! ### Rounding the tape -/

/-- **Rounding to nearest is a tape rounding**: for $t \ge 1$, every tag `p` and range $\Omega$,
the position-independent rounding $\rho(d, i, y) = \mathrm{fl}(y)$ meets
`NLAlib.Computation.IsTapeRounding` at the decoding `Real.roundNearest t`, $u = 2^{-t}$, floor
$0$ and constant $1$: relative error $u$, and a uniform draw in $[-1, 1]$ rounds into $[-1, 1]$
(`NLAlib.abs_roundNearest_le_of_mem_floatGrid` at $\pm1$). No printed source. -/
theorem isTapeRounding_roundNearest {P : Type} {t : ℕ} (ht : 0 < t) (p : P) (Ω : ℝ) :
    Computation.IsTapeRounding (fun _ => Real.roundNearest t) p (2⁻¹ ^ t) 0 Ω (fun _ => 1)
      (fun _ _ y => Real.roundNearest t y) := by
  refine ⟨fun d i x _ => ?_, fun i x hx => ?_⟩
  · change |Real.roundNearest t (Real.roundNearest t x) - x| ≤ 1 * 2⁻¹ ^ t * max |x| 0
    rw [Real.roundNearest_roundNearest ht, abs_sub_comm, one_mul, max_eq_left (abs_nonneg x)]
    exact Real.abs_sub_roundNearest_le t x
  · have h1 : (1 : ℝ) ∈ Real.floatGrid t := by
      rw [← roundNearest_one ht]; exact Real.roundNearest_mem_floatGrid ht 1
    have h := abs_roundNearest_le_of_mem_floatGrid h1 (abs_le.mpr ⟨by simpa using hx.1,
      by simpa using hx.2⟩)
    rw [abs_one] at h
    change Real.roundNearest t (Real.roundNearest t x) ∈ Set.Icc (-1 : ℝ) 1
    rw [Real.roundNearest_roundNearest ht]
    exact ⟨(abs_le.mp h).1, (abs_le.mp h).2⟩

/-- Rounding to nearest has countable range: its values are integers times powers of two.
No printed source. -/
theorem countable_range_roundNearest (t : ℕ) : (Set.range (Real.roundNearest t)).Countable := by
  refine (Set.countable_range fun p : ℤ × ℤ => (p.1 : ℝ) * (2 : ℝ) ^ p.2).mono ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨(_, _), rfl⟩

/-- Rounding to nearest is measurable. No printed source. -/
theorem measurable_roundNearest (t : ℕ) : Measurable (Real.roundNearest t) := by
  have hround : Measurable fun x : ℝ => ((round x : ℤ) : ℝ) := by
    have e : (fun x : ℝ => ((round x : ℤ) : ℝ)) = fun x => ((⌊x + 1 / 2⌋ : ℤ) : ℝ) := by
      funext x; rw [round_eq]
    rw [e]
    exact (Measurable.of_discrete (f := fun k : ℤ => (k : ℝ))).comp
      (Int.measurable_floor.comp (measurable_id.add_const _))
  have hk : ∀ k : ℤ, Measurable fun x : ℝ =>
      ((round (x / (2 : ℝ) ^ (k + 1 - t)) : ℤ) : ℝ) * (2 : ℝ) ^ (k + 1 - t) := fun k =>
    (hround.comp (measurable_id.div_const _)).mul_const _
  have hg : Measurable fun q : ℝ × ℤ =>
      ((round (q.1 / (2 : ℝ) ^ (q.2 + 1 - t)) : ℤ) : ℝ) * (2 : ℝ) ^ (q.2 + 1 - t) :=
    measurable_from_prod_countable_left hk
  have e : Real.roundNearest t = (fun q : ℝ × ℤ =>
      ((round (q.1 / (2 : ℝ) ^ (q.2 + 1 - t)) : ℤ) : ℝ) * (2 : ℝ) ^ (q.2 + 1 - t)) ∘
      fun x => (x, Int.log 2 |x|) := by
    funext x; rfl
  rw [e]
  exact hg.comp (measurable_id.prodMk measurable_intLog_abs)

end NLAlib
