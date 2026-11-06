/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.Primitives
public import NLAlib.Matrix.Factorizations.QR
public import NLAlib.Computation.BinaryFloat
public import NLAlibScaffold.Matrix.Computation.EntrywiseRounding

/-!
# The machine contract is satisfiable, and a bridge for products (scaffold)

Statements for `NLAlib/Matrix/Computation/Primitives.lean` (stage HDIAG, wave W1, design note
`docs/design/Eigensolvers-HermitianDiagonalization.md` §3.3): the exact machine (stored numbers
the reals, every operation exact, an exact QR factorization) meets
`NLAlib.FloatMachine.IsAccurate` at $u = 0$ for every floor, range and constants, so the
hypotheses of the analyses are consistent; and a mixed absolute–relative product bound, the form
a bounded-exponent model gives, implies the product contract with a floor (§12 of the note,
item (b)).

## Main results

* `NLAlib.exists_floatMachine_isAccurate`: the exact machine.
* `NLAlib.exists_floatMachine_isAccurate_binaryFloatRound`: a bounded-format machine.
* `NLAlib.IsMatMulErr.of_specNorm_mul_sub_le_add`: from a mixed bound to the floor form.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

/-- A stored pair of reals as a complex number. -/
private def toCplx (z : ℝ × ℝ) : ℂ := ⟨z.1, z.2⟩

/-- A complex number as a stored pair of reals. -/
private def ofCplx (w : ℂ) : ℝ × ℝ := (w.re, w.im)

private lemma map_ofCplx_toCplx {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℂ) :
    (X.map ofCplx).map toCplx = X := by
  ext i j; rfl

private lemma exists_qrFactors {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    ∃ p : Matrix (Fin m) (Fin m) ℂ × Matrix (Fin m) (Fin n) ℂ,
      HasOrthonormalCols p.1 ∧ IsUpperTrapezoidal p.2 ∧ A = p.1 * p.2 := by
  obtain ⟨Q, R, hQ, hR, hA⟩ := exists_hasOrthonormalCols_mul_isUpperTrapezoidal A
  exact ⟨(Q, R), hQ, hR, hA⟩

/-- The exact QR factors of a complex matrix (a choice). -/
private noncomputable def qrFactors {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    Matrix (Fin m) (Fin m) ℂ × Matrix (Fin m) (Fin n) ℂ :=
  Classical.choose (exists_qrFactors A)

/-- The exact machine on stored reals and complex pairs: every operation is exact. -/
private noncomputable def exactMachine : FloatMachine ℝ ℝ ℂ where
  zero := 0
  one := 1
  ofNat k := (k : ℝ)
  add x y := x + y
  sub x y := x - y
  mul x y := x * y
  div x y := x / y
  neg x := -x
  le x y := if x ≤ y then true else false
  toNat x := ⌊x⌋₊
  mm := fun {_ _ _} A B => ((A.map toCplx) * (B.map toCplx)).map ofCplx
  qr := fun {_ _} A =>
    (((qrFactors (A.map toCplx)).1).map ofCplx, ((qrFactors (A.map toCplx)).2).map ofCplx)
  unif s v := s * v
  normal z := ofCplx z

private lemma exactMachine_mm_decode {l m n : ℕ} (A : Matrix (Fin l) (Fin m) (ℝ × ℝ))
    (B : Matrix (Fin m) (Fin n) (ℝ × ℝ)) :
    (exactMachine.mm A B).map (decodeComplex id) =
      A.map (decodeComplex id) * B.map (decodeComplex id) :=
  map_ofCplx_toCplx _

private lemma isRounding_exact {u τ Ω a z : ℝ} (h : a = z) (hu : u = 0) :
    IsRoundingOf u τ Ω a z :=
  fun _ => by simp [h, hu]

private lemma exactMachine_isMatMulErr (u τ Ω : ℝ) (μ : ℕ → ℝ) (hu : 0 ≤ u)
    (hμ : ∀ d, 0 ≤ μ d) : IsMatMulErr (decodeComplex id) u τ Ω μ exactMachine.mm where
  specNorm_mul_sub_le A B _ := by
    rw [exactMachine_mm_decode, sub_self, specNorm_zero]
    exact mul_nonneg (mul_nonneg (hμ _) hu) (le_max_of_le_left (by positivity))
  isHermitian_of_map_eq_conjTranspose A B hB := by
    rw [exactMachine_mm_decode, hB]
    exact Matrix.isHermitian_mul_conjTranspose_self _

private lemma exactMachine_isQRErr (u τ Ω : ℝ) (μ : ℕ → ℝ) (hu : 0 ≤ u)
    (hμ : ∀ d, 0 ≤ μ d) : IsQRErr (decodeComplex id) u τ Ω μ exactMachine.qr := by
  intro m n A _
  have hp := Classical.choose_spec (exists_qrFactors (A.map toCplx))
  have hA : A.map toCplx = (qrFactors (A.map toCplx)).1 * (qrFactors (A.map toCplx)).2 :=
    hp.2.2
  refine ⟨?_, (qrFactors (A.map toCplx)).1, hp.1, ?_, ?_⟩
  · change IsUpperTrapezoidal ((((qrFactors (A.map toCplx)).2).map ofCplx).map toCplx)
    rw [map_ofCplx_toCplx]
    exact hp.2.1
  · change specNorm ((qrFactors (A.map toCplx)).1 -
      ((((qrFactors (A.map toCplx)).1).map ofCplx).map toCplx)) ≤ _
    rw [map_ofCplx_toCplx, sub_self, specNorm_zero]
    exact mul_nonneg (hμ _) hu
  · change specNorm (A.map toCplx -
      (qrFactors (A.map toCplx)).1 * ((((qrFactors (A.map toCplx)).2).map ofCplx).map toCplx)) ≤ _
    rw [map_ofCplx_toCplx, ← hA, sub_self, specNorm_zero]
    exact mul_nonneg (mul_nonneg (hμ _) hu) (le_max_of_le_left (by positivity))

/-- **The machine contract is satisfiable**: for every floor $\tau$, range $\Omega$, nonnegative
constants $\mu_{\mathrm{MM}}$, $\mu_{\mathrm{QR}}$ and $c_{\mathrm N} \ge 0$, there is a
`NLAlib.FloatMachine` on stored reals, with real seeds and complex samples, meeting
`NLAlib.FloatMachine.IsAccurate` with the identity decoding and $u = 0$: exact arithmetic,
`Nat.floor` for the conversion, $s v$ for the uniform sampler, the parts of $z$ for the normal
sampler, exact products and an exact QR factorization. No printed source.
Proof: build the machine field by field; products decode, multiply and re-encode
(`Complex.re`, `Complex.im`, `Complex.ext`); for QR choose the factors of
`NLAlib.exists_hasOrthonormalCols_mul_isUpperTrapezoidal` (`Classical.choose`, so the witness is
noncomputable, which the contract allows; `le` is `decide (x ≤ y)` by classical decidability);
every error is $0$, `Nat.floor`,
$\lvert sv \rvert \le s$ for $v \in [-1, 1]$, `Matrix.isHermitian_mul_conjTranspose_self`. M, about
60 lines. -/
theorem exists_floatMachine_isAccurate (τ Ω : ℝ) {μM μQ : ℕ → ℝ} (hμM : ∀ d, 0 ≤ μM d)
    (hμQ : ∀ d, 0 ≤ μQ d) {cN : ℝ} (hcN : 0 ≤ cN) :
    ∃ M : FloatMachine ℝ ℝ ℂ, M.IsAccurate id 0 τ Ω μM μQ cN := by
  refine ⟨exactMachine, ?_⟩
  refine
    { dec_zero := rfl
      dec_one := rfl
      ofNat := fun k => isRounding_exact rfl rfl
      add := fun x y => isRounding_exact rfl rfl
      sub := fun x y => isRounding_exact rfl rfl
      mul := fun x y => isRounding_exact rfl rfl
      div := fun x y _ => isRounding_exact rfl rfl
      dec_neg := fun x => rfl
      le_iff := fun x y => by
        change (if x ≤ y then true else false) = true ↔ x ≤ y
        split_ifs with h <;> simp [h]
      toNat_eq := fun x => rfl
      isMatMulErr := exactMachine_isMatMulErr 0 τ Ω μM le_rfl hμM
      isQRErr := exactMachine_isQRErr 0 τ Ω μQ le_rfl hμQ
      isUnifSampler := fun s v hs hv => by
        have hv' : |v| ≤ 1 := abs_le.mpr ⟨hv.1, hv.2⟩
        have hs' : 0 ≤ s := hs
        refine ⟨?_, ?_⟩
        · change |s * v| ≤ s
          rw [abs_mul, abs_of_nonneg hs']
          exact mul_le_of_le_one_right hs' hv'
        · change |s * v - s * v| ≤ 0 * max s τ
          simp
      isNormalSampler := fun z _ => by
        change ‖z - z‖ ≤ _
        simp }

/-- **A bounded-format machine meets the contract**: for a binary format `fmt` with precision
$p$, smallest exponent $e_{\min}$ and largest finite number $\Omega$, and nonnegative constants,
there is a `NLAlib.FloatMachine` on stored reals whose addition, subtraction, multiplication,
division by a nonzero and conversion round the exact result to `fmt`
(`NLAlib.Computation.binaryFloatRound`, gradual underflow), meeting
`NLAlib.FloatMachine.IsAccurate` with the identity decoding, $u = 2^{-p}$, floor
$\tau = 2^{e_{\min} + p - 1}$, range $\Omega$ and $c_{\mathrm N} = \sqrt2$: the uniform sampler
clamps the rounded $sv$ to $[-s, s]$, the normal sampler rounds both parts, and the black boxes
are exact. The bounded model is therefore an instance of the contract, not a separate one. No
printed source.
Proof: as `NLAlib.exists_floatMachine_isAccurate`, with `NLAlib.isRoundingOf_binaryFloatRound` for
each scalar operation (`binaryFloatRound` of $0$ and $1$ are exact:
`NLAlib.Computation.binaryFloatRound_zero`, `NLAlib.Computation.binaryFloatRound_eq_self`); the
clamped uniform sample is at least as close to $sv \in [-s, s]$ (for every scale, beyond the range
too: use the unrestricted mixed bound `NLAlib.Computation.absRelErr_binaryFloatRound`, whose proof
has no range condition, with $u|sv| + 2^{e_{\min}}/2 \le u\max(s, \tau)$); for the normal sampler
$\max(\lvert\operatorname{Re}\rvert, \tau)^2 + \max(\lvert\operatorname{Im}\rvert, \tau)^2 \le
2\max(\lvert z\rvert, \tau)^2$. M, about 70 lines. -/
theorem exists_floatMachine_isAccurate_binaryFloatRound (fmt : Float.Model.Format) {r : ℝ → ℤ}
    (hr : ∀ x, Computation.AbsRelErr 0 (1 / 2) x (r x : ℝ)) {μM μQ : ℕ → ℝ}
    (hμM : ∀ d, 0 ≤ μM d) (hμQ : ∀ d, 0 ≤ μQ d) :
    ∃ M : FloatMachine ℝ ℝ ℂ,
      M.IsAccurate id ((2 : ℝ)⁻¹ ^ fmt.mantissaBits)
        ((2 : ℝ) ^ (fmt.minExponent + fmt.mantissaBits - 1)) fmt.maxFinite μM μQ √2 ∧
      (∀ x y, M.add x y = Computation.binaryFloatRound fmt r (x + y)) ∧
      (∀ x y, M.sub x y = Computation.binaryFloatRound fmt r (x - y)) ∧
      (∀ x y, M.mul x y = Computation.binaryFloatRound fmt r (x * y)) ∧
      (∀ x y, y ≠ 0 → M.div x y = Computation.binaryFloatRound fmt r (x / y)) := by
  sorry

/-- **From a mixed absolute–relative product bound to the contract with a floor**: if a routine
on stored entries with decoding `dec` satisfies $\|\bar{\mathbf{A}}\bar{\mathbf{B}} -
\overline{\mathrm{mm}(\mathbf{A}, \mathbf{B})}\|_2 \le \mu(d)\,u\,\|\bar{\mathbf{A}}\|_2
\|\bar{\mathbf{B}}\|_2 + \eta$ whenever $\|\bar{\mathbf{A}}\|_2\|\bar{\mathbf{B}}\|_2 \le \Omega$,
computes products with a conjugate transpose exactly Hermitian, and $\eta \le \mu(d)\,u\,\tau$ for
every $d$, then it satisfies `NLAlib.IsMatMulErr` with $2\mu$. A bounded-exponent product bound
(underflow as an absolute $\eta$) therefore gives the contract with floor $\tau = \eta/(\mu u)$.
No printed source.
Proof: $\mu u x + \eta \le \mu u x + \mu u \tau \le 2\mu u\max(x, \tau)$ (`add_le_add`,
`le_max_left`, `le_max_right`, `two_mul`). S, about 12 lines. -/
theorem IsMatMulErr.of_specNorm_mul_sub_le_add {K 𝕜 : Type*} [RCLike 𝕜] {dec : K → 𝕜}
    {u τ Ω η : ℝ} {μ : ℕ → ℝ} {mm : MatMulMap K}
    (hmix : ∀ {l m n : ℕ} (A : Matrix (Fin l) (Fin m) K) (B : Matrix (Fin m) (Fin n) K),
      specNorm (A.map dec) * specNorm (B.map dec) ≤ Ω →
        specNorm (A.map dec * B.map dec - (mm A B).map dec) ≤
          μ (max l (max m n)) * u * (specNorm (A.map dec) * specNorm (B.map dec)) + η)
    (hherm : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) K) (B : Matrix (Fin n) (Fin m) K),
      B.map dec = (A.map dec)ᴴ → ((mm A B).map dec).IsHermitian)
    (hμu : ∀ d, 0 ≤ μ d * u) (hη : ∀ d, η ≤ μ d * u * τ) :
    IsMatMulErr dec u τ Ω (fun d => 2 * μ d) mm := by
  sorry

end NLAlib
