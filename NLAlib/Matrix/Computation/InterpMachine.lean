/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.KernelContracts
public import NLAlib.Computation.Contract
public import NLAlib.Matrix.Computation.EntrywiseRounding

/-!
# The floating-point machine of a value semantics

A shallow algorithm written over a `NLAlib.FloatMachine` ([Shah2024, Section 1.2]) and a program
of the model of computation compute the same thing when the machine's operations are the
program's instructions. `NLAlib.Computation.ScalarSem.toFloatMachine sem p …` is that machine:
its scalar operations are the operations of the value semantics `sem` at tag `p` (a literal for
$0$, $1$ and each natural number, the four arithmetic operations, negation and the comparison
$\le$), and its black boxes are the routines that the kernel contracts
`NLAlib.Computation.IsMatMulKernel` and `NLAlib.Computation.IsQRKernel` name. A failed operation
reads as `default`; a successful run of a program performs only operations that succeed, so on
such a run the machine and the program agree operation by operation, one rounding each (design
note `docs/design/Computation-SignDeflatePrograms.md`).

The machine's normal sampler is built from the tape as the program builds it:
`NLAlib.Computation.ScalarSem.tapeNormal` multiplies two stored Gaussian draws by the stored
$\mathrm{fl}(\sqrt{\mathrm{fl}(1/2)})$ (`NLAlib.Computation.ScalarSem.sqrtHalf`), and
`NLAlib.Computation.ScalarSem.gaussianNormal` is the same sampler on an ideal complex Gaussian
sample, for a tape rounding that does not depend on the position.
`NLAlib.Computation.tapeComplexMatrix` is the ideal complex Gaussian matrix that a tape of real
draws defines, and `NLAlib.Computation.tapeIndexMatrix` the positions of its entries.

## Main definitions

* `NLAlib.Computation.ScalarSem.toFloatMachine`: the machine of a semantics and routines.
* `NLAlib.Computation.ScalarSem.DecidesFlags`: the comparison that a loop on a flag cell needs.
* `NLAlib.Computation.ScalarSem.sqrtHalf`, `NLAlib.Computation.ScalarSem.tapeNormal`,
  `NLAlib.Computation.ScalarSem.gaussianNormal`: the normal sampler of a program.
* `NLAlib.Computation.tapeComplexMatrix`, `NLAlib.Computation.tapeIndexMatrix`.

## Main results

* `NLAlib.Computation.isAccurate_toFloatMachine`: under the standard model with every value in
  range and an exact literal $1$, the machine meets the machine contract
  `NLAlib.FloatMachine.IsAccurate` with floor $0$, given routines and samplers meeting theirs.
* `NLAlib.Computation.IsRelErrSem.decidesFlags`: the semantics decides flags.
* `NLAlib.Computation.isNormalSampler_gaussianNormal`: the normal sampler of a tape rounding.
* `NLAlib.FloatMachine.IsAccurate.mono`: the contract is monotone in the unit roundoff.
* `NLAlib.Computation.decodeMatrix_hermShift_toFloatMachine_exactSem`,
  `NLAlib.Computation.decodeMatrix_hermScale_toFloatMachine_exactSem`,
  `NLAlib.Computation.decodeMatrix_hermAvg_toFloatMachine_exactSem`,
  `NLAlib.Computation.decodeMatrix_conjTransposeMat_toFloatMachine_exactSem`,
  `NLAlib.Computation.traceRe_toFloatMachine_exactSem`,
  `NLAlib.Computation.boxTest_toFloatMachine_exactSem_iff`,
  `NLAlib.Computation.decodeMatrix_addParts_toFloatMachine_exactSem`,
  `NLAlib.Computation.decodeMatrix_subParts_toFloatMachine_exactSem`,
  `NLAlib.Computation.decodeMatrix_mulParts_toFloatMachine_exactSem`: on exact real arithmetic the
  entrywise machine operations decode to their exact values (the exact specifications of the
  complex kernels).
-/

@[expose] public section

namespace NLAlib.Computation

variable {P K : Type} [Inhabited K]

/-- **The floating-point machine of the value semantics `sem` at tag `p`**, with the black boxes
`mm`, `qr`, the conversion `toNat` and the samplers `unif`, `normal`: zero, one and the
conversion of a natural number $k$ are the literals $0$, $1$ and $k$; addition, subtraction,
multiplication and division are the binary operations; negation is the unary one; the
comparison is $\le$. A failed operation gives `default` (a failed comparison `false`). -/
def ScalarSem.toFloatMachine {Su Sg : Type*} (sem : ScalarSem P K) (p : P) (toNat : K → ℕ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K)) (unif : K → Su → K) (normal : Sg → K × K) :
    FloatMachine K Su Sg where
  zero := (sem.lit p 0).getD default
  one := (sem.lit p 1).getD default
  ofNat k := (sem.lit p (k : ℚ)).getD default
  add x y := (sem.bin p .add x y).getD default
  sub x y := (sem.bin p .sub x y).getD default
  mul x y := (sem.bin p .mul x y).getD default
  div x y := (sem.bin p .div x y).getD default
  neg x := (sem.un p .neg x).getD default
  le x y := (sem.cmp p .le x y).getD false
  toNat := toNat
  mm := mm
  qr := qr
  unif := unif
  normal := normal

/-- **The semantics decides flags** at tag `p`: the literals $0$ and $1$ succeed, and the
equality test tells them apart ($0 \ne 1$, $1 = 1$). A program that keeps a pass or fail flag in a
cell and loops on it needs this. Under the standard model with an exact literal $1$ it holds. -/
def ScalarSem.DecidesFlags (sem : ScalarSem P K) (p : P) : Prop :=
  ∃ z o : K, sem.lit p 0 = some z ∧ sem.lit p 1 = some o ∧ sem.cmp p .eq z o = some false ∧
    sem.cmp p .eq o o = some true

/-- **The stored $\sqrt{1/2}$** of the semantics `sem` at tag `p`:
$\mathrm{fl}(\sqrt{\mathrm{fl}(1/2)})$, from the literals $1$ and $2$ by a division and a square
root, as the program computes it. -/
def ScalarSem.sqrtHalf (sem : ScalarSem P K) (p : P) : K :=
  (sem.un p .sqrt ((sem.bin p .div ((sem.lit p 1).getD default)
    ((sem.lit p ((2 : ℕ) : ℚ)).getD default)).getD default)).getD default

/-- **The normal sampler of a tape** of stored real draws $x$: sample $k$ is
$(\mathrm{fl}(x_{2k}s), \mathrm{fl}(x_{2k+1}s))$ with $s$ the stored $\sqrt{1/2}$
(`NLAlib.Computation.ScalarSem.sqrtHalf`), the real and imaginary parts of a stored complex
Gaussian. -/
def ScalarSem.tapeNormal (sem : ScalarSem P K) (p : P) (x : ℕ → K) : ℕ → K × K := fun k =>
  ((sem.bin p .mul (x (2 * k)) (sem.sqrtHalf p)).getD default,
    (sem.bin p .mul (x (2 * k + 1)) (sem.sqrtHalf p)).getD default)

/-- **The normal sampler of a tape rounding** $\rho$ on an ideal complex sample $z$: the stored
draws $\rho(\sqrt2\operatorname{Re} z)$ and $\rho(\sqrt2\operatorname{Im} z)$ times the stored
$\sqrt{1/2}$, each product rounded. With $z$ the ideal sample $(\xi_{2k} + i\xi_{2k+1})/\sqrt2$
of a tape $\xi$ it is `NLAlib.Computation.ScalarSem.tapeNormal` on the stored tape
$\rho \circ \xi$. -/
noncomputable def ScalarSem.gaussianNormal (sem : ScalarSem P K) (p : P) (ρ : ℝ → K) :
    ℂ → K × K := fun z =>
  ((sem.bin p .mul (ρ (√2 * z.re)) (sem.sqrtHalf p)).getD default,
    (sem.bin p .mul (ρ (√2 * z.im)) (sem.sqrtHalf p)).getD default)

/-- **The ideal complex Gaussian matrix of a tape** of real draws $x$: entry $(i, j)$ of the
$N \times N$ matrix is $(x_{2(i + Nj)} + i\,x_{2(i + Nj) + 1})/\sqrt2$, column-major. -/
noncomputable def tapeComplexMatrix (x : ℕ → ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j => ⟨x (2 * (i + N * j)) / √2, x (2 * (i + N * j) + 1) / √2⟩

/-- **The sample positions** of an $N \times N$ matrix drawn column-major: entry $(i, j)$ is
sample $i + Nj$ (its two real draws at tape positions $2(i + Nj)$ and $2(i + Nj) + 1$). -/
def tapeIndexMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℕ :=
  Matrix.of fun i j => i + N * j

end NLAlib.Computation

open scoped Matrix

namespace NLAlib.Computation

variable {P K : Type} [Inhabited K]

/-- The machine of a semantics meets the machine contract: if the value semantics `sem`
meets the standard model at unit roundoff $u \ge 0$ with every value in range
(`NLAlib.Computation.IsRelErrSem`), its literal $1$ is exact, and the routines `mm`, `qr` and the
samplers `unif`, `normal` meet `NLAlib.IsMatMulErr`, `NLAlib.IsQRErr`, `NLAlib.IsUnifSampler` and
`NLAlib.IsNormalSampler` at $u$, floor $0$ and range $\Omega$ through the decoding at tag `p`,
then the machine of `sem` at `p` with these black boxes and the floor conversion meets
`NLAlib.FloatMachine.IsAccurate` at $u$, floor $0$, range $\Omega$. No printed source. -/
theorem isAccurate_toFloatMachine {sem : ScalarSem P K} {dec : P → K → ℝ} {u : ℝ} (Ω : ℝ)
    (hsem : IsRelErrSem (fun _ => u) dec (fun _ _ => True) sem) (hlit : IsExactIntLit dec sem 1)
    (hu : 0 ≤ u) (p : P) {μM μQ : ℕ → ℝ} {cN : ℝ} {mm : MatMulMap (K × K)}
    {qr : QRMap (K × K)} {unif : K → ℝ → K} {normal : ℂ → K × K}
    (hmm : IsMatMulErr (decodeComplex (dec p)) u 0 Ω μM mm)
    (hqr : IsQRErr (decodeComplex (dec p)) u 0 Ω μQ qr)
    (hunif : IsUnifSampler (dec p) u 0 unif)
    (hnormal : IsNormalSampler (decodeComplex (dec p)) u cN 0 Ω normal) :
    (sem.toFloatMachine p (fun x => ⌊dec p x⌋₊) mm qr unif normal).IsAccurate (dec p) u 0 Ω μM μQ
      cN := by
  -- a value `z` decoding to `a (1 + δ)` with `|δ| ≤ u` is a rounding of `a`
  have rnd : ∀ (a : ℝ) (z : K) (δ : ℝ), |δ| ≤ u → dec p z = a * (1 + δ) →
      IsRoundingOf u 0 Ω a (dec p z) := by
    intro a z δ hδ hz
    unfold IsRoundingOf
    intro _
    rw [hz, max_eq_left (abs_nonneg a)]
    have e : a - a * (1 + δ) = -(a * δ) := by ring
    rw [e, abs_neg, abs_mul]
    exact (mul_le_mul_of_nonneg_left hδ (abs_nonneg a)).trans_eq (mul_comm _ _)
  have hbin : ∀ (b : BinOp) (x y : K), b.IsArith → (b = .div → dec p y ≠ 0) →
      IsRoundingOf u 0 Ω (b.realOp (dec p x) (dec p y))
        (dec p ((sem.bin p b x y).getD default)) := by
    intro b x y ha hy
    obtain ⟨z, hz⟩ := hsem.bin_ok p b x y ha hy trivial
    obtain ⟨δ, hδ, hd⟩ := hsem.bin_err p b x y z ha hz
    rw [hz, Option.getD_some]
    exact rnd _ z δ hδ hd
  have hofNat : ∀ k : ℕ, IsRoundingOf u 0 Ω (k : ℝ) (dec p ((sem.lit p (k : ℚ)).getD default)) := by
    intro k
    obtain ⟨z, hz⟩ := hsem.lit_ok p (k : ℚ) trivial
    obtain ⟨δ, hδ, hd⟩ := hsem.lit_err p (k : ℚ) z hz
    rw [hz, Option.getD_some]
    exact rnd _ z δ hδ (by rw [hd]; simp)
  refine ⟨?_, ?_, hofNat, fun x y => hbin .add x y trivial (fun h => nomatch h),
    fun x y => hbin .sub x y trivial (fun h => nomatch h),
    fun x y => hbin .mul x y trivial (fun h => nomatch h),
    fun x y hy => hbin .div x y trivial (fun _ => hy), ?_, ?_, ?_, hmm, hqr, hunif, hnormal⟩
  · obtain ⟨z, hz, hd⟩ := hlit p 0 (Nat.zero_le _)
    simp only [Nat.cast_zero] at hz hd
    change dec p ((sem.lit p 0).getD default) = 0
    rw [hz, Option.getD_some, hd]
  · obtain ⟨z, hz, hd⟩ := hlit p 1 le_rfl
    simp only [Nat.cast_one] at hz hd
    change dec p ((sem.lit p 1).getD default) = 1
    rw [hz, Option.getD_some, hd]
  · intro x
    obtain ⟨z, hz, hd⟩ := hsem.neg p x
    change dec p ((sem.un p .neg x).getD default) = -dec p x
    rw [hz, Option.getD_some, hd]
  · intro x y
    change (sem.cmp p .le x y).getD false = true ↔ dec p x ≤ dec p y
    rw [hsem.cmp_le p x y]
    simp
  · intro x
    rfl

/-- The standard model decides flags: a value semantics meeting the standard model with
every value in range and an exact literal $1$ decides flags at every tag
(`NLAlib.Computation.ScalarSem.DecidesFlags`): its literals $0$ and $1$ decode to $0$ and $1$ and
its equality test is exact. No printed source. -/
theorem IsRelErrSem.decidesFlags {sem : ScalarSem P K} {dec : P → K → ℝ} {u : P → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) sem) (hlit : IsExactIntLit dec sem 1) (p : P) :
    sem.DecidesFlags p := by
  obtain ⟨z, hz, hdz⟩ := hlit p 0 (Nat.zero_le _)
  obtain ⟨o, ho, hdo⟩ := hlit p 1 le_rfl
  simp only [Nat.cast_zero, Nat.cast_one] at hz hdz ho hdo
  refine ⟨z, o, hz, ho, ?_, ?_⟩
  · rw [hsem.cmp_eq p z o, hdz, hdo]
    norm_num
  · rw [hsem.cmp_eq p o o]
    simp

/-- The stored $\sqrt{1/2}$ decodes to $\sigma/\sqrt2\,(1 + \delta)$ with $\lvert\sigma - 1\rvert
\le u$ and $\lvert\delta\rvert \le u$ (helper of `isNormalSampler_gaussianNormal`). -/
private theorem gaussianNormal_sqrtHalf {sem : ScalarSem P K} {dec : P → K → ℝ} {u : ℝ}
    (hsem : IsRelErrSem (fun _ => u) dec (fun _ _ => True) sem) (hlit : IsExactIntLit dec sem 2)
    (p : P) (hu : 0 ≤ u) (hu1 : u ≤ 1 / 10) :
    ∃ σ : ℝ, 0 ≤ σ ∧ |σ - 1| ≤ u ∧ ∃ δ : ℝ, |δ| ≤ u ∧
      dec p (sem.sqrtHalf p) = σ / √2 * (1 + δ) := by
  obtain ⟨z1, hz1, hd1⟩ := hlit p 1 (by norm_num)
  obtain ⟨z2, hz2, hd2⟩ := hlit p 2 le_rfl
  simp only [Nat.cast_one] at hz1 hd1
  obtain ⟨z3, hz3⟩ := hsem.bin_ok p .div z1 z2 trivial (fun _ => by rw [hd2]; norm_num) trivial
  obtain ⟨δ2, hδ2, hd3⟩ := hsem.bin_err p .div z1 z2 z3 trivial hz3
  have hz3' : dec p z3 = (1 + δ2) / 2 := by
    rw [hd3, hd1, hd2]
    simp only [BinOp.realOp]
    push_cast
    ring
  have hb := abs_le.mp hδ2
  have hpos : 0 ≤ 1 + δ2 := by linarith [hb.1]
  obtain ⟨z4, hz4⟩ := hsem.sqrt_ok p z3 (by rw [hz3']; exact div_nonneg hpos (by norm_num))
  obtain ⟨δ3, hδ3, hd4⟩ := hsem.sqrt_err p z3 z4 hz4
  have hs : dec p (sem.sqrtHalf p) = dec p z4 := by
    unfold ScalarSem.sqrtHalf
    simp only [hz1, hz2, hz3, hz4, Option.getD_some]
  have h2 := Real.sq_sqrt hpos
  have hs0 := Real.sqrt_nonneg (1 + δ2)
  refine ⟨√(1 + δ2), hs0, ?_, δ3, hδ3, ?_⟩
  · rw [abs_le]
    constructor <;> nlinarith
  · rw [hs, hd4, hz3', Real.sqrt_div hpos]

/-- The real part (or imaginary part) of the normal sampler of a tape rounding (helper of
`isNormalSampler_gaussianNormal`): the stored product of the rounded draw $\rho(\sqrt2 w)$ and
the stored $\sqrt{1/2}$ is within $2(c + 3)u\lvert w\rvert$ of $w$. -/
private theorem gaussianNormal_part {sem : ScalarSem P K} {dec : P → K → ℝ} {u c Ω : ℝ}
    (hsem : IsRelErrSem (fun _ => u) dec (fun _ _ => True) sem) (p : P) {ρ : ℝ → K}
    (hρ : ∀ x : ℝ, |x| ≤ 2 * Ω → |dec p (ρ x) - x| ≤ c * u * |x|) (hc : 0 ≤ c) (hu : 0 ≤ u)
    (hcu : (c + 3) * u ≤ 1 / 10) {σ δ3 : ℝ} (hσ1 : |σ - 1| ≤ u) (hδ3 : |δ3| ≤ u)
    (hs : dec p (sem.sqrtHalf p) = σ / √2 * (1 + δ3)) (w : ℝ) (hw : |√2 * w| ≤ 2 * Ω) :
    ∃ r : K, sem.bin p .mul (ρ (√2 * w)) (sem.sqrtHalf p) = some r ∧
      |dec p r - w| ≤ 2 * ((c + 3) * u) * |w| := by
  have hu1 : u ≤ 1 / 10 := by nlinarith
  obtain ⟨r, hr⟩ :=
    hsem.bin_ok p .mul (ρ (√2 * w)) (sem.sqrtHalf p) trivial (fun h => nomatch h) trivial
  refine ⟨r, hr, ?_⟩
  obtain ⟨δ4, hδ4, hd⟩ := hsem.bin_err p .mul _ _ r trivial hr
  simp only [BinOp.realOp] at hd
  have h2 : (√2 : ℝ) ≠ 0 := by positivity
  have hX0 := hρ (√2 * w) hw
  obtain ⟨θ, hθ, hX⟩ : ∃ θ : ℝ, |θ| ≤ c * u ∧ dec p (ρ (√2 * w)) = √2 * w * (1 + θ) := by
    by_cases h0 : w = 0
    · subst h0
      refine ⟨0, by simp [mul_nonneg hc hu], ?_⟩
      have h00 : dec p (ρ (√2 * 0)) = 0 := by simpa [abs_nonpos_iff] using hX0
      rw [h00]
      ring
    · have hne : √2 * w ≠ 0 := mul_ne_zero h2 h0
      refine ⟨(dec p (ρ (√2 * w)) - √2 * w) / (√2 * w), ?_, ?_⟩
      · rw [abs_div, div_le_iff₀ (abs_pos.mpr hne)]
        exact hX0
      · field_simp
        ring
  have hrw : dec p r = w * ((1 + θ) * σ * (1 + δ3) * (1 + δ4)) := by
    rw [hd, hX, hs]
    field_simp
  -- a product of factors `1 + a_i` with `|a_i| ≤ α_i` stays within `(1 + M)(1 + α) - 1`
  have chain : ∀ (P f M α : ℝ), 0 ≤ M → 0 ≤ α → |P - 1| ≤ M → |f - 1| ≤ α →
      |P * f - 1| ≤ (1 + M) * (1 + α) - 1 := by
    intro P f M α hM hα hP hf
    have hfa : |f| ≤ 1 + α := by
      rw [abs_le] at hf ⊢
      constructor <;> linarith [hf.1, hf.2]
    have e : P * f - 1 = (P - 1) * f + (f - 1) := by ring
    rw [e]
    calc |(P - 1) * f + (f - 1)| ≤ |(P - 1) * f| + |f - 1| := abs_add_le _ _
      _ = |P - 1| * |f| + |f - 1| := by rw [abs_mul]
      _ ≤ M * (1 + α) + α := add_le_add (mul_le_mul hP hfa (abs_nonneg _) hM) hf
      _ = (1 + M) * (1 + α) - 1 := by ring
  have hQ : |(1 + θ) * σ * (1 + δ3) * (1 + δ4) - 1| ≤ 2 * ((c + 3) * u) := by
    have s1 := chain (1 + θ) σ (c * u) u (mul_nonneg hc hu) hu (by simpa using hθ) hσ1
    have s2 := chain ((1 + θ) * σ) (1 + δ3) ((1 + c * u) * (1 + u) - 1) u
      (by nlinarith [mul_nonneg hc hu]) hu s1 (by simpa using hδ3)
    have s3 := chain ((1 + θ) * σ * (1 + δ3)) (1 + δ4) _ u
      (by nlinarith [mul_nonneg hc hu, mul_nonneg (mul_nonneg hc hu) hu, mul_nonneg hu hu])
      hu s2 (by simpa using hδ4)
    refine s3.trans ?_
    have hq : 0 ≤ c * u * (1 - 3 * u - 3 * u ^ 2 - u ^ 3) :=
      mul_nonneg (mul_nonneg hc hu) (by nlinarith)
    nlinarith [mul_nonneg hu (show (0 : ℝ) ≤ 3 - 3 * u - u ^ 2 by nlinarith)]
  rw [hrw]
  have e : w * ((1 + θ) * σ * (1 + δ3) * (1 + δ4)) - w
      = w * ((1 + θ) * σ * (1 + δ3) * (1 + δ4) - 1) := by ring
  rw [e, abs_mul]
  exact (mul_le_mul_of_nonneg_left hQ (abs_nonneg w)).trans_eq (mul_comm _ _)

/-- The normal sampler of a tape rounding meets the normal-sampler contract: if `sem` meets
the standard model at $u \ge 0$ with every value in range and exact literals up to $2$, and the
rounding $\rho$ of an ideal real Gaussian draw $x$ with $\lvert x\rvert \le 2\Omega$ errs by at most
$c\,u\lvert x\rvert$ with $c \ge 0$ and $(c + 3)u \le 1/10$, then the sampler
`NLAlib.Computation.ScalarSem.gaussianNormal` of $\rho$ meets `NLAlib.IsNormalSampler` at $u$ with
constant $2(c + 3)$, floor $0$ and range $\Omega$. No printed source. -/
theorem isNormalSampler_gaussianNormal {sem : ScalarSem P K} {dec : P → K → ℝ} {u c Ω : ℝ}
    (hsem : IsRelErrSem (fun _ => u) dec (fun _ _ => True) sem) (hlit : IsExactIntLit dec sem 2)
    (p : P) {ρ : ℝ → K} (hρ : ∀ x : ℝ, |x| ≤ 2 * Ω → |dec p (ρ x) - x| ≤ c * u * |x|)
    (hc : 0 ≤ c) (hu : 0 ≤ u) (hcu : (c + 3) * u ≤ 1 / 10) :
    IsNormalSampler (decodeComplex (dec p)) u (2 * (c + 3)) 0 Ω (sem.gaussianNormal p ρ) := by
  have hu1 : u ≤ 1 / 10 := by nlinarith
  obtain ⟨σ, hσ0, hσ1, δ3, hδ3, hs⟩ := gaussianNormal_sqrtHalf hsem hlit p hu hu1
  unfold IsNormalSampler
  intro z hz
  have hΩ : 0 ≤ Ω := (norm_nonneg z).trans hz
  have hsq : ∀ x : ℝ, |x| ≤ ‖z‖ → |√2 * x| ≤ 2 * Ω := by
    intro x hx
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg 2)]
    have h2 : √2 ≤ 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    nlinarith [mul_le_mul_of_nonneg_left (hx.trans hz) (Real.sqrt_nonneg 2)]
  obtain ⟨r1, h1, e1⟩ := gaussianNormal_part hsem p hρ hc hu hcu hσ1 hδ3 hs z.re
    (hsq _ (Complex.abs_re_le_norm z))
  obtain ⟨r2, h2, e2⟩ := gaussianNormal_part hsem p hρ hc hu hcu hσ1 hδ3 hs z.im
    (hsq _ (Complex.abs_im_le_norm z))
  simp only [ScalarSem.gaussianNormal, h1, h2, Option.getD_some]
  rw [max_eq_left (norm_nonneg z)]
  have hA : 0 ≤ 2 * ((c + 3) * u) := by nlinarith
  have hn : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by
    rw [Complex.sq_norm, Complex.normSq_apply]
  have hd : ‖z - decodeComplex (dec p) (r1, r2)‖ ^ 2
      = (z.re - dec p r1) ^ 2 + (z.im - dec p r2) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [decodeComplex]
    ring
  have q1 : (z.re - dec p r1) ^ 2 ≤ (2 * ((c + 3) * u) * z.re) ^ 2 := by
    rw [sq_le_sq, abs_mul, abs_of_nonneg hA, abs_sub_comm]
    exact e1
  have q2 : (z.im - dec p r2) ^ 2 ≤ (2 * ((c + 3) * u) * z.im) ^ 2 := by
    rw [sq_le_sq, abs_mul, abs_of_nonneg hA, abs_sub_comm]
    exact e2
  have key : ‖z - decodeComplex (dec p) (r1, r2)‖ ^ 2 ≤ (2 * ((c + 3) * u) * ‖z‖) ^ 2 := by
    rw [hd]
    have e : (2 * ((c + 3) * u) * ‖z‖) ^ 2
        = (2 * ((c + 3) * u) * z.re) ^ 2 + (2 * ((c + 3) * u) * z.im) ^ 2 := by
      rw [mul_pow (2 * ((c + 3) * u)) ‖z‖, hn]
      ring
    rw [e]
    linarith [q1, q2]
  have hb : 0 ≤ 2 * ((c + 3) * u) * ‖z‖ := mul_nonneg hA (norm_nonneg z)
  have final := (pow_le_pow_iff_left₀ (norm_nonneg _) hb two_ne_zero).mp key
  linarith [final]

end NLAlib.Computation

namespace NLAlib

private lemma isRoundingOf_mono {u u' τ Ω a z : ℝ} (huu' : u ≤ u') (hτ : 0 ≤ τ)
    (h : IsRoundingOf u τ Ω a z) : IsRoundingOf u' τ Ω a z :=
  fun ha => (h ha).trans (mul_le_mul_of_nonneg_right huu' (hτ.trans (le_max_right _ _)))

/-- The machine contract is monotone in the unit roundoff: a machine meeting
`NLAlib.FloatMachine.IsAccurate` at unit roundoff $u \ge 0$, with nonnegative constants
$\mu_{\mathrm{MM}}$, $\mu_{\mathrm{QR}}$, $c_{\mathrm N}$ and floor $\tau \ge 0$, meets it at every
$u' \ge u$. With the exact machine at $u = 0$ (the HDIAG witness) this makes the hypothesis
"the carrier admits an accurate machine" of the SIGN and DEFLATE targets satisfiable at every
$u \ge 0$. No printed source. -/
theorem FloatMachine.IsAccurate.mono {F : Type*} {M : FloatMachine F ℝ ℂ}
    {dec : F → ℝ} {u u' τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hu : 0 ≤ u) (huu' : u ≤ u') (hτ : 0 ≤ τ) (hμM : ∀ d, 0 ≤ μM d) (hμQ : ∀ d, 0 ≤ μQ d)
    (hcN : 0 ≤ cN) : M.IsAccurate dec u' τ Ω μM μQ cN :=
  { dec_zero := hM.dec_zero
    dec_one := hM.dec_one
    ofNat := fun k => isRoundingOf_mono huu' hτ (hM.ofNat k)
    add := fun x y => isRoundingOf_mono huu' hτ (hM.add x y)
    sub := fun x y => isRoundingOf_mono huu' hτ (hM.sub x y)
    mul := fun x y => isRoundingOf_mono huu' hτ (hM.mul x y)
    div := fun x y hy => isRoundingOf_mono huu' hτ (hM.div x y hy)
    dec_neg := hM.dec_neg
    le_iff := hM.le_iff
    toNat_eq := hM.toNat_eq
    isMatMulErr :=
      { specNorm_mul_sub_le := fun A B hAB =>
          (hM.isMatMulErr.specNorm_mul_sub_le A B hAB).trans
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left huu' (hμM _))
              (hτ.trans (le_max_right _ _)))
        isHermitian_of_map_eq_conjTranspose :=
          hM.isMatMulErr.isHermitian_of_map_eq_conjTranspose }
    isQRErr := fun A hA =>
      let h := hM.isQRErr A hA
      ⟨h.1, h.2.choose, h.2.choose_spec.1,
        h.2.choose_spec.2.1.trans (mul_le_mul_of_nonneg_left huu' (hμQ _)),
        h.2.choose_spec.2.2.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left huu' (hμQ _)) (hτ.trans (le_max_right _ _)))⟩
    isUnifSampler := fun s v hs hv =>
      ⟨(hM.isUnifSampler s v hs hv).1,
        (hM.isUnifSampler s v hs hv).2.trans
          (mul_le_mul_of_nonneg_right huu' (hτ.trans (le_max_right _ _)))⟩
    isNormalSampler := fun z hz =>
      (hM.isNormalSampler z hz).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left huu' hcN) (hτ.trans (le_max_right _ _))) }

end NLAlib

namespace NLAlib.Computation

variable {P K : Type} [Inhabited K]

/-! ### Exact specifications: the machine of exact real arithmetic -/

variable {Su Sg : Type} {toNat : ℝ → ℕ} {mm : MatMulMap (ℝ × ℝ)} {qr : QRMap (ℝ × ℝ)}
  {unif : ℝ → Su → ℝ} {normal : Sg → ℝ × ℝ}

/-- The exact shift: on exact real arithmetic (`NLAlib.Computation.exactSem`, decoding the
identity), the stored Hermitian shift of a stored matrix with Hermitian decoding $\mathbf{A}$ by
$c$ decodes to $\mathbf{A} - c\mathbf{I}$. No printed source. -/
theorem decodeMatrix_hermShift_toFloatMachine_exactSem (p : P) {n : ℕ}
    {A : Matrix (Fin n) (Fin n) (ℝ × ℝ)} (hA : (decodeMatrix id A).IsHermitian) (c : ℝ) :
    decodeMatrix id (((exactSem (P := P) (𝕜 := ℝ)).toFloatMachine p toNat mm qr unif
      normal).hermShift A c) = decodeMatrix id A - c • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have hre : ∀ i j, (A i j).1 = (A j i).1 := fun i j => by
    have h := congrArg Complex.re (hA.apply j i)
    simpa [decodeMatrix, decodeComplex] using h
  have him : ∀ i j, (A i j).2 = -(A j i).2 := fun i j => by
    have h := congrArg Complex.im (hA.apply j i)
    simp [decodeMatrix, decodeComplex] at h
    linarith
  ext i j
  simp only [FloatMachine.hermShift, FloatMachine.hermFrom, decodeMatrix, Matrix.map_apply,
    Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, h.ne, decodeComplex]
  · have h0 : (A i i).2 = 0 := by linarith [him i i]
    apply Complex.ext <;> simp [ScalarSem.toFloatMachine, exactSem, decodeComplex, h0]
  · simp [h, h.ne', not_lt.2 h.le, ScalarSem.toFloatMachine, exactSem, decodeComplex, hre i j,
      him i j]

/-- The exact scaling: on exact real arithmetic, the stored Hermitian scaling of a stored
matrix with Hermitian decoding $\mathbf{A}$ by $c$ decodes to $c^{-1}\mathbf{A}$ (at $c = 0$ both
sides are $\mathbf{0}$: the failed division reads as $0$). No printed source. -/
theorem decodeMatrix_hermScale_toFloatMachine_exactSem (p : P) {n : ℕ}
    {A : Matrix (Fin n) (Fin n) (ℝ × ℝ)} (hA : (decodeMatrix id A).IsHermitian) (c : ℝ) :
    decodeMatrix id (((exactSem (P := P) (𝕜 := ℝ)).toFloatMachine p toNat mm qr unif
      normal).hermScale A c) = c⁻¹ • decodeMatrix id A := by
  have hre : ∀ i j, (A i j).1 = (A j i).1 := fun i j => by
    have h := congrArg Complex.re (hA.apply j i)
    simpa [decodeMatrix, decodeComplex] using h
  have him : ∀ i j, (A i j).2 = -(A j i).2 := fun i j => by
    have h := congrArg Complex.im (hA.apply j i)
    simp [decodeMatrix, decodeComplex] at h
    linarith
  by_cases hc : c = 0
  · subst hc
    have hd : (default : ℝ) = 0 := rfl
    ext i j
    simp [FloatMachine.hermScale, FloatMachine.hermFrom, ScalarSem.toFloatMachine, exactSem,
      decodeMatrix, decodeComplex, Complex.ext_iff, hd]
  ext i j
  simp only [FloatMachine.hermScale, FloatMachine.hermFrom, decodeMatrix, Matrix.map_apply,
    Matrix.of_apply, Matrix.smul_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · apply Complex.ext <;> simp [h, hc, ScalarSem.toFloatMachine, exactSem, decodeComplex,
      div_eq_inv_mul]
  · have h0 : (A i i).2 = 0 := by linarith [him i i]
    apply Complex.ext <;> simp [hc, ScalarSem.toFloatMachine, exactSem, decodeComplex,
      div_eq_inv_mul, h0]
  · apply Complex.ext <;> simp [h, not_lt.2 h.le, hc, ScalarSem.toFloatMachine, exactSem,
      decodeComplex, div_eq_inv_mul, hre i j, him i j]

/-- The exact Hermitian part: on exact real arithmetic, the scaled Hermitian part of a stored
matrix with decoding $\mathbf{A}$ by $c$ decodes to $c^{-1}(\mathbf{A} + \mathbf{A}^{\mathsf{H}})$,
for every $\mathbf{A}$. No printed source. -/
theorem decodeMatrix_hermAvg_toFloatMachine_exactSem (p : P) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (ℝ × ℝ)) (c : ℝ) :
    decodeMatrix id (((exactSem (P := P) (𝕜 := ℝ)).toFloatMachine p toNat mm qr unif
      normal).hermAvg A c) = c⁻¹ • (decodeMatrix id A + (decodeMatrix id A)ᴴ) := by
  by_cases hc : c = 0
  · subst hc
    have hd : (default : ℝ) = 0 := rfl
    ext i j
    simp [FloatMachine.hermAvg, FloatMachine.hermFrom, ScalarSem.toFloatMachine, exactSem,
      decodeMatrix, decodeComplex, Complex.ext_iff, hd]
  ext i j
  simp only [FloatMachine.hermAvg, FloatMachine.hermFrom, decodeMatrix, Matrix.map_apply,
    Matrix.of_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.conjTranspose_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · apply Complex.ext <;> simp [h, hc, ScalarSem.toFloatMachine, exactSem, decodeComplex,
      div_eq_inv_mul, Complex.conj_re, Complex.conj_im] <;> ring
  · apply Complex.ext <;> simp [hc, ScalarSem.toFloatMachine, exactSem, decodeComplex,
      div_eq_inv_mul, Complex.conj_re, Complex.conj_im] <;> ring
  · apply Complex.ext <;> simp [h, not_lt.2 h.le, hc, ScalarSem.toFloatMachine, exactSem,
      decodeComplex, div_eq_inv_mul, Complex.conj_re, Complex.conj_im] <;> ring

/-- The exact conjugate transpose: on exact real arithmetic, the stored conjugate transpose
of a stored matrix with decoding $\mathbf{A}$ decodes to $\mathbf{A}^{\mathsf{H}}$. No printed
source. -/
theorem decodeMatrix_conjTransposeMat_toFloatMachine_exactSem (p : P) {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) (ℝ × ℝ)) :
    decodeMatrix id (((exactSem (P := P) (𝕜 := ℝ)).toFloatMachine p toNat mm qr unif
      normal).conjTransposeMat A) = (decodeMatrix id A)ᴴ := by
  ext i j
  apply Complex.ext <;> simp [ScalarSem.toFloatMachine, FloatMachine.conjTransposeMat, exactSem,
    decodeMatrix, decodeComplex, Complex.conj_re, Complex.conj_im]

private lemma foldl_add_eq_add_map_sum {ι : Type*} (f : ι → ℝ) (l : List ι) (a : ℝ) :
    l.foldl (fun s i => s + f i) a = a + (l.map f).sum := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih => simp [ih, add_assoc]

/-- The exact real trace: on exact real arithmetic, the rounded trace of the real parts of a
stored matrix with decoding $\mathbf{A}$ is $\operatorname{Re}\operatorname{tr}\mathbf{A}$. No
printed source. -/
theorem traceRe_toFloatMachine_exactSem (p : P) {n : ℕ} (A : Matrix (Fin n) (Fin n) (ℝ × ℝ)) :
    ((exactSem (P := P) (𝕜 := ℝ)).toFloatMachine p toNat mm qr unif normal).traceRe A =
      (Matrix.trace (decodeMatrix id A)).re := by
  simp [FloatMachine.traceRe, ScalarSem.toFloatMachine, exactSem]
  rw [foldl_add_eq_add_map_sum, zero_add, Matrix.trace, Complex.re_sum, Fin.sum_univ_def]
  simp [decodeMatrix, decodeComplex, Matrix.diag]

/-- The exact max-modulus test: on exact real arithmetic, the test that every part of every
entry of a stored $m \times n$ matrix lies in $[\mathit{lo}, \mathit{hi}]$, by the machine's
comparisons, is true exactly when it does. No printed source. -/
theorem boxTest_toFloatMachine_exactSem_iff (p : P) {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) (ℝ × ℝ)) (lo hi : ℝ) :
    let M := (exactSem (P := P) (𝕜 := ℝ)).toFloatMachine p toNat mm qr unif normal
    ((List.finRange m).all fun i => (List.finRange n).all fun j =>
      M.le lo (A i j).1 && M.le (A i j).1 hi && M.le lo (A i j).2 && M.le (A i j).2 hi) = true ↔
      ∀ i j, lo ≤ (A i j).1 ∧ (A i j).1 ≤ hi ∧ lo ≤ (A i j).2 ∧ (A i j).2 ≤ hi := by
  simp [List.all_eq_true, List.mem_finRange, Bool.and_eq_true, ScalarSem.toFloatMachine,
    exactSem, and_assoc]

/-- The exact entrywise sum: on exact real arithmetic, adding the real and imaginary parts
of two stored matrices with the machine's addition decodes to the sum of the decodings. No
printed source. -/
theorem decodeMatrix_addParts_toFloatMachine_exactSem (p : P) {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) (ℝ × ℝ)) :
    let M := (exactSem (P := P) (𝕜 := ℝ)).toFloatMachine p toNat mm qr unif normal
    decodeMatrix id (Matrix.of fun i j => (M.add (A i j).1 (B i j).1, M.add (A i j).2 (B i j).2)) =
      decodeMatrix id A + decodeMatrix id B := by
  ext i j
  apply Complex.ext <;> simp [ScalarSem.toFloatMachine, exactSem, decodeMatrix, decodeComplex]

/-- The exact entrywise difference: on exact real arithmetic, subtracting the real and
imaginary parts of two stored matrices with the machine's subtraction decodes to the difference
of the decodings. No printed source. -/
theorem decodeMatrix_subParts_toFloatMachine_exactSem (p : P) {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) (ℝ × ℝ)) :
    let M := (exactSem (P := P) (𝕜 := ℝ)).toFloatMachine p toNat mm qr unif normal
    decodeMatrix id (Matrix.of fun i j => (M.sub (A i j).1 (B i j).1, M.sub (A i j).2 (B i j).2)) =
      decodeMatrix id A - decodeMatrix id B := by
  ext i j
  apply Complex.ext <;> simp [ScalarSem.toFloatMachine, exactSem, decodeMatrix, decodeComplex]

/-- The exact real scaling: on exact real arithmetic, multiplying both parts of every entry of
a stored matrix with decoding $\mathbf{A}$ by a stored real $a$ decodes to $a\mathbf{A}$. No
printed source. -/
theorem decodeMatrix_mulParts_toFloatMachine_exactSem (p : P) {m n : ℕ} (a : ℝ)
    (A : Matrix (Fin m) (Fin n) (ℝ × ℝ)) :
    let M := (exactSem (P := P) (𝕜 := ℝ)).toFloatMachine p toNat mm qr unif normal
    decodeMatrix id (Matrix.of fun i j => (M.mul a (A i j).1, M.mul a (A i j).2)) =
      a • decodeMatrix id A := by
  ext i j
  apply Complex.ext <;> simp [ScalarSem.toFloatMachine, exactSem, decodeMatrix, decodeComplex]

end NLAlib.Computation
