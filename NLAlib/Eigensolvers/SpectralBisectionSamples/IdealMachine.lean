/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SpectralBisectionTape
public import NLAlib.RandomMatrix.Tape
public import NLAlib.Eigensolvers.SpectralBisection

/-!
# The ideal machine of spectral bisection

The machine of a semantics with the samplers of the tape rounding meets
`NLAlib.FloatMachine.IsAccurate`, and its samplers have countable ranges and measurable fibres: the
hypotheses under which the shallow theorems on `NLAlib.eigh` apply to the ideal machine.

## Main results

* `NLAlib.Computation.isUnifSampler_uniformUnif`, `NLAlib.Computation.isAccurate_eighIdealMachine`:
  the machine contract.
* `NLAlib.Computation.isAccurate_eighIdealMachine_floor`: the machine contract in the floor model
  of a bounded format.
* `NLAlib.Computation.countable_range_uniformUnif`,
  `NLAlib.Computation.countable_range_gaussianNormal`: countable ranges.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

open scoped Matrix

namespace NLAlib.Computation

variable {P K : Type} [Inhabited K]

/-! ### The ideal machine -/

/-- The uniform shift of a tape rounding meets the uniform-sampler contract: if `sem` meets the
standard model at $u \ge 0$ with every value in range and `NLAlib.Computation.MulShrinks`, and the
rounding $\rho$ of a seed $v \in [-1, 1]$ errs by at most $c\,u\lvert v \rvert$ and stays in
$[-1, 1]$, then `NLAlib.Computation.ScalarSem.uniformUnif` of $\rho$ meets `NLAlib.IsUnifSampler`
at unit roundoff $(c + 1)u$ and floor $0$. No printed source. -/
theorem isUnifSampler_uniformUnif {sem : ScalarSem P K} {dec : P → K → ℝ} {u c : ℝ}
    (hsem : IsRelErrSem (fun _ => u) dec (fun _ _ => True) sem) (hmul : MulShrinks dec sem)
    (p : P) {ρ : ℝ → K} (hρ : ∀ v : ℝ, |v| ≤ 1 → |dec p (ρ v) - v| ≤ c * u * |v|)
    (hρI : ∀ v ∈ Set.Icc (-1 : ℝ) 1, dec p (ρ v) ∈ Set.Icc (-1 : ℝ) 1) (hu : 0 ≤ u) (hc : 0 ≤ c) :
    IsUnifSampler (dec p) ((c + 1) * u) 0 (sem.uniformUnif p ρ) := by
  intro s v hs hv
  have hrI : |dec p (ρ v)| ≤ 1 := abs_le.mpr (hρI v hv)
  have hvabs : |v| ≤ 1 := abs_le.mpr hv
  obtain ⟨z', hz'⟩ := hsem.bin_ok p .mul s (ρ v) trivial (fun h => by cases h) trivial
  obtain ⟨δ, hδ, hzd⟩ := hsem.bin_err p .mul s (ρ v) z' trivial hz'
  have hmz := hmul p s (ρ v) z' hz' hrI
  have hzeq : sem.uniformUnif p ρ s v = z' := by
    change (sem.bin p .mul s (ρ v)).getD default = z'
    rw [hz']; rfl
  rw [hzeq, max_eq_left hs]
  rw [abs_of_nonneg hs] at hmz
  simp only [BinOp.realOp] at hzd
  refine ⟨hmz, ?_⟩
  rw [hzd]
  have key : dec p s * v - dec p s * dec p (ρ v) * (1 + δ) =
      dec p s * (v - dec p (ρ v)) - dec p s * dec p (ρ v) * δ := by ring
  have hvr : |v - dec p (ρ v)| ≤ c * u * |v| := by
    rw [abs_sub_comm]; exact hρ v hvabs
  have hrδ : |dec p (ρ v)| * |δ| ≤ u := by
    calc |dec p (ρ v)| * |δ| ≤ 1 * u := mul_le_mul hrI hδ (abs_nonneg _) zero_le_one
      _ = u := one_mul u
  rw [key]
  calc |dec p s * (v - dec p (ρ v)) - dec p s * dec p (ρ v) * δ|
      ≤ |dec p s * (v - dec p (ρ v))| + |dec p s * dec p (ρ v) * δ| := abs_sub _ _
    _ = dec p s * |v - dec p (ρ v)| + dec p s * (|dec p (ρ v)| * |δ|) := by
        simp only [abs_mul, abs_of_nonneg hs, mul_assoc]
    _ ≤ dec p s * (c * u * |v|) + dec p s * u :=
        add_le_add (mul_le_mul_of_nonneg_left hvr hs) (mul_le_mul_of_nonneg_left hrδ hs)
    _ ≤ (c + 1) * u * dec p s := by
        nlinarith [mul_le_mul_of_nonneg_left hvabs (mul_nonneg (mul_nonneg hs hc) hu)]

/-- The ideal machine is accurate: if `sem` meets the standard model at $u \ge 0$ with every
value in range, exact literals up to $2$, the exact floor conversion and
`NLAlib.Computation.MulShrinks`, the routines meet `NLAlib.IsMatMulErr` and `NLAlib.IsQRErr` at $u$,
floor $0$, range $\Omega$, and the tape rounding $\rho$ meets `NLAlib.Computation.IsTapeRounding` at
$u$, floor $0$, range $2\Omega$, constants $c(d) \ge 0$, with $(c(\mathrm{gaussian}) + 3)u \le 1/10$
and the tape range covering the seeds ($1 \le 2\Omega$; without it the tape contract does not
constrain the rounding of a seed), then the machine of the semantics with the conversion of the
semantics, the routines and the samplers of $\rho$ at position $0$ meets
`NLAlib.FloatMachine.IsAccurate` at the unit roundoff $u_{\mathrm M} = (c(\mathrm{uniform}) + 1)u$,
floor $0$, range $\Omega$ and normal-sampler constant $2(c(\mathrm{gaussian}) + 3)$. No printed
source. -/
theorem isAccurate_eighIdealMachine {sem : ScalarSem P K} {dec : P → K → ℝ} {u Ω : ℝ}
    {μM μQ : ℕ → ℝ} {c : Dist → ℝ} (hsem : IsRelErrSem (fun _ => u) dec (fun _ _ => True) sem)
    (hlit : IsExactIntLit dec sem 2) (htn : IsExactToNat dec sem) (hmul : MulShrinks dec sem)
    (p : P) {mm : MatMulMap (K × K)} {qr : QRMap (K × K)}
    (hmm : IsMatMulErr (decodeComplex (dec p)) u 0 Ω μM mm)
    (hqr : IsQRErr (decodeComplex (dec p)) u 0 Ω μQ qr) {ρ : Dist → ℕ → ℝ → K}
    (hρ : IsTapeRounding dec p u 0 (2 * Ω) c ρ) (hΩ : 1 ≤ 2 * Ω) (hu : 0 ≤ u) (hcu : 0 ≤ c .uniform)
    (hcg : 0 ≤ c .gaussian) (hcgu : (c .gaussian + 3) * u ≤ 1 / 10) (hμM : ∀ d, 0 ≤ μM d)
    (hμQ : ∀ d, 0 ≤ μQ d) :
    (sem.toFloatMachine p (fun x => (sem.toNat p x).getD 0) mm qr
      (sem.uniformUnif p (ρ .uniform 0)) (sem.gaussianNormal p (ρ .gaussian 0))).IsAccurate
        (dec p) ((c .uniform + 1) * u) 0 Ω μM μQ (2 * (c .gaussian + 3)) := by
  have huM : u ≤ (c .uniform + 1) * u := by nlinarith [mul_nonneg hcu hu]
  have hu' : 0 ≤ (c .uniform + 1) * u := mul_nonneg (by linarith) hu
  have hconv : (fun x => (sem.toNat p x).getD 0) = fun x => ⌊dec p x⌋₊ :=
    funext fun x => by
      rw [htn p x]
      split_ifs with h0
      · rfl
      · exact (Nat.floor_eq_zero.mpr (by linarith [not_le.mp h0])).symm
  have hsem' : IsRelErrSem (fun _ => (c .uniform + 1) * u) dec (fun _ _ => True) sem :=
    hsem.mono fun _ => huM
  have hlit' : IsExactIntLit dec sem 1 := fun p k hk => hlit p k (hk.trans (by norm_num))
  have hmm' : IsMatMulErr (decodeComplex (dec p)) ((c .uniform + 1) * u) 0 Ω μM mm :=
    { specNorm_mul_sub_le := fun A B hAB =>
        (hmm.specNorm_mul_sub_le A B hAB).trans
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left huM (hμM _))
            (le_max_right _ _))
      isHermitian_of_map_eq_conjTranspose := hmm.isHermitian_of_map_eq_conjTranspose }
  have hqr' : IsQRErr (decodeComplex (dec p)) ((c .uniform + 1) * u) 0 Ω μQ qr := fun A hA =>
    let h := hqr A hA
    ⟨h.1, h.2.choose, h.2.choose_spec.1,
      h.2.choose_spec.2.1.trans (mul_le_mul_of_nonneg_left huM (hμQ _)),
      h.2.choose_spec.2.2.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left huM (hμQ _)) (le_max_right _ _))⟩
  have hρU : ∀ v : ℝ, |v| ≤ 1 → |dec p (ρ .uniform 0 v) - v| ≤ c .uniform * u * |v| := by
    intro v hv
    have h := hρ.1 .uniform 0 v (hv.trans hΩ)
    rwa [max_eq_left (abs_nonneg v)] at h
  have hunif : IsUnifSampler (dec p) ((c .uniform + 1) * u) 0 (sem.uniformUnif p (ρ .uniform 0)) :=
    isUnifSampler_uniformUnif hsem hmul p hρU (fun v hv => hρ.2 0 v hv) hu hcu
  have hρG : ∀ x : ℝ, |x| ≤ 2 * Ω → |dec p (ρ .gaussian 0 x) - x| ≤ c .gaussian * u * |x| := by
    intro x hx
    have h := hρ.1 .gaussian 0 x hx
    rwa [max_eq_left (abs_nonneg x)] at h
  have hnorm : IsNormalSampler (decodeComplex (dec p)) u (2 * (c .gaussian + 3)) 0 Ω
      (sem.gaussianNormal p (ρ .gaussian 0)) :=
    isNormalSampler_gaussianNormal hsem hlit p hρG hcg hu hcgu
  have hnorm' : IsNormalSampler (decodeComplex (dec p)) ((c .uniform + 1) * u)
      (2 * (c .gaussian + 3)) 0 Ω (sem.gaussianNormal p (ρ .gaussian 0)) := fun z hz =>
    (hnorm z hz).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left huM (by linarith)) (le_max_right _ _))
  rw [hconv]
  exact isAccurate_toFloatMachine Ω hsem' hlit' p hmm' hqr' hunif hnorm'

/-! ### The ideal machine in the floor model -/

/-- The uniform shift of a tape rounding in the floor model meets the uniform-sampler contract
at unit roundoff $(c + 1)u$ and floor $\tau \le 1$ (helper of
`NLAlib.Computation.isAccurate_eighIdealMachine_floor`). -/
private theorem isUnifSampler_uniformUnif_floor {sem : ScalarSem P K} {dec : P → K → ℝ}
    {u τ c Ω' : ℝ}
    (hsem : IsFloorRelErrSem (fun _ => u) (fun _ => τ) dec (fun _ a => |a| ≤ Ω') sem)
    (hmul : MulShrinks dec sem) (p : P) (hrange : ∀ x : K, |dec p x| ≤ Ω') {ρ : ℝ → K}
    (hρ : ∀ v : ℝ, |v| ≤ 1 → |dec p (ρ v) - v| ≤ c * u * max |v| τ)
    (hρI : ∀ v ∈ Set.Icc (-1 : ℝ) 1, dec p (ρ v) ∈ Set.Icc (-1 : ℝ) 1) (hu : 0 ≤ u) (hc : 0 ≤ c)
    (hτ : τ ≤ 1) : IsUnifSampler (dec p) ((c + 1) * u) τ (sem.uniformUnif p ρ) := by
  intro s v hs hv
  have hrI : |dec p (ρ v)| ≤ 1 := abs_le.mpr (hρI v hv)
  have hvabs : |v| ≤ 1 := abs_le.mpr hv
  have hsr : |dec p s * dec p (ρ v)| ≤ dec p s := by
    rw [abs_mul, abs_of_nonneg hs]
    exact mul_le_of_le_one_right hs hrI
  obtain ⟨z', hz'⟩ := hsem.bin_ok p .mul s (ρ v) trivial (fun h => by cases h)
    (hsr.trans ((le_abs_self _).trans (hrange s)))
  have hzd := hsem.bin_err p .mul s (ρ v) z' trivial hz'
  have hmz := hmul p s (ρ v) z' hz' hrI
  have hzeq : sem.uniformUnif p ρ s v = z' := by
    change (sem.bin p .mul s (ρ v)).getD default = z'
    rw [hz']; rfl
  simp only [BinOp.realOp] at hzd
  rw [hzeq]
  rw [abs_of_nonneg hs] at hmz
  refine ⟨hmz, ?_⟩
  set m := max (dec p s) τ
  have hm1 : u * max |dec p s * dec p (ρ v)| τ ≤ u * m :=
    mul_le_mul_of_nonneg_left (max_le_max hsr le_rfl) hu
  have hm2 : dec p s * |v - dec p (ρ v)| ≤ c * u * m := by
    rw [abs_sub_comm]
    calc dec p s * |dec p (ρ v) - v| ≤ dec p s * (c * u * max |v| τ) :=
          mul_le_mul_of_nonneg_left (hρ v hvabs) hs
      _ = c * u * (dec p s * max |v| τ) := by ring
      _ ≤ c * u * m := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hc hu)
          exact (mul_le_of_le_one_right hs (max_le hvabs hτ)).trans (le_max_left _ _)
  have key : dec p s * v - dec p z' =
      dec p s * (v - dec p (ρ v)) + (dec p s * dec p (ρ v) - dec p z') := by ring
  rw [key]
  calc |dec p s * (v - dec p (ρ v)) + (dec p s * dec p (ρ v) - dec p z')|
      ≤ |dec p s * (v - dec p (ρ v))| + |dec p s * dec p (ρ v) - dec p z'| := abs_add_le _ _
    _ ≤ c * u * m + u * m := by
        rw [abs_mul, abs_of_nonneg hs]
        exact add_le_add hm2 (hzd.trans hm1)
    _ = (c + 1) * u * m := by ring

/-- In the floor model, the stored $\sqrt{1/2}$ decodes to $\sigma/\sqrt2\,(1 + \delta)$ with
$\lvert\sigma - 1\rvert \le u$ and $\lvert\delta\rvert \le u$, for a floor $\tau \le 1/2$ and a
range containing $1$ (helper of `NLAlib.Computation.isAccurate_eighIdealMachine_floor`). -/
private theorem sqrtHalf_floor {sem : ScalarSem P K} {dec : P → K → ℝ} {u τ Ω' : ℝ}
    (hsem : IsFloorRelErrSem (fun _ => u) (fun _ => τ) dec (fun _ a => |a| ≤ Ω') sem)
    (hlit : IsExactIntLit dec sem 2) (p : P) (hu : 0 ≤ u) (hu1 : u ≤ 1 / 10) (hτ : τ ≤ 1 / 2)
    (hΩ₁ : 1 ≤ Ω') :
    ∃ σ : ℝ, 0 ≤ σ ∧ |σ - 1| ≤ u ∧ ∃ δ : ℝ, |δ| ≤ u ∧
      dec p (sem.sqrtHalf p) = σ / √2 * (1 + δ) := by
  obtain ⟨z1, hz1, hd1⟩ := hlit p 1 (by norm_num)
  obtain ⟨z2, hz2, hd2⟩ := hlit p 2 le_rfl
  simp only [Nat.cast_one] at hz1 hd1
  have hhalf : BinOp.div.realOp (dec p z1) (dec p z2) = 1 / 2 := by
    simp only [BinOp.realOp, hd1, hd2]; norm_num
  obtain ⟨z3, hz3⟩ := hsem.bin_ok p .div z1 z2 trivial (fun _ => by rw [hd2]; norm_num)
    (by rw [hhalf]; norm_num; linarith)
  have he3 := hsem.bin_err p .div z1 z2 z3 trivial hz3
  rw [hhalf, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), max_eq_left (by linarith)] at he3
  set δ2 := 2 * dec p z3 - 1
  have hδ2 : |δ2| ≤ u := by
    have : δ2 = -(2 * (1 / 2 - dec p z3)) := by ring
    rw [this, abs_neg, abs_mul, abs_two]; linarith
  have hz3' : dec p z3 = (1 + δ2) / 2 := by ring
  have hb := abs_le.mp hδ2
  have hpos : 0 ≤ 1 + δ2 := by linarith [hb.1]
  have h3le : dec p z3 ≤ 1 := by rw [hz3']; linarith [hb.2]
  have h3ge : 1 / 4 ≤ dec p z3 := by rw [hz3']; linarith [hb.1]
  have hsq1 : √(dec p z3) ≤ 1 := Real.sqrt_le_one.mpr h3le
  have hsq2 : 1 / 2 ≤ √(dec p z3) := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
  obtain ⟨z4, hz4⟩ := hsem.sqrt_ok p z3 (by linarith)
    (by rw [abs_of_nonneg (Real.sqrt_nonneg _)]; linarith)
  have he4 := hsem.sqrt_err p z3 z4 hz4
  rw [max_eq_left (hτ.trans hsq2)] at he4
  obtain ⟨δ3, hδ3, hd4⟩ : RelErr u (√(dec p z3)) (dec p z4) :=
    AbsRelErr.relErr (by
      change |_ - _| ≤ u * |_| + 0
      rwa [add_zero, abs_of_nonneg (Real.sqrt_nonneg _)]) hu
  have hs : dec p (sem.sqrtHalf p) = dec p z4 := by
    unfold ScalarSem.sqrtHalf
    simp only [hz1, hz2, hz3, hz4, Option.getD_some]
  have h2 := Real.sq_sqrt hpos
  have hs0 := Real.sqrt_nonneg (1 + δ2)
  refine ⟨√(1 + δ2), hs0, ?_, δ3, hδ3, ?_⟩
  · rw [abs_le]
    constructor <;> nlinarith
  · rw [hs, hd4, hz3', Real.sqrt_div hpos]

/-- The real part (or imaginary part) of the normal sampler of a tape rounding in the floor
model: the stored product of the rounded draw $\rho(\sqrt2 w)$ and the stored $\sqrt{1/2}$ is
within $2(c + 3)u\max(\lvert w\rvert, \tau)$ of $w$ (helper of
`NLAlib.Computation.isAccurate_eighIdealMachine_floor`). -/
private theorem gaussianNormal_part_floor {sem : ScalarSem P K} {dec : P → K → ℝ}
    {u τ c Ω' : ℝ}
    (hsem : IsFloorRelErrSem (fun _ => u) (fun _ => τ) dec (fun _ a => |a| ≤ Ω') sem) (p : P)
    (hrange : ∀ x : K, |dec p x| ≤ Ω') {ρ : ℝ → K}
    (hρ : ∀ x : ℝ, |x| ≤ Ω' → |dec p (ρ x) - x| ≤ c * u * max |x| τ) (hc : 0 ≤ c) (hu : 0 ≤ u)
    (hcu : (c + 3) * u ≤ 1 / 10) {σ δ3 : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : |σ - 1| ≤ u)
    (hδ3 : |δ3| ≤ u) (hs : dec p (sem.sqrtHalf p) = σ / √2 * (1 + δ3)) (w : ℝ)
    (hw : |√2 * w| ≤ Ω') :
    ∃ r : K, sem.bin p .mul (ρ (√2 * w)) (sem.sqrtHalf p) = some r ∧
      |dec p r - w| ≤ 2 * ((c + 3) * u) * max |w| τ := by
  have hu1 : u ≤ 1 / 30 := by nlinarith
  have hcu1 : c * u ≤ 1 / 10 := by nlinarith
  have h2 : (0 : ℝ) < √2 := by positivity
  have h22 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h2ge : (11 / 10 : ℝ) ≤ √2 := by nlinarith
  set g := σ * (1 + δ3) with hg_def
  have hσb := abs_le.mp hσ1
  have hδb := abs_le.mp hδ3
  have hg : |g - 1| ≤ 3 * u := by
    rw [abs_le]; constructor <;> nlinarith
  have hg0 : 0 ≤ g := mul_nonneg hσ0 (by linarith)
  have hg1 : g ≤ 1 + 3 * u := by linarith [(abs_le.mp hg).2]
  have hsg : dec p (sem.sqrtHalf p) = g / √2 := by rw [hs, hg_def]; ring
  have hsh : |dec p (sem.sqrtHalf p)| ≤ 1 := by
    rw [hsg, abs_div, abs_of_nonneg hg0, abs_of_pos h2, div_le_one h2]; linarith
  set X := dec p (ρ (√2 * w)) with hX_def
  set m := max |w| τ with hm_def
  have hm0 : 0 ≤ m := (abs_nonneg w).trans (le_max_left _ _)
  have hmax : max |√2 * w| τ ≤ √2 * m := by
    refine max_le ?_ ((le_max_right _ _).trans (le_mul_of_one_le_left hm0 (by linarith)))
    rw [abs_mul, abs_of_pos h2]
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) h2.le
  have he1 : |X - √2 * w| ≤ c * u * (√2 * m) :=
    (hρ _ hw).trans (mul_le_mul_of_nonneg_left hmax (mul_nonneg hc hu))
  obtain ⟨r, hr⟩ := hsem.bin_ok p .mul _ _ trivial (fun h => nomatch h) (by
    change |X * dec p (sem.sqrtHalf p)| ≤ Ω'
    rw [abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg _) hsh).trans (hrange _))
  refine ⟨r, hr, ?_⟩
  have hrerr := hsem.bin_err p .mul _ _ r trivial hr
  change |X * dec p (sem.sqrtHalf p) - dec p r| ≤ u * max |X * dec p (sem.sqrtHalf p)| τ
    at hrerr
  set a := X * dec p (sem.sqrtHalf p) with ha_def
  set E := 3 * u * m + c * u * (1 + 3 * u) * m with hE_def
  have ha : a - w = w * (g - 1) + (X - √2 * w) * (g / √2) := by
    rw [ha_def, hsg]; field_simp; ring
  have hE : |a - w| ≤ E := by
    rw [ha]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, mul_comm]
      exact mul_le_mul hg (le_max_left _ _) (abs_nonneg _) (by linarith)
    · rw [abs_mul, abs_div, abs_of_nonneg hg0, abs_of_pos h2]
      calc |X - √2 * w| * (g / √2) ≤ c * u * (√2 * m) * ((1 + 3 * u) / √2) :=
            mul_le_mul he1 (div_le_div_of_nonneg_right hg1 h2.le) (by positivity)
              (by positivity)
        _ = c * u * (1 + 3 * u) * m := by field_simp
  have hA : max |a| τ ≤ m + E := by
    refine max_le ?_ ((le_max_right _ _).trans (le_add_of_nonneg_right (by positivity)))
    have : |a| ≤ |w| + |a - w| := by
      have := abs_add_le w (a - w); rwa [add_sub_cancel] at this
    linarith [le_max_left |w| τ]
  have hk : u * (m + E) + E ≤ 2 * ((c + 3) * u) * m := by
    have hk0 : u + u * (3 * u + c * u * (1 + 3 * u)) + (3 * u + c * u * (1 + 3 * u)) ≤
        2 * ((c + 3) * u) := by
      nlinarith [mul_nonneg hc hu, mul_nonneg (mul_nonneg hc hu) hu]
    have : u * (m + E) + E =
        (u + u * (3 * u + c * u * (1 + 3 * u)) + (3 * u + c * u * (1 + 3 * u))) * m := by
      rw [hE_def]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hk0 hm0
  calc |dec p r - w| = |(a - w) - (a - dec p r)| := by ring_nf
    _ ≤ |a - w| + |a - dec p r| := abs_sub _ _
    _ ≤ E + u * (m + E) := add_le_add hE (hrerr.trans (mul_le_mul_of_nonneg_left hA hu))
    _ ≤ 2 * ((c + 3) * u) * m := by linarith

/-- The normal sampler of a tape rounding in the floor model meets the normal-sampler contract
at $u$, constant $3(c + 3)$, floor $\tau$ and range $\Omega$, when the tape and the semantics
cover the range $\Omega' \ge 2\Omega$ (helper of
`NLAlib.Computation.isAccurate_eighIdealMachine_floor`). -/
private theorem isNormalSampler_gaussianNormal_floor {sem : ScalarSem P K} {dec : P → K → ℝ}
    {u τ c Ω Ω' : ℝ}
    (hsem : IsFloorRelErrSem (fun _ => u) (fun _ => τ) dec (fun _ a => |a| ≤ Ω') sem)
    (hlit : IsExactIntLit dec sem 2) (p : P) (hrange : ∀ x : K, |dec p x| ≤ Ω') {ρ : ℝ → K}
    (hρ : ∀ x : ℝ, |x| ≤ Ω' → |dec p (ρ x) - x| ≤ c * u * max |x| τ) (hΩ : 2 * Ω ≤ Ω')
    (hΩ₁ : 1 ≤ Ω') (hτ : τ ≤ 1 / 2) (hc : 0 ≤ c) (hu : 0 ≤ u) (hcu : (c + 3) * u ≤ 1 / 10) :
    IsNormalSampler (decodeComplex (dec p)) u (3 * (c + 3)) τ Ω (sem.gaussianNormal p ρ) := by
  obtain ⟨σ, hσ0, hσ1, δ3, hδ3, hs⟩ := sqrtHalf_floor hsem hlit p hu (by nlinarith) hτ hΩ₁
  intro z hz
  have hsq : ∀ x : ℝ, |x| ≤ ‖z‖ → |√2 * x| ≤ Ω' := by
    intro x hx
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg 2)]
    have h2 : √2 ≤ 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    nlinarith [mul_le_mul_of_nonneg_left (hx.trans hz) (Real.sqrt_nonneg 2), norm_nonneg z]
  obtain ⟨r1, h1, e1⟩ := gaussianNormal_part_floor hsem p hrange hρ hc hu hcu hσ0 hσ1 hδ3 hs
    z.re (hsq _ (Complex.abs_re_le_norm z))
  obtain ⟨r2, h2, e2⟩ := gaussianNormal_part_floor hsem p hrange hρ hc hu hcu hσ0 hσ1 hδ3 hs
    z.im (hsq _ (Complex.abs_im_le_norm z))
  simp only [ScalarSem.gaussianNormal, h1, h2, Option.getD_some]
  set K₀ := 2 * ((c + 3) * u) with hK₀
  set M := max ‖z‖ τ with hM
  have hK : 0 ≤ K₀ := by positivity
  have hM0 : 0 ≤ M := (norm_nonneg z).trans (le_max_left _ _)
  have hre : max |z.re| τ ≤ M := max_le_max (Complex.abs_re_le_norm z) le_rfl
  have him : max |z.im| τ ≤ M := max_le_max (Complex.abs_im_le_norm z) le_rfl
  have hd : ‖z - decodeComplex (dec p) (r1, r2)‖ ^ 2
      = (z.re - dec p r1) ^ 2 + (z.im - dec p r2) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [decodeComplex]
    ring
  have q1 : (z.re - dec p r1) ^ 2 ≤ (K₀ * M) ^ 2 := by
    rw [sq_le_sq, abs_sub_comm, abs_of_nonneg (mul_nonneg hK hM0)]
    exact e1.trans (mul_le_mul_of_nonneg_left hre hK)
  have q2 : (z.im - dec p r2) ^ 2 ≤ (K₀ * M) ^ 2 := by
    rw [sq_le_sq, abs_sub_comm, abs_of_nonneg (mul_nonneg hK hM0)]
    exact e2.trans (mul_le_mul_of_nonneg_left him hK)
  have key : ‖z - decodeComplex (dec p) (r1, r2)‖ ^ 2 ≤ (3 * (c + 3) * u * M) ^ 2 := by
    rw [hd]
    have : (3 * (c + 3) * u * M) ^ 2 = 9 / 4 * (K₀ * M) ^ 2 := by rw [hK₀]; ring
    rw [this]
    nlinarith [sq_nonneg (K₀ * M)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp key

/-- The ideal machine is accurate in the floor model: let `sem` meet the floor model
`NLAlib.Computation.IsFloorRelErrSem` at unit roundoff $u \ge 0$, floor $\tau \le 1/2$ and range
condition $\lvert a\rvert \le \Omega'$, with exact literals up to $2$, the exact floor
conversion and `NLAlib.Computation.MulShrinks`, and let every stored value at tag `p` decode
into $[-\Omega', \Omega']$; let the routines meet `NLAlib.IsMatMulErr` and `NLAlib.IsQRErr` at
$u$, floor $\tau$, range $\Omega$, and the tape rounding $\rho$ meet
`NLAlib.Computation.IsTapeRounding` at $u$, floor $\tau$, range $\Omega'$, constants
$c(d) \ge 0$, with $(c(\mathrm{gaussian}) + 3)u \le 1/10$, $2\Omega \le \Omega'$ (a complex
draw of modulus $\Omega$ has real draws up to $\sqrt2\,\Omega$) and $1 \le \Omega'$ (the tape
range covers the seeds). Then the machine of the semantics with the conversion of the
semantics, the routines and the samplers of $\rho$ at position $0$ meets
`NLAlib.FloatMachine.IsAccurate` at the unit roundoff $u_{\mathrm M} = (c(\mathrm{uniform}) +
1)u$, floor $\tau$, range $\Omega$ and normal-sampler constant $3(c(\mathrm{gaussian}) + 3)$.
No printed source. -/
theorem isAccurate_eighIdealMachine_floor {sem : ScalarSem P K} {dec : P → K → ℝ}
    {u τ Ω Ω' : ℝ} {μM μQ : ℕ → ℝ} {c : Dist → ℝ}
    (hsem : IsFloorRelErrSem (fun _ => u) (fun _ => τ) dec (fun _ a => |a| ≤ Ω') sem)
    (hlit : IsExactIntLit dec sem 2) (htn : IsExactToNat dec sem) (hmul : MulShrinks dec sem)
    (p : P) (hrange : ∀ x : K, |dec p x| ≤ Ω') {mm : MatMulMap (K × K)} {qr : QRMap (K × K)}
    (hmm : IsMatMulErr (decodeComplex (dec p)) u τ Ω μM mm)
    (hqr : IsQRErr (decodeComplex (dec p)) u τ Ω μQ qr) {ρ : Dist → ℕ → ℝ → K}
    (hρ : IsTapeRounding dec p u τ Ω' c ρ) (hΩ : 2 * Ω ≤ Ω') (hΩ₁ : 1 ≤ Ω') (hu : 0 ≤ u)
    (hτ : τ ≤ 1 / 2) (hcu : 0 ≤ c .uniform) (hcg : 0 ≤ c .gaussian)
    (hcgu : (c .gaussian + 3) * u ≤ 1 / 10) (hμM : ∀ d, 0 ≤ μM d) (hμQ : ∀ d, 0 ≤ μQ d) :
    (sem.toFloatMachine p (fun x => (sem.toNat p x).getD 0) mm qr
      (sem.uniformUnif p (ρ .uniform 0)) (sem.gaussianNormal p (ρ .gaussian 0))).IsAccurate
        (dec p) ((c .uniform + 1) * u) τ Ω μM μQ (3 * (c .gaussian + 3)) := by
  have huM : u ≤ (c .uniform + 1) * u := by nlinarith [mul_nonneg hcu hu]
  have hΩΩ : ∀ a : ℝ, |a| ≤ Ω → |a| ≤ Ω' := fun a ha => by linarith [abs_nonneg a]
  have rnd : ∀ (a : ℝ) (z : K), |a - dec p z| ≤ u * max |a| τ →
      IsRoundingOf ((c .uniform + 1) * u) τ Ω a (dec p z) := fun a z h _ =>
    h.trans (mul_le_mul_of_nonneg_right huM ((abs_nonneg a).trans (le_max_left _ _)))
  have hbin : ∀ (b : BinOp) (x y : K), b.IsArith → (b = .div → dec p y ≠ 0) →
      IsRoundingOf ((c .uniform + 1) * u) τ Ω (b.realOp (dec p x) (dec p y))
        (dec p ((sem.bin p b x y).getD default)) := by
    intro b x y hb hy ha
    obtain ⟨z, hz⟩ := hsem.bin_ok p b x y hb hy (hΩΩ _ ha)
    rw [hz, Option.getD_some]
    exact rnd _ z (hsem.bin_err p b x y z hb hz) ha
  have hunif := isUnifSampler_uniformUnif_floor hsem hmul p hrange
    (fun v hv => hρ.1 .uniform 0 v (hv.trans hΩ₁)) (fun v hv => hρ.2 0 v hv) hu hcu
    (by linarith)
  have hnormal := isNormalSampler_gaussianNormal_floor hsem hlit p hrange
    (fun x hx => hρ.1 .gaussian 0 x hx) hΩ hΩ₁ hτ hcg hu hcgu
  have hmax : ∀ (a : ℝ), 0 ≤ a → 0 ≤ max a τ := fun a ha => ha.trans (le_max_left _ _)
  exact
    { dec_zero := by
        obtain ⟨z, hz, hd⟩ := hlit p 0 (Nat.zero_le _)
        simp only [Nat.cast_zero] at hz hd
        change dec p ((sem.lit p 0).getD default) = 0
        rw [hz, Option.getD_some, hd]
      dec_one := by
        obtain ⟨z, hz, hd⟩ := hlit p 1 (by norm_num)
        simp only [Nat.cast_one] at hz hd
        change dec p ((sem.lit p 1).getD default) = 1
        rw [hz, Option.getD_some, hd]
      ofNat := fun k hk => by
        obtain ⟨z, hz⟩ := hsem.lit_ok p (k : ℚ) (by simpa using hΩΩ _ hk)
        have he := hsem.lit_err p (k : ℚ) z hz
        rw [Rat.cast_natCast] at he
        change |(k : ℝ) - dec p ((sem.lit p (k : ℚ)).getD default)| ≤ _
        rw [hz, Option.getD_some]
        exact rnd _ z he hk
      add := fun x y => hbin .add x y trivial (fun h => nomatch h)
      sub := fun x y => hbin .sub x y trivial (fun h => nomatch h)
      mul := fun x y => hbin .mul x y trivial (fun h => nomatch h)
      div := fun x y hy => hbin .div x y trivial (fun _ => hy)
      dec_neg := fun x => by
        obtain ⟨z, hz, hd⟩ := hsem.neg p x
        change dec p ((sem.un p .neg x).getD default) = -dec p x
        rw [hz, Option.getD_some, hd]
      le_iff := fun x y => by
        change (sem.cmp p .le x y).getD false = true ↔ dec p x ≤ dec p y
        rw [hsem.cmp_le p x y]
        simp
      toNat_eq := fun x => by
        change (sem.toNat p x).getD 0 = ⌊dec p x⌋₊
        rw [htn p x]
        split_ifs with h0
        · rfl
        · exact (Nat.floor_eq_zero.mpr (by linarith [not_le.mp h0])).symm
      isMatMulErr :=
        { specNorm_mul_sub_le := fun A B hAB =>
            (hmm.specNorm_mul_sub_le A B hAB).trans
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left huM (hμM _))
                (hmax _ (mul_nonneg (specNorm_nonneg _) (specNorm_nonneg _))))
          isHermitian_of_map_eq_conjTranspose := hmm.isHermitian_of_map_eq_conjTranspose }
      isQRErr := fun A hA =>
        let h := hqr A hA
        ⟨h.1, h.2.choose, h.2.choose_spec.1,
          h.2.choose_spec.2.1.trans (mul_le_mul_of_nonneg_left huM (hμQ _)),
          h.2.choose_spec.2.2.trans (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left huM (hμQ _)) (hmax _ (specNorm_nonneg _)))⟩
      isUnifSampler := hunif
      isNormalSampler := fun z hz =>
        (hnormal z hz).trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left huM (by linarith)) (hmax _ (norm_nonneg z))) }

set_option linter.style.longLine false in
/-- The uniform shift of a rounding with countable range has countable ranges and measurable
fibres, as
`NLAlib.FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_hasLaw_eighSampleLaw`
asks of a machine's uniform sampler. No printed source. -/
theorem countable_range_uniformUnif (sem : ScalarSem P K) (p : P) {ρ : ℝ → K}
    (hc : (Set.range ρ).Countable) (hm : ∀ z, MeasurableSet (ρ ⁻¹' {z})) :
    (∀ s, (Set.range (sem.uniformUnif p ρ s)).Countable) ∧
      ∀ s z, MeasurableSet (sem.uniformUnif p ρ s ⁻¹' {z}) := by
  refine ⟨fun s => ?_, fun s z => ?_⟩
  · have hrange : Set.range (sem.uniformUnif p ρ s) =
        (fun w => (sem.bin p .mul s w).getD default) '' Set.range ρ := by
      rw [← Set.range_comp]; rfl
    rw [hrange]
    exact hc.image _
  · have hT : {w | w ∈ Set.range ρ ∧ (sem.bin p .mul s w).getD default = z}.Countable :=
      hc.mono fun w hw => hw.1
    have hset : sem.uniformUnif p ρ s ⁻¹' {z} =
        ⋃ w ∈ {w | w ∈ Set.range ρ ∧ (sem.bin p .mul s w).getD default = z}, ρ ⁻¹' {w} := by
      ext v
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_ofPred_eq,
        exists_prop]
      constructor
      · intro h
        exact ⟨ρ v, ⟨⟨v, rfl⟩, h⟩, rfl⟩
      · rintro ⟨w, ⟨_, hw⟩, hv⟩
        rw [← hv] at hw
        exact hw
    rw [hset]
    exact MeasurableSet.biUnion hT fun w _ => hm w

/-- The normal sampler of a rounding with countable range has a countable range and measurable
fibres. No printed source. -/
theorem countable_range_gaussianNormal (sem : ScalarSem P K) (p : P) {ρ : ℝ → K}
    (hc : (Set.range ρ).Countable) (hm : ∀ z, MeasurableSet (ρ ⁻¹' {z})) :
    (Set.range (sem.gaussianNormal p ρ)).Countable ∧
      ∀ z, MeasurableSet (sem.gaussianNormal p ρ ⁻¹' {z}) := by
  have hF : ∀ a : K, MeasurableSet
      {x : ℝ | (sem.bin p .mul (ρ x) (sem.sqrtHalf p)).getD default = a} := by
    intro a
    have hT : {w | w ∈ Set.range ρ ∧
        (sem.bin p .mul w (sem.sqrtHalf p)).getD default = a}.Countable :=
      hc.mono fun w hw => hw.1
    have hset : {x : ℝ | (sem.bin p .mul (ρ x) (sem.sqrtHalf p)).getD default = a} =
        ⋃ w ∈ {w | w ∈ Set.range ρ ∧
          (sem.bin p .mul w (sem.sqrtHalf p)).getD default = a}, ρ ⁻¹' {w} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff,
        exists_prop]
      constructor
      · intro h
        exact ⟨ρ x, ⟨⟨x, rfl⟩, h⟩, rfl⟩
      · rintro ⟨w, ⟨_, hw⟩, hx⟩
        rw [← hx] at hw
        exact hw
    rw [hset]
    exact MeasurableSet.biUnion hT fun w _ => hm w
  have hsub : Set.range (sem.gaussianNormal p ρ) ⊆
      (fun q : K × K => ((sem.bin p .mul q.1 (sem.sqrtHalf p)).getD default,
        (sem.bin p .mul q.2 (sem.sqrtHalf p)).getD default)) ''
        (Set.range ρ ×ˢ Set.range ρ) := by
    rintro _ ⟨z, rfl⟩
    exact ⟨(ρ (√2 * z.re), ρ (√2 * z.im)), ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩, rfl⟩
  refine ⟨((hc.prod hc).image _).mono hsub, fun z => ?_⟩
  have hset : sem.gaussianNormal p ρ ⁻¹' {z} =
      (fun x : ℂ => √2 * x.re) ⁻¹' {x : ℝ | (sem.bin p .mul (ρ x) (sem.sqrtHalf p)).getD default
          = z.1} ∩
        (fun x : ℂ => √2 * x.im) ⁻¹' {x : ℝ | (sem.bin p .mul (ρ x) (sem.sqrtHalf p)).getD default
          = z.2} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_ofPred_eq,
      ScalarSem.gaussianNormal, Prod.ext_iff]
  rw [hset]
  exact ((hF z.1).preimage (measurable_const.mul Complex.measurable_re)).inter
    ((hF z.2).preimage (measurable_const.mul Complex.measurable_im))

end NLAlib.Computation
