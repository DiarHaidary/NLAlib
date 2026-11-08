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
