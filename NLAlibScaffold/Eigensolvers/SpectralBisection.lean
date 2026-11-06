/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlibScaffold.Eigensolvers.RandomizedDeflation
public import NLAlibScaffold.Matrix.Computation.SpectralBisection
public import NLAlibScaffold.Probability.AdaptiveUnionBound
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import NLAlib.Computation.BinaryFloat

/-!
# Hermitian diagonalization in linear precision (scaffold)

Statements for a new file `NLAlib/Eigensolvers/SpectralBisection.lean` (stage HDIAG, wave W4,
design note `docs/design/Eigensolvers-HermitianDiagonalization.md` §3.9; the folder
`NLAlib/Eigensolvers` is open question OQ1). The main theorem ([Shah2024, Theorem 4.2]):
randomized spectral bisection (`NLAlib.eigh`) on a floating-point machine with black-box
multiplication and QR returns, with
probability at least $1 - \theta$, an approximate diagonalization with residual
$2\varepsilon R_0$ and $\mathbf{U}$ within $\varepsilon/3$ of unitary, using
$\log_2(1/\varepsilon) + O(\log n + \log\log(1/\varepsilon)) + \tfrac32\log_2(1/\theta)$ bits of
precision. The samples of the nodes are independent, each with the law `NLAlib.eighSampleLaw`
(a uniform seed on $[-1, 1]$ and two independent standard complex Gaussian matrices); the
computed samples are deterministic functions of them with countably many values, which is all the
probability argument needs about the algorithm's measurability.

## Main definitions

* `NLAlib.eighSampleLaw`.

## Main results

* `NLAlib.measureReal_exists_abs_sub_lt_le`: a random shift avoids the spectrum.
* `NLAlib.FloatMachine.IsAccurate.measure_not_isEighGoodSample_le`: the good events of a node.
* `NLAlib.countable_range_eighNodeAt`, `NLAlib.measurableSet_eighNodeAt_eq`,
  `NLAlib.indepFun_eighNodeAt_eq`: the nodes are computed from earlier samples.
* `NLAlib.FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le`: Theorem 4.2.
* `NLAlib.FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_logb_le`:
  its bit count.
*
`NLAlib.FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_exponentBits_le`:
  the bounded format, with $\log_2\log_2(n/(\varepsilon\theta)) + O(1)$ exponent bits.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder ENNReal

namespace NLAlib


/-- The **law of the ideal sample of a node**: a seed uniform on $[-1, 1]$ and two independent
standard complex Gaussian $N \times N$ matrices, independent of the seed. -/
noncomputable def eighSampleLaw (N : ℕ) : Measure (EighSample ℝ ℂ N) :=
  (ProbabilityTheory.cond volume (Set.Icc (-1 : ℝ) 1)).prod
    (Measure.pi fun _ : Bool => complexGaussianMatrix (Fin N) (Fin N))

/-- **A random shift avoids a finite set** (Event I): for a finite set $\Lambda$ of reals,
$c > 0$, $w \ge 0$ and $v$ uniform on $[-1, 1]$,
$$\mathbb{P}[\exists \lambda \in \Lambda,\ \lvert \lambda - cv \rvert < w] \le
\frac{\lvert\Lambda\rvert\,w}{c} \,.$$
[Shah2024, proof of Lemma 4.1], there with the density $\ell/(2R)$ of the shift and the bound
$nw/R$, which drops the factor $\ell$; here $c = R/\ell$ gives $nw\ell/R$.
Proof: the event is the union over $\lambda$ of $\{v : \lvert v - \lambda/c \rvert < w/c\}$, each
of uniform measure at most $(2w/c)/2$ (`ProbabilityTheory.cond_apply`,
`Real.volume_Ioo`, `MeasureTheory.measure_mono` to the interval, `Real.volume_Icc`);
`MeasureTheory.measure_biUnion_finset_le`. M, about 25 lines. -/
theorem measureReal_exists_abs_sub_lt_le (Λ : Finset ℝ) {c w : ℝ} (hc : 0 < c) (hw : 0 ≤ w) :
    (ProbabilityTheory.cond volume (Set.Icc (-1 : ℝ) 1)).real
      {v | ∃ e ∈ Λ, |e - c * v| < w} ≤ Λ.card * w / c := by
  rw [measureReal_def, cond_apply measurableSet_Icc]
  have hvol : volume (Set.Icc (-1 : ℝ) 1) = ENNReal.ofReal 2 := by
    rw [Real.volume_Icc]; norm_num
  have hsub : Set.Icc (-1 : ℝ) 1 ∩ {v | ∃ e ∈ Λ, |e - c * v| < w} ⊆
      ⋃ e ∈ Λ, Set.Ioo ((e - w) / c) ((e + w) / c) := by
    rintro v ⟨-, e, he, hv⟩
    rw [abs_lt] at hv
    simp only [Set.mem_iUnion, Set.mem_Ioo]
    refine ⟨e, he, ?_, ?_⟩
    · rw [div_lt_iff₀ hc]; linarith [hv.2]
    · rw [lt_div_iff₀ hc]; linarith [hv.1]
  have h1 : volume (Set.Icc (-1 : ℝ) 1 ∩ {v | ∃ e ∈ Λ, |e - c * v| < w}) ≤
      ∑ e ∈ Λ, volume (Set.Ioo ((e - w) / c) ((e + w) / c)) :=
    (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
  have h2 : ∀ e : ℝ, volume (Set.Ioo ((e - w) / c) ((e + w) / c)) =
      ENNReal.ofReal (2 * w / c) := by
    intro e
    rw [Real.volume_Ioo]
    congr 1
    field_simp
    ring
  rw [Finset.sum_congr rfl fun e _ => h2 e, Finset.sum_const, nsmul_eq_mul] at h1
  have hpos : (0 : ℝ) ≤ Λ.card * w / c := by positivity
  refine ENNReal.toReal_le_of_le_ofReal hpos ?_
  rw [hvol]
  calc (ENNReal.ofReal 2)⁻¹ * volume (Set.Icc (-1 : ℝ) 1 ∩ {v | ∃ e ∈ Λ, |e - c * v| < w})
      ≤ (ENNReal.ofReal 2)⁻¹ * ((Λ.card : ℝ≥0∞) * ENNReal.ofReal (2 * w / c)) := by gcongr
    _ = ENNReal.ofReal (Λ.card * w / c) := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos two_pos, ← ENNReal.ofReal_mul
        (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp

/-- The sign of a shifted Hermitian matrix is a measurable function of the shift. -/
private lemma measurable_cfc_sign_sub_smul_aux {k : ℕ} {A : Matrix (Fin k) (Fin k) ℂ}
    (hA : A.IsHermitian) (a : ℝ) :
    Measurable fun v : ℝ => cfc Real.sign (A - (a * v) • (1 : Matrix (Fin k) (Fin k) ℂ)) := by
  have h : ∀ c : ℝ, cfc Real.sign (A - c • (1 : Matrix (Fin k) (Fin k) ℂ)) =
      hA.cfc fun x => Real.sign (x + -c) := by
    intro c
    have hAc : A - c • (1 : Matrix (Fin k) (Fin k) ℂ) = cfc (fun x : ℝ => x + -c) A := by
      rw [cfc_add_const (-c) (fun x : ℝ => x) A, cfc_id' ℝ A, Algebra.algebraMap_eq_smul_one,
        neg_smul, sub_eq_add_neg]
    rw [hAc, ← cfc_comp' Real.sign (fun x : ℝ => x + -c) A
      ((A.finite_real_spectrum.image _).continuousOn _), ← hA.cfc_eq]
  simp_rw [h]
  unfold Matrix.IsHermitian.cfc
  simp only [Unitary.conjStarAlgAut_apply]
  have hs : Measurable Real.sign := by
    unfold Real.sign
    exact Measurable.ite measurableSet_Iio measurable_const
      (Measurable.ite measurableSet_Ioi measurable_const measurable_const)
  have hd : Measurable fun v : ℝ => Matrix.diagonal
      (RCLike.ofReal ∘ (fun x => Real.sign (x + -(a * v))) ∘ hA.eigenvalues : Fin k → ℂ) := by
    refine (continuous_id.matrix_diagonal).measurable.comp ?_
    refine measurable_pi_lambda _ fun i => ?_
    exact Complex.measurable_ofReal.comp (hs.comp (measurable_const.add
      (measurable_const.mul measurable_id).neg))
  have hc : Continuous fun X : Matrix (Fin k) (Fin k) ℂ =>
      (hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) * X *
        star (hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) := by fun_prop
  exact hc.measurable.comp hd

/-- The trace of $\mathbf{V}\mathbf{V}^{\mathsf{H}}$ is the number of orthonormal columns. -/
private lemma re_trace_mul_conjTranspose_aux {k m : ℕ} {V : Matrix (Fin k) (Fin m) ℂ}
    (hV : HasOrthonormalCols V) : RCLike.re (V * Vᴴ).trace = m := by
  rw [Matrix.trace_mul_comm, hV.conjTranspose_mul_self, Matrix.trace_one, Fintype.card_fin]
  simp

/-- For $k \le N$ the leading block is the submatrix along `Fin.castLE`. -/
private lemma leadingBlock_eq_submatrix_aux {k N : ℕ} (h : k ≤ N)
    (G : Matrix (Fin N) (Fin N) ℂ) :
    leadingBlock k G = G.submatrix (Fin.castLE h) (Fin.castLE h) := by
  ext i j
  simp [leadingBlock, Fin.castLE, show (i : ℕ) < N from i.isLt.trans_le h,
    show (j : ℕ) < N from j.isLt.trans_le h]

/-- The leading block of either test matrix of a sample is standard complex Gaussian. -/
private lemma hasLaw_leadingBlock_aux {k N : ℕ} (h : k ≤ N) (b : Bool) :
    HasLaw (fun G : Bool → Matrix (Fin N) (Fin N) ℂ => leadingBlock k (G b))
      (complexGaussianMatrix (Fin k) (Fin k))
      (Measure.pi fun _ : Bool => complexGaussianMatrix (Fin N) (Fin N)) := by
  have h0 : HasLaw (fun G : Bool → Matrix (Fin N) (Fin N) ℂ => G b)
      (complexGaussianMatrix (Fin N) (Fin N))
      (Measure.pi fun _ : Bool => complexGaussianMatrix (Fin N) (Fin N)) :=
    ⟨(measurePreserving_eval (fun _ : Bool => complexGaussianMatrix (Fin N) (Fin N))
        b).measurable.aemeasurable,
      (measurePreserving_eval (fun _ : Bool => complexGaussianMatrix (Fin N) (Fin N)) b).map_eq⟩
  have := hasLaw_submatrix_of_hasLaw_complexGaussianMatrix h0 (Fin.castLE_injective h)
    (Fin.castLE_injective h)
  simpa only [leadingBlock_eq_submatrix_aux h] using this

/-- Event II fails on one side with probability at most $\rho/2 + \rho/2$ for a fixed frame. -/
private lemma measure_fibre_le_aux {k N m : ℕ} (hkN : k ≤ N) (b : Bool) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ₁ : ρ ≤ 1) (hm : 0 < m) (hmk : m ≤ k) {V : Matrix (Fin k) (Fin m) ℂ}
    (hV : HasOrthonormalCols V) :
    (Measure.pi fun _ : Bool => complexGaussianMatrix (Fin N) (Fin N))
      ({G | √2 * (2 * √(k : ℝ) + √(2 * Real.log (4 / ρ))) ≤ specNorm (leadingBlock k (G b))} ∪
        {G | singularValues (Vᴴ * (leadingBlock k (G b)).submatrix id (Fin.castLE hmk)) (m - 1) ≤
          √(ρ / 2) / k}) ≤ ENNReal.ofReal ρ := by
  set μ := Measure.pi fun _ : Bool => complexGaussianMatrix (Fin N) (Fin N)
  have hL := hasLaw_leadingBlock_aux hkN b
  have hlog : 0 ≤ Real.log (4 / ρ) :=
    Real.log_nonneg (by rw [le_div_iff₀ hρ]; linarith)
  have h1 := measureReal_specNorm_ge_le_of_hasLaw_complexGaussianMatrix hL
    (Real.sqrt_nonneg (2 * Real.log (4 / ρ)))
  simp only [Fintype.card_fin] at h1
  have hexp : 2 * Real.exp (-√(2 * Real.log (4 / ρ)) ^ 2 / 2) = ρ / 2 := by
    rw [Real.sq_sqrt (by positivity), show -(2 * Real.log (4 / ρ)) / 2 = -Real.log (4 / ρ) by ring,
      Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
    norm_num
  have h2 := measureReal_singularValues_le_le_of_hasLaw_complexGaussianMatrix
    (hasLaw_conjTranspose_mul_of_hasLaw_complexGaussianMatrix
      (hasLaw_submatrix_of_hasLaw_complexGaussianMatrix hL Function.injective_id
        (Fin.castLE_injective hmk)) hV) (k := m - 1) (by simp; omega)
    (x := √(ρ / 2) / k) (by positivity)
  simp only [Fintype.card_fin] at h2
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hm.trans_le hmk
  have hmk' : (m : ℝ) ≤ k := by exact_mod_cast hmk
  have hx : (m : ℝ) ^ 2 * (√(ρ / 2) / k) ^ 2 ≤ ρ / 2 := by
    rw [div_pow, Real.sq_sqrt (by positivity), mul_div_assoc']
    rw [div_le_iff₀ (by positivity)]
    have : (m : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hmk' 2
    nlinarith
  refine (measure_union_le _ _).trans ?_
  rw [← ofReal_measureReal (measure_ne_top _ _), ← ofReal_measureReal (measure_ne_top _ _),
    ← ENNReal.ofReal_add measureReal_nonneg measureReal_nonneg]
  refine ENNReal.ofReal_le_ofReal ?_
  have e1 : {G : Bool → Matrix (Fin N) (Fin N) ℂ |
      √2 * (2 * √(k : ℝ) + √(2 * Real.log (4 / ρ))) ≤ specNorm (leadingBlock k (G b))} =
      {G | √2 * (√(k : ℝ) + √(k : ℝ) + √(2 * Real.log (4 / ρ))) ≤
        specNorm (leadingBlock k (G b))} := by
    ext G; simp only [Set.mem_ofPred_eq, two_mul]
  rw [e1]
  linarith

/-- Off the spectrum, each spectral projector of a shift has a frame with orthonormal columns. -/
private lemma exists_frame_aux {k : ℕ} {A : Matrix (Fin k) (Fin k) ℂ} (hA : A.IsHermitian)
    {c : ℝ} (hc : ∀ x ∈ spectrum ℝ A, x ≠ c) (b : Bool) :
    ∃ m, ∃ V : Matrix (Fin k) (Fin m) ℂ, HasOrthonormalCols V ∧
      V * Vᴴ = (2⁻¹ : ℝ) • (1 + (if b then (1 : ℝ) else -1) •
        cfc Real.sign (A - c • (1 : Matrix (Fin k) (Fin k) ℂ))) := by
  cases b
  · have hc' : ∀ x ∈ spectrum ℝ (-A), x ≠ -c := by
      intro x hx hxc
      rw [← spectrum.neg_eq] at hx
      exact hc (-x) hx (by rw [hxc, neg_neg])
    obtain ⟨V, hV, hVV, -⟩ := hA.neg.exists_hasOrthonormalCols_mul_conjTranspose_eq hc'
    refine ⟨_, V, hV, ?_⟩
    have hX : (A - c • (1 : Matrix (Fin k) (Fin k) ℂ)).IsHermitian :=
      hA.sub (by simp [Matrix.IsHermitian, Matrix.conjTranspose_smul])
    have h1 : -A - (-c) • (1 : Matrix (Fin k) (Fin k) ℂ) = -(A - c • 1) := by
      rw [neg_smul, sub_neg_eq_add, neg_sub', sub_neg_eq_add]
    have h2 : cfc Real.sign (-(A - c • (1 : Matrix (Fin k) (Fin k) ℂ))) =
        -cfc Real.sign (A - c • (1 : Matrix (Fin k) (Fin k) ℂ)) := by
      rw [← cfc_comp_neg Real.sign (A - c • 1)
        (((A - c • 1).finite_real_spectrum.image _).continuousOn _) hX.isSelfAdjoint,
        ← cfc_neg]
      simp only [Real.sign_neg]
    rw [hVV, h1, h2]
    simp
  · obtain ⟨V, hV, hVV, -⟩ := hA.exists_hasOrthonormalCols_mul_conjTranspose_eq hc
    exact ⟨_, V, hV, by rw [hVV]; simp⟩

/-- Each singular value is continuous (`NLAlib.continuous_singularValues`, not imported here). -/
private lemma continuous_singularValues_aux {m n : Type*} [Fintype m] [Fintype n] (k : ℕ) :
    Continuous fun A : Matrix m n ℂ => singularValues A k := by
  refine continuous_iff_continuousAt.2 fun A => ?_
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  have h0 : Filter.Tendsto (fun B : Matrix m n ℂ => specNorm (B - A)) (nhds A) (nhds 0) := by
    have := (continuous_specNorm.comp (continuous_id.sub (continuous_const (y := A)))).tendsto A
    simpa [Function.comp_def, specNorm_zero] using this
  refine squeeze_zero (fun _ => dist_nonneg) (fun B => ?_) h0
  rw [Real.dist_eq]
  exact abs_singularValues_sub_le_specNorm B A k

/-- The spectral projector of side `b` at the ideal shift $Lv$. -/
private noncomputable def sideProjAux {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (L : ℝ) (b : Bool)
    (v : ℝ) : Matrix (Fin k) (Fin k) ℂ :=
  (2⁻¹ : ℝ) • (1 + (if b then (1 : ℝ) else -1) •
    cfc Real.sign (A - (L * v) • (1 : Matrix (Fin k) (Fin k) ℂ)))

/-- The seeds of Event I at which the positive projector has rank strictly between $0$ and $k$. -/
private def splitSeedsAux {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (L w : ℝ) : Set ℝ :=
  (Set.Icc (-1 : ℝ) 1 ∩ ⋂ e ∈ spectrum ℝ A, {v | w ≤ |e - L * v|}) ∩
    ({v | 0 < RCLike.re (sideProjAux A L true v).trace} ∩
      {v | RCLike.re (sideProjAux A L true v).trace < k})

/-- A measurable superset of the failure of Event II on side `b` at the seeds of
`splitSeedsAux`, with the frame replaced by the projector. -/
private def sideBadAux {k : ℕ} (N : ℕ) (A : Matrix (Fin k) (Fin k) ℂ) (L w ρ : ℝ) (b : Bool) :
    Set (EighSample ℝ ℂ N) :=
  {s | s.1 ∈ splitSeedsAux A L w ∧ ∃ r : Fin k, 0 < (r : ℕ) ∧
    RCLike.re (sideProjAux A L b s.1).trace = ((r : ℕ) : ℝ) ∧
    (√2 * (2 * √(k : ℝ) + √(2 * Real.log (4 / ρ))) ≤ specNorm (leadingBlock k (s.2 b)) ∨
      singularValues (sideProjAux A L b s.1 * (leadingBlock k (s.2 b)).submatrix id
        (Fin.castLE r.isLt.le)) ((r : ℕ) - 1) ≤ √(ρ / 2) / k)}

/-- Membership in `splitSeedsAux`. -/
private lemma mem_splitSeedsAux {k : ℕ} {A : Matrix (Fin k) (Fin k) ℂ} {L w v : ℝ} :
    v ∈ splitSeedsAux A L w ↔ (v ∈ Set.Icc (-1 : ℝ) 1 ∧ ∀ e ∈ spectrum ℝ A, w ≤ |e - L * v|) ∧
      0 < RCLike.re (sideProjAux A L true v).trace ∧
        RCLike.re (sideProjAux A L true v).trace < k := by
  simp only [splitSeedsAux, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]

/-- The two projectors have traces adding up to $k$. -/
private lemma re_trace_sideProjAux_add {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (L v : ℝ) :
    RCLike.re (sideProjAux A L true v).trace + RCLike.re (sideProjAux A L false v).trace = k := by
  have : sideProjAux A L true v + sideProjAux A L false v = 1 := by
    simp only [sideProjAux, if_true, Bool.false_eq_true, if_false, one_smul, neg_smul]
    module
  rw [← map_add, ← Matrix.trace_add, this, Matrix.trace_one, Fintype.card_fin]
  simp

/-- The trace function of a projector is measurable in the seed. -/
private lemma measurable_re_trace_sideProjAux {k : ℕ} {A : Matrix (Fin k) (Fin k) ℂ}
    (hA : A.IsHermitian) (L : ℝ) (b : Bool) :
    Measurable (sideProjAux A L b) ∧ Measurable fun v => RCLike.re (sideProjAux A L b v).trace := by
  have h : Measurable (sideProjAux A L b) :=
    (Continuous.measurable (by fun_prop) : Measurable fun S : Matrix (Fin k) (Fin k) ℂ =>
      (2⁻¹ : ℝ) • (1 + (if b then (1 : ℝ) else -1) • S)).comp
        (measurable_cfc_sign_sub_smul_aux hA L)
  exact ⟨h, (Continuous.measurable (by fun_prop : Continuous fun X : Matrix (Fin k) (Fin k) ℂ =>
    RCLike.re X.trace)).comp h⟩

/-- `splitSeedsAux` is measurable. -/
private lemma measurableSet_splitSeedsAux {k : ℕ} {A : Matrix (Fin k) (Fin k) ℂ}
    (hA : A.IsHermitian) (L w : ℝ) : MeasurableSet (splitSeedsAux A L w) :=
  (measurableSet_Icc.inter (A.finite_real_spectrum.measurableSet_biInter fun _ _ =>
    measurableSet_le measurable_const
      (continuous_const.sub (continuous_const.mul continuous_id)).abs.measurable)).inter
    ((measurableSet_lt measurable_const (measurable_re_trace_sideProjAux hA L true).2).inter
      (measurableSet_lt (measurable_re_trace_sideProjAux hA L true).2 measurable_const))

/-- `sideBadAux` is measurable. -/
private lemma measurableSet_sideBadAux {k N : ℕ} {A : Matrix (Fin k) (Fin k) ℂ}
    (hA : A.IsHermitian) (hkN : k ≤ N) (L w ρ : ℝ) (b : Bool) :
    MeasurableSet (sideBadAux N A L w ρ b) := by
  have hLB : Measurable fun G : Bool → Matrix (Fin N) (Fin N) ℂ => leadingBlock k (G b) := by
    simp_rw [leadingBlock_eq_submatrix_aux hkN]
    exact ((continuous_apply b).matrix_submatrix _ _).measurable
  obtain ⟨hP, htr⟩ := measurable_re_trace_sideProjAux hA L b
  refine measurableSet_setOfPred.2 ((measurableSet_setOfPred.1
    (measurable_fst (measurableSet_splitSeedsAux hA L w))).and
    (Measurable.exists fun r => measurable_const.and
      ((measurableSet_setOfPred.1 (measurableSet_eq_fun (htr.comp measurable_fst)
        measurable_const)).and ((measurableSet_setOfPred.1 (measurableSet_le measurable_const
          (continuous_specNorm.measurable.comp (hLB.comp measurable_snd)))).or
          (measurableSet_setOfPred.1 (measurableSet_le ?_ measurable_const))))))
  refine (continuous_singularValues_aux _).measurable.comp ?_
  exact Continuous.measurable2 (by fun_prop) (hP.comp measurable_fst)
    ((Continuous.matrix_submatrix continuous_id _ _).measurable.comp (hLB.comp measurable_snd))

/-- Each side fails Event II with probability at most $\rho$ on the seeds of `splitSeedsAux`:
`MeasureTheory.Measure.prod_apply` and the fibre bound for a frame of the projector. -/
private lemma measure_sideBadAux_le {k N : ℕ} {A : Matrix (Fin k) (Fin k) ℂ}
    (hA : A.IsHermitian) (hkN : k ≤ N) {L w ρ : ℝ} (hw : 0 < w) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1)
    (μ : Measure ℝ) (b : Bool) :
    (μ.prod (Measure.pi fun _ : Bool => complexGaussianMatrix (Fin N) (Fin N)))
      (sideBadAux N A L w ρ b) ≤ ENNReal.ofReal ρ * μ (splitSeedsAux A L w) := by
  rw [Measure.prod_apply (measurableSet_sideBadAux hA hkN L w ρ b),
    ← lintegral_indicator_const (measurableSet_splitSeedsAux hA L w)]
  refine lintegral_mono fun v => ?_
  by_cases hv : v ∈ splitSeedsAux A L w
  · rw [Set.indicator_of_mem hv]
    obtain ⟨⟨-, hI⟩, -⟩ := mem_splitSeedsAux.1 hv
    obtain ⟨m, V, hV, hVV⟩ := exists_frame_aux hA (c := L * v) (fun e he hev => by
      have := hI e he
      rw [hev, sub_self, abs_zero] at this
      linarith) b
    change V * Vᴴ = sideProjAux A L b v at hVV
    have htrV := re_trace_mul_conjTranspose_aux hV
    rw [hVV] at htrV
    by_cases hm : 0 < m ∧ m ≤ k
    · refine (measure_mono ?_).trans (measure_fibre_le_aux hkN b hρ hρ₁ hm.1 hm.2 hV)
      intro G hG
      obtain ⟨-, ⟨r, hrk⟩, -, hrtr, hbad⟩ := hG
      have hrm : r = m := by exact_mod_cast hrtr.symm.trans htrV
      subst hrm
      rcases hbad with h | h
      · exact Or.inl h
      · right
        rw [Set.mem_ofPred_eq, ← hV.singularValues_mul_left, ← Matrix.mul_assoc, hVV]
        exact h
    · refine le_of_eq_of_le (measure_mono_null (fun G hG => ?_) measure_empty) zero_le
      obtain ⟨-, ⟨r, hrk⟩, hr0, hrtr, -⟩ := hG
      have hrm : r = m := by exact_mod_cast hrtr.symm.trans htrV
      exact hm ⟨hrm ▸ hr0, hrm ▸ hrk.le⟩
  · rw [Set.indicator_of_notMem hv]
    exact le_of_eq (measure_mono_null (fun G hG => hv hG.1) measure_empty)

/-- Event I fails with probability at most $kw/L$ (`NLAlib.measureReal_exists_abs_sub_lt_le`; the
seed lies in $[-1, 1]$ almost surely). -/
private lemma measure_not_eventI_le {k : ℕ} {A : Matrix (Fin k) (Fin k) ℂ} (hA : A.IsHermitian)
    {L w : ℝ} (hL : 0 < L) (hw : 0 < w) {β : Type*} [MeasurableSpace β] (ν : Measure β)
    [IsProbabilityMeasure ν] :
    ((ProbabilityTheory.cond volume (Set.Icc (-1 : ℝ) 1)).prod ν)
      (Prod.fst ⁻¹' ({v | v ∉ Set.Icc (-1 : ℝ) 1} ∪
        {v | ∃ e ∈ spectrum ℝ A, |e - L * v| < w})) ≤ ENNReal.ofReal (k * w / L) := by
  classical
  rw [← Set.prod_univ, Measure.prod_prod, measure_univ, mul_one]
  refine (measure_union_le _ _).trans ?_
  have h0 : ProbabilityTheory.cond volume (Set.Icc (-1 : ℝ) 1)
      {v | v ∉ Set.Icc (-1 : ℝ) 1} = 0 := by
    rw [cond_apply measurableSet_Icc]
    have : Set.Icc (-1 : ℝ) 1 ∩ {v | v ∉ Set.Icc (-1 : ℝ) 1} = ∅ := by
      ext v; simp
    rw [this, measure_empty, mul_zero]
  have hΛ : {v : ℝ | ∃ e ∈ spectrum ℝ A, |e - L * v| < w} =
      {v | ∃ e ∈ Finset.univ.image hA.eigenvalues, |e - L * v| < w} := by
    ext v
    simp [hA.spectrum_real_eq_range_eigenvalues]
  rw [h0, zero_add, hΛ, ← ofReal_measureReal (measure_ne_top _ _)]
  refine ENNReal.ofReal_le_ofReal ((measureReal_exists_abs_sub_lt_le _ hL hw.le).trans ?_)
  have hΛk : ((Finset.univ.image hA.eigenvalues).card : ℝ) ≤ k := by
    have := Finset.card_image_le (s := Finset.univ) (f := hA.eigenvalues)
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact_mod_cast this
  gcongr

/-- The failure of the good events lies in the failure of Event I or in `sideBadAux` on a side:
on Event I a frame of a projector with $0 < r < k$ columns pins the trace to $r$, and
`NLAlib.HasOrthonormalCols.singularValues_mul_left` replaces the frame by the projector. -/
private lemma not_isEighGoodSample_subset {F : Type*} {dec : F → ℝ} {w ρ : ℝ} {y : EighNode F}
    {N : ℕ} :
    {s : EighSample ℝ ℂ N | ¬ IsEighGoodSample dec w (√(ρ / 2) / y.k)
      (√2 * (2 * √(y.k : ℝ) + √(2 * Real.log (4 / ρ)))) y s} ⊆
      Prod.fst ⁻¹' ({v | v ∉ Set.Icc (-1 : ℝ) 1} ∪
        {v | ∃ e ∈ spectrum ℝ (decodeMatrix dec y.A), |e - dec y.R / y.ℓ * v| < w}) ∪
      (sideBadAux N (decodeMatrix dec y.A) (dec y.R / y.ℓ) w ρ true ∪
        sideBadAux N (decodeMatrix dec y.A) (dec y.R / y.ℓ) w ρ false) := by
  intro s hs
  simp only [IsEighGoodSample, Set.mem_ofPred_eq] at hs
  generalize decodeMatrix dec y.A = A at hs ⊢
  generalize dec y.R / (y.ℓ : ℝ) = L at hs ⊢
  by_cases h1 : s.1 ∈ Set.Icc (-1 : ℝ) 1 ∧ ∀ e ∈ spectrum ℝ A, w ≤ |e - L * s.1|
  · right
    have h2 := not_and.1 hs h1
    push Not at h2
    obtain ⟨b, r, V, hr0, hrk, hV, hVV, hbad⟩ := h2
    change V * Vᴴ = sideProjAux A L b s.1 at hVV
    have htrV := re_trace_mul_conjTranspose_aux hV
    rw [hVV] at htrV
    have hsT : s.1 ∈ splitSeedsAux A L w := by
      refine mem_splitSeedsAux.2 ⟨h1, ?_⟩
      have hrk' : (r : ℝ) < y.k := by exact_mod_cast hrk
      have hr0' : (0 : ℝ) < r := by exact_mod_cast hr0
      have := re_trace_sideProjAux_add A L s.1
      cases b
      · rw [htrV] at this
        constructor <;> linarith
      · rw [htrV]
        exact ⟨hr0', hrk'⟩
    have hmem : s ∈ sideBadAux N A L w ρ b := by
      refine ⟨hsT, ⟨r, hrk⟩, hr0, htrV, ?_⟩
      rcases le_or_gt (√2 * (2 * √(y.k : ℝ) + √(2 * Real.log (4 / ρ))))
        (specNorm (leadingBlock y.k (s.2 b))) with ht | ht
      · exact Or.inl ht
      · obtain ⟨h, hσ⟩ := hbad ht
        right
        rw [← hVV, Matrix.mul_assoc, hV.singularValues_mul_left]
        exact hσ
    cases b
    · exact Or.inr hmem
    · exact Or.inl hmem
  · left
    simp only [Set.mem_preimage, Set.mem_union, Set.mem_ofPred_eq]
    by_cases hv : s.1 ∈ Set.Icc (-1 : ℝ) 1
    · right
      push Not at h1
      exact h1 hv
    · exact Or.inl hv

/-- **Probability of the good events of a node**: under the hypotheses of
`NLAlib.FloatMachine.IsAccurate.isApproxDiagonalization_eighAux_succ_of_isEighGoodSample` on the
node $y$ (contracts, precision, step limit, floor and range) with $2 \le k \le N$ and the machine's
leaf test $R \le \mathrm{fl}(\varepsilon R_0)$ failing, the
sample law `NLAlib.eighSampleLaw` $N$ gives the bad events (`NLAlib.IsEighGoodSample` with $w$,
$x = \sqrt{\rho/2}/k$, $t = \sqrt2(2\sqrt k + \sqrt{2\log(4/\rho)})$ failing) probability at most
$$\frac{kw\ell}{R} + 2\rho\,\mathbb{P}[\text{the node splits}] \,,$$
the node splitting when `NLAlib.eighStep` is `NLAlib.EighStep.split`. [Shah2024, Lemma 4.1],
"Event I occurs with probability at least $1 - wn/R$ and Event II with probability at least
$1 - 2\rho$".
Proof: Event I fails with probability at most $kw\ell/R$
(`NLAlib.measureReal_exists_abs_sub_lt_le` with $\Lambda$ the eigenvalues, $c = R/\ell$; the
first marginal of `NLAlib.eighSampleLaw`; the seed lies in $[-1, 1]$ almost surely). On Event I
the node splits exactly when the true projector has rank strictly between $0$ and $k$
(`NLAlib.FloatMachine.IsAccurate.eighStep_isSplit_iff_of_forall_le_abs_sub`), and the split depends
on the seed only. Given the seed, the two Gaussian matrices are independent with the complex
Gaussian law (`MeasureTheory.Measure.prod_apply`, `MeasureTheory.Measure.pi_pi`), and for each side
the leading block fails Event II with probability at most $2e^{-\log(4/\rho)} + k^2 \cdot
\rho/(2k^2) = \rho$
(`NLAlib.FloatMachine.IsAccurate.measureReal_not_exists_specNorm_mul_sub_deflate_le_le`'s two tails:
`NLAlib.measureReal_specNorm_ge_le_of_hasLaw_complexGaussianMatrix`,
`NLAlib.measureReal_singularValues_le_le_of_hasLaw_complexGaussianMatrix`,
`NLAlib.hasLaw_submatrix_of_hasLaw_complexGaussianMatrix` for the leading block,
`NLAlib.leadingBlock` $k$ $\mathbf{G}$ the submatrix along `Fin.castLE`). The sets of split seeds
and of samples failing Event II depend on the seed through the machine and need not be measurable,
so do not apply `MeasureTheory.Measure.prod_apply` to them; use a measurable superset:
$\lnot\mathrm{good} \subseteq \lnot\mathrm{I} \cup (\mathrm{I} \cap J \cap B)$ with $J = \{v \mid 0
< i_+(\mathbf{A} - (R/\ell)v\mathbf{I}) < k\}$ (an open interval between extreme eigenvalues) and
$B = \bigcup_b\{(v, \mathbf{G}) \mid \|\mathbf{G}_b\|_2 \ge t \lor
\sigma_{r(v)-1}(\mathbf{\Pi}_b(v)\mathbf{G}_{b,1}) \le x\}$, measurable since $r(v)$ and
$\mathbf{\Pi}_b(v)$ are piecewise constant in $v$ (finitely many values) and norms and singular
values are continuous; `NLAlib.HasOrthonormalCols.singularValues_mul_left` gives
$\sigma(\mathbf{V}^{\mathsf{H}}\mathbf{G}_1) = \sigma(\mathbf{\Pi}\mathbf{G}_1)$, so the bad event
does not depend on the frame $\mathbf{V}$ quantified in `NLAlib.IsEighGoodSample`. Then
`MeasureTheory.Measure.prod_apply` with the tails gives fibre measure $\le \rho$ per side, and
$\mathrm{I} \cap J \subseteq \{\text{split seeds}\}$ (the forward direction of rank recovery) with
`MeasureTheory.Measure.prod_prod` (valid for arbitrary sets) gives $\le
2\rho\,\mathbb{P}[\text{split}]$; $k_+$ depends on the sample only through the seed. H, about 150
lines. -/
theorem FloatMachine.IsAccurate.measure_not_isEighGoodSample_le
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ}
    {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) {N signFuel : ℕ} {R₀ β : F}
    {ρ w : ℝ} {y : EighNode F} (hμM : 0 ≤ μM y.k) (hμQ : 0 ≤ μQ y.k) (hcN : 0 ≤ cN) (hu : 0 ≤ u)
    (hA : (decodeMatrix dec y.A).IsHermitian) (hR : specNorm (decodeMatrix dec y.A) ≤ dec y.R)
    (hk : 2 ≤ y.k) (hkN : y.k ≤ N) (hℓ : 20 ≤ y.ℓ) (hε : 0 < dec y.ε) (hε₁ : dec y.ε ≤ 1 / 8)
    (hR₀ : 0 < dec R₀) (hint : M.le y.R (M.mul y.ε R₀) = false) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1)
    (hw : 0 < w) (hwR : w ≤ dec y.R) (hβ : 0 < dec β)
    (hβtol : dec β ≤ bisectionSignTol y.k (dec y.ε) ρ y.ℓ)
    (husign : 640 * y.k * √(y.k : ℝ) * (8 + μM y.k) *
      (newtonSchulzSteps (w / (8 * dec y.R)) (dec β / (16 * y.k)) + 1) * u ≤
        w / (4 * dec y.R) * dec β)
    (hudefl : (4 * μQ y.k + 4 * √(y.k : ℝ) * (cN + 1) + 2 * μM y.k + 1) * u ≤ dec β)
    (hfuel : newtonSchulzSteps (w / (8 * dec y.R)) (dec β / (16 * y.k)) ≤ signFuel)
    (hτ₀ : 0 ≤ τ) (hτ : τ * (4 * y.k * √(y.k : ℝ)) ≤ min (√(ρ / 2)) (dec y.ε * dec R₀))
    (hΩ : 16 * (dec R₀ + dec y.R + y.k + y.ℓ + √(Real.log (4 / ρ))) ≤ Ω) :
    eighSampleLaw N {s | ¬ IsEighGoodSample dec w (√(ρ / 2) / y.k)
      (√2 * (2 * √(y.k : ℝ) + √(2 * Real.log (4 / ρ)))) y s} ≤
      ENNReal.ofReal (y.k * w * y.ℓ / dec y.R) + ENNReal.ofReal (2 * ρ) *
        eighSampleLaw N {s | (eighStep M N signFuel R₀ β y.A y.R y.ε y.ℓ s).IsSplit} := by
  have hRpos : 0 < dec y.R := hw.trans_le hwR
  have hℓpos : (0 : ℝ) < y.ℓ := by
    have : (20 : ℝ) ≤ y.ℓ := by exact_mod_cast hℓ
    linarith
  have hLpos : 0 < dec y.R / y.ℓ := div_pos hRpos hℓpos
  set μ₁ := ProbabilityTheory.cond volume (Set.Icc (-1 : ℝ) 1)
  set ν := Measure.pi fun _ : Bool => complexGaussianMatrix (Fin N) (Fin N)
  set T := splitSeedsAux (decodeMatrix dec y.A) (dec y.R / y.ℓ) w
  -- the seeds of `T` split the node (rank recovery on Event I)
  have hTsplit : μ₁ T ≤
      (μ₁.prod ν) {s | (eighStep M N signFuel R₀ β y.A y.R y.ε y.ℓ s).IsSplit} := by
    calc μ₁ T = (μ₁.prod ν) (T ×ˢ Set.univ) := by rw [Measure.prod_prod, measure_univ, mul_one]
      _ ≤ _ := measure_mono fun s hs => ?_
    obtain ⟨⟨hv, hI⟩, h0, h1⟩ := mem_splitSeedsAux.1 hs.1
    have htr := hA.re_trace_smul_one_add_cfc_sign (c := dec y.R / y.ℓ * s.1) fun e he hev => by
      have := hI e he
      rw [hev, sub_self, abs_zero] at this
      linarith
    have hPt : sideProjAux (decodeMatrix dec y.A) (dec y.R / y.ℓ) true s.1 =
        (2⁻¹ : ℝ) • (1 + cfc Real.sign (decodeMatrix dec y.A -
          (dec y.R / y.ℓ * s.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ))) := by
      simp [sideProjAux]
    rw [hPt, htr] at h0 h1
    exact (hM.eighStep_isSplit_iff_of_forall_le_abs_sub (signFuel := signFuel) (R₀ := R₀) hμM hu
      hA hR hℓ hε hε₁ hR₀ hρ hρ₁ hw hwR hβ hβtol husign hfuel hτ₀ hτ hΩ hk hint hv hI).2
      ⟨by exact_mod_cast h0, by exact_mod_cast h1⟩
  refine (measure_mono not_isEighGoodSample_subset).trans ((measure_union_le _ _).trans ?_)
  refine (add_le_add (measure_not_eventI_le hA hLpos hw ν) ((measure_union_le _ _).trans
    (add_le_add (measure_sideBadAux_le hA hkN hw hρ hρ₁ μ₁ true)
      (measure_sideBadAux_le hA hkN hw hρ hρ₁ μ₁ false)))).trans ?_
  rw [div_div_eq_mul_div, ← add_mul, ← ENNReal.ofReal_add hρ.le hρ.le, ← two_mul]
  gcongr
  exact hTsplit

/-- Deflation sees the sampled block only through its normal image. -/
private lemma deflate_eq_of_map_normal_eq {F Su Sg : Type*} (M : FloatMachine F Su Sg)
    (r : ℕ) {n : ℕ} (P : Matrix (Fin n) (Fin n) (F × F)) {G G' : Matrix (Fin n) (Fin n) Sg}
    (h : G.map M.normal = G'.map M.normal) : deflate M r P G = deflate M r P G' := by
  unfold deflate
  rw [h]

/-- The child of a node has countably many values as the ideal sample varies. -/
private lemma countable_range_eighChild {F : Type*} {M : FloatMachine F ℝ ℂ}
    (hunif : ∀ c, (Set.range (M.unif c)).Countable) (hnormal : (Set.range M.normal).Countable)
    (N signFuel : ℕ) (R₀ β : F) (x : EighNode F) (b : Bool) :
    (Set.range fun s : EighSample ℝ ℂ N => eighChild M N signFuel R₀ β x s b).Countable := by
  classical
  have := hnormal.to_subtype
  have := (hunif (M.div x.R (M.ofNat x.ℓ))).to_subtype
  let key : EighSample ℝ ℂ N → Set.range (M.unif (M.div x.R (M.ofNat x.ℓ))) ×
      (Fin x.k × Fin x.k → Set.range M.normal) × (Fin x.k × Fin x.k → Set.range M.normal) :=
    fun s => (⟨M.unif (M.div x.R (M.ofNat x.ℓ)) s.1, Set.mem_range_self _⟩,
      fun p => ⟨M.normal (leadingBlock x.k (s.2 true) p.1 p.2), Set.mem_range_self _⟩,
      fun p => ⟨M.normal (leadingBlock x.k (s.2 false) p.1 p.2), Set.mem_range_self _⟩)
  -- the step, written with the computed shift `a` and the normal-mapped blocks as parameters
  let body : F → (Bool → Matrix (Fin N) (Fin N) ℂ) → EighStep F x.k := fun a G =>
    if x.k ≤ 1 then .leaf (M.identityMat x.k) fun i => (x.A i i).1
    else if M.le x.R (M.mul x.ε R₀) then .leaf (M.identityMat x.k) fun _ => M.zero
    else
      let two := M.ofNat 2
      let half := M.div x.R two
      let B := newtonSchulzSign M β (M.mul two x.R) signFuel (M.hermShift x.A a)
      let Pp := M.hermScale (M.hermShift B (M.neg M.one)) two
      let Pm := M.hermScale (M.negMat (M.hermShift B M.one)) two
      let kp := min x.k (M.toNat (M.add (M.traceRe Pp) (M.div M.one two)))
      if kp = x.k then .shift true (M.hermShift x.A half) half
      else if kp = 0 then .shift false (M.hermShift x.A (M.neg half)) (M.neg half)
      else
        let Qp := deflate M kp Pp (leadingBlock x.k (G true))
        let Qm := deflate M (x.k - kp) Pm (leadingBlock x.k (G false))
        .split kp (min_le_left _ _) Qp Qm
          (M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Qp) x.A) Qp) two) half)
          (M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Qm) x.A) Qm) two) (M.neg half))
          half
  have hbody : ∀ (a : F) (G G' : Bool → Matrix (Fin N) (Fin N) ℂ),
      (leadingBlock x.k (G true)).map M.normal = (leadingBlock x.k (G' true)).map M.normal →
      (leadingBlock x.k (G false)).map M.normal = (leadingBlock x.k (G' false)).map M.normal →
      body a G = body a G' := by
    intro a G G' hT hF
    have dT : ∀ (r : ℕ) (P : Matrix (Fin x.k) (Fin x.k) (F × F)),
        deflate M r P (leadingBlock x.k (G true)) =
          deflate M r P (leadingBlock x.k (G' true)) :=
      fun r P => deflate_eq_of_map_normal_eq M r P hT
    have dF : ∀ (r : ℕ) (P : Matrix (Fin x.k) (Fin x.k) (F × F)),
        deflate M r P (leadingBlock x.k (G false)) =
          deflate M r P (leadingBlock x.k (G' false)) :=
      fun r P => deflate_eq_of_map_normal_eq M r P hF
    simp only [body, dT, dF]
  have hfac : ∀ s s', key s = key s' →
      eighChild M N signFuel R₀ β x s b = eighChild M N signFuel R₀ β x s' b := by
    intro s s' h
    have h1 : M.unif (M.div x.R (M.ofNat x.ℓ)) s.1 = M.unif (M.div x.R (M.ofNat x.ℓ)) s'.1 :=
      congrArg Subtype.val (congrArg Prod.fst h)
    have hT : (leadingBlock x.k (s.2 true)).map M.normal =
        (leadingBlock x.k (s'.2 true)).map M.normal :=
      Matrix.ext fun i j => congrArg Subtype.val (congrFun (congrArg (fun t => t.2.1) h) (i, j))
    have hF : (leadingBlock x.k (s.2 false)).map M.normal =
        (leadingBlock x.k (s'.2 false)).map M.normal :=
      Matrix.ext fun i j => congrArg Subtype.val (congrFun (congrArg (fun t => t.2.2) h) (i, j))
    have hstep : eighStep M N signFuel R₀ β x.A x.R x.ε x.ℓ s =
        eighStep M N signFuel R₀ β x.A x.R x.ε x.ℓ s' := by
      change body _ s.2 = body _ s'.2
      rw [h1]
      exact hbody _ _ _ hT hF
    unfold eighChild
    rw [hstep]
  have hrange : Set.range (fun s : EighSample ℝ ℂ N => eighChild M N signFuel R₀ β x s b) ⊆
      (fun t => if hs : ∃ s', key s' = t then eighChild M N signFuel R₀ β x hs.choose b
        else none) '' Set.range key := by
    rintro _ ⟨s, rfl⟩
    refine ⟨key s, ⟨s, rfl⟩, ?_⟩
    dsimp only
    rw [dif_pos (⟨s, rfl⟩ : ∃ s', key s' = key s)]
    exact hfac _ _ (Classical.choose_spec (⟨s, rfl⟩ : ∃ s', key s' = key s))
  exact (((Set.countable_univ).mono (Set.subset_univ _)).image _).mono hrange

/-- **The nodes take countably many values**: if the computed samples have countably many values
(the uniform sampler at every scale and the normal sampler have countable ranges, as the
floating-point numbers do), then for every root and path the node `NLAlib.eighNodeAt` ranges over
a countable set as the samples vary. No printed source.
The algorithm can reach its ideal samples only through the samplers, since their types are
abstract in `NLAlib.eighStep` (§2.0 of the note).
Proof: induction on the path: the node at `b :: a` is a function of the root, of the computed
shift $\mathrm{unif}(\mathrm{fl}(R/\ell), v)$ (countable range for each stored scale; the
stored scales of the nodes form a countable set because they are computed from the root and
earlier countably-valued samples) and of
the computed leading blocks $(\mathrm{normal}(\mathbf{G}_{i,j}))$ of the root's sample (countably
many for each of countably many sizes; `Set.Countable.image`, `Set.countable_iUnion`,
`Set.Countable.prod`, `Set.countable_setOf_finite_subset`-type lemmas for finite tuples), and of
the node at `a` in the subtree. M, about 50 lines. -/
theorem countable_range_eighNodeAt {F : Type*} {M : FloatMachine F ℝ ℂ}
    (hunif : ∀ c, (Set.range (M.unif c)).Countable) (hnormal : (Set.range M.normal).Countable)
    (N signFuel : ℕ) (R₀ β : F) (a : List Bool) (x : EighNode F) :
    (Set.range fun s : List Bool → EighSample ℝ ℂ N =>
      eighNodeAt M N signFuel R₀ β a x s).Countable := by
  induction a generalizing x with
  | nil =>
    refine (Set.countable_singleton (some x)).mono ?_
    rintro _ ⟨s, rfl⟩
    exact Set.mem_singleton _
  | cons b a ih =>
    let S : Option (EighNode F) → Set (Option (EighNode F)) := fun y => match y with
      | none => {none}
      | some y' => Set.range fun s => eighNodeAt M N signFuel R₀ β a y' s
    have hS : ∀ y, (S y).Countable := by
      intro y
      cases y with
      | none => exact Set.countable_singleton _
      | some y' => exact ih y'
    have hY : (Set.range fun s : List Bool → EighSample ℝ ℂ N =>
        eighChild M N signFuel R₀ β x (s []) b).Countable :=
      (countable_range_eighChild hunif hnormal N signFuel R₀ β x b).mono (by
        rintro _ ⟨s, rfl⟩
        exact ⟨s [], rfl⟩)
    refine (hY.biUnion fun y _ => hS y).mono ?_
    rintro _ ⟨s, rfl⟩
    simp only [Set.mem_iUnion]
    refine ⟨eighChild M N signFuel R₀ β x (s []) b, ⟨s, rfl⟩, ?_⟩
    rcases hy : eighChild M N signFuel R₀ β x (s []) b with _ | y'
    · simp [S, eighNodeAt, hy]
    · exact ⟨fun a' => s (b :: a'), by simp [eighNodeAt, hy]⟩

/-- A map with countable range and measurable fibres has measurable preimages. -/
private lemma measurableSet_preimage_of_countable_range_fibres {Ω' α : Type*}
    {mΩ' : MeasurableSpace Ω'} {f : Ω' → α} (hc : (Set.range f).Countable)
    (hf : ∀ z, MeasurableSet (f ⁻¹' {z})) (T : Set α) : MeasurableSet (f ⁻¹' T) := by
  have : f ⁻¹' T = ⋃ z ∈ T ∩ Set.range f, f ⁻¹' {z} := by
    ext ω; simp
  rw [this]
  exact MeasurableSet.biUnion (hc.mono Set.inter_subset_right) fun z _ => hf z

-- the proof names the size bound of `eighStep` to restate it without the sample
set_option linter.auxLemma false in
/-- The child of a node depends on its sample only through the computed shift and the computed
leading blocks. -/
private lemma eighChild_eq_of_unif_eq_of_map_normal_eq {F : Type*} {M : FloatMachine F ℝ ℂ}
    {N signFuel : ℕ} {R₀ β : F} (x : EighNode F) {s s' : EighSample ℝ ℂ N}
    (h1 : M.unif (M.div x.R (M.ofNat x.ℓ)) s.1 = M.unif (M.div x.R (M.ofNat x.ℓ)) s'.1)
    (h2 : ∀ b, (leadingBlock x.k (s.2 b)).map M.normal =
      (leadingBlock x.k (s'.2 b)).map M.normal) (b : Bool) :
    eighChild M N signFuel R₀ β x s b = eighChild M N signFuel R₀ β x s' b := by
  have hd : ∀ r P b, deflate M r P (leadingBlock x.k (s.2 b)) =
      deflate M r P (leadingBlock x.k (s'.2 b)) := by
    intro r P b
    unfold deflate
    rw [h2 b]
  have hs : eighStep M N signFuel R₀ β x.A x.R x.ε x.ℓ s =
      eighStep M N signFuel R₀ β x.A x.R x.ε x.ℓ s' := by
    obtain ⟨v, G⟩ := s
    obtain ⟨v', G'⟩ := s'
    calc eighStep M N signFuel R₀ β x.A x.R x.ε x.ℓ (v, G)
        = eighStep M N signFuel R₀ β x.A x.R x.ε x.ℓ (v, G') := by
          unfold eighStep
          simp only [hd]
      _ = _ := by
          dsimp only at h1
          unfold eighStep
          by_cases hk : x.k ≤ 1
          · simp only [hk, if_true]
          · simp (config := {zeta := false}) only [hk, if_false]
            -- the size bound of the split mentions the sample: restate it without it
            rw [show eighStep._proof_1 M N signFuel β x.A x.R x.ℓ (v, G') = min_le_left _ _
              from rfl, h1]
  unfold eighChild
  rw [hs]

/-- **The node at a path is an event of the earlier samples**: if the samplers have measurable
fibres and countable ranges and each sample $\zeta_b$ is measurable, then for every root $x$, path
$a$ and possible node $y$, the set of outcomes at which the node at $a$ is $y$ is measurable. No
printed source.
Proof: the node at $a$ is a function of the computed samples at the proper prefixes of $a$, a
finite tuple of measurable maps into countable sets
(`NLAlib.countable_range_eighNodeAt`'s decomposition); its fibre at $y$ is a countable union of
fibres of that tuple (`MeasurableSet.iUnion`, `measurableSet_eq_fun`-type lemmas,
`Measurable.comp`). L, about 60 lines. -/
theorem measurableSet_eighNodeAt_eq {F : Type*} {M : FloatMachine F ℝ ℂ}
    (hunifm : ∀ c z, MeasurableSet (M.unif c ⁻¹' {z}))
    (hunif : ∀ c, (Set.range (M.unif c)).Countable)
    (hnormalm : ∀ z, MeasurableSet (M.normal ⁻¹' {z})) (hnormal : (Set.range M.normal).Countable)
    {N signFuel : ℕ} {R₀ β : F} {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    {ζ : List Bool → Ω' → EighSample ℝ ℂ N} (hζ : ∀ b, Measurable (ζ b)) (a : List Bool)
    (x : EighNode F) (y : Option (EighNode F)) :
    MeasurableSet {ω | eighNodeAt M N signFuel R₀ β a x (fun b => ζ b ω) = y} := by
  induction a generalizing x ζ with
  | nil =>
    simp only [eighNodeAt]
    exact MeasurableSet.const _
  | cons b a ih =>
    -- the computed shift and leading blocks: countable range and measurable fibres
    set sc := M.div x.R (M.ofNat x.ℓ)
    let κ : EighSample ℝ ℂ N → F × (Bool → Matrix (Fin x.k) (Fin x.k) (F × F)) :=
      fun s => (M.unif sc s.1, fun b => (leadingBlock x.k (s.2 b)).map M.normal)
    have hκc : (Set.range fun ω => κ (ζ [] ω)).Countable := by
      refine ((hunif sc).prod (Set.countable_pi fun _ => Set.countable_pi fun _ =>
        Set.countable_pi fun _ => hnormal)).mono ?_
      rintro _ ⟨ω, rfl⟩
      exact ⟨⟨_, rfl⟩, fun b i j => ⟨_, rfl⟩⟩
    have hκm : ∀ t, MeasurableSet ((fun ω => κ (ζ [] ω)) ⁻¹' {t}) := by
      intro t
      have : (fun ω => κ (ζ [] ω)) ⁻¹' {t} = {ω | M.unif sc (ζ [] ω).1 = t.1} ∩
          ⋂ b, ⋂ i, ⋂ j,
            {ω | M.normal (leadingBlock x.k ((ζ [] ω).2 b) i j) = t.2 b i j} := by
        ext ω
        simp only [κ, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff,
          Set.mem_iInter, Set.mem_ofPred_eq, Prod.ext_iff, funext_iff (β := fun _ : Bool => _),
          ← Matrix.ext_iff, Matrix.map_apply]
      rw [this]
      refine ((hunifm sc t.1).preimage (measurable_fst.comp (hζ []))).inter
        (MeasurableSet.iInter fun b => MeasurableSet.iInter fun i =>
          MeasurableSet.iInter fun j => ?_)
      by_cases h : (i : ℕ) < N ∧ (j : ℕ) < N
      · simp only [leadingBlock, Matrix.of_apply, dif_pos h]
        have := hζ []
        exact (hnormalm _).preimage (by fun_prop)
      · simp only [leadingBlock, Matrix.of_apply, dif_neg h]
        exact MeasurableSet.const _
    -- the child: countable range and measurable fibres
    set C := fun ω => eighChild M N signFuel R₀ β x (ζ [] ω) b
    have hCm : ∀ z, MeasurableSet (C ⁻¹' {z}) := by
      intro z
      have : C ⁻¹' {z} = (fun ω => κ (ζ [] ω)) ⁻¹'
          {t | ∃ s, κ s = t ∧ eighChild M N signFuel R₀ β x s b = z} := by
        ext ω
        refine ⟨fun h => ⟨ζ [] ω, rfl, h⟩, ?_⟩
        rintro ⟨s, hs, hz⟩
        simp only [Set.mem_preimage, Set.mem_singleton_iff, C, ← hz]
        exact eighChild_eq_of_unif_eq_of_map_normal_eq x (congrArg Prod.fst hs).symm
          (fun b' => congrFun (congrArg Prod.snd hs).symm b') b
      rw [this]
      exact measurableSet_preimage_of_countable_range_fibres hκc hκm _
    have hCc : (Set.range C).Countable := by
      refine (countable_range_eighNodeAt hunif hnormal N signFuel R₀ β [b] x).mono ?_
      rintro _ ⟨ω, rfl⟩
      exact ⟨fun _ => ζ [] ω, by simp [eighNodeAt, C]⟩
    -- the node below the child
    have : {ω | eighNodeAt M N signFuel R₀ β (b :: a) x (fun b => ζ b ω) = y} =
        ⋃ z ∈ Set.range C, C ⁻¹' {z} ∩ {ω | z.bind (fun y' =>
          eighNodeAt M N signFuel R₀ β a y' fun a' => ζ (b :: a') ω) = y} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_singleton_iff, Set.mem_range, exists_prop]
      constructor
      · exact fun h => ⟨C ω, ⟨ω, rfl⟩, rfl, h⟩
      · rintro ⟨z, -, hz, h⟩
        rw [← hz] at h
        exact h
    rw [this]
    refine MeasurableSet.biUnion hCc fun z _ => (hCm z).inter ?_
    cases z with
    | none => exact MeasurableSet.const (none = y)
    | some y' => exact ih (fun a' => hζ _) y'

/-- The node at a path depends on the samples only at the proper prefixes of the path. -/
private lemma eighNodeAt_eq_of_forall_lt_length {F : Type*} {M : FloatMachine F ℝ ℂ}
    {N signFuel : ℕ} {R₀ β : F} (a : List Bool) (x : EighNode F)
    {s s' : List Bool → EighSample ℝ ℂ N} (h : ∀ i < a.length, s (a.take i) = s' (a.take i)) :
    eighNodeAt M N signFuel R₀ β a x s = eighNodeAt M N signFuel R₀ β a x s' := by
  induction a generalizing x s s' with
  | nil => rfl
  | cons b a ih =>
    have h0 := h 0 (by simp)
    simp only [List.take_zero] at h0
    simp only [eighNodeAt, h0]
    congr 1
    funext y
    exact ih y fun i hi => h (i + 1) (by simpa using hi)

/-- **The node at a path is independent of its own sample**: under the hypotheses of
`NLAlib.measurableSet_eighNodeAt_eq` and independence of the samples
($(\zeta_b)_b$ mutually independent), the event that the node at the path $a$ is $y$ is
independent of $\zeta_a$. No printed source; [Shah2024, proof of Theorem 4.2] uses it implicitly
("Event I ... $c'$ is sampled from a density bounded by $\ell/2R$").
Proof: the event is measurable with respect to $\sigma(\zeta_b : b \text{ a proper prefix of }
a)$ (the decomposition of `NLAlib.measurableSet_eighNodeAt_eq`, with each computed sample a
function of one $\zeta_b$), and $a$ is not a proper prefix of itself;
`ProbabilityTheory.iIndepFun.indepFun_finset` (disjoint finite index sets $\{a\}$ and the proper
prefixes) and `ProbabilityTheory.IndepFun.comp`; cleanest as a prefix-dependence lemma (the node
at $a$ agrees for samples agreeing on the proper prefixes of $a$, induction on $a$) and the
measurability lemma on the product over the proper prefixes, with
`ProbabilityTheory.iIndepFun.indepFun_finset`, `ProbabilityTheory.IndepFun.comp` and
`measurableSet_setOf`. H, about 90 lines (the decomposition through the
prefixes, shared with `NLAlib.measurableSet_eighNodeAt_eq`, is the work). -/
theorem indepFun_eighNodeAt_eq {F : Type*} {M : FloatMachine F ℝ ℂ}
    (hunifm : ∀ c z, MeasurableSet (M.unif c ⁻¹' {z}))
    (hunif : ∀ c, (Set.range (M.unif c)).Countable)
    (hnormalm : ∀ z, MeasurableSet (M.normal ⁻¹' {z})) (hnormal : (Set.range M.normal).Countable)
    {N signFuel : ℕ} {R₀ β : F} {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'}
    {ζ : List Bool → Ω' → EighSample ℝ ℂ N} (hζ : ∀ b, Measurable (ζ b)) (hind : iIndepFun ζ μ)
    (a : List Bool) (x : EighNode F) (y : Option (EighNode F)) :
    IndepFun (fun ω => eighNodeAt M N signFuel R₀ β a x (fun b => ζ b ω) = y) (ζ a) μ := by
  -- the proper prefixes of `a`
  set S : Finset (List Bool) := (Finset.range a.length).image fun i => a.take i
  have haS : a ∉ S := by
    simp only [S, Finset.mem_image, Finset.mem_range, not_exists, not_and]
    intro i hi he
    have := congrArg List.length he
    simp only [List.length_take] at this
    omega
  have hST := hind.indepFun_finset S {a} (Finset.disjoint_singleton_right.mpr haS) hζ
  -- the samples on `S`, extended by a default value
  let ext : (S → EighSample ℝ ℂ N) → List Bool → EighSample ℝ ℂ N :=
    fun t c => if h : c ∈ S then t ⟨c, h⟩ else default
  have hext : ∀ c, Measurable fun t => ext t c := by
    intro c
    by_cases h : c ∈ S
    · simp only [ext, dif_pos h]
      exact measurable_pi_apply _
    · simp only [ext, dif_neg h]
      exact measurable_const
  have hφ : Measurable fun t => eighNodeAt M N signFuel R₀ β a x (ext t) = y :=
    measurableSet_setOfPred.mp
      (measurableSet_eighNodeAt_eq hunifm hunif hnormalm hnormal (ζ := fun c t => ext t c)
        hext a x y)
  have hψ : Measurable fun t : ({a} : Finset (List Bool)) → EighSample ℝ ℂ N =>
      t ⟨a, Finset.mem_singleton_self a⟩ :=
    measurable_pi_apply _
  convert hST.comp hφ hψ using 1
  · funext ω
    simp only [Function.comp]
    congr 1
    refine eighNodeAt_eq_of_forall_lt_length a x fun i hi => ?_
    have hi' : a.take i ∈ S := Finset.mem_image_of_mem _ (Finset.mem_range.mpr hi)
    simp only [ext, dif_pos hi']
  · rfl

private theorem eighNodeAt_append_singleton {F Su Sg : Type*} [Inhabited Sg]
    (M : FloatMachine F Su Sg) (N signFuel : ℕ) (R₀ β : F) (b : Bool) :
    ∀ (a : List Bool) (x : EighNode F) (s : List Bool → EighSample Su Sg N),
      eighNodeAt M N signFuel R₀ β (a ++ [b]) x s =
        (eighNodeAt M N signFuel R₀ β a x s).bind fun y => eighChild M N signFuel R₀ β y (s a) b
  | [], x, s => by simp [eighNodeAt]
  | c :: a, x, s => by
    simp only [List.cons_append, eighNodeAt, Option.bind_assoc]
    congr 1; funext y
    exact eighNodeAt_append_singleton M N signFuel R₀ β b a y _

private theorem two_le_k_and_le_eq_false_of_eighChild_eq_some {F Su Sg : Type*} [Inhabited Sg]
    {M : FloatMachine F Su Sg} {N signFuel : ℕ} {R₀ β : F} {x : EighNode F}
    {smp : EighSample Su Sg N} {b : Bool} {y : EighNode F}
    (h : eighChild M N signFuel R₀ β x smp b = some y) :
    2 ≤ x.k ∧ M.le x.R (M.mul x.ε R₀) = false := by
  by_contra hc
  have hleaf : ∃ U d, eighStep M N signFuel R₀ β x.A x.R x.ε x.ℓ smp = .leaf U d := by
    unfold eighStep
    by_cases hk : x.k ≤ 1
    · rw [if_pos hk]; exact ⟨_, _, rfl⟩
    · have hle : M.le x.R (M.mul x.ε R₀) = true := by
        by_contra h'; exact hc ⟨by omega, by simpa using h'⟩
      rw [if_neg hk, if_pos hle]; exact ⟨_, _, rfl⟩
  obtain ⟨U, d, hU⟩ := hleaf
  simp [eighChild, hU] at h

private theorem measurableSet_setOf_eighStep_isSplit {F : Type*} {M : FloatMachine F ℝ ℂ}
    (hunifm : ∀ c z, MeasurableSet (M.unif c ⁻¹' {z}))
    (hunifc : ∀ c, (Set.range (M.unif c)).Countable) (N signFuel : ℕ) (R₀ β : F) {k : ℕ}
    (A : Matrix (Fin k) (Fin k) (F × F)) (R ε : F) (ℓ : ℕ) :
    MeasurableSet {s : EighSample ℝ ℂ N | (eighStep M N signFuel R₀ β A R ε ℓ s).IsSplit} := by
  have hK : ∀ s : EighSample ℝ ℂ N, (eighStep M N signFuel R₀ β A R ε ℓ s).IsSplit ↔
      ¬ k ≤ 1 ∧ ¬ M.le R (M.mul ε R₀) = true ∧
        min k (M.toNat (M.add (M.traceRe (M.hermScale (M.hermShift (newtonSchulzSign M β
          (M.mul (M.ofNat 2) R) signFuel (M.hermShift A (M.unif (M.div R (M.ofNat ℓ)) s.1)))
          (M.neg M.one)) (M.ofNat 2))) (M.div M.one (M.ofNat 2)))) ≠ k ∧
        min k (M.toNat (M.add (M.traceRe (M.hermScale (M.hermShift (newtonSchulzSign M β
          (M.mul (M.ofNat 2) R) signFuel (M.hermShift A (M.unif (M.div R (M.ofNat ℓ)) s.1)))
          (M.neg M.one)) (M.ofNat 2))) (M.div M.one (M.ofNat 2)))) ≠ 0 := by
    intro s
    simp only [eighStep]
    split_ifs <;> simp only [EighStep.IsSplit] <;> tauto
  have hdep : ∀ s s' : EighSample ℝ ℂ N,
      M.unif (M.div R (M.ofNat ℓ)) s.1 = M.unif (M.div R (M.ofNat ℓ)) s'.1 →
      ((eighStep M N signFuel R₀ β A R ε ℓ s).IsSplit ↔
        (eighStep M N signFuel R₀ β A R ε ℓ s').IsSplit) := by
    intro s s' h
    rw [hK, hK, h]
  have heq : {s : EighSample ℝ ℂ N | (eighStep M N signFuel R₀ β A R ε ℓ s).IsSplit} =
      ⋃ z ∈ {z | ∃ s : EighSample ℝ ℂ N, M.unif (M.div R (M.ofNat ℓ)) s.1 = z ∧
        (eighStep M N signFuel R₀ β A R ε ℓ s).IsSplit},
        Prod.fst ⁻¹' (M.unif (M.div R (M.ofNat ℓ)) ⁻¹' {z}) := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff,
      exists_prop]
    exact ⟨fun h => ⟨_, ⟨s, rfl, h⟩, rfl⟩,
      fun ⟨z, ⟨s', hs', h'⟩, hz⟩ => (hdep s s' (hz.trans hs'.symm)).2 h'⟩
  rw [heq]
  refine MeasurableSet.biUnion ((hunifc (M.div R (M.ofNat ℓ))).mono ?_) fun z _ =>
    measurable_fst (hunifm (M.div R (M.ofNat ℓ)) z)
  rintro _ ⟨s, rfl, -⟩
  exact ⟨s.1, rfl⟩

private theorem newtonSchulzSteps_nonneg_of_pos {x e : ℝ} (hx : 0 < x) (he : 0 < e)
    (he₁ : e ≤ 1 / 2) : 0 ≤ newtonSchulzSteps x e := by
  rw [newtonSchulzSteps]
  have h₁ : 0 ≤ Real.logb 2 (min |x| (1 / 2))⁻¹ :=
    Real.logb_nonneg one_lt_two ((one_le_inv₀ (by positivity)).mpr
      ((min_le_right _ _).trans (by norm_num)))
  have h₂ : 1 ≤ Real.logb 2 e⁻¹ := by
    have h2 : (2 : ℝ) ≤ e⁻¹ := by rw [le_inv_comm₀ two_pos he]; linarith
    simpa only [Real.logb_self_eq_one one_lt_two] using
      Real.logb_le_logb_of_le one_lt_two two_pos h2
  linarith [Real.logb_nonneg one_lt_two h₂]

private theorem FloatMachine.IsAccurate.nonneg_and_one_le_and_mul_le
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hμM : Monotone μM) (hμM₀ : 0 ≤ μM 0) {n : ℕ} {R₀ ε β : F} {θ : ℝ} (hR₀pos : 0 < dec R₀)
    (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) {ℓ : ℕ}
    (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hβ : 0 < dec β)
    (hβle : dec β ≤ dec ε * √θ / (2880 * ℓ * n * √(n : ℝ) *
      (2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ))))) {Nst : ℝ}
    (hN : Nst = newtonSchulzSteps (θ / (32 * n * (n + 1) * ℓ * (ℓ + 1))) (dec β / (16 * n)))
    (husign : 640 * n * √(n : ℝ) * (8 + μM n) * (Nst + 1) * (16 * n * (n + 1) * ℓ * (ℓ + 1)) *
      u ≤ θ * dec β) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (100 * n * √(n : ℝ)) ≤ min (√(θ / (8 * n))) (dec ε * min (dec R₀) 1))
    (hΩ : 16 * (2 * dec R₀ + n + 2 * ℓ + √(Real.log (16 * n / θ))) ≤ Ω) :
    0 ≤ u ∧ 1 ≤ n ∧ 20 ≤ ℓ ∧ 0 ≤ Nst ∧ dec β ≤ 1 ∧ 100 * (ℓ : ℝ) ^ 2 * u ≤ 1 ∧
      100 * τ ≤ dec ε * min (dec R₀) 1 ∧ 16 * (dec R₀ + ℓ) ≤ Ω := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, mul_zero, zero_mul, div_zero] at hβle
    exact absurd hβle hβ.not_ge
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ0
  · simp only [Nat.cast_zero, mul_zero, zero_mul, div_zero] at hβle
    exact absurd hβle hβ.not_ge
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ0
  have hsn : 1 ≤ √(n : ℝ) := Real.one_le_sqrt.mpr hn1
  have hμMn : 0 ≤ μM n := hμM₀.trans (hμM (Nat.zero_le n))
  have hlog := Real.sqrt_nonneg (Real.log (16 * n / θ))
  have hS2 : 2 ≤ 2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ)) := by
    have := Real.sqrt_nonneg (2 * Real.log (16 * n / θ)); linarith
  have hb1 : dec β ≤ 1 := by
    have h4 : 1 ≤ (ℓ : ℝ) * n * √(n : ℝ) :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hl1 hn1) hsn
    have hc1 : 1 ≤ 2880 * ℓ * n * √(n : ℝ) * (2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ))) := by
      nlinarith [mul_le_mul h4 hS2 (by norm_num) (by positivity)]
    refine hβle.trans ((div_le_one (by linarith)).mpr (le_trans ?_ hc1))
    exact mul_le_one₀ (hε₁.trans (by norm_num)) (Real.sqrt_nonneg θ) (Real.sqrt_le_one.mpr hθ₁)
  have hNst : 0 ≤ Nst := hN ▸ newtonSchulzSteps_nonneg_of_pos (by positivity) (by positivity)
    (by rw [div_le_iff₀ (by positivity)]; linarith)
  have hΩ16 : 16 * (dec R₀ + ℓ) ≤ Ω := by linarith
  have hu : 0 ≤ u := by
    have h := hM.ofNat 1 (by norm_num; linarith)
    have h1 : 0 < max |((1 : ℕ) : ℝ)| τ := lt_max_of_lt_left (by norm_num)
    by_contra hneg
    have := mul_neg_of_neg_of_pos (not_le.mp hneg) h1
    linarith [abs_nonneg (((1 : ℕ) : ℝ) - dec (M.ofNat 1))]
  have hθβ : θ * dec β ≤ 1 := mul_le_one₀ hθ₁ hβ.le hb1
  have hl20 : 20 ≤ ℓ := by
    have h15 : (15 : ℝ) ≤ Real.logb 2 (dec ε)⁻¹ := by
      have h2 : (2 : ℝ) ^ (15 : ℕ) ≤ (dec ε)⁻¹ := by
        rw [le_inv_comm₀ (by positivity) hε, ← inv_pow]; exact hε₁
      have := Real.logb_le_logb_of_le one_lt_two (by positivity) h2
      rwa [Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one] at this
    have : 15 ≤ ⌈Real.logb 2 (dec ε)⁻¹⌉₊ := by
      have := h15.trans (Nat.le_ceil _); exact_mod_cast this
    unfold bisectionDepth at hℓ; omega
  refine ⟨hu, hn, hl20, hNst, hb1, ?_, ?_, hΩ16⟩
  · have h1 : (1 : ℝ) ≤ n * √(n : ℝ) := one_le_mul_of_one_le_of_one_le hn1 hsn
    have h2 : 8 ≤ (8 + μM n) * (Nst + 1) := by linarith [mul_nonneg hμMn hNst]
    have h3 : 640 * 8 ≤ 640 * n * √(n : ℝ) * (8 + μM n) * (Nst + 1) := by
      linarith [mul_le_mul h1 h2 (by norm_num) (by positivity)]
    have h4 : 32 * (ℓ : ℝ) ^ 2 ≤ 16 * n * (n + 1) * ℓ * (ℓ + 1) := by
      have h41 : (2 : ℝ) ≤ n * (n + 1) := by nlinarith
      have h42 : (ℓ : ℝ) ^ 2 ≤ ℓ * (ℓ + 1) := by nlinarith
      linarith [mul_le_mul h42 h41 (by norm_num) (by positivity)]
    have h5 := mul_le_mul h3 h4 (by positivity) (by positivity)
    have h6 := mul_le_mul_of_nonneg_right h5 hu
    linarith [mul_nonneg (sq_nonneg (ℓ : ℝ)) hu]
  · have h1 : (1 : ℝ) ≤ n * √(n : ℝ) := one_le_mul_of_one_le_of_one_le hn1 hsn
    have : 100 * τ ≤ τ * (100 * n * √(n : ℝ)) := by
      linarith [mul_le_mul_of_nonneg_left h1 hτ₀]
    exact this.trans (hτ.trans (min_le_right _ _))

private theorem le_bisectionSignTol_of_le_div {n k L ℓ : ℕ} {e ey b θ : ℝ} (hk : 1 ≤ k)
    (hkn : k ≤ n) (hL : ℓ ≤ L) (hL₂ : L ≤ 2 * ℓ) (hl20 : 20 ≤ ℓ) (he : 0 < e) (hey : e / 3 ≤ ey)
    (hθ : 0 < θ) (hb : b ≤ e * √θ / (2880 * ℓ * n * √(n : ℝ) *
      (2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ))))) :
    b ≤ bisectionSignTol k ey (θ / (4 * n)) L := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hn1 : (1 : ℝ) ≤ n := hk1.trans hkn'
  have hl20' : (20 : ℝ) ≤ ℓ := by exact_mod_cast hl20
  have hL1 : (ℓ : ℝ) ≤ L := by exact_mod_cast hL
  have hL2 : (L : ℝ) ≤ 2 * ℓ := by exact_mod_cast hL₂
  have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hsρ : √(θ / (4 * n)) * (2 * √(n : ℝ)) = √θ := by
    rw [show (2 : ℝ) * √n = √(4 * n) by
      rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)], ← Real.sqrt_mul (by positivity),
      div_mul_cancel₀ _ (by positivity)]
  have h4ρ : 4 / (θ / (4 * n)) = 16 * n / θ := by field_simp; ring
  have hlog := Real.sqrt_nonneg (2 * Real.log (16 * n / θ))
  have hSk : 2 * √(k : ℝ) + √(2 * Real.log (4 / (θ / (4 * n)))) ≤
      2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ)) := by
    rw [h4ρ]; gcongr
  have hβ' : b * (2880 * ℓ * n * √(n : ℝ) * (2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ)))) ≤
      e * √θ := by rwa [le_div_iff₀ (by positivity)] at hb
  have hA : 19 / 20 * (e / 3) / (10 * ℓ) ≤ (1 - 1 / (L : ℝ)) * ey / (5 * L) := by
    have h1 : 1 / (L : ℝ) ≤ 1 / 20 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    apply div_le_div₀ (by nlinarith) (mul_le_mul (by linarith) hey (by positivity) (by linarith))
      (by linarith) (by linarith)
  rcases le_or_gt b 0 with hb0 | hb0
  · exact hb0.trans (by
      rw [bisectionSignTol]
      exact div_nonneg (mul_nonneg ((by positivity : (0 : ℝ) ≤ 19 / 20 * (e / 3) / (10 * ℓ)).trans
        hA) (Real.sqrt_nonneg _)) (by positivity))
  rw [bisectionSignTol, le_div_iff₀ (by positivity)]
  calc b * (36 * k * (2 * √(k : ℝ) + √(2 * Real.log (4 / (θ / (4 * n))))))
      ≤ b * (36 * n * (2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ)))) := by gcongr
    _ ≤ 19 / 20 * (e / 3) / (10 * ℓ) * √(θ / (4 * n)) := by
        refine le_of_mul_le_mul_right ?_ (by positivity : (0 : ℝ) < 10 * ℓ * (2 * √(n : ℝ)))
        rw [show 19 / 20 * (e / 3) / (10 * ℓ) * √(θ / (4 * n)) * (10 * ℓ * (2 * √(n : ℝ))) =
          19 / 20 * (e / 3) * (√(θ / (4 * n)) * (2 * √(n : ℝ))) by field_simp, hsρ]
        nlinarith [mul_nonneg he.le (Real.sqrt_nonneg θ)]
    _ ≤ (1 - 1 / (L : ℝ)) * ey / (5 * L) * √(θ / (4 * n)) :=
        mul_le_mul_of_nonneg_right hA (Real.sqrt_nonneg _)

private theorem FloatMachine.IsAccurate.pos_of_le_mul_eq_false
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) (hu : u ≤ 1 / 100)
    {R e R₀ ε : F} (hint : M.le R (M.mul e R₀) = false) (hR₀pos : 0 < dec R₀)
    (hε : 0 < dec ε) (hε₁ : dec ε ≤ 1) (he : dec ε / 3 ≤ dec e) (he₁ : dec e ≤ dec ε)
    (hτ : 100 * τ ≤ dec ε * min (dec R₀) 1) (hR₀Ω : dec R₀ ≤ Ω) : 0 < dec R := by
  have h1 : ¬ dec R ≤ dec (M.mul e R₀) := fun h => by simp [(hM.le_iff _ _).2 h] at hint
  have ha : 0 < dec e * dec R₀ := mul_pos (by linarith) hR₀pos
  have hτa : τ ≤ dec e * dec R₀ := by
    linarith [mul_le_mul_of_nonneg_left (min_le_left (dec R₀) 1) hε.le,
      mul_le_mul_of_nonneg_right he hR₀pos.le]
  have h2 := hM.mul e R₀ (by
    rw [abs_of_pos ha]
    linarith [mul_le_mul_of_nonneg_right (he₁.trans hε₁) hR₀pos.le])
  rw [abs_of_pos ha, max_eq_left hτa] at h2
  have h3 := (abs_le.mp h2).2
  linarith [mul_le_mul_of_nonneg_right hu ha.le, lt_of_not_ge h1]

private theorem FloatMachine.IsAccurate.pos_and_le_of_eighNode
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) (hu : 0 ≤ u)
    (hμM : Monotone μM) (hμQ : Monotone μQ) (hμM₀ : 0 ≤ μM 0) (hμQ₀ : 0 ≤ μQ 0) (hcN : 0 ≤ cN)
    {n : ℕ} (hn : 1 ≤ n) {R₀ ε β : F} {θ : ℝ} (hR₀pos : 0 < dec R₀)
    (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) {ℓ : ℕ}
    (hl20 : 20 ≤ ℓ) (hu₁ : 100 * (ℓ : ℝ) ^ 2 * u ≤ 1) (hβ : 0 < dec β) (hb1 : dec β ≤ 1)
    (hβle : dec β ≤ dec ε * √θ / (2880 * ℓ * n * √(n : ℝ) *
      (2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ))))) {Nst : ℝ}
    (hN : Nst = newtonSchulzSteps (θ / (32 * n * (n + 1) * ℓ * (ℓ + 1))) (dec β / (16 * n)))
    (husign : 640 * n * √(n : ℝ) * (8 + μM n) * (Nst + 1) * (16 * n * (n + 1) * ℓ * (ℓ + 1)) *
      u ≤ θ * dec β)
    (hudefl : (4 * μQ n + 4 * √(n : ℝ) * (cN + 1) + 2 * μM n + 1) * u ≤ dec β) {signFuel : ℕ}
    (hfuel : Nst ≤ signFuel) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (100 * n * √(n : ℝ)) ≤ min (√(θ / (8 * n))) (dec ε * min (dec R₀) 1))
    (hτ100 : 100 * τ ≤ dec ε * min (dec R₀) 1) (hΩ16 : 16 * (dec R₀ + ℓ) ≤ Ω)
    (hΩ : 16 * (2 * dec R₀ + n + 2 * ℓ + √(Real.log (16 * n / θ))) ≤ Ω)
    {y : EighNode F} (hk : 2 ≤ y.k) (hint : M.le y.R (M.mul y.ε R₀) = false) (hkn : y.k ≤ n)
    (hℓy : ℓ ≤ y.ℓ) (hℓy₂ : y.ℓ ≤ 2 * ℓ) (hεy : dec ε / 3 ≤ dec y.ε) (hεy₁ : dec y.ε ≤ dec ε)
    (hRy : dec y.R ≤ dec R₀) {w : ℝ}
    (hw : w = θ * dec y.R / (2 * y.k * y.ℓ * (n + 1) * (ℓ + 1))) :
    0 < dec y.R ∧ 0 ≤ μM y.k ∧ 0 ≤ μQ y.k ∧ 20 ≤ y.ℓ ∧ 0 < dec y.ε ∧ dec y.ε ≤ 1 / 8 ∧
      0 < θ / (4 * n) ∧ θ / (4 * n) ≤ 1 ∧ 0 < w ∧ w ≤ dec y.R ∧
      dec β ≤ bisectionSignTol y.k (dec y.ε) (θ / (4 * n)) y.ℓ ∧
      640 * y.k * √(y.k : ℝ) * (8 + μM y.k) *
        (newtonSchulzSteps (w / (8 * dec y.R)) (dec β / (16 * y.k)) + 1) * u ≤
          w / (4 * dec y.R) * dec β ∧
      (4 * μQ y.k + 4 * √(y.k : ℝ) * (cN + 1) + 2 * μM y.k + 1) * u ≤ dec β ∧
      newtonSchulzSteps (w / (8 * dec y.R)) (dec β / (16 * y.k)) ≤ signFuel ∧
      τ * (4 * y.k * √(y.k : ℝ)) ≤ min (√(θ / (4 * n) / 2)) (dec y.ε * dec R₀) ∧
      16 * (dec R₀ + dec y.R + y.k + y.ℓ + √(Real.log (4 / (θ / (4 * n))))) ≤ Ω := by
  have hk2 : (2 : ℝ) ≤ y.k := by exact_mod_cast hk
  have hkn' : (y.k : ℝ) ≤ n := by exact_mod_cast hkn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl20' : (20 : ℝ) ≤ ℓ := by exact_mod_cast hl20
  have hL1 : (ℓ : ℝ) ≤ y.ℓ := by exact_mod_cast hℓy
  have hL2 : (y.ℓ : ℝ) ≤ 2 * ℓ := by exact_mod_cast hℓy₂
  have hεy0 : 0 < dec y.ε := by linarith
  have hk0 : 0 < y.k := by omega
  have hL0 : 0 < y.ℓ := by omega
  have hn0 : 0 < n := by omega
  have hl0 : 0 < ℓ := by omega
  have hu100 : u ≤ 1 / 100 := by
    have : (1 : ℝ) ≤ (ℓ : ℝ) ^ 2 := one_le_pow₀ (by linarith)
    linarith [mul_le_mul_of_nonneg_right this hu]
  have hRpos : 0 < dec y.R := hM.pos_of_le_mul_eq_false hu100 hint hR₀pos hε
    (hε₁.trans (by norm_num)) hεy hεy₁ hτ100 (by linarith)
  have hD : 0 < (2 * y.k * y.ℓ * (n + 1) * (ℓ + 1) : ℝ) := by positivity
  have hD1 : θ ≤ (2 * y.k * y.ℓ * (n + 1) * (ℓ + 1) : ℝ) := by
    have h1 : (1 : ℝ) ≤ 2 * y.k * y.ℓ := one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
    have h2 := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h1
      (by linarith : (1 : ℝ) ≤ n + 1)) (by linarith : (1 : ℝ) ≤ ℓ + 1)
    linarith
  have hkL : (y.k : ℝ) * y.ℓ ≤ n * (2 * ℓ) := mul_le_mul hkn' hL2 (by positivity) (by positivity)
  have hw8 : w / (8 * dec y.R) = θ / (16 * y.k * y.ℓ * (n + 1) * (ℓ + 1)) := by
    rw [hw]; field_simp; ring
  have hw4 : w / (4 * dec y.R) = θ / (8 * y.k * y.ℓ * (n + 1) * (ℓ + 1)) := by
    rw [hw]; field_simp; ring
  have hNy : newtonSchulzSteps (w / (8 * dec y.R)) (dec β / (16 * y.k)) ≤ Nst := by
    rw [hw8, hN]
    refine (newtonSchulzSteps_le_of_le_abs (a := θ / (32 * n * (n + 1) * ℓ * (ℓ + 1)))
      (by positivity) ?_).trans (newtonSchulzSteps_le_of_le (by positivity) ?_ ?_)
    · rw [abs_of_pos (by positivity)]
      apply div_le_div_of_nonneg_left hθ.le (by positivity)
      linarith [mul_le_mul_of_nonneg_right hkL (by positivity : (0 : ℝ) ≤ 16 * (n + 1) * (ℓ + 1))]
    · exact div_le_div_of_nonneg_left hβ.le (by positivity) (by linarith)
    · rw [div_le_iff₀ (by positivity)]; linarith
  have hNy0 : 0 ≤ newtonSchulzSteps (w / (8 * dec y.R)) (dec β / (16 * y.k)) :=
    newtonSchulzSteps_nonneg_of_pos (by rw [hw8]; positivity) (by positivity)
      (by rw [div_le_iff₀ (by positivity)]; linarith)
  have hsk : √(y.k : ℝ) ≤ √n := Real.sqrt_le_sqrt hkn'
  have h4ρ : 4 / (θ / (4 * n)) = 16 * n / θ := by field_simp; ring
  refine ⟨hRpos, hμM₀.trans (hμM (Nat.zero_le _)), hμQ₀.trans (hμQ (Nat.zero_le _)), by omega,
    hεy0, by linarith [hε₁.trans (by norm_num : (2⁻¹ : ℝ) ^ 15 ≤ 1 / 8)], by positivity,
    by rw [div_le_one (by positivity)]; linarith, by rw [hw]; positivity, ?_,
    le_bisectionSignTol_of_le_div (by omega) hkn hℓy hℓy₂ hl20 hε hεy hθ hβle, ?_, ?_,
    hNy.trans hfuel, ?_, ?_⟩
  · rw [hw, div_le_iff₀ hD]; linarith [mul_le_mul_of_nonneg_left hD1 hRpos.le]
  · have hA : 640 * y.k * √(y.k : ℝ) * (8 + μM y.k) ≤ 640 * n * √(n : ℝ) * (8 + μM n) := by
      have := hμM hkn
      have := hμM₀.trans (hμM (Nat.zero_le y.k))
      gcongr
    calc 640 * y.k * √(y.k : ℝ) * (8 + μM y.k) *
          (newtonSchulzSteps (w / (8 * dec y.R)) (dec β / (16 * y.k)) + 1) * u
        ≤ 640 * n * √(n : ℝ) * (8 + μM n) * (Nst + 1) * u :=
          mul_le_mul_of_nonneg_right (mul_le_mul hA (by linarith) (by linarith)
            (by have := hμM₀.trans (hμM (Nat.zero_le n)); positivity)) hu
      _ ≤ θ * dec β / (16 * n * (n + 1) * ℓ * (ℓ + 1)) := by
          rw [le_div_iff₀ (by positivity)]; linarith
      _ ≤ w / (4 * dec y.R) * dec β := by
          rw [hw4, div_mul_eq_mul_div]
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          linarith [mul_le_mul_of_nonneg_right hkL
            (by positivity : (0 : ℝ) ≤ 8 * (n + 1) * (ℓ + 1))]
  · refine le_trans (mul_le_mul_of_nonneg_right ?_ hu) hudefl
    linarith [hμQ hkn, hμM hkn, mul_le_mul_of_nonneg_right hsk (by linarith : (0 : ℝ) ≤ cN + 1)]
  · have hX : τ * (4 * y.k * √(y.k : ℝ)) ≤ τ * (4 * n * √(n : ℝ)) := by gcongr
    have hX1 : τ * (4 * n * √(n : ℝ)) * 25 = τ * (100 * n * √(n : ℝ)) := by ring
    have hX0 : 0 ≤ τ * (4 * n * √(n : ℝ)) := by positivity
    rw [show θ / (4 * n) / 2 = θ / (8 * n) by ring]
    refine le_min (hX.trans (by linarith [hτ.trans (min_le_left _ _)])) ?_
    have hτ' := hτ.trans (min_le_right _ _)
    linarith [mul_le_mul_of_nonneg_left (min_le_left (dec R₀) 1) hε.le,
      mul_le_mul_of_nonneg_right hεy hR₀pos.le, mul_pos hεy0 hR₀pos]
  · rw [h4ρ]; linarith

private theorem FloatMachine.IsAccurate.isEighGoodSample_of_forall_isHermitian_imp
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) (hu : 0 ≤ u)
    (hμM : Monotone μM) (hμQ : Monotone μQ) (hμM₀ : 0 ≤ μM 0) (hμQ₀ : 0 ≤ μQ 0) (hcN : 0 ≤ cN)
    {n : ℕ} (hn : 1 ≤ n) {A : Matrix (Fin n) (Fin n) (F × F)}
    (hA : (decodeMatrix dec A).IsHermitian) {R₀ ε β : F} {θ : ℝ}
    (hR₀ : specNorm (decodeMatrix dec A) ≤ dec R₀) (hR₀pos : 0 < dec R₀)
    (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) {ℓ : ℕ}
    (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hl20 : 20 ≤ ℓ) (hu₁ : 100 * (ℓ : ℝ) ^ 2 * u ≤ 1)
    (hβ : 0 < dec β) (hb1 : dec β ≤ 1)
    (hβle : dec β ≤ dec ε * √θ / (2880 * ℓ * n * √(n : ℝ) *
      (2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ))))) {Nst : ℝ}
    (hN : Nst = newtonSchulzSteps (θ / (32 * n * (n + 1) * ℓ * (ℓ + 1))) (dec β / (16 * n)))
    (husign : 640 * n * √(n : ℝ) * (8 + μM n) * (Nst + 1) * (16 * n * (n + 1) * ℓ * (ℓ + 1)) *
      u ≤ θ * dec β)
    (hudefl : (4 * μQ n + 4 * √(n : ℝ) * (cN + 1) + 2 * μM n + 1) * u ≤ dec β) {signFuel : ℕ}
    (hfuel : Nst ≤ signFuel) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (100 * n * √(n : ℝ)) ≤ min (√(θ / (8 * n))) (dec ε * min (dec R₀) 1))
    (hτ100 : 100 * τ ≤ dec ε * min (dec R₀) 1) (hΩ16 : 16 * (dec R₀ + ℓ) ≤ Ω)
    (hΩ : 16 * (2 * dec R₀ + n + 2 * ℓ + √(Real.log (16 * n / θ))) ≤ Ω)
    {s : List Bool → EighSample ℝ ℂ n}
    (hS : ∀ (a : List Bool) (y : EighNode F),
      eighNodeAt M n signFuel R₀ β a ⟨n, A, R₀, ε, ℓ⟩ s = some y → 2 ≤ y.k →
        M.le y.R (M.mul y.ε R₀) = false → (decodeMatrix dec y.A).IsHermitian →
        specNorm (decodeMatrix dec y.A) ≤ dec y.R →
        IsEighGoodSample dec (θ * dec y.R / (2 * y.k * y.ℓ * (n + 1) * (ℓ + 1)))
          (√(θ / (4 * n) / 2) / y.k)
          (√2 * (2 * √(y.k : ℝ) + √(2 * Real.log (4 / (θ / (4 * n)))))) y (s a)) :
    ∀ (a : List Bool) (y : EighNode F),
      eighNodeAt M n signFuel R₀ β a ⟨n, A, R₀, ε, ℓ⟩ s = some y → 2 ≤ y.k →
        M.le y.R (M.mul y.ε R₀) = false →
        IsEighGoodSample dec (θ * dec y.R / (2 * y.k * y.ℓ * (n + 1) * (ℓ + 1)))
          (√(θ / (8 * n)) / y.k) (√2 * (2 * √(y.k : ℝ) + √(2 * Real.log (16 * n / θ)))) y
          (s a) := by
  have hinv : ∀ (a : List Bool) (y : EighNode F),
      eighNodeAt M n signFuel R₀ β a ⟨n, A, R₀, ε, ℓ⟩ s = some y →
        (decodeMatrix dec y.A).IsHermitian ∧ specNorm (decodeMatrix dec y.A) ≤ dec y.R := by
    intro a
    induction a using List.reverseRecOn with
    | nil =>
      intro y hy
      simp only [eighNodeAt, Option.some.injEq] at hy
      subst hy
      exact ⟨hA, hR₀⟩
    | append_singleton a b ih =>
      intro y hy
      rw [eighNodeAt_append_singleton] at hy
      obtain ⟨z, hz, hzy⟩ := Option.bind_eq_some_iff.1 hy
      obtain ⟨hH, hNz⟩ := ih z hz
      obtain ⟨hk, hint⟩ := two_le_k_and_le_eq_false_of_eighChild_eq_some hzy
      obtain ⟨hlen, hkn, hLz, hεz, hεz₁, hRz⟩ :=
        hM.eighNodeAt_eq_some_params hε hε₁ hR₀pos hℓ hu hu₁ hτ₀ hτ100 hΩ16 A s hz
      obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ :=
        hM.pos_and_le_of_eighNode hu hμM hμQ hμM₀ hμQ₀ hcN hn hR₀pos hε hε₁ hθ hθ₁ hl20 hu₁ hβ
          hb1 hβle hN husign hudefl hfuel hτ₀ hτ hτ100 hΩ16 hΩ hk hint hkn (by omega)
          (by omega) hεz hεz₁ hRz rfl
      exact hM.isHermitian_and_specNorm_le_of_eighChild_eq_some h1 h2 hcN hu hH hNz h3 h4 h5
        hR₀pos h6 h7 h8 h9 hβ h10 h11 h12 h13 hτ₀ h14 h15 (fun _ _ => hS a z hz hk hint hH hNz)
        hzy
  intro a y hy hk hint
  obtain ⟨hH, hNy⟩ := hinv a y hy
  have h := hS a y hy hk hint hH hNy
  rwa [show θ / (4 * n) / 2 = θ / (8 * n) by ring,
    show 4 / (θ / (4 * n)) = 16 * n / θ by field_simp; ring] at h

private theorem FloatMachine.IsAccurate.eighSampleLaw_not_isEighGoodSample_le
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) (hu : 0 ≤ u)
    (hμM : Monotone μM) (hμQ : Monotone μQ) (hμM₀ : 0 ≤ μM 0) (hμQ₀ : 0 ≤ μQ 0) (hcN : 0 ≤ cN)
    {n : ℕ} (hn : 1 ≤ n) {R₀ ε β : F} {θ : ℝ} (hR₀pos : 0 < dec R₀)
    (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) {ℓ : ℕ}
    (hl20 : 20 ≤ ℓ) (hu₁ : 100 * (ℓ : ℝ) ^ 2 * u ≤ 1) (hβ : 0 < dec β) (hb1 : dec β ≤ 1)
    (hβle : dec β ≤ dec ε * √θ / (2880 * ℓ * n * √(n : ℝ) *
      (2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ))))) {Nst : ℝ}
    (hN : Nst = newtonSchulzSteps (θ / (32 * n * (n + 1) * ℓ * (ℓ + 1))) (dec β / (16 * n)))
    (husign : 640 * n * √(n : ℝ) * (8 + μM n) * (Nst + 1) * (16 * n * (n + 1) * ℓ * (ℓ + 1)) *
      u ≤ θ * dec β)
    (hudefl : (4 * μQ n + 4 * √(n : ℝ) * (cN + 1) + 2 * μM n + 1) * u ≤ dec β) {signFuel : ℕ}
    (hfuel : Nst ≤ signFuel) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (100 * n * √(n : ℝ)) ≤ min (√(θ / (8 * n))) (dec ε * min (dec R₀) 1))
    (hτ100 : 100 * τ ≤ dec ε * min (dec R₀) 1) (hΩ16 : 16 * (dec R₀ + ℓ) ≤ Ω)
    (hΩ : 16 * (2 * dec R₀ + n + 2 * ℓ + √(Real.log (16 * n / θ))) ≤ Ω)
    {y : EighNode F} (hk : 2 ≤ y.k) (hint : M.le y.R (M.mul y.ε R₀) = false) (hkn : y.k ≤ n)
    (hℓy : ℓ ≤ y.ℓ) (hℓy₂ : y.ℓ ≤ 2 * ℓ) (hεy : dec ε / 3 ≤ dec y.ε) (hεy₁ : dec y.ε ≤ dec ε)
    (hRy : dec y.R ≤ dec R₀) (hH : (decodeMatrix dec y.A).IsHermitian)
    (hNy : specNorm (decodeMatrix dec y.A) ≤ dec y.R) :
    eighSampleLaw n {z | ¬ IsEighGoodSample dec (θ * dec y.R / (2 * y.k * y.ℓ * (n + 1) * (ℓ + 1)))
      (√(θ / (4 * n) / 2) / y.k) (√2 * (2 * √(y.k : ℝ) + √(2 * Real.log (4 / (θ / (4 * n))))))
      y z} ≤ ENNReal.ofReal (θ / (2 * (n + 1) * (ℓ + 1))) + ENNReal.ofReal (2 * (θ / (4 * n))) *
        eighSampleLaw n {z | (eighStep M n signFuel R₀ β y.A y.R y.ε y.ℓ z).IsSplit} := by
  obtain ⟨hRpos, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ :=
    hM.pos_and_le_of_eighNode hu hμM hμQ hμM₀ hμQ₀ hcN hn hR₀pos hε hε₁ hθ hθ₁ hl20 hu₁ hβ
      hb1 hβle hN husign hudefl hfuel hτ₀ hτ hτ100 hΩ16 hΩ hk hint hkn hℓy hℓy₂ hεy hεy₁ hRy rfl
  refine (hM.measure_not_isEighGoodSample_le h1 h2 hcN hu hH hNy hk hkn h3 h4 h5 hR₀pos hint
    h6 h7 h8 h9 hβ h10 h11 h12 h13 hτ₀ h14 h15).trans
    (add_le_add (ENNReal.ofReal_le_ofReal (le_of_eq ?_)) le_rfl)
  have : (y.k : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ y.k := by exact_mod_cast hk
    linarith
  have : (y.ℓ : ℝ) ≠ 0 := by
    have : (20 : ℝ) ≤ y.ℓ := by exact_mod_cast h3
    linarith
  field_simp

private theorem FloatMachine.IsAccurate.tsum_elim_le
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) {n : ℕ} (hn : 1 ≤ n)
    {signFuel : ℕ} {R₀ ε β : F} {θ : ℝ} (hθ : 0 < θ) (hR₀pos : 0 < dec R₀) (hε : 0 < dec ε)
    (hε₁ : dec ε ≤ 2⁻¹ ^ 15) {ℓ : ℕ} (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hu : 0 ≤ u)
    (hu₁ : 100 * (ℓ : ℝ) ^ 2 * u ≤ 1) (hτ₀ : 0 ≤ τ) (hτ100 : 100 * τ ≤ dec ε * min (dec R₀) 1)
    (hΩ16 : 16 * (dec R₀ + ℓ) ≤ Ω) (A : Matrix (Fin n) (Fin n) (F × F))
    (V : EighNode F → Prop) [DecidablePred V] (s : List Bool → EighSample ℝ ℂ n) :
    ∑' a, (eighNodeAt M n signFuel R₀ β a ⟨n, A, R₀, ε, ℓ⟩ s).elim 0 (fun y => if V y then
      ENNReal.ofReal (θ / (2 * (n + 1) * (ℓ + 1))) + ENNReal.ofReal (2 * (θ / (4 * n))) *
        {z | (eighStep M n signFuel R₀ β y.A y.R y.ε y.ℓ z).IsSplit}.indicator 1 (s a)
      else 0) ≤ ENNReal.ofReal θ := by
  set C₁ : ℝ≥0∞ := ENNReal.ofReal (θ / (2 * (n + 1) * (ℓ + 1)))
  set C₂ : ℝ≥0∞ := ENNReal.ofReal (2 * (θ / (4 * n)))
  set Spl : EighNode F → Set (EighSample ℝ ℂ n) := fun y =>
    {z | (eighStep M n signFuel R₀ β y.A y.R y.ε y.ℓ z).IsSplit}
  have hle : ∀ a, ((eighNodeAt M n signFuel R₀ β a ⟨n, A, R₀, ε, ℓ⟩ s).elim 0 fun y =>
      if V y then C₁ + C₂ * (Spl y).indicator 1 (s a) else 0) ≤
      {a | eighNodeAt M n signFuel R₀ β a ⟨n, A, R₀, ε, ℓ⟩ s ≠ none}.indicator
        (fun _ => C₁) a +
      {a | ∃ y, eighNodeAt M n signFuel R₀ β a ⟨n, A, R₀, ε, ℓ⟩ s = some y ∧
        (eighStep M n signFuel R₀ β y.A y.R y.ε y.ℓ (s a)).IsSplit}.indicator
        (fun _ => C₂) a := by
    intro a
    rcases hX : eighNodeAt M n signFuel R₀ β a ⟨n, A, R₀, ε, ℓ⟩ s with _ | y
    · exact zero_le
    simp only [Option.elim_some]
    split_ifs with hV
    · have hmem : a ∈ {a | eighNodeAt M n signFuel R₀ β a ⟨n, A, R₀, ε, ℓ⟩ s ≠ none} := by
        simp [hX]
      rw [Set.indicator_of_mem hmem]
      gcongr
      by_cases hsp : s a ∈ Spl y
      · have hmem2 : a ∈ {a | ∃ y, eighNodeAt M n signFuel R₀ β a ⟨n, A, R₀, ε, ℓ⟩ s = some y ∧
            (eighStep M n signFuel R₀ β y.A y.R y.ε y.ℓ (s a)).IsSplit} := ⟨y, hX, hsp⟩
        rw [Set.indicator_of_mem hsp, Set.indicator_of_mem hmem2]
        simp
      · rw [Set.indicator_of_notMem hsp]
        simp
    · exact zero_le
  refine (ENNReal.tsum_le_tsum hle).trans ?_
  rw [ENNReal.tsum_add, ← tsum_subtype, ← tsum_subtype, ENNReal.tsum_set_const,
    ENNReal.tsum_set_const]
  have e1 := hM.encard_eighNodeAt_ne_none_le (N := n) (signFuel := signFuel) (β := β) hε hε₁
    hR₀pos hℓ hu hu₁ hτ₀ hτ100 hΩ16 A s
  have e2 := encard_eighNodeAt_isSplit_le M (signFuel := signFuel) (R₀ := R₀) (β := β)
    ⟨n, A, R₀, ε, ℓ⟩ s
  calc _ ≤ (((n + 1) * (ℓ + 1) : ℕ) : ℝ≥0∞) * C₁ + (n : ℝ≥0∞) * C₂ := by
        gcongr
        · exact_mod_cast e1
        · exact_mod_cast e2
    _ = ENNReal.ofReal θ := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast n,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        have : (n : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ n := by exact_mod_cast hn
                                 linarith
        push_cast
        field_simp
        ring

private theorem isProbabilityMeasure_eighSampleLaw (N : ℕ) :
    IsProbabilityMeasure (eighSampleLaw N) := by
  unfold eighSampleLaw
  have : IsProbabilityMeasure (ProbabilityTheory.cond volume (Set.Icc (-1 : ℝ) 1)) :=
    ProbabilityTheory.cond_isProbabilityMeasure_of_finite (by simp [Real.volume_Icc])
      (by simp [Real.volume_Icc])
  infer_instance

private theorem FloatMachine.IsAccurate.measureReal_eigh_le_of_measurable
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hunifm : ∀ c z, MeasurableSet (M.unif c ⁻¹' {z}))
    (hunifc : ∀ c, (Set.range (M.unif c)).Countable)
    (hnormalm : ∀ z, MeasurableSet (M.normal ⁻¹' {z})) (hnormalc : (Set.range M.normal).Countable)
    (hμM : Monotone μM) (hμQ : Monotone μQ) (hμM₀ : 0 ≤ μM 0) (hμQ₀ : 0 ≤ μQ 0) (hcN : 0 ≤ cN)
    {n : ℕ} {A : Matrix (Fin n) (Fin n) (F × F)} (hA : (decodeMatrix dec A).IsHermitian)
    {R₀ ε β : F} {θ : ℝ} (hR₀ : specNorm (decodeMatrix dec A) ≤ dec R₀) (hR₀pos : 0 < dec R₀)
    (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) {ℓ : ℕ}
    (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hβ : 0 < dec β)
    (hβle : dec β ≤ dec ε * √θ / (2880 * ℓ * n * √(n : ℝ) *
      (2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ))))) {Nst : ℝ}
    (hN : Nst = newtonSchulzSteps (θ / (32 * n * (n + 1) * ℓ * (ℓ + 1))) (dec β / (16 * n)))
    (husign : 640 * n * √(n : ℝ) * (8 + μM n) * (Nst + 1) * (16 * n * (n + 1) * ℓ * (ℓ + 1)) *
      u ≤ θ * dec β)
    (hudefl : (4 * μQ n + 4 * √(n : ℝ) * (cN + 1) + 2 * μM n + 1) * u ≤ dec β) {signFuel : ℕ}
    (hfuel : Nst ≤ signFuel) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (100 * n * √(n : ℝ)) ≤ min (√(θ / (8 * n))) (dec ε * min (dec R₀) 1))
    (hΩ : 16 * (2 * dec R₀ + n + 2 * ℓ + √(Real.log (16 * n / θ))) ≤ Ω) {Ω' : Type*}
    {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'} {ζ : List Bool → Ω' → EighSample ℝ ℂ n}
    (hζ : ∀ a, Measurable (ζ a)) (hind : iIndepFun ζ μ)
    (hlaw : ∀ a, HasLaw (ζ a) (eighSampleLaw n) μ) :
    μ.real {ω | ¬ IsApproxDiagonalization (decodeMatrix dec A)
      (decodeMatrix dec (eigh M signFuel ℓ A R₀ ε β fun a => ζ a ω).1)
      (fun i => dec ((eigh M signFuel ℓ A R₀ ε β fun a => ζ a ω).2 i)) (2 * dec ε * dec R₀)
      (dec ε / 3)} ≤ θ := by
  classical
  obtain ⟨hu, hn, hl20, hNst, hb1, hu₁, hτ100, hΩ16⟩ := hM.nonneg_and_one_le_and_mul_le hμM hμM₀
    hR₀pos hε hε₁ hθ hθ₁ hℓ hβ hβle hN husign hτ₀ hτ hΩ
  have := isProbabilityMeasure_eighSampleLaw n
  have : IsProbabilityMeasure μ := (hlaw []).isProbabilityMeasure_iff.2 this
  let V : EighNode F → Prop := fun y => 2 ≤ y.k ∧ M.le y.R (M.mul y.ε R₀) = false ∧
    (decodeMatrix dec y.A).IsHermitian ∧ specNorm (decodeMatrix dec y.A) ≤ dec y.R ∧ y.k ≤ n ∧
    ℓ ≤ y.ℓ ∧ y.ℓ ≤ 2 * ℓ ∧ dec ε / 3 ≤ dec y.ε ∧ dec y.ε ≤ dec ε ∧ dec y.R ≤ dec R₀
  let G : EighNode F → EighSample ℝ ℂ n → Prop := fun y z =>
    IsEighGoodSample dec (θ * dec y.R / (2 * y.k * y.ℓ * (n + 1) * (ℓ + 1)))
      (√(θ / (4 * n) / 2) / y.k) (√2 * (2 * √(y.k : ℝ) + √(2 * Real.log (4 / (θ / (4 * n)))))) y z
  let Spl : EighNode F → Set (EighSample ℝ ℂ n) := fun y =>
    {z | (eighStep M n signFuel R₀ β y.A y.R y.ε y.ℓ z).IsSplit}
  let C₁ : ℝ≥0∞ := ENNReal.ofReal (θ / (2 * (n + 1) * (ℓ + 1)))
  let C₂ : ℝ≥0∞ := ENNReal.ofReal (2 * (θ / (4 * n)))
  let X : List Bool → Ω' → Option (EighNode F) := fun a ω =>
    eighNodeAt M n signFuel R₀ β a ⟨n, A, R₀, ε, ℓ⟩ fun b => ζ b ω
  have hsub : {ω | ¬ IsApproxDiagonalization (decodeMatrix dec A)
      (decodeMatrix dec (eigh M signFuel ℓ A R₀ ε β fun a => ζ a ω).1)
      (fun i => dec ((eigh M signFuel ℓ A R₀ ε β fun a => ζ a ω).2 i)) (2 * dec ε * dec R₀)
      (dec ε / 3)} ⊆ {ω | ∃ a, ζ a ω ∈ {z | ∃ y, X a ω = some y ∧ V y ∧ ¬ G y z}} := by
    intro ω hω
    by_contra hne
    apply hω
    refine hM.isApproxDiagonalization_eigh_of_forall_isEighGoodSample hu hμM hμQ hμM₀ hμQ₀ hcN hA
      hR₀ hR₀pos hε hε₁ hθ hθ₁ hℓ hβ hβle hN husign hudefl hfuel hτ₀ hτ hΩ ?_
    refine hM.isEighGoodSample_of_forall_isHermitian_imp hu hμM hμQ hμM₀ hμQ₀ hcN hn hA hR₀
      hR₀pos hε hε₁ hθ hθ₁ hℓ hl20 hu₁ hβ hb1 hβle hN husign hudefl hfuel hτ₀ hτ hτ100 hΩ16 hΩ ?_
    intro a y hy hk hint hH hNy
    obtain ⟨hlen, hkn, hLy, hεy, hεy₁, hRy⟩ :=
      hM.eighNodeAt_eq_some_params hε hε₁ hR₀pos hℓ hu hu₁ hτ₀ hτ100 hΩ16 A _ hy
    by_contra hbad
    exact hne ⟨a, y, hy, ⟨hk, hint, hH, hNy, hkn, by omega, by omega, hεy, hεy₁, hRy⟩, hbad⟩
  refine (measureReal_mono hsub).trans ?_
  refine measureReal_exists_mem_le_of_forall_measure_le_lintegral hlaw (X := X)
    (fun a => (countable_range_eighNodeAt hunifc hnormalc n signFuel R₀ β a _).mono
      (by rintro _ ⟨ω, rfl⟩; exact ⟨_, rfl⟩))
    (fun a y => measurableSet_eighNodeAt_eq hunifm hunifc hnormalm hnormalc hζ a _ y)
    (fun a y => indepFun_eighNodeAt_eq hunifm hunifc hnormalm hnormalc hζ hind a _ y)
    (S := fun _ oy => {z | ∃ y, oy = some y ∧ V y ∧ ¬ G y z})
    (q := fun _ oy z => oy.elim 0 fun y => if V y then C₁ + C₂ * (Spl y).indicator 1 z else 0)
    ?_ ?_ hθ.le ?_
  · intro a oy
    rcases oy with _ | y
    · simp only [Option.elim_none]
      exact measurable_const
    · simp only [Option.elim_some]
      split_ifs
      · exact measurable_const.add (((measurable_const : Measurable fun _ :
          EighSample ℝ ℂ n => (1 : ℝ≥0∞)).indicator
          (measurableSet_setOf_eighStep_isSplit hunifm hunifc n signFuel R₀ β y.A y.R y.ε
            y.ℓ)).const_mul _)
      · exact measurable_const
  · intro a oy
    rcases oy with _ | y
    · simp
    by_cases hV : V y
    · have hS : {z | ∃ y', some y = some y' ∧ V y' ∧ ¬ G y' z} = {z | ¬ G y z} := by
        ext z
        simp only [Set.mem_ofPred_eq, Option.some.injEq]
        exact ⟨fun ⟨_, h, _, hg⟩ => h ▸ hg, fun hg => ⟨y, rfl, hV, hg⟩⟩
      have hs := measurableSet_setOf_eighStep_isSplit hunifm hunifc n signFuel R₀ β y.A y.R y.ε
        y.ℓ
      rw [hS]
      simp only [Option.elim_some, if_pos hV]
      rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
        lintegral_const_mul _ (measurable_one.indicator hs), lintegral_indicator_one hs]
      obtain ⟨hk, hint, hH, hNy, hkn, hLy, hLy₂, hεy, hεy₁, hRy⟩ := hV
      exact hM.eighSampleLaw_not_isEighGoodSample_le hu hμM hμQ hμM₀ hμQ₀ hcN hn hR₀pos hε hε₁
        hθ hθ₁ hl20 hu₁ hβ hb1 hβle hN husign hudefl hfuel hτ₀ hτ hτ100 hΩ16 hΩ hk hint hkn hLy
        hLy₂ hεy hεy₁ hRy hH hNy
    · have hS : {z | ∃ y', some y = some y' ∧ V y' ∧ ¬ G y' z} = ∅ := by
        ext z
        simp only [Set.mem_ofPred_eq, Option.some.injEq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨_, rfl, hV', -⟩
        exact hV hV'
      rw [hS, measure_empty]
      exact zero_le
  · exact fun ω => hM.tsum_elim_le hn hθ hR₀pos hε hε₁ hℓ hu hu₁ hτ₀ hτ100 hΩ16 A V
      (fun b => ζ b ω)

/-- **Hermitian diagonalization in linear precision** (Theorem 4.2): let the machine meet
`NLAlib.FloatMachine.IsAccurate` $u$ $\tau$ $\Omega$ (constants $\mu_{\mathrm{MM}}$,
$\mu_{\mathrm{QR}}$, $c_{\mathrm N}$), with $\mu_{\mathrm{MM}}, \mu_{\mathrm{QR}}$ monotone
and nonnegative, $c_{\mathrm N} \ge 0$, and the samplers with measurable fibres and countable
ranges. Let the stored $\mathbf{A}$ have Hermitian decoding with $\|\mathbf{A}\|_2 \le R_0$, for
stored $R_0 > 0$, $\varepsilon$, $\beta$ (decoded values) with $0 < \varepsilon \le 2^{-15}$, $0 <
\theta \le 1$, a depth counter $\ell \ge$ `NLAlib.bisectionDepth` $\varepsilon$, and the
precomputed accuracy $$0 < \beta \le \frac{\varepsilon\sqrt\theta}{2880\,\ell\, n^{3/2}\bigl(2\sqrt
n + \sqrt{2\log(16n/\theta)}\bigr)} \,, \qquad
N_* = N\Bigl(\frac{\theta}{32n(n+1)\ell(\ell+1)}, \frac{\beta}{16n}\Bigr) \,.$$
If $640\,n^{3/2}(8 + \mu_{\mathrm{MM}}(n))(N_* + 1)\cdot16n(n+1)\ell(\ell+1)\,u \le
\theta\beta$, $(4\mu_{\mathrm{QR}}(n) + 4\sqrt n(c_{\mathrm N} + 1) + 2\mu_{\mathrm{MM}}(n) + 1)u
\le \beta$, the sign step limit is at least $N_*$, $0 \le \tau$,
$100n^{3/2}\tau \le \min(\sqrt{\theta/(8n)}, \varepsilon\min(R_0, 1))$,
$16(2R_0 + n + 2\ell + \sqrt{\log(16n/\theta)}) \le \Omega$, and the node samples $\zeta_a$ are
independent, each of law `NLAlib.eighSampleLaw` $n$, then
$$\mathbb{P}\bigl[\mathsf{eigh}(\mathbf{A}, \varepsilon, \theta) \text{ is not an approximate
diagonalization with residual } 2\varepsilon R_0 \text{ and } \mathbf{U} \text{ within }
\varepsilon/3 \text{ of unitary}\bigr] \le \theta \,,$$
$\mathsf{eigh}$ the decoded output of `NLAlib.eigh`. [Shah2024, Theorem 4.2], there with
$R_0 = \|\mathbf{A}\|_2$, node-dependent accuracies, the bit count of
`NLAlib.measureReal_not_isApproxDiagonalization_eigh_le_of_logb_le` with other constants, and an
operation count (not formalized).
Proof: the bad event is contained in "some internal node of the tree has a bad sample"
(contrapositive of
`NLAlib.FloatMachine.IsAccurate.isApproxDiagonalization_eigh_of_forall_isEighGoodSample`). Apply
`NLAlib.measureReal_exists_mem_le_of_forall_measure_le_lintegral` with index the paths, state $X_a$
the node at $a$ (`NLAlib.countable_range_eighNodeAt`, `NLAlib.measurableSet_eighNodeAt_eq`,
`NLAlib.indepFun_eighNodeAt_eq`), bad set the complement of `NLAlib.IsEighGoodSample` at internal
nodes (empty elsewhere) and charge $k w \ell/R + 2\rho\,[\text{split}]$ = $\theta/(2(n+1)(\ell+1))
+ (\theta/(2n))[\text{split}]$ (`NLAlib.FloatMachine.IsAccurate.measure_not_isEighGoodSample_le`);
the charges sum to at most $\theta/2 + \theta/2$ by
`NLAlib.FloatMachine.IsAccurate.encard_eighNodeAt_ne_none_le` and
`NLAlib.encard_eighNodeAt_isSplit_le`. The node hypotheses come from the global ones as in the
proof of `NLAlib.FloatMachine.IsAccurate.isApproxDiagonalization_eigh_of_forall_isEighGoodSample`,
with `NLAlib.FloatMachine.IsAccurate.eighNodeAt_eq_some_params` ($\ell_y \le 2\ell$,
$\varepsilon_y \ge \varepsilon/3$, $R_y \le R_0$). Two side obligations: the charge contains the
indicator of the split seeds, which UB1's `hq` needs measurable: it is the countable union over
the range of `unif` of its fibres (`hunifc`, `hunifm`), about 20 lines; and
`MeasureTheory.IsProbabilityMeasure` $\mu$ comes from `hlaw`
(`ProbabilityTheory.HasLaw.isProbabilityMeasure_iff`, `NLAlib.eighSampleLaw` being a probability
measure: `ProbabilityTheory.cond` of `Set.Icc` with positive finite volume, `Measure.pi`,
`Measure.prod`). L, about 140 lines. -/
theorem FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hunifm : ∀ c z, MeasurableSet (M.unif c ⁻¹' {z}))
    (hunifc : ∀ c, (Set.range (M.unif c)).Countable)
    (hnormalm : ∀ z, MeasurableSet (M.normal ⁻¹' {z})) (hnormalc : (Set.range M.normal).Countable)
    (hμM : Monotone μM) (hμQ : Monotone μQ) (hμM₀ : 0 ≤ μM 0) (hμQ₀ : 0 ≤ μQ 0) (hcN : 0 ≤ cN)
    {n : ℕ} {A : Matrix (Fin n) (Fin n) (F × F)} (hA : (decodeMatrix dec A).IsHermitian)
    {R₀ ε β : F} {θ : ℝ} (hR₀ : specNorm (decodeMatrix dec A) ≤ dec R₀) (hR₀pos : 0 < dec R₀)
    (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) {ℓ : ℕ}
    (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hβ : 0 < dec β)
    (hβle : dec β ≤ dec ε * √θ / (2880 * ℓ * n * √(n : ℝ) *
      (2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ))))) {Nst : ℝ}
    (hN : Nst = newtonSchulzSteps (θ / (32 * n * (n + 1) * ℓ * (ℓ + 1))) (dec β / (16 * n)))
    (husign : 640 * n * √(n : ℝ) * (8 + μM n) * (Nst + 1) * (16 * n * (n + 1) * ℓ * (ℓ + 1)) *
      u ≤ θ * dec β)
    (hudefl : (4 * μQ n + 4 * √(n : ℝ) * (cN + 1) + 2 * μM n + 1) * u ≤ dec β) {signFuel : ℕ}
    (hfuel : Nst ≤ signFuel) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (100 * n * √(n : ℝ)) ≤ min (√(θ / (8 * n))) (dec ε * min (dec R₀) 1))
    (hΩ : 16 * (2 * dec R₀ + n + 2 * ℓ + √(Real.log (16 * n / θ))) ≤ Ω) {Ω' : Type*}
    {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'} {ζ : List Bool → Ω' → EighSample ℝ ℂ n}
    (hind : iIndepFun ζ μ) (hlaw : ∀ a, HasLaw (ζ a) (eighSampleLaw n) μ) :
    μ.real {ω | ¬ IsApproxDiagonalization (decodeMatrix dec A)
      (decodeMatrix dec (eigh M signFuel ℓ A R₀ ε β fun a => ζ a ω).1)
      (fun i => dec ((eigh M signFuel ℓ A R₀ ε β fun a => ζ a ω).2 i)) (2 * dec ε * dec R₀)
      (dec ε / 3)} ≤ θ := by
  have hae : ∀ᵐ ω ∂μ, ∀ a, ζ a ω = (hlaw a).aemeasurable.mk (ζ a) ω :=
    ae_all_iff.2 fun a => (hlaw a).aemeasurable.ae_eq_mk
  have heq : μ.real {ω | ¬ IsApproxDiagonalization (decodeMatrix dec A)
      (decodeMatrix dec (eigh M signFuel ℓ A R₀ ε β fun a => ζ a ω).1)
      (fun i => dec ((eigh M signFuel ℓ A R₀ ε β fun a => ζ a ω).2 i)) (2 * dec ε * dec R₀)
      (dec ε / 3)} = μ.real {ω | ¬ IsApproxDiagonalization (decodeMatrix dec A)
      (decodeMatrix dec (eigh M signFuel ℓ A R₀ ε β fun a =>
        (hlaw a).aemeasurable.mk (ζ a) ω).1)
      (fun i => dec ((eigh M signFuel ℓ A R₀ ε β fun a =>
        (hlaw a).aemeasurable.mk (ζ a) ω).2 i)) (2 * dec ε * dec R₀) (dec ε / 3)} := by
    refine measureReal_congr (Filter.eventuallyEq_set.2 ?_)
    filter_upwards [hae] with ω hω
    have h2 : (fun a => ζ a ω) = fun a => (hlaw a).aemeasurable.mk (ζ a) ω := funext hω
    simp only [h2]
  rw [heq]
  exact hM.measureReal_eigh_le_of_measurable hunifm hunifc hnormalm
    hnormalc hμM hμQ hμM₀ hμQ₀ hcN hA hR₀ hR₀pos hε hε₁ hθ hθ₁ hℓ hβ hβle hN husign hudefl hfuel
    hτ₀ hτ hΩ (fun a => (hlaw a).aemeasurable.measurable_mk)
    ((iIndepFun_congr fun a => (hlaw a).aemeasurable.ae_eq_mk).1 hind)
    fun a => (hlaw a).congr (hlaw a).aemeasurable.ae_eq_mk.symm

private theorem mul_le_mul_mul_sqrt_of_logb_le {e θ P N L S u : ℝ} (he : 0 < e) (hθ : 0 < θ)
    (hP : 0 < P) (hN : 0 < N) (hL : 0 < L) (hS : 0 < S) (hu : 0 < u)
    (h : Real.logb 2 e⁻¹ + 3 / 2 * Real.logb 2 θ⁻¹ + Real.logb 2 P + Real.logb 2 N +
      3 * Real.logb 2 L + Real.logb 2 S + 26 ≤ Real.logb 2 u⁻¹) :
    u * (2 ^ 26 * P * N * L ^ 3 * S) ≤ e * (θ * √θ) := by
  have hsθ : 0 < √θ := Real.sqrt_pos.mpr hθ
  have hK : 2 ^ 26 * P * N * L ^ 3 * S / (e * (θ * √θ)) ≤ u⁻¹ := by
    rw [← Real.logb_le_logb one_lt_two (by positivity) (by positivity), Real.logb_div
      (by positivity) (by positivity), Real.logb_mul (by positivity) (by positivity),
      Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity)
      (by positivity), Real.logb_mul (by positivity) (by positivity), Real.logb_mul he.ne'
      (by positivity), Real.logb_mul hθ.ne' hsθ.ne', Real.logb_pow,
      Real.logb_pow, Real.sqrt_eq_rpow, Real.logb_rpow_eq_mul_logb_of_pos hθ,
      Real.logb_self_eq_one one_lt_two]
    rw [Real.logb_inv, Real.logb_inv] at h
    push_cast
    linarith
  rw [div_le_iff₀ (by positivity)] at hK
  calc u * (2 ^ 26 * P * N * L ^ 3 * S) ≤ u * (u⁻¹ * (e * (θ * √θ))) :=
        mul_le_mul_of_nonneg_left hK hu.le
    _ = e * (θ * √θ) := by rw [← mul_assoc, mul_inv_cancel₀ hu.ne', one_mul]

private theorem mul_le_mul_and_mul_le_of_mul_le_mul_sqrt {n l sn m D S N b e θ u : ℝ} (hn : 1 ≤ n)
    (hl : 1 ≤ l) (hsn : sn * sn = n) (hsn0 : 0 ≤ sn) (hm : 0 ≤ m) (hD : 0 ≤ D) (hS : 0 < S)
    (hN : 0 ≤ N) (he : 0 ≤ e) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) (hu : 0 ≤ u)
    (key : u * (2 ^ 26 * (n ^ 4 * (n + 1) * (8 + m) + n * sn * D) * (N + 1) * (l + 1) ^ 3 * S) ≤
      e * (θ * √θ))
    (hβ : e * √θ ≤ 2 * (2880 * l * n * sn * S) * b) :
    640 * n * sn * (8 + m) * (N + 1) * (16 * n * (n + 1) * l * (l + 1)) * u ≤ θ * b ∧
      D * u ≤ b := by
  have hsθ : 0 < √θ := Real.sqrt_pos.mpr hθ
  have hsn1 : 1 ≤ sn := by nlinarith
  have hc0 : 0 < 2 * (2880 * l * n * sn * S) := by positivity
  have hA : 0 ≤ n ^ 4 * (n + 1) * (8 + m) := by positivity
  have hB : 0 ≤ n * sn * D := by positivity
  have hl3 : l ^ 2 * (l + 1) ≤ (l + 1) ^ 3 := by nlinarith
  have hl3' : l ≤ (l + 1) ^ 3 := by nlinarith
  constructor
  · refine le_of_mul_le_mul_right ?_ hc0
    calc 640 * n * sn * (8 + m) * (N + 1) * (16 * n * (n + 1) * l * (l + 1)) * u *
          (2 * (2880 * l * n * sn * S))
        = 58982400 * (n ^ 4 * (n + 1) * (8 + m)) * (N + 1) * (l ^ 2 * (l + 1)) * S * u := by
          rw [← hsn]; ring
      _ ≤ 2 ^ 26 * (n ^ 4 * (n + 1) * (8 + m) + n * sn * D) * (N + 1) * (l + 1) ^ 3 * S * u := by
          gcongr ?_ * ?_ * _ * ?_ * _ * _
          · norm_num
          · linarith
      _ ≤ e * (θ * √θ) := by linarith
      _ ≤ θ * b * (2 * (2880 * l * n * sn * S)) := by
          have := mul_le_mul_of_nonneg_left hβ hθ.le
          linarith
  · refine le_of_mul_le_mul_right ?_ hc0
    calc D * u * (2 * (2880 * l * n * sn * S)) = 5760 * (n * sn * D) * 1 * l * S * u := by ring
      _ ≤ 2 ^ 26 * (n ^ 4 * (n + 1) * (8 + m) + n * sn * D) * (N + 1) * (l + 1) ^ 3 * S * u := by
          gcongr ?_ * ?_ * ?_ * ?_ * _ * _
          · norm_num
          · linarith
          · linarith
      _ ≤ e * (θ * √θ) := by linarith
      _ ≤ e * √θ := mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hsθ.le hθ₁) he
      _ ≤ b * (2 * (2880 * l * n * sn * S)) := by linarith

/-- **The bit count of Hermitian diagonalization** (Theorem 4.2, in bits): under the hypotheses
of `NLAlib.FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le` with the two
precision conditions replaced by $u > 0$, the accuracy within a factor $2$ of its bound,
$\beta_* /2 \le \beta \le \beta_*$ ($\beta_*$ the right side of that bound), and
$$\begin{aligned}\log_2\frac1u \ge{}& \log_2\frac1\varepsilon + \frac32\log_2\frac1\theta +
\log_2\Bigl(n^4(n + 1)(8 + \mu_{\mathrm{MM}}(n)) + n^{3/2}\bigl(4\mu_{\mathrm{QR}}(n) +
4\sqrt n(c_{\mathrm N} + 1) + 2\mu_{\mathrm{MM}}(n) + 1\bigr)\Bigr) \\
&+ \log_2(N_* + 1) + 3\log_2(\ell + 1) +
\log_2\bigl(2\sqrt n + \sqrt{2\log(16n/\theta)}\bigr) + 26 \,,\end{aligned}$$
the failure probability is at most $\theta$. Since $\ell = O(\log(1/\varepsilon))$ and
$N_* = O(\log(n\ell/\theta) + \log\log(n/(\varepsilon\theta)))$, this is
$\log_2(1/\varepsilon) + O(\log n + \log\log(1/\varepsilon)) + \tfrac32\log_2(1/\theta)$ bits.
[Shah2024, Theorem 4.2], there $\log_2(1/\varepsilon) + \log_2\max(n^{1.5}\mu_{\mathrm{QR}},
n^{1.5}\sqrt n c_{\mathrm N}, n^{4.5}\mu_{\mathrm{MM}}) + 2\log_2\log_2(1/\varepsilon) +
1.5\log_2(1/\theta) + \log_2\log_2(n\log_2(1/\varepsilon)/\theta) + 23$; the exponent of $n$ and
the third power of $\ell$ (from the corrected shift-avoidance probability) differ.
Proof: exponentiate (`Real.logb_le_logb`, `Real.rpow_logb`, `Real.logb_mul`, `Real.logb_rpow`)
to get both precision conditions of
`NLAlib.FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le` for $n \ge 1$ (at
$n = 0$ `hβle` reads $\beta \le 0$ (as $x/0 = 0$), contradicting `hβ`: `hβ.not_le hβle`) ($2 \cdot
640 \cdot 16 \cdot 2880 \le 2^{26}$, the factor $2$ from $\beta \ge \beta_*/2$, $\ell^2(\ell + 1)
\le (\ell + 1)^3$, $\log_2(N_* + 1) \ge 0$), and apply it. L, about 50 lines (seven-term
`Real.logb` exponentiation). -/
theorem FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_logb_le
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hunifm : ∀ c z, MeasurableSet (M.unif c ⁻¹' {z}))
    (hunifc : ∀ c, (Set.range (M.unif c)).Countable)
    (hnormalm : ∀ z, MeasurableSet (M.normal ⁻¹' {z})) (hnormalc : (Set.range M.normal).Countable)
    (hμM : Monotone μM) (hμQ : Monotone μQ) (hμM₀ : 0 ≤ μM 0) (hμQ₀ : 0 ≤ μQ 0) (hcN : 0 ≤ cN)
    {n : ℕ} {A : Matrix (Fin n) (Fin n) (F × F)} (hA : (decodeMatrix dec A).IsHermitian)
    {R₀ ε β : F} {θ : ℝ} (hR₀ : specNorm (decodeMatrix dec A) ≤ dec R₀) (hR₀pos : 0 < dec R₀)
    (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) {ℓ : ℕ}
    (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hβ : 0 < dec β)
    (hβle : dec β ≤ dec ε * √θ / (2880 * ℓ * n * √(n : ℝ) *
      (2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ)))))
    (hβge : dec ε * √θ / (2880 * ℓ * n * √(n : ℝ) *
      (2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ)))) / 2 ≤ dec β)
    {Nst : ℝ}
    (hN : Nst = newtonSchulzSteps (θ / (32 * n * (n + 1) * ℓ * (ℓ + 1))) (dec β / (16 * n)))
    (hu : 0 < u)
    (hbits : Real.logb 2 (dec ε)⁻¹ + 3 / 2 * Real.logb 2 θ⁻¹ +
      Real.logb 2 (n ^ 4 * (n + 1) * (8 + μM n) +
        n * √(n : ℝ) * (4 * μQ n + 4 * √(n : ℝ) * (cN + 1) + 2 * μM n + 1)) +
      Real.logb 2 (Nst + 1) + 3 * Real.logb 2 (ℓ + 1) +
      Real.logb 2 (2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ))) + 26 ≤ Real.logb 2 u⁻¹)
    {signFuel : ℕ}
    (hfuel : Nst ≤ signFuel) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (100 * n * √(n : ℝ)) ≤ min (√(θ / (8 * n))) (dec ε * min (dec R₀) 1))
    (hΩ : 16 * (2 * dec R₀ + n + 2 * ℓ + √(Real.log (16 * n / θ))) ≤ Ω) {Ω' : Type*}
    {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'} {ζ : List Bool → Ω' → EighSample ℝ ℂ n}
    (hind : iIndepFun ζ μ) (hlaw : ∀ a, HasLaw (ζ a) (eighSampleLaw n) μ) :
    μ.real {ω | ¬ IsApproxDiagonalization (decodeMatrix dec A)
      (decodeMatrix dec (eigh M signFuel ℓ A R₀ ε β fun a => ζ a ω).1)
      (fun i => dec ((eigh M signFuel ℓ A R₀ ε β fun a => ζ a ω).2 i)) (2 * dec ε * dec R₀)
      (dec ε / 3)} ≤ θ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, mul_zero, zero_mul, div_zero] at hβle
    exact absurd hβle hβ.not_ge
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ0
  · simp only [Nat.cast_zero, mul_zero, zero_mul, div_zero] at hβle
    exact absurd hβle hβ.not_ge
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ0
  have hsn : 1 ≤ √(n : ℝ) := Real.one_le_sqrt.mpr hn1
  have hμMn : 0 ≤ μM n := hμM₀.trans (hμM (Nat.zero_le n))
  have hμQn : 0 ≤ μQ n := hμQ₀.trans (hμQ (Nat.zero_le n))
  have hS2 : 2 ≤ 2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ)) := by
    have := Real.sqrt_nonneg (2 * Real.log (16 * n / θ)); linarith
  have hc1 : 1 ≤ 2880 * ℓ * n * √(n : ℝ) * (2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ))) := by
    have h4 : 1 ≤ (ℓ : ℝ) * n * √(n : ℝ) :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hl1 hn1) hsn
    nlinarith [mul_le_mul h4 hS2 (by norm_num) (by positivity)]
  have hb1 : dec β ≤ 1 := by
    refine hβle.trans ((div_le_one (by linarith)).mpr (le_trans ?_ hc1))
    exact mul_le_one₀ (hε₁.trans (by norm_num)) (Real.sqrt_nonneg θ) (Real.sqrt_le_one.mpr hθ₁)
  have hNst : 0 ≤ Nst := by
    rw [hN, newtonSchulzSteps]
    have h₁ : 0 ≤ Real.logb 2 (min |θ / (32 * n * (n + 1) * ℓ * (ℓ + 1))| (1 / 2))⁻¹ :=
      Real.logb_nonneg one_lt_two ((one_le_inv₀ (by positivity)).mpr
        ((min_le_right _ _).trans (by norm_num)))
    have h₂ : 1 ≤ Real.logb 2 (dec β / (16 * n))⁻¹ := by
      have h2 : (2 : ℝ) ≤ (dec β / (16 * n))⁻¹ := by
        rw [inv_div, le_div_iff₀ hβ]; linarith
      simpa only [Real.logb_self_eq_one one_lt_two] using
        Real.logb_le_logb_of_le one_lt_two two_pos h2
    linarith [Real.logb_nonneg one_lt_two h₂]
  have hβ' : dec ε * √θ ≤ 2 * (2880 * ℓ * n * √(n : ℝ) *
      (2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ)))) * dec β := by
    rw [div_div, div_le_iff₀ (by positivity)] at hβge; linarith
  obtain ⟨h₁, h₂⟩ := mul_le_mul_and_mul_le_of_mul_le_mul_sqrt hn1 hl1
    (Real.mul_self_sqrt (by positivity)) (Real.sqrt_nonneg _) hμMn (by positivity) (by linarith)
    hNst hε.le hθ hθ₁ hu.le
    (mul_le_mul_mul_sqrt_of_logb_le hε hθ (by positivity) (by linarith) (by positivity)
      (by linarith) hu hbits) hβ'
  exact hM.measureReal_not_isApproxDiagonalization_eigh_le hunifm hunifc hnormalm hnormalc hμM
    hμQ hμM₀ hμQ₀ hcN hA hR₀ hR₀pos hε hε₁ hθ hθ₁ hℓ hβ hβle hN h₁ h₂ hfuel hτ₀ hτ hΩ hind hlaw

private theorem le_zpow_of_logb_logb_add_two_le {L : ℝ} {E : ℕ} (hE : 2 ≤ E) (hL : 1 ≤ L)
    (h : Real.logb 2 (Real.logb 2 L + 2) + 1 ≤ E) : L ≤ (2 : ℝ) ^ ((2 : ℤ) ^ (E - 1) - 2) := by
  have h0 : 0 ≤ Real.logb 2 L := Real.logb_nonneg one_lt_two hL
  have h1 : Real.logb 2 L + 2 ≤ (2 : ℝ) ^ (E - 1) := by
    have : Real.logb 2 (Real.logb 2 L + 2) ≤ ((E - 1 : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ E)]; linarith
    rwa [Real.logb_le_iff_le_rpow one_lt_two (by linarith), Real.rpow_natCast] at this
  have h2 : Real.logb 2 L ≤ (((2 : ℤ) ^ (E - 1) - 2 : ℤ) : ℝ) := by push_cast; linarith
  rwa [Real.logb_le_iff_le_rpow one_lt_two (by linarith), Real.rpow_intCast] at h2

private theorem mul_le_min_and_le_of_mul_le {n ℓ e θ R τ Ω : ℝ} (hn : 0 ≤ n) (hℓ : 0 ≤ ℓ)
    (he : 0 < e) (he₁ : e ≤ 1) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) (hR : 1 / 2 ≤ R) (hR₁ : R ≤ 1)
    (hτ₀ : 0 ≤ τ) (hτ : τ * (1536 * (n + ℓ + 2) ^ 2) ≤ e * θ)
    (hΩ : 3072 * (n + ℓ + 2) ^ 2 ≤ Ω * (e * θ)) :
    τ * (100 * n * √n) ≤ min (√(θ / (8 * n))) (e * min R 1) ∧
      16 * (2 * R + n + 2 * ℓ + √(Real.log (16 * n / θ))) ≤ Ω := by
  have hm : 2 ≤ n + ℓ + 2 := by linarith
  have hm2 : 0 < 1536 * (n + ℓ + 2) ^ 2 := by positivity
  have hs : √n ^ 2 = n := Real.sq_sqrt hn
  have hsn : √n ≤ n + ℓ + 2 := by nlinarith [Real.sqrt_nonneg n]
  have hnsn : n * √n ≤ (n + ℓ + 2) ^ 2 := by
    rw [sq]; exact mul_le_mul (by linarith) hsn (Real.sqrt_nonneg n) (by linarith)
  have heθ : e * θ ≤ θ := mul_le_of_le_one_left hθ.le he₁
  have hX0 : 0 ≤ τ * (100 * n * √n) := by positivity
  have hX : τ * (100 * n * √n) * (1536 * (n + ℓ + 2) ^ 2) ≤ 100 * n * √n * (e * θ) := by
    have := mul_le_mul_of_nonneg_left hτ (by positivity : (0 : ℝ) ≤ 100 * n * √n)
    linarith
  refine ⟨le_min ?_ ?_, ?_⟩
  · rcases hn.eq_or_lt with rfl | hn0
    · simp
    rw [← Real.sqrt_sq hX0]
    refine Real.sqrt_le_sqrt ?_
    rw [le_div_iff₀ (by positivity)]
    refine le_of_mul_le_mul_right ?_ (pow_pos hm2 2)
    have h1 := pow_le_pow_left₀ (by positivity) hX 2
    have h2 : (100 * n * √n * (e * θ)) ^ 2 = 10000 * n ^ 3 * (e * θ) ^ 2 := by
      linear_combination (10000 * n ^ 2 * (e * θ) ^ 2) * hs
    have h3 : n ^ 4 ≤ (n + ℓ + 2) ^ 4 := pow_le_pow_left₀ hn (by linarith) 4
    have h4 : (e * θ) ^ 2 ≤ θ := by nlinarith [mul_pos he hθ]
    have h5 := mul_le_mul h3 h4 (by positivity) (by positivity)
    nlinarith
  · have h1 : 1 / 2 ≤ min R 1 := le_min hR (by norm_num)
    refine le_trans ?_ (mul_le_mul_of_nonneg_left h1 he.le)
    refine le_of_mul_le_mul_right ?_ hm2
    have := mul_le_mul_of_nonneg_left hnsn (by positivity : (0 : ℝ) ≤ 100 * (e * θ))
    have := mul_le_mul_of_nonneg_right (mul_le_of_le_one_right he.le hθ₁)
      (sq_nonneg (n + ℓ + 2))
    linarith [mul_nonneg he.le (sq_nonneg (n + ℓ + 2))]
  · have hy : 0 ≤ 16 * n / θ := by positivity
    have h1 : √(Real.log (16 * n / θ)) ≤ 16 * n / θ + 1 :=
      (Real.sqrt_le_sqrt (Real.log_le_self hy)).trans
        (by nlinarith [Real.sq_sqrt hy, Real.sqrt_nonneg (16 * n / θ)])
    have h2 : (16 * n / θ) * θ = 16 * n := div_mul_cancel₀ _ hθ.ne'
    refine le_of_mul_le_mul_right ?_ (mul_pos he hθ)
    calc 16 * (2 * R + n + 2 * ℓ + √(Real.log (16 * n / θ))) * (e * θ)
        ≤ 16 * (2 + n + 2 * ℓ + (16 * n / θ + 1)) * (e * θ) := by gcongr; linarith
      _ = 16 * (3 + n + 2 * ℓ) * (e * θ) + 256 * n * e := by linear_combination 16 * e * h2
      _ ≤ 16 * (3 + n + 2 * ℓ) + 256 * n := by
          have := mul_le_mul_of_nonneg_left (mul_le_one₀ he₁ hθ.le hθ₁)
            (by positivity : (0 : ℝ) ≤ 16 * (3 + n + 2 * ℓ))
          have := mul_le_mul_of_nonneg_left he₁ (by positivity : (0 : ℝ) ≤ 256 * n)
          linarith
      _ ≤ 3072 * (n + ℓ + 2) ^ 2 := by nlinarith
      _ ≤ Ω * (e * θ) := hΩ

/-- **Hermitian diagonalization in a bounded binary format: $\log_2\log_2(n/(\varepsilon\theta)) +
O(1)$ exponent bits suffice** (Theorem 4.2 for a finite exponent range): let the machine meet
`NLAlib.FloatMachine.IsAccurate` with $u = 2^{-p}$, floor $2^{e_{\min} + p - 1}$ (the smallest
normal number) and range the largest finite number of a binary format with $E \ge 2$ exponent
bits, precision $p$ and smallest exponent $e_{\min}$ (as
`NLAlib.exists_floatMachine_isAccurate_binaryFloatRound` provides), with the other hypotheses of
`NLAlib.FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_logb_le`, the
input scaled so that $1/2 \le R_0 \le 1$ (an exact power-of-two scaling), the precision condition
there with $\log_2(1/u) = p$, and
$$\log_2\Bigl(\log_2\frac{1536\,(n + \ell + 2)^2}{\varepsilon\theta} + 2\Bigr) + 1 \le E \,.$$
Then the failure probability is at most $\theta$. With $\ell = O(\log(1/\varepsilon))$ this is
$\log_2\log_2(n/(\varepsilon\theta)) + O(1)$ exponent bits, the claim of [Shah2024, Section 1.2]
("$\lg\lg(n/\varepsilon) + O(1)$ bits to store the exponent"), with the $\theta$ it omits.
Proof: for a binary format, $e_{\min} + p - 1 = 2 - 2^{E - 1}$ and the largest finite number is
at least $2^{2^{E-1} - 1}$ (`Float.Model.Format.minExponent_eq`, the bias $2^{E-1} - 1$,
`Float.Model.Format.maxFinite`); the exponent condition gives $2^{E-1} \ge \log_2 L + 2$ for the
displayed $L$, hence floor $\le 1/L \le \varepsilon\theta/(24n^2)$, which implies the floor
hypothesis $100n^{3/2}\tau \le \min(\sqrt{\theta/(8n)}, \varepsilon\min(R_0, 1))$, and range
$\ge 2L \ge 16(2R_0 + n + 2\ell + \sqrt{\log(16n/\theta)})$ (as $2L \ge 3072 \cdot 2^{15}(n +
\ell + 2)^2/\theta$); then apply
`NLAlib.FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_logb_le`. L,
about 70 lines (`Float.Model.Format` arithmetic). -/
theorem FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_exponentBits_le
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} (fmt : Float.Model.Format)
    (hE : 2 ≤ fmt.exponentBits) {cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec ((2 : ℝ)⁻¹ ^ fmt.mantissaBits)
      ((2 : ℝ) ^ (fmt.minExponent + fmt.mantissaBits - 1)) fmt.maxFinite μM μQ cN)
    (hunifm : ∀ c z, MeasurableSet (M.unif c ⁻¹' {z}))
    (hunifc : ∀ c, (Set.range (M.unif c)).Countable)
    (hnormalm : ∀ z, MeasurableSet (M.normal ⁻¹' {z})) (hnormalc : (Set.range M.normal).Countable)
    (hμM : Monotone μM) (hμQ : Monotone μQ) (hμM₀ : 0 ≤ μM 0) (hμQ₀ : 0 ≤ μQ 0) (hcN : 0 ≤ cN)
    {n : ℕ} {A : Matrix (Fin n) (Fin n) (F × F)} (hA : (decodeMatrix dec A).IsHermitian)
    {R₀ ε β : F} {θ : ℝ} (hR₀ : specNorm (decodeMatrix dec A) ≤ dec R₀)
    (hR₀half : 1 / 2 ≤ dec R₀) (hR₀one : dec R₀ ≤ 1) (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15)
    (hθ : 0 < θ) (hθ₁ : θ ≤ 1) {ℓ : ℕ} (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hβ : 0 < dec β)
    (hβle : dec β ≤ dec ε * √θ / (2880 * ℓ * n * √(n : ℝ) *
      (2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ)))))
    (hβge : dec ε * √θ / (2880 * ℓ * n * √(n : ℝ) *
      (2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ)))) / 2 ≤ dec β)
    {Nst : ℝ}
    (hN : Nst = newtonSchulzSteps (θ / (32 * n * (n + 1) * ℓ * (ℓ + 1))) (dec β / (16 * n)))
    (hbits : Real.logb 2 (dec ε)⁻¹ + 3 / 2 * Real.logb 2 θ⁻¹ +
      Real.logb 2 (n ^ 4 * (n + 1) * (8 + μM n) +
        n * √(n : ℝ) * (4 * μQ n + 4 * √(n : ℝ) * (cN + 1) + 2 * μM n + 1)) +
      Real.logb 2 (Nst + 1) + 3 * Real.logb 2 (ℓ + 1) +
      Real.logb 2 (2 * √(n : ℝ) + √(2 * Real.log (16 * n / θ))) + 26 ≤ fmt.mantissaBits)
    (hexp : Real.logb 2 (Real.logb 2 (1536 * (n + ℓ + 2) ^ 2 / (dec ε * θ)) + 2) + 1 ≤
      fmt.exponentBits)
    {signFuel : ℕ} (hfuel : Nst ≤ signFuel) {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    {μ : Measure Ω'} {ζ : List Bool → Ω' → EighSample ℝ ℂ n} (hind : iIndepFun ζ μ)
    (hlaw : ∀ a, HasLaw (ζ a) (eighSampleLaw n) μ) :
    μ.real {ω | ¬ IsApproxDiagonalization (decodeMatrix dec A)
      (decodeMatrix dec (eigh M signFuel ℓ A R₀ ε β fun a => ζ a ω).1)
      (fun i => dec ((eigh M signFuel ℓ A R₀ ε β fun a => ζ a ω).2 i)) (2 * dec ε * dec R₀)
      (dec ε / 3)} ≤ θ := by
  have hτeq : fmt.minExponent + (fmt.mantissaBits : ℤ) - 1 =
      -((2 : ℤ) ^ (fmt.exponentBits - 1) - 2) := by
    simp only [Float.Model.Format.minExponent]; ring
  have hB : fmt.maxExponentBound = (2 : ℤ) ^ (fmt.exponentBits - 1) - fmt.mantissaBits := by
    have h1 : 1 ≤ 2 ^ (fmt.exponentBits - 1) := Nat.one_le_two_pow
    have h2 : (2 : ℤ) ^ fmt.exponentBits = 2 * 2 ^ (fmt.exponentBits - 1) := by
      rw [← pow_succ']; congr 1; omega
    simp only [Float.Model.Format.maxExponentBound, Float.Model.Format.exponentBias,
      Float.Model.Format.mantissaBits]
    rw [Nat.cast_sub h1]
    push_cast
    rw [h2]
    ring
  have hp : 1 ≤ fmt.mantissaBits := by simp only [Float.Model.Format.mantissaBits]; omega
  have hmax : 2 * (2 : ℝ) ^ ((2 : ℤ) ^ (fmt.exponentBits - 1) - 2) ≤ fmt.maxFinite := by
    rw [Float.Model.Format.maxFinite, hB]
    have h2p : (2 : ℝ) ≤ 2 ^ fmt.mantissaBits := by
      simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hp
    have : 2 * (2 : ℝ) ^ ((2 : ℤ) ^ (fmt.exponentBits - 1) - 2) =
        (2 ^ fmt.mantissaBits / 2) * 2 ^ ((2 : ℤ) ^ (fmt.exponentBits - 1) - fmt.mantissaBits) := by
      rw [← zpow_natCast, div_eq_mul_inv, ← zpow_neg_one, ← zpow_add₀ two_ne_zero,
        ← zpow_add₀ two_ne_zero, mul_comm (2 : ℝ), ← zpow_add_one₀ two_ne_zero]
      congr 1; ring
    rw [this]
    gcongr
    linarith
  set m : ℝ := (n : ℝ) + ℓ + 2 with hm_def
  have hm : 2 ≤ m := by
    have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); have := (Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ)
    linarith
  have he₁ : dec ε ≤ 1 := hε₁.trans (by norm_num)
  have hL1 : 1 ≤ 1536 * m ^ 2 / (dec ε * θ) := by
    rw [le_div_iff₀ (by positivity), one_mul]
    nlinarith [mul_le_one₀ he₁ hθ.le hθ₁]
  have hL := le_zpow_of_logb_logb_add_two_le hE hL1 (by simpa only [m] using hexp)
  have hτ : (2 : ℝ) ^ (fmt.minExponent + (fmt.mantissaBits : ℤ) - 1) *
      (1536 * m ^ 2) ≤ dec ε * θ := by
    rw [hτeq, zpow_neg, ← div_eq_inv_mul, div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hL
    linarith
  have hΩ : 3072 * m ^ 2 ≤ fmt.maxFinite * (dec ε * θ) := by
    rw [div_le_iff₀ (by positivity)] at hL
    nlinarith [mul_le_mul_of_nonneg_right hmax (by positivity : 0 ≤ dec ε * θ)]
  obtain ⟨h₁, h₂⟩ := mul_le_min_and_le_of_mul_le (Nat.cast_nonneg n) (Nat.cast_nonneg ℓ) hε he₁
    hθ hθ₁ hR₀half hR₀one (by positivity) hτ hΩ
  refine hM.measureReal_not_isApproxDiagonalization_eigh_le_of_logb_le hunifm hunifc hnormalm
    hnormalc hμM hμQ hμM₀ hμQ₀ hcN hA hR₀ (by linarith) hε hε₁ hθ hθ₁ hℓ hβ hβle hβge hN
    (by positivity) ?_ hfuel (by positivity) h₁ h₂ hind hlaw
  rwa [inv_pow, inv_inv, Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one]

end NLAlib
