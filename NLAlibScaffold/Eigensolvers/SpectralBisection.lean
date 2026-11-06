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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

end NLAlib
