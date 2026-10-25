/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Dirac
public import Mathlib.MeasureTheory.Measure.WithDensity
public import NLAlib.Matrix.Basic.QuadForm
public import NLAlib.Matrix.Functions.HermitianCalculus
public import NLAlib.Matrix.Functions.Polynomial
public import NLAlib.Matrix.Spectral.Eigenvalues

/-!
# Spectral measures

The spectral measure $\mu_{\mathbf{A},\mathbf{b}}$ of a Hermitian matrix $\mathbf{A}$ and a
vector $\mathbf{b}$ is the finite measure on $\mathbb{R}$ with an atom at each distinct
eigenvalue $x$ of weight $\|\mathbf{P}_x\mathbf{b}\|^2$, $\mathbf{P}_x$ the orthogonal projector
onto the eigenspace of $x$. It is characterised by its integrals: for every
$f : \mathbb{R} \to \mathbb{R}$,
$$\int f\,d\mu_{\mathbf{A},\mathbf{b}} =
\operatorname{Re}\,\mathbf{b}^{\mathsf{H}}f(\mathbf{A})\mathbf{b}\,,$$
with no continuity or measurability of $f$ needed, since the measure is atomic. Its mass is
$\|\mathbf{b}\|^2$; a repeated eigenvalue is one atom carrying the whole eigenspace's weight. The
definition is basis-free; the form through any unitary eigenbasis is a bridge theorem.

The squared tangent of the angle between $\mathbf{b}$ and the eigenspace of $c$ is read off
the measure, $\mu_{\mathbf{A},\mathbf{b}}(\mathbb{R}\setminus\{c\}) /
\mu_{\mathbf{A},\mathbf{b}}(\{c\})$, with no eigenvector in sight. Every eigenvalue bound for a
filtered vector $g(\mathbf{A})\mathbf{b}$ (power method, inverse iteration, Kaniel–Paige–Saad)
is a bound on a ratio of two integrals against $\mu_{\mathbf{A},\mathbf{b}}$; the filter theorem
below is that bound.

The empirical spectral measure $\lvert n\rvert^{-1}\sum_{k<\lvert n\rvert}\delta_{\lambda_k}$,
eigenvalues counted with multiplicity, is a probability measure for nonempty $n$; it is the
average of the spectral measures of the coordinate vectors.

Junk values: both measures, and every statement about them that carries no Hermitian
hypothesis, are trivial off Hermitian matrices: the spectral measure is then $0$ (Mathlib's
`cfc` returns $0$) and the empirical one is $\delta_0$.

## Main definitions

* `NLAlib.spectralMeasure`: $\mu_{\mathbf{A},\mathbf{b}}$.
* `NLAlib.empiricalSpectralMeasure`: the empirical spectral measure.
* `NLAlib.spectralTangentSq`: the squared tangent of the angle between a vector and an
  eigenspace.

## Main results

* `NLAlib.integral_spectralMeasure`: the characterising integral identity.
* `NLAlib.ae_mem_Icc_spectralMeasure`: the support hypothesis of the Polynomial layer.
* `NLAlib.spectralMeasure_apply`, `NLAlib.spectralMeasure_real`: the measure of every set.
* `NLAlib.isStarProjection_cfc_indicator`: spectral projectors are orthogonal
  projectors.
* `NLAlib.HasOrthonormalCols.spectralMeasure_eq_sum`: the eigenbasis form.
* `NLAlib.spectralMeasure_cfc_mulVec`: filtering multiplies the measure by $g^2$.
* `Matrix.IsHermitian.rayleighQuotient_eq_integral_div`: the Rayleigh quotient as a ratio of
  integrals.
* `Matrix.IsHermitian.spectralTangentSq_le`: the bridge to an eigenvector overlap.
* `Matrix.IsHermitian.abs_sub_rayleighQuotient_cfc_mulVec_le`: the filter theorem.
* `Matrix.IsHermitian.integral_empiricalSpectralMeasure`: the normalised trace of
  $f(\mathbf{A})$.
* `Matrix.IsHermitian.empiricalSpectralMeasure_real`: the empirical measure of every set.
* `Matrix.IsHermitian.star_aeval_mulVec_dotProduct_aeval_mulVec`,
  `Matrix.IsHermitian.norm_aeval_mulVec_sq`: polynomial inner products.
* `NLAlib.spectralMeasure_diagonal`: the spectral measure of a diagonal matrix.
* `NLAlib.spectralMeasure_diagonal_sqrt_of_ae_mem`: every finite atomic measure is a spectral
  measure.
-/

@[expose] public section

open MeasureTheory Polynomial
open scoped Matrix MatrixOrder ComplexOrder ENNReal

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n r : Type*} [Fintype n] [DecidableEq n] [Fintype r]
  [DecidableEq r]

/-! ### Definitions -/

/-- The **spectral measure** $\mu_{\mathbf{A},\mathbf{b}}$ of a Hermitian $\mathbf{A}$ and a
vector $\mathbf{b}$: the finite measure on $\mathbb{R}$ with an atom at each distinct eigenvalue
$x$ of weight $\|\mathbf{P}_x\mathbf{b}\|^2$, $\mathbf{P}_x$ the orthogonal projector onto the
eigenspace of $x$. Its integral of every $f$ is
$\operatorname{Re}\,\mathbf{b}^{\mathsf{H}}f(\mathbf{A})\mathbf{b}$
(`integral_spectralMeasure`); its mass is $\|\mathbf{b}\|^2$. A repeated eigenvalue is one atom.
Junk value: $0$ when $\mathbf{A}$ is not Hermitian. The projector $\mathbf{P}_x$ is `cfc` of the
indicator of $\{x\}$; that is a legitimate functional calculus (not the junk value of
`cfc_apply_of_not_continuousOn`) because the spectrum is finite, so every function is continuous
on it. The definition needs `[DecidableEq n]` through Mathlib's `Matrix.finite_real_spectrum`
(`Mathlib/Analysis/Matrix/Spectrum.lean`). [GolubMeurant2010, Ch. 7]. -/
noncomputable def spectralMeasure (A : Matrix n n 𝕜) (b : n → 𝕜) : Measure ℝ :=
  ∑ x ∈ A.finite_real_spectrum.toFinset,
    ENNReal.ofReal (RCLike.re (quadForm (cfc (fun t : ℝ => if t = x then (1 : ℝ) else 0) A) b)) •
      Measure.dirac x

omit [DecidableEq n] in
/-- The **empirical spectral measure** $\lvert n\rvert^{-1}\sum_{k<\lvert n\rvert}
\delta_{\lambda_k(\mathbf{A})}$, eigenvalues counted with multiplicity. A probability measure for
nonempty $n$; $0$ for empty $n$; $\delta_0$ when $\mathbf{A}$ is not Hermitian (every
`eigenvalue A k` is then $0$). -/
noncomputable def empiricalSpectralMeasure (A : Matrix n n 𝕜) : Measure ℝ :=
  (Fintype.card n : ℝ≥0∞)⁻¹ •
    ∑ k ∈ Finset.range (Fintype.card n), Measure.dirac (eigenvalue A k)

/-- The squared tangent of the angle between $\mathbf{b}$ and the eigenspace of $c$, read off
the spectral measure: $\mu_{\mathbf{A},\mathbf{b}}(\mathbb{R}\setminus\{c\}) /
\mu_{\mathbf{A},\mathbf{b}}(\{c\})$. Junk value $0$ when $\mathbf{b}$ has no component in that
eigenspace (in particular when $c$ is not an eigenvalue). -/
noncomputable def spectralTangentSq (A : Matrix n n 𝕜) (b : n → 𝕜) (c : ℝ) : ℝ :=
  (spectralMeasure A b).real {c}ᶜ / (spectralMeasure A b).real {c}

/-! ### Integrals -/

/-- The weight of the atom at $x$ is nonnegative: it is the quadratic form of the positive
semidefinite $\mathbf{1}_{\{x\}}(\mathbf{A})$ ($0$ off Hermitian). -/
private theorem re_quadForm_cfc_ite_nonneg (A : Matrix n n 𝕜) (b : n → 𝕜) (x : ℝ) :
    0 ≤ RCLike.re (quadForm (cfc (fun t : ℝ => if t = x then (1 : ℝ) else 0) A) b) :=
  (Matrix.nonneg_iff_posSemidef.1
    (cfc_nonneg fun t _ => by split_ifs <;> norm_num)).re_quadForm_nonneg b

/-- The quadratic form of the spectral projector $\mathbf{1}_S(\mathbf{A})$ is nonnegative. -/
private theorem re_quadForm_cfc_indicator_nonneg (A : Matrix n n 𝕜) (b : n → 𝕜) (S : Set ℝ) :
    0 ≤ RCLike.re (quadForm (cfc (S.indicator fun _ => (1 : ℝ)) A) b) :=
  (Matrix.nonneg_iff_posSemidef.1 (cfc_nonneg fun t _ =>
    Set.indicator_nonneg (fun _ _ => zero_le_one) t)).re_quadForm_nonneg b

/-- The integral against a spectral measure as a sum over the spectrum. -/
private theorem integral_spectralMeasure_eq_sum (A : Matrix n n 𝕜) (b : n → 𝕜) (f : ℝ → ℝ) :
    ∫ x, f x ∂spectralMeasure A b = ∑ x ∈ A.finite_real_spectrum.toFinset,
      RCLike.re (quadForm (cfc (fun t : ℝ => if t = x then (1 : ℝ) else 0) A) b) * f x := by
  rw [spectralMeasure, integral_finsetSum_measure fun x _ =>
    (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal
    (re_quadForm_cfc_ite_nonneg A b x), smul_eq_mul]

/-- The measure of a set under a spectral measure as a sum over the spectrum. -/
private theorem spectralMeasure_apply_eq_sum (A : Matrix n n 𝕜) (b : n → 𝕜) (S : Set ℝ) :
    spectralMeasure A b S = ∑ x ∈ A.finite_real_spectrum.toFinset,
      ENNReal.ofReal (RCLike.re (quadForm (cfc (fun t : ℝ => if t = x then (1 : ℝ) else 0) A) b))
        * S.indicator 1 x := by
  rw [spectralMeasure, Measure.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]

/-- The spectral measure is finite: a finite sum of finite multiples of Dirac masses. -/
instance isFiniteMeasure_spectralMeasure (A : Matrix n n 𝕜) (b : n → 𝕜) :
    IsFiniteMeasure (spectralMeasure A b) := by
  unfold spectralMeasure
  have : ∀ x : ℝ, IsFiniteMeasure (ENNReal.ofReal (RCLike.re
      (quadForm (cfc (fun t : ℝ => if t = x then (1 : ℝ) else 0) A) b)) • Measure.dirac x) :=
    fun x => Measure.smul_finite _ ENNReal.ofReal_ne_top
  infer_instance

/-- Every real function is integrable against a spectral measure, which is a finite sum of
finite multiples of Dirac masses. -/
theorem integrable_spectralMeasure (A : Matrix n n 𝕜) (b : n → 𝕜) (f : ℝ → ℝ) :
    Integrable f (spectralMeasure A b) := by
  unfold spectralMeasure
  refine integrable_finsetSum_measure.2 fun x _ => ?_
  exact (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top

/-- **The spectral measure integrates the quadratic form**: for every square $\mathbf{A}$
(both sides vanish off Hermitian, so no hypothesis), every $\mathbf{b}$ and every
$f : \mathbb{R} \to \mathbb{R}$,
$\int f\,d\mu_{\mathbf{A},\mathbf{b}} = \operatorname{Re}\,\mathbf{b}^{\mathsf{H}}
f(\mathbf{A})\mathbf{b}$, with $f(\mathbf{A})$ Mathlib's `cfc f A`. No continuity or
measurability of $f$ is needed: the measure is atomic.
[GolubMeurant2010, Ch. 7]; there for real symmetric $\mathbf{A}$ as a Riemann–Stieltjes integral,
here over any `RCLike` field.
Result: spectral-measure -/
theorem integral_spectralMeasure (A : Matrix n n 𝕜) (b : n → 𝕜) (f : ℝ → ℝ) :
    ∫ x, f x ∂spectralMeasure A b = RCLike.re (quadForm (cfc f A) b) := by
  set F := A.finite_real_spectrum.toFinset
  set e : ℝ → ℝ → ℝ := fun x t => if t = x then (1 : ℝ) else 0
  have hcfc : cfc f A = ∑ x ∈ F, f x • cfc (e x) A := by
    have hsum : (fun t => ∑ x ∈ F, f x * e x t) = ∑ x ∈ F, fun t => f x * e x t := by
      ext t
      rw [Finset.sum_apply]
    have hc : ∀ g : ℝ → ℝ, ContinuousOn g (spectrum ℝ A) := fun g =>
      A.finite_real_spectrum.continuousOn g
    rw [cfc_congr (g := fun t => ∑ x ∈ F, f x * e x t), hsum, cfc_sum _ _ _ fun x _ => hc _]
    · exact Finset.sum_congr rfl fun x _ => cfc_const_mul _ _ _ (hc _)
    · intro t ht
      simp only [e, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq, if_pos ((Set.Finite.mem_toFinset _).2 ht)]
  rw [integral_spectralMeasure_eq_sum, hcfc, quadForm_def, Matrix.sum_mulVec, dotProduct_sum,
    map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, RCLike.smul_re, quadForm_def, mul_comm]

/-- The integral of a real polynomial against the spectral measure of a Hermitian
$\mathbf{A}$: $\int p\,d\mu_{\mathbf{A},\mathbf{b}} =
\operatorname{Re}\,\mathbf{b}^{\mathsf{H}}p(\mathbf{A})\mathbf{b}$, with $p(\mathbf{A})$ the
algebra evaluation `aeval A p`. -/
theorem _root_.Matrix.IsHermitian.integral_eval_spectralMeasure {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) (p : ℝ[X]) :
    ∫ x, p.eval x ∂spectralMeasure A b = RCLike.re (quadForm (aeval A p) b) := by
  rw [integral_spectralMeasure, hA.cfc_eq_aeval_of_forall_eval_eq fun _ _ => rfl]

/-- The moments of the spectral measure of a Hermitian $\mathbf{A}$:
$\int x^k\,d\mu_{\mathbf{A},\mathbf{b}} =
\operatorname{Re}\,\mathbf{b}^{\mathsf{H}}\mathbf{A}^k\mathbf{b}$. -/
theorem _root_.Matrix.IsHermitian.integral_pow_spectralMeasure {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) (k : ℕ) :
    ∫ x, x ^ k ∂spectralMeasure A b = RCLike.re (quadForm (A ^ k) b) := by
  have h := hA.integral_eval_spectralMeasure b (X ^ k)
  simpa only [eval_pow, eval_X, map_pow, aeval_X] using h

/-- The mass of the spectral measure of a Hermitian $\mathbf{A}$ is $\|\mathbf{b}\|^2$. -/
theorem _root_.Matrix.IsHermitian.spectralMeasure_real_univ {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) :
    (spectralMeasure A b).real Set.univ = ‖WithLp.toLp 2 b‖ ^ 2 := by
  have h := integral_spectralMeasure A b (fun _ => 1)
  have hA' : IsSelfAdjoint A := hA
  rw [integral_const, smul_eq_mul, mul_one, cfc_const_one ℝ A hA', quadForm_one,
    RCLike.ofReal_re] at h
  exact h

/-- The spectral measure of a set $S \subseteq \mathbb{R}$, for every square $\mathbf{A}$:
$\mu_{\mathbf{A},\mathbf{b}}(S) = \operatorname{Re}\,\mathbf{b}^{\mathsf{H}}
\mathbf{1}_S(\mathbf{A})\mathbf{b}$, with $\mathbf{1}_S$ the indicator of $S$; every set is
measurable for an atomic measure, and $\mathbf{1}_S(\mathbf{A})$ is the orthogonal projector onto
the sum of the eigenspaces of the eigenvalues in $S$. -/
theorem spectralMeasure_apply (A : Matrix n n 𝕜) (b : n → 𝕜) (S : Set ℝ) :
    spectralMeasure A b S =
      ENNReal.ofReal (RCLike.re (quadForm (cfc (S.indicator fun _ => (1 : ℝ)) A) b)) := by
  rw [← integral_spectralMeasure, integral_spectralMeasure_eq_sum, spectralMeasure_apply_eq_sum,
    ENNReal.ofReal_sum_of_nonneg fun x _ => mul_nonneg (re_quadForm_cfc_ite_nonneg A b x)
      (Set.indicator_nonneg (fun _ _ => zero_le_one) x)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [ENNReal.ofReal_mul (re_quadForm_cfc_ite_nonneg A b x)]
  by_cases hx : x ∈ S <;> simp [hx]

/-- The spectral measure lives on the spectrum: for every square $\mathbf{A}$,
$\mu_{\mathbf{A},\mathbf{b}}(\mathbb{R} \setminus \operatorname{spec}\mathbf{A}) = 0$. -/
theorem spectralMeasure_compl_spectrum_eq_zero (A : Matrix n n 𝕜) (b : n → 𝕜) :
    spectralMeasure A b (spectrum ℝ A)ᶜ = 0 := by
  rw [spectralMeasure, Measure.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Measure.smul_apply, Measure.dirac_apply' _ A.finite_real_spectrum.measurableSet.compl,
    Set.indicator_of_notMem (Set.notMem_compl_iff.2 ((Set.Finite.mem_toFinset _).1 hx)),
    smul_zero]

/-- The support hypothesis of the Polynomial layer for a spectral measure: if the spectrum of a
square $\mathbf{A}$ lies in $[a, a']$, then $\mu_{\mathbf{A},\mathbf{b}}$-almost every $x$
lies in $[a, a']$ (off Hermitian the measure is $0$, so no hypothesis). -/
theorem ae_mem_Icc_spectralMeasure (A : Matrix n n 𝕜) {a a' : ℝ}
    (hs : spectrum ℝ A ⊆ Set.Icc a a') (b : n → 𝕜) :
    ∀ᵐ x ∂spectralMeasure A b, x ∈ Set.Icc a a' := by
  rw [ae_iff]
  exact measure_mono_null (fun x hx => fun hxs => hx (hs hxs))
    (spectralMeasure_compl_spectrum_eq_zero A b)

/-- A point carrying positive spectral weight is in the spectrum: for every square
$\mathbf{A}$, every $\mathbf{b}$ and every $c \in \mathbb{R}$ with
$0 < \mu_{\mathbf{A},\mathbf{b}}(\{c\})$, $c \in \operatorname{spec}\mathbf{A}$. -/
theorem mem_spectrum_of_spectralMeasure_real_pos {A : Matrix n n 𝕜} {b : n → 𝕜} {c : ℝ}
    (hb : 0 < (spectralMeasure A b).real {c}) : c ∈ spectrum ℝ A := by
  by_contra h
  have h0 : spectralMeasure A b {c} = 0 := measure_mono_null (Set.singleton_subset_iff.2 h)
    (spectralMeasure_compl_spectrum_eq_zero A b)
  rw [measureReal_def, h0, ENNReal.toReal_zero] at hb
  exact lt_irrefl _ hb

/-- An atom is dominated by the integral of a nonnegative function: for every square
$\mathbf{A}$, every $\mathbf{b}$, every $c \in \mathbb{R}$ and every
$f : \mathbb{R} \to \mathbb{R}$ with $f \ge 0$ $\mu_{\mathbf{A},\mathbf{b}}$-almost everywhere,
$$f(c)\,\mu_{\mathbf{A},\mathbf{b}}(\{c\}) \le \int f\,d\mu_{\mathbf{A},\mathbf{b}}\,.$$ -/
theorem mul_spectralMeasure_real_le_integral (A : Matrix n n 𝕜) (b : n → 𝕜) {f : ℝ → ℝ}
    (hf : 0 ≤ᵐ[spectralMeasure A b] f) (c : ℝ) :
    f c * (spectralMeasure A b).real {c} ≤ ∫ x, f x ∂spectralMeasure A b := by
  rw [mul_comm, ← smul_eq_mul, ← integral_indicator_const _ (measurableSet_singleton c)]
  refine integral_mono_ae (integrable_spectralMeasure A b _) (integrable_spectralMeasure A b _) ?_
  filter_upwards [hf] with x hx
  by_cases hxc : x = c
  · simp [hxc]
  · simpa [hxc] using hx

/-- The filtered mass dominates the weight of an atom: for every square $\mathbf{A}$, every
$\mathbf{b}$, every $g : \mathbb{R} \to \mathbb{R}$ and every $c \in \mathbb{R}$,
$$g(c)^2\mu_{\mathbf{A},\mathbf{b}}(\{c\}) \le \int g^2\,d\mu_{\mathbf{A},\mathbf{b}}\,.$$ -/
theorem mul_spectralMeasure_real_le_integral_sq (A : Matrix n n 𝕜) (b : n → 𝕜) (g : ℝ → ℝ)
    (c : ℝ) : g c ^ 2 * (spectralMeasure A b).real {c} ≤ ∫ x, g x ^ 2 ∂spectralMeasure A b :=
  mul_spectralMeasure_real_le_integral A b (f := fun x => g x ^ 2)
    (Filter.Eventually.of_forall fun x => sq_nonneg (g x)) c

/-- The spectral measure of every set as a real number: for every square $\mathbf{A}$, every
$\mathbf{b}$ and every $S \subseteq \mathbb{R}$,
$\mu_{\mathbf{A},\mathbf{b}}(S) =
\operatorname{Re}\,\mathbf{b}^{\mathsf{H}}\mathbf{1}_S(\mathbf{A})\mathbf{b}$, the quadratic form of
the spectral projector $\mathbf{1}_S(\mathbf{A})$; no measurability of $S$ is needed. -/
theorem spectralMeasure_real (A : Matrix n n 𝕜) (b : n → 𝕜) (S : Set ℝ) :
    (spectralMeasure A b).real S =
      RCLike.re (quadForm (cfc (S.indicator fun _ => (1 : ℝ)) A) b) := by
  rw [measureReal_def, spectralMeasure_apply, ENNReal.toReal_ofReal
    (re_quadForm_cfc_indicator_nonneg A b S)]

/-- The spectral projector is an orthogonal projector: for every square $\mathbf{A}$ and every
$S \subseteq \mathbb{R}$, $\mathbf{1}_S(\mathbf{A})$ is self-adjoint and idempotent (off
Hermitian it is $\mathbf{0}$, Mathlib's junk value of `cfc`). -/
theorem isStarProjection_cfc_indicator (A : Matrix n n 𝕜) (S : Set ℝ) :
    IsStarProjection (cfc (S.indicator fun _ => (1 : ℝ)) A) := by
  have hc : ContinuousOn (S.indicator fun _ => (1 : ℝ)) (spectrum ℝ A) :=
    A.finite_real_spectrum.continuousOn _
  refine ⟨?_, cfc_predicate _ A⟩
  rw [IsIdempotentElem, ← cfc_mul _ _ A hc hc]
  congr 1
  funext x
  by_cases hx : x ∈ S <;> simp [hx]

/-- Off Hermitian the spectral measure is $0$. -/
private theorem spectralMeasure_of_not_isHermitian {A : Matrix n n 𝕜} (hA : ¬ A.IsHermitian)
    (b : n → 𝕜) : spectralMeasure A b = 0 := by
  have hA' : ¬ IsSelfAdjoint A := hA
  ext S hS
  rw [spectralMeasure_apply, cfc_apply_of_not_predicate A hA', quadForm_zero_left, map_zero,
    ENNReal.ofReal_zero, Measure.coe_zero, Pi.zero_apply]

/-- **The spectral measure in an eigenbasis**: if
$\mathbf{A} = \mathbf{U}\operatorname{diag}(\mathbf{d})\mathbf{U}^{\mathsf{H}}$ with
$\mathbf{U}$ having orthonormal columns, as many as rows, and $\mathbf{d}$ real, then
$$\mu_{\mathbf{A},\mathbf{b}} = \sum_i \lvert(\mathbf{U}^{\mathsf{H}}\mathbf{b})_i\rvert^2\,
\delta_{\mathbf{d}_i}\,;$$
a repeated eigenvalue gives atoms at the same point, which add up.
[GolubMeurant2010, Ch. 7]; there with the eigenbasis of a real symmetric matrix. -/
theorem HasOrthonormalCols.spectralMeasure_eq_sum {U : Matrix n r 𝕜} (hU : HasOrthonormalCols U)
    (hr : Fintype.card r = Fintype.card n) {A : Matrix n n 𝕜} {d : r → ℝ}
    (hA : A = U * Matrix.diagonal (fun i => ((d i : ℝ) : 𝕜)) * Uᴴ) (b : n → 𝕜) :
    spectralMeasure A b =
      ∑ i, ENNReal.ofReal (‖(Uᴴ *ᵥ b) i‖ ^ 2) • Measure.dirac (d i) := by
  ext S hS
  have hind : ∀ x, 0 ≤ S.indicator (fun _ => (1 : ℝ)) x :=
    Set.indicator_nonneg fun _ _ => zero_le_one
  rw [spectralMeasure_apply, HasOrthonormalCols.re_quadForm_cfc_eq_sum hU hr hA,
    Measure.coe_finsetSum, Finset.sum_apply,
    ENNReal.ofReal_sum_of_nonneg fun i _ => mul_nonneg (hind _) (sq_nonneg _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul, ENNReal.ofReal_mul (hind _),
    mul_comm]
  by_cases hx : d i ∈ S <;> simp [hx]

/-- Isometric invariance: for $\mathbf{U}$ with orthonormal columns and every square
$\mathbf{T}$ on its column index,
$\mu_{\mathbf{U}\mathbf{T}\mathbf{U}^{\mathsf{H}},\,\mathbf{U}\mathbf{c}} =
\mu_{\mathbf{T},\mathbf{c}}$. The padding eigenvalue $0$ of
$\mathbf{U}\mathbf{T}\mathbf{U}^{\mathsf{H}}$ carries no weight from $\mathbf{U}\mathbf{c}$; for
a square $\mathbf{U}$ this is unitary invariance. For a non-Hermitian $\mathbf{T}$ both sides are
$0$, since $\mathbf{U}\mathbf{T}\mathbf{U}^{\mathsf{H}}$ is Hermitian exactly when $\mathbf{T}$
is. -/
theorem HasOrthonormalCols.spectralMeasure_mul_mul_conjTranspose {U : Matrix n r 𝕜}
    (hU : HasOrthonormalCols U) (T : Matrix r r 𝕜) (c : r → 𝕜) :
    spectralMeasure (U * T * Uᴴ) (U *ᵥ c) = spectralMeasure T c := by
  by_cases hT : T.IsHermitian
  · ext S hS
    rw [spectralMeasure_apply, spectralMeasure_apply, hU.cfc_mul_mul_conjTranspose hT,
      ← quadForm_conjTranspose_mul_mul]
    congr 3
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
      ← Matrix.mul_assoc, hU.conjTranspose_mul_self, Matrix.one_mul, sub_self, smul_zero, add_zero]
    rw [Matrix.mul_assoc, hU.conjTranspose_mul_self, Matrix.mul_one]
  · have hT' : ¬ (U * T * Uᴴ).IsHermitian := fun h => hT (by
      have h' := Matrix.isHermitian_conjTranspose_mul_mul U h
      rwa [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU.conjTranspose_mul_self, Matrix.one_mul,
        Matrix.mul_assoc, hU.conjTranspose_mul_self, Matrix.mul_one] at h')
    rw [spectralMeasure_of_not_isHermitian hT, spectralMeasure_of_not_isHermitian hT']

/-- The spectral measure is quadratic in the vector: for every square $\mathbf{A}$ and scalar
$c$, $\mu_{\mathbf{A},c\mathbf{b}} = \lvert c\rvert^2\mu_{\mathbf{A},\mathbf{b}}$. -/
theorem spectralMeasure_smul (A : Matrix n n 𝕜) (c : 𝕜) (b : n → 𝕜) :
    spectralMeasure A (c • b) = ENNReal.ofReal (‖c‖ ^ 2) • spectralMeasure A b := by
  ext S hS
  rw [spectralMeasure_apply, Measure.smul_apply, spectralMeasure_apply, quadForm_smul_right,
    RCLike.star_def, RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.re_ofReal_mul,
    ENNReal.ofReal_mul (sq_nonneg _), smul_eq_mul]

/-- Filtering multiplies the measure by $g^2$: for every square $\mathbf{A}$ and every
$g : \mathbb{R} \to \mathbb{R}$, $\mu_{\mathbf{A},\,g(\mathbf{A})\mathbf{b}}$ has density $g^2$
with respect to $\mu_{\mathbf{A},\mathbf{b}}$. -/
theorem spectralMeasure_cfc_mulVec (A : Matrix n n 𝕜) (g : ℝ → ℝ) (b : n → 𝕜) :
    spectralMeasure A (cfc g A *ᵥ b) =
      (spectralMeasure A b).withDensity (fun x => ENNReal.ofReal (g x ^ 2)) := by
  ext S hS
  have hind : S.indicator (fun x => ENNReal.ofReal (g x ^ 2)) =
      fun x => ENNReal.ofReal (S.indicator (fun x => g x ^ 2) x) := by
    ext x
    by_cases hx : x ∈ S <;> simp [hx]
  rw [withDensity_apply _ hS, spectralMeasure_apply, ← lintegral_indicator hS, hind,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_spectralMeasure A b _)
      (Filter.Eventually.of_forall fun x => Set.indicator_nonneg (fun _ _ => sq_nonneg _) x),
    integral_spectralMeasure]
  congr 2
  by_cases hA : A.IsHermitian
  · have hc : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ A) := fun f =>
      A.finite_real_spectrum.continuousOn f
    have hH : (cfc g A).IsHermitian := cfc_predicate g A
    rw [← quadForm_conjTranspose_mul_mul, hH.eq, ← cfc_mul _ _ A (hc _) (hc _),
      ← cfc_mul _ _ A (hc _) (hc _)]
    congr 1
    refine cfc_congr fun x _ => ?_
    by_cases hx : x ∈ S <;> simp [hx, sq]
  · have hA' : ¬ IsSelfAdjoint A := hA
    simp only [cfc_apply_of_not_predicate A hA', Matrix.zero_mulVec, quadForm_zero_right,
      quadForm_zero_left]

/-- The Rayleigh quotient as a ratio of spectral integrals: for Hermitian $\mathbf{A}$,
$$\frac{\operatorname{Re}\,\mathbf{b}^{\mathsf{H}}\mathbf{A}\mathbf{b}}{\|\mathbf{b}\|^2} =
\frac{\int x\,d\mu_{\mathbf{A},\mathbf{b}}}{\mu_{\mathbf{A},\mathbf{b}}(\mathbb{R})}\,,$$
both sides $0$ at $\mathbf{b} = \mathbf{0}$. -/
theorem _root_.Matrix.IsHermitian.rayleighQuotient_eq_integral_div {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) :
    rayleighQuotient A b =
      (∫ x, x ∂spectralMeasure A b) / (spectralMeasure A b).real Set.univ := by
  have h := hA.integral_pow_spectralMeasure b 1
  simp only [pow_one] at h
  rw [rayleighQuotient, h, hA.spectralMeasure_real_univ]

/-- The weight of an eigenvalue dominates every eigenvector overlap: for Hermitian
$\mathbf{A}$ and a unit vector $\mathbf{u}$ with $\mathbf{A}\mathbf{u} = c\mathbf{u}$,
$\lvert\mathbf{u}^{\mathsf{H}}\mathbf{b}\rvert^2 \le \mu_{\mathbf{A},\mathbf{b}}(\{c\})$, with
equality when the eigenvalue $c$ is simple. -/
theorem _root_.Matrix.IsHermitian.norm_star_dotProduct_sq_le_spectralMeasure_real
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {u : n → 𝕜} {c : ℝ}
    (hu : A *ᵥ u = (c : 𝕜) • u) (hu1 : ‖WithLp.toLp 2 u‖ = 1) (b : n → 𝕜) :
    ‖star u ⬝ᵥ b‖ ^ 2 ≤ (spectralMeasure A b).real {c} := by
  set ψ : ℝ → ℝ := ({c} : Set ℝ).indicator fun _ => (1 : ℝ)
  have hH : (cfc ψ A).IsHermitian := cfc_predicate ψ A
  have hPu : cfc ψ A *ᵥ u = u := by
    have hu' : A *ᵥ u = c • u := hu.trans (RCLike.real_smul_eq_coe_smul (K := 𝕜) c u).symm
    rw [hA.cfc_mulVec_of_mulVec_eq_smul ψ hu']
    simp [ψ]
  have hψ : (fun t => ψ t ^ 2) = ψ := by
    ext t
    by_cases ht : t = c <;> simp [ψ, ht]
  have hub : star u ⬝ᵥ b = star u ⬝ᵥ (cfc ψ A *ᵥ b) := by
    conv_lhs => rw [← hPu]
    rw [star_mulVec_dotProduct, hH.eq]
  have hnorm := hA.norm_toLp_cfc_mulVec_sq ψ b
  rw [hψ, ← spectralMeasure_real] at hnorm
  rw [← hnorm, hub]
  have hin : star u ⬝ᵥ (cfc ψ A *ᵥ b) =
      inner 𝕜 (WithLp.toLp 2 u) (WithLp.toLp 2 (cfc ψ A *ᵥ b)) := by
    rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
  rw [hin]
  refine (pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2).trans_eq ?_
  rw [hu1, one_mul]

/-! ### The angle between a vector and an eigenspace -/

/-- The squared tangent is nonnegative. -/
theorem spectralTangentSq_nonneg (A : Matrix n n 𝕜) (b : n → 𝕜) (c : ℝ) :
    0 ≤ spectralTangentSq A b c :=
  div_nonneg measureReal_nonneg measureReal_nonneg

/-- The squared secant: for Hermitian $\mathbf{A}$ and $\mathbf{b}$ with a nonzero component in
the eigenspace $E_c$ of $c$,
$$1 + \tan^2\angle(\mathbf{b}, E_c) =
\frac{\|\mathbf{b}\|^2}{\mu_{\mathbf{A},\mathbf{b}}(\{c\})}\,,$$
$\tan^2\angle(\mathbf{b}, E_c)$ the ratio
$\mu_{\mathbf{A},\mathbf{b}}(\mathbb{R}\setminus\{c\})/\mu_{\mathbf{A},\mathbf{b}}(\{c\})$. -/
theorem _root_.Matrix.IsHermitian.one_add_spectralTangentSq {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {b : n → 𝕜} {c : ℝ} (hb : 0 < (spectralMeasure A b).real {c}) :
    1 + spectralTangentSq A b c = ‖WithLp.toLp 2 b‖ ^ 2 / (spectralMeasure A b).real {c} := by
  rw [spectralTangentSq, ← hA.spectralMeasure_real_univ,
    ← measureReal_add_measureReal_compl (s := {c}) (measurableSet_singleton c)]
  field_simp

/-- The tangent against an eigenvector: for Hermitian $\mathbf{A}$, a unit vector
$\mathbf{u}$ with $\mathbf{A}\mathbf{u} = c\mathbf{u}$ and $\mathbf{b}$ with
$\mathbf{u}^{\mathsf{H}}\mathbf{b} \ne 0$,
$$\tan^2\angle(\mathbf{b}, E_c) \le
\frac{\|\mathbf{b}\|^2 - \lvert\mathbf{u}^{\mathsf{H}}\mathbf{b}\rvert^2}
{\lvert\mathbf{u}^{\mathsf{H}}\mathbf{b}\rvert^2}\,,$$
$\tan^2\angle(\mathbf{b}, E_c)$ the ratio
$\mu_{\mathbf{A},\mathbf{b}}(\mathbb{R}\setminus\{c\})/\mu_{\mathbf{A},\mathbf{b}}(\{c\})$ for
the eigenspace $E_c$ of $c$; equality holds when $c$ is a simple eigenvalue. The right side is
the eigenvector form of the overlap that sources use. -/
theorem _root_.Matrix.IsHermitian.spectralTangentSq_le {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {u : n → 𝕜} {c : ℝ} (hu : A *ᵥ u = (c : 𝕜) • u) (hu1 : ‖WithLp.toLp 2 u‖ = 1)
    {b : n → 𝕜} (hub : star u ⬝ᵥ b ≠ 0) :
    spectralTangentSq A b c ≤
      (‖WithLp.toLp 2 b‖ ^ 2 - ‖star u ⬝ᵥ b‖ ^ 2) / ‖star u ⬝ᵥ b‖ ^ 2 := by
  have ht : 0 < ‖star u ⬝ᵥ b‖ ^ 2 := by positivity
  have hm := hA.norm_star_dotProduct_sq_le_spectralMeasure_real hu hu1 b
  have hm0 : 0 < (spectralMeasure A b).real {c} := ht.trans_le hm
  rw [spectralTangentSq, measureReal_compl (measurableSet_singleton c),
    hA.spectralMeasure_real_univ, sub_div, sub_div, div_self hm0.ne', div_self ht.ne']
  gcongr

/-! ### The filter theorem -/

/-- The Rayleigh quotient of a filtered vector as a ratio of spectral integrals: for Hermitian
$\mathbf{A}$ and every $g : \mathbb{R} \to \mathbb{R}$,
$$\rho_{\mathbf{A}}(g(\mathbf{A})\mathbf{b}) =
\frac{\int x g(x)^2\,d\mu_{\mathbf{A},\mathbf{b}}}{\int g^2\,d\mu_{\mathbf{A},\mathbf{b}}}\,,$$
$\rho_{\mathbf{A}}$ the Rayleigh quotient; both sides are $0$ when
$g(\mathbf{A})\mathbf{b} = \mathbf{0}$. -/
theorem _root_.Matrix.IsHermitian.rayleighQuotient_cfc_mulVec_eq_integral_div {A : Matrix n n 𝕜}
    (hA : A.IsHermitian)
    (g : ℝ → ℝ) (b : n → 𝕜) :
    rayleighQuotient A (cfc g A *ᵥ b) =
      (∫ x, x * g x ^ 2 ∂spectralMeasure A b) / ∫ x, g x ^ 2 ∂spectralMeasure A b := by
  have hc : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ A) := fun f =>
    A.finite_real_spectrum.continuousOn f
  have hH : (cfc g A).IsHermitian := cfc_predicate g A
  have hA' : IsSelfAdjoint A := hA
  have hnum : RCLike.re (quadForm A (cfc g A *ᵥ b)) = ∫ x, x * g x ^ 2 ∂spectralMeasure A b := by
    rw [integral_spectralMeasure, ← quadForm_conjTranspose_mul_mul, hH.eq,
      show cfc g A * A * cfc g A = cfc g A * cfc (fun x => x) A * cfc g A by rw [cfc_id' ℝ A]]
    rw [← cfc_mul _ _ A (hc _) (hc _), ← cfc_mul _ _ A (hc _) (hc _)]
    congr 3
    ext x
    ring
  rw [rayleighQuotient, hnum, hA.norm_toLp_cfc_mulVec_sq, ← integral_spectralMeasure]

/-- **Rayleigh quotient of a filtered vector**: let $\mathbf{A}$ be Hermitian with spectrum in
$s \cup \{c\}$, $\lvert x - c\rvert \le D$ and $\lvert g(x)\rvert \le \delta\lvert g(c)\rvert$ for
$x \in s$, $g(c) \ne 0$, and $\mathbf{b}$ with a nonzero component in the eigenspace $E_c$ of
$c$. Then
$$\bigl\lvert c - \rho_{\mathbf{A}}(g(\mathbf{A})\mathbf{b})\bigr\rvert \le
D\,\delta^2\tan^2\angle(\mathbf{b}, E_c)\,,$$
$\rho_{\mathbf{A}}$ the Rayleigh quotient and $\tan^2\angle(\mathbf{b}, E_c)$ the ratio
$\mu_{\mathbf{A},\mathbf{b}}(\mathbb{R}\setminus\{c\})/\mu_{\mathbf{A},\mathbf{b}}(\{c\})$.
[TrefethenBau1997, Theorem 27.1] (proof); [Saad2011, §6.6.1] (proof): both for a polynomial or
power filter and an eigenvector of a simple eigenvalue; here any filter and any multiplicity. -/
theorem _root_.Matrix.IsHermitian.abs_sub_rayleighQuotient_cfc_mulVec_le {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {s : Set ℝ} {c D δ : ℝ} (hs : spectrum ℝ A ⊆ s ∪ {c})
    (hD : ∀ x ∈ s, |x - c| ≤ D) {g : ℝ → ℝ} (hgc : g c ≠ 0)
    (hg : ∀ x ∈ s, |g x| ≤ δ * |g c|) (b : n → 𝕜) (hb : 0 < (spectralMeasure A b).real {c}) :
    |c - rayleighQuotient A (cfc g A *ᵥ b)| ≤ D * δ ^ 2 * spectralTangentSq A b c := by
  set μ := spectralMeasure A b with hμ
  have hi : ∀ f : ℝ → ℝ, Integrable f μ := integrable_spectralMeasure A b
  have hae : ∀ᵐ x ∂μ, x ∈ spectrum ℝ A := ae_iff.2 (spectralMeasure_compl_spectrum_eq_zero A b)
  set K := D * δ ^ 2 * g c ^ 2
  -- the numerator: $\lvert\int (c - x) g^2\,d\mu\rvert \le K\mu(\mathbb{R}\setminus\{c\})$
  have hnum : |∫ x, (c - x) * g x ^ 2 ∂μ| ≤ K * μ.real {c}ᶜ := by
    rw [mul_comm, ← smul_eq_mul, ← integral_indicator_const _ (measurableSet_singleton c).compl]
    refine (abs_integral_le_integral_abs).trans (integral_mono_ae (hi _) (hi _) ?_)
    filter_upwards [hae] with x hx
    by_cases hxc : x = c
    · simp [hxc]
    · have hxs : x ∈ s := (hs hx).resolve_right hxc
      rw [Set.indicator_of_mem (Set.mem_compl_singleton_iff.2 hxc), abs_mul, abs_sub_comm,
        abs_of_nonneg (sq_nonneg (g x))]
      have hg2 : g x ^ 2 ≤ δ ^ 2 * g c ^ 2 := by
        rw [← sq_abs (g x), ← sq_abs (g c), ← mul_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hg x hxs) 2
      calc |x - c| * g x ^ 2 ≤ D * (δ ^ 2 * g c ^ 2) :=
            mul_le_mul (hD x hxs) hg2 (sq_nonneg _) ((abs_nonneg _).trans (hD x hxs))
        _ = K := by ring
  -- the denominator: $\int g^2\,d\mu \ge g(c)^2\mu(\{c\})$
  have hden : g c ^ 2 * μ.real {c} ≤ ∫ x, g x ^ 2 ∂μ :=
    mul_spectralMeasure_real_le_integral_sq A b g c
  have hpos : 0 < g c ^ 2 * μ.real {c} := mul_pos (by positivity) hb
  have hsub : c - rayleighQuotient A (cfc g A *ᵥ b) =
      (∫ x, (c - x) * g x ^ 2 ∂μ) / ∫ x, g x ^ 2 ∂μ := by
    have hI : ∫ x, (c - x) * g x ^ 2 ∂μ = c * ∫ x, g x ^ 2 ∂μ - ∫ x, x * g x ^ 2 ∂μ := by
      simp only [sub_mul]
      rw [integral_sub (hi _) (hi _), integral_const_mul]
    have h0 := (hpos.trans_le hden).ne'
    rw [hA.rayleighQuotient_cfc_mulVec_eq_integral_div, ← hμ, hI]
    field_simp
  rw [hsub, abs_div, abs_of_pos (hpos.trans_le hden)]
  calc |∫ x, (c - x) * g x ^ 2 ∂μ| / ∫ x, g x ^ 2 ∂μ ≤ K * μ.real {c}ᶜ / (g c ^ 2 * μ.real {c}) :=
        div_le_div₀ ((abs_nonneg _).trans hnum) hnum hpos hden
    _ = D * δ ^ 2 * spectralTangentSq A b c := by
        have := hb.ne'
        rw [spectralTangentSq, ← hμ]
        simp only [K]
        field_simp

/-! ### The empirical spectral measure -/

omit [DecidableEq n] in
/-- The empirical spectral measure of a matrix of nonempty size is a probability measure. -/
instance isProbabilityMeasure_empiricalSpectralMeasure [Nonempty n] (A : Matrix n n 𝕜) :
    IsProbabilityMeasure (empiricalSpectralMeasure A) := by
  constructor
  rw [empiricalSpectralMeasure, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply]
  simp only [measure_univ, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)

omit [DecidableEq n] in
/-- The empirical spectral measure of every square matrix is a finite measure (the zero measure
for the empty matrix). -/
instance isFiniteMeasure_empiricalSpectralMeasure (A : Matrix n n 𝕜) :
    IsFiniteMeasure (empiricalSpectralMeasure A) := by
  rcases isEmpty_or_nonempty n with hn | hn
  · unfold empiricalSpectralMeasure
    simp only [Fintype.card_eq_zero, Finset.range_zero, Finset.sum_empty, smul_zero]
    infer_instance
  · infer_instance

omit [DecidableEq n] in
/-- The integral against the empirical spectral measure, for every square $\mathbf{A}$ and
every $f : \mathbb{R} \to \mathbb{R}$, is the average of $f$ over the eigenvalues counted with
multiplicity: $\lvert n\rvert^{-1}\sum_{k<\lvert n\rvert} f(\lambda_k(\mathbf{A}))$. -/
theorem integral_empiricalSpectralMeasure (A : Matrix n n 𝕜) (f : ℝ → ℝ) :
    ∫ x, f x ∂empiricalSpectralMeasure A =
      (∑ k ∈ Finset.range (Fintype.card n), f (eigenvalue A k)) / Fintype.card n := by
  rw [empiricalSpectralMeasure, integral_smul_measure,
    integral_finsetSum_measure fun k _ => integrable_dirac enorm_lt_top]
  simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]
  rw [div_eq_inv_mul]

/-- The integral against the empirical spectral measure of a Hermitian $\mathbf{A}$ is the
normalised trace: $\int f\,d\nu_{\mathbf{A}} =
\operatorname{Re}\operatorname{tr} f(\mathbf{A}) / \lvert n\rvert$, $\nu_{\mathbf{A}}$ the
empirical spectral measure. -/
theorem _root_.Matrix.IsHermitian.integral_empiricalSpectralMeasure {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (f : ℝ → ℝ) :
    ∫ x, f x ∂empiricalSpectralMeasure A = RCLike.re (cfc f A).trace / Fintype.card n := by
  rw [NLAlib.integral_empiricalSpectralMeasure, hA.re_trace_cfc]

/-- The spectral measures of the coordinate vectors add up to the counting measure of the
eigenvalues: for Hermitian $\mathbf{A}$,
$\sum_i \mu_{\mathbf{A},\mathbf{e}_i} = \lvert n\rvert\,\nu_{\mathbf{A}}$,
$\nu_{\mathbf{A}}$ the empirical spectral measure. -/
theorem _root_.Matrix.IsHermitian.sum_spectralMeasure_single {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) :
    ∑ i, spectralMeasure A (Pi.single i 1) =
      (Fintype.card n : ℝ≥0∞) • empiricalSpectralMeasure A := by
  ext S hS
  have hind : ∀ x, 0 ≤ S.indicator (fun _ => (1 : ℝ)) x :=
    Set.indicator_nonneg fun _ _ => zero_le_one
  have hdiag : ∀ i, RCLike.re (quadForm (cfc (S.indicator fun _ => (1 : ℝ)) A) (Pi.single i 1)) =
      RCLike.re (cfc (S.indicator fun _ => (1 : ℝ)) A i i) := fun i => by
    simp [quadForm_def]
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  simp only [spectralMeasure_apply, hdiag]
  rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => by
      rw [← hdiag]; exact re_quadForm_cfc_indicator_nonneg A _ S,
    ← map_sum, show (∑ i, cfc (S.indicator fun _ => (1 : ℝ)) A i i) =
      (cfc (S.indicator fun _ => (1 : ℝ)) A).trace from rfl, hA.re_trace_cfc,
    ENNReal.ofReal_sum_of_nonneg fun k _ => hind _, Measure.smul_apply, empiricalSpectralMeasure,
    Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul, smul_eq_mul]
  have hk : ∀ k ∈ Finset.range (Fintype.card n), ENNReal.ofReal
      (S.indicator (fun _ => (1 : ℝ)) (eigenvalue A k)) = Measure.dirac (eigenvalue A k) S :=
    fun k _ => by
      rw [Measure.dirac_apply]
      by_cases hx : eigenvalue A k ∈ S <;> simp [hx]
  rw [Finset.sum_congr rfl hk]
  rcases Nat.eq_zero_or_pos (Fintype.card n) with h0 | h0
  · simp [h0]
  · rw [← mul_assoc, ENNReal.mul_inv_cancel (by exact_mod_cast h0.ne') (ENNReal.natCast_ne_top _),
      one_mul]

/-- The empirical spectral measure of every set: for Hermitian $\mathbf{A}$ and every
$S \subseteq \mathbb{R}$, $\nu_{\mathbf{A}}(S) =
\operatorname{Re}\operatorname{tr}\mathbf{1}_S(\mathbf{A}) / \lvert n\rvert$, the fraction of the
eigenvalues, counted with multiplicity, that lie in $S$; $\nu_{\mathbf{A}}$ is the empirical
spectral measure. No measurability of $S$ is needed (the measure is atomic). -/
theorem _root_.Matrix.IsHermitian.empiricalSpectralMeasure_real {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (S : Set ℝ) :
    (empiricalSpectralMeasure A).real S =
      RCLike.re (cfc (S.indicator fun _ => (1 : ℝ)) A).trace / Fintype.card n := by
  rw [measureReal_def, empiricalSpectralMeasure, Measure.smul_apply, Measure.coe_finsetSum,
    Finset.sum_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, ENNReal.toReal_sum fun k _ => measure_ne_top _ _, hA.re_trace_cfc,
    div_eq_inv_mul]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Measure.dirac_apply]
  by_cases hx : eigenvalue A k ∈ S <;> simp [hx]

/-- The empirical spectral measure of a Hermitian $\mathbf{A}$ lives on the spectrum. -/
theorem _root_.Matrix.IsHermitian.ae_mem_spectrum_empiricalSpectralMeasure {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) : ∀ᵐ x ∂empiricalSpectralMeasure A, x ∈ spectrum ℝ A := by
  rw [ae_iff, empiricalSpectralMeasure, Measure.smul_apply, Measure.coe_finsetSum,
    Finset.sum_apply, Finset.sum_eq_zero fun k hk => ?_, smul_zero]
  change Measure.dirac (eigenvalue A k) (spectrum ℝ A)ᶜ = 0
  rw [Measure.dirac_apply' _ A.finite_real_spectrum.measurableSet.compl,
    Set.indicator_of_notMem
      (Set.notMem_compl_iff.2 (hA.eigenvalue_mem_spectrum (Finset.mem_range.1 hk)))]

/-- Polynomial inner products are spectral integrals: for Hermitian $\mathbf{A}$, every
$\mathbf{b}$ and real polynomials $p$, $r$,
$$\langle p(\mathbf{A})\mathbf{b}, r(\mathbf{A})\mathbf{b}\rangle =
\int p\,r\,d\mu_{\mathbf{A},\mathbf{b}}\,,$$
the inner product of $p$ and $r$ in $L^2(\mu_{\mathbf{A},\mathbf{b}})$. -/
theorem _root_.Matrix.IsHermitian.star_aeval_mulVec_dotProduct_aeval_mulVec {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) (p r : ℝ[X]) :
    star (aeval A p *ᵥ b) ⬝ᵥ (aeval A r *ᵥ b) =
      ((∫ x, p.eval x * r.eval x ∂spectralMeasure A b : ℝ) : 𝕜) := by
  have hp : (aeval A p)ᴴ = aeval A p := (hA.aeval p).eq
  rw [star_mulVec_dotProduct, hp, Matrix.mulVec_mulVec, ← map_mul, ← quadForm_def]
  simp only [← eval_mul]
  rw [hA.integral_eval_spectralMeasure, (hA.aeval (p * r)).coe_re_quadForm]

/-- Polynomial norms are spectral integrals: for Hermitian $\mathbf{A}$, every $\mathbf{b}$ and
every real polynomial $p$, $\|p(\mathbf{A})\mathbf{b}\|^2 = \int
p^2\,d\mu_{\mathbf{A},\mathbf{b}}$. -/
theorem _root_.Matrix.IsHermitian.norm_aeval_mulVec_sq {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) (p : ℝ[X]) :
    ‖WithLp.toLp 2 (aeval A p *ᵥ b)‖ ^ 2 = ∫ x, p.eval x ^ 2 ∂spectralMeasure A b := by
  have h := hA.star_aeval_mulVec_dotProduct_aeval_mulVec b p p
  rw [EuclideanSpace.star_dotProduct_self_eq_coe_norm_sq, RCLike.ofReal_inj] at h
  rw [h]
  simp only [sq]

/-- The spectral measure of a diagonal matrix: for real $\mathbf{d}$ and every $\mathbf{w}$,
$$\mu_{\operatorname{diag}(\mathbf{d}),\,\mathbf{w}} = \sum_i\lvert\mathbf{w}_i\rvert^2\,
\delta_{\mathbf{d}_i}\,.$$ -/
theorem spectralMeasure_diagonal {r : Type*} [Fintype r] [DecidableEq r] (d : r → ℝ)
    (w : r → 𝕜) :
    spectralMeasure (Matrix.diagonal fun i => ((d i : ℝ) : 𝕜)) w =
      ∑ i, ENNReal.ofReal (‖w i‖ ^ 2) • Measure.dirac (d i) := by
  have h1 : HasOrthonormalCols (1 : Matrix r r 𝕜) :=
    hasOrthonormalCols_iff.2 (by rw [Matrix.conjTranspose_one, Matrix.one_mul])
  have hA : (Matrix.diagonal fun i => ((d i : ℝ) : 𝕜) : Matrix r r 𝕜) =
      (1 : Matrix r r 𝕜) * Matrix.diagonal (fun i => ((d i : ℝ) : 𝕜)) * (1 : Matrix r r 𝕜)ᴴ := by
    rw [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]
  rw [h1.spectralMeasure_eq_sum rfl hA]
  simp only [Matrix.conjTranspose_one, Matrix.one_mulVec]

/-- Every finite measure carried by a finite set is a spectral measure: if a finite measure
$\nu$ is carried by a finite set $s \subseteq \mathbb{R}$, then $\nu$ is the spectral measure of
the real diagonal matrix of the points of $s$ and the vector of the square roots of their masses,
$\nu = \mu_{\operatorname{diag}(x)_{x\in s},\,(\sqrt{\nu\{x\}})_{x\in s}}$. -/
theorem spectralMeasure_diagonal_sqrt_of_ae_mem {ν : Measure ℝ} [IsFiniteMeasure ν]
    {s : Finset ℝ} (hν : ∀ᵐ x ∂ν, x ∈ s) :
    spectralMeasure (Matrix.diagonal fun x : s => (x : ℝ)) (fun x => √(ν.real {(x : ℝ)})) = ν := by
  have hsum : ν = ∑ a ∈ s, ν {a} • Measure.dirac a := Measure.ae_mem_finset_iff.mp hν
  calc spectralMeasure (Matrix.diagonal fun x : s => (x : ℝ)) (fun x => √(ν.real {(x : ℝ)}))
      = ∑ i : s, ENNReal.ofReal (‖√(ν.real {↑i})‖ ^ 2) • Measure.dirac (i : ℝ) :=
        spectralMeasure_diagonal _ _
    _ = ν := by
        rw [Finset.sum_coe_sort s (fun a : ℝ => ENNReal.ofReal (‖√(ν.real {a})‖ ^ 2) •
          Measure.dirac a)]
        refine Eq.trans (Finset.sum_congr rfl fun a _ => ?_) hsum.symm
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
          Real.sq_sqrt (measureReal_nonneg), ofReal_measureReal]

/-- Every spectral measure is carried by a compact interval: for every square $\mathbf{A}$ and
every $\mathbf{b}$, $\mu_{\mathbf{A},\mathbf{b}}$-almost every $x$ lies in some $[a, a']$, the
support hypothesis of the Polynomial layer (`ae_mem_Icc_spectralMeasure` with bounds of the
finite spectrum). -/
theorem exists_ae_mem_Icc_spectralMeasure (A : Matrix n n 𝕜) (b : n → 𝕜) :
    ∃ a a' : ℝ, ∀ᵐ x ∂spectralMeasure A b, x ∈ Set.Icc a a' := by
  obtain ⟨a, ha⟩ := A.finite_real_spectrum.bddBelow
  obtain ⟨a', ha'⟩ := A.finite_real_spectrum.bddAbove
  exact ⟨a, a', ae_mem_Icc_spectralMeasure A (fun x hx => ⟨ha hx, ha' hx⟩) b⟩

end NLAlib
