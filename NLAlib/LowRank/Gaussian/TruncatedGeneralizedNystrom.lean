/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Probability.Independence.Basic
public import NLAlib.ForMathlib.Probability.Moments.Variance
public import NLAlib.LowRank.Gaussian.GeneralizedNystrom
public import NLAlib.LowRank.Gaussian.RangeFinder
public import NLAlib.LowRank.Structural.Truncation

/-!
# Truncated generalized Nyström in expectation

For independent standard Gaussian test matrices $\mathbf{\Omega}$ ($n \times \ell$, the Lean
`X`) and $\mathbf{\Psi}$ ($m \times p$), the late truncation
$\llbracket\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})\rrbracket_k$ of generalized
Nyström (`NLAlib.generalizedNystrom`, `NLAlib.truncatedSVD`) reaches relative error
$1 + \varepsilon$ in expectation with $\ell = O(k/\varepsilon)$ and $p = O(k/\varepsilon^2)$:
for $4k \le \ell$ and $4\ell \le p$ the expected squared Frobenius error is at most a named
factor times $\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$, a factor at
most $1 + \varepsilon$ at $\ell \ge 6k/\varepsilon$, $p \ge 8000\ell/\varepsilon$. The proof
combines the perturbed truncation lemma
`NLAlib.frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_specNorm` (the spectral norm of
the core noise enters with weight $\sqrt{k}$), the expected error of the truncated randomized SVD,
the spectral core noise of Gaussian sketch-and-solve
(`integral_specNorm_obliqueProjector_mul_one_sub_rangeProjector_mul_sq_le_of_hasLaw_gaussianMatrix`)
conditionally on $\mathbf{\Omega}$, and the second spectral moment of the range finder at a
comparison rank near $\ell/2$
(`NLAlib.integral_specNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix_pinvSpecNormBound`). A second
bound, through the Frobenius norm of the core noise, has milder size conditions and better
constants at practical sizes but needs $p = O(k/\varepsilon^3)$. Every rank of $\mathbf{A}$; the
truncation is `truncatedSVD`, measurable (`NLAlib.measurable_truncatedSVD`), and both bounds hold
for every best rank-$k$ approximation of the output. Real throughout. Design:
`docs/design/LowRank-S6.md` §3.5, §3.7, §8.

## Main definitions

* `NLAlib.truncatedGNFactor k l p`: the factor of the expected error, at
  present <!-- value truncatedGNFactor k \ell p -->
  $$1 + \frac{k}{\ell - k - 1} + 4\sqrt{\frac{2k}{p}\Bigl(25\Bigl(1 + \frac{k}{\ell - k - 1}\Bigr) +
  484\Bigr)} + \frac{8k}{p}\Bigl(25\Bigl(1 + \frac{k}{\ell - k - 1}\Bigr) + 484\Bigr)\,.$$

## Main results

* `NLAlib.integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_of_hasLaw_gaussianMatrix`:
  the expected error.
* [relative-error bound](https://nla-lib.org/explore/#d/NLAlib.integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_one_add_mul_of_hasLaw_gaussianMatrix):
  relative error $1 + \varepsilon$; its asymptotic form is
  [asymptotic form](https://nla-lib.org/explore/#d/NLAlib.exists_forall_integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_of_hasLaw_gaussianMatrix).
* the Frobenius core-noise form:
  `integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_sqrt_of_hasLaw_gaussianMatrix`.
* `NLAlib.integral_frobNorm_rangeProjector_mul_obliqueProjector_sq_of_hasLaw_gaussianMatrix`: the
  core noise in the dominant rank-$k$ subspace of the randomized SVD has mean
  $k/(p - \ell - 1)$ times the range-finder error, exactly.
* `NLAlib.integral_frobNorm_sub_truncatedSVD_rsvd_sub_rangeProjector_sq_of_hasLaw_gaussianMatrix`:
  the oracle truncation's expected error, exactly, and its bound
  `integral_frobNorm_sub_truncatedSVD_rsvd_sub_rangeProjector_sq_le_of_hasLaw_gaussianMatrix`.
  Both are new (research note OP2 of the NLAlib workflow, §3); they feed the lower bound
  `NLAlib.LowerBounds.LowRank.TruncatedGeneralizedNystrom`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal

namespace NLAlib

/-! ### The truncated generalized Nyström factor -/

/-- **The truncated generalized Nyström factor**: the multiplier of
$\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$ in the expected squared
Frobenius error of truncated generalized Nyström with independent Gaussian test matrices of sizes
$\ell$ and $p$, for $4k \le \ell$ and $4\ell \le p$
(`NLAlib.integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_of_hasLaw_gaussianMatrix`),
at present <!-- value truncatedGNFactor k \ell p -->
$$1 + \frac{k}{\ell - k - 1} + 4\sqrt{\frac{2k}{p}\Bigl(25\Bigl(1 + \frac{k}{\ell - k - 1}\Bigr) +
484\Bigr)} + \frac{8k}{p}\Bigl(25\Bigl(1 + \frac{k}{\ell - k - 1}\Bigr) + 484\Bigr)\,.$$
For $0 < \varepsilon \le 1$, it is at most $1 + \varepsilon$ at $\ell \ge 6k/\varepsilon$,
$p \ge 8000\ell/\varepsilon$ (`NLAlib.truncatedGNFactor_le_one_add`).
Source value: none; proved here without a matching published bound. Value proved: as displayed;
the triangle inequality alone gives a squared-error factor of $9$
(`NLAlib.IsBestRankApprox.matrixNorm_sub_le_add_two_mul`).
Consumers use `NLAlib.one_le_truncatedGNFactor` and `NLAlib.truncatedGNFactor_le_one_add`.
Junk for $\ell \le k + 1$ with $k \ge 1$; the theorems carry `4 * k ≤ l`. -/
noncomputable irreducible_def truncatedGNFactor (k l p : ℕ) : ℝ :=
  gaussianProjectionFactor k l +
    4 * √(2 * k * ((25 * gaussianProjectionFactor k l + 484) / p)) +
      8 * k * ((25 * gaussianProjectionFactor k l + 484) / p)

/-- The truncated generalized Nyström factor is at least $1$: for
$4k \le \ell$, <!-- value truncatedGNFactor k \ell p -->
$$1 \le 1 + \frac{k}{\ell - k - 1} + 4\sqrt{\frac{2k}{p}\Bigl(25\Bigl(1 + \frac{k}{\ell - k - 1}
\Bigr) + 484\Bigr)} + \frac{8k}{p}\Bigl(25\Bigl(1 + \frac{k}{\ell - k - 1}\Bigr) + 484\Bigr)\,.$$ -/
theorem one_le_truncatedGNFactor {k l p : ℕ} (h : 4 * k ≤ l) : 1 ≤ truncatedGNFactor k l p := by
  rw [truncatedGNFactor_def]
  have hg : 1 ≤ gaussianProjectionFactor k l := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp only [gaussianProjectionFactor_def, Nat.cast_zero, zero_div, add_zero, le_refl]
    · exact one_le_gaussianProjectionFactor (by omega)
  have hc : 0 ≤ (25 * gaussianProjectionFactor k l + 484) / p :=
    div_nonneg (by linarith) (Nat.cast_nonneg _)
  have h1 : 0 ≤ 4 * √(2 * k * ((25 * gaussianProjectionFactor k l + 484) / p)) := by positivity
  have h2 : 0 ≤ 8 * k * ((25 * gaussianProjectionFactor k l + 484) / p) := by positivity
  linarith

/-- The explicit comparison of the truncated generalized Nyström factor: for
$0 < \varepsilon \le 1$, $6k \le \varepsilon\ell$ and
$8000\,\ell \le \varepsilon p$, <!-- value truncatedGNFactor k \ell p -->
$$1 + \frac{k}{\ell - k - 1} + 4\sqrt{\frac{2k}{p}\Bigl(25\Bigl(1 + \frac{k}{\ell - k - 1}
\Bigr) + 484\Bigr)} + \frac{8k}{p}\Bigl(25\Bigl(1 + \frac{k}{\ell - k - 1}\Bigr) + 484\Bigr) \le
1 + \varepsilon\,.$$ -/
theorem truncatedGNFactor_le_one_add {k l p : ℕ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hl : 6 * (k : ℝ) ≤ ε * l) (hp : 8000 * (l : ℝ) ≤ ε * p) :
    truncatedGNFactor k l p ≤ 1 + ε := by
  rw [truncatedGNFactor_def]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp only [gaussianProjectionFactor_def, Nat.cast_zero, zero_div, add_zero, mul_zero,
      zero_mul, Real.sqrt_zero]
    linarith
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hl' : 6 * (k : ℝ) ≤ l := by nlinarith
  have hp0 : (0 : ℝ) < p := by nlinarith
  have hden : 0 < (l : ℝ) - k - 1 := by linarith
  set g := gaussianProjectionFactor k l with hgdef
  have hg : g ≤ 1 + ε / 4 := by
    rw [hgdef, gaussianProjectionFactor_def, add_le_add_iff_left,
      div_le_div_iff₀ hden (by norm_num)]
    nlinarith
  have hk2 : k + 2 ≤ l := by
    have : (k : ℝ) + 2 ≤ l := by linarith
    exact_mod_cast this
  have hg1 : 1 ≤ g := one_le_gaussianProjectionFactor hk2
  set c := (25 * g + 484) / p with hcdef
  have hc0 : 0 ≤ c := div_nonneg (by linarith) hp0.le
  have hkp : 48000 * (k : ℝ) ≤ ε ^ 2 * p := by nlinarith
  have hkc : (k : ℝ) * c ≤ 515.25 / 48000 * ε ^ 2 := by
    rw [hcdef, mul_div_assoc', div_le_iff₀ hp0]
    nlinarith
  have hs : √(2 * k * c) ≤ 0.15 * ε := by
    rw [show (0.15 : ℝ) * ε = √((0.15 * ε) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have h8 : 8 * k * c ≤ 0.09 * ε := by nlinarith
  rw [show 2 * (k : ℝ) * c = 2 * k * c from rfl] at hs
  linarith

/-- The shared-size comparison of the truncated generalized Nyström factor, for the asymptotic
form: for $0 < \varepsilon \le 1$, $160k \le \varepsilon\ell$ and
$160\ell \le \varepsilon p$, <!-- value truncatedGNFactor k \ell p -->
$$1 + \frac{k}{\ell - k - 1} + 4\sqrt{\frac{2k}{p}\Bigl(25\Bigl(1 + \frac{k}{\ell - k - 1}
\Bigr) + 484\Bigr)} + \frac{8k}{p}\Bigl(25\Bigl(1 + \frac{k}{\ell - k - 1}\Bigr) + 484\Bigr) \le
1 + \varepsilon\,:$$
$k/(\ell - k - 1) \le \varepsilon/150$, $k/p \le \varepsilon^2/25600$, and
$\varepsilon/150 + 4\sqrt{1020/25600}\,\varepsilon + 8 \cdot 510\,\varepsilon^2/25600 \le
\varepsilon$. -/
private theorem truncatedGNFactor_le_one_add_of_mul_le {k l p : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hl : 160 * (k : ℝ) ≤ ε * l) (hp : 160 * (l : ℝ) ≤ ε * p) :
    truncatedGNFactor k l p ≤ 1 + ε := by
  rw [truncatedGNFactor_def]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp only [gaussianProjectionFactor_def, Nat.cast_zero, zero_div, add_zero, mul_zero,
      zero_mul, Real.sqrt_zero]
    linarith
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hl' : 160 * (k : ℝ) ≤ l := by nlinarith
  have hp0 : (0 : ℝ) < p := by nlinarith
  have hden : 0 < (l : ℝ) - k - 1 := by linarith
  set g := gaussianProjectionFactor k l with hgdef
  have hg : g ≤ 1 + ε / 150 := by
    rw [hgdef, gaussianProjectionFactor_def, add_le_add_iff_left,
      div_le_div_iff₀ hden (by norm_num)]
    nlinarith
  set c := (25 * g + 484) / p with hcdef
  have hkp : 25600 * (k : ℝ) ≤ ε ^ 2 * p := by nlinarith
  have hkc : (k : ℝ) * c ≤ 510 / 25600 * ε ^ 2 := by
    rw [hcdef, mul_div_assoc', div_le_iff₀ hp0]
    nlinarith
  have hs : √(2 * k * c) ≤ 0.2 * ε := by
    rw [show (0.2 : ℝ) * ε = √((0.2 * ε) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have h8 : 8 * k * c ≤ 0.16 * ε := by nlinarith
  linarith

/-! ### Helpers: the joint rank event -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n l p : Type*} [Fintype m]
  [Fintype n] [Fintype l] [Fintype p] {X : Ω → Matrix n l ℝ} {Ψ : Ω → Matrix m p ℝ}

/-- The joint rank event of the two test matrices: almost surely
$\operatorname{rank}(\mathbf{\Psi}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega}) =
\operatorname{rank}(\mathbf{A}\mathbf{\Omega})$, for any law of $\mathbf{\Omega}$ independent of a
standard Gaussian $\mathbf{\Psi}$, when every $\operatorname{rank}(\mathbf{A}\mathbf{x}) \le p$.
Proved without a literature source. -/
theorem ae_rank_conjTranspose_mul_mul_eq (A : Matrix m n ℝ)
    (hX : AEMeasurable X μ) (hΨ : HasLaw Ψ (gaussianMatrix m p) μ) (hXΨ : IndepFun X Ψ μ)
    (hr : ∀ x : Matrix n l ℝ, (A * x).rank ≤ Fintype.card p) :
    ∀ᵐ ω ∂μ, ((Ψ ω)ᴴ * (A * X ω)).rank = (A * X ω).rank := by
  have := hΨ.isProbabilityMeasure
  set E : Set (Matrix m p ℝ × Matrix n l ℝ) := {q | (q.1ᴴ * (A * q.2)).rank ≠ (A * q.2).rank}
    with hEdef
  have hE : MeasurableSet E := by
    have h1 : Measurable fun q : Matrix m p ℝ × Matrix n l ℝ => (q.1ᴴ * (A * q.2)).rank :=
      measurable_rank.comp ((continuous_id.matrix_conjTranspose.measurable.comp
        measurable_fst).matrix_mul (measurable_const.matrix_mul measurable_snd))
    have h2 : Measurable fun q : Matrix m p ℝ × Matrix n l ℝ => (A * q.2).rank :=
      measurable_rank.comp (measurable_const.matrix_mul measurable_snd)
    exact (measurableSet_eq_fun h1 h2).compl
  have hsec (x : Matrix n l ℝ) (_ : x ∈ Set.univ) : μ.real {ω | (Ψ ω, x) ∈ E} ≤ 0 := by
    have h := ae_iff.mp (ae_rank_conjTranspose_mul_eq_of_hasLaw_gaussianMatrix (A * x) hΨ (hr x))
    change (μ {a | ¬((Ψ a)ᴴ * (A * x)).rank = (A * x).rank}).toReal ≤ 0
    rw [h, ENNReal.toReal_zero]
  have h := hXΨ.symm.measureReal_mem_le_add hΨ.aemeasurable hX hE MeasurableSet.univ le_rfl hsec
    (δ₂ := 0) (by simp)
  rw [add_zero] at h
  have h0 : μ {ω | (Ψ ω, X ω) ∈ E} = 0 :=
    (measureReal_eq_zero_iff (measure_ne_top μ _)).mp (le_antisymm h measureReal_nonneg)
  exact ae_iff.mpr (by simpa only [hEdef, Set.mem_ofPred_eq] using h0)

/-! ### The spectral core noise and the spectral residual -/

/-- The core noise $\mathbf{\Pi}_{\mathbf{A}\mathbf{x},\mathbf{\psi}^{\mathsf{H}}}
(\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{x}))$ is measurable in the pair. -/
theorem measurable_obliqueProjector_mul_sub_rsvd (A : Matrix m n ℝ) :
    Measurable fun q : Matrix n l ℝ × Matrix m p ℝ =>
      obliqueProjector (A * q.1) q.2ᴴ * (A - rsvd A q.1) := by
  have hΨ : Measurable fun q : Matrix n l ℝ × Matrix m p ℝ => q.2ᴴ :=
    (continuous_id.matrix_conjTranspose.measurable).comp measurable_snd
  have hAX : Measurable fun q : Matrix n l ℝ × Matrix m p ℝ => A * q.1 :=
    measurable_const.matrix_mul measurable_fst
  simp only [obliqueProjector]
  exact ((hAX.matrix_mul (measurable_pinv.comp (hΨ.matrix_mul hAX))).matrix_mul hΨ).matrix_mul
    (measurable_const.sub ((measurable_rsvd A).comp measurable_fst))

/-- The squared spectral norm of the core noise is measurable in the pair. -/
private theorem measurable_specNorm_obliqueProjector_sub_rsvd_sq (A : Matrix m n ℝ) :
    Measurable fun q : Matrix n l ℝ × Matrix m p ℝ =>
      specNorm (obliqueProjector (A * q.1) q.2ᴴ * (A - rsvd A q.1)) ^ 2 :=
  (continuous_specNorm.measurable.comp (measurable_obliqueProjector_mul_sub_rsvd A)).pow_const 2

/-- The arithmetic of the spectral residual: from $\ell\sigma^2 \le 4\,\mathrm{OPT}^2$,
$w \le \mathrm{OPT}$, $h \le 3$ and $\ell\beta^2 \le 32.4$ with $\ell \ge 4$, the second-moment
bound $\sigma^2 + (\sigma\sqrt h + \beta w)^2 + \sigma^2\beta^2$ is at most
$(121/\ell)\mathrm{OPT}^2$. -/
private theorem residual_arith {L u w O h β : ℝ} (hL : 4 ≤ L) (hw0 : 0 ≤ w)
    (hwO : w ≤ O) (hu : L * u ^ 2 ≤ 4 * O ^ 2) (hh0 : 0 ≤ h) (hh : h ≤ 3)
    (hβ : L * β ^ 2 ≤ 32.4) :
    u ^ 2 + (u * √h + β * w) ^ 2 + (u * β) ^ 2 ≤ 121 / L * O ^ 2 := by
  have hL0 : 0 < L := by linarith
  have hs : √h ^ 2 = h := Real.sq_sqrt hh0
  have hw2 : w ^ 2 ≤ O ^ 2 := pow_le_pow_left₀ hw0 hwO 2
  have hcross : (u * √h + β * w) ^ 2 ≤ 2.6 * (u ^ 2 * h) + 1.625 * (β ^ 2 * w ^ 2) := by
    nlinarith [sq_nonneg (1.6 * (u * √h) - β * w)]
  have h1 : L * (2.6 * (u ^ 2 * h)) ≤ 31.2 * O ^ 2 := by
    have : L * u ^ 2 * h ≤ 4 * O ^ 2 * 3 :=
      mul_le_mul hu hh hh0 (by positivity)
    nlinarith
  have h2 : L * (1.625 * (β ^ 2 * w ^ 2)) ≤ 52.65 * O ^ 2 := by
    have : L * β ^ 2 * w ^ 2 ≤ 32.4 * O ^ 2 :=
      mul_le_mul hβ hw2 (sq_nonneg _) (by norm_num)
    nlinarith
  have h3 : L * (u * β) ^ 2 ≤ 32.4 * O ^ 2 := by
    have hb : β ^ 2 ≤ 8.1 := by nlinarith
    have : L * u ^ 2 * β ^ 2 ≤ 4 * O ^ 2 * 8.1 := mul_le_mul hu hb (sq_nonneg _) (by positivity)
    nlinarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hL0]
  nlinarith [mul_le_mul_of_nonneg_left hcross hL0.le]

/-- The constants of the range finder at the comparison rank $j = \lceil \ell/2 \rceil$: for
$\ell \ge 4$, $j/(\ell - j - 1) \le 3$. -/
private theorem div_le_three_of_half {L j : ℕ} (hL : 4 ≤ L) (hj : j = (L + 1) / 2) :
    (j : ℝ) / ((L : ℝ) - j - 1) ≤ 3 := by
  rcases (by omega : L = 4 ∨ 5 ≤ L) with h | h
  · subst h
    have : j = 2 := by omega
    subst this
    norm_num
  · have h1 : 2 * j ≤ L + 1 := by omega
    have h1' : 2 * (j : ℝ) ≤ L + 1 := by exact_mod_cast h1
    have h5 : (5 : ℝ) ≤ L := by exact_mod_cast h
    rw [div_le_iff₀ (by linarith)]
    linarith

/-- The constants of the range finder at the comparison rank $j = \lceil \ell/2 \rceil$: for
$\ell \ge 4$, <!-- value gaussianPinvSpecNormBound j \ell -->
$\ell\bigl(e\sqrt{(\ell + j - 1)/2}/(\ell - j)\bigr)^2 \le 32.4$. -/
private theorem mul_gaussianPinvSpecNormBound_sq_le_of_half {L j : ℕ} (hL : 4 ≤ L)
    (hj : j = (L + 1) / 2) : (L : ℝ) * gaussianPinvSpecNormBound j L ^ 2 ≤ 32.4 := by
  have he := Real.exp_one_lt_d9
  have he0 := Real.exp_pos 1
  have he2 : Real.exp 1 ^ 2 ≤ 7.3891 := by nlinarith
  have h1 : 2 * j ≤ L + 1 := by omega
  have h2 : L ≤ 2 * j := by omega
  have h1' : 2 * (j : ℝ) ≤ L + 1 := by exact_mod_cast h1
  have h2' : (L : ℝ) ≤ 2 * j := by exact_mod_cast h2
  have hL' : (4 : ℝ) ≤ L := by exact_mod_cast hL
  have hLj : 0 < (L : ℝ) - j := by linarith
  rw [gaussianPinvSpecNormBound_def, mul_pow, div_pow, Real.sq_sqrt (by linarith),
    show (L : ℝ) * (Real.exp 1 ^ 2 / ((L : ℝ) - j) ^ 2 * (((L : ℝ) + j - 1) / 2)) =
      Real.exp 1 ^ 2 * ((L : ℝ) * ((L : ℝ) + j - 1)) / (2 * ((L : ℝ) - j) ^ 2) by
      field_simp, div_le_iff₀ (by positivity)]
  rcases (by omega : L = 4 ∨ 5 ≤ L) with h | h
  · subst h
    have : j = 2 := by omega
    subst this
    push_cast
    nlinarith
  · have h5 : (5 : ℝ) ≤ L := by exact_mod_cast h
    have hA : (L : ℝ) * ((L : ℝ) + j - 1) ≤ (L : ℝ) * ((3 * L - 1) / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have hB : ((L : ℝ) - 1) ^ 2 / 4 ≤ ((L : ℝ) - j) ^ 2 := by nlinarith
    have hC : 7.3891 * ((L : ℝ) * ((3 * L - 1) / 2)) ≤ 64.8 * (((L : ℝ) - 1) ^ 2 / 4) := by
      nlinarith
    have hD := mul_le_mul he2 hA (by nlinarith) (by norm_num)
    nlinarith

/-- **The spectral residual of the range finder**: for a standard Gaussian $n \times \ell$ test
matrix, $k \ge 1$ and $4k \le \ell$,
$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_2^2 \le
(121/\ell)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$, from the second
spectral moment at the comparison rank $\lceil \ell/2 \rceil$ and the tail flattening. -/
private theorem integral_specNorm_sub_rsvd_sq_le_div (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ} (hk : 1 ≤ k) (hkl : 4 * k ≤ Fintype.card l) :
    ∫ ω, specNorm (A - rsvd A (X ω)) ^ 2 ∂μ ≤
      121 / (Fintype.card l : ℝ) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  set L := Fintype.card l with hLdef
  set j := (L + 1) / 2 with hjdef
  have hL4 : 4 ≤ L := by omega
  have hj2 : j + 2 ≤ L := by omega
  have hkj : k ≤ j := by omega
  refine (integral_specNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix_pinvSpecNormBound A hX
    hj2).trans ?_
  have hL' : (4 : ℝ) ≤ L := by exact_mod_cast hL4
  -- the tail flattening at `d = j - k`
  have hflat := natCast_mul_singularValues_add_sq_le_frobNorm_sub_truncatedSVD_sq A k (j - k)
  rw [Nat.add_sub_cancel' hkj] at hflat
  have hd : (L : ℝ) ≤ 4 * ((j - k : ℕ) : ℝ) := by
    have : L ≤ 4 * (j - k) := by omega
    exact_mod_cast this
  have hu : (L : ℝ) * singularValues A j ^ 2 ≤ 4 * frobNorm (A - truncatedSVD A k) ^ 2 := by
    nlinarith [sq_nonneg (singularValues A j)]
  -- the optimal error is antitone in the rank
  have hw : frobNorm (A - truncatedSVD A j) ≤ frobNorm (A - truncatedSVD A k) := by
    refine (pow_le_pow_iff_left₀ (frobNorm_nonneg _) (frobNorm_nonneg _) two_ne_zero).mp ?_
    rw [frobNorm_sub_truncatedSVD_sq, frobNorm_sub_truncatedSVD_sq]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_left hkj)
      fun _ _ _ => sq_nonneg _
  exact residual_arith hL' (frobNorm_nonneg _) hw hu
    (div_nonneg (Nat.cast_nonneg _) (by
      have : (j : ℝ) + 2 ≤ L := by exact_mod_cast hj2
      linarith))
    (div_le_three_of_half hL4 rfl) (mul_gaussianPinvSpecNormBound_sq_le_of_half hL4 rfl)

-- The names of the sketch-and-solve lemmas used exceed 100 characters with their indentation.
set_option linter.style.longLine false in
/-- **The spectral core noise of generalized Nyström**: for independent standard Gaussian test
matrices, $k \ge 1$, $4k \le \ell$ and $4\ell \le p$, the core noise
$e = \|\mathbf{\Pi}_{\mathbf{A}\mathbf{\Omega},\mathbf{\Psi}^{\mathsf{H}}}(\mathbf{A} -
\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega}))\|_2$ is square integrable with
$\mathbb{E}e^2 \le ((25g + 484)/p)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k
\|_{\mathsf{F}}^2$, $g$ the value of the Gaussian projection factor at $(k, \ell)$. -/
private theorem integral_specNorm_obliqueProjector_sub_rsvd_sq_le (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) (hΨ : HasLaw Ψ (gaussianMatrix m p) μ)
    (hXΨ : IndepFun X Ψ μ) {k : ℕ} (hk : 1 ≤ k) (hkl : 4 * k ≤ Fintype.card l)
    (hlp : 4 * Fintype.card l ≤ Fintype.card p) :
    Integrable (fun ω =>
      specNorm (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω))) ^ 2) μ ∧
    ∫ ω, specNorm (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω))) ^ 2 ∂μ ≤
      (25 * gaussianProjectionFactor k (Fintype.card l) + 484) / Fintype.card p *
        frobNorm (A - truncatedSVD A k) ^ 2 := by
  classical
  have := hX.isProbabilityMeasure
  set L := Fintype.card l with hLdef
  set P := Fintype.card p with hPdef
  have hP0 : (0 : ℝ) < P := by
    have : 0 < P := by omega
    exact_mod_cast this
  have hL0 : (0 : ℝ) < L := by
    have : 0 < L := by omega
    exact_mod_cast this
  set H : Matrix n l ℝ → ℝ := fun x => 25 / (P : ℝ) * frobNorm (A - rsvd A x) ^ 2 +
    4 * (L : ℝ) / P * specNorm (A - rsvd A x) ^ 2 with hHdef
  have hid : HasLaw (fun ψ : Matrix m p ℝ => ψ) (gaussianMatrix m p) (gaussianMatrix m p) :=
    HasLaw.id
  have hS := hasLaw_conjTranspose_of_hasLaw_gaussianMatrix hid
  have hrank (x : Matrix n l ℝ) : 4 * (A * x).rank ≤ P := by
    have := Matrix.rank_le_card_width (A * x)
    omega
  have hint (x : Matrix n l ℝ) : Integrable (fun ψ : Matrix m p ℝ =>
      specNorm (obliqueProjector (A * x) ψᴴ * (A - rsvd A x)) ^ 2) (gaussianMatrix m p) := by
    rw [sub_rsvd]
    exact
      integrable_specNorm_obliqueProjector_mul_one_sub_rangeProjector_mul_sq_of_hasLaw_gaussianMatrix
        hS (A * x) (by have := hrank x; omega) A
  have hle (x : Matrix n l ℝ) : ∫ ψ, specNorm (obliqueProjector (A * x) ψᴴ * (A - rsvd A x)) ^ 2
      ∂(gaussianMatrix m p) ≤ H x := by
    have h :=
      integral_specNorm_obliqueProjector_mul_one_sub_rangeProjector_mul_sq_le_div_card_of_hasLaw_gaussianMatrix
        hS (A * x) (hrank x) A
    rw [← sub_rsvd] at h
    refine h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)))
    have : ((A * x).rank : ℝ) ≤ L := by exact_mod_cast Matrix.rank_le_card_width (A * x)
    gcongr
  have hHi : Integrable (fun ω => H (X ω)) μ :=
    ((integrable_frobNorm_sub_rsvd_sq A hX.aemeasurable).const_mul _).add
      ((integrable_specNorm_sub_rsvd_sq A hX.aemeasurable).const_mul _)
  have hF := measurable_specNorm_obliqueProjector_sub_rsvd_sq (l := l) (p := p) A
  refine ⟨hXΨ.integrable_comp_of_integral_le hX.aemeasurable hΨ hF (fun _ => sq_nonneg _)
      (ae_of_all _ fun ω => hint (X ω)) (ae_of_all _ fun ω => hle (X ω)) hHi,
    (hXΨ.integral_comp_le_of_integral_le hX.aemeasurable hΨ hF (fun _ => sq_nonneg _)
      (ae_of_all _ fun ω => hint (X ω)) (ae_of_all _ fun ω => hle (X ω)) hHi).trans ?_⟩
  have hG2 := integral_frobNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix A hX
    (k := k) (by omega)
  have hR := integral_specNorm_sub_rsvd_sq_le_div A hX hk hkl
  simp only [hHdef]
  rw [integral_add ((integrable_frobNorm_sub_rsvd_sq A hX.aemeasurable).const_mul _)
      ((integrable_specNorm_sub_rsvd_sq A hX.aemeasurable).const_mul _), integral_const_mul,
    integral_const_mul]
  have e1 : 25 / (P : ℝ) * ∫ ω, frobNorm (A - rsvd A (X ω)) ^ 2 ∂μ ≤
      25 / (P : ℝ) * (gaussianProjectionFactor k L * frobNorm (A - truncatedSVD A k) ^ 2) :=
    mul_le_mul_of_nonneg_left hG2 (by positivity)
  have e2 : 4 * (L : ℝ) / P * ∫ ω, specNorm (A - rsvd A (X ω)) ^ 2 ∂μ ≤
      4 * (L : ℝ) / P * (121 / (L : ℝ) * frobNorm (A - truncatedSVD A k) ^ 2) :=
    mul_le_mul_of_nonneg_left hR (by positivity)
  have e3 : 4 * (L : ℝ) / P * (121 / (L : ℝ) * frobNorm (A - truncatedSVD A k) ^ 2) =
      484 / P * frobNorm (A - truncatedSVD A k) ^ 2 := by
    field_simp
    ring
  have e4 : (25 * gaussianProjectionFactor k L + 484) / P * frobNorm (A - truncatedSVD A k) ^ 2 =
      25 / (P : ℝ) * (gaussianProjectionFactor k L * frobNorm (A - truncatedSVD A k) ^ 2) +
        484 / P * frobNorm (A - truncatedSVD A k) ^ 2 := by
    ring
  linarith

/-- The Frobenius core noise of generalized Nyström: for independent standard Gaussian test
matrices, any law of the range test matrix and $\ell + 2 \le p$, the core noise
$\mathbf{N} = \mathbf{\Pi}_{\mathbf{A}\mathbf{\Omega},\mathbf{\Psi}^{\mathsf{H}}}
(\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega}))$ is square integrable with
$\mathbb{E}\|\mathbf{N}\|_{\mathsf{F}}^2 \le (\ell/(p - \ell - 1))\,
\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_{\mathsf{F}}^2$. -/
private theorem integral_frobNorm_obliqueProjector_sub_rsvd_sq_le (A : Matrix m n ℝ)
    (hX : AEMeasurable X μ) (hΨ : HasLaw Ψ (gaussianMatrix m p) μ) (hXΨ : IndepFun X Ψ μ)
    (hlp : Fintype.card l + 2 ≤ Fintype.card p) :
    Integrable (fun ω =>
      frobNorm (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω))) ^ 2) μ ∧
    ∫ ω, frobNorm (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω))) ^ 2 ∂μ ≤
      (Fintype.card l : ℝ) / ((Fintype.card p : ℝ) - Fintype.card l - 1) *
        ∫ ω, frobNorm (A - rsvd A (X ω)) ^ 2 ∂μ := by
  classical
  have := hΨ.isProbabilityMeasure
  set h := (Fintype.card l : ℝ) / ((Fintype.card p : ℝ) - Fintype.card l - 1) with hhdef
  have hid : HasLaw (fun ψ : Matrix m p ℝ => ψ) (gaussianMatrix m p) (gaussianMatrix m p) :=
    HasLaw.id
  have hS := hasLaw_conjTranspose_of_hasLaw_gaussianMatrix hid
  have hr (x : Matrix n l ℝ) : (A * x).rank + 2 ≤ Fintype.card p := by
    have := Matrix.rank_le_card_width (A * x)
    omega
  have hsplit (x : Matrix n l ℝ) : ∀ᵐ ψ ∂(gaussianMatrix m p),
      frobNorm (obliqueProjector (A * x) ψᴴ * (A - rsvd A x)) ^ 2 =
        frobNorm (A - generalizedNystrom A x ψ) ^ 2 - frobNorm (A - rsvd A x) ^ 2 := by
    filter_upwards [ae_rank_conjTranspose_mul_eq_of_hasLaw_gaussianMatrix (A * x) hid
      (by have := hr x; omega)] with ψ hψ
    rw [frobNorm_sub_generalizedNystrom_sq hψ]
    ring
  have hgn (x : Matrix n l ℝ) : Integrable (fun ψ : Matrix m p ℝ =>
      frobNorm (A - generalizedNystrom A x ψ) ^ 2) (gaussianMatrix m p) := by
    simp only [sub_generalizedNystrom]
    exact integrable_frobNorm_one_sub_obliqueProjector_mul_sq_of_hasLaw_gaussianMatrix hS (A * x)
      (hr x) A
  have hint (x : Matrix n l ℝ) : Integrable (fun ψ : Matrix m p ℝ =>
      frobNorm (obliqueProjector (A * x) ψᴴ * (A - rsvd A x)) ^ 2) (gaussianMatrix m p) :=
    ((hgn x).sub (integrable_const _)).congr ((hsplit x).mono fun _ h => h.symm)
  have hle (x : Matrix n l ℝ) : ∫ ψ, frobNorm (obliqueProjector (A * x) ψᴴ * (A - rsvd A x)) ^ 2
      ∂(gaussianMatrix m p) ≤ h * frobNorm (A - rsvd A x) ^ 2 := by
    rw [integral_congr_ae (hsplit x), integral_sub (hgn x) (integrable_const _),
      integral_frobNorm_sub_generalizedNystrom_sq_of_hasLaw_gaussianMatrix A x hid (hr x),
      integral_const, probReal_univ, one_smul]
    have hq := gaussianProjectionFactor_le_gaussianProjectionFactor
      (Matrix.rank_le_card_width (A * x)) hlp
    rw [gaussianProjectionFactor_def, gaussianProjectionFactor_def] at hq
    rw [gaussianProjectionFactor_def]
    nlinarith [sq_nonneg (frobNorm (A - rsvd A x))]
  have hF := (continuous_frobNorm.measurable.comp
    (measurable_obliqueProjector_mul_sub_rsvd (l := l) (p := p) A)).pow_const 2
  have hHi := (integrable_frobNorm_sub_rsvd_sq A hX).const_mul h
  exact ⟨hXΨ.integrable_comp_of_integral_le hX hΨ hF (fun _ => sq_nonneg _)
      (ae_of_all _ fun ω => hint (X ω)) (ae_of_all _ fun ω => hle (X ω)) hHi,
    (hXΨ.integral_comp_le_of_integral_le hX hΨ hF (fun _ => sq_nonneg _)
      (ae_of_all _ fun ω => hint (X ω)) (ae_of_all _ fun ω => hle (X ω)) hHi).trans_eq
      (integral_const_mul _ _)⟩

/-! ### Truncated generalized Nyström -/

/-- The squared Frobenius error of truncated generalized Nyström is integrable for any law of the
range test matrix independent of a Gaussian co-range test matrix, when $\ell + 2 \le p$. It is at
most $2\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2 +
8\|\mathbf{A} - \mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})\|_{\mathsf{F}}^2$. -/
theorem integrable_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : AEMeasurable X μ) (hΨ : HasLaw Ψ (gaussianMatrix m p) μ)
    (hXΨ : IndepFun X Ψ μ) (hlp : Fintype.card l + 2 ≤ Fintype.card p) (k : ℕ) :
    Integrable (fun ω => frobNorm (A - truncatedSVD (generalizedNystrom A (X ω) (Ψ ω)) k) ^ 2)
      μ := by
  have := hΨ.isProbabilityMeasure
  have hgn := integrable_frobNorm_sub_generalizedNystrom_sq_of_hasLaw_gaussianMatrix A hX hΨ hXΨ
    (ae_of_all _ fun ω => by have := Matrix.rank_le_card_width (A * X ω); omega)
  have hm : AEStronglyMeasurable
      (fun ω => frobNorm (A - truncatedSVD (generalizedNystrom A (X ω) (Ψ ω)) k) ^ 2) μ :=
    (((continuous_frobNorm.measurable.comp (measurable_const.sub
      ((measurable_truncatedSVD k).comp
        (measurable_generalizedNystrom A)))).pow_const 2).comp_aemeasurable
        (hX.prodMk hΨ.aemeasurable)).aestronglyMeasurable
  have hB : Integrable (fun ω => 8 * frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2 +
      2 * frobNorm (A - truncatedSVD A k) ^ 2) μ :=
    (hgn.const_mul 8).add (integrable_const _)
  refine hB.mono' hm (ae_of_all _ fun ω => ?_)
  have h := (isBestRankApprox_truncatedSVD (generalizedNystrom A (X ω) (Ψ ω)) k
    ).matrixNorm_sub_le_add_two_mul (lpGauge 2) A
  simp only [lpGauge_two_matrixNorm] at h
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have h2 := pow_le_pow_left₀ (frobNorm_nonneg _) h 2
  nlinarith [sq_nonneg (frobNorm (A - truncatedSVD A k) -
    2 * frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)))]

/-- **The expected error of truncated generalized Nyström**: for independent standard Gaussian
test matrices $\mathbf{\Omega}$ ($n \times \ell$) and $\mathbf{\Psi}$ ($m \times p$) with
$4k \le \ell$ and $4\ell \le p$, <!-- value truncatedGNFactor k \ell p -->
$$\mathbb{E}\|\mathbf{A}-\llbracket\mathsf{gn}(\mathbf{A}, \mathbf{\Omega},
\mathbf{\Psi})\rrbracket_k\|_{\mathsf{F}}^2 \le \Bigl(1 + \frac{k}{\ell - k - 1} +
4\sqrt{\frac{2k}{p}\Bigl(25\Bigl(1 + \frac{k}{\ell - k - 1}\Bigr) + 484\Bigr)} +
\frac{8k}{p}\Bigl(25\Bigl(1 + \frac{k}{\ell - k - 1}\Bigr) + 484\Bigr)\Bigr)
\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,,$$
that is, $g + 4\sqrt{2kc} + 8kc$ with
$g = 1 + k/(\ell - k - 1)$ and $c = (25g + 484)/p$.
Every rank of $\mathbf{A}$; the truncation is `truncatedSVD`, and the bound holds for every best
rank-$k$ approximation of the output. Proved without a literature source; inputs
[HalkoMartinssonTropp2011, Theorems 9.1, 10.5]; [TroppWebber2023, Lemmas B.1, B.3];
[HornJohnson2013, Theorem 7.4.1.1] (through the perturbed truncation lemma). Comparison points:
[TroppYurtseverUdellCevher2017, Corollary 6.4] (the constant-2 triangle bound, first moment, never
below $3\,\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}$); the Frobenius-noise
bound
`integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_sqrt_of_hasLaw_gaussianMatrix`
(relative error $1 + \varepsilon$ only at $p = O(k/\varepsilon^3)$, better constants below
$\ell \approx 10^3 k$); [CamanoEpperlyMeyerTropp2025, Remark 2.9] concerns a different,
core-truncated estimator and states no bound.
Result: tgn-expected-error -/
theorem integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ)
    (hΨ : HasLaw Ψ (gaussianMatrix m p) μ) (hXΨ : IndepFun X Ψ μ) {k : ℕ}
    (hkl : 4 * k ≤ Fintype.card l) (hlp : 4 * Fintype.card l ≤ Fintype.card p) :
    ∫ ω, frobNorm (A - truncatedSVD (generalizedNystrom A (X ω) (Ψ ω)) k) ^ 2 ∂μ ≤
      truncatedGNFactor k (Fintype.card l) (Fintype.card p) *
        frobNorm (A - truncatedSVD A k) ^ 2 := by
  have := hX.isProbabilityMeasure
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · subst hk0
    simp only [truncatedSVD_zero, sub_zero, integral_const, probReal_univ, one_smul]
    exact le_mul_of_one_le_left (sq_nonneg _) (one_le_truncatedGNFactor hkl)
  obtain ⟨he2i, he2⟩ := integral_specNorm_obliqueProjector_sub_rsvd_sq_le A hX hΨ hXΨ hk hkl hlp
  set O := frobNorm (A - truncatedSVD A k) with hOdef
  set g := gaussianProjectionFactor k (Fintype.card l) with hgdef
  set c := (25 * g + 484) / (Fintype.card p : ℝ) with hcdef
  have hk2 : k + 2 ≤ Fintype.card l := by omega
  have hc0 : 0 ≤ c := div_nonneg (by linarith [one_le_gaussianProjectionFactor hk2])
    (Nat.cast_nonneg _)
  have hO0 : 0 ≤ O := frobNorm_nonneg _
  have hem : AEStronglyMeasurable
      (fun ω => specNorm (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω)))) μ :=
    ((continuous_specNorm.measurable.comp
      (measurable_obliqueProjector_mul_sub_rsvd A)).comp_aemeasurable
        (hX.aemeasurable.prodMk hΨ.aemeasurable)).aestronglyMeasurable
  have heL := (memLp_two_iff_integrable_sq hem).2 he2i
  have hei := heL.integrable one_le_two
  have hE1 : ∫ ω, specNorm (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω))) ∂μ ≤
      √c * O := by
    refine (integral_le_sqrt_integral_sq heL).trans ?_
    rw [← Real.sqrt_sq hO0, ← Real.sqrt_mul hc0]
    exact Real.sqrt_le_sqrt he2
  have hlpw : Fintype.card l ≤ Fintype.card p := by omega
  have hJ := ae_rank_conjTranspose_mul_mul_eq A hX.aemeasurable hΨ hXΨ
    fun x => (Matrix.rank_le_card_width _).trans hlpw
  have hpt : ∀ᵐ ω ∂μ, frobNorm (A - truncatedSVD (generalizedNystrom A (X ω) (Ψ ω)) k) ^ 2 ≤
      frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 +
        4 * √(2 * (k : ℝ)) * O *
          specNorm (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω))) +
        8 * k * specNorm (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω))) ^ 2 := by
    filter_upwards [hJ] with ω hω
    have h := frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_specNorm hω k
    have h3 := frobNorm_sub_truncatedSVD_rsvd_sq A (X ω) k
    have hγ := frobNorm_rsvd_sub_truncatedSVD_le A (X ω) k
    have hs : √(2 * (k : ℝ)) ^ 2 = 2 * k := Real.sq_sqrt (by positivity)
    have he0 := specNorm_nonneg (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω)))
    have hγ' := mul_le_mul_of_nonneg_right hγ (mul_nonneg (Real.sqrt_nonneg (2 * (k : ℝ))) he0)
    nlinarith
  have hU := integrable_frobNorm_sub_truncatedSVD_rsvd_sq A hX.aemeasurable k
  have hR1 : Integrable (fun ω => frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 +
      4 * √(2 * (k : ℝ)) * O *
        specNorm (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω)))) μ :=
    hU.add (hei.const_mul _)
  have hRi : Integrable (fun ω => frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 +
      4 * √(2 * (k : ℝ)) * O *
        specNorm (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω))) +
      8 * k * specNorm (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω))) ^ 2) μ :=
    hR1.add (he2i.const_mul _)
  refine (integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _) hRi hpt).trans ?_
  rw [integral_add hR1 (he2i.const_mul _), integral_add hU (hei.const_mul _), integral_const_mul,
    integral_const_mul]
  have hU1 := integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_hasLaw_gaussianMatrix A hX hk2
  have hsq : √(2 * (k : ℝ) * c) = √(2 * (k : ℝ)) * √c := Real.sqrt_mul (by positivity) c
  have h4 : 0 ≤ 4 * √(2 * (k : ℝ)) * O :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hO0
  have e1 := mul_le_mul_of_nonneg_left hE1 h4
  have e2 := mul_le_mul_of_nonneg_left he2 (by positivity : (0 : ℝ) ≤ 8 * k)
  rw [truncatedGNFactor_def, ← hgdef, ← hcdef, hsq]
  nlinarith

-- A docstring line names a declaration whose name exceeds 100 characters.
set_option linter.style.longLine false in
/-- **Truncated generalized Nyström reaches relative error $1 + \varepsilon$** with
independent standard Gaussian test matrices of sizes $\ell \ge 6k/\varepsilon$ and
$p \ge 8000\,\ell/\varepsilon$, $0 < \varepsilon \le 1$:
$$\mathbb{E}\|\mathbf{A}-\llbracket\mathsf{gn}(\mathbf{A}, \mathbf{\Omega},
\mathbf{\Psi})\rrbracket_k\|_{\mathsf{F}}^2 \le (1 + \varepsilon)
\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,.$$
Asymptotic form:
`NLAlib.exists_forall_integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_of_hasLaw_gaussianMatrix`.
Proved without a literature source.
Result: tgn-expected-error -/
theorem
    integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_one_add_mul_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ)
    (hΨ : HasLaw Ψ (gaussianMatrix m p) μ) (hXΨ : IndepFun X Ψ μ) {k : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hl : 6 * (k : ℝ) ≤ ε * Fintype.card l)
    (hp : 8000 * (Fintype.card l : ℝ) ≤ ε * Fintype.card p) :
    ∫ ω, frobNorm (A - truncatedSVD (generalizedNystrom A (X ω) (Ψ ω)) k) ^ 2 ∂μ ≤
      (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  have hkl : 4 * k ≤ Fintype.card l := by
    have : 4 * (k : ℝ) ≤ Fintype.card l := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
    exact_mod_cast this
  have hlp : 4 * Fintype.card l ≤ Fintype.card p := by
    have : 4 * (Fintype.card l : ℝ) ≤ Fintype.card p := by
      nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card l),
        Nat.cast_nonneg (α := ℝ) (Fintype.card p)]
    exact_mod_cast this
  exact (integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_of_hasLaw_gaussianMatrix A hX
    hΨ hXΨ hkl hlp).trans (mul_le_mul_of_nonneg_right (truncatedGNFactor_le_one_add hε hε1 hl hp)
      (sq_nonneg _))

-- A docstring line names a declaration whose name exceeds 100 characters.
set_option linter.style.longLine false in
/-- **$O(k/\varepsilon)$ and $O(\ell/\varepsilon)$ samples suffice for truncated generalized
Nyström**: there are absolute constants $C, \varepsilon_0 > 0$ such that for independent standard
Gaussian test matrices $\mathbf{\Omega}$ ($n \times \ell$) and $\mathbf{\Psi}$ ($m \times p$),
$0 < \varepsilon \le \varepsilon_0$, $\ell \ge Ck/\varepsilon$ and $p \ge C\ell/\varepsilon$,
$$\mathbb{E}\|\mathbf{A}-\llbracket\mathsf{gn}(\mathbf{A}, \mathbf{\Omega},
\mathbf{\Psi})\rrbracket_k\|_{\mathsf{F}}^2 \le (1 + \varepsilon)
\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,.$$
The asymptotic form of
`NLAlib.integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_one_add_mul_of_hasLaw_gaussianMatrix`
through the factor's comparison at one shared $C$; the proof takes $C = 160$ and
$\varepsilon_0 = 1$, against the explicit theorem's $6$ and $8000$ for the two sizes.
Asymptotic:
NLAlib.integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_one_add_mul_of_hasLaw_gaussianMatrix
Result: tgn-expected-error -/
theorem
    exists_forall_integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l p : Type} [MeasurableSpace Ω] [Fintype m]
      [Fintype n] [Fintype l] [Fintype p] (μ : Measure Ω) (A : Matrix m n ℝ)
      (X : Ω → Matrix n l ℝ) (Ψ : Ω → Matrix m p ℝ) (k : ℕ) (ε : ℝ),
      HasLaw X (gaussianMatrix n l) μ → HasLaw Ψ (gaussianMatrix m p) μ → IndepFun X Ψ μ →
      0 < ε → ε ≤ ε₀ → C * ((k : ℝ) / ε) ≤ Fintype.card l →
      C * ((Fintype.card l : ℝ) / ε) ≤ Fintype.card p →
      ∫ ω, frobNorm (A - truncatedSVD (generalizedNystrom A (X ω) (Ψ ω)) k) ^ 2 ∂μ ≤
        (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  refine ⟨160, 1, by norm_num, one_pos, ?_⟩
  intro Ω m n l p _ _ _ _ _ μ A X Ψ k ε hX hΨ hXΨ hε hε1 hl hp
  rw [← mul_div_assoc, div_le_iff₀ hε] at hl hp
  have hl' : 160 * (k : ℝ) ≤ ε * Fintype.card l := by linarith
  have hp' : 160 * (Fintype.card l : ℝ) ≤ ε * Fintype.card p := by linarith
  have hkl : 4 * k ≤ Fintype.card l := by
    have : 4 * (k : ℝ) ≤ Fintype.card l := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
    exact_mod_cast this
  have hlp : 4 * Fintype.card l ≤ Fintype.card p := by
    have : 4 * (Fintype.card l : ℝ) ≤ Fintype.card p := by
      nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card l)]
    exact_mod_cast this
  exact (integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_of_hasLaw_gaussianMatrix A hX
    hΨ hXΨ hkl hlp).trans (mul_le_mul_of_nonneg_right
      (truncatedGNFactor_le_one_add_of_mul_le hε hε1 hl' hp') (sq_nonneg _))

/-- **Truncated generalized Nyström, Frobenius core-noise form**: for independent standard Gaussian
test matrices, $k + 2 \le \ell$ and $\ell + 2 \le p$, writing $h = \ell/(p - \ell - 1)$,
the bound is <!-- value gaussianProjectionFactor k \ell -->
$$\mathbb{E}\|\mathbf{A}-\llbracket\mathsf{gn}(\mathbf{A}, \mathbf{\Omega},
\mathbf{\Psi})\rrbracket_k\|_{\mathsf{F}}^2 \le \Bigl(1 + \frac{k}{\ell - k - 1} +
4\sqrt{h\Bigl(1 + \frac{k}{\ell - k - 1}\Bigr)} +
4h\Bigl(1 + \frac{k}{\ell - k - 1}\Bigr)\Bigr)
\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,.$$
Incomparable with
`NLAlib.integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_of_hasLaw_gaussianMatrix`:
milder size conditions and better constants at practical sizes (below $\ell \approx 10^3 k$), but
relative error $1 + \varepsilon$ only at $p = O(k/\varepsilon^3)$. Proved without a literature
source; [TroppYurtseverUdellCevher2017, Corollary 6.4] is the published first-moment bound of
this kind (constant 2, triangle inequality).
Result: tgn-expected-error -/
theorem
    integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_sqrt_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ)
    (hΨ : HasLaw Ψ (gaussianMatrix m p) μ) (hXΨ : IndepFun X Ψ μ) {k : ℕ}
    (hk : k + 2 ≤ Fintype.card l) (hlp : Fintype.card l + 2 ≤ Fintype.card p) :
    ∫ ω, frobNorm (A - truncatedSVD (generalizedNystrom A (X ω) (Ψ ω)) k) ^ 2 ∂μ ≤
      (gaussianProjectionFactor k (Fintype.card l) +
          4 * √((Fintype.card l : ℝ) / ((Fintype.card p : ℝ) - Fintype.card l - 1) *
            gaussianProjectionFactor k (Fintype.card l)) +
          4 * ((Fintype.card l : ℝ) / ((Fintype.card p : ℝ) - Fintype.card l - 1)) *
            gaussianProjectionFactor k (Fintype.card l)) *
        frobNorm (A - truncatedSVD A k) ^ 2 := by
  have := hX.isProbabilityMeasure
  obtain ⟨hN2i, hN2⟩ := integral_frobNorm_obliqueProjector_sub_rsvd_sq_le A hX.aemeasurable hΨ hXΨ
    hlp
  set O := frobNorm (A - truncatedSVD A k) with hOdef
  set g := gaussianProjectionFactor k (Fintype.card l) with hgdef
  set h := (Fintype.card l : ℝ) / ((Fintype.card p : ℝ) - Fintype.card l - 1) with hhdef
  have hlp' : (Fintype.card l : ℝ) + 2 ≤ Fintype.card p := by exact_mod_cast hlp
  have hh0 : 0 ≤ h := div_nonneg (Nat.cast_nonneg _) (by linarith)
  have hg1 : 1 ≤ g := one_le_gaussianProjectionFactor hk
  have hO0 : 0 ≤ O := frobNorm_nonneg _
  have hG2 := integral_frobNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix A hX hk
  have hN2' : ∫ ω, frobNorm (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω))) ^ 2 ∂μ ≤
      h * g * O ^ 2 := by
    rw [mul_assoc]
    exact hN2.trans (mul_le_mul_of_nonneg_left hG2 hh0)
  have hNm : AEStronglyMeasurable
      (fun ω => frobNorm (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω)))) μ :=
    ((continuous_frobNorm.measurable.comp
      (measurable_obliqueProjector_mul_sub_rsvd A)).comp_aemeasurable
        (hX.aemeasurable.prodMk hΨ.aemeasurable)).aestronglyMeasurable
  have hNL := (memLp_two_iff_integrable_sq hNm).2 hN2i
  have hNi := hNL.integrable one_le_two
  have hE1 : ∫ ω, frobNorm (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω))) ∂μ ≤
      √(h * g) * O := by
    refine (integral_le_sqrt_integral_sq hNL).trans ?_
    rw [← Real.sqrt_sq hO0, ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt hN2'
  have hlpw : Fintype.card l ≤ Fintype.card p := by omega
  have hJ := ae_rank_conjTranspose_mul_mul_eq A hX.aemeasurable hΨ hXΨ
    fun x => (Matrix.rank_le_card_width _).trans hlpw
  have hpt : ∀ᵐ ω ∂μ, frobNorm (A - truncatedSVD (generalizedNystrom A (X ω) (Ψ ω)) k) ^ 2 ≤
      frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 +
        4 * O * frobNorm (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω))) +
        4 * frobNorm (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω))) ^ 2 := by
    filter_upwards [hJ] with ω hω
    have h1 := frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_frobNorm_truncatedSVD hω k
    have h3 := frobNorm_sub_truncatedSVD_rsvd_sq A (X ω) k
    have hγ := frobNorm_rsvd_sub_truncatedSVD_le A (X ω) k
    have hT := frobNorm_truncatedSVD_le
      (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω))) (2 * k)
    have hγ0 := frobNorm_nonneg (rsvd A (X ω) - truncatedSVD (rsvd A (X ω)) k)
    have hT0 := frobNorm_nonneg
      (truncatedSVD (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω))) (2 * k))
    have hb := add_le_add hγ (mul_le_mul_of_nonneg_left hT (by norm_num : (0 : ℝ) ≤ 2))
    have hb2 := pow_le_pow_left₀ (add_nonneg hγ0 (by positivity)) hb 2
    nlinarith
  have hU := integrable_frobNorm_sub_truncatedSVD_rsvd_sq A hX.aemeasurable k
  have hR1 : Integrable (fun ω => frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 +
      4 * O * frobNorm (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω)))) μ :=
    hU.add (hNi.const_mul _)
  have hRi : Integrable (fun ω => frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 +
      4 * O * frobNorm (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω))) +
      4 * frobNorm (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω))) ^ 2) μ :=
    hR1.add (hN2i.const_mul _)
  refine (integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _) hRi hpt).trans ?_
  rw [integral_add hR1 (hN2i.const_mul _), integral_add hU (hNi.const_mul _), integral_const_mul,
    integral_const_mul]
  have hU1 := integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_hasLaw_gaussianMatrix A hX hk
  have e1 := mul_le_mul_of_nonneg_left hE1 (mul_nonneg (by norm_num) hO0 : 0 ≤ 4 * O)
  have e2 := mul_le_mul_of_nonneg_left hN2' (by norm_num : (0 : ℝ) ≤ 4)
  nlinarith

/-! ### The noise in the dominant subspace and the oracle truncation -/

section Oracle

/-- Almost surely $\|\mathbf{G}^{+}\mathbf{M}\|_{\mathsf{F}}^2 =
\operatorname{tr}(\mathbf{M}^{\mathsf{H}}(\mathbf{G}\mathbf{G}^{\mathsf{H}})^{-1}\mathbf{M})$ for a
standard Gaussian $r \times k$ matrix $\mathbf{G}$ with $\lvert r \rvert \le \lvert k \rvert$. -/
private theorem ae_frobNorm_pinv_mul_sq_eq_trace {r k a : Type*} [Fintype r] [Fintype k]
    [Fintype a] [DecidableEq r] {Y : Ω → Matrix r k ℝ} (hY : HasLaw Y (gaussianMatrix r k) μ)
    (hrk : Fintype.card r ≤ Fintype.card k) (M : Matrix r a ℝ) :
    ∀ᵐ ω ∂μ, frobNorm (pinv (Y ω) * M) ^ 2 = (Mᴴ * (Y ω * (Y ω)ᴴ)⁻¹ * M).trace := by
  filter_upwards [ae_rank_eq_min_of_hasLaw_gaussianMatrix hY] with ω hω
  have hu : IsUnit (Y ω * (Y ω)ᴴ) := by
    have h := (isUnit_conjTranspose_mul_self_iff_rank (A := (Y ω)ᴴ)).2
      (by rw [Matrix.rank_conjTranspose, hω, min_eq_left hrk])
    rwa [Matrix.conjTranspose_conjTranspose] at h
  rw [frobNorm_sq_eq_re_trace, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ M,
    ← pinv_mul_conjTranspose_self, pinv_of_isUnit hu, ← Matrix.mul_assoc, RCLike.re_to_real]

open scoped Matrix.Norms.L2Operator in
/-- The weighted inverse moment: $\mathbb{E}\|\mathbf{G}^{+}\mathbf{M}\|_{\mathsf{F}}^2 =
\|\mathbf{M}\|_{\mathsf{F}}^2/(\lvert k \rvert - \lvert r \rvert - 1)$, with integrability. -/
private theorem integral_frobNorm_pinv_mul_sq {r k a : Type*} [Fintype r] [Fintype k]
    [Fintype a] {Y : Ω → Matrix r k ℝ} (hY : HasLaw Y (gaussianMatrix r k) μ)
    (hrk : Fintype.card r + 2 ≤ Fintype.card k) (M : Matrix r a ℝ) :
    Integrable (fun ω => frobNorm (pinv (Y ω) * M) ^ 2) μ ∧
      ∫ ω, frobNorm (pinv (Y ω) * M) ^ 2 ∂μ =
        frobNorm M ^ 2 / ((Fintype.card k : ℝ) - Fintype.card r - 1) := by
  classical
  have := hY.isProbabilityMeasure
  have hZ := integrable_mul_conjTranspose_inv_of_hasLaw_gaussianMatrix hY hrk
  have hZ' := Matrix.integrable_iff.1 hZ
  have hMZ : Integrable (fun ω => Mᴴ * (Y ω * (Y ω)ᴴ)⁻¹ * M) μ := by
    refine Matrix.integrable_iff.2 fun i j => ?_
    simp only [Matrix.mul_apply]
    exact integrable_finsetSum _ fun b _ => (integrable_finsetSum _ fun c _ =>
      (hZ' c b).const_mul _).mul_const _
  have htr : Integrable (fun ω => (Mᴴ * (Y ω * (Y ω)ᴴ)⁻¹ * M).trace) μ :=
    integrable_finsetSum _ fun i _ => Matrix.integrable_iff.1 hMZ i i
  have hae := ae_frobNorm_pinv_mul_sq_eq_trace hY (by omega) M
  refine ⟨htr.congr (hae.mono fun _ h => h.symm), ?_⟩
  rw [integral_congr_ae hae, Matrix.integral_trace hMZ, Matrix.integral_mul_const
    (Matrix.integrable_iff.2 fun i j => by
      simp only [Matrix.mul_apply]
      exact integrable_finsetSum _ fun c _ => (hZ' c j).const_mul _) M,
    Matrix.integral_const_mul _ hZ,
    integral_mul_conjTranspose_inv_of_hasLaw_gaussianMatrix hY hrk, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, frobNorm_sq_eq_re_trace, RCLike.re_to_real,
    div_eq_inv_mul]

/-- The Gaussian block with a left factor, conjugate-transposed. -/
private theorem frobNorm_mul_pinv_mul_mul_eq {r s c a : Type*} [Fintype r] [Fintype s]
    [Fintype c] [Fintype a] (G : Matrix m p ℝ) (V₁ : Matrix m r ℝ) (V₂ : Matrix m s ℝ)
    (T : Matrix c r ℝ) (W : Matrix s a ℝ) :
    frobNorm (T * pinv (Gᴴ * V₁) * (Gᴴ * V₂) * W) =
      frobNorm (Wᴴ * (V₂ᴴ * G) * (pinv (V₁ᴴ * G) * Tᴴ)) := by
  rw [← frobNorm_conjTranspose]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, ← pinv_conjTranspose,
    Matrix.mul_assoc]

/-- The Gaussian block with a fixed left factor: for frames $\mathbf{V}_1$, $\mathbf{V}_2$ with
$\mathbf{V}_1^{\mathsf{H}}\mathbf{V}_2 = \mathbf{0}$,
$\mathbb{E}\|\mathbf{T}(\mathbf{G}^{\mathsf{H}}\mathbf{V}_1)^{+}
(\mathbf{G}^{\mathsf{H}}\mathbf{V}_2)\mathbf{W}\|_{\mathsf{F}}^2 =
\|\mathbf{T}\|_{\mathsf{F}}^2\|\mathbf{W}\|_{\mathsf{F}}^2/(\lvert p \rvert - \lvert r \rvert - 1)$,
with integrability. -/
private theorem integral_frobNorm_mul_pinv_mul_mul_sq {r s c a : Type*} [Fintype r] [Fintype s]
    [Fintype c] [Fintype a] [DecidableEq r] [DecidableEq s] {G : Ω → Matrix m p ℝ}
    (hG : HasLaw G (gaussianMatrix m p) μ) {V₁ : Matrix m r ℝ} {V₂ : Matrix m s ℝ}
    (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂) (h₁₂ : V₁ᴴ * V₂ = 0)
    (hrk : Fintype.card r + 2 ≤ Fintype.card p) (T : Matrix c r ℝ) (W : Matrix s a ℝ) :
    Integrable (fun ω => frobNorm (T * pinv ((G ω)ᴴ * V₁) * ((G ω)ᴴ * V₂) * W) ^ 2) μ ∧
      ∫ ω, frobNorm (T * pinv ((G ω)ᴴ * V₁) * ((G ω)ᴴ * V₂) * W) ^ 2 ∂μ =
        frobNorm W ^ 2 * (frobNorm T ^ 2 / ((Fintype.card p : ℝ) - Fintype.card r - 1)) := by
  simp only [frobNorm_mul_pinv_mul_mul_eq]
  have hY := hasLaw_conjTranspose_mul_of_hasLaw_gaussianMatrix hG hV₁
  have hX := hasLaw_conjTranspose_mul_of_hasLaw_gaussianMatrix hG hV₂
  have hI := indepFun_conjTranspose_mul_of_hasLaw_gaussianMatrix hG hV₁ hV₂ h₁₂
  have hT : Measurable fun y : Matrix r p ℝ => pinv y * Tᴴ := measurable_pinv.matrix_mul
    measurable_const
  obtain ⟨hint, hval⟩ := integral_frobNorm_pinv_mul_sq hY hrk Tᴴ
  refine ⟨(integrable_frobNorm_mul_mul_sq_iff_of_hasLaw_gaussianMatrix_of_indepFun hX
    hY.aemeasurable hI (S := fun _ => Wᴴ) measurable_const hT).2 (hint.const_mul _), ?_⟩
  rw [integral_frobNorm_mul_mul_sq_of_hasLaw_gaussianMatrix_of_indepFun hX hY.aemeasurable hI
    (S := fun _ => Wᴴ) measurable_const hT, integral_const_mul, hval, frobNorm_conjTranspose,
    frobNorm_conjTranspose]

/-- Fixed range test matrix: for $\mathbf{F}$ with
$\mathbf{F}\mathbf{P}_{\mathbf{A}\mathbf{\Omega}} = \mathbf{F}$ and
$q = \operatorname{rank}(\mathbf{A}\mathbf{\Omega})$, $q + 2 \le p$,
$\mathbb{E}_{\mathbf{\Psi}}\|\mathbf{F}\mathbf{N}\|_{\mathsf{F}}^2 =
\|\mathbf{F}\|_{\mathsf{F}}^2/(p - q - 1) \cdot \|\mathbf{A} - \mathbf{R}\|_{\mathsf{F}}^2$,
with integrability. -/
private theorem integral_frobNorm_mul_obliqueProjector_sq_of_fixed {c : Type*} [Fintype c]
    (A : Matrix m n ℝ) (X₀ : Matrix n l ℝ) (hΨ : HasLaw Ψ (gaussianMatrix m p) μ)
    (hr : (A * X₀).rank + 2 ≤ Fintype.card p) (F : Matrix c m ℝ)
    (hF : F * rangeProjector (A * X₀) = F) :
    Integrable (fun ω => frobNorm (F * (obliqueProjector (A * X₀) (Ψ ω)ᴴ *
      (A - rsvd A X₀))) ^ 2) μ ∧
      ∫ ω, frobNorm (F * (obliqueProjector (A * X₀) (Ψ ω)ᴴ * (A - rsvd A X₀))) ^ 2 ∂μ =
        frobNorm F ^ 2 / ((Fintype.card p : ℝ) - (A * X₀).rank - 1) *
          frobNorm (A - rsvd A X₀) ^ 2 := by
  classical
  obtain ⟨Q₁, Q₂, hQ₁, hQ₂, h₁₂, hR₁, hE⟩ := exists_hasOrthonormalCols_frames_range_compl (A * X₀) A
  have hrk : Fintype.card (Fin (A * X₀).rank) + 2 ≤ Fintype.card p := by rwa [Fintype.card_fin]
  obtain ⟨hint, hval⟩ := integral_frobNorm_mul_pinv_mul_mul_sq hΨ hQ₁ hQ₂ h₁₂ hrk (F * Q₁)
    (Q₂ᴴ * ((1 - rangeProjector (A * X₀)) * A))
  have hae : ∀ᵐ ω ∂μ, frobNorm (F * (obliqueProjector (A * X₀) (Ψ ω)ᴴ *
      (A - rsvd A X₀))) ^ 2 = frobNorm (F * Q₁ * pinv ((Ψ ω)ᴴ * Q₁) * ((Ψ ω)ᴴ * Q₂) *
        (Q₂ᴴ * ((1 - rangeProjector (A * X₀)) * A))) ^ 2 := by
    filter_upwards [ae_rank_conjTranspose_mul_eq_of_hasLaw_gaussianMatrix (A * X₀) hΨ
      (by omega)] with ω hω
    rw [sub_rsvd, obliqueProjector_eq_of_range_eq hω hR₁.symm, obliqueProjector]
    conv_lhs => rw [← hE]
    simp only [Matrix.mul_assoc]
  have hFQ : frobNorm (F * Q₁) = frobNorm F := by
    rw [← frobNorm_conjTranspose, ← hQ₁.frobNorm_mul_left, ← frobNorm_conjTranspose,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
      ← hQ₁.rangeProjector_eq, rangeProjector_inj.mpr hR₁, hF]
  have hW : frobNorm (Q₂ᴴ * ((1 - rangeProjector (A * X₀)) * A)) = frobNorm (A - rsvd A X₀) := by
    rw [← hQ₂.frobNorm_mul_left, hE, sub_rsvd]
  refine ⟨hint.congr (hae.mono fun _ h => h.symm), ?_⟩
  rw [integral_congr_ae hae, hval, hFQ, hW, Fintype.card_fin]
  ring

/-- The squared core noise in the dominant subspace is measurable in the pair. -/
private theorem measurable_frobNorm_rangeProjector_mul_obliqueProjector_sq (A : Matrix m n ℝ)
    (k : ℕ) : Measurable fun q : Matrix n l ℝ × Matrix m p ℝ =>
      frobNorm (rangeProjector (truncatedSVD (rsvd A q.1) k) *
        (obliqueProjector (A * q.1) q.2ᴴ * (A - rsvd A q.1))) ^ 2 :=
  (continuous_frobNorm.measurable.comp ((measurable_rangeProjector.comp
    (((measurable_truncatedSVD k).comp (measurable_rsvd A)).comp measurable_fst)).matrix_mul
      (measurable_obliqueProjector_mul_sub_rsvd A))).pow_const 2

/-- The rank of the truncated randomized SVD is $k$ once the sketch has rank $\ge k$. -/
private theorem rank_truncatedSVD_rsvd (A : Matrix m n ℝ) (x : Matrix n l ℝ) {k : ℕ}
    (hk : k ≤ (A * x).rank) : (truncatedSVD (rsvd A x) k).rank = k := by
  classical
  have h : (A * x).rank ≤ (rsvd A x).rank := by
    have := Matrix.rank_mul_le_left (rsvd A x) x
    rwa [rsvd, Matrix.mul_assoc, rangeProjector_mul_self] at this
  rw [rank_truncatedSVD, min_eq_left (hk.trans h)]

/-- The core noise in the dominant subspace: for independent standard Gaussian test
matrices $\mathbf{\Omega}$ ($n \times \ell$) and $\mathbf{\Psi}$ ($m \times p$), $k \le \ell$,
$\ell + 2 \le p$, $\mathbf{R} = \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})$ and
$\mathbf{N} = \mathbf{\Pi}_{\mathbf{A}\mathbf{\Omega},\mathbf{\Psi}^{\mathsf{H}}}(\mathbf{A} -
\mathbf{R})$,
$$\mathbb{E}\|\mathbf{P}_{\llbracket\mathbf{R}\rrbracket_k}\mathbf{N}\|_{\mathsf{F}}^2 =
\frac{k}{p - \ell - 1}\,\mathbb{E}\|\mathbf{A} - \mathbf{R}\|_{\mathsf{F}}^2\,.$$
Every rank of $\mathbf{A}$: if $\operatorname{rank}\mathbf{A} < \ell$ both sides vanish
($\mathbf{R} = \mathbf{A}$ almost surely). For the choice `truncatedSVD` makes.
No printed source. New (research note OP2, §3, I2). -/
theorem integral_frobNorm_rangeProjector_mul_obliqueProjector_sq_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ)
    (hΨ : HasLaw Ψ (gaussianMatrix m p) μ) (hXΨ : IndepFun X Ψ μ) {k : ℕ}
    (hkl : k ≤ Fintype.card l) (hlp : Fintype.card l + 2 ≤ Fintype.card p) :
    ∫ ω, frobNorm (rangeProjector (truncatedSVD (rsvd A (X ω)) k) *
        (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω)))) ^ 2 ∂μ =
      k / ((Fintype.card p : ℝ) - Fintype.card l - 1) *
        ∫ ω, frobNorm (A - rsvd A (X ω)) ^ 2 ∂μ := by
  classical
  have := hΨ.isProbabilityMeasure
  rcases lt_or_ge A.rank (Fintype.card l) with hA | hA
  · have h0 := ae_rsvd_eq_self_of_hasLaw_gaussianMatrix A hX hA.le
    rw [integral_eq_zero_of_ae (h0.mono fun ω h => by
        simp only [h, sub_self, Matrix.mul_zero, frobNorm_zero, Pi.zero_apply]; norm_num),
      integral_eq_zero_of_ae (h0.mono fun ω h => by
        simp only [h, sub_self, frobNorm_zero, Pi.zero_apply]; norm_num), mul_zero]
  have hrk : ∀ᵐ ω ∂μ, (A * X ω).rank = Fintype.card l :=
    (ae_rank_mul_eq_min_of_hasLaw_gaussianMatrix A hX).mono fun ω h => by rw [h, min_eq_right hA]
  have hF (x : Matrix n l ℝ) : rangeProjector (truncatedSVD (rsvd A x) k) *
      rangeProjector (A * x) = rangeProjector (truncatedSVD (rsvd A x) k) :=
    rangeProjector_mul_rangeProjector_of_range_le'
      ((range_truncatedSVD_le _ k).trans (range_rsvd_le A x))
  have hid : HasLaw (fun ψ : Matrix m p ℝ => ψ) (gaussianMatrix m p) (gaussianMatrix m p) :=
    HasLaw.id
  have hc : 0 ≤ (k : ℝ) / ((Fintype.card p : ℝ) - Fintype.card l - 1) := by
    have : (Fintype.card l : ℝ) + 2 ≤ Fintype.card p := by exact_mod_cast hlp
    exact div_nonneg (Nat.cast_nonneg k) (by linarith)
  have hm := measurable_frobNorm_rangeProjector_mul_obliqueProjector_sq A k (l := l) (p := p)
  rw [← integral_const_mul, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => sq_nonneg _)
      (hm.comp_aemeasurable (hX.aemeasurable.prodMk hΨ.aemeasurable)).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => mul_nonneg hc (sq_nonneg _))
      ((integrable_frobNorm_sub_rsvd_sq A hX.aemeasurable).const_mul _).aestronglyMeasurable]
  congr 1
  refine (hXΨ.lintegral_ofReal_comp_eq_lintegral_ofReal_integral hX.aemeasurable hΨ hm
    (fun _ => sq_nonneg _) (hrk.mono fun ω hω =>
      (integral_frobNorm_mul_obliqueProjector_sq_of_fixed A (X ω) hid (by omega) _
        (hF (X ω))).1)).trans (lintegral_congr_ae (hrk.mono fun ω hω => ?_))
  dsimp only
  rw [(integral_frobNorm_mul_obliqueProjector_sq_of_fixed A (X ω) hid (by omega) _
    (hF (X ω))).2, frobNorm_rangeProjector_sq, rank_truncatedSVD_rsvd A (X ω) (by omega), hω]

/-- The oracle-truncated generalized Nyström error, exactly: for independent standard Gaussian
test matrices $\mathbf{\Omega}$ ($n \times \ell$) and $\mathbf{\Psi}$ ($m \times p$), $k \le \ell$,
$\ell + 2 \le p$, $\mathbf{R} = \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})$,
$\mathbf{N} = \mathbf{\Pi}_{\mathbf{A}\mathbf{\Omega},\mathbf{\Psi}^{\mathsf{H}}}(\mathbf{A} -
\mathbf{R})$
and the oracle truncation $\widehat{\mathbf{A}} = \llbracket\mathbf{R}\rrbracket_k +
\mathbf{P}_{\llbracket\mathbf{R}\rrbracket_k}\mathbf{N}$ (truncation in the dominant subspace of
$\mathbf{R}$ instead of that of $\mathsf{gn}$; not computable from the sketches),
$$\mathbb{E}\|\mathbf{A} - \widehat{\mathbf{A}}\|_{\mathsf{F}}^2 =
\mathbb{E}\|\mathbf{A} - \llbracket\mathbf{R}\rrbracket_k\|_{\mathsf{F}}^2 +
\frac{k}{p - \ell - 1}\,\mathbb{E}\|\mathbf{A} - \mathbf{R}\|_{\mathsf{F}}^2\,.$$
The noise costs $k/(p - \ell - 1)$, not $\ell/(p - \ell - 1)$: what truncated generalized Nyström
loses beyond this is the misalignment of its truncation subspace.
No printed source. New (research note OP2, §3, I3). -/
theorem integral_frobNorm_sub_truncatedSVD_rsvd_sub_rangeProjector_sq_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ)
    (hΨ : HasLaw Ψ (gaussianMatrix m p) μ) (hXΨ : IndepFun X Ψ μ) {k : ℕ}
    (hkl : k ≤ Fintype.card l) (hlp : Fintype.card l + 2 ≤ Fintype.card p) :
    ∫ ω, frobNorm (A - truncatedSVD (rsvd A (X ω)) k -
        rangeProjector (truncatedSVD (rsvd A (X ω)) k) *
          (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω)))) ^ 2 ∂μ =
      ∫ ω, frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 ∂μ +
        k / ((Fintype.card p : ℝ) - Fintype.card l - 1) *
          ∫ ω, frobNorm (A - rsvd A (X ω)) ^ 2 ∂μ := by
  classical
  have := hΨ.isProbabilityMeasure
  have hpt (ω : Ω) : frobNorm (A - truncatedSVD (rsvd A (X ω)) k -
      rangeProjector (truncatedSVD (rsvd A (X ω)) k) *
        (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω)))) ^ 2 =
      frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 +
        frobNorm (rangeProjector (truncatedSVD (rsvd A (X ω)) k) *
          (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω)))) ^ 2 := by
    refine frobNorm_sub_sq_of_frobInner_eq_zero ?_
    -- the cross term vanishes pointwise: `P (A - T) = P A - T = 0` with `T = P A`
    rw [frobInner_comm, frobInner_mul_left, conjTranspose_rangeProjector,
      Matrix.mul_sub (rangeProjector _), rangeProjector_mul_self,
      ← truncatedSVD_rsvd_eq_rangeProjector_mul, sub_self, frobInner_zero_right]
  have hT := (measurable_truncatedSVD k).comp (measurable_rsvd (l := l) A)
  have hf := integrable_frobNorm_sub_truncatedSVD_rsvd_sq A hX.aemeasurable k
  have hN := measurable_obliqueProjector_mul_sub_rsvd (l := l) (p := p) A
  have hgn := integrable_frobNorm_sub_generalizedNystrom_sq_of_hasLaw_gaussianMatrix A
    hX.aemeasurable hΨ hXΨ
    (ae_of_all _ fun ω => by have := Matrix.rank_le_card_width (A * X ω); omega)
  have hg : Integrable (fun ω => frobNorm (rangeProjector (truncatedSVD (rsvd A (X ω)) k) *
      (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω)))) ^ 2) μ := by
    refine hgn.mono' (((continuous_frobNorm.measurable.comp
      ((measurable_rangeProjector.comp (hT.comp measurable_fst)).matrix_mul hN)).pow_const
        2).comp_aemeasurable (hX.aemeasurable.prodMk hΨ.aemeasurable)).aestronglyMeasurable ?_
    filter_upwards [ae_rank_conjTranspose_mul_mul_eq A hX.aemeasurable hΨ hXΨ
      (fun x => by have := Matrix.rank_le_card_width (A * x); omega)] with ω hω
    rw [Real.norm_of_nonneg (sq_nonneg _), frobNorm_sub_generalizedNystrom_sq hω]
    have h := (isStarProjection_rangeProjector (truncatedSVD (rsvd A (X ω)) k)).frobNorm_mul_le
      (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω)))
    nlinarith [frobNorm_nonneg (rangeProjector (truncatedSVD (rsvd A (X ω)) k) *
      (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω)))),
      sq_nonneg (frobNorm (A - rsvd A (X ω)))]
  rw [← integral_frobNorm_rangeProjector_mul_obliqueProjector_sq_of_hasLaw_gaussianMatrix A hX hΨ
    hXΨ hkl hlp, ← integral_add hf hg]
  exact integral_congr_ae (ae_of_all _ hpt)

/-- The expected error of the oracle truncation: for
independent standard Gaussian test matrices $\mathbf{\Omega}$ ($n \times \ell$) and
$\mathbf{\Psi}$ ($m \times p$), $k + 2 \le \ell$, $\ell + 2 \le p$,
$\mathbf{R} = \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})$,
$\mathbf{N} = \mathbf{\Pi}_{\mathbf{A}\mathbf{\Omega},\mathbf{\Psi}^{\mathsf{H}}}(\mathbf{A} -
\mathbf{R})$
and $\widehat{\mathbf{A}} = \llbracket\mathbf{R}\rrbracket_k +
\mathbf{P}_{\llbracket\mathbf{R}\rrbracket_k}\mathbf{N}$,
so <!-- value gaussianProjectionFactor k \ell -->
$$\mathbb{E}\|\mathbf{A} - \widehat{\mathbf{A}}\|_{\mathsf{F}}^2 \le
\Bigl(1 + \frac{k}{\ell - k - 1}\Bigr)\Bigl(1 + \frac{k}{p - \ell - 1}\Bigr)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,.$$
A statement about an analysis device, not an algorithm: the dominant subspace of $\mathbf{R}$
is not available from the two sketches, so this says nothing about what an estimator built from
them can reach. It separates the two losses of truncated generalized Nyström: the noise in a
fixed rank-$k$ subspace costs $k/(p - \ell - 1)$; the rest is the misalignment of the data-driven
truncation subspace (design note §3.2).
No printed source. New (research note OP2, §3, I3). -/
theorem integral_frobNorm_sub_truncatedSVD_rsvd_sub_rangeProjector_sq_le_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ)
    (hΨ : HasLaw Ψ (gaussianMatrix m p) μ) (hXΨ : IndepFun X Ψ μ) {k : ℕ}
    (hkl : k + 2 ≤ Fintype.card l) (hlp : Fintype.card l + 2 ≤ Fintype.card p) :
    ∫ ω, frobNorm (A - truncatedSVD (rsvd A (X ω)) k -
        rangeProjector (truncatedSVD (rsvd A (X ω)) k) *
          (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω)))) ^ 2 ∂μ ≤
      gaussianProjectionFactor k (Fintype.card l) *
        (1 + k / ((Fintype.card p : ℝ) - Fintype.card l - 1)) *
          frobNorm (A - truncatedSVD A k) ^ 2 := by
  have := hX.isProbabilityMeasure
  have hc : 0 ≤ (k : ℝ) / ((Fintype.card p : ℝ) - Fintype.card l - 1) := by
    apply div_nonneg (Nat.cast_nonneg _)
    have : (Fintype.card l : ℝ) + 2 ≤ Fintype.card p := by exact_mod_cast hlp
    linarith
  have hI := integral_frobNorm_sub_truncatedSVD_rsvd_sub_rangeProjector_sq_of_hasLaw_gaussianMatrix
    A hX hΨ hXΨ (k := k) (by omega) hlp
  have hmono : ∫ ω, frobNorm (A - rsvd A (X ω)) ^ 2 ∂μ ≤
      ∫ ω, frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 ∂μ :=
    integral_mono (integrable_frobNorm_sub_rsvd_sq A hX.aemeasurable)
      (integrable_frobNorm_sub_truncatedSVD_rsvd_sq A hX.aemeasurable k) fun ω => by
        rw [frobNorm_sub_truncatedSVD_rsvd_sq]
        exact le_add_of_nonneg_right (sq_nonneg _)
  have h2 := integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_hasLaw_gaussianMatrix A hX (k := k)
    (by omega)
  have h3 := mul_le_mul_of_nonneg_left hmono hc
  have h4 := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 1 + k / ((Fintype.card p : ℝ) -
    Fintype.card l - 1))
  rw [hI]
  nlinarith [h3, h4]

end Oracle

end NLAlib
