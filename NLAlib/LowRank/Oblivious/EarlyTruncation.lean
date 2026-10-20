/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Oblivious.RangeFinder
public import NLAlib.LowRank.Structural.EarlyTruncation

/-!
# Early truncation with oblivious subspace injections and approximate multiplication

Tail bounds for the early-truncated randomized SVD
$\mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)$ and early-truncated generalized
Nyström $\mathsf{earlyTruncatedGN}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi}, k)$ from sketch
properties: a head injection of $\mathbf{\Omega}^{\mathsf{H}}$ and two approximate-multiplication
tails, tail–tail
$\|\mathbf{E}\mathbf{\Omega}\mathbf{\Omega}^{\mathsf{H}}\mathbf{E}^{\mathsf{H}} -
\mathbf{E}\mathbf{E}^{\mathsf{H}}\|_{\mathsf{F}}$ and tail–head
$\|\mathbf{E}\mathbf{\Omega}\mathbf{\Omega}^{\mathsf{H}}
\mathbf{P}_{\llbracket\mathbf{A}\rrbracket_k^{\mathsf{H}}}\|_{\mathsf{F}}$, with
$\mathbf{E} = \mathbf{A} - \llbracket\mathbf{A}\rrbracket_k$, on the range side; an OSI
independent of $\mathbf{\Omega}$ on the co-range side.

**Any optimal projector.** The core tail is stated for every random orthogonal projector
$\mathbf{P}$ of rank at most $k$ that is at least as good on the sketch as the head,
$\|\mathbf{A}\mathbf{\Omega} - \mathbf{P}\mathbf{A}\mathbf{\Omega}\|_{\mathsf{F}} \le
\|\mathbf{E}\mathbf{\Omega}\|_{\mathsf{F}}$ (the projector form of the deterministic core
`NLAlib.IsSubspaceInjection.frobNorm_sub_mul_sq_le`). The projector of
$\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k$ is one, and so is the projector of the output at
the raw test matrix when a family's analysis runs at a rescaled one: a family statement concludes
about the output the user computes without identifying outputs under ties.

**Through a projection-cost-preserving sketch.** The last section states the same outputs for a
sketch known only to satisfy `NLAlib.HasProjectionCostPreserving`, the tail form of the
deterministic `NLAlib.IsProjectionCostPreserving.mul_frobNorm_sub_earlyTruncatedRSVD_sq_le`. For a
sketch of a known family the structural route above uses fewer events and gives better constants.
Design: `docs/design/LowRank-S7.md` §3.4, §8 items 1 and 18; `docs/design/LowRank-S9.md` §3.6.

## Main results

* `NLAlib.HasSubspaceInjection.measureReal_frobNorm_sub_mul_sq_gt_le`: the core tail, any optimal
  projector; `NLAlib.HasSubspaceInjection.measureReal_frobNorm_sub_mul_sq_gt_one_add_mul_le`, its
  $(1 + \varepsilon)$ form.
* `NLAlib.HasJLMoment.measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le`: the early-truncated
  randomized SVD from an injection and the JL moment property, with its tail–tail input, in
  `HasJLMoment`,
  `measureReal_frobNorm_sub_truncatedSVD_mul_mul_conjTranspose_mul_conjTranspose_sub_gt_le`.
* in `IsObliviousSubspaceInjection`,
  `measureReal_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_gt_mul_le`, and
  `NLAlib.HasJLMoment.measureReal_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_gt_mul_le`: the
  completion step, any law of $\mathbf{\Omega}$;
  `NLAlib.HasJLMoment.measureReal_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_gt_le`: both
  sides.
* `NLAlib.HasProjectionCostPreserving.measureReal_mul_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le`: the
  early-truncated randomized SVD through a random projection-cost-preserving sketch, and
  [generalized
  Nyström](https://nla-lib.org/explore/#d/NLAlib.HasProjectionCostPreserving.measureReal_mul_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_gt_le)
  through it and an OSI.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder ComplexOrder

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {m n l p : Type*} [Fintype m] [Fintype n] [Fintype l] [Fintype p] [DecidableEq m]
  [DecidableEq n] {X : Ω → Matrix n l 𝕜} {Ψ : Ω → Matrix m p 𝕜}

/-! ### The core tail, any optimal projector -/

omit [Fintype p] [DecidableEq m] [DecidableEq n] in
/-- **Early truncation from a head injection and approximate-multiplication tails, any optimal
projector**: if $\mathbf{\Omega}^{\mathsf{H}}$ injects
$\operatorname{range}\llbracket\mathbf{A}\rrbracket_k^{\mathsf{H}}$ with constant $0 < a \le 1$
except with probability $\delta$, the tail–tail error
$\|\mathbf{E}\mathbf{\Omega}\mathbf{\Omega}^{\mathsf{H}}\mathbf{E}^{\mathsf{H}} -
\mathbf{E}\mathbf{E}^{\mathsf{H}}\|_{\mathsf{F}}$ exceeds $\eta_w$ with probability at most
$\delta_w$ and the tail–head error $\|\mathbf{E}\mathbf{\Omega}\mathbf{\Omega}^{\mathsf{H}}
\mathbf{P}_{\llbracket\mathbf{A}\rrbracket_k^{\mathsf{H}}}\|_{\mathsf{F}}$ exceeds $\eta_\chi$ with
probability at most $\delta_\chi$, $\mathbf{E} = \mathbf{A} - \llbracket\mathbf{A}\rrbracket_k$,
then
for every random orthogonal projector $\mathbf{P}$ of rank at most $k$ with
$\|\mathbf{A}\mathbf{\Omega} - \mathbf{P}\mathbf{A}\mathbf{\Omega}\|_{\mathsf{F}} \le
\|\mathbf{E}\mathbf{\Omega}\|_{\mathsf{F}}$ and $0 < \theta < 1$,
$$\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{\mathsf{F}}^2 \le
\frac{\|\mathbf{E}\|_{\mathsf{F}}^2 + \sqrt{k}\,\eta_w}{(1-\theta)a} +
\frac{\eta_\chi^2}{\theta(1-\theta)a^2}$$
except with probability $\delta + \delta_w + \delta_\chi$. The projector of
$\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k$ qualifies (Eckart–Young), and so does the
projector of the output at $c^{-1}\mathbf{\Omega}$ when the analysis runs at $\mathbf{\Omega}$.
Proved without a literature source (the deterministic core of LowRank S2b); the sketch conditions
are those of [CohenElderMuscoMuscoPersu2015, proof of Theorem 12].
Result: etrsvd -/
theorem HasSubspaceInjection.measureReal_frobNorm_sub_mul_sq_gt_le [IsFiniteMeasure μ]
    {A : Matrix m n 𝕜} {k : ℕ} {a θ δ ηw δw ηχ δχ : ℝ}
    (h : HasSubspaceInjection (fun ω => (X ω)ᴴ) (truncatedSVD A k)ᴴ a δ μ) (ha : 0 < a)
    (ha1 : a ≤ 1) (hθ : 0 < θ) (hθ1 : θ < 1) {P : Ω → Matrix m m 𝕜}
    (hP : ∀ ω, IsStarProjection (P ω)) (hPk : ∀ ω, (P ω).rank ≤ k)
    (hopt : ∀ ω, frobNorm (A * X ω - P ω * (A * X ω)) ≤
      frobNorm ((A - truncatedSVD A k) * X ω))
    (hw : μ.real {ω | ηw < frobNorm ((A - truncatedSVD A k) * X ω * (X ω)ᴴ *
      (A - truncatedSVD A k)ᴴ - (A - truncatedSVD A k) * (A - truncatedSVD A k)ᴴ)} ≤ δw)
    (hχ : μ.real {ω | ηχ < frobNorm ((A - truncatedSVD A k) * X ω * (X ω)ᴴ *
      rangeProjector (truncatedSVD A k)ᴴ)} ≤ δχ) :
    μ.real {ω | (frobNorm (A - truncatedSVD A k) ^ 2 + √(k : ℝ) * ηw) / ((1 - θ) * a) +
        ηχ ^ 2 / (θ * (1 - θ) * a ^ 2) < frobNorm (A - P ω * A) ^ 2} ≤ δ + δw + δχ := by
  classical
  obtain ⟨Z, hZ, hR⟩ :=
    exists_hasOrthonormalCols_range_eq (truncatedSVD A k)ᴴ (Fintype.card_fin _)
  have hPZ : Z * Zᴴ = rangeProjector (truncatedSVD A k)ᴴ := by
    rw [← hZ.rangeProjector_eq, rangeProjector_inj, hR]
  have hAZ : A * Z * Zᴴ = truncatedSVD A k := by
    rw [Matrix.mul_assoc, hPZ, mul_rangeProjector_conjTranspose_truncatedSVD]
  have hEZ : (A - truncatedSVD A k) * Z = 0 := by
    have h0 : (A - A * Z * Zᴴ) * Z = 0 := by
      rw [Matrix.sub_mul, Matrix.mul_assoc (A * Z), show Zᴴ * Z = 1 from hZ, Matrix.mul_one,
        sub_self]
    rwa [hAZ] at h0
  unfold HasSubspaceInjection at h
  refine (measureReal_mono (s₂ := ({ω | ¬ IsSubspaceInjection (X ω)ᴴ (truncatedSVD A k)ᴴ a} ∪
    {ω | ηw < frobNorm ((A - truncatedSVD A k) * X ω * (X ω)ᴴ * (A - truncatedSVD A k)ᴴ -
      (A - truncatedSVD A k) * (A - truncatedSVD A k)ᴴ)}) ∪
    {ω | ηχ < frobNorm ((A - truncatedSVD A k) * X ω * (X ω)ᴴ *
      rangeProjector (truncatedSVD A k)ᴴ)}) fun ω hω => ?_).trans
    ((measureReal_union_le _ _).trans (add_le_add ((measureReal_union_le _ _).trans
      (add_le_add h hw)) hχ))
  by_contra hc
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not, not_lt] at hc
  obtain ⟨⟨hinj, hwω⟩, hχω⟩ := hc
  have hinjZ : IsSubspaceInjection (X ω)ᴴ Z a := hinj.of_range_le hR.le
  have hopt' : frobNorm (A * X ω - P ω * (A * X ω)) ≤ frobNorm ((A - A * Z * Zᴴ) * X ω) := by
    rw [hAZ]
    exact hopt ω
  have h1 := hinjZ.frobNorm_sub_mul_sq_le hZ ha ha1 hθ hθ1 (hP ω) (hPk ω) hopt'
  have e : frobNorm ((A - truncatedSVD A k) * X ω * (X ω)ᴴ * Z) =
      frobNorm ((A - truncatedSVD A k) * X ω * (X ω)ᴴ * rangeProjector (truncatedSVD A k)ᴴ) := by
    rw [← hPZ, ← Matrix.mul_assoc, hZ.frobNorm_mul_conjTranspose_right]
  rw [hAZ, hEZ, sub_zero, e] at h1
  have hω' : (frobNorm (A - truncatedSVD A k) ^ 2 + √(k : ℝ) * ηw) / ((1 - θ) * a) +
      ηχ ^ 2 / (θ * (1 - θ) * a ^ 2) < frobNorm (A - P ω * A) ^ 2 := hω
  have hd1 : 0 < (1 - θ) * a := mul_pos (by linarith) ha
  have h1θ : 0 < 1 - θ := by linarith
  have hd2 : 0 < θ * (1 - θ) * a ^ 2 := by positivity
  have hχ0 := frobNorm_nonneg ((A - truncatedSVD A k) * X ω * (X ω)ᴴ *
    rangeProjector (truncatedSVD A k)ᴴ)
  have h2 : (frobNorm (A - truncatedSVD A k) ^ 2 +
      √(k : ℝ) * frobNorm ((A - truncatedSVD A k) * X ω * (X ω)ᴴ * (A - truncatedSVD A k)ᴴ -
        (A - truncatedSVD A k) * (A - truncatedSVD A k)ᴴ)) / ((1 - θ) * a) ≤
      (frobNorm (A - truncatedSVD A k) ^ 2 + √(k : ℝ) * ηw) / ((1 - θ) * a) := by
    gcongr
  have h3 : frobNorm ((A - truncatedSVD A k) * X ω * (X ω)ᴴ *
      rangeProjector (truncatedSVD A k)ᴴ) ^ 2 / (θ * (1 - θ) * a ^ 2) ≤
      ηχ ^ 2 / (θ * (1 - θ) * a ^ 2) := by
    gcongr
  linarith

omit [Fintype p] [DecidableEq m] [DecidableEq n] in
/-- **Early truncation to relative error, any optimal projector**: with injection constant
$1 - \varepsilon/6$ and $0 < \varepsilon \le 1$, if the tail–tail error exceeds
$(\varepsilon/(6\sqrt{k}))\|\mathbf{E}\|_{\mathsf{F}}^2$ with probability at most $\delta_w$
and the tail–head error exceeds $(\varepsilon/6)\|\mathbf{E}\|_{\mathsf{F}}$ with probability
at most $\delta_\chi$, $\mathbf{E} = \mathbf{A} - \llbracket\mathbf{A}\rrbracket_k$, then for every
random orthogonal projector $\mathbf{P}$ of rank at most $k$ with
$\|\mathbf{A}\mathbf{\Omega} - \mathbf{P}\mathbf{A}\mathbf{\Omega}\|_{\mathsf{F}} \le
\|\mathbf{E}\mathbf{\Omega}\|_{\mathsf{F}}$
$$\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{\mathsf{F}}^2 \le (1 + \varepsilon)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta + \delta_w + \delta_\chi$: the core tail
`NLAlib.HasSubspaceInjection.measureReal_frobNorm_sub_mul_sq_gt_le` at
$\theta = \varepsilon/(6 + \varepsilon)$, the minimiser of its right side, which solves the
quadratic $\lambda s^2 \le c + 2\chi s$ of the structural bound exactly: with $x = \varepsilon/6$
it gives $((1 + x)/(1 - x))^2\|\mathbf{E}\|_{\mathsf{F}}^2$, at most
$(1 + \varepsilon)\|\mathbf{E}\|_{\mathsf{F}}^2$. The form every family statement instantiates.
Proved without a literature source; [CohenElderMuscoMuscoPersu2015, proof of Theorem 12] for the
sketch conditions.
Result: etrsvd -/
theorem HasSubspaceInjection.measureReal_frobNorm_sub_mul_sq_gt_one_add_mul_le [IsFiniteMeasure μ]
    {A : Matrix m n 𝕜} {k : ℕ} {ε δ δw δχ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (h : HasSubspaceInjection (fun ω => (X ω)ᴴ) (truncatedSVD A k)ᴴ (1 - ε / 6) δ μ)
    {P : Ω → Matrix m m 𝕜} (hP : ∀ ω, IsStarProjection (P ω)) (hPk : ∀ ω, (P ω).rank ≤ k)
    (hopt : ∀ ω, frobNorm (A * X ω - P ω * (A * X ω)) ≤
      frobNorm ((A - truncatedSVD A k) * X ω))
    (hw : μ.real {ω | ε / (6 * √(k : ℝ)) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm ((A - truncatedSVD A k) * X ω * (X ω)ᴴ * (A - truncatedSVD A k)ᴴ -
        (A - truncatedSVD A k) * (A - truncatedSVD A k)ᴴ)} ≤ δw)
    (hχ : μ.real {ω | ε / 6 * frobNorm (A - truncatedSVD A k) <
      frobNorm ((A - truncatedSVD A k) * X ω * (X ω)ᴴ *
        rangeProjector (truncatedSVD A k)ᴴ)} ≤ δχ) :
    μ.real {ω | (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - P ω * A) ^ 2} ≤ δ + δw + δχ := by
  classical
  have hx : 0 < ε / 6 := by positivity
  have h1x : 0 < 1 - ε / 6 := by linarith
  have hθ0 : 0 < ε / (6 + ε) := by positivity
  have hθ1 : ε / (6 + ε) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have h1 := h.measureReal_frobNorm_sub_mul_sq_gt_le h1x (by linarith) hθ0 hθ1 hP hPk hopt hw hχ
  refine (measureReal_mono fun ω hω => ?_).trans h1
  have hω' : (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 < frobNorm (A - P ω * A) ^ 2 := hω
  refine lt_of_le_of_lt ?_ hω'
  set y := frobNorm (A - truncatedSVD A k) ^ 2 with hy
  have hy0 : 0 ≤ y := sq_nonneg _
  have hs : √(k : ℝ) * (ε / (6 * √(k : ℝ)) * y) ≤ ε / 6 * y := by
    rcases eq_or_lt_of_le (Real.sqrt_nonneg (k : ℝ)) with h0 | h0
    · rw [← h0, zero_mul]
      positivity
    · rw [← mul_assoc, show √(k : ℝ) * (ε / (6 * √(k : ℝ))) = ε / 6 by field_simp]
  have h1θ : 1 - ε / (6 + ε) = 6 / (6 + ε) := by field_simp; ring
  have hd : 0 < (1 - ε / (6 + ε)) * (1 - ε / 6) := by rw [h1θ]; positivity
  have e1 : (y + √(k : ℝ) * (ε / (6 * √(k : ℝ)) * y)) / ((1 - ε / (6 + ε)) * (1 - ε / 6)) ≤
      (1 + ε / 6) * y / ((1 - ε / (6 + ε)) * (1 - ε / 6)) :=
    div_le_div_of_nonneg_right (by linarith) hd.le
  have e2 : (1 + ε / 6) * y / ((1 - ε / (6 + ε)) * (1 - ε / 6)) +
      (ε / 6 * frobNorm (A - truncatedSVD A k)) ^ 2 /
        (ε / (6 + ε) * (1 - ε / (6 + ε)) * (1 - ε / 6) ^ 2) =
      (6 + ε) ^ 2 / (6 - ε) ^ 2 * y := by
    rw [h1θ, mul_pow, ← hy]
    have : (6 : ℝ) - ε ≠ 0 := by linarith
    field_simp
    ring
  have hf : (6 + ε) ^ 2 / (6 - ε) ^ 2 ≤ 1 + ε := by
    rw [div_le_iff₀ (by nlinarith)]
    nlinarith [mul_nonneg hε.le (sub_nonneg.2 hε1), pow_pos hε 3]
  nlinarith [mul_le_mul_of_nonneg_right hf hy0]

/-! ### The early-truncated randomized SVD at the JL moment -/

section Real

variable {X : Ω → Matrix n l ℝ} {Ψ : Ω → Matrix m p ℝ}

-- A declaration name below is too long for a 100-character line.
set_option linter.style.longLine false in
omit [Fintype p] [DecidableEq m] [DecidableEq n] in
/-- **The tail–tail multiplication error from the JL moment property**: if the real sketch
$\mathbf{\Omega}^{\mathsf{H}}$ has the $(\varepsilon, \delta', q)$ JL moment property,
$\varepsilon > 0$, $q \ge 2$, $\delta' \ge 0$, then with
$\mathbf{E} = \mathbf{A} - \llbracket\mathbf{A}\rrbracket_k$
$$\|\mathbf{E}\mathbf{\Omega}\mathbf{\Omega}^{\mathsf{H}}\mathbf{E}^{\mathsf{H}} -
\mathbf{E}\mathbf{E}^{\mathsf{H}}\|_{\mathsf{F}} \le \varepsilon\|\mathbf{E}\|_{\mathsf{F}}^2$$
except with probability $\delta'$: approximate multiplication of $\mathbf{E}$ with itself. The
tail–tail hypothesis of `NLAlib.HasSubspaceInjection.measureReal_frobNorm_sub_mul_sq_gt_le` at the
JL moment; its tail–head twin is
`HasJLMoment.measureReal_frobNorm_sub_truncatedSVD_mul_mul_conjTranspose_mul_rangeProjector_gt_le`.
[Woodruff2014, Theorem 13]. -/
theorem
    HasJLMoment.measureReal_frobNorm_sub_truncatedSVD_mul_mul_conjTranspose_mul_conjTranspose_sub_gt_le
    [IsFiniteMeasure μ] {A : Matrix m n ℝ} {k : ℕ} {ε δ' q : ℝ}
    (hJL : HasJLMoment (fun ω => (X ω)ᴴ) ε δ' q μ) (hX : AEMeasurable X μ) (hε : 0 < ε)
    (hq : 2 ≤ q) (hδ' : 0 ≤ δ') :
    μ.real {ω | ε * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm ((A - truncatedSVD A k) * X ω * (X ω)ᴴ * (A - truncatedSVD A k)ᴴ -
        (A - truncatedSVD A k) * (A - truncatedSVD A k)ᴴ)} ≤ δ' := by
  classical
  have hS : AEMeasurable (fun ω => (X ω)ᴴ) μ :=
    continuous_id.matrix_conjTranspose.measurable.comp_aemeasurable hX
  by_cases h0 : A - truncatedSVD A k = 0
  · have he : {ω | ε * frobNorm (A - truncatedSVD A k) ^ 2 <
        frobNorm ((A - truncatedSVD A k) * X ω * (X ω)ᴴ * (A - truncatedSVD A k)ᴴ -
          (A - truncatedSVD A k) * (A - truncatedSVD A k)ᴴ)} = ∅ := by
      ext ω
      simp [h0]
    rw [he, measureReal_empty]
    exact hδ'
  have h0' : (A - truncatedSVD A k)ᴴ ≠ 0 := by rwa [Ne, Matrix.conjTranspose_eq_zero]
  refine (measureReal_mono fun ω hω => ?_).trans
    (hJL.measureReal_frobNorm_conjTranspose_mul_sub_ge_le hε hq hS h0' h0')
  have hω' : ε * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm ((A - truncatedSVD A k) * X ω * (X ω)ᴴ * (A - truncatedSVD A k)ᴴ -
        (A - truncatedSVD A k) * (A - truncatedSVD A k)ᴴ) := hω
  change ε * frobNorm (A - truncatedSVD A k)ᴴ * frobNorm (A - truncatedSVD A k)ᴴ ≤
    frobNorm ((A - truncatedSVD A k)ᴴᴴ * ((X ω)ᴴ)ᴴ * (X ω)ᴴ * (A - truncatedSVD A k)ᴴ -
      (A - truncatedSVD A k)ᴴᴴ * (A - truncatedSVD A k)ᴴ)
  rw [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose,
    frobNorm_conjTranspose, mul_assoc, ← sq]
  exact hω'.le

omit [Fintype p] [DecidableEq m] [DecidableEq n] in
/-- **The early-truncated randomized SVD from an injection and the JL moment property**: if the
real sketch $\mathbf{\Omega}^{\mathsf{H}}$ injects
$\operatorname{range}\llbracket\mathbf{A}\rrbracket_k^{\mathsf{H}}$ with constant $0 < a \le 1$
except with probability $\delta$ and has the $(\varepsilon, \delta', q)$ JL moment property,
$\varepsilon > 0$, $q \ge 2$, $\delta' \ge 0$, then for $0 < \theta < 1$
$$\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)\|_{\mathsf{F}}^2 \le
\Bigl(\frac{1 + \sqrt{k}\,\varepsilon}{(1-\theta)a} +
\frac{k\varepsilon^2}{\theta(1-\theta)a^2}\Bigr)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta + 2\delta'$; with $\varepsilon$ of order $\varepsilon_0/\sqrt{k}$
this is $1 + O(\varepsilon_0)$ at $\ell = O(k/(\varepsilon_0^2\delta'))$ for the dense families. Its
Gaussian expectation twin is
`NLAlib.integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_one_add_mul_of_hasLaw_gaussianMatrix`.
Proved without a literature source (the deterministic core of LowRank S2b);
[CohenElderMuscoMuscoPersu2015, Theorem 12 and Lemma 3]; [Woodruff2014, Theorem 61] is the
full-row-space form.
Result: etrsvd -/
theorem HasJLMoment.measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le [IsFiniteMeasure μ]
    {A : Matrix m n ℝ} {k : ℕ} {a θ δ ε δ' q : ℝ}
    (hJL : HasJLMoment (fun ω => (X ω)ᴴ) ε δ' q μ)
    (h : HasSubspaceInjection (fun ω => (X ω)ᴴ) (truncatedSVD A k)ᴴ a δ μ)
    (hX : AEMeasurable X μ) (ha : 0 < a) (ha1 : a ≤ 1) (hθ : 0 < θ) (hθ1 : θ < 1) (hε : 0 < ε)
    (hq : 2 ≤ q) (hδ' : 0 ≤ δ') :
    μ.real {ω | ((1 + √(k : ℝ) * ε) / ((1 - θ) * a) +
        (k : ℝ) * ε ^ 2 / (θ * (1 - θ) * a ^ 2)) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2} ≤ δ + 2 * δ' := by
  classical
  have hopt : ∀ ω, frobNorm (A * X ω - rangeProjector (truncatedSVD (A * X ω) k) * (A * X ω)) ≤
      frobNorm ((A - truncatedSVD A k) * X ω) := fun ω => by
    rw [rangeProjector_truncatedSVD_mul, Matrix.sub_mul]
    exact frobNorm_sub_truncatedSVD_le_of_rank_le (A * X ω)
      ((Matrix.rank_mul_le_left _ _).trans (rank_truncatedSVD_le A k))
  have h1 := h.measureReal_frobNorm_sub_mul_sq_gt_le ha ha1 hθ hθ1
    (fun ω => isStarProjection_rangeProjector (truncatedSVD (A * X ω) k))
    (fun ω => (rank_rangeProjector _).trans_le (rank_truncatedSVD_le _ k)) hopt
    (hJL.measureReal_frobNorm_sub_truncatedSVD_mul_mul_conjTranspose_mul_conjTranspose_sub_gt_le hX
      hε hq hδ')
    (hJL.measureReal_frobNorm_sub_truncatedSVD_mul_mul_conjTranspose_mul_rangeProjector_gt_le hX hε
      hq hδ')
  refine (measureReal_mono fun ω hω => ?_).trans (h1.trans_eq (by ring))
  have hω' : ((1 + √(k : ℝ) * ε) / ((1 - θ) * a) +
      (k : ℝ) * ε ^ 2 / (θ * (1 - θ) * a ^ 2)) * frobNorm (A - truncatedSVD A k) ^ 2 <
        frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 := hω
  rw [sub_earlyTruncatedRSVD, Matrix.sub_mul, Matrix.one_mul] at hω'
  change _ < frobNorm (A - rangeProjector (truncatedSVD (A * X ω) k) * A) ^ 2
  refine lt_of_eq_of_lt ?_ hω'
  rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg k)]
  field_simp

end Real

/-! ### Early-truncated generalized Nyström -/

omit [DecidableEq n] [DecidableEq m] in
/-- The completion error is the sketch-and-solve error with the design
$\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k$. -/
private theorem sub_earlyTruncatedGeneralizedNystrom_eq (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜)
    (Ψ : Matrix m p 𝕜) (k : ℕ) :
    A - earlyTruncatedGeneralizedNystrom A Ω Ψ k =
      A - truncatedSVD (A * Ω) k * sketchAndSolve (truncatedSVD (A * Ω) k) Ψᴴ A := by
  classical
  rw [sub_earlyTruncatedGeneralizedNystrom, mul_sketchAndSolve, Matrix.sub_mul, Matrix.one_mul]

-- A declaration name below is too long for a 100-character line.
set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- **Early-truncated generalized Nyström: the completion step with a structured co-range
sketch**: for any law of $\mathbf{\Omega}$ and an independent $\mathbf{\Psi}$ whose
$\mathbf{\Psi}^{\mathsf{H}}$ is an OSI for dimension $k$ with constant $a > 0$ and failure
probability $\delta$, for $t > 0$
$$\|\mathbf{A} - \mathsf{earlyTruncatedGN}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi}, k)
\|_{\mathsf{F}}^2 \le \Bigl(1 + \frac{t}{a}\Bigr)
\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)\|_{\mathsf{F}}^2$$
except with probability $\delta + 1/t$. Every early-truncated RSVD tail composes with it. Proved
without a literature source, as a composition with
`NLAlib.IsObliviousSubspaceInjection.measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_indepFun`;
the algorithm is [TroppYurtseverUdellCevher2017, §7.3.1, (7.3)].
Result: etgn -/
theorem
    IsObliviousSubspaceInjection.measureReal_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_gt_mul_le
    [IsProbabilityMeasure μ] {A : Matrix m n 𝕜} {k : ℕ} {a δ t : ℝ}
    (h : IsObliviousSubspaceInjection (fun ω => (Ψ ω)ᴴ) k a δ μ) (ha : 0 < a) (ht : 0 < t)
    (hind : IndepFun X Ψ μ) (hX : AEMeasurable X μ) (hΨ : AEMeasurable Ψ μ) :
    μ.real {ω | (1 + t / a) * frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 <
      frobNorm (A - earlyTruncatedGeneralizedNystrom A (X ω) (Ψ ω) k) ^ 2} ≤ δ + 1 / t := by
  classical
  simp only [sub_earlyTruncatedRSVD, sub_earlyTruncatedGeneralizedNystrom_eq]
  exact h.measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_indepFun ha ht
    (hind.symm.comp continuous_id.matrix_conjTranspose.measurable
      (((measurable_truncatedSVD k).comp (measurable_const.matrix_mul measurable_id)).prodMk
        measurable_const))
    (continuous_id.matrix_conjTranspose.measurable.comp_aemeasurable hΨ)
    (((measurable_truncatedSVD k).comp (measurable_const.matrix_mul measurable_id)
      ).comp_aemeasurable hX) aemeasurable_const
    (ae_of_all _ fun ω => rank_truncatedSVD_le _ k)

section Real

variable {X : Ω → Matrix n l ℝ} {Ψ : Ω → Matrix m p ℝ}

-- A declaration name below is too long for a 100-character line.
set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- **Early-truncated generalized Nyström: the completion through approximate multiplication**:
for any law of $\mathbf{\Omega}$ and an independent real $\mathbf{\Psi}$ whose
$\mathbf{\Psi}^{\mathsf{H}}$ is an OSI for dimension $k$ (constant $a > 0$, failure probability
$\delta$) with the $(\varepsilon, \delta', q)$ JL moment property, $\varepsilon > 0$, $q \ge 2$,
$\delta' \ge 0$,
$$\|\mathbf{A} - \mathsf{earlyTruncatedGN}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi}, k)
\|_{\mathsf{F}}^2 \le \Bigl(1 + \frac{k\varepsilon^2}{a^2}\Bigr)
\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)\|_{\mathsf{F}}^2$$
except with probability $\delta + \delta'$. Its constant-factor neighbour is
`IsObliviousSubspaceInjection.measureReal_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_gt_mul_le`.
Proved without a literature source, as a composition; the algorithm is
[TroppYurtseverUdellCevher2017, §7.3.1, (7.3)].
Result: etgn -/
theorem HasJLMoment.measureReal_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_gt_mul_le
    [IsProbabilityMeasure μ] {A : Matrix m n ℝ} {k : ℕ} {a δ ε δ' q : ℝ}
    (hJL : HasJLMoment (fun ω => (Ψ ω)ᴴ) ε δ' q μ)
    (h : IsObliviousSubspaceInjection (fun ω => (Ψ ω)ᴴ) k a δ μ) (ha : 0 < a) (hε : 0 < ε)
    (hq : 2 ≤ q) (hδ' : 0 ≤ δ') (hind : IndepFun X Ψ μ) (hX : AEMeasurable X μ)
    (hΨ : AEMeasurable Ψ μ) :
    μ.real {ω | (1 + (k : ℝ) * ε ^ 2 / a ^ 2) * frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 <
      frobNorm (A - earlyTruncatedGeneralizedNystrom A (X ω) (Ψ ω) k) ^ 2} ≤ δ + δ' := by
  classical
  simp only [sub_earlyTruncatedRSVD, sub_earlyTruncatedGeneralizedNystrom_eq]
  exact hJL.measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_indepFun h ha hε hq hδ'
    (hind.symm.comp continuous_id.matrix_conjTranspose.measurable
      (((measurable_truncatedSVD k).comp (measurable_const.matrix_mul measurable_id)).prodMk
        measurable_const))
    (continuous_id.matrix_conjTranspose.measurable.comp_aemeasurable hΨ)
    (((measurable_truncatedSVD k).comp (measurable_const.matrix_mul measurable_id)
      ).comp_aemeasurable hX) aemeasurable_const
    (ae_of_all _ fun ω => rank_truncatedSVD_le _ k)

omit [DecidableEq n] in
/-- **Early-truncated generalized Nyström with structured sketches**: if the real
$\mathbf{\Omega}^{\mathsf{H}}$ injects
$\operatorname{range}\llbracket\mathbf{A}\rrbracket_k^{\mathsf{H}}$ with constant $0 < a \le 1$
except with probability $\delta$ and has the $(\varepsilon, \delta_1, q)$ JL moment property,
and an independent real $\mathbf{\Psi}^{\mathsf{H}}$ is an OSI for dimension
$k$ (constant $a' > 0$, failure probability $\delta'$) with the $(\varepsilon', \delta_2, q')$ JL
moment property, $\varepsilon, \varepsilon' > 0$, $q, q' \ge 2$, $\delta_1, \delta_2 \ge 0$, then
for $0 < \theta < 1$
$$\|\mathbf{A} - \mathsf{earlyTruncatedGN}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi}, k)
\|_{\mathsf{F}}^2 \le \Bigl(1 + \frac{k\varepsilon'^2}{a'^2}\Bigr)
\Bigl(\frac{1 + \sqrt{k}\,\varepsilon}{(1-\theta)a} +
\frac{k\varepsilon^2}{\theta(1-\theta)a^2}\Bigr)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta + 2\delta_1 + \delta' + \delta_2$: $1 + \varepsilon_0$ at
$\ell = O(k/\varepsilon_0^2)$ and $p = O(k/\varepsilon_0)$ at constant failure probability. Proved
without a literature source, as a composition; [TroppYurtseverUdellCevher2017, §7.3.1] states the
algorithm and the rate $\Theta(r/\varepsilon^2)$ for both sizes, with unspecified constants.
Result: etgn -/
theorem HasJLMoment.measureReal_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_gt_le
    [IsProbabilityMeasure μ] {A : Matrix m n ℝ} {k : ℕ} {a θ δ ε δ₁ q a' δ' ε' δ₂ q' : ℝ}
    (hJL : HasJLMoment (fun ω => (X ω)ᴴ) ε δ₁ q μ)
    (h : HasSubspaceInjection (fun ω => (X ω)ᴴ) (truncatedSVD A k)ᴴ a δ μ)
    (hJLΨ : HasJLMoment (fun ω => (Ψ ω)ᴴ) ε' δ₂ q' μ)
    (hΨ : IsObliviousSubspaceInjection (fun ω => (Ψ ω)ᴴ) k a' δ' μ) (hind : IndepFun X Ψ μ)
    (hX : AEMeasurable X μ) (hΨm : AEMeasurable Ψ μ) (ha : 0 < a) (ha1 : a ≤ 1) (hθ : 0 < θ)
    (hθ1 : θ < 1) (hε : 0 < ε) (hq : 2 ≤ q) (hδ₁ : 0 ≤ δ₁) (ha' : 0 < a') (hε' : 0 < ε')
    (hq' : 2 ≤ q') (hδ₂ : 0 ≤ δ₂) :
    μ.real {ω | (1 + (k : ℝ) * ε' ^ 2 / a' ^ 2) *
        ((1 + √(k : ℝ) * ε) / ((1 - θ) * a) + (k : ℝ) * ε ^ 2 / (θ * (1 - θ) * a ^ 2)) *
        frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - earlyTruncatedGeneralizedNystrom A (X ω) (Ψ ω) k) ^ 2} ≤
      δ + 2 * δ₁ + (δ' + δ₂) := by
  classical
  refine (measureReal_mono (s₂ := {ω | ((1 + √(k : ℝ) * ε) / ((1 - θ) * a) +
      (k : ℝ) * ε ^ 2 / (θ * (1 - θ) * a ^ 2)) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2} ∪
      {ω | (1 + (k : ℝ) * ε' ^ 2 / a' ^ 2) * frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 <
        frobNorm (A - earlyTruncatedGeneralizedNystrom A (X ω) (Ψ ω) k) ^ 2})
      fun ω hω => ?_).trans
    ((measureReal_union_le _ _).trans (add_le_add
      (hJL.measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le h hX ha ha1 hθ hθ1 hε hq hδ₁)
      (hJLΨ.measureReal_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_gt_mul_le hΨ ha' hε' hq'
        hδ₂ hind hX hΨm)))
  by_contra hc
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hc
  have hω' : (1 + (k : ℝ) * ε' ^ 2 / a' ^ 2) *
      ((1 + √(k : ℝ) * ε) / ((1 - θ) * a) + (k : ℝ) * ε ^ 2 / (θ * (1 - θ) * a ^ 2)) *
      frobNorm (A - truncatedSVD A k) ^ 2 <
        frobNorm (A - earlyTruncatedGeneralizedNystrom A (X ω) (Ψ ω) k) ^ 2 := hω
  have h1 := mul_le_mul_of_nonneg_left hc.1
    (by positivity : (0 : ℝ) ≤ 1 + (k : ℝ) * ε' ^ 2 / a' ^ 2)
  linarith [hc.2]

end Real

/-! ### Through a projection-cost-preserving sketch -/

omit [Fintype p] [DecidableEq m] [DecidableEq n] in
/-- **Early truncation through a random projection-cost-preserving sketch**: if
$\mathbf{\Omega}^{\mathsf{H}}$ is a rank-$k$ projection-cost-preserving sketch for $\mathbf{A}$
with constants $a$, $b$ except with probability $\delta$, then
$$a\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)\|_{\mathsf{F}}^2
\le b\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta$, for every choice of the truncations. With constants
$1 \mp \varepsilon$ this is
$$(1 - \varepsilon)\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)
\|_{\mathsf{F}}^2 \le
(1 + \varepsilon)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,.$$
The tail form of `NLAlib.IsProjectionCostPreserving.mul_frobNorm_sub_earlyTruncatedRSVD_sq_le`.
For a sketch of a known family the structural route
`NLAlib.HasJLMoment.measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le` (the tail form of
`NLAlib.IsSubspaceInjection.frobNorm_sub_earlyTruncatedRSVD_sq_le`) uses fewer events and gives
better constants; this is the form for a sketch known only to be projection-cost-preserving.
[CohenElderMuscoMuscoPersu2015, Lemma 3]; there for a fixed sketch with $\varepsilon$, here
a tail with constants $a$, $b$ and the named output.
Result: early-truncation-pcp-bound -/
theorem HasProjectionCostPreserving.measureReal_mul_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le
    [IsFiniteMeasure μ] {A : Matrix m n 𝕜} {k : ℕ} {a b δ : ℝ}
    (h : HasProjectionCostPreserving (fun ω => (X ω)ᴴ) A k a b δ μ) :
    μ.real {ω | b * frobNorm (A - truncatedSVD A k) ^ 2 <
      a * frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2} ≤ δ := by
  refine (measureReal_mono (s₂ := {ω | ¬ IsProjectionCostPreserving A (A * X ω) k a b})
    fun ω hω hpcp => ?_).trans (hasProjectionCostPreserving_conjTranspose_iff.1 h)
  have hω' : b * frobNorm (A - truncatedSVD A k) ^ 2 <
      a * frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 := hω
  exact not_lt.2 hpcp.mul_frobNorm_sub_earlyTruncatedRSVD_sq_le hω'

-- The name of this theorem exceeds 100 characters with its indentation.
set_option linter.style.longLine false in
omit [DecidableEq n] in
/-- **Early-truncated generalized Nyström through a random projection-cost-preserving sketch**:
if $\mathbf{\Omega}^{\mathsf{H}}$ is a rank-$k$ projection-cost-preserving sketch for
$\mathbf{A}$ with constants $a \ge 0$, $b$ except with probability $\delta$, and an independent
co-range test matrix $\mathbf{\Psi}$ has $\mathbf{\Psi}^{\mathsf{H}}$ an oblivious subspace
injection for dimension $k$ with constant $a' > 0$ and failure probability $\delta'$, then for
$t > 0$
$$a\|\mathbf{A} - \mathsf{earlyTruncatedGN}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi}, k)
\|_{\mathsf{F}}^2 \le \Bigl(1 + \frac{t}{a'}\Bigr) b\,
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta + \delta' + 1/t$. One pass, rank at most $k$. Proved as the union
of the events of
`NLAlib.HasProjectionCostPreserving.measureReal_mul_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le` and
the completion step
`NLAlib.IsObliviousSubspaceInjection.measureReal_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_gt_mul_le`.
For real sketches with the JL moment property
`NLAlib.HasJLMoment.measureReal_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_gt_le` uses no
projection-cost-preserving event and has no $1/t$ term; this is the form for a sketch known only
to be projection-cost-preserving.
[TroppYurtseverUdellCevher2017, §7.3.1], the algorithm and the remark that the results of
[CohenElderMuscoMuscoPersu2015, Theorem 12 and §10.1] imply a $(1+\varepsilon)$ bound at
$\Theta(r/\varepsilon^2)$ for both sketch sizes, with unspecified constants; here explicit, with
failure probability $\delta + \delta' + 1/t$.
Result: early-truncation-pcp-bound -/
theorem
    HasProjectionCostPreserving.measureReal_mul_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_gt_le
    [IsProbabilityMeasure μ] {A : Matrix m n 𝕜} {k : ℕ} {a b δ a' δ' t : ℝ}
    (h : HasProjectionCostPreserving (fun ω => (X ω)ᴴ) A k a b δ μ) (ha : 0 ≤ a)
    (hΨ : IsObliviousSubspaceInjection (fun ω => (Ψ ω)ᴴ) k a' δ' μ) (ha' : 0 < a') (ht : 0 < t)
    (hind : IndepFun X Ψ μ) (hX : AEMeasurable X μ) (hΨm : AEMeasurable Ψ μ) :
    μ.real {ω | (1 + t / a') * b * frobNorm (A - truncatedSVD A k) ^ 2 <
      a * frobNorm (A - earlyTruncatedGeneralizedNystrom A (X ω) (Ψ ω) k) ^ 2} ≤
      δ + δ' + 1 / t := by
  refine (measureReal_mono (s₂ := {ω | b * frobNorm (A - truncatedSVD A k) ^ 2 <
      a * frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2} ∪
      {ω | (1 + t / a') * frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 <
        frobNorm (A - earlyTruncatedGeneralizedNystrom A (X ω) (Ψ ω) k) ^ 2})
      fun ω hω => ?_).trans
    ((measureReal_union_le _ _).trans ((add_le_add
      h.measureReal_mul_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le
      (hΨ.measureReal_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_gt_mul_le ha' ht hind hX
        hΨm)).trans_eq (add_assoc _ _ _).symm))
  by_contra hc
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hc
  have hω' : (1 + t / a') * b * frobNorm (A - truncatedSVD A k) ^ 2 <
      a * frobNorm (A - earlyTruncatedGeneralizedNystrom A (X ω) (Ψ ω) k) ^ 2 := hω
  have h1 := mul_le_mul_of_nonneg_left hc.2 ha
  have h2 := mul_le_mul_of_nonneg_left hc.1 (by positivity : (0 : ℝ) ≤ 1 + t / a')
  linarith

end NLAlib
