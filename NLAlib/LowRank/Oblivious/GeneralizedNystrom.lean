/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Oblivious.RangeFinder

/-!
# Generalized Nyström with oblivious subspace injections

Tail bounds for generalized Nyström $\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})$ with
a co-range sketch $\mathbf{\Psi}^{\mathsf{H}}$ (`fun ω => (Ψ ω)ᴴ`) that is an oblivious subspace
injection, independent of the range test matrix $\mathbf{\Omega}$. The completion step is
sketch-and-solve with the random design $\mathbf{A}\mathbf{\Omega}$, whose rank is at most
$\min(\operatorname{rank}\mathbf{A}, \ell)$; so the co-range OSI needs that dimension, and the
range test matrix may have any law. Composed with a range-finder tail (the injection forms of
`NLAlib.LowRank.Oblivious.RangeFinder`, the Gaussian tail of S3, a sampling bound) it gives the
one-pass bounds of [CamanoEpperlyMeyerTropp2025, Corollary 2.8] and [Woodruff2014, Theorem 47],
and a late-truncated form. Errors are spelled as the matrix minus the named output.

## Main results

* `NLAlib.IsObliviousSubspaceInjection.measureReal_frobNorm_sub_generalizedNystrom_sq_gt_mul_le`:
  the completion step, any law of $\mathbf{\Omega}$.
* `NLAlib.HasSubspaceInjection.measureReal_frobNorm_sub_generalizedNystrom_sq_gt_le`: CEMT
  Corollary 2.8.
* `NLAlib.HasSubspaceInjection.measureReal_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_gt_le`:
  the late-truncated output.
* `NLAlib.HasJLMoment.measureReal_frobNorm_sub_generalizedNystrom_sq_gt_mul_le`,
  `NLAlib.HasJLMoment.measureReal_frobNorm_sub_generalizedNystrom_sq_gt_le`: through approximate
  multiplication, Woodruff Theorem 47's first part.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder ComplexOrder

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {m n l p : Type*} [Fintype m] [Fintype n] [Fintype l] [Fintype p] [DecidableEq m]
  [DecidableEq n] {X : Ω → Matrix n l 𝕜} {Ψ : Ω → Matrix m p 𝕜}

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
/-- The range sketch has rank at most $\min(\operatorname{rank}\mathbf{A}, \ell)$. -/
private theorem rank_mul_le_of_min_le (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) {d : ℕ}
    (hd : min A.rank (Fintype.card l) ≤ d) : (A * Ω).rank ≤ d :=
  (le_min (Matrix.rank_mul_le_left A Ω) (Matrix.rank_le_card_width (A * Ω))).trans hd

omit [DecidableEq m] [DecidableEq n] in
/-- The completion error is the sketch-and-solve error with the design
$\mathbf{A}\mathbf{\Omega}$. -/
private theorem sub_generalizedNystrom_eq (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜)
    (Ψ : Matrix m p 𝕜) :
    A - generalizedNystrom A Ω Ψ = A - A * Ω * sketchAndSolve (A * Ω) Ψᴴ A := by
  classical
  rw [sub_generalizedNystrom, mul_sketchAndSolve, Matrix.sub_mul, Matrix.one_mul]

omit [DecidableEq n] in
/-- **Generalized Nyström: the completion step with a structured co-range sketch**: for any law
of $\mathbf{\Omega}$ and an independent co-range test matrix $\mathbf{\Psi}$ whose
$\mathbf{\Psi}^{\mathsf{H}}$ is an OSI for dimension
$d \ge \min(\operatorname{rank}\mathbf{A}, \ell)$ with constant $a > 0$ and failure probability
$\delta$, for $t > 0$
$$\|\mathbf{A} - \mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})\|_{\mathsf{F}}^2 \le
\Bigl(1 + \frac{t}{a}\Bigr)
\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_{\mathsf{F}}^2$$
except with probability $\delta + 1/t$. Any range-finder tail composes with it.
[CamanoEpperlyMeyerTropp2025, proof of Corollary 2.8]; there $\mathbf{\Psi}^{\mathsf{H}}$ an OSI
for dimension $\ell$ and probability $9/10$; here dimension
$\min(\operatorname{rank}\mathbf{A}, \ell)$ and over any `RCLike` field.
Result: generalized-nystrom-tail -/
theorem IsObliviousSubspaceInjection.measureReal_frobNorm_sub_generalizedNystrom_sq_gt_mul_le
    [IsProbabilityMeasure μ] {A : Matrix m n 𝕜} {d : ℕ} {a δ t : ℝ}
    (h : IsObliviousSubspaceInjection (fun ω => (Ψ ω)ᴴ) d a δ μ)
    (hd : min A.rank (Fintype.card l) ≤ d) (hind : IndepFun X Ψ μ) (hX : AEMeasurable X μ)
    (hΨ : AEMeasurable Ψ μ) (ha : 0 < a) (ht : 0 < t) :
    μ.real {ω | (1 + t / a) * frobNorm (A - rsvd A (X ω)) ^ 2 <
      frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2} ≤ δ + 1 / t := by
  classical
  simp only [sub_rsvd, sub_generalizedNystrom_eq]
  exact h.measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_indepFun ha ht
    (hind.symm.comp continuous_id.matrix_conjTranspose.measurable
      ((measurable_const.matrix_mul measurable_id).prodMk measurable_const))
    (continuous_id.matrix_conjTranspose.measurable.comp_aemeasurable hΨ)
    ((measurable_const.matrix_mul measurable_id).comp_aemeasurable hX) aemeasurable_const
    (ae_of_all _ fun ω => rank_mul_le_of_min_le A (X ω) hd)

/-- **Generalized Nyström with oblivious subspace injections**: if $\mathbf{\Omega}^{\mathsf{H}}$
is isotropic and injects $\operatorname{range}\llbracket\mathbf{A}\rrbracket_k^{\mathsf{H}}$ with
constant $a > 0$ except with probability $\delta$, and an independent $\mathbf{\Psi}^{\mathsf{H}}$
is an OSI for dimension $d \ge \min(\operatorname{rank}\mathbf{A}, \ell)$ with constant $a' > 0$
and failure probability $\delta'$, then for $t, t' > 0$
$$\|\mathbf{A} - \mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})\|_{\mathsf{F}}^2 \le
\Bigl(1 + \frac{t'}{a'}\Bigr)\Bigl(1 + \frac{t}{a}\Bigr)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta + 1/t + \delta' + 1/t'$. One pass over $\mathbf{A}$.
[CamanoEpperlyMeyerTropp2025, Corollary 2.8]; there $(C/\alpha)^2$ at probability $4/5$, over
$\mathbb{R}$, $\mathbf{\Psi}^{\mathsf{H}}$ an OSI for dimension $\ell$; here over any `RCLike`
field, dimension $\min(\operatorname{rank}\mathbf{A}, \ell)$, explicit in $t$ and $t'$.
Result: generalized-nystrom-tail -/
theorem HasSubspaceInjection.measureReal_frobNorm_sub_generalizedNystrom_sq_gt_le
    [IsProbabilityMeasure μ] {A : Matrix m n 𝕜} {k d : ℕ} {a δ t a' δ' t' : ℝ}
    (h : HasSubspaceInjection (fun ω => (X ω)ᴴ) (truncatedSVD A k)ᴴ a δ μ)
    (hiso : IsIsotropicSketch (fun ω => (X ω)ᴴ) μ)
    (hΨ : IsObliviousSubspaceInjection (fun ω => (Ψ ω)ᴴ) d a' δ' μ)
    (hd : min A.rank (Fintype.card l) ≤ d) (hind : IndepFun X Ψ μ) (hX : AEMeasurable X μ)
    (hΨm : AEMeasurable Ψ μ) (ha : 0 < a) (ht : 0 < t) (ha' : 0 < a') (ht' : 0 < t') :
    μ.real {ω | (1 + t' / a') * (1 + t / a) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2} ≤ δ + 1 / t + (δ' + 1 / t') := by
  refine (measureReal_mono (s₂ := {ω | (1 + t / a) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - rsvd A (X ω)) ^ 2} ∪ {ω | (1 + t' / a') * frobNorm (A - rsvd A (X ω)) ^ 2 <
      frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2}) fun ω hω => ?_).trans
    ((measureReal_union_le _ _).trans (add_le_add
      (h.measureReal_frobNorm_sub_rsvd_sq_gt_le hiso ha ht)
      (hΨ.measureReal_frobNorm_sub_generalizedNystrom_sq_gt_mul_le hd hind hX hΨm ha' ht')))
  by_contra hc
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hc
  have hω' : (1 + t' / a') * (1 + t / a) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2 := hω
  have h1 := mul_le_mul_of_nonneg_left hc.1 (by positivity : (0 : ℝ) ≤ 1 + t' / a')
  linarith [hc.2]

/-- The arithmetic of the late-truncated bound: $u^2 + (v + cu)^2 \le (1 + c)^2(u^2 + v^2)$
for $u, c \ge 0$. -/
private theorem sq_add_add_mul_sq_le {u v c : ℝ} (hu : 0 ≤ u) (hc : 0 ≤ c) :
    u ^ 2 + (v + c * u) ^ 2 ≤ (1 + c) ^ 2 * (u ^ 2 + v ^ 2) := by
  set s := √(u ^ 2 + v ^ 2)
  have hs : s ^ 2 = u ^ 2 + v ^ 2 := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hus : u ≤ s := Real.le_sqrt_of_sq_le (by nlinarith)
  have hvs : v ≤ s := Real.le_sqrt_of_sq_le (by nlinarith)
  have huv : u * v ≤ s ^ 2 := by nlinarith
  have huu : u ^ 2 ≤ s ^ 2 := by nlinarith
  rw [← hs]
  nlinarith [mul_le_mul_of_nonneg_left huv hc, mul_le_mul_of_nonneg_left huu (mul_nonneg hc hc)]

/-- **Late-truncated generalized Nyström with oblivious subspace injections**: let
$\mathbf{A} \in \Bbbk^{m \times n}$, $k$ a target rank and $\mathbb{P}$ a probability measure,
and let $\mathbf{\Omega} \in \Bbbk^{n \times \ell}$ and $\mathbf{\Psi} \in \Bbbk^{m \times p}$ be
independent, almost everywhere measurable random test matrices such that
$\mathbf{\Omega}^{\mathsf{H}}$ is isotropic
($\mathbb{E}[\mathbf{\Omega}\mathbf{\Omega}^{\mathsf{H}}] = \mathbf{I}$, square-integrable
entries) and injects $\operatorname{range}\llbracket\mathbf{A}\rrbracket_k^{\mathsf{H}}$ with
constant $a > 0$ except with probability $\delta$ (`HasSubspaceInjection`), and
$\mathbf{\Psi}^{\mathsf{H}}$ is an oblivious subspace injection for dimension
$d \ge \min(\operatorname{rank}\mathbf{A}, \ell)$ with constant $a' > 0$ and failure
probability $\delta'$ (`IsObliviousSubspaceInjection`). Then for $t, t' > 0$
$$\mathbb{P}\Bigl[
\|\mathbf{A} - \llbracket\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})\rrbracket_k
\|_{\mathsf{F}}^2 > \Bigl(1 + 2\sqrt{t'/a'}\Bigr)^2\Bigl(1 + \frac{t}{a}\Bigr)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\Bigr]
\le \delta + \frac{1}{t} + \delta' + \frac{1}{t'}\,:$$
a rank-$k$ single-pass output with a constant factor. The truncated form of
`NLAlib.HasSubspaceInjection.measureReal_frobNorm_sub_generalizedNystrom_sq_gt_le`. Proved without
a literature source; [CamanoEpperlyMeyerTropp2025, Remark 2.9] discusses a different,
core-truncated estimator.
Result: generalized-nystrom-tail -/
theorem HasSubspaceInjection.measureReal_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_gt_le
    [IsProbabilityMeasure μ] {A : Matrix m n 𝕜} {k d : ℕ} {a δ t a' δ' t' : ℝ}
    (h : HasSubspaceInjection (fun ω => (X ω)ᴴ) (truncatedSVD A k)ᴴ a δ μ)
    (hiso : IsIsotropicSketch (fun ω => (X ω)ᴴ) μ)
    (hΨ : IsObliviousSubspaceInjection (fun ω => (Ψ ω)ᴴ) d a' δ' μ)
    (hd : min A.rank (Fintype.card l) ≤ d) (hind : IndepFun X Ψ μ) (hX : AEMeasurable X μ)
    (hΨm : AEMeasurable Ψ μ) (ha : 0 < a) (ht : 0 < t) (ha' : 0 < a') (ht' : 0 < t') :
    μ.real {ω | (1 + 2 * √(t' / a')) ^ 2 * (1 + t / a) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - truncatedSVD (generalizedNystrom A (X ω) (Ψ ω)) k) ^ 2} ≤
      δ + 1 / t + (δ' + 1 / t') := by
  have hU := hΨ.measure_not_isSubspaceInjection_union_gt_le_of_indepFun ht'
    (hind.symm.comp continuous_id.matrix_conjTranspose.measurable
      ((measurable_const.matrix_mul measurable_id).prodMk measurable_const))
    (continuous_id.matrix_conjTranspose.measurable.comp_aemeasurable hΨm)
    ((measurable_const.matrix_mul measurable_id).comp_aemeasurable hX) aemeasurable_const
    (ae_of_all _ fun ω => rank_mul_le_of_min_le A (X ω) hd) (a := a') (B := fun _ => A)
  refine (measureReal_mono fun ω hω => ?_).trans ((measureReal_union_le _ _).trans
    (add_le_add (h.measureReal_frobNorm_sub_truncatedSVD_rsvd_sq_gt_le hiso ha ht) hU))
  by_contra hc
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt, not_not] at hc
  obtain ⟨h4, hinj, hM⟩ := hc
  simp only [id_eq] at hinj hM
  rw [← sub_rsvd] at hM
  have hω' : (1 + 2 * √(t' / a')) ^ 2 * (1 + t / a) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - truncatedSVD (generalizedNystrom A (X ω) (Ψ ω)) k) ^ 2 := hω
  have hrank := hinj.rank_mul_eq ha'
  have hT := frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_frobNorm_truncatedSVD hrank k
  have hL6 := frobNorm_truncatedSVD_le
    (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω))) (2 * k)
  have hPi := hinj.frobNorm_obliqueProjector_mul_sq_le ha' (A - rsvd A (X ω))
  have hu := frobNorm_nonneg (A - rsvd A (X ω))
  have hc0 : 0 ≤ 2 * √(t' / a') := by positivity
  have hw : 2 * frobNorm (truncatedSVD (obliqueProjector (A * X ω) (Ψ ω)ᴴ *
      (A - rsvd A (X ω))) (2 * k)) ≤ 2 * √(t' / a') * frobNorm (A - rsvd A (X ω)) := by
    have hsq : frobNorm (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω))) ^ 2 ≤
        (√(t' / a') * frobNorm (A - rsvd A (X ω))) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      calc _ ≤ frobNorm ((Ψ ω)ᴴ * (A - rsvd A (X ω))) ^ 2 / a' := hPi
        _ ≤ t' * frobNorm (A - rsvd A (X ω)) ^ 2 / a' := div_le_div_of_nonneg_right hM ha'.le
        _ = t' / a' * frobNorm (A - rsvd A (X ω)) ^ 2 := by ring
    have h1 := (pow_le_pow_iff_left₀ (frobNorm_nonneg _) (by positivity) two_ne_zero).1 hsq
    linarith
  have h5 : frobNorm (A - rsvd A (X ω)) ^ 2 +
      (frobNorm (rsvd A (X ω) - truncatedSVD (rsvd A (X ω)) k) +
        2 * frobNorm (truncatedSVD (obliqueProjector (A * X ω) (Ψ ω)ᴴ *
          (A - rsvd A (X ω))) (2 * k))) ^ 2 ≤
      frobNorm (A - rsvd A (X ω)) ^ 2 +
        (frobNorm (rsvd A (X ω) - truncatedSVD (rsvd A (X ω)) k) +
          2 * √(t' / a') * frobNorm (A - rsvd A (X ω))) ^ 2 := by
    gcongr
  have h6 := sq_add_add_mul_sq_le
    (v := frobNorm (rsvd A (X ω) - truncatedSVD (rsvd A (X ω)) k)) hu hc0
  have h4' : frobNorm (A - rsvd A (X ω)) ^ 2 +
      frobNorm (rsvd A (X ω) - truncatedSVD (rsvd A (X ω)) k) ^ 2 ≤
        (1 + t / a) * frobNorm (A - truncatedSVD A k) ^ 2 := by
    rw [← frobNorm_sub_truncatedSVD_rsvd_sq]
    exact h4
  have h7 := mul_le_mul_of_nonneg_left h4' (sq_nonneg (1 + 2 * √(t' / a')))
  have e : (1 + 2 * √(t' / a')) ^ 2 * ((1 + t / a) * frobNorm (A - truncatedSVD A k) ^ 2) =
      (1 + 2 * √(t' / a')) ^ 2 * (1 + t / a) * frobNorm (A - truncatedSVD A k) ^ 2 := by ring
  linarith

section Real

variable {X : Ω → Matrix n l ℝ} {Ψ : Ω → Matrix m p ℝ}

omit [DecidableEq n] in
/-- **Generalized Nyström: the completion through approximate multiplication**: for any law of
$\mathbf{\Omega}$ and an independent real $\mathbf{\Psi}$ whose $\mathbf{\Psi}^{\mathsf{H}}$ is an
OSI for dimension $d \ge \min(\operatorname{rank}\mathbf{A}, \ell)$ (constant $a > 0$, failure
probability $\delta$) with the $(\varepsilon, \delta', q)$ JL moment property, $\varepsilon > 0$,
$q \ge 2$, $\delta' \ge 0$,
$$\|\mathbf{A} - \mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})\|_{\mathsf{F}}^2 \le
\Bigl(1 + \frac{d\,\varepsilon^2}{a^2}\Bigr)
\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_{\mathsf{F}}^2$$
except with probability $\delta + \delta'$. Its constant-factor neighbour is
`NLAlib.IsObliviousSubspaceInjection.measureReal_frobNorm_sub_generalizedNystrom_sq_gt_mul_le`.
[Woodruff2014, proof of Theorem 47]; there the multiplication step implicit.
Result: generalized-nystrom-tail -/
theorem HasJLMoment.measureReal_frobNorm_sub_generalizedNystrom_sq_gt_mul_le
    [IsProbabilityMeasure μ] {A : Matrix m n ℝ} {d : ℕ} {a δ ε δ' q : ℝ}
    (hJL : HasJLMoment (fun ω => (Ψ ω)ᴴ) ε δ' q μ)
    (h : IsObliviousSubspaceInjection (fun ω => (Ψ ω)ᴴ) d a δ μ)
    (hd : min A.rank (Fintype.card l) ≤ d) (hind : IndepFun X Ψ μ) (hX : AEMeasurable X μ)
    (hΨ : AEMeasurable Ψ μ) (ha : 0 < a) (hε : 0 < ε) (hq : 2 ≤ q) (hδ' : 0 ≤ δ') :
    μ.real {ω | (1 + (d : ℝ) * ε ^ 2 / a ^ 2) * frobNorm (A - rsvd A (X ω)) ^ 2 <
      frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2} ≤ δ + δ' := by
  classical
  simp only [sub_rsvd, sub_generalizedNystrom_eq]
  exact hJL.measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_indepFun h ha hε hq hδ'
    (hind.symm.comp continuous_id.matrix_conjTranspose.measurable
      ((measurable_const.matrix_mul measurable_id).prodMk measurable_const))
    (continuous_id.matrix_conjTranspose.measurable.comp_aemeasurable hΨ)
    ((measurable_const.matrix_mul measurable_id).comp_aemeasurable hX) aemeasurable_const
    (ae_of_all _ fun ω => rank_mul_le_of_min_le A (X ω) hd)

omit [DecidableEq n] in
/-- **Generalized Nyström to relative error**: both sides through approximate multiplication. If
the real $\mathbf{\Omega}^{\mathsf{H}}$ injects
$\operatorname{range}\llbracket\mathbf{A}\rrbracket_k^{\mathsf{H}}$ with constant $a > 0$ except
with probability $\delta$ and has the $(\varepsilon, \delta_1, q)$ JL moment property, and an
independent real $\mathbf{\Psi}^{\mathsf{H}}$ is an OSI for dimension
$d \ge \min(\operatorname{rank}\mathbf{A}, \ell)$ (constant $a' > 0$, failure probability $\delta'$)
with the $(\varepsilon', \delta_2, q')$ JL moment property, with $\varepsilon, \varepsilon' > 0$,
$q, q' \ge 2$ and $\delta_1, \delta_2 \ge 0$, then
$$\|\mathbf{A} - \mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})\|_{\mathsf{F}}^2 \le
\Bigl(1 + \frac{d\,\varepsilon'^2}{a'^2}\Bigr)\Bigl(1 + \frac{k\varepsilon^2}{a^2}\Bigr)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta + \delta_1 + \delta' + \delta_2$. Its constant-factor neighbour is
`NLAlib.HasSubspaceInjection.measureReal_frobNorm_sub_generalizedNystrom_sq_gt_le`.
[Woodruff2014, Theorem 47, first part]; there $\mathbf{R}$ a $(1 + O(\varepsilon))$ embedding of
the row space of $\mathbf{S}\mathbf{A}$ and the multiplication step implicit; here explicit.
Result: generalized-nystrom-tail -/
theorem HasJLMoment.measureReal_frobNorm_sub_generalizedNystrom_sq_gt_le [IsProbabilityMeasure μ]
    {A : Matrix m n ℝ} {k d : ℕ} {a δ ε δ₁ q a' δ' ε' δ₂ q' : ℝ}
    (hJL : HasJLMoment (fun ω => (X ω)ᴴ) ε δ₁ q μ)
    (h : HasSubspaceInjection (fun ω => (X ω)ᴴ) (truncatedSVD A k)ᴴ a δ μ)
    (hJLΨ : HasJLMoment (fun ω => (Ψ ω)ᴴ) ε' δ₂ q' μ)
    (hΨ : IsObliviousSubspaceInjection (fun ω => (Ψ ω)ᴴ) d a' δ' μ)
    (hd : min A.rank (Fintype.card l) ≤ d) (hind : IndepFun X Ψ μ) (hX : AEMeasurable X μ)
    (hΨm : AEMeasurable Ψ μ) (ha : 0 < a) (hε : 0 < ε) (hq : 2 ≤ q) (hδ₁ : 0 ≤ δ₁)
    (ha' : 0 < a') (hε' : 0 < ε') (hq' : 2 ≤ q') (hδ₂ : 0 ≤ δ₂) :
    μ.real {ω | (1 + (d : ℝ) * ε' ^ 2 / a' ^ 2) * (1 + (k : ℝ) * ε ^ 2 / a ^ 2) *
        frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2} ≤ δ + δ₁ + (δ' + δ₂) := by
  classical
  refine (measureReal_mono (s₂ := {ω | (1 + (k : ℝ) * ε ^ 2 / a ^ 2) *
      frobNorm (A - truncatedSVD A k) ^ 2 < frobNorm (A - rsvd A (X ω)) ^ 2} ∪
      {ω | (1 + (d : ℝ) * ε' ^ 2 / a' ^ 2) * frobNorm (A - rsvd A (X ω)) ^ 2 <
        frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2}) fun ω hω => ?_).trans
    ((measureReal_union_le _ _).trans (add_le_add
      (hJL.measureReal_frobNorm_sub_rsvd_sq_gt_le h hX ha hε hq hδ₁)
      (hJLΨ.measureReal_frobNorm_sub_generalizedNystrom_sq_gt_mul_le hΨ hd hind hX hΨm ha' hε' hq'
        hδ₂)))
  by_contra hc
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hc
  have hω' : (1 + (d : ℝ) * ε' ^ 2 / a' ^ 2) * (1 + (k : ℝ) * ε ^ 2 / a ^ 2) *
      frobNorm (A - truncatedSVD A k) ^ 2 <
        frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2 := hω
  have h1 := mul_le_mul_of_nonneg_left hc.1
    (by positivity : (0 : ℝ) ≤ 1 + (d : ℝ) * ε' ^ 2 / a' ^ 2)
  linarith [hc.2]

end Real

end NLAlib
