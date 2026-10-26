/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Gaussian.TruncatedGeneralizedNystrom
public import NLAlibScaffold.LowRank.Gaussian.RangeFinder
public import NLAlibScaffold.LowRank.Structural.Truncation
public import NLAlibScaffold.Regression.SketchAndSolve

/-!
# Truncated generalized Nyström with $O(k/\varepsilon)$ sketches (research)

For independent standard Gaussian test matrices $\mathbf{\Omega}$ ($n \times \ell$) and
$\mathbf{\Psi}$ ($m \times p$) with $4k \le \ell$ and $4\ell \le p$, the late truncation of
generalized Nyström satisfies
$$\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})
\rrbracket_k\|_{\mathsf{F}}^2 \le \Bigl(1 + \frac{k}{\ell - k - 1} + C\Bigl(\frac{k}{p} +
\frac{k}{\sqrt{\ell p}}\Bigr)\Bigr)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
for an absolute constant $C$, so relative error $1 + \varepsilon$ needs only
$\ell = O(k/\varepsilon)$ and $p = 4\ell$, against $p = O(k/\varepsilon^2)$ in
`NLAlib/LowRank/Gaussian/TruncatedGeneralizedNystrom.lean`. The proof conditions on
$\mathbf{\Omega}$: the localized perturbed truncation
(`NLAlib.frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_window`) leaves the spectral core
noise (the library's sketch-and-solve bound) and its compression to the window of singular values
of $\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})$ within a factor $2$ of the truncation level,
whose mean is $O(\sqrt{w/p})$ for a window of dimension $w$; then the range-finder moments.

Research statements for `docs/design/research/TruncatedGN-Upper.md` (G43, C45, M1, M2), after the
maintainer's derivation and its verification (research note OP6 of the NLAlib workflow,
`reports/OP6-TruncatedGN-Upper.md`, Theorem (1)). Not for `main`. Real. Proofs deferred.

## Main results

* the compressed core noise at a fixed range test matrix (G43):
`integral_specNorm_mul_obliqueProjector_mul_sub_rsvd_mul_le_of_hasLaw_gaussianMatrix`;
* the conditional expected error (C45):
`exists_forall_integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_of_gaussianMatrix`;
* the expected error (M1):
[explorer](https://nla-lib.org/explore/#d/NLAlib.exists_forall_integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_of_hasLaw_gaussianMatrix);
* relative error $1 + \varepsilon$ with $O(k/\varepsilon)$ samples (M2):
[explorer](https://nla-lib.org/explore/#d/NLAlib.exists_forall_integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_one_add_of_hasLaw_gaussianMatrix).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n l p : Type*} [Fintype m]
  [Fintype n] [Fintype l] [Fintype p] {Ψ : Ω → Matrix m p ℝ}

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The compressed core noise of generalized Nyström**: for $\mathbf{A} \in
\mathbb{R}^{m \times n}$, a fixed $\mathbf{x} \in \mathbb{R}^{n \times \ell}$, a standard
Gaussian $\mathbf{\Psi} \in \mathbb{R}^{m \times p}$ with $4\ell \le p$, $\mathbf{R} =
\mathsf{rsvd}(\mathbf{A}, \mathbf{x})$, $\mathbf{N} = \mathbf{\Pi}_{\mathbf{A}\mathbf{x},
\mathbf{\Psi}^{\mathsf{T}}}(\mathbf{A} - \mathbf{R})$ and any $\mathbf{F} \in
\mathbb{R}^{a \times m}$, $\mathbf{T} \in \mathbb{R}^{n \times b}$,
$$\mathbb{E}\|\mathbf{F}\mathbf{N}\mathbf{T}\|_2 \le \frac{4}{\sqrt p}\bigl(
\|(\mathbf{A} - \mathbf{R})\mathbf{T}\|_2\|\mathbf{F}\|_{\mathsf{F}} +
\|(\mathbf{A} - \mathbf{R})\mathbf{T}\|_{\mathsf{F}}\|\mathbf{F}\|_2\bigr)\,.$$
With $\mathbf{F}$, $\mathbf{T}$ projectors of rank $w$ the right side is at most
$8\sqrt{w/p}\,\|\mathbf{A} - \mathbf{R}\|_2$ (research note OP6, §4.3).
No printed source.
Proof: S, about 35 lines. If $\ell = 0$ then $\mathbf{A}\mathbf{x} = \mathbf{0}$ and the
integrand vanishes (`obliqueProjector`, `Matrix.mul_zero`-type simp). Otherwise $p \ge 4$.
$\mathbf{N}\mathbf{T} = \mathbf{\Pi}((\mathbf{I} - \mathbf{P}_{\mathbf{A}\mathbf{x}})
(\mathbf{A}\mathbf{T}))$ (`sub_rsvd`, `Matrix.mul_assoc`), and
`NLAlib.integral_specNorm_mul_obliqueProjector_mul_one_sub_rangeProjector_mul_le_of_hasLaw_gaussianMatrix`
with the sketch $\mathbf{\Psi}^{\mathsf{T}}$ (`hasLaw_conjTranspose_of_hasLaw_gaussianMatrix`),
$\mathbf{X} = \mathbf{A}\mathbf{x}$ (rank $q \le \ell$, `Matrix.rank_le_card_width`, so
$q + 2 \le p$) and $\mathbf{B} = \mathbf{A}\mathbf{T}$. The constant:
`gaussianPinvSpecNormBound_le` gives $\beta \le e\sqrt p/(p - q) \le \tfrac{4e}{3}/\sqrt p \le
4/\sqrt p$ ($4q \le p$, `Real.exp_one_lt_d9`). -/
theorem integral_specNorm_mul_obliqueProjector_mul_sub_rsvd_mul_le_of_hasLaw_gaussianMatrix
    {a b : Type*} [Fintype a] [Fintype b] (A : Matrix m n ℝ) (x : Matrix n l ℝ)
    (hΨ : HasLaw Ψ (gaussianMatrix m p) μ) (hlp : 4 * Fintype.card l ≤ Fintype.card p)
    (F : Matrix a m ℝ) (T : Matrix n b ℝ) :
    ∫ ω, specNorm (F * (obliqueProjector (A * x) (Ψ ω)ᴴ * (A - rsvd A x)) * T) ∂μ ≤
      4 / √(Fintype.card p : ℝ) *
        (specNorm ((A - rsvd A x) * T) * frobNorm F +
          frobNorm ((A - rsvd A x) * T) * specNorm F) := by
  classical
  have hΨ' : HasLaw (fun ω => (Ψ ω)ᴴ) (gaussianMatrix p m) μ :=
    hasLaw_conjTranspose_of_hasLaw_gaussianMatrix hΨ
  rcases Nat.eq_zero_or_pos (Fintype.card l) with hl | hl
  · have hx : A * x = 0 := by
      have : IsEmpty l := Fintype.card_eq_zero_iff.mp hl
      ext i j
      exact (IsEmpty.false j).elim
    simp only [hx, obliqueProjector, Matrix.zero_mul, Matrix.mul_zero, specNorm_zero,
      integral_zero]
    positivity
  · have hq : (A * x).rank ≤ Fintype.card l := Matrix.rank_le_card_width _
    have hq2 : (A * x).rank + 2 ≤ Fintype.card p := by omega
    have hβ : gaussianPinvSpecNormBound (A * x).rank (Fintype.card p) ≤
        4 / √(Fintype.card p : ℝ) := by
      have hlt : (A * x).rank < Fintype.card p := by omega
      refine (gaussianPinvSpecNormBound_le hlt).trans ?_
      have hP : (4 : ℝ) ≤ Fintype.card p := by exact_mod_cast (by omega : 4 ≤ Fintype.card p)
      have hq4 : ((A * x).rank : ℝ) * 4 ≤ Fintype.card p := by
        exact_mod_cast (by omega : (A * x).rank * 4 ≤ Fintype.card p)
      have hsq : 0 < √(Fintype.card p : ℝ) := Real.sqrt_pos.mpr (by linarith)
      have hsq2 := Real.mul_self_sqrt (by linarith : (0 : ℝ) ≤ Fintype.card p)
      have he := Real.exp_one_lt_d9
      have hpos : (0 : ℝ) < (Fintype.card p : ℝ) - (A * x).rank := by
        have : (0 : ℝ) ≤ (A * x).rank := by positivity
        linarith
      rw [div_le_div_iff₀ hpos hsq]
      have e1 : Real.exp 1 * √(Fintype.card p : ℝ) * √(Fintype.card p : ℝ) =
          Real.exp 1 * Fintype.card p := by
        rw [mul_assoc, hsq2]
      rw [e1]
      nlinarith [mul_le_mul_of_nonneg_right he.le (by linarith : (0 : ℝ) ≤ Fintype.card p)]
    have hmain :=
      integral_specNorm_mul_obliqueProjector_mul_one_sub_rangeProjector_mul_le_of_hasLaw_gaussianMatrix
        (S := fun ω => (Ψ ω)ᴴ) hΨ' (A * x) hq2 (A * T) F
    simp only [sub_rsvd, Matrix.mul_assoc]
    refine hmain.trans ?_
    exact mul_le_mul_of_nonneg_right hβ (by positivity)

/-- The difference of the range projectors of two matrices of rank at most $b$ has squared
Frobenius norm at most $4b$. -/
private theorem frobNorm_rangeProjector_sub_rangeProjector_sq_le {r s : Type*} [Fintype r]
    [Fintype s] {X Y : Matrix r s ℝ} {b : ℕ} (hX : X.rank ≤ b) (hY : Y.rank ≤ b) :
    frobNorm (rangeProjector X - rangeProjector Y) ^ 2 ≤ 4 * b := by
  have hXb : frobNorm (rangeProjector X) ^ 2 ≤ b := by
    rw [frobNorm_rangeProjector_sq]; exact_mod_cast hX
  have hYb : frobNorm (rangeProjector Y) ^ 2 ≤ b := by
    rw [frobNorm_rangeProjector_sq]; exact_mod_cast hY
  have h := frobNorm_sub_le (rangeProjector X) (rangeProjector Y)
  nlinarith [frobNorm_nonneg (rangeProjector X - rangeProjector Y),
    sq_nonneg (frobNorm (rangeProjector X) - frobNorm (rangeProjector Y))]

/-- The difference of two range projectors has spectral norm at most $2$. -/
private theorem specNorm_rangeProjector_sub_rangeProjector_le_two {r s : Type*} [Fintype r]
    [Fintype s] (X Y : Matrix r s ℝ) :
    specNorm (rangeProjector X - rangeProjector Y) ≤ 2 :=
  (specNorm_sub_le _ _).trans (by linarith [(isStarProjection_rangeProjector X).specNorm_le_one,
    (isStarProjection_rangeProjector Y).specNorm_le_one])

/-- The compressed core noise at a fixed range test matrix, for compressions of spectral norm at
most $2$: it is integrable with mean at most
$8\|\mathbf{E}\|_2(\|\mathbf{F}\|_{\mathsf{F}} + \|\mathbf{T}\|_{\mathsf{F}})/\sqrt p$. -/
private theorem integral_specNorm_mul_obliqueProjector_mul_sub_rsvd_mul_le_div {a b : Type*}
    [Fintype a] [Fintype b] (A : Matrix m n ℝ) (x : Matrix n l ℝ)
    (hlp : 4 * Fintype.card l ≤ Fintype.card p) {F : Matrix a m ℝ} {T : Matrix n b ℝ}
    (hF : specNorm F ≤ 2) (hT : specNorm T ≤ 2) (hη : Integrable (fun ψ : Matrix m p ℝ =>
      specNorm (obliqueProjector (A * x) ψᴴ * (A - rsvd A x)) ^ 2) (gaussianMatrix m p)) :
    Integrable (fun ψ : Matrix m p ℝ =>
      specNorm (F * (obliqueProjector (A * x) ψᴴ * (A - rsvd A x)) * T)) (gaussianMatrix m p) ∧
    ∫ ψ, specNorm (F * (obliqueProjector (A * x) ψᴴ * (A - rsvd A x)) * T)
        ∂(gaussianMatrix m p) ≤
      8 * specNorm (A - rsvd A x) * (frobNorm F + frobNorm T) / √(Fintype.card p : ℝ) := by
  set E := A - rsvd A x
  refine ⟨?_, ?_⟩
  · have hNm := (measurable_obliqueProjector_mul_sub_rsvd (l := l) (p := p) A).comp
      ((measurable_const (a := x)).prodMk (measurable_id (α := Matrix m p ℝ)))
    refine ((hη.const_mul 2).add (integrable_const 2)).mono' (continuous_specNorm.measurable.comp
        ((measurable_const.matrix_mul hNm).matrix_mul measurable_const)).aestronglyMeasurable
      (ae_of_all _ fun ψ => ?_)
    set N := obliqueProjector (A * x) ψᴴ * E
    have h1 := specNorm_mul_le (F * N) T
    have h2 := specNorm_mul_le F N
    rw [Real.norm_of_nonneg (specNorm_nonneg _)]
    simp only [Pi.add_apply]
    nlinarith [specNorm_nonneg F, specNorm_nonneg T, specNorm_nonneg N,
      specNorm_nonneg (F * N), sq_nonneg (specNorm N - 1),
      mul_le_mul_of_nonneg_right h2 (specNorm_nonneg T),
      mul_le_mul_of_nonneg_left hF (specNorm_nonneg N),
      mul_le_mul_of_nonneg_left hT (mul_nonneg (specNorm_nonneg F) (specNorm_nonneg N))]
  · refine (integral_specNorm_mul_obliqueProjector_mul_sub_rsvd_mul_le_of_hasLaw_gaussianMatrix
      A x HasLaw.id hlp F T).trans ?_
    have h1 := specNorm_mul_le E T
    have h2 := frobNorm_mul_le_specNorm_mul_frobNorm E T
    rw [div_mul_eq_mul_div]
    gcongr ?_ / _
    nlinarith [specNorm_nonneg E, specNorm_nonneg F, frobNorm_nonneg F,
      frobNorm_nonneg T, specNorm_nonneg (E * T),
      mul_le_mul_of_nonneg_right h1 (frobNorm_nonneg F),
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hT (specNorm_nonneg E))
        (frobNorm_nonneg F),
      mul_le_mul_of_nonneg_left hF (frobNorm_nonneg (E * T)),
      mul_le_mul_of_nonneg_right h2 (specNorm_nonneg F)]

/-- The arithmetic of the spectral term: from
$I \le \frac{25}{P}F + \frac{4L}{P}S^2$, $500kI \le 12500k\frac{F + LS^2}{P}$. -/
private theorem mul_le_mul_div_add_of_le {k F L P S I : ℝ} (hk : 0 ≤ k) (hF : 0 ≤ F)
    (hL : 0 ≤ L) (hP : 0 ≤ P) (hI : I ≤ 25 / P * F + 4 * L / P * S ^ 2) :
    500 * k * I ≤ 12500 * k * ((F + L * S ^ 2) / P) := by
  have e1 : 25 / P * F + 4 * L / P * S ^ 2 = 25 * (F * P⁻¹) + 4 * (L * S ^ 2 * P⁻¹) := by ring
  have e2 : (F + L * S ^ 2) / P = F * P⁻¹ + L * S ^ 2 * P⁻¹ := by ring
  rw [e1] at hI
  rw [e2]
  have hu : 0 ≤ L * S ^ 2 * P⁻¹ := by positivity
  have hv : 0 ≤ F * P⁻¹ := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hI hk, mul_nonneg hk hu, mul_nonneg hk hv]

/-- The arithmetic of the window term: from $s^2 \le 16(k + q)$ and $q\theta^2 \le 4\gamma^2$,
$\theta\min(k, q)\,s \le 12k\gamma$. -/
private theorem mul_min_mul_le {θ γ s : ℝ} {k q : ℕ} (hθ : 0 ≤ θ) (hγ : 0 ≤ γ) (hs : 0 ≤ s)
    (hs2 : s ^ 2 ≤ 16 * ((k : ℝ) + q)) (hq : (q : ℝ) * θ ^ 2 ≤ 4 * γ ^ 2) :
    θ * ((min k q : ℕ) : ℝ) * s ≤ 12 * k * γ := by
  have hkey : ((min k q : ℕ) : ℝ) ^ 2 * ((k : ℝ) + q) ≤ 2 * (k : ℝ) ^ 2 * q := by
    rcases le_total k q with h | h
    · rw [min_eq_left h]
      have h' : (k : ℝ) ≤ q := by exact_mod_cast h
      nlinarith [sq_nonneg (k : ℝ)]
    · rw [min_eq_right h]
      have h' : (q : ℝ) ≤ k := by exact_mod_cast h
      have hq0 : (0 : ℝ) ≤ q := by positivity
      nlinarith [mul_nonneg hq0 hq0, mul_le_mul_of_nonneg_left h' (mul_nonneg hq0 hq0),
        mul_le_mul_of_nonneg_left h' (mul_nonneg hq0 (Nat.cast_nonneg (α := ℝ) k))]
  have hm0 : (0 : ℝ) ≤ ((min k q : ℕ) : ℝ) := by positivity
  have hsq : (θ * ((min k q : ℕ) : ℝ) * s) ^ 2 ≤ (12 * k * γ) ^ 2 := by
    have e1 : (θ * ((min k q : ℕ) : ℝ) * s) ^ 2 ≤
        θ ^ 2 * ((min k q : ℕ) : ℝ) ^ 2 * (16 * ((k : ℝ) + q)) := by
      rw [mul_pow, mul_pow]; gcongr
    have e2 : θ ^ 2 * (((min k q : ℕ) : ℝ) ^ 2 * ((k : ℝ) + q)) ≤ θ ^ 2 * (2 * (k : ℝ) ^ 2 * q) :=
      mul_le_mul_of_nonneg_left hkey (sq_nonneg θ)
    have e3 : (k : ℝ) ^ 2 * ((q : ℝ) * θ ^ 2) ≤ (k : ℝ) ^ 2 * (4 * γ ^ 2) :=
      mul_le_mul_of_nonneg_left hq (sq_nonneg _)
    nlinarith
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq

/-- The arithmetic of the window term after integration: from $I \le 8es/\sqrt P$ and
$\theta m s \le 12k\gamma$, $40\theta m I \le 12500k\,e\gamma/\sqrt P$. -/
private theorem mul_le_mul_div_sqrt_of_le {θ m I e s k γ P : ℝ} (hθ : 0 ≤ θ) (hm : 0 ≤ m)
    (he : 0 ≤ e) (hk : 0 ≤ k) (hγ : 0 ≤ γ) (hI : I ≤ 8 * e * s / √P)
    (hw : θ * m * s ≤ 12 * k * γ) :
    40 * θ * m * I ≤ 12500 * k * (e * γ / √P) := by
  refine (mul_le_mul_of_nonneg_left hI (by positivity)).trans ?_
  have e1 : 40 * θ * m * (8 * e * s / √P) = 320 * (e * (1 / √P)) * (θ * m * s) := by ring
  have e2 : 12500 * k * (e * γ / √P) = 12500 * (e * (1 / √P)) * (k * γ) := by ring
  rw [e1, e2]
  have hw0 : 0 ≤ e * (1 / √P) := by positivity
  linarith [mul_le_mul_of_nonneg_left hw hw0, mul_nonneg hw0 (mul_nonneg hk hγ)]

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The expected error of truncated generalized Nyström at a fixed range test matrix**: there is
an absolute constant $C > 0$ such that for $\mathbf{A} \in \mathbb{R}^{m \times n}$, every fixed
$\mathbf{x} \in \mathbb{R}^{n \times \ell}$, a standard Gaussian $\mathbf{\Psi} \in
\mathbb{R}^{m \times p}$ with $4\ell \le p$, any $k$, $\mathbf{R} = \mathsf{rsvd}(\mathbf{A},
\mathbf{x})$ and $\mathbf{E} = \mathbf{A} - \mathbf{R}$,
$$\mathbb{E}_{\mathbf{\Psi}}\|\mathbf{A} - \llbracket\mathsf{gn}(\mathbf{A}, \mathbf{x},
\mathbf{\Psi})\rrbracket_k\|_{\mathsf{F}}^2 \le
\|\mathbf{A} - \llbracket\mathbf{R}\rrbracket_k\|_{\mathsf{F}}^2 + Ck\Bigl(
\frac{\|\mathbf{E}\|_{\mathsf{F}}^2 + \ell\,\|\mathbf{E}\|_2^2}{p} +
\frac{\|\mathbf{E}\|_2\,\|\mathbf{R} - \llbracket\mathbf{R}\rrbracket_k\|_{\mathsf{F}}}{\sqrt p}
\Bigr)\,.$$
$O(1)$ suffices for $C$: the proof gives $C = 12500$. For the choice `truncatedSVD` makes.
No printed source. New (maintainer's derivation (2); research note OP6, Corollary 4.5).
Proof: L, about 100 lines. Take $C = 12500$; $k = 0$ is trivial (`truncatedSVD_zero`); for
$\ell = 0$ both sides are $\|\mathbf{A}\|_{\mathsf{F}}^2$-type and the noise vanishes. Fix the
window $a \le k \le b$ of $\mathbf{R}$ (`NLAlib.exists_singularValues_window`; it depends on
$\mathbf{x}$ only). Almost surely $\operatorname{rank}(\mathbf{\Psi}^{\mathsf{T}}\mathbf{A}
\mathbf{x}) = \operatorname{rank}(\mathbf{A}\mathbf{x})$
(`ae_rank_conjTranspose_mul_eq_of_hasLaw_gaussianMatrix` with `HasLaw.id`), and there
`NLAlib.frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_window` bounds the integrand by
$\|\mathbf{A} - \llbracket\mathbf{R}\rrbracket_k\|^2 + 500k\eta^2 + 40\theta\min(k, b - k)\mu$.
Integrate (`integral_mono_ae`; integrability of the left side:
`integrable_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_of_hasLaw_gaussianMatrix` with the
constant range test matrix, `aemeasurable_const`, `indepFun_const_left`; of $\eta^2$:
`integrable_specNorm_obliqueProjector_mul_one_sub_rangeProjector_mul_sq_of_hasLaw_gaussianMatrix`;
$\mu \le \eta \le 1 + \eta^2$ dominates $\mu$, measurable by
`measurable_obliqueProjector_mul_sub_rsvd`). Then
$\mathbb{E}\eta^2 \le \frac{25}{p}\|\mathbf{E}\|_{\mathsf{F}}^2 + \frac{4\ell}{p}\|\mathbf{E}\|_2^2$
(`integral_specNorm_obliqueProjector_mul_one_sub_rangeProjector_mul_sq_le_div_card_of_hasLaw_gaussianMatrix`,
`sub_rsvd`, `Matrix.rank_le_card_width`), and
`NLAlib.integral_specNorm_mul_obliqueProjector_mul_sub_rsvd_mul_le_of_hasLaw_gaussianMatrix` with
$\mathbf{F} = \mathbf{P}_b - \mathbf{P}_a$, $\mathbf{T} = \mathbf{P}'_b - \mathbf{P}'_a$
(orthogonal projectors of rank $w \le b - a$, `IsStarProjection.frobNorm_sq_eq_rank`,
`IsStarProjection.specNorm_le_one`) gives $\mathbb{E}\mu \le 8\sqrt{w/p}\,\|\mathbf{E}\|_2$.
Finally $\theta\min(k, b - k)\sqrt{w} \le \theta\min(k, q)\sqrt{k + q} \le \sqrt2\,k\,\theta\sqrt q
\le 2\sqrt2\,k\,\|\mathbf{R} - \llbracket\mathbf{R}\rrbracket_k\|_{\mathsf{F}}$ with $q = b - k$
(window lemma; research note OP6, §4.4); collect constants. -/
theorem
    exists_forall_integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_of_gaussianMatrix :
    ∃ C : ℝ, 0 < C ∧ ∀ {m n l p : Type} [Fintype m] [Fintype n] [Fintype l] [Fintype p]
      (A : Matrix m n ℝ) (x : Matrix n l ℝ) (k : ℕ), 4 * Fintype.card l ≤ Fintype.card p →
      ∫ ψ, frobNorm (A - truncatedSVD (generalizedNystrom A x ψ) k) ^ 2 ∂(gaussianMatrix m p) ≤
        frobNorm (A - truncatedSVD (rsvd A x) k) ^ 2 +
          C * k * ((frobNorm (A - rsvd A x) ^ 2 +
              Fintype.card l * specNorm (A - rsvd A x) ^ 2) / Fintype.card p +
            specNorm (A - rsvd A x) * frobNorm (rsvd A x - truncatedSVD (rsvd A x) k) /
              √(Fintype.card p : ℝ)) := by
  refine ⟨12500, by norm_num, ?_⟩
  intro m n l p _ _ _ _ A x k hlp
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [truncatedSVD_zero]
  obtain ⟨a, b, hak, hkb, ha, ha₂, hb, hcount⟩ := exists_singularValues_window (rsvd A x) hk
  set R := rsvd A x
  set E := A - R
  set N : Matrix m p ℝ → Matrix m n ℝ := fun ψ => obliqueProjector (A * x) ψᴴ * E
  set Lw := rangeProjector (truncatedSVD R b) - rangeProjector (truncatedSVD R a)
  set Lw' := rangeProjector (truncatedSVD R b)ᴴ - rangeProjector (truncatedSVD R a)ᴴ
  set θ := singularValues R (k - 1) with hθ
  set γ := frobNorm (R - truncatedSVD R k) with hγ
  set P := Fintype.card p
  set L := Fintype.card l
  have hLs : specNorm Lw ≤ 2 := specNorm_rangeProjector_sub_rangeProjector_le_two _ _
  have hLs' : specNorm Lw' ≤ 2 := specNorm_rangeProjector_sub_rangeProjector_le_two _ _
  have hLf : frobNorm Lw ^ 2 ≤ 4 * b := frobNorm_rangeProjector_sub_rangeProjector_sq_le
    (rank_truncatedSVD_le _ _) ((rank_truncatedSVD_le _ _).trans hak |>.trans hkb)
  have hLf' : frobNorm Lw' ^ 2 ≤ 4 * b := frobNorm_rangeProjector_sub_rangeProjector_sq_le
    (by rw [Matrix.rank_conjTranspose]; exact rank_truncatedSVD_le _ _)
    (by rw [Matrix.rank_conjTranspose]; exact (rank_truncatedSVD_le _ _).trans hak |>.trans hkb)
  have hid : HasLaw (fun ψ : Matrix m p ℝ => ψ) (gaussianMatrix m p) (gaussianMatrix m p) :=
    HasLaw.id
  have hS := hasLaw_conjTranspose_of_hasLaw_gaussianMatrix hid
  have hr := Matrix.rank_le_card_width (A * x)
  have hη : Integrable (fun ψ => specNorm (N ψ) ^ 2) (gaussianMatrix m p) := by
    rcases Nat.eq_zero_or_pos (A * x).rank with h0 | hpos
    · simp only [N, Matrix.rank_eq_zero.mp h0, obliqueProjector, Matrix.zero_mul, specNorm_zero]
      exact integrable_const _
    · simp only [N, E, R, sub_rsvd]
      exact
        integrable_specNorm_obliqueProjector_mul_one_sub_rangeProjector_mul_sq_of_hasLaw_gaussianMatrix
          hS (A * x) (by omega) A
  have hEη : ∫ ψ, specNorm (N ψ) ^ 2 ∂(gaussianMatrix m p) ≤
      25 / (P : ℝ) * frobNorm E ^ 2 + 4 * (L : ℝ) / P * specNorm E ^ 2 := by
    have h :=
      integral_specNorm_obliqueProjector_mul_one_sub_rangeProjector_mul_sq_le_div_card_of_hasLaw_gaussianMatrix
        hS (A * x) (by omega) A
    rw [← sub_rsvd] at h
    refine h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)))
    have : ((A * x).rank : ℝ) ≤ L := by exact_mod_cast hr
    gcongr
  obtain ⟨hμ, hEμ⟩ := integral_specNorm_mul_obliqueProjector_mul_sub_rsvd_mul_le_div A x hlp
    hLs hLs' hη
  have hpt : ∀ᵐ ψ ∂(gaussianMatrix m p),
      frobNorm (A - truncatedSVD (generalizedNystrom A x ψ) k) ^ 2 ≤
        frobNorm (A - truncatedSVD R k) ^ 2 + 500 * k * specNorm (N ψ) ^ 2 +
          40 * θ * ((min k (b - k) : ℕ) : ℝ) * specNorm (Lw * N ψ * Lw') := by
    filter_upwards [ae_rank_conjTranspose_mul_eq_of_hasLaw_gaussianMatrix (A * x) hid
      (by omega)] with ψ hψ
    exact frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_window hψ hk hak hkb ha ha₂ hb
  have h1 : Integrable (fun ψ => frobNorm (A - truncatedSVD R k) ^ 2 +
      500 * k * specNorm (N ψ) ^ 2) (gaussianMatrix m p) :=
    (integrable_const _).add (hη.const_mul _)
  have hg : Integrable (fun ψ => frobNorm (A - truncatedSVD R k) ^ 2 +
      500 * k * specNorm (N ψ) ^ 2 + 40 * θ * ((min k (b - k) : ℕ) : ℝ) *
        specNorm (Lw * N ψ * Lw')) (gaussianMatrix m p) := h1.add (hμ.const_mul _)
  refine (integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _) hg hpt).trans ?_
  rw [integral_add h1 (hμ.const_mul _), integral_add (integrable_const _) (hη.const_mul _),
    integral_const, integral_const_mul, integral_const_mul, probReal_univ, one_smul]
  have hwin := mul_min_mul_le (k := k) (q := b - k) (singularValues_nonneg R (k - 1))
    (frobNorm_nonneg _) (add_nonneg (frobNorm_nonneg Lw) (frobNorm_nonneg Lw'))
    (by
      rw [Nat.cast_sub hkb, add_sub_cancel]
      nlinarith [sq_nonneg (frobNorm Lw - frobNorm Lw')]) hcount
  rw [← hθ, ← hγ] at hwin
  have hθ0 : 0 ≤ θ := singularValues_nonneg R (k - 1)
  have t1 := mul_le_mul_div_add_of_le (Nat.cast_nonneg (α := ℝ) k) (sq_nonneg (frobNorm E))
    (Nat.cast_nonneg (α := ℝ) L) (Nat.cast_nonneg (α := ℝ) P) hEη
  have t2 := mul_le_mul_div_sqrt_of_le hθ0 (Nat.cast_nonneg _) (specNorm_nonneg E)
    (Nat.cast_nonneg (α := ℝ) k) (frobNorm_nonneg _) hEμ hwin
  linarith

private theorem add_mul_div_sqrt_le {C a b e γ L P : ℝ} (hC : 0 ≤ C) (hL : 0 < L) (hP : 0 < P)
    (hγa : γ ^ 2 ≤ a) :
    a + C * ((b + L * e ^ 2) / P + e * γ / √P) ≤
      (1 + C / (2 * √L * √P)) * a + C / P * b + C * (L / P + √L / (2 * √P)) * e ^ 2 := by
  have hsL0 : 0 < √L := Real.sqrt_pos.mpr hL
  have hsP0 : 0 < √P := Real.sqrt_pos.mpr hP
  have hsL2 : √L ^ 2 = L := Real.sq_sqrt hL.le
  -- AM–GM: `e γ / √P ≤ (√L e² + γ² / √L) / (2√P)`, then `γ² ≤ a`
  have key : e * γ / √P ≤ √L * e ^ 2 / (2 * √P) + a / (2 * √L * √P) := by
    refine le_trans ?_ (add_le_add le_rfl (div_le_div_of_nonneg_right hγa (by positivity)))
    rw [div_add_div _ _ (by positivity) (by positivity), le_div_iff₀ (by positivity),
      show e * γ / √P * (2 * √P * (2 * √L * √P)) = 2 * √P * (2 * √L * e * γ) by field_simp]
    nlinarith [mul_nonneg hsP0.le (sq_nonneg (√L * e - γ))]
  have h2 := mul_le_mul_of_nonneg_left key hC
  have hH : (1 + C / (2 * √L * √P)) * a + C / P * b + C * (L / P + √L / (2 * √P)) * e ^ 2 =
      a + C * ((b + L * e ^ 2) / P) + C * (√L * e ^ 2 / (2 * √P) + a / (2 * √L * √P)) := by
    ring
  rw [hH]
  nlinarith

private theorem moments_le_add_mul {C₁ K L P T g u v w : ℝ} (hC₁ : 0 ≤ C₁) (hK : 0 ≤ K)
    (hL : 0 < L) (hP : 0 < P) (hT : 0 ≤ T) (hg : g ≤ 3 / 2) (hu : u ≤ g * T) (hv : v ≤ g * T)
    (hw : w ≤ 121 / L * T) :
    (1 + C₁ * K / (2 * √L * √P)) * u + C₁ * K / P * v +
        C₁ * K * (L / P + √L / (2 * √P)) * w ≤
      (g + 140 * C₁ * (K / P + K / √(L * P))) * T := by
  have hsL0 : 0 < √L := Real.sqrt_pos.mpr hL
  have hsP0 : 0 < √P := Real.sqrt_pos.mpr hP
  have hsL2 : √L ^ 2 = L := Real.sq_sqrt hL.le
  have e1 := mul_le_mul_of_nonneg_left hu (by positivity : 0 ≤ 1 + C₁ * K / (2 * √L * √P))
  have e2 := mul_le_mul_of_nonneg_left hv (by positivity : 0 ≤ C₁ * K / P)
  have e3 := mul_le_mul_of_nonneg_left hw
    (by positivity : 0 ≤ C₁ * K * (L / P + √L / (2 * √P)))
  have hc2 : C₁ * K * (L / P + √L / (2 * √P)) * (121 / L * T) =
      (121 * (C₁ * K / P) + 121 / 2 * (C₁ * K / (√L * √P))) * T := by
    rw [show (121 : ℝ) / L = 121 / √L ^ 2 by rw [hsL2], show L / P = √L ^ 2 / P by rw [hsL2]]
    field_simp
  have hx : 0 ≤ C₁ * K / (√L * √P) * T := by positivity
  have hy : 0 ≤ C₁ * K / P * T := by positivity
  have h0 : (1 + C₁ * K / (2 * √L * √P)) * (g * T) =
      g * T + g * (C₁ * K / (√L * √P) * T) / 2 := by
    field_simp
  have h1 : C₁ * K / P * (g * T) = g * (C₁ * K / P * T) := by ring
  have h2 : (g + 140 * C₁ * (K / P + K / √(L * P))) * T =
      g * T + 140 * (C₁ * K / P * T) + 140 * (C₁ * K / (√L * √P) * T) := by
    rw [Real.sqrt_mul hL.le]
    ring
  rw [h2]
  nlinarith [mul_le_mul_of_nonneg_right hg hx, mul_le_mul_of_nonneg_right hg hy]

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The expected error of truncated generalized Nyström, sketch sizes $O(k/\varepsilon)$**: there
is an absolute constant $C > 0$ such that for independent standard Gaussian test matrices
$\mathbf{\Omega}$ ($n \times \ell$) and $\mathbf{\Psi}$ ($m \times p$) with $4k \le \ell$ and
$4\ell \le p$,
$$\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})
\rrbracket_k\|_{\mathsf{F}}^2 \le \Bigl(1 + \frac{k}{\ell - k - 1} +
C\Bigl(\frac{k}{p} + \frac{k}{\sqrt{\ell p}}\Bigr)\Bigr)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,.$$
$O(1)$ suffices for $C$. For the choice `truncatedSVD` makes. Every rank of $\mathbf{A}$.
No printed source. New (maintainer's derivation (1); research note OP6, Theorem (1), there with
$\ell \ge 6k$, $p \ge 2\ell + 2$ and explicit constants).
Proof: M, about 80 lines. $k = 0$: `truncatedSVD_zero`, `one_le_gaussianProjectionFactor`-type
bound ($\ge 1$). Otherwise take $C_1$ from
`NLAlib.exists_forall_integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_of_gaussianMatrix`
and integrate it over $\mathbf{\Omega}$ with `IndepFun.integral_comp_le_of_integral_le` (the
pattern of the library's
`integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_of_hasLaw_gaussianMatrix`;
measurability from `measurable_truncatedSVD`, `measurable_generalizedNystrom`, `measurable_rsvd`,
`continuous_frobNorm`, `continuous_specNorm`; the per-$\mathbf{x}$ integrability from
`integrable_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_of_hasLaw_gaussianMatrix`). Moments:
`integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_hasLaw_gaussianMatrix` (the joint baseline
$\mathbb{E}\|\mathbf{A} - \llbracket\mathbf{R}\rrbracket_k\|^2 \le gT$),
`integral_frobNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix` ($\le gT$),
`NLAlib.integral_specNorm_sub_rsvd_sq_le_div_of_hasLaw_gaussianMatrix` ($\le 121T/\ell$), and for
the product Cauchy–Schwarz (`integral_mul_le_Lp_mul_Lq_of_nonneg` at $p = q = 2$, or AM–GM
pointwise $xy \le (\lambda x^2 + y^2/\lambda)/2$ with $\lambda = \sqrt{\ell/(121g)}$-type
choice) with $\|\mathbf{R} - \llbracket\mathbf{R}\rrbracket_k\|^2 \le
\|\mathbf{A} - \llbracket\mathbf{R}\rrbracket_k\|^2$ (`frobNorm_sub_truncatedSVD_rsvd_sq`);
integrability of the conditional bound: `integrable_frobNorm_sub_rsvd_sq`,
`integrable_specNorm_sub_rsvd_sq`, `integrable_frobNorm_sub_truncatedSVD_rsvd_sq`, and the product
dominated by the sum of squares. With $g = $ `gaussianProjectionFactor` $\le 3/2$ for $4k \le
\ell$ the result holds with $C = 140\,C_1$. -/
theorem
    exists_forall_integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_of_hasLaw_gaussianMatrix :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω m n l p : Type} [MeasurableSpace Ω] [Fintype m] [Fintype n]
      [Fintype l] [Fintype p] (μ : Measure Ω) (A : Matrix m n ℝ) (X : Ω → Matrix n l ℝ)
      (Ψ : Ω → Matrix m p ℝ) (k : ℕ),
      HasLaw X (gaussianMatrix n l) μ → HasLaw Ψ (gaussianMatrix m p) μ → IndepFun X Ψ μ →
      4 * k ≤ Fintype.card l → 4 * Fintype.card l ≤ Fintype.card p →
      ∫ ω, frobNorm (A - truncatedSVD (generalizedNystrom A (X ω) (Ψ ω)) k) ^ 2 ∂μ ≤
        (gaussianProjectionFactor k (Fintype.card l) +
            C * ((k : ℝ) / Fintype.card p +
              (k : ℝ) / √((Fintype.card l : ℝ) * Fintype.card p))) *
          frobNorm (A - truncatedSVD A k) ^ 2 := by
  obtain ⟨C₁, hC₁, hcond⟩ :=
    exists_forall_integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_of_gaussianMatrix
  refine ⟨140 * C₁, by positivity, ?_⟩
  intro Ω m n l p _ _ _ _ _ μ A X Ψ k hX hΨ hXΨ hkl hlp
  have := hX.isProbabilityMeasure
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · subst hk0
    simp [truncatedSVD_zero]
  set L := Fintype.card l with hLdef
  set P := Fintype.card p with hPdef
  have hL0 : (0 : ℝ) < L := by have : 0 < L := by omega
                               exact_mod_cast this
  have hP0 : (0 : ℝ) < P := by have : 0 < P := by omega
                               exact_mod_cast this
  -- coefficients of the linear majorant of the conditional bound
  set c₀ := 1 + C₁ * k / (2 * √(L : ℝ) * √(P : ℝ)) with hc₀
  set c₁ := C₁ * k / P with hc₁
  set c₂ := C₁ * k * (L / P + √(L : ℝ) / (2 * √(P : ℝ))) with hc₂
  set H : Matrix n l ℝ → ℝ := fun x => c₀ * frobNorm (A - truncatedSVD (rsvd A x) k) ^ 2 +
    c₁ * frobNorm (A - rsvd A x) ^ 2 + c₂ * specNorm (A - rsvd A x) ^ 2 with hHdef
  have hid : HasLaw (fun ψ : Matrix m p ℝ => ψ) (gaussianMatrix m p) (gaussianMatrix m p) :=
    HasLaw.id
  have hint (x : Matrix n l ℝ) : Integrable (fun ψ : Matrix m p ℝ =>
      frobNorm (A - truncatedSVD (generalizedNystrom A x ψ) k) ^ 2) (gaussianMatrix m p) :=
    integrable_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_of_hasLaw_gaussianMatrix
      (X := fun _ => x) A aemeasurable_const hid (indepFun_const_left x _) (by omega) k
  have hle (x : Matrix n l ℝ) : ∫ ψ, frobNorm (A - truncatedSVD (generalizedNystrom A x ψ) k) ^ 2
      ∂(gaussianMatrix m p) ≤ H x := by
    refine (hcond A x k hlp).trans (add_mul_div_sqrt_le (by positivity) hL0 hP0 ?_)
    rw [frobNorm_sub_truncatedSVD_rsvd_sq]
    linarith [sq_nonneg (frobNorm (A - rsvd A x))]
  have hU := (integrable_frobNorm_sub_truncatedSVD_rsvd_sq A hX.aemeasurable k).const_mul c₀
  have hE := (integrable_frobNorm_sub_rsvd_sq A hX.aemeasurable).const_mul c₁
  have hS := (integrable_specNorm_sub_rsvd_sq A hX.aemeasurable).const_mul c₂
  have hUE : Integrable (fun ω => c₀ * frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 +
      c₁ * frobNorm (A - rsvd A (X ω)) ^ 2) μ := hU.add hE
  have hF : Measurable fun q : Matrix n l ℝ × Matrix m p ℝ =>
      frobNorm (A - truncatedSVD (generalizedNystrom A q.1 q.2) k) ^ 2 :=
    (continuous_frobNorm.measurable.comp (measurable_const.sub
      ((measurable_truncatedSVD k).comp (measurable_generalizedNystrom A)))).pow_const 2
  refine (hXΨ.integral_comp_le_of_integral_le hX.aemeasurable hΨ hF (fun _ => sq_nonneg _)
    (ae_of_all _ fun ω => hint (X ω)) (ae_of_all _ fun ω => hle (X ω)) (hUE.add hS)).trans ?_
  simp only [hHdef]
  rw [integral_add hUE hS, integral_add hU hE, integral_const_mul, integral_const_mul,
    integral_const_mul]
  have hk2 : k + 2 ≤ L := by omega
  have hg : gaussianProjectionFactor k L ≤ 3 / 2 := by
    have h4 : (4 : ℝ) * k ≤ L := by exact_mod_cast hkl
    have h1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have : (k : ℝ) / (L - k - 1) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    rw [gaussianProjectionFactor_def]
    linarith
  exact moments_le_add_mul hC₁.le k.cast_nonneg hL0 hP0 (sq_nonneg _) hg
    (integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_hasLaw_gaussianMatrix A hX hk2)
    (integral_frobNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix A hX hk2)
    (integral_specNorm_sub_rsvd_sq_le_div_of_hasLaw_gaussianMatrix A hX hk hkl)

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **Truncated generalized Nyström reaches relative error $1 + \varepsilon$ with
$O(k/\varepsilon)$ samples**: there is an absolute constant $C > 0$ such that for independent
standard Gaussian test matrices $\mathbf{\Omega}$ ($n \times \ell$) and $\mathbf{\Psi}$
($m \times p$), $0 < \varepsilon \le 1$, $\ell \ge Ck/\varepsilon$ and $p \ge 4\ell$,
$$\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})
\rrbracket_k\|_{\mathsf{F}}^2 \le (1 + \varepsilon)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,.$$
$O(k/\varepsilon)$ suffices for both sketch sizes, against $p = O(k/\varepsilon^2)$ in
`integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_one_add_mul_of_hasLaw_gaussianMatrix`.
For the choice `truncatedSVD` makes. No printed source. New (research note OP6, §6).
Proof: S, about 40 lines. Take $C_1$ from
`NLAlib.exists_forall_integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_of_hasLaw_gaussianMatrix`
and $C = 4 + 2C_1$. $k = 0$ is trivial. Otherwise $4k \le \ell$ ($C \ge 4$, $\varepsilon \le 1$),
$k/(\ell - k - 1) \le 2k/\ell \le 2\varepsilon/C$ (`gaussianProjectionFactor_def`, $\ell \ge 4$),
$k/p \le k/(4\ell)$, $k/\sqrt{\ell p} \le k/(2\ell)$ (`Real.sqrt_le_sqrt`, `Real.sqrt_mul_self`),
so the factor is at most $1 + \varepsilon(2 + \tfrac34 C_1)/C \le 1 + \varepsilon$;
`mul_le_mul_of_nonneg_right`. -/
theorem
    exists_forall_integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_one_add_of_hasLaw_gaussianMatrix :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω m n l p : Type} [MeasurableSpace Ω] [Fintype m] [Fintype n]
      [Fintype l] [Fintype p] (μ : Measure Ω) (A : Matrix m n ℝ) (X : Ω → Matrix n l ℝ)
      (Ψ : Ω → Matrix m p ℝ) (k : ℕ) (ε : ℝ),
      HasLaw X (gaussianMatrix n l) μ → HasLaw Ψ (gaussianMatrix m p) μ → IndepFun X Ψ μ →
      0 < ε → ε ≤ 1 → C * k ≤ ε * Fintype.card l → 4 * Fintype.card l ≤ Fintype.card p →
      ∫ ω, frobNorm (A - truncatedSVD (generalizedNystrom A (X ω) (Ψ ω)) k) ^ 2 ∂μ ≤
        (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  obtain ⟨C₁, hC₁, hM⟩ :=
    exists_forall_integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_of_hasLaw_gaussianMatrix
  refine ⟨4 + 2 * C₁, by positivity, ?_⟩
  intro Ω m n l p _ _ _ _ _ μ A X Ψ k ε hX hΨ hXΨ hε hε1 hkl hlp
  have hF : 0 ≤ frobNorm (A - truncatedSVD A k) ^ 2 := by positivity
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h1 : gaussianProjectionFactor 0 (Fintype.card l) = 1 := by
      simp [gaussianProjectionFactor_def]
    have hM0 := hM μ A X Ψ 0 hX hΨ hXΨ (by simp) hlp
    refine hM0.trans (mul_le_mul_of_nonneg_right (by rw [h1]; simp; linarith) hF)
  · have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
    have hk1' : 1 ≤ k := hk
    have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk1'
    have hL0 : (0:ℝ) ≤ Fintype.card l := Nat.cast_nonneg _
    have hkl' : (4 + 2 * C₁) * (k:ℝ) ≤ ε * (Fintype.card l : ℝ) := hkl
    have h4k : 4 * (k:ℝ) ≤ Fintype.card l := by
      nlinarith [mul_nonneg hC₁.le hk0, mul_nonneg (sub_nonneg.2 hε1) hL0]
    have h4k' : 4 * k ≤ Fintype.card l := by exact_mod_cast h4k
    have hlp' : 4 * (Fintype.card l : ℝ) ≤ Fintype.card p := by exact_mod_cast hlp
    have hL : (4:ℝ) ≤ Fintype.card l := by linarith
    have hLpos : (0:ℝ) < Fintype.card l := by linarith
    have hM' := hM μ A X Ψ k hX hΨ hXΨ h4k' hlp
    have hfac : gaussianProjectionFactor k (Fintype.card l) ≤
        1 + 2 * ((k:ℝ) / Fintype.card l) := by
      rw [gaussianProjectionFactor_def]
      have hden : (Fintype.card l : ℝ) / 2 ≤ (Fintype.card l : ℝ) - k - 1 := by linarith
      have h2 : (k:ℝ) / ((Fintype.card l : ℝ) - k - 1) ≤ (k:ℝ) / ((Fintype.card l : ℝ) / 2) :=
        div_le_div_of_nonneg_left hk0 (by linarith) hden
      have h3 : (k:ℝ) / ((Fintype.card l : ℝ) / 2) = 2 * ((k:ℝ) / Fintype.card l) := by
        ring
      linarith
    have hr0 : (0:ℝ) ≤ (k:ℝ) / Fintype.card l := div_nonneg hk0 hL0
    have hkr : (4 + 2 * C₁) * ((k:ℝ) / Fintype.card l) ≤ ε := by
      rw [mul_div_assoc', div_le_iff₀ hLpos]
      linarith
    have hsq : 2 * (Fintype.card l : ℝ) ≤ √((Fintype.card l : ℝ) * Fintype.card p) := by
      calc 2 * (Fintype.card l : ℝ) = √((2 * Fintype.card l : ℝ) ^ 2) :=
            (Real.sqrt_sq (by linarith)).symm
        _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [mul_le_mul_of_nonneg_left hlp' hL0])
    have e1 : (k:ℝ) / Fintype.card p ≤ (k:ℝ) / Fintype.card l / 4 := by
      calc (k:ℝ) / Fintype.card p ≤ (k:ℝ) / (Fintype.card l * 4) :=
            div_le_div_of_nonneg_left hk0 (by linarith) (by linarith)
        _ = _ := by ring
    have e2 : (k:ℝ) / √((Fintype.card l : ℝ) * Fintype.card p) ≤
        (k:ℝ) / Fintype.card l / 2 := by
      calc (k:ℝ) / √((Fintype.card l : ℝ) * Fintype.card p) ≤
            (k:ℝ) / (2 * Fintype.card l) :=
            div_le_div_of_nonneg_left hk0 (by linarith) hsq
        _ = _ := by ring
    have hfin : gaussianProjectionFactor k (Fintype.card l) +
        C₁ * ((k:ℝ) / Fintype.card p + (k:ℝ) / √((Fintype.card l : ℝ) * Fintype.card p)) ≤
        1 + ε := by
      have := mul_le_mul_of_nonneg_left (add_le_add e1 e2) hC₁.le
      nlinarith [mul_nonneg hC₁.le hr0]
    exact hM'.trans (mul_le_mul_of_nonneg_right hfin hF)

end NLAlib
