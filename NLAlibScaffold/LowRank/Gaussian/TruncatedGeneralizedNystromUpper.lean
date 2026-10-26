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
  sorry

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
  sorry

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
