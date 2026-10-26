/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Gaussian.RangeFinder

/-!
# The spectral residual of the Gaussian range finder at a comparison rank (research)

For a standard Gaussian $n \times \ell$ test matrix, $1 \le k$ and $4k \le \ell$, the second
spectral moment of the range-finder residual is $O(1/\ell)$ times the optimal Frobenius error:
$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_2^2 \le
(121/\ell)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$. The library proves it
as a private step of `NLAlib/LowRank/Gaussian/TruncatedGeneralizedNystrom.lean`; the upper bound
of `docs/design/research/TruncatedGN-Upper.md` (R1) needs it public. Joins
`NLAlib/LowRank/Gaussian/RangeFinder.lean`. Not for `main`. Proofs deferred.

## Main results

* `NLAlib.integral_specNorm_sub_rsvd_sq_le_div_of_hasLaw_gaussianMatrix` (R1).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n l : Type*} [Fintype m]
  [Fintype n] [Fintype l] {X : Ω → Matrix n l ℝ}

/-- The arithmetic of the spectral residual: from $\ell\sigma^2 \le 4\,\mathrm{OPT}^2$,
$w \le \mathrm{OPT}$, $h \le 3$ and $\ell\beta^2 \le 32.4$ with $\ell \ge 4$, the second-moment
bound $\sigma^2 + (\sigma\sqrt h + \beta w)^2 + \sigma^2\beta^2$ is at most
$(121/\ell)\mathrm{OPT}^2$. -/
private theorem residual_arith_rf {L u w O h β : ℝ} (hL : 4 ≤ L) (hw0 : 0 ≤ w)
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
private theorem div_le_three_of_half_rf {L j : ℕ} (hL : 4 ≤ L) (hj : j = (L + 1) / 2) :
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
private theorem mul_gaussianPinvSpecNormBound_sq_le_of_half_rf {L j : ℕ} (hL : 4 ≤ L)
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

/-- The spectral residual of the range finder, at comparison rank $\lceil \ell/2 \rceil$ and
tail flattening (private copy of the library's step). -/
private theorem integral_specNorm_sub_rsvd_sq_le_div_rf (A : Matrix m n ℝ)
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
  exact residual_arith_rf hL' (frobNorm_nonneg _) hw hu
    (div_nonneg (Nat.cast_nonneg _) (by
      have : (j : ℝ) + 2 ≤ L := by exact_mod_cast hj2
      linarith))
    (div_le_three_of_half_rf hL4 rfl) (mul_gaussianPinvSpecNormBound_sq_le_of_half_rf hL4 rfl)

/-- **The spectral residual of the range finder is $O(1/\ell)$ of the optimal Frobenius
error**: for a standard Gaussian test matrix $\mathbf{\Omega} \in \mathbb{R}^{n \times \ell}$,
$1 \le k$ and $4k \le \ell$,
$$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_2^2 \le
\frac{121}{\ell}\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,.$$
No printed source; the comparison-rank argument of [HalkoMartinssonTropp2011, Theorem 10.6].
Proof: S, about 90 lines, copied. The private lemma integral_specNorm_sub_rsvd_sq_le_div of
`NLAlib/LowRank/Gaussian/TruncatedGeneralizedNystrom.lean` is this statement; copy it and its
three private helpers (residual_arith, div_le_three_of_half,
mul_gaussianPinvSpecNormBound_sq_le_of_half) as private lemmas here. They use
`integral_specNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix_pinvSpecNormBound` at the comparison
rank $\lceil\ell/2\rceil$, `natCast_mul_singularValues_add_sq_le_frobNorm_sub_truncatedSVD_sq`,
`frobNorm_sub_truncatedSVD_sq` and `gaussianPinvSpecNormBound_def`. -/
theorem integral_specNorm_sub_rsvd_sq_le_div_of_hasLaw_gaussianMatrix (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ} (hk : 1 ≤ k) (hkl : 4 * k ≤ Fintype.card l) :
    ∫ ω, specNorm (A - rsvd A (X ω)) ^ 2 ∂μ ≤
      121 / (Fintype.card l : ℝ) * frobNorm (A - truncatedSVD A k) ^ 2 :=
  integral_specNorm_sub_rsvd_sq_le_div_rf A hX hk hkl

end NLAlib
