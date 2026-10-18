/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Gaussian.BlockKrylovGapless
public import NLAlib.LowRank.Gaussian.Nystrom

/-!
# Block Krylov and subspace iteration Nyström with a Gaussian test matrix

Expected errors of block Krylov Nyström $\mathsf{nystromBKI}(\mathbf{H}, \mathbf{X}, q)$ and of
Nyström subspace iteration with $p$ power steps, $\mathsf{nystrom}(\mathbf{H},
\mathbf{H}^p\mathbf{X})$, for positive semidefinite $\mathbf{H}$ and a standard Gaussian
$n \times \ell$ test matrix $\mathbf{X}$. Every bound comes from the Gram correspondence
(`Matrix.PosSemidef.sub_nystromBKI_eq`, `Matrix.PosSemidef.sub_nystrom_eq`): the Nyström error of
$\mathbf{H}$ is the Gram matrix of the RBKI (respectively RSI) error of
$\mathbf{F} = \mathbf{H}^{1/2}$, with $\sigma_i(\mathbf{F})^2 = \sigma_i(\mathbf{H})$,
$\|\mathbf{F} - \llbracket\mathbf{F}\rrbracket_t\|_{\mathsf{F}}^2 =
\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_t\|_*$, and relative gap of $\mathbf{F}$ at least
half that of $\mathbf{H}$. The statements are in the Nyström-native shape of Tropp and Webber's
Corollary 8.2: unsquared spectral error, nuclear tail.

Comparison with the printed lines: Tropp and Webber's Theorem 9.2 states NysBKI for
$\mathbb{E}\|\mathbf{H} - \hat{\mathbf{H}}\|_p^2$ with a squared Frobenius tail and exponent
$4(m - 3/2)\sqrt{2\gamma}$, and Theorem 9.1 with rate $1/(8(m - 3/2)^2)$; the statements here are
the Nyström-native shape obtained from the RBKI lines at $\mathbf{H}^{1/2}$, with exponent
$4\sqrt{2}(q - 1)\sqrt{\gamma}$ and rate $1/(16(q-1)^2)$. The two shapes are incomparable.

## Main results

In the `Matrix.PosSemidef` namespace:
* `integral_specNorm_sub_nystromBKI_le_singularGapRatio_of_hasLaw_gaussianMatrix`,
  `integral_specNorm_sub_nystrom_pow_mul_le_singularGapRatio_of_hasLaw_gaussianMatrix`: gapped
  bounds.
* `integral_specNorm_sub_nystromBKI_le_one_add_sq_mul_of_hasLaw_gaussianMatrix`,
  `integral_specNorm_sub_nystrom_pow_mul_le_one_add_sq_mul_of_hasLaw_gaussianMatrix`: gapless
  bounds, $(1 + \varepsilon)$ form.
* `integral_specNorm_sub_nystromBKI_le_mul_exp_of_hasLaw_gaussianMatrix`,
  `integral_specNorm_sub_nystrom_pow_mul_le_mul_rpow_of_hasLaw_gaussianMatrix`: gapless bounds,
  Tropp and Webber's form, with `rangeFinderTailRatio_sqrt`.
* the late-truncated outputs, trace norm:
  `integral_nuclearNorm_sub_truncatedSVD_nystromBKI_le_singularGapRatio_of_hasLaw_gaussianMatrix`,
`integral_nuclearNorm_sub_truncatedSVD_nystrom_pow_mul_le_singularGapRatio_of_hasLaw_gaussianMatrix`
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal MatrixOrder

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n l : Type*} [Fintype n]
  [Fintype l] {X : Ω → Matrix n l ℝ} {H : Matrix n n ℝ}

-- Stage B7

/-! ### The tail ratio of the square root -/

open scoped Classical in
/-- The range-finder tail ratio of $\mathbf{H}^{1/2}$ in terms of $\mathbf{H}$: for positive
semidefinite $\mathbf{H}$, <!-- value rangeFinderTailRatio \mathbf{H}^{1/2} r \ell -->
$$1 + \frac{r}{\ell - r - 1}\,
\frac{\|\mathbf{H}^{1/2} - \llbracket\mathbf{H}^{1/2}\rrbracket_r\|_{\mathsf{F}}^2}
{\sigma_r(\mathbf{H}^{1/2})^2} = 1 + \frac{r}{\ell - r - 1}\,
\frac{\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_r\|_*}{\sigma_r(\mathbf{H})}\,,$$
the Nyström-native ratio of the gapless Nyström bounds. -/
theorem _root_.Matrix.PosSemidef.rangeFinderTailRatio_sqrt (hH : H.PosSemidef) (r l : ℕ) :
    rangeFinderTailRatio (CFC.sqrt H) r l =
      1 + (r : ℝ) / ((l : ℝ) - r - 1) * nuclearNorm (H - truncatedSVD H r) /
        singularValues H r := by
  rw [rangeFinderTailRatio, hH.frobNorm_sqrt_sub_truncatedSVD_sq, hH.sq_singularValues_sqrt]

open scoped Classical in
/-- Positivity of $\sigma_r(\mathbf{H})$ passes to $\sigma_r(\mathbf{H}^{1/2})$. -/
private theorem singularValues_sqrt_pos (hH : H.PosSemidef) {r : ℕ}
    (hσ : 0 < singularValues H r) : 0 < singularValues (CFC.sqrt H) r := by
  refine (singularValues_nonneg _ r).lt_of_ne fun h => ?_
  rw [← hH.sq_singularValues_sqrt, ← h] at hσ
  norm_num at hσ

/-- The tail weight $t/(\ell - t - 1)$ is nonnegative for $t + 2 \le \ell$. -/
private theorem div_card_sub_nonneg {t : ℕ} (ht : t + 2 ≤ Fintype.card l) :
    0 ≤ (t : ℝ) / ((Fintype.card l : ℝ) - t - 1) := by
  have : (t : ℝ) + 2 ≤ Fintype.card l := by exact_mod_cast ht
  exact div_nonneg (Nat.cast_nonneg t) (by linarith)

/-! ### Spectral errors through the square root -/

-- `CFC.sqrt` takes the `DecidableEq` instance only inside a proof argument, so the statements above
-- are stated under `Classical` and rewrite every spelling of `CFC.sqrt H`.
variable [DecidableEq n]

/-- The Gram correspondence in the spectral norm: the spectral error of NysBKI is the squared
spectral error of RBKI of the square root. -/
private theorem specNorm_sub_nystromBKI_eq (hH : H.PosSemidef) (Y : Matrix n l ℝ) (q : ℕ) :
    specNorm (H - nystromBKI H Y q) = specNorm (CFC.sqrt H - rbki (CFC.sqrt H) Y q) ^ 2 := by
  rw [hH.sub_nystromBKI_eq, specNorm_conjTranspose_mul_self]

/-- The same for NysSI and RSI of the square root, at the test matrix $\mathbf{H}^p\mathbf{Y}$. -/
private theorem specNorm_sub_nystrom_pow_mul_eq (hH : H.PosSemidef) (Y : Matrix n l ℝ) (p : ℕ) :
    specNorm (H - nystrom H (H ^ p * Y)) =
      specNorm (CFC.sqrt H - rsvd (CFC.sqrt H) (H ^ p * Y)) ^ 2 := by
  rw [hH.sub_nystrom_eq, specNorm_conjTranspose_mul_self]

/-! ### Gapped bounds -/

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The gapped bound for block Krylov Nyström**: for positive semidefinite $\mathbf{H}$, a
standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$, $q \ge 1$ blocks, a head of
$r = h + 1$ eigenvalues, a tail index $t \ge r$ with $t + 2 \le \ell$, and
$\gamma = (\sigma_h(\mathbf{H}) - \sigma_t(\mathbf{H}))/(\sigma_h(\mathbf{H}) + \sigma_t(\mathbf{H}))$,
$$\mathbb{E}\|\mathbf{H} - \mathsf{nystromBKI}(\mathbf{H}, \mathbf{X}, q)\|_2 \le
\sigma_r(\mathbf{H}) + 4e^{-4\sqrt{2}(q-1)\sqrt{\gamma}}\,\frac{t}{\ell - t - 1}
\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_t\|_*\,.$$
By the Gram correspondence from the RBKI bound at $\mathbf{H}^{1/2}$
(`NLAlib.integral_specNorm_sub_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix`), whose gap is
at least $\gamma/2$. [TroppWebber2023, Theorem 9.2 (NysBKI)]; there for
$\mathbb{E}\|\mathbf{H} - \hat{\mathbf{H}}\|_p^2$ with a squared Frobenius tail and exponent
$4(m - 3/2)\sqrt{2\gamma}$ for $m = q$ products; this statement is the Nyström-native shape of TW
Corollary 8.2, obtained from the RBKI line at $\mathbf{H}^{1/2}$; the two are incomparable.
Result: nysbki-gapped-error -/
theorem
_root_.Matrix.PosSemidef.integral_specNorm_sub_nystromBKI_le_singularGapRatio_of_hasLaw_gaussianMatrix
    (hH : H.PosSemidef) (hX : HasLaw X (gaussianMatrix n l) μ) {h r t q : ℕ} (hr : h + 1 = r)
    (hrt : r ≤ t) (ht : t + 2 ≤ Fintype.card l) (hq : 1 ≤ q) :
    ∫ ω, specNorm (H - nystromBKI H (X ω) q) ∂μ ≤
      singularValues H r +
        4 * Real.exp (-4 * Real.sqrt 2 * ((q : ℝ) - 1) * Real.sqrt (singularGapRatio H h t)) *
          ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) * nuclearNorm (H - truncatedSVD H t) := by
  have hht : h ≤ t := by omega
  have hq1 : (0 : ℝ) ≤ (q : ℝ) - 1 := by
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hgap := hH.singularGapRatio_le_two_mul_singularGapRatio_sqrt hht
  have hγ : Real.sqrt 2 * Real.sqrt (singularGapRatio H h t) ≤
      2 * Real.sqrt (singularGapRatio (CFC.sqrt H) h t) := by
    rw [← Real.sqrt_mul zero_le_two]
    calc Real.sqrt (2 * singularGapRatio H h t)
        ≤ Real.sqrt (2 ^ 2 * singularGapRatio (CFC.sqrt H) h t) :=
          Real.sqrt_le_sqrt (by linarith)
      _ = 2 * Real.sqrt (singularGapRatio (CFC.sqrt H) h t) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq zero_le_two]
  have hexp : Real.exp (-8 * ((q : ℝ) - 1) * Real.sqrt (singularGapRatio (CFC.sqrt H) h t)) ≤
      Real.exp (-4 * Real.sqrt 2 * ((q : ℝ) - 1) * Real.sqrt (singularGapRatio H h t)) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hγ hq1])
  simp only [specNorm_sub_nystromBKI_eq hH]
  refine (integral_specNorm_sub_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix
    (CFC.sqrt H) hX hr hrt ht hq).trans ?_
  rw [hH.sq_singularValues_sqrt, hH.frobNorm_sqrt_sub_truncatedSVD_sq]
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hexp zero_le_four) (div_card_sub_nonneg ht))
    (nuclearNorm_nonneg (H - truncatedSVD H t))
  linarith

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The gapped bound for Nyström subspace iteration**: for positive semidefinite $\mathbf{H}$, a
standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$, $p$ power steps, a head of $r = h + 1$
eigenvalues, a tail index $t \ge r$ with $t + 2 \le \ell$, and the relative gap $\gamma$ of
$\sigma_h(\mathbf{H})$ and $\sigma_t(\mathbf{H})$,
$$\mathbb{E}\|\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{H}^p\mathbf{X})\|_2 \le
\sigma_r(\mathbf{H}) + e^{-4p\gamma}\,\frac{t}{\ell - t - 1}
\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_t\|_*\,.$$
By the Gram correspondence from the RSI bound at $\mathbf{H}^{1/2}$.
[TroppWebber2023, Theorem 9.2 (NysSI)]; there for $\mathbb{E}\|\mathbf{H} - \hat{\mathbf{H}}\|_p^2$
with a squared Frobenius tail and exponent $4(m - 3/2)\gamma$ for $m = p + 1$ products; this
statement is the Nyström-native shape of TW Corollary 8.2; the two are incomparable.
Result: nyssi-gapped-error -/
theorem
_root_.Matrix.PosSemidef.integral_specNorm_sub_nystrom_pow_mul_le_singularGapRatio_of_hasLaw_gaussianMatrix
    (hH : H.PosSemidef) (hX : HasLaw X (gaussianMatrix n l) μ) {h r t : ℕ} (hr : h + 1 = r)
    (hrt : r ≤ t) (ht : t + 2 ≤ Fintype.card l) (p : ℕ) :
    ∫ ω, specNorm (H - nystrom H (H ^ p * X ω)) ∂μ ≤
      singularValues H r +
        Real.exp (-4 * (p : ℝ) * singularGapRatio H h t) *
          ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) * nuclearNorm (H - truncatedSVD H t) := by
  have hgap := hH.singularGapRatio_le_two_mul_singularGapRatio_sqrt (show h ≤ t by omega)
  have hexp : Real.exp (-8 * (p : ℝ) * singularGapRatio (CFC.sqrt H) h t) ≤
      Real.exp (-4 * (p : ℝ) * singularGapRatio H h t) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hgap (Nat.cast_nonneg (α := ℝ) p)])
  have hb := integral_specNorm_sub_rsvd_pow_mul_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix
    (CFC.sqrt H) hX hr hrt ht p
  rw [hH.conjTranspose_sqrt_mul_sqrt, hH.sq_singularValues_sqrt,
    hH.frobNorm_sqrt_sub_truncatedSVD_sq] at hb
  simp only [specNorm_sub_nystrom_pow_mul_eq hH]
  refine hb.trans ?_
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hexp (div_card_sub_nonneg ht))
    (nuclearNorm_nonneg (H - truncatedSVD H t))
  linarith

/-! ### Gapless bounds -/

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The gapless bound for block Krylov Nyström, $(1 + \varepsilon)$ form**: for positive
semidefinite $\mathbf{H}$, a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$, $q \ge 1$
blocks, a target rank $r$ with $r + 2 \le \ell$ and every $\varepsilon > 0$,
$$\mathbb{E}\|\mathbf{H} - \mathsf{nystromBKI}(\mathbf{H}, \mathbf{X}, q)\|_2 \le
(1 + \varepsilon)^2\sigma_r(\mathbf{H}) +
4e^{-8(q-1)\sqrt{\varepsilon/(2 + \varepsilon)}}\,\frac{r}{\ell - r - 1}
\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_r\|_*\,.$$
By the Gram correspondence from
`NLAlib.integral_specNorm_sub_rbki_sq_le_one_add_sq_mul_of_hasLaw_gaussianMatrix` at
$\mathbf{H}^{1/2}$. [MuscoMusco2015, Theorem 10 (proof)]; [TroppWebber2023, Theorem 9.2]; constants
composed here.
Result: nysbki-gapless-error -/
theorem
_root_.Matrix.PosSemidef.integral_specNorm_sub_nystromBKI_le_one_add_sq_mul_of_hasLaw_gaussianMatrix
    (hH : H.PosSemidef) (hX : HasLaw X (gaussianMatrix n l) μ) {r q : ℕ}
    (hr : r + 2 ≤ Fintype.card l) (hq : 1 ≤ q) {ε : ℝ} (hε : 0 < ε) :
    ∫ ω, specNorm (H - nystromBKI H (X ω) q) ∂μ ≤
      (1 + ε) ^ 2 * singularValues H r +
        4 * Real.exp (-8 * ((q : ℝ) - 1) * Real.sqrt (ε / (2 + ε))) *
          ((r : ℝ) / ((Fintype.card l : ℝ) - r - 1)) * nuclearNorm (H - truncatedSVD H r) := by
  simp only [specNorm_sub_nystromBKI_eq hH]
  have hb := integral_specNorm_sub_rbki_sq_le_one_add_sq_mul_of_hasLaw_gaussianMatrix
    (CFC.sqrt H) hX hr hq hε
  rwa [hH.sq_singularValues_sqrt, hH.frobNorm_sqrt_sub_truncatedSVD_sq] at hb

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The gapless bound for Nyström subspace iteration, $(1 + \varepsilon)$ form**: for positive
semidefinite $\mathbf{H}$, a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$, $p$ power
steps, a target rank $r$ with $r + 2 \le \ell$ and every $\varepsilon > 0$,
$$\mathbb{E}\|\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{H}^p\mathbf{X})\|_2 \le
(1 + \varepsilon)^2\sigma_r(\mathbf{H}) +
e^{-8p\varepsilon/(2 + \varepsilon)}\,\frac{r}{\ell - r - 1}
\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_r\|_*\,.$$
By the Gram correspondence from the RSI $(1 + \varepsilon)$ form at $\mathbf{H}^{1/2}$.
[MuscoMusco2015, Theorem 10 (proof)]; [TroppWebber2023, Theorem 9.2]; constants composed here.
Result: nyssi-gapless-error -/
theorem
_root_.Matrix.PosSemidef.integral_specNorm_sub_nystrom_pow_mul_le_one_add_sq_mul_of_hasLaw_gaussianMatrix
    (hH : H.PosSemidef) (hX : HasLaw X (gaussianMatrix n l) μ) {r : ℕ}
    (hr : r + 2 ≤ Fintype.card l) (p : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∫ ω, specNorm (H - nystrom H (H ^ p * X ω)) ∂μ ≤
      (1 + ε) ^ 2 * singularValues H r +
        Real.exp (-8 * (p : ℝ) * (ε / (2 + ε))) *
          ((r : ℝ) / ((Fintype.card l : ℝ) - r - 1)) * nuclearNorm (H - truncatedSVD H r) := by
  simp only [specNorm_sub_nystrom_pow_mul_eq hH]
  have hb := integral_specNorm_sub_rsvd_pow_mul_sq_le_one_add_sq_mul_of_hasLaw_gaussianMatrix
    (CFC.sqrt H) hX hr p hε
  rwa [hH.conjTranspose_sqrt_mul_sqrt, hH.sq_singularValues_sqrt,
    hH.frobNorm_sqrt_sub_truncatedSVD_sq] at hb

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **Tropp and Webber's gapless bound for block Krylov Nyström, Nyström-native shape**: for
positive semidefinite $\mathbf{H}$, a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$,
$q \ge 2$ blocks, a target rank $r$ with $r + 2 \le \ell$ and $\sigma_r(\mathbf{H}) > 0$,
the bound <!-- value rangeFinderTailRatio \mathbf{H}^{1/2} r \ell -->
$$\mathbb{E}\|\mathbf{H} - \mathsf{nystromBKI}(\mathbf{H}, \mathbf{X}, q)\|_2 \le
\sigma_r(\mathbf{H})\exp\biggl(\frac{1}{16(q-1)^2}\log^2\biggl(4\Bigl(1 + \frac{r}{\ell - r - 1}\,
\frac{\|\mathbf{H}^{1/2} - \llbracket\mathbf{H}^{1/2}\rrbracket_r\|_{\mathsf{F}}^2}
{\sigma_r(\mathbf{H}^{1/2})^2}\Bigr)\biggr)\biggr)\,,$$
where the ratio is $1 + \frac{r}{\ell - r - 1}\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_r\|_*/
\sigma_r(\mathbf{H})$ (`Matrix.PosSemidef.rangeFinderTailRatio_sqrt`). By the Gram correspondence
from `NLAlib.integral_specNorm_sub_rbki_sq_le_mul_exp_of_hasLaw_gaussianMatrix` at
$\mathbf{H}^{1/2}$. [TroppWebber2023, Theorem 9.1 (NysBKI)]; there on the squared error with the
Frobenius tail ratio and rate $1/(8(m - 3/2)^2)$ for $m = q$ products; this statement is the
Nyström-native shape; the two are incomparable.
Result: nysbki-gapless-error -/
theorem
_root_.Matrix.PosSemidef.integral_specNorm_sub_nystromBKI_le_mul_exp_of_hasLaw_gaussianMatrix
    (hH : H.PosSemidef) (hX : HasLaw X (gaussianMatrix n l) μ) {r q : ℕ}
    (hr : r + 2 ≤ Fintype.card l) (hq : 2 ≤ q) (hσ : 0 < singularValues H r) :
    ∫ ω, specNorm (H - nystromBKI H (X ω) q) ∂μ ≤
      singularValues H r *
        Real.exp (Real.log (4 * rangeFinderTailRatio (CFC.sqrt H) r (Fintype.card l)) ^ 2 /
          (16 * ((q : ℝ) - 1) ^ 2)) := by
  simp only [specNorm_sub_nystromBKI_eq hH]
  have hb := integral_specNorm_sub_rbki_sq_le_mul_exp_of_hasLaw_gaussianMatrix (CFC.sqrt H) hX hr
    hq (singularValues_sqrt_pos hH hσ)
  rwa [hH.sq_singularValues_sqrt] at hb

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **Tropp and Webber's gapless bound for Nyström subspace iteration, Nyström-native shape**: for
positive semidefinite $\mathbf{H}$, a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$,
$p$ power steps, a target rank $r$ with $r + 2 \le \ell$ and $\sigma_r(\mathbf{H}) > 0$,
the bound <!-- value rangeFinderTailRatio \mathbf{H}^{1/2} r \ell -->
$$\mathbb{E}\|\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{H}^p\mathbf{X})\|_2 \le
\sigma_r(\mathbf{H})\Bigl(1 + \frac{r}{\ell - r - 1}\,
\frac{\|\mathbf{H}^{1/2} - \llbracket\mathbf{H}^{1/2}\rrbracket_r\|_{\mathsf{F}}^2}
{\sigma_r(\mathbf{H}^{1/2})^2}\Bigr)^{1/(2p+1)}\,.$$
By the Gram correspondence from
`NLAlib.integral_specNorm_sub_rsvd_pow_mul_sq_le_mul_rpow_of_hasLaw_gaussianMatrix` at
$\mathbf{H}^{1/2}$. [TroppWebber2023, Theorem 9.1 (NysSI)]; there on the squared error with the
Frobenius tail ratio and rate $1/(m - 1/2)$ for $m = p + 1$ products; this statement is the
Nyström-native shape; the two are incomparable.
Result: nyssi-gapless-error -/
theorem
_root_.Matrix.PosSemidef.integral_specNorm_sub_nystrom_pow_mul_le_mul_rpow_of_hasLaw_gaussianMatrix
    (hH : H.PosSemidef) (hX : HasLaw X (gaussianMatrix n l) μ) {r : ℕ}
    (hr : r + 2 ≤ Fintype.card l) (p : ℕ) (hσ : 0 < singularValues H r) :
    ∫ ω, specNorm (H - nystrom H (H ^ p * X ω)) ∂μ ≤
      singularValues H r *
        rangeFinderTailRatio (CFC.sqrt H) r (Fintype.card l) ^ (1 / (2 * (p : ℝ) + 1)) := by
  simp only [specNorm_sub_nystrom_pow_mul_eq hH]
  have hb := integral_specNorm_sub_rsvd_pow_mul_sq_le_mul_rpow_of_hasLaw_gaussianMatrix
    (CFC.sqrt H) hX hr p (singularValues_sqrt_pos hH hσ)
  rwa [hH.conjTranspose_sqrt_mul_sqrt, hH.sq_singularValues_sqrt] at hb

/-! ### The late-truncated outputs -/

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The gapped bound for truncated block Krylov Nyström, trace norm**: under the hypotheses of
the untruncated form
(`Matrix.PosSemidef.integral_specNorm_sub_nystromBKI_le_singularGapRatio_of_hasLaw_gaussianMatrix`),
$$\mathbb{E}\|\mathbf{H} - \llbracket\mathsf{nystromBKI}(\mathbf{H}, \mathbf{X}, q)\rrbracket_r\|_*
\le \|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_r\|_* +
4e^{-4\sqrt{2}(q-1)\sqrt{\gamma}}\,\frac{t}{\ell - t - 1}
\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_t\|_*\,,$$
by the truncated Gram correspondence (`Matrix.PosSemidef.nuclearNorm_sub_truncatedSVD_nystrom`)
from the truncated Frobenius RBKI bound at $\mathbf{H}^{1/2}$.
[TroppWebber2023, §9.1, remark after Theorem 9.2]; there stated without a proof.
Result: nysbki-gapped-error -/
theorem
_root_.Matrix.PosSemidef.integral_nuclearNorm_sub_truncatedSVD_nystromBKI_le_singularGapRatio_of_hasLaw_gaussianMatrix
    (hH : H.PosSemidef) (hX : HasLaw X (gaussianMatrix n l) μ) {h r t q : ℕ} (hr : h + 1 = r)
    (hrt : r ≤ t) (ht : t + 2 ≤ Fintype.card l) (hq : 1 ≤ q) :
    ∫ ω, nuclearNorm (H - truncatedSVD (nystromBKI H (X ω) q) r) ∂μ ≤
      nuclearNorm (H - truncatedSVD H r) +
        4 * Real.exp (-4 * Real.sqrt 2 * ((q : ℝ) - 1) * Real.sqrt (singularGapRatio H h t)) *
          ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) * nuclearNorm (H - truncatedSVD H t) := by
  have hht : h ≤ t := by omega
  have hq1 : (0 : ℝ) ≤ (q : ℝ) - 1 := by
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hgap := hH.singularGapRatio_le_two_mul_singularGapRatio_sqrt hht
  have hγ : Real.sqrt 2 * Real.sqrt (singularGapRatio H h t) ≤
      2 * Real.sqrt (singularGapRatio (CFC.sqrt H) h t) := by
    rw [← Real.sqrt_mul zero_le_two]
    calc Real.sqrt (2 * singularGapRatio H h t)
        ≤ Real.sqrt (2 ^ 2 * singularGapRatio (CFC.sqrt H) h t) :=
          Real.sqrt_le_sqrt (by linarith)
      _ = 2 * Real.sqrt (singularGapRatio (CFC.sqrt H) h t) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq zero_le_two]
  have hexp : Real.exp (-8 * ((q : ℝ) - 1) * Real.sqrt (singularGapRatio (CFC.sqrt H) h t)) ≤
      Real.exp (-4 * Real.sqrt 2 * ((q : ℝ) - 1) * Real.sqrt (singularGapRatio H h t)) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hγ hq1])
  have key : ∀ ω, nuclearNorm (H - truncatedSVD (nystromBKI H (X ω) q) r) =
      frobNorm (CFC.sqrt H - truncatedSVD (rbki (CFC.sqrt H) (X ω) q) r) ^ 2 := fun ω => by
    rw [nystromBKI, hH.nuclearNorm_sub_truncatedSVD_nystrom, rbki, hH.conjTranspose_sqrt_mul_sqrt]
  simp only [key]
  refine (integral_frobNorm_sub_truncatedSVD_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix
    (CFC.sqrt H) hX hr hrt ht hq).trans ?_
  rw [hH.frobNorm_sqrt_sub_truncatedSVD_sq, hH.frobNorm_sqrt_sub_truncatedSVD_sq]
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hexp zero_le_four) (div_card_sub_nonneg ht))
    (nuclearNorm_nonneg (H - truncatedSVD H t))
  linarith

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The gapped bound for truncated Nyström subspace iteration, trace norm**: under the hypotheses
of the untruncated form,
$$\mathbb{E}\|\mathbf{H} - \llbracket\mathsf{nystrom}(\mathbf{H}, \mathbf{H}^p\mathbf{X})
\rrbracket_r\|_* \le \|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_r\|_* +
e^{-4p\gamma}\,\frac{t}{\ell - t - 1}\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_t\|_*\,.$$
[TroppWebber2023, §9.1, remark after Theorem 9.2]; there stated without a proof.
Result: nyssi-gapped-error -/
theorem
_root_.Matrix.PosSemidef.integral_nuclearNorm_sub_truncatedSVD_nystrom_pow_mul_le_singularGapRatio_of_hasLaw_gaussianMatrix
    (hH : H.PosSemidef) (hX : HasLaw X (gaussianMatrix n l) μ) {h r t : ℕ} (hr : h + 1 = r)
    (hrt : r ≤ t) (ht : t + 2 ≤ Fintype.card l) (p : ℕ) :
    ∫ ω, nuclearNorm (H - truncatedSVD (nystrom H (H ^ p * X ω)) r) ∂μ ≤
      nuclearNorm (H - truncatedSVD H r) +
        Real.exp (-4 * (p : ℝ) * singularGapRatio H h t) *
          ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) * nuclearNorm (H - truncatedSVD H t) := by
  have hgap := hH.singularGapRatio_le_two_mul_singularGapRatio_sqrt (show h ≤ t by omega)
  have hexp : Real.exp (-8 * (p : ℝ) * singularGapRatio (CFC.sqrt H) h t) ≤
      Real.exp (-4 * (p : ℝ) * singularGapRatio H h t) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hgap (Nat.cast_nonneg (α := ℝ) p)])
  have hb :=
    integral_frobNorm_sub_truncatedSVD_rsvd_pow_mul_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix
      (CFC.sqrt H) hX hr hrt ht p
  rw [hH.conjTranspose_sqrt_mul_sqrt, hH.frobNorm_sqrt_sub_truncatedSVD_sq,
    hH.frobNorm_sqrt_sub_truncatedSVD_sq] at hb
  simp only [hH.nuclearNorm_sub_truncatedSVD_nystrom]
  refine hb.trans ?_
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hexp (div_card_sub_nonneg ht))
    (nuclearNorm_nonneg (H - truncatedSVD H t))
  linarith

end NLAlib
