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

In the `NLAlib` namespace, the asymptotic forms of the four gapped bounds (depth
$O(\log(\lvert n \rvert/\varepsilon)/\sqrt{\gamma})$, respectively
$O(\log(\lvert n \rvert/\varepsilon)/\gamma)$ power steps) and of the two Tropp–Webber-form gapless
bounds ($O(\log(\lvert n \rvert + 1)/\sqrt{\varepsilon})$, respectively
$O(\log(\lvert n \rvert + 1)/\varepsilon)$): `exists_forall_` followed by the explicit
conclusion, with `_of_singularGapRatio_pos_` for the gapped ones, for example
`NLAlib.exists_forall_integral_specNorm_sub_nystromBKI_le_of_hasLaw_gaussianMatrix`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal MatrixOrder

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n l : Type*} [Fintype n]
  [Fintype l] {X : Ω → Matrix n l ℝ} {H : Matrix n n ℝ}


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
  rw [rangeFinderTailRatio, hH.frobNorm_sqrt_sub_truncatedSVD_sq, hH.singularValues_sqrt_sq]

open scoped Classical in
/-- Positivity of $\sigma_r(\mathbf{H})$ passes to $\sigma_r(\mathbf{H}^{1/2})$. -/
private theorem singularValues_sqrt_pos (hH : H.PosSemidef) {r : ℕ}
    (hσ : 0 < singularValues H r) : 0 < singularValues (CFC.sqrt H) r := by
  refine (singularValues_nonneg _ r).lt_of_ne fun h => ?_
  rw [← hH.singularValues_sqrt_sq, ← h] at hσ
  norm_num at hσ

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
$\gamma = (\sigma_h(\mathbf{H}) - \sigma_t(\mathbf{H}))/(\sigma_h(\mathbf{H}) +
\sigma_t(\mathbf{H}))$,
$$\mathbb{E}\|\mathbf{H} - \mathsf{nystromBKI}(\mathbf{H}, \mathbf{X}, q)\|_2 \le
\sigma_r(\mathbf{H}) + 4e^{-4\sqrt{2}(q-1)\sqrt{\gamma}}\,\frac{t}{\ell - t - 1}
\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_t\|_*\,.$$
By the Gram correspondence from the RBKI bound at $\mathbf{H}^{1/2}$
(`NLAlib.integral_specNorm_sub_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix`), whose gap
$\gamma_{1/2}$ is at least $\gamma/2$; its Chebyshev filter gives the factor
$\operatorname{sech}^2(4(q-1)\operatorname{artanh}\sqrt{\gamma_{1/2}}) \le
\operatorname{sech}^2(2\sqrt{2}(q-1)\sqrt{\gamma}) =
4e^{-4\sqrt{2}(q-1)\sqrt{\gamma}}/(1 + e^{-4\sqrt{2}(q-1)\sqrt{\gamma}})^2$, and the statement
drops $(1 + e^{-4\sqrt{2}(q-1)\sqrt{\gamma}})^2 \le 4$, which tends to $1$ (CONTRIBUTING §5.2
rule 7). [TroppWebber2023, Theorem 9.2 (NysBKI)]; there for
$\mathbb{E}\|\mathbf{H} - \hat{\mathbf{H}}\|_p^2$ with a squared Frobenius tail and exponent
$4(m - 3/2)\sqrt{2\gamma}$ for $m = q$ products; this statement is the Nyström-native shape of TW
Corollary 8.2, obtained from the RBKI line at $\mathbf{H}^{1/2}$; the two are incomparable.
Asymptotic form:
`NLAlib.exists_forall_integral_specNorm_sub_nystromBKI_le_of_singularGapRatio_pos_of_hasLaw_gaussianMatrix`.
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
  rw [hH.singularValues_sqrt_sq, hH.frobNorm_sqrt_sub_truncatedSVD_sq]
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hexp zero_le_four) (natCast_div_sub_sub_one_nonneg ht))
    (nuclearNorm_nonneg (H - truncatedSVD H t))
  linarith

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The gapped bound for Nyström subspace iteration**: for positive semidefinite $\mathbf{H}$, a
standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$, $p$ power steps, a head of $r = h + 1$
eigenvalues, a tail index $t \ge r$ with $t + 2 \le \ell$, and $\gamma = (\sigma_h(\mathbf{H}) -
\sigma_t(\mathbf{H}))/(\sigma_h(\mathbf{H}) + \sigma_t(\mathbf{H}))$,
$$\mathbb{E}\|\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{H}^p\mathbf{X})\|_2 \le
\sigma_r(\mathbf{H}) + e^{-4p\gamma}\,\frac{t}{\ell - t - 1}
\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_t\|_*\,.$$
By the Gram correspondence from the RSI bound at $\mathbf{H}^{1/2}$.
Asymptotic form:
`NLAlib.exists_forall_integral_specNorm_sub_nystrom_pow_mul_le_of_singularGapRatio_pos_of_hasLaw_gaussianMatrix`.
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
  rw [hH.conjTranspose_sqrt_mul_sqrt, hH.singularValues_sqrt_sq,
    hH.frobNorm_sqrt_sub_truncatedSVD_sq] at hb
  simp only [specNorm_sub_nystrom_pow_mul_eq hH]
  refine hb.trans ?_
  have := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hexp (natCast_div_sub_sub_one_nonneg ht))
    (nuclearNorm_nonneg (H - truncatedSVD H t))
  linarith

/-! ### Gapless bounds -/

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
  rwa [hH.singularValues_sqrt_sq, hH.frobNorm_sqrt_sub_truncatedSVD_sq] at hb

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
  rwa [hH.conjTranspose_sqrt_mul_sqrt, hH.singularValues_sqrt_sq,
    hH.frobNorm_sqrt_sub_truncatedSVD_sq] at hb

/-- **Tropp and Webber's gapless bound for block Krylov Nyström, Nyström-native shape**: for
positive semidefinite $\mathbf{H}$, a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$,
$q \ge 2$ blocks, a target rank $r$ with $r + 2 \le \ell$ and $\sigma_r(\mathbf{H}) > 0$,
the bound <!-- value rangeFinderTailRatio \mathbf{H}^{1/2} r \ell -->
$$\mathbb{E}\|\mathbf{H} - \mathsf{nystromBKI}(\mathbf{H}, \mathbf{X}, q)\|_2 \le
\sigma_r(\mathbf{H})\exp\biggl(\frac{1}{16(q-1)^2}\log^2\biggl(4\Bigl(1 + \frac{r}{\ell - r - 1}\,
\frac{\|\mathbf{H}^{1/2} - \llbracket\mathbf{H}^{1/2}\rrbracket_r\|_{\mathsf{F}}^2}
{\sigma_r(\mathbf{H}^{1/2})^2}\Bigr)\biggr)\biggr)\,,$$
where the ratio is $1 + (r/(\ell - r - 1))\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_r\|_*/
\sigma_r(\mathbf{H})$ (`Matrix.PosSemidef.rangeFinderTailRatio_sqrt`). By the Gram correspondence
from `NLAlib.integral_specNorm_sub_rbki_sq_le_mul_exp_of_hasLaw_gaussianMatrix` at
$\mathbf{H}^{1/2}$. [TroppWebber2023, Theorem 9.1 (NysBKI)]; there on the squared error with the
Frobenius tail ratio and rate $1/(8(m - 3/2)^2)$ for $m = q$ products; this statement is the
Nyström-native shape; the two are incomparable.
Asymptotic form:
`NLAlib.exists_forall_integral_specNorm_sub_nystromBKI_le_of_hasLaw_gaussianMatrix`.
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
  rwa [hH.singularValues_sqrt_sq] at hb

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
Asymptotic form:
`NLAlib.exists_forall_integral_specNorm_sub_nystrom_pow_mul_le_of_hasLaw_gaussianMatrix`.
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
  rwa [hH.conjTranspose_sqrt_mul_sqrt, hH.singularValues_sqrt_sq] at hb

/-! ### The late-truncated outputs -/

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The gapped bound for truncated block Krylov Nyström, trace norm**: for positive semidefinite
$\mathbf{H}$, a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$, $q \ge 1$ blocks, a head
of $r = h + 1$ eigenvalues, a tail index $t \ge r$ with $t + 2 \le \ell$, and $\gamma =
(\sigma_h(\mathbf{H}) - \sigma_t(\mathbf{H}))/(\sigma_h(\mathbf{H}) + \sigma_t(\mathbf{H}))$,
$$\mathbb{E}\|\mathbf{H} - \llbracket\mathsf{nystromBKI}(\mathbf{H}, \mathbf{X}, q)\rrbracket_r\|_*
\le \|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_r\|_* +
4e^{-4\sqrt{2}(q-1)\sqrt{\gamma}}\,\frac{t}{\ell - t - 1}
\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_t\|_*\,,$$
by the truncated Gram correspondence (`Matrix.PosSemidef.nuclearNorm_sub_truncatedSVD_nystrom`)
from the truncated Frobenius RBKI bound at $\mathbf{H}^{1/2}$. The untruncated spectral form is
`Matrix.PosSemidef.integral_specNorm_sub_nystromBKI_le_singularGapRatio_of_hasLaw_gaussianMatrix`.
Asymptotic form:
`NLAlib.exists_forall_integral_nuclearNorm_sub_truncatedSVD_nystromBKI_le_of_singularGapRatio_pos_of_hasLaw_gaussianMatrix`.
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
    (mul_le_mul_of_nonneg_left hexp zero_le_four) (natCast_div_sub_sub_one_nonneg ht))
    (nuclearNorm_nonneg (H - truncatedSVD H t))
  linarith

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The gapped bound for truncated Nyström subspace iteration, trace norm**: for positive
semidefinite $\mathbf{H}$, a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$, $p$ power
steps, a head of $r = h + 1$ eigenvalues, a tail index $t \ge r$ with $t + 2 \le \ell$, and
$\gamma = (\sigma_h(\mathbf{H}) - \sigma_t(\mathbf{H}))/(\sigma_h(\mathbf{H}) +
\sigma_t(\mathbf{H}))$,
$$\mathbb{E}\|\mathbf{H} - \llbracket\mathsf{nystrom}(\mathbf{H}, \mathbf{H}^p\mathbf{X})
\rrbracket_r\|_* \le \|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_r\|_* +
e^{-4p\gamma}\,\frac{t}{\ell - t - 1}\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_t\|_*\,.$$
By the truncated Gram correspondence from the truncated Frobenius RSI bound at
$\mathbf{H}^{1/2}$. The untruncated spectral form is
`Matrix.PosSemidef.integral_specNorm_sub_nystrom_pow_mul_le_singularGapRatio_of_hasLaw_gaussianMatrix`.
Asymptotic form:
`NLAlib.exists_forall_integral_nuclearNorm_sub_truncatedSVD_nystrom_pow_mul_le_of_singularGapRatio_pos_of_hasLaw_gaussianMatrix`.
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
  have := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hexp (natCast_div_sub_sub_one_nonneg ht))
    (nuclearNorm_nonneg (H - truncatedSVD H t))
  linarith

/-! ### Asymptotic forms -/

/-- **Depth $O(\log(\lvert n \rvert/\varepsilon)/\sqrt{\gamma})$ suffices for block Krylov
Nyström with a gap**: there are absolute constants $C, \varepsilon_0 > 0$ such that for positive
semidefinite $\mathbf{H}$, a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$, a head of
$r = h + 1$ eigenvalues, a tail index $t \ge r$ with $t + 2 \le \ell$, a positive relative gap
$\gamma = (\sigma_h(\mathbf{H}) - \sigma_t(\mathbf{H}))/(\sigma_h(\mathbf{H}) +
\sigma_t(\mathbf{H}))$,
$0 < \varepsilon \le \varepsilon_0$ and $q \ge C\log(\lvert n \rvert/\varepsilon)/\sqrt{\gamma}$
blocks,
$$\mathbb{E}\|\mathbf{H} - \mathsf{nystromBKI}(\mathbf{H}, \mathbf{X}, q)\|_2 \le
(1 + \varepsilon)\,\sigma_r(\mathbf{H})\,.$$
The asymptotic form of
`Matrix.PosSemidef.integral_specNorm_sub_nystromBKI_le_singularGapRatio_of_hasLaw_gaussianMatrix`,
whose tail term is at most $4\lvert n \rvert^2e^{-4\sqrt{2}(q-1)\sqrt{\gamma}}\sigma_r(\mathbf{H})$;
the proof takes $C = 3$ and $\varepsilon_0 = 1/2$. [TroppWebber2023, Theorem 9.2 (NysBKI)]; there
for the squared error in explicit form.
Asymptotic:
Matrix.PosSemidef.integral_specNorm_sub_nystromBKI_le_singularGapRatio_of_hasLaw_gaussianMatrix
Result: nysbki-gapped-error -/
theorem
exists_forall_integral_specNorm_sub_nystromBKI_le_of_singularGapRatio_pos_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω n l : Type} [MeasurableSpace Ω] [Fintype n]
      [DecidableEq n] [Fintype l] (μ : Measure Ω) (H : Matrix n n ℝ) (X : Ω → Matrix n l ℝ)
      (h r t q : ℕ) (ε : ℝ), H.PosSemidef → HasLaw X (gaussianMatrix n l) μ → h + 1 = r →
      r ≤ t → t + 2 ≤ Fintype.card l → 0 < singularGapRatio H h t → 0 < ε → ε ≤ ε₀ →
      C * Real.log (Fintype.card n / ε) / Real.sqrt (singularGapRatio H h t) ≤ q →
      ∫ ω, specNorm (H - nystromBKI H (X ω) q) ∂μ ≤ (1 + ε) * singularValues H r := by
  refine ⟨3, 1 / 2, by norm_num, by norm_num, ?_⟩
  intro Ω n l _ _ _ _ μ H X h r t q ε hH hX hr hrt ht hγ hε hε₀ hq
  have hN : (1 : ℝ) ≤ Fintype.card n := by
    rcases Nat.eq_zero_or_pos (Fintype.card n) with h0 | h0
    · simp [singularGapRatio, singularValues_of_card_cols_le H (k := h) (by omega),
        singularValues_of_card_cols_le H (k := t) (by omega)] at hγ
    · exact_mod_cast h0
  have hL := Real.one_half_le_log_div hN hε hε₀
  obtain ⟨hq1, hqL⟩ := Real.one_le_and_log_div_le_sub_one_mul hN hε hε₀ (Real.sqrt_pos.2 hγ)
    (Real.sqrt_le_one.2 (singularGapRatio_le_one H h t)) hq
  have hexp :=
    hH.integral_specNorm_sub_nystromBKI_le_singularGapRatio_of_hasLaw_gaussianMatrix hX hr hrt ht
      hq1
  rw [← one_mul (singularValues H r)] at hexp
  have hT :=
    natCast_div_sub_sub_one_mul_frobNorm_sub_truncatedSVD_sq_le_card_sq_mul_singularValues_sq
      (CFC.sqrt H) hrt ht
  rw [hH.frobNorm_sqrt_sub_truncatedSVD_sq, hH.singularValues_sqrt_sq] at hT
  have hs2 : 1 ≤ Real.sqrt 2 := Real.one_le_sqrt.2 (by norm_num)
  have hqγ : 0 ≤ ((q : ℝ) - 1) * Real.sqrt (singularGapRatio H h t) := by linarith
  exact Real.le_add_mul_of_le_add_mul_exp hexp (singularValues_nonneg _ _) (by norm_num) le_rfl hT
    hN hε hε₀ (by nlinarith [mul_le_mul_of_nonneg_right hs2 hqγ])

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **$O(\log(\lvert n \rvert/\varepsilon)/\gamma)$ power steps suffice for Nyström subspace
iteration with a gap**: there are absolute constants $C, \varepsilon_0 > 0$ such that for positive
semidefinite $\mathbf{H}$, a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$, a head of
$r = h + 1$ eigenvalues, a tail index $t \ge r$ with $t + 2 \le \ell$, a positive relative gap
$\gamma = (\sigma_h(\mathbf{H}) - \sigma_t(\mathbf{H}))/(\sigma_h(\mathbf{H}) +
\sigma_t(\mathbf{H}))$, $0 < \varepsilon \le \varepsilon_0$ and
$p \ge C\log(\lvert n \rvert/\varepsilon)/\gamma$ power steps,
$$\mathbb{E}\|\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{H}^p\mathbf{X})\|_2 \le
(1 + \varepsilon)\,\sigma_r(\mathbf{H})\,.$$
The asymptotic form of
`Matrix.PosSemidef.integral_specNorm_sub_nystrom_pow_mul_le_singularGapRatio_of_hasLaw_gaussianMatrix`,
whose tail term is at most $\lvert n \rvert^2e^{-4p\gamma}\sigma_r(\mathbf{H})$; the proof takes
$C = 1$ and $\varepsilon_0 = 1/2$. [TroppWebber2023, Theorem 9.2 (NysSI)]; there for the squared
error in explicit form.
Asymptotic:
Matrix.PosSemidef.integral_specNorm_sub_nystrom_pow_mul_le_singularGapRatio_of_hasLaw_gaussianMatrix
Result: nyssi-gapped-error -/
theorem
exists_forall_integral_specNorm_sub_nystrom_pow_mul_le_of_singularGapRatio_pos_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω n l : Type} [MeasurableSpace Ω] [Fintype n]
      [DecidableEq n] [Fintype l] (μ : Measure Ω) (H : Matrix n n ℝ) (X : Ω → Matrix n l ℝ)
      (h r t p : ℕ) (ε : ℝ), H.PosSemidef → HasLaw X (gaussianMatrix n l) μ → h + 1 = r →
      r ≤ t → t + 2 ≤ Fintype.card l → 0 < singularGapRatio H h t → 0 < ε → ε ≤ ε₀ →
      C * Real.log (Fintype.card n / ε) / singularGapRatio H h t ≤ p →
      ∫ ω, specNorm (H - nystrom H (H ^ p * X ω)) ∂μ ≤ (1 + ε) * singularValues H r := by
  refine ⟨1, 1 / 2, one_pos, by norm_num, ?_⟩
  intro Ω n l _ _ _ _ μ H X h r t p ε hH hX hr hrt ht hγ hε hε₀ hp
  have hN : (1 : ℝ) ≤ Fintype.card n := by
    rcases Nat.eq_zero_or_pos (Fintype.card n) with h0 | h0
    · simp [singularGapRatio, singularValues_of_card_cols_le H (k := h) (by omega),
        singularValues_of_card_cols_le H (k := t) (by omega)] at hγ
    · exact_mod_cast h0
  have hL := Real.one_half_le_log_div hN hε hε₀
  rw [one_mul, div_le_iff₀ hγ] at hp
  have hexp :=
    hH.integral_specNorm_sub_nystrom_pow_mul_le_singularGapRatio_of_hasLaw_gaussianMatrix hX hr
      hrt ht p
  rw [← one_mul (singularValues H r), ← one_mul (Real.exp _)] at hexp
  have hT :=
    natCast_div_sub_sub_one_mul_frobNorm_sub_truncatedSVD_sq_le_card_sq_mul_singularValues_sq
      (CFC.sqrt H) hrt ht
  rw [hH.frobNorm_sqrt_sub_truncatedSVD_sq, hH.singularValues_sqrt_sq] at hT
  exact Real.le_add_mul_of_le_add_mul_exp hexp (singularValues_nonneg _ _) zero_le_one (by norm_num)
    hT hN hε hε₀ (by nlinarith)

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **Depth $O(\log(\lvert n \rvert/\varepsilon)/\sqrt{\gamma})$ suffices for truncated block Krylov
Nyström with a gap**, trace norm: there are absolute constants $C, \varepsilon_0 > 0$ such that for
positive semidefinite $\mathbf{H}$, a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$, a
head of $r = h + 1$ eigenvalues, a tail index $t \ge r$ with $t + 2 \le \ell$, a positive relative
gap $\gamma = (\sigma_h(\mathbf{H}) - \sigma_t(\mathbf{H}))/(\sigma_h(\mathbf{H}) +
\sigma_t(\mathbf{H}))$, $0 < \varepsilon \le \varepsilon_0$ and
$q \ge C\log(\lvert n \rvert/\varepsilon)/\sqrt{\gamma}$ blocks,
$$\mathbb{E}\|\mathbf{H} - \llbracket\mathsf{nystromBKI}(\mathbf{H}, \mathbf{X}, q)\rrbracket_r\|_*
\le (1 + \varepsilon)\,\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_r\|_*\,.$$
The asymptotic form of
`Matrix.PosSemidef.integral_nuclearNorm_sub_truncatedSVD_nystromBKI_le_singularGapRatio_of_hasLaw_gaussianMatrix`;
the proof takes $C = 3$ and $\varepsilon_0 = 1/2$. [TroppWebber2023, §9.1, remark after
Theorem 9.2]; there stated without a proof.
Asymptotic:
Matrix.PosSemidef.integral_nuclearNorm_sub_truncatedSVD_nystromBKI_le_singularGapRatio_of_hasLaw_gaussianMatrix
Result: nysbki-gapped-error -/
theorem
exists_forall_integral_nuclearNorm_sub_truncatedSVD_nystromBKI_le_of_singularGapRatio_pos_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω n l : Type} [MeasurableSpace Ω] [Fintype n]
      [DecidableEq n] [Fintype l] (μ : Measure Ω) (H : Matrix n n ℝ) (X : Ω → Matrix n l ℝ)
      (h r t q : ℕ) (ε : ℝ), H.PosSemidef → HasLaw X (gaussianMatrix n l) μ → h + 1 = r →
      r ≤ t → t + 2 ≤ Fintype.card l → 0 < singularGapRatio H h t → 0 < ε → ε ≤ ε₀ →
      C * Real.log (Fintype.card n / ε) / Real.sqrt (singularGapRatio H h t) ≤ q →
      ∫ ω, nuclearNorm (H - truncatedSVD (nystromBKI H (X ω) q) r) ∂μ ≤
        (1 + ε) * nuclearNorm (H - truncatedSVD H r) := by
  refine ⟨3, 1 / 2, by norm_num, by norm_num, ?_⟩
  intro Ω n l _ _ _ _ μ H X h r t q ε hH hX hr hrt ht hγ hε hε₀ hq
  have hN : (1 : ℝ) ≤ Fintype.card n := by
    rcases Nat.eq_zero_or_pos (Fintype.card n) with h0 | h0
    · simp [singularGapRatio, singularValues_of_card_cols_le H (k := h) (by omega),
        singularValues_of_card_cols_le H (k := t) (by omega)] at hγ
    · exact_mod_cast h0
  have hL := Real.one_half_le_log_div hN hε hε₀
  obtain ⟨hq1, hqL⟩ := Real.one_le_and_log_div_le_sub_one_mul hN hε hε₀ (Real.sqrt_pos.2 hγ)
    (Real.sqrt_le_one.2 (singularGapRatio_le_one H h t)) hq
  have hexp :=
    hH.integral_nuclearNorm_sub_truncatedSVD_nystromBKI_le_singularGapRatio_of_hasLaw_gaussianMatrix
      hX hr hrt ht hq1
  rw [← one_mul (nuclearNorm (H - truncatedSVD H r))] at hexp
  have hT :=
    natCast_div_sub_sub_one_mul_frobNorm_sub_truncatedSVD_sq_le_card_mul_frobNorm_sub_truncatedSVD_sq
      (CFC.sqrt H) hrt ht
  rw [hH.frobNorm_sqrt_sub_truncatedSVD_sq, hH.frobNorm_sqrt_sub_truncatedSVD_sq] at hT
  have hs2 : 1 ≤ Real.sqrt 2 := Real.one_le_sqrt.2 (by norm_num)
  have hqγ : 0 ≤ ((q : ℝ) - 1) * Real.sqrt (singularGapRatio H h t) := by linarith
  exact Real.le_add_mul_of_le_add_mul_exp hexp (nuclearNorm_nonneg _) (by norm_num) le_rfl
    (hT.trans (mul_le_mul_of_nonneg_right (by nlinarith) (nuclearNorm_nonneg _))) hN hε hε₀
    (by nlinarith [mul_le_mul_of_nonneg_right hs2 hqγ])

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **$O(\log(\lvert n \rvert/\varepsilon)/\gamma)$ power steps suffice for truncated Nyström
subspace iteration with a gap**, trace norm: there are absolute constants $C, \varepsilon_0 > 0$
such that for positive semidefinite $\mathbf{H}$, a standard Gaussian $n \times \ell$ test matrix
$\mathbf{X}$, a head of $r = h + 1$ eigenvalues, a tail index $t \ge r$ with $t + 2 \le \ell$, a
positive relative gap $\gamma = (\sigma_h(\mathbf{H}) -
\sigma_t(\mathbf{H}))/(\sigma_h(\mathbf{H}) + \sigma_t(\mathbf{H}))$,
$0 < \varepsilon \le \varepsilon_0$ and $p \ge C\log(\lvert n \rvert/\varepsilon)/\gamma$ power
steps,
$$\mathbb{E}\|\mathbf{H} - \llbracket\mathsf{nystrom}(\mathbf{H}, \mathbf{H}^p\mathbf{X})
\rrbracket_r\|_* \le (1 + \varepsilon)\,\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_r\|_*\,.$$
The asymptotic form of
`Matrix.PosSemidef.integral_nuclearNorm_sub_truncatedSVD_nystrom_pow_mul_le_singularGapRatio_of_hasLaw_gaussianMatrix`;
the proof takes $C = 1$ and $\varepsilon_0 = 1/2$. [TroppWebber2023, §9.1, remark after
Theorem 9.2]; there stated without a proof.
Asymptotic:
Matrix.PosSemidef.integral_nuclearNorm_sub_truncatedSVD_nystrom_pow_mul_le_singularGapRatio_of_hasLaw_gaussianMatrix
Result: nyssi-gapped-error -/
theorem
exists_forall_integral_nuclearNorm_sub_truncatedSVD_nystrom_pow_mul_le_of_singularGapRatio_pos_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω n l : Type} [MeasurableSpace Ω] [Fintype n]
      [DecidableEq n] [Fintype l] (μ : Measure Ω) (H : Matrix n n ℝ) (X : Ω → Matrix n l ℝ)
      (h r t p : ℕ) (ε : ℝ), H.PosSemidef → HasLaw X (gaussianMatrix n l) μ → h + 1 = r →
      r ≤ t → t + 2 ≤ Fintype.card l → 0 < singularGapRatio H h t → 0 < ε → ε ≤ ε₀ →
      C * Real.log (Fintype.card n / ε) / singularGapRatio H h t ≤ p →
      ∫ ω, nuclearNorm (H - truncatedSVD (nystrom H (H ^ p * X ω)) r) ∂μ ≤
        (1 + ε) * nuclearNorm (H - truncatedSVD H r) := by
  refine ⟨1, 1 / 2, one_pos, by norm_num, ?_⟩
  intro Ω n l _ _ _ _ μ H X h r t p ε hH hX hr hrt ht hγ hε hε₀ hp
  have hN : (1 : ℝ) ≤ Fintype.card n := by
    rcases Nat.eq_zero_or_pos (Fintype.card n) with h0 | h0
    · simp [singularGapRatio, singularValues_of_card_cols_le H (k := h) (by omega),
        singularValues_of_card_cols_le H (k := t) (by omega)] at hγ
    · exact_mod_cast h0
  have hL := Real.one_half_le_log_div hN hε hε₀
  rw [one_mul, div_le_iff₀ hγ] at hp
  have hexp :=
    hH.integral_nuclearNorm_sub_truncatedSVD_nystrom_pow_mul_le_singularGapRatio_of_hasLaw_gaussianMatrix
      hX hr hrt ht p
  rw [← one_mul (nuclearNorm (H - truncatedSVD H r)), ← one_mul (Real.exp _)] at hexp
  have hT :=
    natCast_div_sub_sub_one_mul_frobNorm_sub_truncatedSVD_sq_le_card_mul_frobNorm_sub_truncatedSVD_sq
      (CFC.sqrt H) hrt ht
  rw [hH.frobNorm_sqrt_sub_truncatedSVD_sq, hH.frobNorm_sqrt_sub_truncatedSVD_sq] at hT
  exact Real.le_add_mul_of_le_add_mul_exp hexp (nuclearNorm_nonneg _) zero_le_one (by norm_num)
    (hT.trans (mul_le_mul_of_nonneg_right (by nlinarith) (nuclearNorm_nonneg _))) hN hε hε₀
    (by nlinarith)

/-- **Depth $O(\log(\lvert n \rvert + 1)/\sqrt{\varepsilon})$ suffices for block Krylov Nyström**,
no gap: there are absolute constants $C, \varepsilon_0 > 0$ such that for positive semidefinite
$\mathbf{H}$, a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$, a target rank $r$ with
$r + 2 \le \ell$, $0 < \varepsilon \le \varepsilon_0$ and
$q \ge C\log(\lvert n \rvert + 1)/\sqrt{\varepsilon}$ blocks,
$$\mathbb{E}\|\mathbf{H} - \mathsf{nystromBKI}(\mathbf{H}, \mathbf{X}, q)\|_2 \le
(1 + \varepsilon)\,\sigma_r(\mathbf{H})\,.$$
The asymptotic form of the Tropp–Webber-form gapless bound
`Matrix.PosSemidef.integral_specNorm_sub_nystromBKI_le_mul_exp_of_hasLaw_gaussianMatrix`, with the
tail ratio of $\mathbf{H}^{1/2}$ at most $1 + \lvert n \rvert^2$
(`NLAlib.rangeFinderTailRatio_le_one_add_card_sq`). When $\sigma_r(\mathbf{H}) = 0$ the
$(1 + \varepsilon)$ form
(`Matrix.PosSemidef.integral_specNorm_sub_nystromBKI_le_one_add_sq_mul_of_hasLaw_gaussianMatrix`)
gives error $0$, so no positivity hypothesis is needed. The proof takes $C = 4$ and
$\varepsilon_0 = 1$. [TroppWebber2023, Theorem 9.1 (NysBKI)]; there for the squared error with
$m = q$ products.
Asymptotic:
Matrix.PosSemidef.integral_specNorm_sub_nystromBKI_le_mul_exp_of_hasLaw_gaussianMatrix
Result: nysbki-gapless-error -/
theorem exists_forall_integral_specNorm_sub_nystromBKI_le_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω n l : Type} [MeasurableSpace Ω] [Fintype n]
      [DecidableEq n] [Fintype l] (μ : Measure Ω) (H : Matrix n n ℝ) (X : Ω → Matrix n l ℝ)
      (r q : ℕ) (ε : ℝ), H.PosSemidef → HasLaw X (gaussianMatrix n l) μ →
      r + 2 ≤ Fintype.card l → 0 < ε → ε ≤ ε₀ →
      C * Real.log (Fintype.card n + 1) / Real.sqrt ε ≤ q →
      ∫ ω, specNorm (H - nystromBKI H (X ω) q) ∂μ ≤ (1 + ε) * singularValues H r := by
  refine ⟨4, 1, by norm_num, one_pos, ?_⟩
  intro Ω n l _ _ _ _ μ H X r q ε hH hX hr hε hε₁ hq
  have := hX.isProbabilityMeasure
  rcases Nat.eq_zero_or_pos (Fintype.card n) with hN0 | hNpos
  · -- An empty index type: $\mathbf{H} = \mathbf{0}$.
    have : IsEmpty n := Fintype.card_eq_zero_iff.mp hN0
    have h0 : ∀ ω, H - nystromBKI H (X ω) q = 0 := fun ω => Subsingleton.elim _ _
    simp only [h0, specNorm_zero, integral_zero]
    exact mul_nonneg (by linarith) (singularValues_nonneg _ _)
  have hN : (1 : ℝ) ≤ Fintype.card n := by exact_mod_cast hNpos
  obtain ⟨hq2, hexp⟩ := Real.two_le_and_exp_log_four_mul_sq_div_le_one_add hN hε hε₁ hq
  rcases (singularValues_nonneg H r).eq_or_lt with hσ0 | hσ
  · -- $\sigma_r(\mathbf{H}) = 0$: the $(1 + \varepsilon)$ form bounds the error by $0$.
    have hH0 : H - truncatedSVD H r = 0 := by
      rw [truncatedSVD_of_singularValues_eq_zero H hσ0.symm, sub_self]
    have h := hH.integral_specNorm_sub_nystromBKI_le_one_add_sq_mul_of_hasLaw_gaussianMatrix hX hr
      (q := q) (by omega) hε
    rw [hH0, nuclearNorm_zero, ← hσ0] at h
    rw [← hσ0]
    simpa using h
  refine (hH.integral_specNorm_sub_nystromBKI_le_mul_exp_of_hasLaw_gaussianMatrix hX hr hq2
    hσ).trans ?_
  rw [mul_comm (1 + ε)]
  exact mul_le_mul_of_nonneg_left (hexp _ (one_le_rangeFinderTailRatio _ hr)
    (rangeFinderTailRatio_le_one_add_card_sq _ hr (singularValues_sqrt_pos hH hσ)))
    (singularValues_nonneg _ _)

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **$O(\log(\lvert n \rvert + 1)/\varepsilon)$ power steps suffice for Nyström subspace
iteration**, no gap: there are absolute constants $C, \varepsilon_0 > 0$ such that for positive
semidefinite $\mathbf{H}$, a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$, a target
rank $r$ with $r + 2 \le \ell$, $0 < \varepsilon \le \varepsilon_0$ and
$p \ge C\log(\lvert n \rvert + 1)/\varepsilon$ power steps,
$$\mathbb{E}\|\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{H}^p\mathbf{X})\|_2 \le
(1 + \varepsilon)\,\sigma_r(\mathbf{H})\,.$$
The asymptotic form of the Tropp–Webber-form gapless bound
`Matrix.PosSemidef.integral_specNorm_sub_nystrom_pow_mul_le_mul_rpow_of_hasLaw_gaussianMatrix`,
with the tail ratio of $\mathbf{H}^{1/2}$ at most $1 + \lvert n \rvert^2$
(`NLAlib.rangeFinderTailRatio_le_one_add_card_sq`). When $\sigma_r(\mathbf{H}) = 0$ the
$(1 + \varepsilon)$ form
(`Matrix.PosSemidef.integral_specNorm_sub_nystrom_pow_mul_le_one_add_sq_mul_of_hasLaw_gaussianMatrix`)
gives error $0$, so no positivity hypothesis is needed. The proof takes $C = 2$ and
$\varepsilon_0 = 1$. [TroppWebber2023, Theorem 9.1 (NysSI)]; there for the squared error with
$m = p + 1$ products.
Asymptotic:
Matrix.PosSemidef.integral_specNorm_sub_nystrom_pow_mul_le_mul_rpow_of_hasLaw_gaussianMatrix
Result: nyssi-gapless-error -/
theorem exists_forall_integral_specNorm_sub_nystrom_pow_mul_le_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω n l : Type} [MeasurableSpace Ω] [Fintype n]
      [DecidableEq n] [Fintype l] (μ : Measure Ω) (H : Matrix n n ℝ) (X : Ω → Matrix n l ℝ)
      (r p : ℕ) (ε : ℝ), H.PosSemidef → HasLaw X (gaussianMatrix n l) μ →
      r + 2 ≤ Fintype.card l → 0 < ε → ε ≤ ε₀ → C * Real.log (Fintype.card n + 1) / ε ≤ p →
      ∫ ω, specNorm (H - nystrom H (H ^ p * X ω)) ∂μ ≤ (1 + ε) * singularValues H r := by
  refine ⟨2, 1, by norm_num, one_pos, ?_⟩
  intro Ω n l _ _ _ _ μ H X r p ε hH hX hr hε hε₁ hp
  rcases (singularValues_nonneg H r).eq_or_lt with hσ0 | hσ
  · -- $\sigma_r(\mathbf{H}) = 0$: the $(1 + \varepsilon)$ form bounds the error by $0$.
    have hH0 : H - truncatedSVD H r = 0 := by
      rw [truncatedSVD_of_singularValues_eq_zero H hσ0.symm, sub_self]
    have h := hH.integral_specNorm_sub_nystrom_pow_mul_le_one_add_sq_mul_of_hasLaw_gaussianMatrix
      hX hr p hε
    rw [hH0, nuclearNorm_zero, ← hσ0] at h
    rw [← hσ0]
    simpa using h
  refine (hH.integral_specNorm_sub_nystrom_pow_mul_le_mul_rpow_of_hasLaw_gaussianMatrix hX hr p
    hσ).trans ?_
  rw [mul_comm (1 + ε)]
  exact mul_le_mul_of_nonneg_left (Real.rpow_one_div_two_mul_add_one_le_one_add (Nat.cast_nonneg _)
    (one_le_rangeFinderTailRatio _ hr)
    (rangeFinderTailRatio_le_one_add_card_sq _ hr (singularValues_sqrt_pos hH hσ)) hε hε₁ hp)
    (singularValues_nonneg _ _)

end NLAlib
