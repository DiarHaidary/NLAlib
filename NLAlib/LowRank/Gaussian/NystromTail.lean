/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Gaussian.RangeFinderTail
public import NLAlib.LowRank.Random.Nystrom

/-!
# Tail bounds for Gaussian Nyström

For a real positive semidefinite $\mathbf{H}$, a standard Gaussian test matrix
$\mathbf{X} \in \mathbb{R}^{n \times \ell}$ and a target rank $k$, the error of Nyström is
`H - nystrom H (X ω)`, $\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{X})$, and the error of
its late truncation is `H - truncatedSVD (nystrom H (X ω)) k`. Throughout $d = \ell - k + 1$,
written `hd : k + d = Fintype.card l + 1`, and the bounds are in $\mathbf{H}$'s own best errors,
$\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_* = \sum_{i \ge k}\lambda_i(\mathbf{H})$ and
$\sigma_k(\mathbf{H}) = \lambda_k(\mathbf{H})$, indexed from $0$.

Every statement bounds the probability of the failure event, written as the negation of the
guarantee, `μ.real {ω | ¬ error ω ≤ bound}`; the failure probability is $e^{-(u-2)/4}$ plus
`NLAlib.gaussianPinvFrobTail k d t`, at present
<!-- value gaussianPinvFrobTail k d t -->
$2\sqrt{k}\,(d/(2t))^{d/2}/\Gamma(d/2 + 1)$<!-- /value -->, which is smaller than Tropp and Webber's
$\sqrt{\pi k}\,(e/t)^{d/2}$. The primary tail is their Corollary 8.2 (NysSVD1), in every unitarily
invariant norm, with its Schatten, trace and spectral corollaries and the truncated outputs.

Each statement is a corollary of the corresponding tail of the randomized SVD
(`NLAlib.LowRank.Gaussian.RangeFinderTail`) through the Gram correspondence: with
$\mathbf{H} = \mathbf{F}^{\mathsf{H}}\mathbf{F}$ the failure events are equal
(`NLAlib.conjTranspose_mul_self_sub_nystrom`,
`NLAlib.SymmetricGauge.matrixNorm_conjTranspose_mul_self_sub_truncatedSVD`,
`NLAlib.nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD`,
`NLAlib.nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD_nystrom`). The spectral tails of
truncated Nyström add reverse Eckart–Young to the trace tail.

**Measurability.** The spectral error of truncated Nyström depends on the choice the truncation
makes and is not known to be measurable. Its tails bound `μ.real` of a possibly non-measurable
set, which is the outer measure: the failure event lies in a measurable event of at most the
stated probability. The success-set form does not follow without measurability. Design:
`docs/design/LowRank-S5.md` §3.4 and §8.

## Main results

* `NLAlib.SymmetricGauge.measureReal_not_matrixNorm_sub_nystrom_le_le_of_hasLaw_gaussianMatrix`:
  every unitarily invariant norm.
* in the `Matrix.PosSemidef` namespace:
  `measureReal_not_schattenNorm_sub_nystrom_le_le_of_hasLaw_gaussianMatrix`,
  `measureReal_not_nuclearNorm_sub_nystrom_le_le_of_hasLaw_gaussianMatrix`,
  `measureReal_not_specNorm_sub_nystrom_le_le_of_hasLaw_gaussianMatrix`: Schatten, trace and
  spectral norms;
  `measureReal_not_nuclearNorm_sub_truncatedSVD_nystrom_le_le_of_hasLaw_gaussianMatrix`,
  `measureReal_not_specNorm_sub_le_le_of_isBestRankApprox_nystrom_of_hasLaw_gaussianMatrix`,
  `measureReal_not_specNorm_sub_truncatedSVD_nystrom_le_le_of_hasLaw_gaussianMatrix`: truncated
  Nyström.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix ComplexOrder MatrixOrder ENNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n l : Type*} [Fintype n]
  [Fintype l] {H : Matrix n n ℝ} {X : Ω → Matrix n l ℝ}

/-! ### The untruncated output -/

/-- **The tail of randomized Nyström, every unitarily invariant norm**: for positive
semidefinite $\mathbf{H}$, a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$,
$d = \ell - k + 1$, any $u$ and $t > 0$,
$$\|\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{X})\|_{\Phi} \le
\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_{\Phi} + \Phi(\mathbf{e}_0)\,\frac{utk}{d}\,
\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_*$$
outside probability $e^{-(u-2)/4}$ + `gaussianPinvFrobTail k d t` (at present
<!-- value gaussianPinvFrobTail k d t -->
$2\sqrt{k}\,(d/(2t))^{d/2}/\Gamma(d/2 + 1)$<!-- /value -->), with $\mathbf{e}_0$ the first
unit coordinate sequence. The Gram-form tail of the randomized SVD at a factor of $\mathbf{H}$
(in `NLAlib.SymmetricGauge`,
`measureReal_not_matrixNorm_conjTranspose_mul_self_sub_rsvd_le_le_of_hasLaw_gaussianMatrix`),
with the same constants. For $u \le 2$, or $d = 0$, the bound is at least $1$.
[TroppWebber2023, Corollary 8.2 (NysSVD1)]; there for Schatten norms $1 \le p \le \infty$, with
$u, t \ge 0$ and the larger second failure term $\sqrt{\pi k}\,(t/e)^{-d/2}$; here every
unitarily invariant norm, $t > 0$ and any $u$.
Result: randomized-nystrom-tail -/
theorem SymmetricGauge.measureReal_not_matrixNorm_sub_nystrom_le_le_of_hasLaw_gaussianMatrix
    (Φ : SymmetricGauge) (hH : H.PosSemidef) (hX : HasLaw X (gaussianMatrix n l) μ) {k d : ℕ}
    (hd : k + d = Fintype.card l + 1) (u : ℝ) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | ¬ Φ.matrixNorm (H - nystrom H (X ω)) ≤
        Φ.matrixNorm (H - truncatedSVD H k) +
          Φ (Finsupp.single 0 1) * (u * t * k / d) * nuclearNorm (H - truncatedSVD H k)} ≤
      Real.exp (-(u - 2) / 4) + gaussianPinvFrobTail k d t := by
  classical
  obtain ⟨F, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hH.nonneg
  simp only [Matrix.star_eq_conjTranspose, conjTranspose_mul_self_sub_nystrom,
    Φ.matrixNorm_conjTranspose_mul_self_sub_truncatedSVD,
    nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD]
  exact Φ.measureReal_not_matrixNorm_conjTranspose_mul_self_sub_rsvd_le_le_of_hasLaw_gaussianMatrix
    F hX hd u ht

open SymmetricGauge in
/-- **The tail of randomized Nyström, Schatten norms**: for $1 \le p \le \infty$, with the
hypotheses of the gauge form (in `NLAlib.SymmetricGauge`,
`measureReal_not_matrixNorm_sub_nystrom_le_le_of_hasLaw_gaussianMatrix`),
$$\|\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{X})\|_{S_p} \le
\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_{S_p} + \frac{utk}{d}\,
\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_*$$
outside probability $e^{-(u-2)/4}$ + `gaussianPinvFrobTail k d t` (at present
<!-- value gaussianPinvFrobTail k d t -->
$2\sqrt{k}\,(d/(2t))^{d/2}/\Gamma(d/2 + 1)$<!-- /value -->).
[TroppWebber2023, Corollary 8.2 (NysSVD1)]; as printed there, with a smaller second failure term.
Result: randomized-nystrom-tail -/
theorem
_root_.Matrix.PosSemidef.measureReal_not_schattenNorm_sub_nystrom_le_le_of_hasLaw_gaussianMatrix
    (hH : H.PosSemidef) (hX : HasLaw X (gaussianMatrix n l) μ) {k d : ℕ}
    (hd : k + d = Fintype.card l + 1) {p : ℝ≥0∞} (hp : 1 ≤ p) (u : ℝ) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | ¬ schattenNorm p (H - nystrom H (X ω)) ≤
        schattenNorm p (H - truncatedSVD H k) +
          u * t * k / d * nuclearNorm (H - truncatedSVD H k)} ≤
      Real.exp (-(u - 2) / 4) + gaussianPinvFrobTail k d t := by
  have h := measureReal_not_matrixNorm_sub_nystrom_le_le_of_hasLaw_gaussianMatrix (lpGauge p hp)
    hH hX hd u ht
  simpa only [lpGauge_matrixNorm hp, lpGauge_apply_single_zero hp, one_mul] using h

open SymmetricGauge in
/-- **The tail of randomized Nyström, trace**: with the hypotheses of the gauge form (in
`NLAlib.SymmetricGauge`, `measureReal_not_matrixNorm_sub_nystrom_le_le_of_hasLaw_gaussianMatrix`),
$$\|\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{X})\|_* \le
\Bigl(1 + \frac{utk}{d}\Bigr)\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_*$$
outside probability $e^{-(u-2)/4}$ + `gaussianPinvFrobTail k d t` (at present
<!-- value gaussianPinvFrobTail k d t -->
$2\sqrt{k}\,(d/(2t))^{d/2}/\Gamma(d/2 + 1)$<!-- /value -->). The error is positive
semidefinite, so this bounds $\operatorname{tr}(\mathbf{H} - \mathsf{nystrom}(\mathbf{H},
\mathbf{X}))$.
[TroppWebber2023, Corollary 8.2 (NysSVD1)]; there at $p = 1$, with a larger second failure term.
Result: randomized-nystrom-tail -/
theorem
_root_.Matrix.PosSemidef.measureReal_not_nuclearNorm_sub_nystrom_le_le_of_hasLaw_gaussianMatrix
    (hH : H.PosSemidef) (hX : HasLaw X (gaussianMatrix n l) μ) {k d : ℕ}
    (hd : k + d = Fintype.card l + 1) (u : ℝ) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | ¬ nuclearNorm (H - nystrom H (X ω)) ≤
        (1 + u * t * k / d) * nuclearNorm (H - truncatedSVD H k)} ≤
      Real.exp (-(u - 2) / 4) + gaussianPinvFrobTail k d t := by
  have h := measureReal_not_matrixNorm_sub_nystrom_le_le_of_hasLaw_gaussianMatrix
    (lpGauge 1 le_rfl) hH hX hd u ht
  simp only [lpGauge_one_matrixNorm, lpGauge_apply_single_zero, one_mul] at h
  rwa [add_mul, one_mul]

open SymmetricGauge in
/-- **The tail of randomized Nyström, spectral norm**: with the hypotheses of the gauge form (in
`NLAlib.SymmetricGauge`, `measureReal_not_matrixNorm_sub_nystrom_le_le_of_hasLaw_gaussianMatrix`),
$$\|\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{X})\|_2 \le \lambda_k(\mathbf{H}) +
\frac{utk}{d}\,\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_*$$
outside probability $e^{-(u-2)/4}$ + `gaussianPinvFrobTail k d t` (at present
<!-- value gaussianPinvFrobTail k d t -->
$2\sqrt{k}\,(d/(2t))^{d/2}/\Gamma(d/2 + 1)$<!-- /value -->), eigenvalues indexed from $0$.
[TroppWebber2023, Corollary 8.2 (NysSVD1)]; there at $p = \infty$, with a larger second failure
term.
Result: randomized-nystrom-tail -/
theorem _root_.Matrix.PosSemidef.measureReal_not_specNorm_sub_nystrom_le_le_of_hasLaw_gaussianMatrix
    (hH : H.PosSemidef) (hX : HasLaw X (gaussianMatrix n l) μ) {k d : ℕ}
    (hd : k + d = Fintype.card l + 1) (u : ℝ) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | ¬ specNorm (H - nystrom H (X ω)) ≤
        singularValues H k + u * t * k / d * nuclearNorm (H - truncatedSVD H k)} ≤
      Real.exp (-(u - 2) / 4) + gaussianPinvFrobTail k d t := by
  have h := measureReal_not_matrixNorm_sub_nystrom_le_le_of_hasLaw_gaussianMatrix
    (lpGauge ⊤ le_top) hH hX hd u ht
  simpa only [lpGauge_top_matrixNorm, lpGauge_apply_single_zero le_top, one_mul,
    specNorm_sub_truncatedSVD] using h

/-! ### The late-truncated output -/

-- The declaration name alone, with its `_root_.Matrix.PosSemidef` prefix, exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The tail of truncated Nyström, trace**: with the hypotheses of
`Matrix.PosSemidef.measureReal_not_nuclearNorm_sub_nystrom_le_le_of_hasLaw_gaussianMatrix`,
$$\|\mathbf{H} - \llbracket\mathsf{nystrom}(\mathbf{H}, \mathbf{X})\rrbracket_k\|_* \le
\Bigl(1 + \frac{utk}{d}\Bigr)\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_*$$
outside probability $e^{-(u-2)/4}$ + `gaussianPinvFrobTail k d t` (at present
<!-- value gaussianPinvFrobTail k d t -->
$2\sqrt{k}\,(d/(2t))^{d/2}/\Gamma(d/2 + 1)$<!-- /value -->), for every choice of the
truncation: the late truncation costs nothing. The error does not depend on the choice (it is the
squared Frobenius error of the truncated randomized SVD of a factor,
`NLAlib.measureReal_not_frobNorm_sub_truncatedSVD_rsvd_sq_le_le_of_hasLaw_gaussianMatrix`), so
the failure event is measurable.
[TroppWebber2023, Corollary 8.2 (NysSVD1)] with [TroppYurtseverUdellCevher2017a, Remark A.4];
there announced ("We omit the details"), composed here.
Result: randomized-nystrom-tail -/
theorem
_root_.Matrix.PosSemidef.measureReal_not_nuclearNorm_sub_truncatedSVD_nystrom_le_le_of_hasLaw_gaussianMatrix
    (hH : H.PosSemidef) (hX : HasLaw X (gaussianMatrix n l) μ) {k d : ℕ}
    (hd : k + d = Fintype.card l + 1) (u : ℝ) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | ¬ nuclearNorm (H - truncatedSVD (nystrom H (X ω)) k) ≤
        (1 + u * t * k / d) * nuclearNorm (H - truncatedSVD H k)} ≤
      Real.exp (-(u - 2) / 4) + gaussianPinvFrobTail k d t := by
  classical
  obtain ⟨F, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hH.nonneg
  simp only [Matrix.star_eq_conjTranspose,
    nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD_nystrom,
    nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD]
  exact measureReal_not_frobNorm_sub_truncatedSVD_rsvd_sq_le_le_of_hasLaw_gaussianMatrix F hX hd u
    ht

-- The declaration name alone, with its `_root_.Matrix.PosSemidef` prefix, exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The tail of truncated Nyström, spectral norm** (Martinsson and Tropp's Theorem 14.1 in tail
form), for any best rank-$k$ approximations $\mathbf{Y}(\omega)$ of
$\mathsf{nystrom}(\mathbf{H}, \mathbf{X})$, no measurability: with the hypotheses of
`Matrix.PosSemidef.measureReal_not_specNorm_sub_nystrom_le_le_of_hasLaw_gaussianMatrix`,
$$\|\mathbf{H} - \mathbf{Y}\|_2 \le \lambda_k(\mathbf{H}) +
\frac{utk}{d}\,\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_*$$
outside probability $e^{-(u-2)/4}$ + `gaussianPinvFrobTail k d t` (at present
<!-- value gaussianPinvFrobTail k d t -->
$2\sqrt{k}\,(d/(2t))^{d/2}/\Gamma(d/2 + 1)$<!-- /value -->), the bound of the untruncated
output, eigenvalues indexed from $0$. The failure event lies inside that of the trace tail of
truncated Nyström, by reverse Eckart–Young
(`NLAlib.specNorm_sub_add_nuclearNorm_sub_truncatedSVD_le_of_rank_le`). The event may be
non-measurable; `μ.real` is then the outer measure, so this bound says exactly that the failure
event lies in a measurable event of at most this probability
(`MeasureTheory.exists_measurable_superset`). The success-set form, probability at least
$1 - \delta$ for the good event, does not follow without measurability
(`MeasureTheory.measureReal_compl` needs `MeasurableSet`).
[TroppWebber2023, Corollary 8.2 (NysSVD1)] with [TroppYurtseverUdellCevher2017a, Proposition
A.8]; composed here.
Result: randomized-nystrom-tail -/
theorem
_root_.Matrix.PosSemidef.measureReal_not_specNorm_sub_le_le_of_isBestRankApprox_nystrom_of_hasLaw_gaussianMatrix
    (hH : H.PosSemidef) (hX : HasLaw X (gaussianMatrix n l) μ) {k d : ℕ}
    (hd : k + d = Fintype.card l + 1) {Y : Ω → Matrix n n ℝ}
    (hY : ∀ ω, IsBestRankApprox (nystrom H (X ω)) k (Y ω)) (u : ℝ) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | ¬ specNorm (H - Y ω) ≤
        singularValues H k + u * t * k / d * nuclearNorm (H - truncatedSVD H k)} ≤
      Real.exp (-(u - 2) / 4) + gaussianPinvFrobTail k d t := by
  have := hX.isProbabilityMeasure
  refine (measureReal_mono (fun ω hω => ?_) (measure_ne_top μ _)).trans
    (hH.measureReal_not_nuclearNorm_sub_truncatedSVD_nystrom_le_le_of_hasLaw_gaussianMatrix hX hd
      u ht)
  intro h
  apply hω
  have h1 := specNorm_sub_add_nuclearNorm_sub_truncatedSVD_le_of_rank_le H (hY ω).rank_le
  have h2 := hH.nuclearNorm_sub_le_nuclearNorm_sub_truncatedSVD_nystrom_of_isBestRankApprox (hY ω)
  linarith

-- The declaration name alone, with its `_root_.Matrix.PosSemidef` prefix, exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The tail of truncated Nyström, spectral norm**, for the output
`truncatedSVD (nystrom H (X ω)) k`: with the hypotheses of
`Matrix.PosSemidef.measureReal_not_specNorm_sub_nystrom_le_le_of_hasLaw_gaussianMatrix`,
$$\|\mathbf{H} - \llbracket\mathsf{nystrom}(\mathbf{H}, \mathbf{X})\rrbracket_k\|_2 \le
\lambda_k(\mathbf{H}) + \frac{utk}{d}\,\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_*$$
outside probability $e^{-(u-2)/4}$ + `gaussianPinvFrobTail k d t` (at present
<!-- value gaussianPinvFrobTail k d t -->
$2\sqrt{k}\,(d/(2t))^{d/2}/\Gamma(d/2 + 1)$<!-- /value -->). The event may be
non-measurable (the truncation is a choice); `μ.real` is then the outer measure, and the bound
says that the failure event lies in a measurable event of at most this probability. The
success-set form, probability at least $1 - \delta$ for the good event, does not follow without
measurability (`MeasureTheory.measureReal_compl` needs `MeasurableSet`).
[TroppWebber2023, Corollary 8.2 (NysSVD1)] with [TroppYurtseverUdellCevher2017a, Proposition
A.8]; composed here.
Result: randomized-nystrom-tail -/
theorem
_root_.Matrix.PosSemidef.measureReal_not_specNorm_sub_truncatedSVD_nystrom_le_le_of_hasLaw_gaussianMatrix
    (hH : H.PosSemidef) (hX : HasLaw X (gaussianMatrix n l) μ) {k d : ℕ}
    (hd : k + d = Fintype.card l + 1) (u : ℝ) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | ¬ specNorm (H - truncatedSVD (nystrom H (X ω)) k) ≤
        singularValues H k + u * t * k / d * nuclearNorm (H - truncatedSVD H k)} ≤
      Real.exp (-(u - 2) / 4) + gaussianPinvFrobTail k d t :=
  hH.measureReal_not_specNorm_sub_le_le_of_isBestRankApprox_nystrom_of_hasLaw_gaussianMatrix hX
    hd (fun _ => isBestRankApprox_truncatedSVD _ k) u ht

end NLAlib
