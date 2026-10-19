/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Gaussian.RangeFinder
public import NLAlib.LowRank.Random.Nystrom

/-!
# The expected error of Gaussian Nyström

For a real positive semidefinite $\mathbf{H}$ and a standard Gaussian $n \times \ell$ test matrix
$\mathbf{X}$, the Nyström approximation $\mathsf{nystrom}(\mathbf{H}, \mathbf{X})$
(`NLAlib.nystrom`) has, for a target rank $k$ with $k + 2 \le \ell$,
$$\mathbb{E}\|\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{X})\|_* \le
\Bigl(1 + \frac{k}{\ell - k - 1}\Bigr)\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_*\,,$$
and in every unitarily invariant norm the bound of Tropp and Webber's Corollary 8.2 (NysSVD2),
with its Schatten, spectral and Frobenius corollaries. The late-truncated output
`truncatedSVD (nystrom H (X ω)) k` keeps the trace bound (fixed-rank Nyström, TYUC Theorem 4.1),
and its spectral error obeys Martinsson and Tropp's Theorem 14.1 for a measurable choice of the
truncation; two spectral-decay forms (TYUC Theorem 4.2, with constant one) are here too. Every
error is $\mathbf{H}$ minus the named output, every bound is in $\mathbf{H}$'s own best errors
$\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_{\Phi}$,
$\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_* = \sum_{i \ge k}\lambda_i(\mathbf{H})$ and
$\sigma_k(\mathbf{H}) = \lambda_k(\mathbf{H})$, indexed from $0$.

Each statement is a corollary of the corresponding statement for the randomized SVD
(`NLAlib.LowRank.Gaussian.RangeFinder`) through the Gram correspondence: with
$\mathbf{H} = \mathbf{F}^{\mathsf{H}}\mathbf{F}$, the Nyström error is the Gram matrix of the
randomized SVD error of $\mathbf{F}$ (`NLAlib.conjTranspose_mul_self_sub_nystrom`), the best
errors of $\mathbf{H}$ are those of $\mathbf{F}$ squared
(`NLAlib.SymmetricGauge.matrixNorm_conjTranspose_mul_self_sub_truncatedSVD`,
`NLAlib.nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD`), and the trace error of truncated
Nyström is the squared Frobenius error of the truncated randomized SVD
(`NLAlib.nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD_nystrom`). The constants are the
range finder's. The spectral bounds for truncated Nyström add reverse Eckart–Young
(`NLAlib.LowRank.Random.Nystrom`).

The spectral error of truncated Nyström depends on the choice `truncatedSVD` makes; its
expectation is stated for any measurable choice of best approximations and, directly, for
`truncatedSVD`, which is Borel measurable (`NLAlib.measurable_truncatedSVD`). The hypothesis
$k + 2 \le \ell$ is necessary: at $\ell = k + 1$ the expectation is not bounded by any multiple of
$\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_*$. Design:
`docs/design/LowRank-S5.md` §3.3, §8; `docs/design/LowRank-S2c.md` §8 item 8.

## Main results

* `Matrix.PosSemidef.ae_nystrom_eq_self_of_hasLaw_gaussianMatrix`: exact recovery at
  $\operatorname{rank}\mathbf{H} \le \ell$.
* `NLAlib.SymmetricGauge.integral_matrixNorm_sub_nystrom_le_of_hasLaw_gaussianMatrix`: every
  unitarily invariant norm.
* `Matrix.PosSemidef.integral_nuclearNorm_sub_nystrom_le_of_hasLaw_gaussianMatrix`,
  `Matrix.PosSemidef.integral_schattenNorm_sub_nystrom_le_of_hasLaw_gaussianMatrix`,
  `Matrix.PosSemidef.integral_specNorm_sub_nystrom_le_of_hasLaw_gaussianMatrix`,
  `Matrix.PosSemidef.integral_frobNorm_sub_nystrom_le_of_hasLaw_gaussianMatrix`: trace, Schatten,
  spectral and Frobenius norms.
* in the `Matrix.PosSemidef` namespace, truncated Nyström:
  `integral_nuclearNorm_sub_truncatedSVD_nystrom_le_of_hasLaw_gaussianMatrix` (trace),
  `integral_specNorm_sub_le_of_isBestRankApprox_nystrom_of_hasLaw_gaussianMatrix` (MT Theorem
  14.1, for a measurable selector) and its direct form
  `integral_specNorm_sub_truncatedSVD_nystrom_le_of_hasLaw_gaussianMatrix`, and the spectral-decay
  forms `integral_nuclearNorm_sub_truncatedSVD_nystrom_le_add_of_hasLaw_gaussianMatrix`,
  `integral_specNorm_sub_le_add_of_isBestRankApprox_nystrom_of_hasLaw_gaussianMatrix` and its
  direct form `integral_specNorm_sub_truncatedSVD_nystrom_le_add_of_hasLaw_gaussianMatrix`.
* the asymptotic forms of the two trace bounds, $O(k/\varepsilon)$ samples for relative error
  $1 + \varepsilon$: `NLAlib.exists_forall_` followed by their names in `Matrix.PosSemidef`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix ComplexOrder MatrixOrder ENNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n l : Type*} [Fintype n]
  [Fintype l] {H : Matrix n n ℝ} {X : Ω → Matrix n l ℝ}

/-! ### Exact recovery -/

/-- **A Gaussian sketch at least as wide as the rank makes Nyström exact**: for positive
semidefinite $\mathbf{H}$ with $\operatorname{rank}\mathbf{H} \le \ell$ and a standard Gaussian
$n \times \ell$ test matrix $\mathbf{X}$, $\mathsf{nystrom}(\mathbf{H}, \mathbf{X}) = \mathbf{H}$
almost surely. -/
theorem _root_.Matrix.PosSemidef.ae_nystrom_eq_self_of_hasLaw_gaussianMatrix (hH : H.PosSemidef)
    (hX : HasLaw X (gaussianMatrix n l) μ) (hHl : H.rank ≤ Fintype.card l) :
    ∀ᵐ ω ∂μ, nystrom H (X ω) = H := by
  filter_upwards [ae_rank_mul_eq_min_of_hasLaw_gaussianMatrix H hX] with ω hω
  exact hH.nystrom_eq_self_of_rank_eq (hω.trans (min_eq_left hHl))

/-! ### The untruncated output -/

/-- **The expected error of randomized Nyström, every unitarily invariant norm**: for positive
semidefinite $\mathbf{H}$, a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$ and
$k + 2 \le \ell$,
$$\mathbb{E}\|\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{X})\|_{\Phi} \le
\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_{\Phi} + \Phi(\mathbf{e}_0)\,
\frac{k}{\ell - k - 1}\,\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_*\,,$$
with $\mathbf{e}_0$ the first unit coordinate sequence ($\Phi(\mathbf{e}_0) = 1$ for every
Schatten gauge, `NLAlib.lpGauge_apply_single_zero`). The Gram form of the randomized SVD's
expected error at a factor of $\mathbf{H}$, with the same constant (in `NLAlib.SymmetricGauge`,
`integral_matrixNorm_conjTranspose_mul_self_sub_rsvd_le_of_hasLaw_gaussianMatrix`); no square
root.
[TroppWebber2023, Corollary 8.2 (NysSVD2)]; [MartinssonTropp2020, §14.4];
[TroppYurtseverUdellCevher2017a, Theorem A.1]; there Schatten $1 \le p \le \infty$ (TW) or the
trace (TYUC), here every unitarily invariant norm, with the factor $\Phi(\mathbf{e}_0)$.
Result: randomized-nystrom-expected-error -/
theorem SymmetricGauge.integral_matrixNorm_sub_nystrom_le_of_hasLaw_gaussianMatrix
    (Φ : SymmetricGauge) (hH : H.PosSemidef) (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ}
    (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, Φ.matrixNorm (H - nystrom H (X ω)) ∂μ ≤
      Φ.matrixNorm (H - truncatedSVD H k) +
        Φ (Finsupp.single 0 1) * ((k : ℝ) / ((Fintype.card l : ℝ) - k - 1)) *
          nuclearNorm (H - truncatedSVD H k) := by
  classical
  obtain ⟨F, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hH.nonneg
  simp only [Matrix.star_eq_conjTranspose, conjTranspose_mul_self_sub_nystrom,
    Φ.matrixNorm_conjTranspose_mul_self_sub_truncatedSVD,
    nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD]
  exact Φ.integral_matrixNorm_conjTranspose_mul_self_sub_rsvd_le_of_hasLaw_gaussianMatrix F hX hk

open SymmetricGauge in
/-- **The expected error of randomized Nyström, trace**: for positive semidefinite $\mathbf{H}$,
a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$ and
$k + 2 \le \ell$, <!-- value gaussianProjectionFactor k \ell -->
$$\mathbb{E}\|\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{X})\|_* \le
\Bigl(1 + \frac{k}{\ell - k - 1}\Bigr)\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_*\,.$$
The error is positive semidefinite, so this is
$\mathbb{E}\operatorname{tr}(\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{X}))$. The trace
instance of the Gram-form bound above; Epperly and Webber's sharper factor, with a rank
parameter, is
`Matrix.PosSemidef.integral_nuclearNorm_sub_nystrom_le_of_hasLaw_gaussianMatrix_of_rank_le`.
Asymptotic form:
`NLAlib.exists_forall_integral_nuclearNorm_sub_nystrom_le_of_hasLaw_gaussianMatrix`.
[TroppYurtseverUdellCevher2017a, Theorem A.1]; [TroppWebber2023, Corollary 8.8]; there with a
minimum over the comparison rank (TYUC) and $k \ge 1$, here at one rank, any $k$; the first case
of TW Corollary 8.8.
Result: randomized-nystrom-expected-error -/
theorem _root_.Matrix.PosSemidef.integral_nuclearNorm_sub_nystrom_le_of_hasLaw_gaussianMatrix
    (hH : H.PosSemidef) (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ}
    (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, nuclearNorm (H - nystrom H (X ω)) ∂μ ≤
      gaussianProjectionFactor k (Fintype.card l) * nuclearNorm (H - truncatedSVD H k) := by
  have h := integral_matrixNorm_sub_nystrom_le_of_hasLaw_gaussianMatrix (lpGauge 1 le_rfl) hH hX hk
  simp only [lpGauge_one_matrixNorm, lpGauge_apply_single_zero, one_mul] at h
  rw [gaussianProjectionFactor_def]
  linarith

/-- **$O(k/\varepsilon)$ samples suffice for randomized Nyström**, trace: there are absolute
constants $C, \varepsilon_0 > 0$ such that for positive semidefinite $\mathbf{H}$, a standard
Gaussian $n \times \ell$ test matrix $\mathbf{X}$, $k \ge 1$, $0 < \varepsilon \le \varepsilon_0$
and $\ell \ge Ck/\varepsilon$,
$$\mathbb{E}\|\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{X})\|_* \le
(1 + \varepsilon)\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_*\,.$$
The asymptotic form of
`Matrix.PosSemidef.integral_nuclearNorm_sub_nystrom_le_of_hasLaw_gaussianMatrix`; the proof takes
$C = 3$ and $\varepsilon_0 = 1$.
[TroppYurtseverUdellCevher2017a, §4, after Theorem 4.1]; there $\ell = (1 + 1/\varepsilon)k + 1$,
for the truncated output, whose error is the larger.
Asymptotic: Matrix.PosSemidef.integral_nuclearNorm_sub_nystrom_le_of_hasLaw_gaussianMatrix
Result: randomized-nystrom-expected-error -/
theorem exists_forall_integral_nuclearNorm_sub_nystrom_le_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω n l : Type} [MeasurableSpace Ω] [Fintype n] [Fintype l]
      (μ : Measure Ω) (H : Matrix n n ℝ) (X : Ω → Matrix n l ℝ) (k : ℕ) (ε : ℝ),
      H.PosSemidef → HasLaw X (gaussianMatrix n l) μ → 0 < k → 0 < ε → ε ≤ ε₀ →
      C * ((k : ℝ) / ε) ≤ Fintype.card l →
      ∫ ω, nuclearNorm (H - nystrom H (X ω)) ∂μ ≤
        (1 + ε) * nuclearNorm (H - truncatedSVD H k) := by
  refine ⟨3, 1, by norm_num, one_pos, ?_⟩
  intro Ω n l _ _ _ μ H X k ε hH hX hk hε hε1 hl
  obtain ⟨hkl, hg⟩ := gaussianProjectionFactor_le_one_add_of_three_mul_div_le hk hε hε1 hl
  exact (hH.integral_nuclearNorm_sub_nystrom_le_of_hasLaw_gaussianMatrix hX hkl).trans
    (mul_le_mul_of_nonneg_right hg (nuclearNorm_nonneg _))

open SymmetricGauge in
/-- **The expected error of randomized Nyström, Schatten norms**: for positive semidefinite
$\mathbf{H}$, a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$, $k + 2 \le \ell$ and
$1 \le p \le \infty$,
$$\mathbb{E}\|\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{X})\|_{S_p} \le
\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_{S_p} + \frac{k}{\ell - k - 1}
\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_*\,.$$
[TroppWebber2023, Corollary 8.2 (NysSVD2)]; as printed there, with $k + 2 \le \ell$ and no
hypothesis on $k \ge 1$.
Result: randomized-nystrom-expected-error -/
theorem _root_.Matrix.PosSemidef.integral_schattenNorm_sub_nystrom_le_of_hasLaw_gaussianMatrix
    (hH : H.PosSemidef) (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ}
    (hk : k + 2 ≤ Fintype.card l) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    ∫ ω, schattenNorm p (H - nystrom H (X ω)) ∂μ ≤
      schattenNorm p (H - truncatedSVD H k) +
        (k : ℝ) / ((Fintype.card l : ℝ) - k - 1) * nuclearNorm (H - truncatedSVD H k) := by
  have h := integral_matrixNorm_sub_nystrom_le_of_hasLaw_gaussianMatrix (lpGauge p hp) hH hX hk
  simpa only [lpGauge_matrixNorm hp, lpGauge_apply_single_zero hp, one_mul] using h

open SymmetricGauge in
/-- **The expected error of randomized Nyström, spectral norm**: for positive semidefinite
$\mathbf{H}$, a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$ and $k + 2 \le \ell$,
$$\mathbb{E}\|\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{X})\|_2 \le
\lambda_k(\mathbf{H}) + \frac{k}{\ell - k - 1}\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_*
\,,$$
eigenvalues indexed from $0$ ($\lambda_k(\mathbf{H})$ is `singularValues H k`): the squared
spectral error of the randomized SVD of a factor
(`NLAlib.integral_specNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix`).
[TroppWebber2023, Corollary 8.2 (NysSVD2)]; there at $p = \infty$.
Result: randomized-nystrom-expected-error -/
theorem _root_.Matrix.PosSemidef.integral_specNorm_sub_nystrom_le_of_hasLaw_gaussianMatrix
    (hH : H.PosSemidef) (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ}
    (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, specNorm (H - nystrom H (X ω)) ∂μ ≤
      singularValues H k +
        (k : ℝ) / ((Fintype.card l : ℝ) - k - 1) * nuclearNorm (H - truncatedSVD H k) := by
  have h := integral_matrixNorm_sub_nystrom_le_of_hasLaw_gaussianMatrix (lpGauge ⊤ le_top) hH hX hk
  simpa only [lpGauge_top_matrixNorm, lpGauge_apply_single_zero le_top, one_mul,
    specNorm_sub_truncatedSVD] using h

/-- **The expected error of randomized Nyström, Frobenius norm**: for positive semidefinite
$\mathbf{H}$, a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$ and $k + 2 \le \ell$,
$$\mathbb{E}\|\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{X})\|_{\mathsf{F}} \le
\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_{\mathsf{F}} + \frac{k}{\ell - k - 1}
\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_*\,.$$
[TroppWebber2023, Corollary 8.2 (NysSVD2)]; there at $p = 2$.
Result: randomized-nystrom-expected-error -/
theorem _root_.Matrix.PosSemidef.integral_frobNorm_sub_nystrom_le_of_hasLaw_gaussianMatrix
    (hH : H.PosSemidef) (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ}
    (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, frobNorm (H - nystrom H (X ω)) ∂μ ≤
      frobNorm (H - truncatedSVD H k) +
        (k : ℝ) / ((Fintype.card l : ℝ) - k - 1) * nuclearNorm (H - truncatedSVD H k) := by
  simpa only [schattenNorm_two] using
    hH.integral_schattenNorm_sub_nystrom_le_of_hasLaw_gaussianMatrix hX hk one_le_two

/-! ### The late-truncated output -/

-- A docstring line names a declaration whose name exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The expected trace error of truncated Nyström** (fixed-rank Nyström): for positive
semidefinite $\mathbf{H}$, a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$,
$k + 2 \le \ell$ and every choice of the truncation,
$$\mathbb{E}\|\mathbf{H} - \llbracket\mathsf{nystrom}(\mathbf{H}, \mathbf{X})\rrbracket_k\|_*
\le \Bigl(1 + \frac{k}{\ell - k - 1}\Bigr)\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_*\,,$$
the bound of the untruncated output. The error does not depend on the choice: it is the squared
Frobenius error of the truncated randomized SVD of a factor
(`NLAlib.integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_hasLaw_gaussianMatrix`). Incomparable with
the decay form with Epperly and Webber's factor,
`Matrix.PosSemidef.integral_nuclearNorm_sub_truncatedSVD_nystrom_le_add_of_isLeftUnitarilyInvariant_of_rank_le`
(a Gaussian test matrix is an instance), which is better for rank close to $\ell$ or a decaying
tail. Asymptotic form:
`NLAlib.exists_forall_integral_nuclearNorm_sub_truncatedSVD_nystrom_le_of_hasLaw_gaussianMatrix`.
[TroppYurtseverUdellCevher2017a, Theorem 4.1 (4.1)]; there with $1 \le k$ and $\ell \le n$,
neither needed here, and through Gu's projected truncation; here through Woodruff's truncation
for free.
Result: randomized-nystrom-expected-error -/
theorem
_root_.Matrix.PosSemidef.integral_nuclearNorm_sub_truncatedSVD_nystrom_le_of_hasLaw_gaussianMatrix
    (hH : H.PosSemidef) (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ}
    (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, nuclearNorm (H - truncatedSVD (nystrom H (X ω)) k) ∂μ ≤
      gaussianProjectionFactor k (Fintype.card l) * nuclearNorm (H - truncatedSVD H k) := by
  classical
  obtain ⟨F, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hH.nonneg
  simp only [Matrix.star_eq_conjTranspose,
    nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD_nystrom,
    nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD]
  exact integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_hasLaw_gaussianMatrix F hX hk

/-- **$O(k/\varepsilon)$ samples suffice for truncated Nyström**, trace: there are absolute
constants $C, \varepsilon_0 > 0$ such that for positive semidefinite $\mathbf{H}$, a standard
Gaussian $n \times \ell$ test matrix $\mathbf{X}$, $0 < \varepsilon \le \varepsilon_0$ and
$\ell \ge Ck/\varepsilon$,
$$\mathbb{E}\|\mathbf{H} - \llbracket\mathsf{nystrom}(\mathbf{H}, \mathbf{X})\rrbracket_k\|_*
\le (1 + \varepsilon)\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_*\,.$$
The asymptotic form of
`Matrix.PosSemidef.integral_nuclearNorm_sub_truncatedSVD_nystrom_le_of_hasLaw_gaussianMatrix`; the
proof takes $C = 3$ and $\varepsilon_0 = 1$.
[TroppYurtseverUdellCevher2017a, §4, after Theorem 4.1]; there $\ell = (1 + 1/\varepsilon)k + 1$.
Asymptotic:
Matrix.PosSemidef.integral_nuclearNorm_sub_truncatedSVD_nystrom_le_of_hasLaw_gaussianMatrix
Result: randomized-nystrom-expected-error -/
theorem exists_forall_integral_nuclearNorm_sub_truncatedSVD_nystrom_le_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω n l : Type} [MeasurableSpace Ω] [Fintype n] [Fintype l]
      (μ : Measure Ω) (H : Matrix n n ℝ) (X : Ω → Matrix n l ℝ) (k : ℕ) (ε : ℝ),
      H.PosSemidef → HasLaw X (gaussianMatrix n l) μ → 0 < ε → ε ≤ ε₀ →
      C * ((k : ℝ) / ε) ≤ Fintype.card l →
      ∫ ω, nuclearNorm (H - truncatedSVD (nystrom H (X ω)) k) ∂μ ≤
        (1 + ε) * nuclearNorm (H - truncatedSVD H k) := by
  refine ⟨3, 1, by norm_num, one_pos, ?_⟩
  intro Ω n l _ _ _ μ H X k ε hH hX hε hε1 hl
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have := hX.isProbabilityMeasure
    simp only [truncatedSVD_zero, sub_zero, integral_const, probReal_univ, one_smul]
    nlinarith [nuclearNorm_nonneg H]
  obtain ⟨hkl, hg⟩ := gaussianProjectionFactor_le_one_add_of_three_mul_div_le hk hε hε1 hl
  exact (hH.integral_nuclearNorm_sub_truncatedSVD_nystrom_le_of_hasLaw_gaussianMatrix hX hkl).trans
    (mul_le_mul_of_nonneg_right hg (nuclearNorm_nonneg _))

-- The declaration name alone, with its `_root_.Matrix.PosSemidef` prefix, exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The expected spectral error of truncated Nyström** (Martinsson and Tropp's Theorem 14.1):
for positive semidefinite $\mathbf{H}$, a standard Gaussian $n \times \ell$ test matrix
$\mathbf{X}$, $k + 2 \le \ell$ and a measurable choice $\mathbf{Y}$ of best rank-$k$
approximations of $\mathsf{nystrom}(\mathbf{H}, \mathbf{X})$,
$$\mathbb{E}\|\mathbf{H} - \mathbf{Y}\|_2 \le \lambda_k(\mathbf{H}) + \frac{k}{\ell - k - 1}
\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_*\,,$$
eigenvalues indexed from $0$ (MT's $\lambda_{k+1}$), the bound of the untruncated output, by
reverse Eckart–Young from the trace bound.
Direct form at `truncatedSVD`:
`Matrix.PosSemidef.integral_specNorm_sub_truncatedSVD_nystrom_le_of_hasLaw_gaussianMatrix`.
[MartinssonTropp2020, Theorem 14.1]; [TroppYurtseverUdellCevher2017a, Theorem 4.1 (4.2)]; there
with $1 \le k < \ell \le n$ and for the truncation an algorithm computes; here $k + 2 \le \ell$,
any $n$, under a selector.
Result: randomized-nystrom-expected-error -/
theorem
_root_.Matrix.PosSemidef.integral_specNorm_sub_le_of_isBestRankApprox_nystrom_of_hasLaw_gaussianMatrix
    (hH : H.PosSemidef) (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ}
    (hk : k + 2 ≤ Fintype.card l) {Y : Ω → Matrix n n ℝ}
    (hY : ∀ ω, IsBestRankApprox (nystrom H (X ω)) k (Y ω)) (hYm : AEStronglyMeasurable Y μ) :
    ∫ ω, specNorm (H - Y ω) ∂μ ≤
      singularValues H k +
        (k : ℝ) / ((Fintype.card l : ℝ) - k - 1) * nuclearNorm (H - truncatedSVD H k) := by
  have := hX.isProbabilityMeasure
  have h1 :=
    hH.integral_specNorm_sub_add_nuclearNorm_sub_truncatedSVD_le_of_isBestRankApprox_nystrom
      hX.aemeasurable hY hYm
  have h2 := hH.integral_nuclearNorm_sub_truncatedSVD_nystrom_le_of_hasLaw_gaussianMatrix hX hk
  rw [gaussianProjectionFactor_def] at h2
  linarith

/-- **The expected spectral error of truncated Nyström** (Martinsson and Tropp's Theorem 14.1):
for positive semidefinite $\mathbf{H}$, a standard Gaussian $n \times \ell$ test matrix
$\mathbf{X}$ and $k + 2 \le \ell$,
$$\mathbb{E}\|\mathbf{H} - \llbracket\mathsf{nystrom}(\mathbf{H}, \mathbf{X})\rrbracket_k\|_2 \le
\lambda_k(\mathbf{H}) + \frac{k}{\ell - k - 1}
\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_*\,,$$
eigenvalues indexed from $0$ (MT's $\lambda_{k+1}$). The direct form of
`Matrix.PosSemidef.integral_specNorm_sub_le_of_isBestRankApprox_nystrom_of_hasLaw_gaussianMatrix`,
which covers any other measurable choice of the truncation.
[MartinssonTropp2020, Theorem 14.1]; [TroppYurtseverUdellCevher2017a, Theorem 4.1 (4.2)]; there
with $1 \le k < \ell \le n$; here $k + 2 \le \ell$, any $n$.
Result: randomized-nystrom-expected-error -/
theorem
_root_.Matrix.PosSemidef.integral_specNorm_sub_truncatedSVD_nystrom_le_of_hasLaw_gaussianMatrix
    (hH : H.PosSemidef) (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ}
    (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, specNorm (H - truncatedSVD (nystrom H (X ω)) k) ∂μ ≤
      singularValues H k +
        (k : ℝ) / ((Fintype.card l : ℝ) - k - 1) * nuclearNorm (H - truncatedSVD H k) :=
  hH.integral_specNorm_sub_le_of_isBestRankApprox_nystrom_of_hasLaw_gaussianMatrix hX hk
    (fun _ => isBestRankApprox_truncatedSVD _ k)
    ((measurable_truncatedSVD k).comp_aemeasurable
      ((measurable_nystrom H).comp_aemeasurable hX.aemeasurable)).aestronglyMeasurable

-- The declaration name alone, with its `_root_.Matrix.PosSemidef` prefix, exceeds 100 characters.
set_option linter.style.longLine false in
/-- **Truncated Nyström exploits spectral decay, trace**: for positive semidefinite
$\mathbf{H}$, a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$, any target rank $k$,
any comparison rank $q$ with $q + 2 \le \ell$ and every choice of the truncation,
$$\mathbb{E}\|\mathbf{H} - \llbracket\mathsf{nystrom}(\mathbf{H}, \mathbf{X})\rrbracket_k\|_*
\le \|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_* + \Bigl(1 + \frac{q}{\ell - q - 1}\Bigr)
\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_q\|_*\,.$$
Incomparable with
`Matrix.PosSemidef.integral_nuclearNorm_sub_truncatedSVD_nystrom_le_of_hasLaw_gaussianMatrix`:
better when the spectrum decays past $k$ and $q > k$. From the constant-one truncation lemma
`NLAlib.SymmetricGauge.matrixNorm_sub_truncatedSVD_nystrom_le` and the untruncated trace bound
at $q$.
[TroppYurtseverUdellCevher2017a, Theorem 4.2 (4.3)]; there with the constant $2$ in place of $1$
and a minimum over $q$; here the constant $1$ (Nyström does not increase singular values) at each
$q$.
Result: randomized-nystrom-expected-error -/
theorem
_root_.Matrix.PosSemidef.integral_nuclearNorm_sub_truncatedSVD_nystrom_le_add_of_hasLaw_gaussianMatrix
    (hH : H.PosSemidef) (hX : HasLaw X (gaussianMatrix n l) μ) (k : ℕ) {q : ℕ}
    (hq : q + 2 ≤ Fintype.card l) :
    ∫ ω, nuclearNorm (H - truncatedSVD (nystrom H (X ω)) k) ∂μ ≤
      nuclearNorm (H - truncatedSVD H k) +
        gaussianProjectionFactor q (Fintype.card l) * nuclearNorm (H - truncatedSVD H q) := by
  have := hX.isProbabilityMeasure
  have hpt : ∀ ω, nuclearNorm (H - truncatedSVD (nystrom H (X ω)) k) ≤
      nuclearNorm (H - truncatedSVD H k) + nuclearNorm (H - nystrom H (X ω)) := fun ω => by
    simpa only [lpGauge_one_matrixNorm] using
      (lpGauge 1 le_rfl).matrixNorm_sub_truncatedSVD_nystrom_le hH (X ω) k
  have hN := hH.integrable_nuclearNorm_sub_nystrom hX.aemeasurable
  have hI : Integrable (fun ω => nuclearNorm (H - truncatedSVD H k) +
      nuclearNorm (H - nystrom H (X ω))) μ := (integrable_const _).add hN
  refine (integral_mono (hH.integrable_nuclearNorm_sub_truncatedSVD_nystrom hX.aemeasurable k)
    hI hpt).trans ?_
  rw [integral_add (integrable_const _) hN, integral_const, probReal_univ, one_smul]
  exact add_le_add le_rfl (hH.integral_nuclearNorm_sub_nystrom_le_of_hasLaw_gaussianMatrix hX hq)

-- The declaration name alone, with its `_root_.Matrix.PosSemidef` prefix, exceeds 100 characters.
set_option linter.style.longLine false in
/-- **Truncated Nyström exploits spectral decay, spectral norm**: for positive semidefinite
$\mathbf{H}$, a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$, any target rank $k$,
a measurable choice $\mathbf{Y}$ of best rank-$k$ approximations of
$\mathsf{nystrom}(\mathbf{H}, \mathbf{X})$ and any comparison rank $q$ with $q + 2 \le \ell$,
$$\mathbb{E}\|\mathbf{H} - \mathbf{Y}\|_2 \le \lambda_k(\mathbf{H}) + \lambda_q(\mathbf{H}) +
\frac{q}{\ell - q - 1}\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_q\|_*\,,$$
eigenvalues indexed from $0$. At $q = k$ it is dominated by
`Matrix.PosSemidef.integral_specNorm_sub_le_of_isBestRankApprox_nystrom_of_hasLaw_gaussianMatrix`
(Martinsson and Tropp's Theorem 14.1); for $q > k$ the two are incomparable, this one better when
the spectrum decays past $k$.
Direct form at `truncatedSVD`:
`Matrix.PosSemidef.integral_specNorm_sub_truncatedSVD_nystrom_le_add_of_hasLaw_gaussianMatrix`.
[TroppYurtseverUdellCevher2017a, Theorem 4.2 (4.4)]; there
$2(1 + q/(\ell - q - 1))\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_q\|_*$ in place of the
last two terms and a minimum over $q$.
Result: randomized-nystrom-expected-error -/
theorem
_root_.Matrix.PosSemidef.integral_specNorm_sub_le_add_of_isBestRankApprox_nystrom_of_hasLaw_gaussianMatrix
    (hH : H.PosSemidef) (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ} {Y : Ω → Matrix n n ℝ}
    (hY : ∀ ω, IsBestRankApprox (nystrom H (X ω)) k (Y ω)) (hYm : AEStronglyMeasurable Y μ)
    {q : ℕ} (hq : q + 2 ≤ Fintype.card l) :
    ∫ ω, specNorm (H - Y ω) ∂μ ≤
      singularValues H k + singularValues H q +
        (q : ℝ) / ((Fintype.card l : ℝ) - q - 1) * nuclearNorm (H - truncatedSVD H q) := by
  have := hX.isProbabilityMeasure
  have hpt : ∀ ω, specNorm (H - Y ω) ≤ singularValues H k + specNorm (H - nystrom H (X ω)) :=
    fun ω => by
      simpa only [lpGauge_top_matrixNorm, specNorm_sub_truncatedSVD] using
        (hY ω).matrixNorm_sub_le_add_of_singularValues_le (hH.singularValues_nystrom_le (X ω))
          (lpGauge ⊤ le_top)
  have hS := hH.integrable_specNorm_sub_nystrom hX.aemeasurable
  have hI : Integrable (fun ω => singularValues H k + specNorm (H - nystrom H (X ω))) μ :=
    (integrable_const _).add hS
  refine (integral_mono (hH.integrable_specNorm_sub_of_isBestRankApprox_nystrom hY hYm) hI
    hpt).trans ?_
  rw [integral_add (integrable_const _) hS, integral_const, probReal_univ, one_smul, add_assoc]
  exact add_le_add le_rfl (hH.integral_specNorm_sub_nystrom_le_of_hasLaw_gaussianMatrix hX hq)

-- The declaration name alone, with its `_root_.Matrix.PosSemidef` prefix, exceeds 100 characters.
set_option linter.style.longLine false in
/-- **Truncated Nyström exploits spectral decay, spectral norm**: for positive semidefinite
$\mathbf{H}$, a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$, any target rank $k$
and any comparison rank $q$ with $q + 2 \le \ell$,
$$\mathbb{E}\|\mathbf{H} - \llbracket\mathsf{nystrom}(\mathbf{H}, \mathbf{X})\rrbracket_k\|_2 \le
\lambda_k(\mathbf{H}) + \lambda_q(\mathbf{H}) + \frac{q}{\ell - q - 1}
\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_q\|_*\,,$$
eigenvalues indexed from $0$. The direct form of
`Matrix.PosSemidef.integral_specNorm_sub_le_add_of_isBestRankApprox_nystrom_of_hasLaw_gaussianMatrix`;
at $q = k$ it is dominated by
`Matrix.PosSemidef.integral_specNorm_sub_truncatedSVD_nystrom_le_of_hasLaw_gaussianMatrix`, and for
$q > k$ the two are incomparable, this one better when the spectrum decays past $k$.
[TroppYurtseverUdellCevher2017a, Theorem 4.2 (4.4)]; there
$2(1 + q/(\ell - q - 1))\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_q\|_*$ in place of the
last two terms and a minimum over $q$.
Result: randomized-nystrom-expected-error -/
theorem
_root_.Matrix.PosSemidef.integral_specNorm_sub_truncatedSVD_nystrom_le_add_of_hasLaw_gaussianMatrix
    (hH : H.PosSemidef) (hX : HasLaw X (gaussianMatrix n l) μ) (k : ℕ) {q : ℕ}
    (hq : q + 2 ≤ Fintype.card l) :
    ∫ ω, specNorm (H - truncatedSVD (nystrom H (X ω)) k) ∂μ ≤
      singularValues H k + singularValues H q +
        (q : ℝ) / ((Fintype.card l : ℝ) - q - 1) * nuclearNorm (H - truncatedSVD H q) :=
  hH.integral_specNorm_sub_le_add_of_isBestRankApprox_nystrom_of_hasLaw_gaussianMatrix hX
    (fun _ => isBestRankApprox_truncatedSVD _ k)
    ((measurable_truncatedSVD k).comp_aemeasurable
      ((measurable_nystrom H).comp_aemeasurable hX.aemeasurable)).aestronglyMeasurable
    hq

end NLAlib
