/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
public import NLAlib.Matrix.Functions.OperatorMonotone
public import NLAlib.Matrix.Norms.SchattenPowers

/-!
# The matrix absolute value

The absolute value of a rectangular matrix $\mathbf{A}$ is
$\lvert \mathbf{A} \rvert = (\mathbf{A}^{\mathsf{H}}\mathbf{A})^{1/2}$, spelled `CFC.sqrt`
applied to $\mathbf{A}^{\mathsf{H}}\mathbf{A}$; for a square matrix this is Mathlib's `CFC.abs`
by definition. Its eigenvalues are the singular values of $\mathbf{A}$, so the nuclear norm is
$\operatorname{tr} \lvert \mathbf{A} \rvert$ and the Schatten norms are traces of powers of
$\mathbf{A}^{\mathsf{H}}\mathbf{A}$. For an even natural exponent the trace form, with natural
powers, is `NLAlib.schattenNorm_two_mul_natCast_pow`.

For a Hermitian matrix, $\lvert \mathbf{A} \rvert$ is the functional calculus of
$\lvert \cdot \rvert$ at $\mathbf{A}$ (Mathlib's `CFC.abs_eq_cfc_norm`), and the positive and
negative parts
$\mathbf{A}^{+}$, $\mathbf{A}^{-}$ are Mathlib's, with `CFC.le_posPart`,
`CFC.posPart_sub_negPart` and `CFC.abs_eq_posPart_add_negPart`.

## Main results

* `NLAlib.eigenvalue_sqrt_conjTranspose_mul_self`: the eigenvalues of $\lvert \mathbf{A} \rvert$.
* `NLAlib.nuclearNorm_eq_re_trace_sqrt`:
  $\|\mathbf{A}\|_* = \operatorname{tr} \lvert \mathbf{A} \rvert$.
* `NLAlib.schattenNorm_rpow_eq_re_trace_rpow`:
  $\|\mathbf{A}\|_{S_p}^p = \operatorname{tr} (\mathbf{A}^{\mathsf{H}}\mathbf{A})^{p/2}$.
* `Matrix.IsHermitian.le_abs`, `Matrix.IsHermitian.neg_abs_le`.
* in the `Matrix.PosSemidef` namespace, the square root as a factor:
  `sq_singularValues_sqrt`, `frobNorm_sqrt_sub_truncatedSVD_sq`,
  `singularGapRatio_le_two_mul_singularGapRatio_sqrt`.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder ENNReal

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

open scoped Classical in
/-- **The eigenvalues of the absolute value are the singular values**:
$\lambda_k((\mathbf{A}^{\mathsf{H}}\mathbf{A})^{1/2}) = \sigma_k(\mathbf{A})$ for
$k < \lvert n \rvert$, the number of columns, both indexed from $0$ and non-increasing. -/
theorem eigenvalue_sqrt_conjTranspose_mul_self (A : Matrix m n 𝕜) {k : ℕ}
    (hk : k < Fintype.card n) : eigenvalue (CFC.sqrt (Aᴴ * A)) k = singularValues A k := by
  have hG : (Aᴴ * A).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self A
  rw [CFC.sqrt_eq_real_sqrt (Aᴴ * A) hG.nonneg, cfcₙ_eq_cfc,
    hG.isHermitian.eigenvalue_cfc_of_monotoneOn (s := Set.univ)
      (fun x _ y _ h => Real.sqrt_le_sqrt h) (Set.subset_univ _) hk,
    ← sq_singularValues, Real.sqrt_sq (singularValues_nonneg A k)]

open scoped Classical in
/-- The absolute value has the same singular values as the matrix. -/
theorem singularValues_sqrt_conjTranspose_mul_self (A : Matrix m n 𝕜) (k : ℕ) :
    singularValues (CFC.sqrt (Aᴴ * A)) k = singularValues A k := by
  have hG : (Aᴴ * A).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self A
  have hH : (CFC.sqrt (Aᴴ * A)).IsHermitian := (CFC.sqrt_nonneg _).isSelfAdjoint
  refine congrFun (singularValues_eq_of_conjTranspose_mul_self_eq ?_) k
  rw [hH.eq, CFC.sqrt_mul_sqrt_self (Aᴴ * A) hG.nonneg]

open scoped Classical in
/-- **The nuclear norm is the trace of the absolute value**:
$\|\mathbf{A}\|_* = \operatorname{Re} \operatorname{tr} (\mathbf{A}^{\mathsf{H}}\mathbf{A})^{1/2}$
(the trace is real).
[HornJohnson2013, §7.4.1 context]. -/
theorem nuclearNorm_eq_re_trace_sqrt (A : Matrix m n 𝕜) :
    nuclearNorm A = RCLike.re (CFC.sqrt (Aᴴ * A)).trace := by
  have hS : (CFC.sqrt (Aᴴ * A)).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)
  rw [← hS.nuclearNorm_eq_re_trace, nuclearNorm_eq_sum_range A A.rank_le_card_width,
    nuclearNorm_eq_sum_range _ (Matrix.rank_le_card_width _)]
  exact Finset.sum_congr rfl fun i _ => (singularValues_sqrt_conjTranspose_mul_self A i).symm

/-! ### The square root of a positive semidefinite matrix

The square root $\mathbf{H}^{1/2}$ is a Hermitian factor of $\mathbf{H}$, so its singular values,
best errors and relative gaps are those of a factor; these are the bridges the Nyström bounds of
the Gram correspondence use. The `DecidableEq` instance enters `CFC.sqrt` only through a proof
argument, so these statements, under `Classical`, rewrite `CFC.sqrt H` for any instance. -/

open scoped Classical in
/-- The square root is a Hermitian factor: for positive semidefinite $\mathbf{H}$,
$(\mathbf{H}^{1/2})^{\mathsf{H}}\mathbf{H}^{1/2} = \mathbf{H}$. -/
theorem _root_.Matrix.PosSemidef.conjTranspose_sqrt_mul_sqrt {H : Matrix n n 𝕜}
    (hH : H.PosSemidef) : (CFC.sqrt H)ᴴ * CFC.sqrt H = H := by
  rw [(Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg H)).isHermitian.eq,
    CFC.sqrt_mul_sqrt_self H hH.nonneg]

open scoped Classical in
/-- **The singular values of the square root**: for positive semidefinite $\mathbf{H}$,
$\sigma_k(\mathbf{H}^{1/2})^2 = \sigma_k(\mathbf{H})$ at every index, the zero padding
included. -/
theorem _root_.Matrix.PosSemidef.sq_singularValues_sqrt {H : Matrix n n 𝕜}
    (hH : H.PosSemidef) (k : ℕ) : singularValues (CFC.sqrt H) k ^ 2 = singularValues H k := by
  rw [← singularValues_conjTranspose_mul_self, hH.conjTranspose_sqrt_mul_sqrt]

open scoped Classical in
/-- **The best Frobenius error of the square root**: for positive semidefinite $\mathbf{H}$,
$$\|\mathbf{H}^{1/2} - \llbracket\mathbf{H}^{1/2}\rrbracket_k\|_{\mathsf{F}}^2 =
\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_*\,,$$
both sides being $\sum_{i \ge k}\sigma_i(\mathbf{H})$. -/
theorem _root_.Matrix.PosSemidef.frobNorm_sqrt_sub_truncatedSVD_sq {H : Matrix n n 𝕜}
    (hH : H.PosSemidef) (k : ℕ) :
    frobNorm (CFC.sqrt H - truncatedSVD (CFC.sqrt H) k) ^ 2 =
      nuclearNorm (H - truncatedSVD H k) := by
  rw [nuclearNorm_eq_sum_range _ (Matrix.rank_le_card_width (H - truncatedSVD H k)),
    frobNorm_sq_eq_sum_range_singularValues_sq _ (Matrix.rank_le_card_width _)]
  exact Finset.sum_congr rfl fun i _ => by
    rw [singularValues_sub_truncatedSVD, singularValues_sub_truncatedSVD,
      hH.sq_singularValues_sqrt]

open scoped Classical in
/-- **The relative gap of the square root is at least half that of the matrix**: for positive
semidefinite $\mathbf{H}$ and $i \le j$,
$$\frac{\sigma_i(\mathbf{H}) - \sigma_j(\mathbf{H})}{\sigma_i(\mathbf{H}) + \sigma_j(\mathbf{H})}
\le 2\,\frac{\sigma_i(\mathbf{H}^{1/2}) - \sigma_j(\mathbf{H}^{1/2})}
{\sigma_i(\mathbf{H}^{1/2}) + \sigma_j(\mathbf{H}^{1/2})}\,,$$
from $(a + b)^2 \le 2(a^2 + b^2)$.
[TroppWebber2023, proof of Theorem 9.2 (NysBKI)]; there as
$\sqrt{(1 + \gamma)/(1 - \gamma)} \ge (1 + \gamma/2)/(1 - \gamma/2)$. -/
theorem _root_.Matrix.PosSemidef.singularGapRatio_le_two_mul_singularGapRatio_sqrt
    {H : Matrix n n 𝕜} (hH : H.PosSemidef) {i j : ℕ} (hij : i ≤ j) :
    singularGapRatio H i j ≤ 2 * singularGapRatio (CFC.sqrt H) i j := by
  rw [singularGapRatio, singularGapRatio, ← hH.sq_singularValues_sqrt i,
    ← hH.sq_singularValues_sqrt j]
  set a := singularValues (CFC.sqrt H) i
  set b := singularValues (CFC.sqrt H) j
  have hb : 0 ≤ b := singularValues_nonneg _ j
  have hba : b ≤ a := singularValues_antitone _ hij
  rcases (add_nonneg (hb.trans hba) hb).eq_or_lt with h0 | h0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [ha0, hb0]
  · have h2 : 0 < a ^ 2 + b ^ 2 := by nlinarith
    rw [mul_div_assoc', div_le_div_iff₀ h2 h0]
    nlinarith [mul_nonneg (sub_nonneg.mpr hba) (sq_nonneg (a - b))]

/-- **Schatten norms as traces**: for real $p > 0$,
$$\|\mathbf{A}\|_{S_p}^p
  = \operatorname{Re} \operatorname{tr} (\mathbf{A}^{\mathsf{H}}\mathbf{A})^{p/2},$$
the power taken in the continuous functional calculus (the trace is real). -/
theorem schattenNorm_rpow_eq_re_trace_rpow [DecidableEq n] (A : Matrix m n 𝕜) {p : ℝ}
    (hp : 0 < p) :
    schattenNorm (ENNReal.ofReal p) A ^ p = RCLike.re ((Aᴴ * A) ^ (p / 2)).trace := by
  have hG : (Aᴴ * A).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self A
  have h := schattenNorm_rpow (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top A
    A.rank_le_card_width
  rw [ENNReal.toReal_ofReal hp.le] at h
  rw [h, CFC.rpow_eq_cfc_real hG.nonneg, hG.isHermitian.re_trace_cfc]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← sq_singularValues, ← Real.rpow_natCast, ← Real.rpow_mul (singularValues_nonneg A i)]
  congr 1
  push_cast
  ring

open scoped Classical in
/-- A Hermitian matrix is at most its absolute value:
$\mathbf{A} \preceq \lvert \mathbf{A} \rvert$. -/
theorem _root_.Matrix.IsHermitian.le_abs {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    A ≤ CFC.abs A := by
  have hsa : IsSelfAdjoint A := hA
  rw [← sub_nonneg, CFC.abs_sub_self A hsa]
  exact nsmul_nonneg (CFC.negPart_nonneg A) 2

open scoped Classical in
/-- A Hermitian matrix is at least minus its absolute value:
$-\lvert \mathbf{A} \rvert \preceq \mathbf{A}$. -/
theorem _root_.Matrix.IsHermitian.neg_abs_le {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    -CFC.abs A ≤ A := by
  have hsa : IsSelfAdjoint A := hA
  rw [neg_le_iff_add_nonneg', CFC.abs_add_self A hsa]
  exact nsmul_nonneg (CFC.posPart_nonneg A) 2

/-- The spectral norm bounds the absolute value in the Loewner order:
$\lvert \mathbf{A} \rvert \preceq \|\mathbf{A}\|_2 \mathbf{I}$ for every square matrix
$\mathbf{A}$. -/
theorem abs_le_specNorm_smul_one [DecidableEq n] (A : Matrix n n 𝕜) :
    CFC.abs A ≤ specNorm A • (1 : Matrix n n 𝕜) := by
  rcases isEmpty_or_nonempty n with h | h
  · exact le_of_eq (Subsingleton.elim _ _)
  · have hH : (CFC.sqrt (Aᴴ * A)).IsHermitian := (CFC.sqrt_nonneg _).isSelfAdjoint
    have h1 := hH.le_eigenvalue_zero_smul_one
    rwa [eigenvalue_sqrt_conjTranspose_mul_self A Fintype.card_pos,
      singularValues_zero_eq_specNorm] at h1

end NLAlib
