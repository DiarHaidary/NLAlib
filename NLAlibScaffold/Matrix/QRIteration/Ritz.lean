/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.QRIteration.Ritz
public import NLAlibScaffold.ForMathlib.Analysis.MeanInequalities
public import NLAlibScaffold.Matrix.QRIteration.EigenvectorWeights
public import NLAlibScaffold.Matrix.QRIteration.ShiftedQR
public import NLAlibScaffold.Matrix.Spectral.Diagonalizable

/-!
# Optimal and promising Ritz values (scaffold)

Statements for `NLAlib/Matrix/QRIteration/Ritz.lean` (stage SHIFTED-QR, waves W1–W2, design note
`docs/design/Eigensolvers-ShiftedQR.md` §3.4): exact Ritz values are $1$-optimal; the moment
comparison and almost-monotonicity for a promising Ritz value
([BanksGarzaVargasSrivastava2021, Lemma 4.4]); the binary search `NLAlib.findRitz` returns a
$\kappa_V^{4\log_2 k/k}$-promising Ritz value ([BanksGarzaVargasSrivastava2021, Lemma 4.5]).

## Main results

* `NLAlib.length_ritzValues`, `NLAlib.IsUpperHessenberg.isOptimalRitzValues_one_ritzValues`,
  `NLAlib.norm_le_specNorm_of_mem_ritzValues`.
* `NLAlib.IsOptimalRitzValues.one_le_mul_sum_lastRowWeights_div`: the moment comparison.
* `NLAlib.IsUpperHessenberg.hessenbergPotential_multiShiftedQRStep_replicate_le`:
  almost-monotonicity.
* `NLAlib.sum_lastRowWeights_div_norm_eval_shiftPoly_le`, `NLAlib.findRitz_mem`,
  `NLAlib.isPromisingRitzValue_findRitz`: the binary search.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {n : ℕ}

/-! ### Exact Ritz values -/

/-- **There are $k$ Ritz values**: the trailing block is $k \times k$ and its characteristic
polynomial splits over $\mathbb{C}$, so `NLAlib.ritzValues` $k$ $\mathbf{H}$ has length $k$.
Proof: `Multiset.length_toList`, `Polynomial.splits_iff_card_roots` with
`IsAlgClosed.splits`, `Matrix.charpoly_natDegree_eq_dim`. S, about 8 lines. -/
theorem length_ritzValues (k : ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    (ritzValues k H).length = k := by
  unfold ritzValues
  rw [Multiset.length_toList, Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _),
    Matrix.charpoly_natDegree_eq_dim]
  simp

/-- **Exact Ritz values are $1$-optimal**: for upper Hessenberg $\mathbf{H}$ and $1 \le k \le n$,
the eigenvalues of the trailing block $\mathbf{H}_{(k)}$ satisfy
$\|\mathbf{e}_n^{\mathsf{H}}\chi_k(\mathbf{H})\| \le \psi_k(\mathbf{H})^k$.
[BanksGarzaVargasSrivastava2021, §1.1]: the true Ritz values are $1$-optimal.
Proof: `NLAlib.shiftPoly` of the roots is the characteristic polynomial
(`Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq`, `Multiset.prod_toList`,
`Multiset.map_coe`), then `NLAlib.IsUpperHessenberg.norm_aeval_charpoly_trailingBlock_eq` and
`NLAlib.length_ritzValues`. S, about 15 lines. -/
theorem IsUpperHessenberg.isOptimalRitzValues_one_ritzValues
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H) {k : ℕ} (hk : 0 < k)
    (hkn : k ≤ n) : IsOptimalRitzValues 1 H (ritzValues k H) := by
  have hcard : (trailingBlock k H).charpoly.roots.card =
      (trailingBlock k H).charpoly.natDegree := by
    simpa using IsAlgClosed.card_roots_map_eq_natDegree_of_injective
      (f := RingHom.id ℂ) (trailingBlock k H).charpoly Function.injective_id
  have hL : shiftPoly (ritzValues k H) = (trailingBlock k H).charpoly := by
    unfold ritzValues shiftPoly
    rw [← Multiset.prod_coe, ← Multiset.map_coe, Multiset.coe_toList]
    exact Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq
      (Matrix.charpoly_monic _) hcard
  unfold IsOptimalRitzValues
  rw [hL, length_ritzValues,
    NLAlib.IsUpperHessenberg.norm_aeval_charpoly_trailingBlock_eq hH hk hkn, one_mul]

/-- **Ritz values are bounded by the norm**: every Ritz value $s$ of order $k \le n + 1$ has
$\lvert s\rvert \le \|\mathbf{H}\|_2$.
Proof: $s$ is an eigenvalue of the principal submatrix $\mathbf{H}_{(k)}$
(`Polynomial.mem_roots`, `Matrix.mem_spectrum_iff_isRoot_charpoly`), so
$\lvert s\rvert \le \|\mathbf{H}_{(k)}\|_2 \le \|\mathbf{H}\|_2$ (`spectrum.norm_le_norm_of_mem`,
`NLAlib.specNorm_submatrix_le` or the compression bound). S, about 15 lines. -/
theorem norm_le_specNorm_of_mem_ritzValues {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {k : ℕ}
    (hkn : k ≤ n + 1) {s : ℂ} (hs : s ∈ ritzValues k H) : ‖s‖ ≤ specNorm H := by
  have hroot : (trailingBlock k H).charpoly.IsRoot s := by
    unfold ritzValues at hs
    exact (Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero).mp (Multiset.mem_toList.mp hs)
  have hspec : s ∈ spectrum ℂ (trailingBlock k H) := Matrix.mem_spectrum_of_isRoot_charpoly hroot
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at hspec
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hspec
  have hBv : trailingBlock k H *ᵥ v = s • v := by
    rw [Algebra.algebraMap_eq_smul_one, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec] at hv
    exact (sub_eq_zero.mp hv).symm
  have hN : 0 < ‖WithLp.toLp 2 v‖ := by
    refine norm_pos_iff.mpr fun h => hv0 ?_
    simpa using h
  have hle : ‖s‖ * ‖WithLp.toLp 2 v‖ ≤ specNorm (trailingBlock k H) * ‖WithLp.toLp 2 v‖ := by
    have h1 := norm_toLp_mulVec_le (trailingBlock k H) v
    rw [hBv] at h1
    simpa [norm_smul] using h1
  have hsub : specNorm (trailingBlock k H) ≤ specNorm H := by
    unfold trailingBlock
    refine specNorm_submatrix_le H (fun a b hab => ?_) (fun a b hab => ?_)
    · simp only [Fin.mk.injEq] at hab
      have ha := a.isLt
      have hb := b.isLt
      exact Fin.ext (by omega)
    · simp only [Fin.mk.injEq] at hab
      have ha := a.isLt
      have hb := b.isLt
      exact Fin.ext (by omega)
  exact (le_of_mul_le_mul_right hle hN).trans hsub

/-! ### Promising Ritz values -/

/-- **Moment comparison for a promising Ritz value**: let $\mathbf{H}\mathbf{V} =
\mathbf{V}\operatorname{diag}(\mathbf{d})$, $\mathbf{V}$ invertible with
$\kappa = \|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2$ and last-row weights $w$, let the $k$ shifts
`ss` be $\theta$-optimal Ritz values of $\mathbf{H}$, none an eigenvalue, and $r$ an
$\alpha$-promising one, $\alpha, \theta \ge 0$. Then
$$1 \le \kappa\,(\alpha\theta\psi_k(\mathbf{H}))^k\sum_i\frac{w_i}{\lvert\mathbf{d}_i -
r\rvert^k}\,,$$
i.e. $\mathbb{E}\lvert Z_{\mathbf{H}} - r\rvert^{-k} \ge
\kappa^{-1}(\alpha\theta\psi_k(\mathbf{H}))^{-k}$. [BanksGarzaVargasSrivastava2021, Lemma 4.4],
(4.2) there.
Proof: the chain of the paper: promising, then Jensen for $1/x$ (`ConvexOn.map_sum_le` with
`convexOn_zpow` at $-1$) and for $x^2$ (`Finset.sum_mul_sq_le_sq_mul_sq`), then
`NLAlib.sum_lastRowWeights_mul_sq_le` with $\mathbf{g} = p(\mathbf{d})$ and
`NLAlib.aeval_eq_mul_diagonal_mul_inv`, then optimality. M, about 50 lines. -/
theorem IsOptimalRitzValues.one_le_mul_sum_lastRowWeights_div {θ α : ℝ}
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} {ss : List ℂ} {r : ℂ}
    (hss : IsOptimalRitzValues θ H ss) (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d)
    (hd : ∀ i, ∀ s ∈ ss, d i ≠ s) (hr : IsPromisingRitzValue α V d ss r) (hα : 0 ≤ α)
    (hθ : 0 ≤ θ) :
    1 ≤ pseudoConditionNumber V * (α * θ * hessenbergPotential ss.length H) ^ ss.length *
      ∑ i, lastRowWeights V i / ‖d i - r‖ ^ ss.length := by
  obtain ⟨-, hr2⟩ := hr
  have hW : ∑ i, lastRowWeights V i = 1 := sum_lastRowWeights hV
  have hκ0 : 0 ≤ pseudoConditionNumber V := by unfold pseudoConditionNumber; positivity
  have hψ0 : 0 ≤ hessenbergPotential ss.length H := by unfold hessenbergPotential; positivity
  have hne : ∀ i, (shiftPoly ss).eval (d i) ≠ 0 := by
    intro i
    unfold shiftPoly
    rw [Polynomial.eval_list_prod, List.map_map]
    apply List.prod_ne_zero
    simp only [List.mem_map, Function.comp_apply, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, not_exists, not_and]
    intro s hs
    exact sub_ne_zero.mpr (hd i s hs)
  -- the second moment of `p(d)` is at most `(κ (θ ψ)^k)^2`
  have hA := hss
  unfold IsOptimalRitzValues at hA
  rw [aeval_eq_mul_diagonal_mul_inv hV hHV] at hA
  have hm2 : ∑ i, lastRowWeights V i * ‖(shiftPoly ss).eval (d i)‖ ^ 2 ≤
      (pseudoConditionNumber V * (θ * hessenbergPotential ss.length H) ^ ss.length) ^ 2 := by
    have h1 := sum_lastRowWeights_mul_sq_le hV (fun i => (shiftPoly ss).eval (d i))
    calc ∑ i, lastRowWeights V i * ‖(shiftPoly ss).eval (d i)‖ ^ 2
        ≤ _ := h1
      _ ≤ pseudoConditionNumber V ^ 2 *
          ((θ * hessenbergPotential ss.length H) ^ ss.length) ^ 2 := by
        gcongr
      _ = _ := by ring
  -- first moment, by Cauchy–Schwarz
  have hm1 : ∑ i, lastRowWeights V i * ‖(shiftPoly ss).eval (d i)‖ ≤
      pseudoConditionNumber V * (θ * hessenbergPotential ss.length H) ^ ss.length := by
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (r := fun i => lastRowWeights V i * ‖(shiftPoly ss).eval (d i)‖)
      (f := fun i => lastRowWeights V i)
      (g := fun i => lastRowWeights V i * ‖(shiftPoly ss).eval (d i)‖ ^ 2)
      (fun i _ => lastRowWeights_nonneg V i)
      (fun i _ => mul_nonneg (lastRowWeights_nonneg V i) (sq_nonneg _))
      (fun i _ => le_of_eq (by ring))
    rw [hW, one_mul] at hcs
    have hnn : 0 ≤ pseudoConditionNumber V * (θ * hessenbergPotential ss.length H) ^ ss.length :=
      mul_nonneg hκ0 (pow_nonneg (mul_nonneg hθ hψ0) _)
    exact le_of_pow_le_pow_left₀ two_ne_zero hnn (hcs.trans hm2)
  -- reciprocal moment, by Cauchy–Schwarz again
  have hrec : 1 ≤ (∑ i, lastRowWeights V i / ‖(shiftPoly ss).eval (d i)‖) *
      ∑ i, lastRowWeights V i * ‖(shiftPoly ss).eval (d i)‖ := by
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (r := fun i => lastRowWeights V i)
      (f := fun i => lastRowWeights V i / ‖(shiftPoly ss).eval (d i)‖)
      (g := fun i => lastRowWeights V i * ‖(shiftPoly ss).eval (d i)‖)
      (fun i _ => div_nonneg (lastRowWeights_nonneg V i) (norm_nonneg _))
      (fun i _ => mul_nonneg (lastRowWeights_nonneg V i) (norm_nonneg _))
      (fun i _ => le_of_eq (by
        have : ‖(shiftPoly ss).eval (d i)‖ ≠ 0 := norm_ne_zero_iff.mpr (hne i)
        field_simp))
    rw [hW, one_pow] at hcs
    exact hcs
  have hS0 : 0 ≤ ∑ i, lastRowWeights V i / ‖(shiftPoly ss).eval (d i)‖ :=
    Finset.sum_nonneg fun i _ => div_nonneg (lastRowWeights_nonneg V i) (norm_nonneg _)
  have hK0 : 0 ≤ pseudoConditionNumber V * (θ * hessenbergPotential ss.length H) ^ ss.length :=
    mul_nonneg hκ0 (pow_nonneg (mul_nonneg hθ hψ0) _)
  calc (1 : ℝ)
      ≤ (∑ i, lastRowWeights V i / ‖(shiftPoly ss).eval (d i)‖) *
          ∑ i, lastRowWeights V i * ‖(shiftPoly ss).eval (d i)‖ := hrec
    _ ≤ (∑ i, lastRowWeights V i / ‖(shiftPoly ss).eval (d i)‖) *
          (pseudoConditionNumber V * (θ * hessenbergPotential ss.length H) ^ ss.length) :=
        mul_le_mul_of_nonneg_left hm1 hS0
    _ ≤ (α ^ ss.length * ∑ i, lastRowWeights V i / ‖d i - r‖ ^ ss.length) *
          (pseudoConditionNumber V * (θ * hessenbergPotential ss.length H) ^ ss.length) :=
        mul_le_mul_of_nonneg_right hr2 hK0
    _ = _ := by simp only [mul_pow]; ring

/-- **Almost-monotonicity of the potential**: in the setting of the moment comparison
(upper Hessenberg $\mathbf{H}$, $\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$
with $\mathbf{V}$ invertible and $\kappa = \|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2$; $k$ shifts `ss`,
$1 \le k \le n$, $\theta$-optimal, none an eigenvalue; $r$ an $\alpha$-promising member;
$\alpha, \theta \ge 0$), the degree $k$ step with shift polynomial $(z - r)^k$ satisfies
$$\psi_k(\widehat{\mathbf{H}}) \le \kappa^{2/k}\alpha\theta\,\psi_k(\mathbf{H})\,.$$
[BanksGarzaVargasSrivastava2021, Lemma 4.4]. Not used by the convergence theorem.
Proof: `NLAlib.IsOptimalRitzValues.one_le_mul_sum_lastRowWeights_div` and Jensen for $x^2$ give
$\mathbb{E}\lvert Z - r\rvert^{-2k} \ge \kappa^{-2}(\alpha\theta\psi)^{-2k}$; then
`NLAlib.sum_lastRowWeights_mul_sq_le` with $\mathbf{g} = (\mathbf{d} - r)^{-k}$
(`NLAlib.inv_aeval_eq_mul_diagonal_mul_inv`, `NLAlib.mul_diagonal_mul_inv_pow`) and
`NLAlib.IsUpperHessenberg.hessenbergPotential_multiShiftedQRStep_pow_mul_le`; take $k$-th roots.
M, about 45 lines. -/
theorem IsUpperHessenberg.hessenbergPotential_multiShiftedQRStep_replicate_le {θ α : ℝ}
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H) {d : Fin (n + 1) → ℂ}
    {ss : List ℂ} {r : ℂ} (hss : IsOptimalRitzValues θ H ss) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal d) (hd : ∀ i, ∀ s ∈ ss, d i ≠ s)
    (hr : IsPromisingRitzValue α V d ss r) (hk : 0 < ss.length) (hkn : ss.length ≤ n)
    (hα : 0 ≤ α) (hθ : 0 ≤ θ) :
    hessenbergPotential ss.length (multiShiftedQRStep H (List.replicate ss.length r)) ≤
      pseudoConditionNumber V ^ ((2 : ℝ) / ss.length) * α * θ *
        hessenbergPotential ss.length H := by
  sorry

/-! ### The binary search -/

/-- The two-sided moment bound for the inverse power `(p(H))⁻¹ ^ q` of a shift polynomial, from
`NLAlib.norm_mul_diagonal_mul_inv_last_sq_le` and `NLAlib.sum_lastRowWeights_mul_sq_le`. -/
private theorem moment_sandwich_shiftPoly {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {d : Fin (n + 1) → ℂ} (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d) (q : ℕ)
    {l : List ℂ} (hl : ∀ i, (shiftPoly l).eval (d i) ≠ 0) :
    ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly l))⁻¹ ^ q) (Fin.last n))‖ ^ 2 ≤
        pseudoConditionNumber V ^ 2 *
          ∑ i, lastRowWeights V i * ‖((shiftPoly l).eval (d i))⁻¹ ^ q‖ ^ 2 ∧
      ∑ i, lastRowWeights V i * ‖((shiftPoly l).eval (d i))⁻¹ ^ q‖ ^ 2 ≤
        pseudoConditionNumber V ^ 2 *
          ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly l))⁻¹ ^ q) (Fin.last n))‖ ^ 2 := by
  have hA : (Polynomial.aeval H (shiftPoly l))⁻¹ ^ q =
      V * Matrix.diagonal (fun i => ((shiftPoly l).eval (d i))⁻¹ ^ q) * V⁻¹ := by
    rw [inv_aeval_eq_mul_diagonal_mul_inv hV hHV hl, mul_diagonal_mul_inv_pow hV]
    rfl
  rw [hA]
  exact ⟨norm_mul_diagonal_mul_inv_last_sq_le hV _, sum_lastRowWeights_mul_sq_le hV _⟩

/-- Reciprocals of a product of powers: `1 / (x y)^q` is at most the mean of the squared inverse
powers `(x⁻¹)^q` and `(y⁻¹)^q`, weighted by `w ≥ 0`. -/
private theorem inv_pow_mul_le (x y w : ℝ) (q : ℕ) (hw : 0 ≤ w) :
    w / (x * y) ^ q ≤ w * (((x⁻¹) ^ q) ^ 2 + ((y⁻¹) ^ q) ^ 2) / 2 := by
  have huv : ((x * y) ^ q)⁻¹ = (x⁻¹) ^ q * (y⁻¹) ^ q := by
    rw [mul_pow, mul_inv, inv_pow, inv_pow]
  have ham : (x⁻¹) ^ q * (y⁻¹) ^ q ≤ (((x⁻¹) ^ q) ^ 2 + ((y⁻¹) ^ q) ^ 2) / 2 := by
    nlinarith [sq_nonneg ((x⁻¹) ^ q - (y⁻¹) ^ q)]
  rw [div_eq_mul_inv, huv]
  nlinarith [mul_le_mul_of_nonneg_left ham hw]

/-- A two-sided moment bound transfers along a maximum: `Xg ≤ κ² Kg²`, `Kg ≤ Kh` and
`Kh² ≤ κ² Xh` give `Xg ≤ κ⁴ Xh`. -/
private theorem moment_le_of_sandwich {κ Kg Kh Xg Xh : ℝ} (hKg0 : 0 ≤ Kg) (hKg : Kg ≤ Kh)
    (hg : Xg ≤ κ ^ 2 * Kg ^ 2) (hh : Kh ^ 2 ≤ κ ^ 2 * Xh) : Xg ≤ κ ^ 4 * Xh :=
  calc Xg ≤ κ ^ 2 * Kg ^ 2 := hg
    _ ≤ κ ^ 2 * Kh ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hKg0 hKg 2) (sq_nonneg _)
    _ ≤ κ ^ 2 * (κ ^ 2 * Xh) := mul_le_mul_of_nonneg_left hh (sq_nonneg _)
    _ = κ ^ 4 * Xh := by ring

/-- **One halving step of the binary search loses at most $\kappa^4$**: let $\mathbf{H}\mathbf{V}
= \mathbf{V}\operatorname{diag}(\mathbf{d})$, $\mathbf{V}$ invertible with
$\kappa = \|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2$ and last-row weights $w$; let $a$, $b$ be lists of
shifts, none an eigenvalue, $h \in \{a, b\}$ the one with the larger
$\|\mathbf{e}_n^{\mathsf{H}}p_h(\mathbf{H})^{-q}\|$, and $p_c = p_ap_b$ for $c = a \mathbin{+\!+}
b$. Then
$$\sum_i\frac{w_i}{\lvert p_c(\mathbf{d}_i)\rvert^q} \le \kappa^4\sum_i\frac{w_i}{\lvert
p_h(\mathbf{d}_i)\rvert^{2q}}\,.$$
[BanksGarzaVargasSrivastava2021, proof of Lemma 4.5], one step of the induction (with the squares
the printed chain omits; gap G5 of the design note).
Proof: $\mathbb{E}\lvert p_h\rvert^{-2q} \ge \kappa^{-2}\|\mathbf{e}_n^{\mathsf{H}}
p_h(\mathbf{H})^{-q}\|^2$ (`NLAlib.norm_mul_diagonal_mul_inv_last_sq_le`), which is the maximum
over $\{a, b\}$, at least the average, and each term is $\ge \kappa^{-2}\mathbb{E}\lvert
p_g\rvert^{-2q}$ (`NLAlib.sum_lastRowWeights_mul_sq_le`); AM–GM
$\tfrac12(x^2 + y^2) \ge xy$ and $p_c = p_ap_b$ (`List.map_append`, `List.prod_append`,
`Polynomial.eval_mul`). M, about 50 lines. -/
theorem sum_lastRowWeights_div_norm_eval_shiftPoly_le
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal d) {a b h : List ℂ} (hd : ∀ i, ∀ s ∈ a ++ b, d i ≠ s)
    (hh : h = a ∨ h = b) (q : ℕ)
    (hmax : ∀ g ∈ [a, b],
      ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly g))⁻¹ ^ q) (Fin.last n))‖ ≤
        ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly h))⁻¹ ^ q) (Fin.last n))‖) :
    ∑ i, lastRowWeights V i / ‖(shiftPoly (a ++ b)).eval (d i)‖ ^ q ≤
      pseudoConditionNumber V ^ 4 *
        ∑ i, lastRowWeights V i / ‖(shiftPoly h).eval (d i)‖ ^ (2 * q) := by
  have hne : ∀ l : List ℂ, (∀ i, ∀ s ∈ l, d i ≠ s) → ∀ i, (shiftPoly l).eval (d i) ≠ 0 := by
    intro l hl i
    unfold shiftPoly
    rw [Polynomial.eval_list_prod, List.map_map]
    apply List.prod_ne_zero
    simp only [List.mem_map, Function.comp_apply, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, not_exists, not_and]
    intro s hs
    exact sub_ne_zero.mpr (hl i s hs)
  have hna : ∀ i, (shiftPoly a).eval (d i) ≠ 0 :=
    hne a fun i s hs => hd i s (List.mem_append_left _ hs)
  have hnb : ∀ i, (shiftPoly b).eval (d i) ≠ 0 :=
    hne b fun i s hs => hd i s (List.mem_append_right _ hs)
  have hnh : ∀ i, (shiftPoly h).eval (d i) ≠ 0 := by
    rcases hh with rfl | rfl
    · exact hna
    · exact hnb
  have hpc : shiftPoly (a ++ b) = shiftPoly a * shiftPoly b := by
    simp [shiftPoly, List.map_append, List.prod_append]
  have hsa := moment_sandwich_shiftPoly hV hHV q hna
  have hsb := moment_sandwich_shiftPoly hV hHV q hnb
  have hsh := moment_sandwich_shiftPoly hV hHV q hnh
  -- pointwise: the reciprocal of `|p_a p_b|^q` is at most the mean of the squared inverse powers
  have hpt : ∀ i, lastRowWeights V i / ‖(shiftPoly (a ++ b)).eval (d i)‖ ^ q ≤
      lastRowWeights V i * (‖((shiftPoly a).eval (d i))⁻¹ ^ q‖ ^ 2 +
        ‖((shiftPoly b).eval (d i))⁻¹ ^ q‖ ^ 2) / 2 := by
    intro i
    rw [hpc, Polynomial.eval_mul, norm_mul]
    simp only [norm_pow, norm_inv]
    exact inv_pow_mul_le _ _ _ _ (lastRowWeights_nonneg V i)
  have hsumh : ∑ i, lastRowWeights V i / ‖(shiftPoly h).eval (d i)‖ ^ (2 * q) =
      ∑ i, lastRowWeights V i * ‖((shiftPoly h).eval (d i))⁻¹ ^ q‖ ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_pow, norm_inv, ← pow_mul, inv_pow, div_eq_mul_inv, mul_comm 2 q]
  rw [hsumh]
  obtain ⟨hKa, hXa⟩ := hsa
  obtain ⟨hKb, hXb⟩ := hsb
  obtain ⟨hKh, hXh⟩ := hsh
  have hmaxa : ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly a))⁻¹ ^ q) (Fin.last n))‖ ≤
      ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly h))⁻¹ ^ q) (Fin.last n))‖ :=
    hmax a (by simp)
  have hmaxb : ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly b))⁻¹ ^ q) (Fin.last n))‖ ≤
      ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly h))⁻¹ ^ q) (Fin.last n))‖ :=
    hmax b (by simp)
  -- the moment of `a` and `b` is at most `κ⁴` times the moment of `h`
  have hXa' := moment_le_of_sandwich (norm_nonneg _) hmaxa hXa hKh
  have hXb' := moment_le_of_sandwich (norm_nonneg _) hmaxb hXb hKh
  calc ∑ i, lastRowWeights V i / ‖(shiftPoly (a ++ b)).eval (d i)‖ ^ q
      ≤ ∑ i, lastRowWeights V i * (‖((shiftPoly a).eval (d i))⁻¹ ^ q‖ ^ 2 +
          ‖((shiftPoly b).eval (d i))⁻¹ ^ q‖ ^ 2) / 2 := Finset.sum_le_sum fun i _ => hpt i
    _ = (∑ i, lastRowWeights V i * ‖((shiftPoly a).eval (d i))⁻¹ ^ q‖ ^ 2 +
          ∑ i, lastRowWeights V i * ‖((shiftPoly b).eval (d i))⁻¹ ^ q‖ ^ 2) / 2 := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ pseudoConditionNumber V ^ 4 *
          ∑ i, lastRowWeights V i * ‖((shiftPoly h).eval (d i))⁻¹ ^ q‖ ^ 2 := by
        linarith

/-- **The binary search returns a member**: for a list of length $2^m$,
`NLAlib.findRitz` $\mathbf{H}$ $m$ $e$ `ss` is in `ss`.
Proof: induction on $m$, generalising $e$ and `ss`; the halves have length $2^{m}$
(`List.length_take`, `List.length_drop`) and are sublists (`List.mem_of_mem_take`,
`List.mem_of_mem_drop`); for $m = 0$, `List.headD` of a singleton. S, about 15 lines. -/
theorem findRitz_mem (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) {m e : ℕ} {ss : List ℂ}
    (hss : ss.length = 2 ^ m) : findRitz H m e ss ∈ ss := by
  induction m generalizing e ss with
  | zero =>
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp (by simpa using hss)
    simp [findRitz]
  | succ m ih =>
    have hlen : ss.length / 2 = 2 ^ m := by rw [hss, pow_succ]; omega
    rw [findRitz]
    split_ifs
    · exact List.mem_of_mem_take (ih (by rw [List.length_take, hlen, hss, pow_succ]; omega))
    · exact List.mem_of_mem_drop (ih (by rw [List.length_drop, hss, pow_succ]; omega))

/-- The binary search keeps the moment bound: for a list of length $2^m$ and exponent $e$, the
weighted sum of $\lvert p_{\mathrm{ss}}(\mathbf{d}_i)\rvert^{-e}$ is at most $\kappa^{4m}$ times
the one at the Ritz value `findRitz H m e ss`, with exponent $e2^m$. -/
private theorem sum_lastRowWeights_div_le_findRitz {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {d : Fin (n + 1) → ℂ} (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d) (m : ℕ) :
    ∀ (e : ℕ) (ss : List ℂ), ss.length = 2 ^ m → (∀ i, ∀ s ∈ ss, d i ≠ s) →
      ∑ i, lastRowWeights V i / ‖(shiftPoly ss).eval (d i)‖ ^ e ≤
        pseudoConditionNumber V ^ (4 * m) *
          ∑ i, lastRowWeights V i / ‖d i - findRitz H m e ss‖ ^ (e * 2 ^ m) := by
  induction m with
  | zero =>
    intro e ss hlen hd
    obtain ⟨s, rfl⟩ := List.length_eq_one_iff.mp (by simpa using hlen)
    simp [shiftPoly, findRitz]
  | succ j ih =>
    intro e ss hlen hd
    have hhalf : ss.length / 2 = 2 ^ j := by
      rw [hlen, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
    have hta : (ss.take (ss.length / 2)).length = 2 ^ j := by
      rw [List.length_take, hhalf, hlen]
      exact Nat.min_eq_left (Nat.pow_le_pow_right (by norm_num) (by omega))
    have htd : (ss.drop (ss.length / 2)).length = 2 ^ j := by
      rw [List.length_drop, hhalf, hlen, pow_succ]
      omega
    have hdis : ∀ i, ∀ s ∈ ss.take (ss.length / 2) ++ ss.drop (ss.length / 2), d i ≠ s := by
      simpa only [List.take_append_drop] using hd
    have hdis_a : ∀ i, ∀ s ∈ ss.take (ss.length / 2), d i ≠ s :=
      fun i s hs => hd i s (List.mem_of_mem_take hs)
    have hdis_b : ∀ i, ∀ s ∈ ss.drop (ss.length / 2), d i ≠ s :=
      fun i s hs => hd i s (List.mem_of_mem_drop hs)
    have hpow : e * 2 ^ (j + 1) = 2 * e * 2 ^ j := by ring
    have hsplit : ∑ i, lastRowWeights V i / ‖(shiftPoly ss).eval (d i)‖ ^ e =
        ∑ i, lastRowWeights V i /
          ‖(shiftPoly (ss.take (ss.length / 2) ++ ss.drop (ss.length / 2))).eval (d i)‖ ^ e := by
      rw [List.take_append_drop]
    by_cases hc : ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly (ss.drop (ss.length / 2))))⁻¹ ^ e)
          (Fin.last n))‖ ≤
        ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly (ss.take (ss.length / 2))))⁻¹ ^ e)
          (Fin.last n))‖
    · have hfr : findRitz H (j + 1) e ss = findRitz H j (2 * e) (ss.take (ss.length / 2)) := by
        rw [findRitz, if_pos hc]
      have hmax : ∀ g ∈ [ss.take (ss.length / 2), ss.drop (ss.length / 2)],
          ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly g))⁻¹ ^ e) (Fin.last n))‖ ≤
            ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly (ss.take (ss.length / 2))))⁻¹ ^ e)
              (Fin.last n))‖ := by
        intro g hg
        rcases List.mem_cons.mp hg with rfl | hg
        · exact le_refl _
        · rw [List.mem_singleton.mp hg]; exact hc
      have hmain := sum_lastRowWeights_div_norm_eval_shiftPoly_le hV hHV hdis (Or.inl rfl) e hmax
      have hih := ih (2 * e) _ hta hdis_a
      rw [hsplit, hfr, hpow]
      calc _ ≤ _ := hmain
        _ ≤ pseudoConditionNumber V ^ 4 * (pseudoConditionNumber V ^ (4 * j) *
            ∑ i, lastRowWeights V i / ‖d i - findRitz H j (2 * e) (ss.take (ss.length / 2))‖ ^
              (2 * e * 2 ^ j)) := mul_le_mul_of_nonneg_left hih (by positivity)
        _ = _ := by ring
    · have hfr : findRitz H (j + 1) e ss = findRitz H j (2 * e) (ss.drop (ss.length / 2)) := by
        rw [findRitz, if_neg hc]
      have hmax : ∀ g ∈ [ss.take (ss.length / 2), ss.drop (ss.length / 2)],
          ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly g))⁻¹ ^ e) (Fin.last n))‖ ≤
            ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly (ss.drop (ss.length / 2))))⁻¹ ^ e)
              (Fin.last n))‖ := by
        intro g hg
        rcases List.mem_cons.mp hg with rfl | hg
        · exact (not_le.mp hc).le
        · rw [List.mem_singleton.mp hg]
      have hmain := sum_lastRowWeights_div_norm_eval_shiftPoly_le hV hHV hdis (Or.inr rfl) e hmax
      have hih := ih (2 * e) _ htd hdis_b
      rw [hsplit, hfr, hpow]
      calc _ ≤ _ := hmain
        _ ≤ pseudoConditionNumber V ^ 4 * (pseudoConditionNumber V ^ (4 * j) *
            ∑ i, lastRowWeights V i / ‖d i - findRitz H j (2 * e) (ss.drop (ss.length / 2))‖ ^
              (2 * e * 2 ^ j)) := mul_le_mul_of_nonneg_left hih (by positivity)
        _ = _ := by ring

/-- **The binary search finds a promising Ritz value**: let $\mathbf{H}\mathbf{V} =
\mathbf{V}\operatorname{diag}(\mathbf{d})$, $\mathbf{V}$ invertible with
$\kappa = \|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2$, and `ss` a list of $k = 2^m$ shifts, none an
eigenvalue. If $\kappa^{4m} \le \alpha^k$, then `NLAlib.findRitz` $\mathbf{H}$ $m$ $1$ `ss` is an
$\alpha$-promising member of `ss`: $\sum_i w_i/\lvert p(\mathbf{d}_i)\rvert \le
\alpha^k\sum_i w_i/\lvert\mathbf{d}_i - r\rvert^k$. In particular
$\alpha = \kappa^{4\log_2 k/k}$ works. [BanksGarzaVargasSrivastava2021, Lemma 4.5].
Proof: induction on $m$ generalising the exponent: for `ss` of length $2^j$ and exponent $e$,
$\sum_i w_i/\lvert p_{\mathrm{ss}}(\mathbf{d}_i)\rvert^e \le \kappa^{4j}\sum_i w_i/\lvert
\mathbf{d}_i - r\rvert^{e2^j}$, each level by
`NLAlib.sum_lastRowWeights_div_norm_eval_shiftPoly_le` (the `if` of `NLAlib.findRitz` gives
`hmax`); membership by `NLAlib.findRitz_mem`. M, about 45 lines. -/
theorem isPromisingRitzValue_findRitz {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {d : Fin (n + 1) → ℂ} (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d) {m : ℕ}
    {ss : List ℂ} (hlen : ss.length = 2 ^ m) (hd : ∀ i, ∀ s ∈ ss, d i ≠ s) {α : ℝ}
    (hα : pseudoConditionNumber V ^ (4 * m) ≤ α ^ 2 ^ m) :
    IsPromisingRitzValue α V d ss (findRitz H m 1 ss) := by
  have hcard := sum_lastRowWeights_div_le_findRitz hV hHV m 1 ss hlen hd
  simp only [pow_one, one_mul] at hcard
  have hS0 : 0 ≤ ∑ i, lastRowWeights V i / ‖d i - findRitz H m 1 ss‖ ^ 2 ^ m :=
    Finset.sum_nonneg fun i _ => div_nonneg (lastRowWeights_nonneg V i) (by positivity)
  unfold IsPromisingRitzValue
  refine ⟨findRitz_mem H hlen, ?_⟩
  rw [hlen]
  calc _ ≤ _ := hcard
    _ ≤ α ^ 2 ^ m * ∑ i, lastRowWeights V i / ‖d i - findRitz H m 1 ss‖ ^ 2 ^ m :=
        mul_le_mul_of_nonneg_right hα hS0

end NLAlib
