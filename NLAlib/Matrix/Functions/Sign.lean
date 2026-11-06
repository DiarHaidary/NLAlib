/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Functions.HermitianCalculus
public import NLAlib.Matrix.Perturbation.DavisKahanGap
public import NLAlib.Matrix.Spectral.Inertia
public import NLAlib.Matrix.Spectral.Weyl
public import NLAlib.Polynomial.Approximation.NewtonSchulz
public import Mathlib.Data.Real.Sign

/-!
# The sign of a Hermitian matrix

The sign of a Hermitian matrix is
Mathlib's `cfc Real.sign A`; no new definition. The headline is a dimension-free perturbation
bound, $\|\operatorname{sign}(\mathbf{A}) - \operatorname{sign}(\mathbf{B})\|_2 \le
2\|\mathbf{A} - \mathbf{B}\|_2/a$ when every eigenvalue of $\mathbf{A}$ has modulus at least $a$,
proved by the Davis–Kahan theorem; it replaces the contour-integral Lemma 2.2 of [Shah2024]
($n\|\mathbf{A} - \mathbf{B}\|_2/(a - \|\mathbf{A} - \mathbf{B}\|_2)$, for any matrices).

## Main results

* `Matrix.IsHermitian.specNorm_cfc_sign_sub_cfc_sign_le`: the perturbation bound.
* `Matrix.IsHermitian.cfc_newtonSchulz`, `Matrix.IsHermitian.cfc_sign_cfc_newtonSchulz`.
* `Matrix.IsHermitian.specNorm_sub_cfc_sign_le`.
* `Matrix.IsHermitian.exists_hasOrthonormalCols_mul_conjTranspose_eq`: frames of the spectral
  projectors $\tfrac12(\mathbf{I} \pm \operatorname{sign}(\mathbf{A} - c\mathbf{I}))$.
* `Matrix.IsHermitian.re_trace_smul_one_add_cfc_sign`: the trace of the projector is the inertia.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The Newton–Schulz map of a Hermitian matrix is the polynomial
$g(\mathbf{A}) = \tfrac12\mathbf{A}(3\mathbf{I} - \mathbf{A}^2)$. -/
theorem _root_.Matrix.IsHermitian.cfc_newtonSchulz {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    cfc newtonSchulz A = (2⁻¹ : ℝ) • (A * ((3 : ℝ) • (1 : Matrix n n 𝕜) - A * A)) := by
  have hf : newtonSchulz = fun x : ℝ => (2⁻¹ : ℝ) * (x * ((3 : ℝ) - x * x)) :=
    funext fun x => by simp only [newtonSchulz]; ring
  have hA' : IsSelfAdjoint A := hA.isSelfAdjoint
  have hid : cfc (fun x : ℝ => x) A = A := cfc_id' ℝ A
  have hsq : cfc (fun x : ℝ => x * x) A = A * A := by
    rw [cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) A, hid]
  have h3 : cfc (fun _ : ℝ => (3 : ℝ)) A = (3 : ℝ) • (1 : Matrix n n 𝕜) := by
    rw [cfc_const (3 : ℝ) A, Algebra.algebraMap_eq_smul_one]
  rw [hf, cfc_const_mul (2⁻¹ : ℝ) (fun x : ℝ => x * ((3 : ℝ) - x * x)) A,
    cfc_mul (fun x : ℝ => x) (fun x : ℝ => (3 : ℝ) - x * x) A,
    cfc_sub (fun _ : ℝ => (3 : ℝ)) (fun x : ℝ => x * x) A, hid, hsq, h3]

/-- `Real.sign` is continuous away from zero. -/
private theorem continuousAt_real_sign_of_ne_zero {y : ℝ} (hy : y ≠ 0) :
    ContinuousAt Real.sign y := by
  rcases hy.lt_or_gt with hneg | hpos
  · exact (continuousAt_const : ContinuousAt (fun _ : ℝ => (-1 : ℝ)) y).congr
      (Filter.eventually_of_mem (Iio_mem_nhds hneg) fun z hz => (Real.sign_of_neg hz).symm)
  · exact (continuousAt_const : ContinuousAt (fun _ : ℝ => (1 : ℝ)) y).congr
      (Filter.eventually_of_mem (Ioi_mem_nhds hpos) fun z hz => (Real.sign_of_pos hz).symm)

/-- An eigendecomposition $\mathbf{A} = \mathbf{U}\mathbf{D}\mathbf{U}^{\mathsf{H}}$ with sorted
eigenvalues, and the frame $\mathbf{W}$ of its first $p$ columns: $\mathbf{A}\mathbf{W}$ is
$\mathbf{W}$ times the first $p$ eigenvalues and $\mathbf{W}\mathbf{W}^{\mathsf{H}}$ is
$\mathbf{U}$ times the indicator of the first $p$ indices times $\mathbf{U}^{\mathsf{H}}$. -/
private theorem exists_hasOrthonormalCols_mul_eq_mul_diagonal {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {p : ℕ} (hp : p ≤ Fintype.card n) :
    ∃ (U : Matrix n (Fin (Fintype.card n)) 𝕜) (W : Matrix n (Fin p) 𝕜), HasOrthonormalCols U ∧
      A = U * (Matrix.diagonal fun i : Fin (Fintype.card n) => ((eigenvalue A i : ℝ) : 𝕜)) * Uᴴ ∧
      U * Uᴴ = 1 ∧ HasOrthonormalCols W ∧
      A * W = W * Matrix.diagonal (fun j : Fin p => ((eigenvalue A j : ℝ) : 𝕜)) ∧
      W * Wᴴ = U * Matrix.diagonal (fun i : Fin (Fintype.card n) =>
        if (i : ℕ) < p then (1 : 𝕜) else 0) * Uᴴ := by
  classical
  obtain ⟨U, hU, hAU⟩ := hA.exists_eq_mul_diagonal_mul_conjTranspose
  have hAU' : A * U =
      U * Matrix.diagonal fun i : Fin (Fintype.card n) => ((eigenvalue A i : ℝ) : 𝕜) := by
    nth_rw 1 [hAU]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hU.conjTranspose_mul_self, Matrix.mul_one]
  refine ⟨U, U.submatrix id (Fin.castLE hp), hU, hAU,
    hU.mul_conjTranspose_self_of_card_eq (Fintype.card_fin _).symm,
    hU.submatrix (Equiv.refl _) (Fin.castLE_injective hp), ?_, ?_⟩
  · ext x j
    have h := congrFun (congrFun hAU' x) (Fin.castLE hp j)
    simp only [Matrix.mul_diagonal] at h ⊢
    exact h
  · ext r s
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id]
    refine Fintype.sum_of_injective (Fin.castLE hp) (Fin.castLE_injective hp) _ _
      (fun i hi => ?_) (fun j => ?_)
    · have h : ¬ (i : ℕ) < p := fun h => hi ⟨⟨i, h⟩, rfl⟩
      simp [Matrix.diagonal_apply, h]
    · simp [Matrix.diagonal_apply, j.2]

/-- The sign of a Hermitian matrix whose first $p$ sorted eigenvalues are positive and the others
negative is $2\mathbf{W}\mathbf{W}^{\mathsf{H}} - \mathbf{I}$, for the frame $\mathbf{W}$ of the
top $p$ eigenvectors. -/
private theorem exists_hasOrthonormalCols_cfc_sign_eq_two_smul_sub_one {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {p : ℕ} (hp : p ≤ Fintype.card n)
    (h : ∀ i : Fin (Fintype.card n), (i : ℕ) < p ↔ 0 < eigenvalue A i)
    (h0 : ∀ i : Fin (Fintype.card n), eigenvalue A i ≠ 0) :
    ∃ W : Matrix n (Fin p) 𝕜, HasOrthonormalCols W ∧
      A * W = W * Matrix.diagonal (fun i : Fin p => ((eigenvalue A i : ℝ) : 𝕜)) ∧
      cfc Real.sign A = (2 : ℝ) • (W * Wᴴ) - 1 := by
  classical
  obtain ⟨U, W, hU, hAU, hUU, hW, hAW, hWW⟩ := exists_hasOrthonormalCols_mul_eq_mul_diagonal hA hp
  refine ⟨W, hW, hAW, ?_⟩
  set I := Matrix.diagonal fun i : Fin (Fintype.card n) => if (i : ℕ) < p then (1 : 𝕜) else 0
  have hD : (Matrix.diagonal fun i : Fin (Fintype.card n) =>
      ((Real.sign (eigenvalue A i) : ℝ) : 𝕜)) = (2 : ℝ) • I - 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      by_cases hi : (i : ℕ) < p
      · simp [I, hi, Real.sign_of_pos ((h i).mp hi), two_smul]
      · simp [I, hi, Real.sign_of_neg (lt_of_le_of_ne (not_lt.mp ((h i).not.mp hi)) (h0 i))]
    · simp [I, hij]
  rw [HasOrthonormalCols.cfc_eq_mul_diagonal_mul_conjTranspose hU (Fintype.card_fin _) hAU, hD,
    hWW, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hUU, Matrix.mul_smul, Matrix.smul_mul]

/-- **Perturbation of the sign of a Hermitian matrix**: for Hermitian $\mathbf{A}, \mathbf{B}$
and $a > 0$ with $\lvert \lambda \rvert \ge a$ for every eigenvalue $\lambda$ of $\mathbf{A}$,
$$\|\operatorname{sign}(\mathbf{A}) - \operatorname{sign}(\mathbf{B})\|_2 \le
\frac{2\|\mathbf{A} - \mathbf{B}\|_2}{a} \,.$$
[Shah2024, Lemma 2.2], there $n\|\mathbf{A} - \mathbf{B}\|_2/(a - \|\mathbf{A} - \mathbf{B}\|_2)$
for $\|\mathbf{A} - \mathbf{B}\|_2 < a$ and any matrices, by a contour integral; for Hermitian
matrices the bound is dimension-free and needs no size condition. -/
theorem _root_.Matrix.IsHermitian.specNorm_cfc_sign_sub_cfc_sign_le {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {a : ℝ} (ha : 0 < a)
    (hspec : ∀ x ∈ spectrum ℝ A, a ≤ |x|) :
    specNorm (cfc Real.sign A - cfc Real.sign B) ≤ 2 * specNorm (A - B) / a := by
  classical
  have hε := specNorm_nonneg (A - B)
  rcases le_or_gt a (specNorm (A - B)) with hεa | hεa
  · have hsgn : ∀ x : ℝ, |Real.sign x| ≤ 1 := fun x => by
      rcases Real.sign_apply_eq x with h | h | h <;> rw [h] <;> norm_num
    calc specNorm (cfc Real.sign A - cfc Real.sign B) ≤ 1 + 1 :=
          (specNorm_sub_le _ _).trans (add_le_add (hA.specNorm_cfc_le zero_le_one fun x _ => hsgn x)
            (hB.specNorm_cfc_le zero_le_one fun x _ => hsgn x))
      _ ≤ 2 * specNorm (A - B) / a := by rw [le_div_iff₀ ha]; linarith
  have hAi : ∀ i : Fin (Fintype.card n), a ≤ |eigenvalue A i| := fun i =>
    hspec _ (hA.eigenvalue_mem_spectrum i.isLt)
  have hBi := hA.abs_eigenvalue_sub_le hB
  obtain ⟨p, hp⟩ : ∃ p, p = inertiaPos A := ⟨_, rfl⟩
  have hpA : ∀ i : Fin (Fintype.card n), (i : ℕ) < p ↔ 0 < eigenvalue A i := fun i => by
    rw [hp, hA.lt_inertiaPos_iff]
    simp [i.isLt]
  have hpB : ∀ i : Fin (Fintype.card n), (i : ℕ) < p ↔ 0 < eigenvalue B i := fun i => by
    rw [hpA]
    have h2 := abs_le.mp (hBi i)
    rcases le_abs'.mp (hAi i) with h3 | h3 <;> constructor <;> intro h4 <;> linarith
  have hA0 : ∀ i : Fin (Fintype.card n), eigenvalue A i ≠ 0 := fun i h => by
    linarith [h ▸ hAi i, abs_zero (α := ℝ)]
  have hB0 : ∀ i : Fin (Fintype.card n), eigenvalue B i ≠ 0 := fun i h => by
    have := hBi i
    rw [h, sub_zero] at this
    linarith [hAi i]
  have hpN : p ≤ Fintype.card n :=
    hp ▸ (Finset.card_filter_le _ _).trans (Finset.card_range _).le
  obtain ⟨W, hW, hAW, hsA⟩ := exists_hasOrthonormalCols_cfc_sign_eq_two_smul_sub_one hA hpN hpA hA0
  obtain ⟨W', hW', hBW', hsB⟩ :=
    exists_hasOrthonormalCols_cfc_sign_eq_two_smul_sub_one hB hpN hpB hB0
  rw [hsA, hsB, show (2 : ℝ) • (W * Wᴴ) - 1 - ((2 : ℝ) • (W' * W'ᴴ) - 1) =
    (2 : ℝ) • (W * Wᴴ - W' * W'ᴴ) by rw [smul_sub]; abel, specNorm_real_smul, abs_two,
    mul_div_assoc]
  gcongr
  rcases Nat.eq_zero_or_pos p with h0 | hpos
  · subst h0
    rw [show W * Wᴴ = 0 by ext; simp [Matrix.mul_apply],
      show W' * W'ᴴ = 0 by ext; simp [Matrix.mul_apply], sub_self, specNorm_zero]
    positivity
  rcases eq_or_lt_of_le hpN with hN | hN
  · have hc : Fintype.card n = Fintype.card (Fin p) := by rw [Fintype.card_fin, hN]
    rw [hW.mul_conjTranspose_self_of_card_eq hc, hW'.mul_conjTranspose_self_of_card_eq hc,
      sub_self, specNorm_zero]
    positivity
  obtain ⟨j, rfl⟩ : ∃ j, p = j + 1 := ⟨p - 1, by omega⟩
  have hlj : a ≤ eigenvalue A j :=
    abs_of_pos ((hpA ⟨j, by omega⟩).mp (by simp)) ▸ hAi ⟨j, by omega⟩
  have hlj1 : eigenvalue A (j + 1) ≤ -a :=
    (le_abs'.mp (hAi ⟨j + 1, hN⟩)).resolve_right fun h' =>
      (hpA ⟨j + 1, hN⟩).not.mp (by simp) (ha.trans_le h')
  have hgap : 2 * a ≤ eigengap A (j + 1) := by rw [eigengap_succ]; linarith
  have hDK := hA.specNorm_one_sub_mul_le_two_mul_specNorm_div_eigengap (hB.sub hA) hW hW' hAW
    (by rw [add_sub_cancel]; exact hBW') (by linarith)
  have hrank : (W' * W'ᴴ).rank = (W * Wᴴ).rank := by
    rw [← hW.rangeProjector_eq, ← hW'.rangeProjector_eq, rank_rangeProjector,
      rank_rangeProjector, hW.rank_eq, hW'.rank_eq]
  calc specNorm (W * Wᴴ - W' * W'ᴴ)
      = specNorm ((1 - W * Wᴴ) * W' * W'ᴴ) := by
        rw [specNorm_sub_comm, hW'.isStarProjection_mul_conjTranspose.specNorm_sub_eq_of_rank_eq
          hW.isStarProjection_mul_conjTranspose hrank, Matrix.mul_assoc]
    _ ≤ specNorm ((1 - W * Wᴴ) * W') * specNorm W'ᴴ := specNorm_mul_le _ _
    _ ≤ specNorm ((1 - W * Wᴴ) * W') * 1 := by
        gcongr
        rw [specNorm_conjTranspose]
        exact hW'.specNorm_le_one
    _ ≤ 2 * specNorm (B - A) / eigengap A (j + 1) := by rw [mul_one]; exact hDK
    _ ≤ specNorm (A - B) / a := by
        rw [specNorm_sub_comm, div_le_div_iff₀ (by linarith) ha]
        nlinarith [mul_le_mul_of_nonneg_left hgap hε]

/-- The Newton–Schulz map does not change the sign: for Hermitian $\mathbf{A}$ with
$0 < \lvert \lambda \rvert < \sqrt3$ for every eigenvalue,
$\operatorname{sign}(g(\mathbf{A})) = \operatorname{sign}(\mathbf{A})$. [Shah2024, proof of
Theorem 2.6]. -/
theorem _root_.Matrix.IsHermitian.cfc_sign_cfc_newtonSchulz {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (h : ∀ x ∈ spectrum ℝ A, 0 < |x| ∧ |x| < √3) :
    cfc Real.sign (cfc newtonSchulz A) = cfc Real.sign A := by
  have hsq : ∀ x ∈ spectrum ℝ A, x ^ 2 < 3 := fun x hx => by
    rw [← sq_abs]
    exact (Real.lt_sqrt (abs_nonneg x)).mp (h x hx).2
  have hfac : ∀ x : ℝ, newtonSchulz x = x * ((3 - x ^ 2) / 2) := fun x => by
    unfold newtonSchulz; ring
  calc cfc Real.sign (cfc newtonSchulz A) = cfc (Real.sign ∘ newtonSchulz) A := by
        refine (cfc_comp' Real.sign newtonSchulz A ?_ ?_).symm
        · rintro _ ⟨x, hx, rfl⟩
          have hne : newtonSchulz x ≠ 0 := by
            rw [hfac]
            exact mul_ne_zero (abs_pos.mp (h x hx).1)
              (by have := hsq x hx; exact (by linarith : (0 : ℝ) < (3 - x ^ 2) / 2).ne')
          exact (continuousAt_real_sign_of_ne_zero hne).continuousWithinAt
        · exact (Continuous.continuousOn (by unfold newtonSchulz; fun_prop))
    _ = cfc Real.sign A := cfc_congr fun x hx => by
        have hx0 : x ≠ 0 := abs_pos.mp (h x hx).1
        have hq : 0 < (3 - x ^ 2) / 2 := by linarith [hsq x hx]
        simp only [Function.comp_apply, hfac]
        rcases hx0.lt_or_gt with hneg | hpos
        · rw [Real.sign_of_neg hneg, Real.sign_of_neg (mul_neg_of_neg_of_pos hneg hq)]
        · rw [Real.sign_of_pos hpos, Real.sign_of_pos (mul_pos hpos hq)]

/-- A Hermitian matrix with nearly unimodular eigenvalues is near its sign: if
$\lvert 1 - \lambda^2 \rvert \le \delta$ for every eigenvalue $\lambda$, then
$\|\mathbf{A} - \operatorname{sign}(\mathbf{A})\|_2 \le \delta$. [Shah2024, proof of
Theorem 2.6]. -/
theorem _root_.Matrix.IsHermitian.specNorm_sub_cfc_sign_le {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {δ : ℝ} (hδ : 0 ≤ δ) (h : ∀ x ∈ spectrum ℝ A, |1 - x ^ 2| ≤ δ) :
    specNorm (A - cfc Real.sign A) ≤ δ := by
  have hfin : (spectrum ℝ A).Finite := Matrix.finite_real_spectrum
  have hsub : A - cfc Real.sign A = cfc (fun x => x - Real.sign x) A := by
    rw [cfc_sub (fun x => x) Real.sign A (hf := continuousOn_id)
      (hg := hfin.continuousOn _), cfc_id' ℝ A]
  rw [hsub]
  refine hA.specNorm_cfc_le hδ fun x hx => (?_ : _ ≤ |1 - x ^ 2|).trans (h x hx)
  rcases lt_trichotomy x 0 with hx0 | rfl | hx0
  · rw [Real.sign_of_neg hx0, abs_le]
    constructor <;> nlinarith [le_abs_self (1 - x ^ 2), neg_abs_le (1 - x ^ 2)]
  · simp
  · rw [Real.sign_of_pos hx0, abs_le]
    constructor <;> nlinarith [le_abs_self (1 - x ^ 2), neg_abs_le (1 - x ^ 2)]

/-- **Frames of the spectral projectors**: for Hermitian $\mathbf{A}$ and $c$ not an eigenvalue,
with $k = i_+(\mathbf{A} - c\mathbf{I})$ (`NLAlib.inertiaPos`), there is
$\mathbf{V} \in \Bbbk^{n \times k}$ with orthonormal columns such that
$\mathbf{V}\mathbf{V}^{\mathsf{H}} = \tfrac12(\mathbf{I} + \operatorname{sign}(\mathbf{A} -
c\mathbf{I}))$, $\mathbf{A}\mathbf{V} = \mathbf{V}(\mathbf{V}^{\mathsf{H}}\mathbf{A}\mathbf{V})$,
and the spectrum of $\mathbf{V}^{\mathsf{H}}\mathbf{A}\mathbf{V}$ lies in the spectrum of
$\mathbf{A}$ above $c$. The negative side is this lemma for $-\mathbf{A}$ and $-c$.
[Shah2024, proof of Lemma 4.1]. -/
theorem _root_.Matrix.IsHermitian.exists_hasOrthonormalCols_mul_conjTranspose_eq
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {c : ℝ} (hc : ∀ x ∈ spectrum ℝ A, x ≠ c) :
    ∃ V : Matrix n (Fin (inertiaPos (A - c • (1 : Matrix n n 𝕜)))) 𝕜, HasOrthonormalCols V ∧
      V * Vᴴ = (2⁻¹ : ℝ) • (1 + cfc Real.sign (A - c • (1 : Matrix n n 𝕜))) ∧
      A * V = V * (Vᴴ * A * V) ∧ spectrum ℝ (Vᴴ * A * V) ⊆ spectrum ℝ A ∩ Set.Ioi c := by
  classical
  set k := inertiaPos (A - c • (1 : Matrix n n 𝕜))
  have hAc : (A - c • (1 : Matrix n n 𝕜)).IsHermitian :=
    hA.sub (by simp [Matrix.IsHermitian, Matrix.conjTranspose_smul])
  have hk : ∀ i : Fin (Fintype.card n), (i : ℕ) < k ↔ c < eigenvalue A i := fun i => by
    rw [hAc.lt_inertiaPos_iff, sub_eq_add_neg, ← neg_smul, hA.eigenvalue_add_smul_one _ i.isLt]
    simp [i.isLt]
  have hkN : k ≤ Fintype.card n := (Finset.card_filter_le _ _).trans (Finset.card_range _).le
  obtain ⟨U, V, hU, hAU, hUU, hV, hAV, hVV⟩ := exists_hasOrthonormalCols_mul_eq_mul_diagonal hA hkN
  have hC : Vᴴ * A * V = Matrix.diagonal fun j : Fin k => ((eigenvalue A j : ℝ) : 𝕜) := by
    rw [Matrix.mul_assoc, hAV, ← Matrix.mul_assoc, hV.conjTranspose_mul_self, Matrix.one_mul]
  refine ⟨V, hV, ?_, by rw [hC, hAV], ?_⟩
  · have hAcU : A - c • (1 : Matrix n n 𝕜) = U * Matrix.diagonal
        (fun i : Fin (Fintype.card n) => ((eigenvalue A i - c : ℝ) : 𝕜)) * Uᴴ := by
      have h : Matrix.diagonal (fun i : Fin (Fintype.card n) => ((eigenvalue A i - c : ℝ) : 𝕜)) =
          Matrix.diagonal (fun i : Fin (Fintype.card n) => ((eigenvalue A i : ℝ) : 𝕜)) -
            c • 1 := by
        ext i j
        by_cases hij : i = j <;>
          simp [hij, Algebra.algebraMap_eq_smul_one, sub_smul]
      rw [h, Matrix.mul_sub, Matrix.sub_mul, ← hAU, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_one, hUU]
    rw [HasOrthonormalCols.cfc_eq_mul_diagonal_mul_conjTranspose hU (Fintype.card_fin _) hAcU]
    set D := Matrix.diagonal fun i : Fin (Fintype.card n) =>
      ((Real.sign (eigenvalue A i - c) : ℝ) : 𝕜)
    have hP : (2⁻¹ : ℝ) • (1 + D) = Matrix.diagonal fun i : Fin (Fintype.card n) =>
        if (i : ℕ) < k then 1 else 0 := by
      ext i j
      by_cases hij : i = j
      · subst hij
        by_cases h : (i : ℕ) < k
        · simp only [D, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply_eq,
            Matrix.diagonal_apply_eq, Real.sign_of_pos (sub_pos.mpr ((hk i).mp h)),
            RCLike.ofReal_one, h, if_true, ← one_add_one_eq_two, smul_add]
          rw [← add_smul]
          norm_num
        · have hlt : eigenvalue A i < c := lt_of_le_of_ne (not_lt.mp ((hk i).not.mp h))
            (hc _ (hA.eigenvalue_mem_spectrum i.isLt))
          simp [D, h, Real.sign_of_neg (sub_neg.mpr hlt)]
      · simp [D, hij]
    rw [← hUU, show U * Uᴴ + U * D * Uᴴ = U * (1 + D) * Uᴴ by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one], ← Matrix.smul_mul, ← Matrix.mul_smul, hP,
      hVV]
  · rw [hC]
    set d := fun j : Fin k => eigenvalue A j
    obtain ⟨e, he⟩ :=
      hasOrthonormalCols_one.exists_equiv_eq_eigenvalue_of_eq_mul_diagonal_mul_conjTranspose
        (A := Matrix.diagonal fun j => ((d j : ℝ) : 𝕜)) (d := d) rfl
        (by rw [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one])
    have hD : (Matrix.diagonal fun j => ((d j : ℝ) : 𝕜)).IsHermitian :=
      Matrix.isHermitian_diagonal_iff.mpr fun j => RCLike.conj_ofReal _
    rw [hD.spectrum_subset_iff]
    intro i hi
    obtain ⟨j, hj⟩ := e.surjective ⟨i, hi⟩
    have h := he j
    rw [hj] at h
    rw [show eigenvalue _ i = d j from h.symm]
    exact ⟨hA.eigenvalue_mem_spectrum (j.2.trans_le hkN), (hk ⟨j, j.2.trans_le hkN⟩).mp j.2⟩

/-- **The trace of a spectral projector is the inertia**: for Hermitian $\mathbf{A}$ and $c$ not an
eigenvalue, $\operatorname{Re}\operatorname{tr}\tfrac12(\mathbf{I} + \operatorname{sign}(\mathbf{A}
- c\mathbf{I})) = i_+(\mathbf{A} - c\mathbf{I})$. [Shah2024, proof of Lemma 4.1]. -/
theorem _root_.Matrix.IsHermitian.re_trace_smul_one_add_cfc_sign {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {c : ℝ} (hc : ∀ x ∈ spectrum ℝ A, x ≠ c) :
    RCLike.re ((2⁻¹ : ℝ) • (1 + cfc Real.sign (A - c • (1 : Matrix n n 𝕜)))).trace =
      inertiaPos (A - c • (1 : Matrix n n 𝕜)) := by
  have hB : (A - c • (1 : Matrix n n 𝕜)).IsHermitian :=
    hA.sub (by simp [Matrix.IsHermitian, Matrix.conjTranspose_smul])
  have hsp : ∀ x ∈ spectrum ℝ (A - c • (1 : Matrix n n 𝕜)), x ≠ 0 := by
    intro x hx hx0
    rw [← Algebra.algebraMap_eq_smul_one, ← spectrum.sub_singleton_eq] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_sub.mp hx
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact hc y hy (sub_eq_zero.mp hx0)
  have hsign : ContinuousOn Real.sign (spectrum ℝ (A - c • (1 : Matrix n n 𝕜))) :=
    fun x hx => (continuousAt_real_sign_of_ne_zero (hsp x hx)).continuousWithinAt
  have hcg : cfc (fun y : ℝ => (2⁻¹ : ℝ) * (1 + Real.sign y)) (A - c • (1 : Matrix n n 𝕜)) =
      (2⁻¹ : ℝ) • (1 + cfc Real.sign (A - c • (1 : Matrix n n 𝕜))) := by
    rw [cfc_const_mul (2⁻¹ : ℝ) (fun y : ℝ => 1 + Real.sign y) (A - c • (1 : Matrix n n 𝕜)),
      cfc_add (A - c • (1 : Matrix n n 𝕜)) (fun _ : ℝ => (1 : ℝ)) Real.sign
        continuousOn_const hsign,
      cfc_const (1 : ℝ) (A - c • (1 : Matrix n n 𝕜)), map_one]
  rw [← hcg, hB.re_trace_cfc, inertiaPos, Finset.natCast_card_filter]
  refine Finset.sum_congr rfl fun i hi => ?_
  have he := hsp _ (hB.eigenvalue_mem_spectrum (Finset.mem_range.mp hi))
  rcases he.lt_or_gt with hneg | hpos
  · rw [Real.sign_of_neg hneg, if_neg (not_lt.mpr hneg.le)]; norm_num
  · rw [Real.sign_of_pos hpos, if_pos hpos]; norm_num

end NLAlib
