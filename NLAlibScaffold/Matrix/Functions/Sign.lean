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
public import NLAlibScaffold.Polynomial.Approximation.NewtonSchulz
public import Mathlib.Data.Real.Sign

/-!
# The sign of a Hermitian matrix (scaffold)

Statements for a new file `NLAlib/Matrix/Functions/Sign.lean` (stage HDIAG, wave W1, design note
`docs/design/Eigensolvers-HermitianDiagonalization.md` §3.2). The sign of a Hermitian matrix is
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
$g(\mathbf{A}) = \tfrac12\mathbf{A}(3\mathbf{I} - \mathbf{A}^2)$.
Proof: `cfc_mul`, `cfc_sub`, `cfc_const`, `cfc_id`, `cfc_pow` (Mathlib's unital continuous
functional calculus) after rewriting
`NLAlib.newtonSchulz` as `fun x => (2⁻¹ : ℝ) * (x * (3 - x * x))`; or
`Matrix.IsHermitian.cfc_eq` and a diagonal computation. M, about 12 lines. -/
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
  obtain ⟨U, hU, hAU⟩ := hA.exists_eq_mul_diagonal_mul_conjTranspose
  have hUU : U * Uᴴ = 1 := hU.mul_conjTranspose_self_of_card_eq (Fintype.card_fin _).symm
  set W := U.submatrix id (Fin.castLE hp)
  have hAU' : A * U =
      U * Matrix.diagonal fun i : Fin (Fintype.card n) => ((eigenvalue A i : ℝ) : 𝕜) := by
    nth_rw 1 [hAU]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hU.conjTranspose_mul_self, Matrix.mul_one]
  refine ⟨W, hU.submatrix (Equiv.refl _) (Fin.castLE_injective hp), ?_, ?_⟩
  · ext x j
    have h := congrFun (congrFun hAU' x) (Fin.castLE hp j)
    simp only [Matrix.mul_diagonal] at h ⊢
    exact h
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
  have hWW : W * Wᴴ = U * I * Uᴴ := by
    ext r s
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, W, Matrix.submatrix_apply, id]
    refine Fintype.sum_of_injective (Fin.castLE hp) (Fin.castLE_injective hp) _ _
      (fun i hi => ?_) (fun j => ?_)
    · have h : ¬ (i : ℕ) < p := fun h => hi ⟨⟨i, h⟩, rfl⟩
      simp [I, Matrix.diagonal_apply, h]
    · simp [I, Matrix.diagonal_apply, j.2]
  rw [HasOrthonormalCols.cfc_eq_mul_diagonal_mul_conjTranspose hU (Fintype.card_fin _) hAU, hD,
    hWW, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hUU, Matrix.mul_smul, Matrix.smul_mul]

/-- **Perturbation of the sign of a Hermitian matrix**: for Hermitian $\mathbf{A}, \mathbf{B}$
and $a > 0$ with $\lvert \lambda \rvert \ge a$ for every eigenvalue $\lambda$ of $\mathbf{A}$,
$$\|\operatorname{sign}(\mathbf{A}) - \operatorname{sign}(\mathbf{B})\|_2 \le
\frac{2\|\mathbf{A} - \mathbf{B}\|_2}{a} \,.$$
[Shah2024, Lemma 2.2], there $n\|\mathbf{A} - \mathbf{B}\|_2/(a - \|\mathbf{A} - \mathbf{B}\|_2)$
for $\|\mathbf{A} - \mathbf{B}\|_2 < a$ and any matrices, by a contour integral; for Hermitian
matrices the bound is dimension-free and needs no size condition.
Proof: if $\|\mathbf{E}\|_2 \ge a$, $\mathbf{E} = \mathbf{B} - \mathbf{A}$, the left side is at
most $2$ (`Matrix.IsHermitian.specNorm_cfc_le` with $\lvert\operatorname{sign}\rvert \le 1$). Else
$\mathbf{A}$ has $p$ eigenvalues $\ge a$ and $\mathbf{B}$ exactly $p$ eigenvalues
$\ge a - \|\mathbf{E}\|_2 > 0$ and none in $(-(a - \|\mathbf{E}\|_2), a - \|\mathbf{E}\|_2)$
(`Matrix.IsHermitian.abs_eigenvalue_sub_le`); $\operatorname{sign} = 2\mathbf{P} - \mathbf{I}$
for the top-$p$ eigenprojectors (`HasOrthonormalCols.cfc_eq_mul_diagonal_mul_conjTranspose`);
`Matrix.IsHermitian.specNorm_one_sub_mul_le_two_mul_specNorm_div_eigengap` with
$\lambda_{p-1}(\mathbf{A}) - \lambda_p(\mathbf{A}) \ge 2a$ gives
$\|(\mathbf{I} - \mathbf{P})\mathbf{P}'\|_2 \le \|\mathbf{E}\|_2/a$, and for projectors of equal
rank $\|\mathbf{P} - \mathbf{P}'\|_2 = \|(\mathbf{I} - \mathbf{P})\mathbf{P}'\|_2$
(`IsStarProjection.singularValues_one_sub_mul_eq_of_rank_eq`). Cases $p = 0$ and
$p = \lvert n \rvert$ separately (then the sign is $\mp\mathbf{I}$ for both). M, about 70 lines. -/
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
    have := hAi i
    rw [h, abs_zero] at this
    linarith
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
  have hlj : a ≤ eigenvalue A j := by
    have h := (hpA ⟨j, by omega⟩).mp (by simp)
    have h' := hAi ⟨j, by omega⟩
    rw [abs_of_pos h] at h'
    exact h'
  have hlj1 : eigenvalue A (j + 1) ≤ -a := by
    have h := (hpA ⟨j + 1, hN⟩).not.mp (by simp)
    rcases le_abs'.mp (hAi ⟨j + 1, hN⟩) with h' | h'
    · exact h'
    · exact absurd (ha.trans_le h') h
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
Theorem 2.6].
Proof: `cfc_comp` (Mathlib `cfc_comp'`), and $\operatorname{sign} \circ g = \operatorname{sign}$
on the spectrum (`NLAlib.mul_newtonSchulz_add_pos` at $\xi = u = 0$, or directly:
$g(x) = x(3 - x^2)/2$ has the sign of $x$), `cfc_congr`. M, about 12 lines. -/
theorem _root_.Matrix.IsHermitian.cfc_sign_cfc_newtonSchulz {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (h : ∀ x ∈ spectrum ℝ A, 0 < |x| ∧ |x| < √3) :
    cfc Real.sign (cfc newtonSchulz A) = cfc Real.sign A := by
  have hsq : ∀ x ∈ spectrum ℝ A, x ^ 2 < 3 := fun x hx => by
    have h1 := (h x hx).2
    have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    have h3 : |x| ^ 2 < 3 := by nlinarith [abs_nonneg x, Real.sqrt_nonneg 3]
    rwa [sq_abs] at h3
  have hfac : ∀ x : ℝ, newtonSchulz x = x * ((3 - x ^ 2) / 2) := fun x => by
    unfold newtonSchulz; ring
  have hcont : ∀ y : ℝ, y ≠ 0 → ContinuousAt Real.sign y := fun y hy => by
    rcases hy.lt_or_gt with hneg | hpos
    · exact (continuousAt_const : ContinuousAt (fun _ : ℝ => (-1 : ℝ)) y).congr
        (Filter.eventually_of_mem (Iio_mem_nhds hneg) fun z hz => (Real.sign_of_neg hz).symm)
    · exact (continuousAt_const : ContinuousAt (fun _ : ℝ => (1 : ℝ)) y).congr
        (Filter.eventually_of_mem (Ioi_mem_nhds hpos) fun z hz => (Real.sign_of_pos hz).symm)
  calc cfc Real.sign (cfc newtonSchulz A) = cfc (Real.sign ∘ newtonSchulz) A := by
        refine (cfc_comp' Real.sign newtonSchulz A ?_ ?_).symm
        · rintro _ ⟨x, hx, rfl⟩
          have hne : newtonSchulz x ≠ 0 := by
            rw [hfac]
            exact mul_ne_zero (abs_pos.mp (h x hx).1)
              (by have := hsq x hx; exact (by linarith : (0 : ℝ) < (3 - x ^ 2) / 2).ne')
          exact (hcont _ hne).continuousWithinAt
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
Theorem 2.6].
Proof: $\mathbf{A} - \operatorname{sign}(\mathbf{A}) = f(\mathbf{A})$ with
$f(x) = x - \operatorname{sign}(x)$ (`cfc_sub`, `cfc_id'`), and
$\lvert x - \operatorname{sign} x \rvert = \lvert \lvert x \rvert - 1 \rvert \le
\lvert 1 - x^2 \rvert$ for $x \ne 0$ and $0 \le 1$ at $x = 0$; `Matrix.IsHermitian.specNorm_cfc_le`.
S, about 15 lines. -/
theorem _root_.Matrix.IsHermitian.specNorm_sub_cfc_sign_le {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {δ : ℝ} (hδ : 0 ≤ δ) (h : ∀ x ∈ spectrum ℝ A, |1 - x ^ 2| ≤ δ) :
    specNorm (A - cfc Real.sign A) ≤ δ := by
  sorry

/-- **Frames of the spectral projectors**: for Hermitian $\mathbf{A}$ and $c$ not an eigenvalue,
with $k = i_+(\mathbf{A} - c\mathbf{I})$ (`NLAlib.inertiaPos`), there is
$\mathbf{V} \in \Bbbk^{n \times k}$ with orthonormal columns such that
$\mathbf{V}\mathbf{V}^{\mathsf{H}} = \tfrac12(\mathbf{I} + \operatorname{sign}(\mathbf{A} -
c\mathbf{I}))$, $\mathbf{A}\mathbf{V} = \mathbf{V}(\mathbf{V}^{\mathsf{H}}\mathbf{A}\mathbf{V})$,
and the spectrum of $\mathbf{V}^{\mathsf{H}}\mathbf{A}\mathbf{V}$ lies in the spectrum of
$\mathbf{A}$ above $c$. The negative side is this lemma for $-\mathbf{A}$ and $-c$.
[Shah2024, proof of Lemma 4.1].
Proof: take the eigenvectors of `Matrix.IsHermitian.eigenvectorBasis` with eigenvalue $> c$,
reindexed by `Fin k` (`Matrix.IsHermitian.lt_inertiaPos_iff` counts them);
`HasOrthonormalCols.cfc_eq_mul_diagonal_mul_conjTranspose` for the projector,
`Matrix.IsHermitian.cfc_mul_eq_mul_diagonal_of_mul_eq` for the invariance; the compression is
diagonal with those eigenvalues. M, about 60 lines. -/
theorem _root_.Matrix.IsHermitian.exists_hasOrthonormalCols_mul_conjTranspose_eq
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {c : ℝ} (hc : ∀ x ∈ spectrum ℝ A, x ≠ c) :
    ∃ V : Matrix n (Fin (inertiaPos (A - c • (1 : Matrix n n 𝕜)))) 𝕜, HasOrthonormalCols V ∧
      V * Vᴴ = (2⁻¹ : ℝ) • (1 + cfc Real.sign (A - c • (1 : Matrix n n 𝕜))) ∧
      A * V = V * (Vᴴ * A * V) ∧ spectrum ℝ (Vᴴ * A * V) ⊆ spectrum ℝ A ∩ Set.Ioi c := by
  sorry

/-- **The trace of a spectral projector is the inertia**: for Hermitian $\mathbf{A}$ and $c$ not an
eigenvalue, $\operatorname{Re}\operatorname{tr}\tfrac12(\mathbf{I} + \operatorname{sign}(\mathbf{A}
- c\mathbf{I})) = i_+(\mathbf{A} - c\mathbf{I})$. [Shah2024, proof of Lemma 4.1].
Proof: `Matrix.IsHermitian.re_trace_cfc` for $f(x) = \tfrac12(1 + \operatorname{sign}(x - c))$
(the left side is $\operatorname{tr}$ of `cfc` of it, `cfc_add`, `cfc_const`), which is the
indicator of $(c, \infty)$ on the spectrum; count with `NLAlib.inertiaPos` and
`Matrix.IsHermitian.lt_inertiaPos_iff`. M, about 20 lines. -/
theorem _root_.Matrix.IsHermitian.re_trace_smul_one_add_cfc_sign {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {c : ℝ} (hc : ∀ x ∈ spectrum ℝ A, x ≠ c) :
    RCLike.re ((2⁻¹ : ℝ) • (1 + cfc Real.sign (A - c • (1 : Matrix n n 𝕜)))).trace =
      inertiaPos (A - c • (1 : Matrix n n 𝕜)) := by
  have hB : (A - c • (1 : Matrix n n 𝕜)).IsHermitian := by
    refine hA.sub ?_
    unfold Matrix.IsHermitian
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, star_trivial]
  have hsp : ∀ x ∈ spectrum ℝ (A - c • (1 : Matrix n n 𝕜)), x ≠ 0 := by
    intro x hx hx0
    rw [← Algebra.algebraMap_eq_smul_one, ← spectrum.sub_singleton_eq] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_sub.mp hx
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact hc y hy (sub_eq_zero.mp hx0)
  have hcont : ∀ y : ℝ, y ≠ 0 → ContinuousAt Real.sign y := fun y hy => by
    rcases hy.lt_or_gt with hneg | hpos
    · exact (continuousAt_const : ContinuousAt (fun _ : ℝ => (-1 : ℝ)) y).congr
        (Filter.eventually_of_mem (Iio_mem_nhds hneg) fun z hz => (Real.sign_of_neg hz).symm)
    · exact (continuousAt_const : ContinuousAt (fun _ : ℝ => (1 : ℝ)) y).congr
        (Filter.eventually_of_mem (Ioi_mem_nhds hpos) fun z hz => (Real.sign_of_pos hz).symm)
  have hsign : ContinuousOn Real.sign (spectrum ℝ (A - c • (1 : Matrix n n 𝕜))) :=
    fun x hx => (hcont x (hsp x hx)).continuousWithinAt
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
