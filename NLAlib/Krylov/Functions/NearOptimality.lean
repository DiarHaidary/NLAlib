/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Functions.LanczosFA
public import NLAlib.Polynomial.Interpolation.Stieltjes

/-!
# Near-optimality of Lanczos-FA

For a function $f$ such that $f$ or $f(z)/z$ is a Stieltjes function, a Hermitian positive
definite $\mathbf{A}$ with spectrum in $[a, a']$ and real $\alpha$, the Lanczos-FA error in the
$\mathbf{A}^\alpha$-norm is within the factor
$\tfrac12\bigl(\kappa^{E/2} + \kappa^{-E/2}\bigr)$, $\kappa = a'/a$,
$E = \max(\alpha, 1 - \alpha)$, of the error of the best approximation from the Krylov space
[ChenPersson2026, Theorem 1]. The factor cannot be improved [ChenPersson2026, Theorem 2]; that
is stage K2b. At $\alpha = 0$ this is a Euclidean-norm guarantee with factor
$\tfrac12(\sqrt\kappa + 1/\sqrt\kappa)$, also for CG.

Errors are squared norms `RCLike.re (quadForm N (w - y))` with `N = A ^ α` or `N = cfc ν A`,
as for CG in K0, and the best approximation is not named: the theorems compare with every
$\mathbf{y}$ in the Krylov space.

The argument has one abstract step,
`Matrix.IsHermitian.re_quadForm_cfc_sub_le_of_sub_eq_aeval_mulVec`: an approximation
$\mathbf{y}_0 \in \mathcal{K}_q$ whose error is $\pi(\mathbf{A})\varsigma(\mathbf{A})\mathbf{b}$,
with $\pi(\mathbf{A})\mathbf{b} \perp \mathcal{K}_q$ and $\nu\varsigma$ varying by a factor at
most $R$ on the spectrum, is within $(R + 1)^2/(4R)$ of optimal in the squared
$\nu(\mathbf{A})$-norm. For Lanczos-FA, $\pi$ is the nodal polynomial of the Ritz values
(`HasOrthonormalCols.conjTranspose_mulVec_aeval_nodal_mulVec_eq_zero`) and $\varsigma$ the
Stieltjes function of the interpolation remainder
(`HasStieltjesMeasure.exists_sub_eval_interpolate_eq`).

## Main results

* `Matrix.IsHermitian.re_quadForm_cfc_sub_le_of_sub_eq_aeval_mulVec`: the abstract step.
* `Matrix.PosDef.re_quadForm_cfc_cfc_mulVec_sub_lanczosFA_le_of_hasStieltjesMeasure`: any norm
  $\nu(\mathbf{A})$ with a ratio bound $R$ on the kernel over the support of the measure
  [ChenPersson2026, Theorem 5]; `Matrix.PosDef.re_quadForm_cfc_cfc_mulVec_sub_lanczosFA_le`, the
  same with the bound for every $t \ge 0$.
* `Matrix.IsHermitian.re_quadForm_rpow_cfc_mulVec_sub_lanczosFA_le`: the $\mathbf{A}^\alpha$-norm
  bound [ChenPersson2026, Theorem 1].
* `Matrix.PosDef.re_quadForm_rpow_cfc_mulVec_sub_lanczosFA_le_pseudoConditionNumber`: the same
  in $\kappa(\mathbf{A})$.
* `Matrix.IsHermitian.norm_cfc_mulVec_sub_lanczosFA_le_mul_norm_sub`: the Euclidean norm.
* `Matrix.IsHermitian.re_quadForm_rpow_sub_cgIterate_add_smul_one_le`,
  `Matrix.IsHermitian.re_quadForm_rpow_sub_cgIterate_le`,
  `Matrix.IsHermitian.norm_sub_cgIterate_le_mul_norm_sub`: CG and shifted CG
  [ChenPersson2026, Remark 3].
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder
open Polynomial

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The abstract step -/

/-- The scalar fact behind the abstract step: on $[c, Rc]$, $R \ge 1$, the constant
$\hat g = 2Rc/(R + 1)$ satisfies $\lvert g - \hat g\rvert \le \frac{R - 1}{R + 1}\,g$. -/
private theorem abs_sub_two_mul_div_le {R c g : ℝ} (hR : 1 ≤ R) (hc : c ≤ g) (hg : g ≤ R * c) :
    |g - 2 * R * c / (R + 1)| ≤ (R - 1) / (R + 1) * g := by
  have hR1 : 0 < R + 1 := by linarith
  have h : g - 2 * R * c / (R + 1) = ((R + 1) * g - 2 * R * c) / (R + 1) := by
    field_simp [hR1.ne']
  rw [h, abs_div, abs_of_pos hR1, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hR1, abs_le]
  constructor <;> nlinarith

/-- The completed square behind the abstract step: if
$X \le \tau D E$ with $\tau = (R - 1)/(R + 1)$, $R \ge 1$, then
$E^2 \le \frac{(R + 1)^2}{4R}(E^2 - 2X + D^2)$, since
$E^2 - 2X + D^2 \ge (D - \tau E)^2 + (1 - \tau^2)E^2$ and $1/(1 - \tau^2) = (R + 1)^2/(4R)$. -/
private theorem sq_le_mul_sq_sub_two_mul_add_sq {R D E X : ℝ} (hR : 1 ≤ R)
    (hX : X ≤ (R - 1) / (R + 1) * D * E) :
    E ^ 2 ≤ (R + 1) ^ 2 / (4 * R) * (E ^ 2 - 2 * X + D ^ 2) := by
  set τ := (R - 1) / (R + 1) with hτdef
  have h1 : (1 - τ ^ 2) * E ^ 2 ≤ E ^ 2 - 2 * X + D ^ 2 := by
    nlinarith [sq_nonneg (D - τ * E)]
  have hR0 : R ≠ 0 := (by linarith : (0 : ℝ) < R).ne'
  have hR1 : R + 1 ≠ 0 := (by linarith : (0 : ℝ) < R + 1).ne'
  have h2 : (R + 1) ^ 2 / (4 * R) * (1 - τ ^ 2) = 1 := by
    rw [hτdef]
    field_simp
    ring
  have hR' : 0 < R := by linarith
  calc E ^ 2 = (R + 1) ^ 2 / (4 * R) * ((1 - τ ^ 2) * E ^ 2) := by
        rw [← mul_assoc, h2, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)

/-- **Near-optimality from a factored error**: let $\mathbf{A}$ be Hermitian, $\nu > 0$ and
$\varsigma \ge 0$ on its spectrum with $\nu(x)\varsigma(x) \le R\,\nu(y)\varsigma(y)$ for all
eigenvalues $x, y$ and some $R \ge 1$, and $\pi$ a real polynomial with
$\pi(\mathbf{A})\mathbf{b} \perp
\mathcal{K}_q(\mathbf{A}, \mathbf{b})$. If $\mathbf{y}_0 \in \mathcal{K}_q$ and
$\mathbf{w} - \mathbf{y}_0 = \pi(\mathbf{A})\varsigma(\mathbf{A})\mathbf{b}$, then for every
$\mathbf{y} \in \mathcal{K}_q$
$$\|\mathbf{w} - \mathbf{y}_0\|_{\nu(\mathbf{A})}^2 \le \frac{(R + 1)^2}{4R}\,
\|\mathbf{w} - \mathbf{y}\|_{\nu(\mathbf{A})}^2 \,.$$
With $g = \nu\varsigma$, $\hat g = 2Rc/(R + 1)$, $c = \min g$ and $\tau = (R - 1)/(R + 1)$,
orthogonality removes $\hat g$ from $\langle \mathbf{d}, \mathbf{w} - \mathbf{y}_0\rangle_\nu$
for $\mathbf{d} \in \mathcal{K}_q$, so that $\lvert\langle \mathbf{d}, \mathbf{w} -
\mathbf{y}_0\rangle_\nu\rvert \le \tau\|\mathbf{d}\|_\nu\|\mathbf{w} - \mathbf{y}_0\|_\nu$
(`Matrix.IsHermitian.norm_star_dotProduct_cfc_mulVec_le`), and $1/(1 - \tau^2) =
(R + 1)^2/(4R)$. The hypothesis $R \ge 1$ excludes a junk case ($\varsigma = 0$ with $R < 0$
would make the right side negative). [ChenPersson2026, Theorem 5], there for Lanczos-FA with
$R$ the ratio of $\nu\varsigma$. -/
theorem _root_.Matrix.IsHermitian.re_quadForm_cfc_sub_le_of_sub_eq_aeval_mulVec
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {ν ς : ℝ → ℝ} {R : ℝ} (hR₁ : 1 ≤ R)
    (hν : ∀ x ∈ spectrum ℝ A, 0 < ν x) (hς : ∀ x ∈ spectrum ℝ A, 0 ≤ ς x)
    (hR : ∀ x ∈ spectrum ℝ A, ∀ y ∈ spectrum ℝ A, ν x * ς x ≤ R * (ν y * ς y))
    {b w y₀ y : n → 𝕜} {q : ℕ} {π : ℝ[X]}
    (hπ : (krylovMatrix A b q)ᴴ *ᵥ (aeval A π *ᵥ b) = 0) (hy₀ : y₀ ∈ krylovSpace A b q)
    (he : w - y₀ = aeval A π *ᵥ (cfc ς A *ᵥ b)) (hy : y ∈ krylovSpace A b q) :
    RCLike.re (quadForm (cfc ν A) (w - y₀)) ≤
      (R + 1) ^ 2 / (4 * R) * RCLike.re (quadForm (cfc ν A) (w - y)) := by
  have hc : ∀ φ : ℝ → ℝ, ContinuousOn φ (spectrum ℝ A) := fun φ =>
    A.finite_real_spectrum.continuousOn φ
  set g : ℝ → ℝ := fun x => ν x * ς x with hg
  -- a constant `c` with `c ≤ g ≤ R c` on the spectrum
  obtain ⟨c, hcg⟩ : ∃ c, ∀ x ∈ spectrum ℝ A, c ≤ g x ∧ g x ≤ R * c := by
    rcases (spectrum ℝ A).eq_empty_or_nonempty with hemp | hne
    · exact ⟨0, fun x hx => by simp [hemp] at hx⟩
    · obtain ⟨x₀, hx₀, hmin⟩ :=
        A.finite_real_spectrum.toFinset.exists_min_image g (by simpa using hne)
      rw [Set.Finite.mem_toFinset] at hx₀
      exact ⟨g x₀, fun x hx =>
        ⟨hmin x ((Set.Finite.mem_toFinset _).mpr hx), hR x hx x₀ hx₀⟩⟩
  set ĝ := 2 * R * c / (R + 1)
  set τ := (R - 1) / (R + 1)
  have hτ : 0 ≤ τ := div_nonneg (by linarith) (by linarith)
  have hNH : (cfc ν A).IsHermitian := cfc_predicate ν A
  set e := w - y₀ with he_def
  set d := y - y₀
  have hd : d ∈ krylovSpace A b q := Submodule.sub_mem _ hy hy₀
  have hwy : w - y = e - d := (sub_sub_sub_cancel_right w y y₀).symm
  -- the norm is that of `√ν (A)`
  set ψ : ℝ → ℝ := fun x => Real.sqrt (ν x)
  have hnorm : ∀ v, ‖WithLp.toLp 2 (cfc ψ A *ᵥ v)‖ ^ 2 = RCLike.re (quadForm (cfc ν A) v) :=
    fun v => by
      rw [hA.norm_toLp_cfc_mulVec_sq, cfc_congr fun x hx => Real.sq_sqrt (hν x hx).le]
  have hA' : IsSelfAdjoint A := hA
  have hπA : aeval A π = cfc (fun x => π.eval x) A := (cfc_polynomial π A hA').symm
  -- `⟨d, e⟩_ν = dᴴ φ(A) b` with `φ = (g - ĝ) π`
  set φ : ℝ → ℝ := fun x => (g x - ĝ) * π.eval x
  have hNe : cfc ν A *ᵥ e = cfc φ A *ᵥ b + ĝ • (aeval A π *ᵥ b) := by
    have hM : cfc ν A * aeval A π * cfc ς A = cfc φ A + ĝ • aeval A π := by
      calc cfc ν A * aeval A π * cfc ς A = cfc (fun x => ν x * π.eval x * ς x) A := by
            rw [hπA, ← cfc_mul _ _ A (hc _) (hc _), ← cfc_mul _ _ A (hc _) (hc _)]
        _ = cfc (fun x => φ x + ĝ • π.eval x) A :=
            cfc_congr fun x _ => by simp only [φ, g, smul_eq_mul]; ring
        _ = cfc φ A + ĝ • aeval A π := by
            rw [cfc_add (a := A) φ (fun x => ĝ • π.eval x) (hc _) (hc _),
              cfc_smul ĝ (fun x => π.eval x) A (hc _), hπA]
    rw [he, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM, Matrix.add_mulVec,
      Matrix.smul_mulVec]
  have horth : star d ⬝ᵥ (aeval A π *ᵥ b) = 0 :=
    forall_mem_range_star_dotProduct_eq_zero_iff.mpr hπ d hd
  have hdot : star d ⬝ᵥ (cfc ν A *ᵥ e) = star d ⬝ᵥ (cfc φ A *ᵥ b) := by
    rw [hNe, dotProduct_add, dotProduct_smul, horth, smul_zero, add_zero]
  -- Cauchy–Schwarz with `ψ = √ν` and `χ = τ √ν ς π`
  set χ : ℝ → ℝ := fun x => τ * (ψ x * π.eval x * ς x)
  have hχ : cfc χ A *ᵥ b = τ • (cfc ψ A *ᵥ e) := by
    have hM : cfc χ A = τ • (cfc ψ A * aeval A π * cfc ς A) := by
      change cfc (fun x => τ • (ψ x * π.eval x * ς x)) A = _
      rw [hπA, ← cfc_mul _ _ A (hc _) (hc _), ← cfc_mul _ _ A (hc _) (hc _),
        ← cfc_smul τ _ A (hc _)]
    rw [hM, he, Matrix.smul_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have hbound : ∀ x ∈ spectrum ℝ A, |φ x| ≤ |ψ x| * |χ x| := fun x hx => by
    have hψ0 : 0 ≤ ψ x := Real.sqrt_nonneg _
    have hψ2 : ψ x * ψ x = ν x := Real.mul_self_sqrt (hν x hx).le
    have h1 := abs_sub_two_mul_div_le hR₁ (hcg x hx).1 (hcg x hx).2
    have hφ : |φ x| ≤ τ * g x * |π.eval x| := by
      simp only [φ, abs_mul]
      exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    have hψχ : |ψ x| * |χ x| = τ * g x * |π.eval x| := by
      simp only [χ, g, abs_mul, abs_of_nonneg hψ0, abs_of_nonneg hτ, abs_of_nonneg (hς x hx),
        ← hψ2]
      ring
    rw [hψχ]
    exact hφ
  have hCS := hA.norm_star_dotProduct_cfc_mulVec_le hbound d b
  rw [hχ, WithLp.toLp_smul, norm_smul, Real.norm_of_nonneg hτ, ← hdot] at hCS
  set D := ‖WithLp.toLp 2 (cfc ψ A *ᵥ d)‖
  set E := ‖WithLp.toLp 2 (cfc ψ A *ᵥ e)‖
  have hD2 : RCLike.re (quadForm (cfc ν A) d) = D ^ 2 := (hnorm d).symm
  have hE2 : RCLike.re (quadForm (cfc ν A) e) = E ^ 2 := (hnorm e).symm
  -- expand `‖e - d‖²`
  have hexp : RCLike.re (quadForm (cfc ν A) (e - d)) =
      E ^ 2 - 2 * RCLike.re (star e ⬝ᵥ (cfc ν A *ᵥ d)) + D ^ 2 := by
    rw [sub_eq_add_neg e d, hNH.re_quadForm_add, quadForm_neg_right, Matrix.mulVec_neg,
      dotProduct_neg, map_neg, hD2, hE2]
    ring
  have hcross : RCLike.re (star e ⬝ᵥ (cfc ν A *ᵥ d)) ≤ τ * D * E := by
    rw [hNH.star_dotProduct_mulVec_comm d e, RCLike.star_def, RCLike.conj_re]
    refine (RCLike.re_le_norm _).trans ?_
    calc _ ≤ D * (τ * E) := hCS
      _ = τ * D * E := by ring
  rw [hwy, hE2, hexp]
  exact sq_le_mul_sq_sub_two_mul_add_sq hR₁ hcross

/-! ### Theorem 5 -/

/-- The norm of a function $\nu > 0$ of $\mathbf{A}$ is nonnegative. -/
private theorem re_quadForm_cfc_nonneg {A : Matrix n n 𝕜} {ν : ℝ → ℝ}
    (hν : ∀ x ∈ spectrum ℝ A, 0 < ν x) (v : n → 𝕜) :
    0 ≤ RCLike.re (quadForm (cfc ν A) v) :=
  (Matrix.nonneg_iff_posSemidef.mp (cfc_nonneg fun x hx => (hν x hx).le)).re_quadForm_nonneg v

/-- The common core of the Lanczos-FA bounds: if at every nonempty finite set of positive
nodes the interpolation error of $f$ is $c\,\pi\,\varsigma$ on the spectrum, with $\pi$ the
nodal polynomial and $\nu\varsigma$ varying by at most $R > 0$, then Lanczos-FA is within
$(R + 1)^2/(4R)$ of optimal in the squared $\nu(\mathbf{A})$-norm. -/
private theorem re_quadForm_cfc_cfc_mulVec_sub_lanczosFA_le_of_forall_finset
    {A : Matrix n n 𝕜} (hA : A.PosDef) {f ν : ℝ → ℝ} {R : ℝ} (hR₀ : 0 < R)
    (hν : ∀ x ∈ spectrum ℝ A, 0 < ν x)
    (hrem : ∀ S : Finset ℝ, S.Nonempty → (∀ θ ∈ S, 0 < θ) → ∃ (ς : ℝ → ℝ) (c : ℝ),
      (∀ x ∈ spectrum ℝ A, 0 ≤ ς x) ∧
      (∀ x ∈ spectrum ℝ A, ∀ y ∈ spectrum ℝ A, ν x * ς x ≤ R * (ν y * ς y)) ∧
      ∀ x ∈ spectrum ℝ A, f x - (Lagrange.interpolate S id f).eval x =
        c * (Lagrange.nodal S id).eval x * ς x)
    (b : n → 𝕜) {q : ℕ} {y : n → 𝕜} (hy : y ∈ krylovSpace A b q) :
    RCLike.re (quadForm (cfc ν A) (cfc f A *ᵥ b - lanczosFA A f b q)) ≤
      (R + 1) ^ 2 / (4 * R) * RCLike.re (quadForm (cfc ν A) (cfc f A *ᵥ b - y)) := by
  have hF : 1 ≤ (R + 1) ^ 2 / (4 * R) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (R - 1)]
  have hc : ∀ φ : ℝ → ℝ, ContinuousOn φ (spectrum ℝ A) := fun φ =>
    A.finite_real_spectrum.continuousOn φ
  -- a frame of the Krylov space and the Ritz values
  obtain ⟨Q, hQ, hK⟩ := exists_hasOrthonormalCols_range_eq
    (p := Fin (krylovMatrix A b q).rank) (krylovMatrix A b q) (Fintype.card_fin _)
  have hK' : LinearMap.range Q.mulVecLin = krylovSpace A b q := hK
  have hk : (krylovMatrix A b q).rank ≤ q :=
    (Matrix.rank_le_card_width _).trans_eq (Fintype.card_fin q)
  have hinj : Function.Injective Q.mulVec := fun u v h => by
    rw [← hQ.conjTranspose_mulVec_mulVec u, h, hQ.conjTranspose_mulVec_mulVec]
  have hT : (Qᴴ * A * Q).PosDef := hA.conjTranspose_mul_mul_same hinj
  set S := (Finset.range (krylovMatrix A b q).rank).image (eigenvalue (Qᴴ * A * Q))
  have hST : spectrum ℝ (Qᴴ * A * Q) = ↑S := by
    rw [hT.isHermitian.spectrum_eq_image_eigenvalue, Fintype.card_fin, Finset.coe_image,
      Finset.coe_range]
  have hSq : S.card ≤ q := Finset.card_image_le.trans ((Finset.card_range _).trans_le hk)
  have hSpos : ∀ θ ∈ S, 0 < θ := fun θ hθ =>
    hT.spectrum_subset_Ioi (by rw [hST]; exact hθ)
  have hTS : ∀ x ∈ spectrum ℝ (Qᴴ * A * Q), x ∈ S := fun x hx => by
    rw [hST] at hx
    exact hx
  rcases S.eq_empty_or_nonempty with hS0 | hSne
  · -- the Krylov space is zero
    have hr : (krylovMatrix A b q).rank = 0 := by
      simpa [S, Finset.image_eq_empty, Finset.range_eq_empty_iff] using hS0
    have h0 : ∀ v ∈ krylovSpace A b q, v = 0 := fun v hv => by
      rw [← hK'] at hv
      obtain ⟨u, rfl⟩ := hv
      have : IsEmpty (Fin (krylovMatrix A b q).rank) := by rw [hr]; infer_instance
      rw [Subsingleton.elim u 0, map_zero]
    rw [h0 _ (lanczosFA_mem_krylovSpace A f b q), h0 _ hy, sub_zero]
    exact le_mul_of_one_le_left (re_quadForm_cfc_nonneg hν _) hF
  obtain ⟨ς, c, hς, hRς, heq⟩ := hrem S hSne hSpos
  set p := Lagrange.interpolate S id f
  have hp : p.degree < q :=
    (Lagrange.degree_interpolate_lt (r := f) (Set.injOn_id _)).trans_le (by exact_mod_cast hSq)
  have hL : lanczosFA A f b q = aeval A p *ᵥ b :=
    hQ.lanczosFA_eq_aeval_mulVec hA.isHermitian hK' hp fun x hx =>
      Lagrange.eval_interpolate_at_node (v := id) f (Set.injOn_id _) (hTS x hx)
  -- the error polynomial `c π` is orthogonal to the Krylov space
  have hπ : (krylovMatrix A b q)ᴴ *ᵥ (aeval A (c • Lagrange.nodal S id) *ᵥ b) = 0 := by
    have h0 := hQ.conjTranspose_mulVec_aeval_nodal_mulVec_eq_zero hA.isHermitian hK' hST.le hSq
    rw [← forall_mem_range_star_dotProduct_eq_zero_iff] at h0 ⊢
    intro v hv
    rw [← hK] at hv
    rw [map_smul, Matrix.smul_mulVec, dotProduct_smul, h0 v hv, smul_zero]
  have he : cfc f A *ᵥ b - lanczosFA A f b q =
      aeval A (c • Lagrange.nodal S id) *ᵥ (cfc ς A *ᵥ b) := by
    have hA' : IsSelfAdjoint A := hA.isHermitian
    rw [hL, ← Matrix.sub_mulVec, Matrix.mulVec_mulVec, ← cfc_polynomial p A hA',
      ← cfc_polynomial (c • Lagrange.nodal S id) A hA', ← cfc_sub _ _ A (hc _) (hc _),
      ← cfc_mul _ _ A (hc _) (hc _)]
    congr 1
    refine cfc_congr fun x hx => ?_
    rw [heq x hx]
    simp only [eval_smul, smul_eq_mul]
  have hRmax : ∀ x ∈ spectrum ℝ A, ∀ y ∈ spectrum ℝ A,
      ν x * ς x ≤ max R 1 * (ν y * ς y) := fun x hx y hy' =>
    (hRς x hx y hy').trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (mul_nonneg (hν y hy').le (hς y hy')))
  refine (hA.isHermitian.re_quadForm_cfc_sub_le_of_sub_eq_aeval_mulVec (le_max_right R 1) hν hς
    hRmax hπ (lanczosFA_mem_krylovSpace A f b q) he hy).trans
    (mul_le_mul_of_nonneg_right ?_ (re_quadForm_cfc_nonneg hν _))
  rcases le_total 1 R with h1 | h1
  · rw [max_eq_left h1]
  · rw [max_eq_right h1]
    exact le_trans (le_of_eq (by norm_num)) hF

/-- **Lanczos-FA is near-optimal in every norm with a kernel ratio bound**: for positive
definite $\mathbf{A}$, $f$ (or $f(z)/z$) represented by the measure $\mu$, $\nu > 0$ on the
spectrum, $R > 0$ with $\nu(x)(y + t) \le R\,\nu(y)(x + t)$ for all eigenvalues $x, y$ and
$\mu$-almost every $t \ge 0$, and every $\mathbf{y} \in \mathcal{K}_q(\mathbf{A}, \mathbf{b})$,
$$\|f(\mathbf{A})\mathbf{b} -
\mathsf{lanczosFA}(\mathbf{A}, f, \mathbf{b}, q)\|_{\nu(\mathbf{A})}^2
\le \frac{(R + 1)^2}{4R}\,\|f(\mathbf{A})\mathbf{b} - \mathbf{y}\|_{\nu(\mathbf{A})}^2 \,,$$
where $\|\mathbf{x}\|_{\nu(\mathbf{A})}^2 = \mathbf{x}^{\mathsf{H}}\nu(\mathbf{A})\mathbf{x}$.
The remainder of interpolation at the Ritz values is $\pm\pi\varsigma$ with $\varsigma$
represented by a measure $\varrho \ll \mu$ (`HasStieltjesMeasure.exists_sub_eval_interpolate_eq`
or `_of_div`), so the kernel bound passes to $\nu\varsigma$
(`HasStieltjesMeasure.mul_le_mul_of_ae_le`) and the abstract step
`Matrix.IsHermitian.re_quadForm_cfc_sub_le_of_sub_eq_aeval_mulVec` applies. The hypothesis
$R > 0$ is needed only for $\mu = 0$, where the kernel bound is empty (then $f = 0$, and
$R < 0$ would make the right side negative); for $\mu \ne 0$ the bound at $x = y$ forces
$R \ge 1$. [ChenPersson2026, Theorem 5]; there with $R$ the ratio of $\nu\varsigma_m$ at the
eigenvalues, which depends on the Ritz values; here a bound on the kernel over the support of
$\mu$, which a user can check, and
$(R + 1)^2/(4R) = \bigl(\tfrac12(\sqrt R + 1/\sqrt R)\bigr)^2$. -/
theorem _root_.Matrix.PosDef.re_quadForm_cfc_cfc_mulVec_sub_lanczosFA_le_of_hasStieltjesMeasure
    {A : Matrix n n 𝕜} (hA : A.PosDef) {f : ℝ → ℝ} {μ : MeasureTheory.Measure ℝ}
    (hf : HasStieltjesMeasure f μ ∨ HasStieltjesMeasure (fun z => f z / z) μ)
    {ν : ℝ → ℝ} {R : ℝ} (hR₀ : 0 < R) (hν : ∀ x ∈ spectrum ℝ A, 0 < ν x)
    (hR : ∀ x ∈ spectrum ℝ A, ∀ y ∈ spectrum ℝ A, ∀ᵐ t ∂μ, 0 ≤ t →
      ν x * (y + t) ≤ R * (ν y * (x + t)))
    (b : n → 𝕜) {q : ℕ} {y : n → 𝕜} (hy : y ∈ krylovSpace A b q) :
    RCLike.re (quadForm (cfc ν A) (cfc f A *ᵥ b - lanczosFA A f b q)) ≤
      (R + 1) ^ 2 / (4 * R) * RCLike.re (quadForm (cfc ν A) (cfc f A *ᵥ b - y)) := by
  refine re_quadForm_cfc_cfc_mulVec_sub_lanczosFA_le_of_forall_finset hA hR₀ hν
    (fun S hSne hSpos => ?_) b hy
  have hspec : ∀ x ∈ spectrum ℝ A, 0 < x := fun x hx => hA.spectrum_subset_Ioi hx
  have key : ∀ {ς : ℝ → ℝ} {ρ : MeasureTheory.Measure ℝ}, HasStieltjesMeasure ς ρ →
      ρ.AbsolutelyContinuous μ → (∀ x ∈ spectrum ℝ A, 0 ≤ ς x) ∧
        ∀ x ∈ spectrum ℝ A, ∀ y ∈ spectrum ℝ A, ν x * ς x ≤ R * (ν y * ς y) :=
    fun hρ hρμ => ⟨fun x hx => hρ.nonneg (hspec x hx), fun x hx y hy =>
      hρ.mul_le_mul_of_ae_le (hspec x hx) (hspec y hy) (hρμ.ae_le (hR x hx y hy))⟩
  rcases hf with hf | hf
  · obtain ⟨ς, ρ, hρ, hρμ, heq⟩ := hf.exists_sub_eval_interpolate_eq hSpos
    exact ⟨ς, (-1) ^ S.card, (key hρ hρμ).1, (key hρ hρμ).2, fun x hx => heq x (hspec x hx)⟩
  · obtain ⟨ς, ρ, hρ, hρμ, heq⟩ := hf.exists_sub_eval_interpolate_eq_of_div hSne hSpos
    exact ⟨ς, (-1) ^ (S.card + 1), (key hρ hρμ).1, (key hρ hρμ).2,
      fun x hx => heq x (hspec x hx)⟩

/-- **The same with a kernel bound for every $t \ge 0$**, uniform over Stieltjes functions: for
positive definite $\mathbf{A}$, $f$ or $f(z)/z$ Stieltjes, $\nu > 0$ on the spectrum with
$\nu(x)(y + t) \le R\,\nu(y)(x + t)$ for all eigenvalues $x, y$ and all $t \ge 0$,
$$\|f(\mathbf{A})\mathbf{b} -
\mathsf{lanczosFA}(\mathbf{A}, f, \mathbf{b}, q)\|_{\nu(\mathbf{A})}^2
\le \frac{(R + 1)^2}{4R}\,\|f(\mathbf{A})\mathbf{b} - \mathbf{y}\|_{\nu(\mathbf{A})}^2$$
for every $\mathbf{y} \in \mathcal{K}_q(\mathbf{A}, \mathbf{b})$. A corollary of
`Matrix.PosDef.re_quadForm_cfc_cfc_mulVec_sub_lanczosFA_le_of_hasStieltjesMeasure`, which is
sharper for a given $f$. [ChenPersson2026, Theorem 5]. -/
theorem _root_.Matrix.PosDef.re_quadForm_cfc_cfc_mulVec_sub_lanczosFA_le {A : Matrix n n 𝕜}
    (hA : A.PosDef) {f : ℝ → ℝ} (hf : IsStieltjes f ∨ IsStieltjes fun z => f z / z)
    {ν : ℝ → ℝ} {R : ℝ} (hν : ∀ x ∈ spectrum ℝ A, 0 < ν x)
    (hR : ∀ x ∈ spectrum ℝ A, ∀ y ∈ spectrum ℝ A, ∀ t, 0 ≤ t →
      ν x * (y + t) ≤ R * (ν y * (x + t)))
    (b : n → 𝕜) {q : ℕ} {y : n → 𝕜} (hy : y ∈ krylovSpace A b q) :
    RCLike.re (quadForm (cfc ν A) (cfc f A *ᵥ b - lanczosFA A f b q)) ≤
      (R + 1) ^ 2 / (4 * R) * RCLike.re (quadForm (cfc ν A) (cfc f A *ᵥ b - y)) := by
  rcases isEmpty_or_nonempty n with hn | hn
  · simp [quadForm_eq_sum]
  -- `R ≥ 1` from the kernel bound at `x = y`, `t = 0`
  have hx := hA.isHermitian.eigenvalue_mem_spectrum Fintype.card_pos
  have hx0 : 0 < eigenvalue A 0 := hA.spectrum_subset_Ioi hx
  have h := hR _ hx _ hx 0 le_rfl
  have hR₀ : 0 < R := by
    have := mul_pos (hν _ hx) (by linarith : 0 < eigenvalue A 0 + 0)
    nlinarith
  rcases hf with ⟨μ, hμ⟩ | ⟨μ, hμ⟩
  · exact hA.re_quadForm_cfc_cfc_mulVec_sub_lanczosFA_le_of_hasStieltjesMeasure (Or.inl hμ) hR₀
      hν (fun x hx y hy => Filter.Eventually.of_forall fun t ht => hR x hx y hy t ht) b hy
  · exact hA.re_quadForm_cfc_cfc_mulVec_sub_lanczosFA_le_of_hasStieltjesMeasure (Or.inr hμ) hR₀
      hν (fun x hx y hy => Filter.Eventually.of_forall fun t ht => hR x hx y hy t ht) b hy

/-! ### The $\mathbf{A}^\alpha$-norms: Theorem 1 -/

/-- The factor $(R + 1)^2/(4R)$ at $R = \kappa^E$ is
$\bigl(\tfrac12(\kappa^{E/2} + \kappa^{-E/2})\bigr)^2$. -/
private theorem add_one_sq_div_rpow_eq {K : ℝ} (hK : 0 < K) (E : ℝ) :
    (K ^ E + 1) ^ 2 / (4 * K ^ E) = ((K ^ (E / 2) + K ^ (-(E / 2))) / 2) ^ 2 := by
  have hu0 : 0 < K ^ (E / 2) := Real.rpow_pos_of_pos hK _
  have h1 : K ^ E = (K ^ (E / 2)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hK.le]
    norm_num
  rw [h1, Real.rpow_neg hK.le]
  field_simp
  ring

/-- **Optimal near-optimality of Lanczos-FA in the $\mathbf{A}^\alpha$-norms**: for Hermitian
$\mathbf{A}$ with spectrum in $[a, a']$, $0 < a$, $f$ or $f(z)/z$ Stieltjes, real $\alpha$,
$E = \max(\alpha, 1 - \alpha)$ and every $\mathbf{y} \in \mathcal{K}_q(\mathbf{A}, \mathbf{b})$,
$$\|f(\mathbf{A})\mathbf{b} -
\mathsf{lanczosFA}(\mathbf{A}, f, \mathbf{b}, q)\|_{\mathbf{A}^\alpha}^2
\le \Bigl(\frac{(a'/a)^{E/2} + (a'/a)^{-E/2}}{2}\Bigr)^2
\|f(\mathbf{A})\mathbf{b} - \mathbf{y}\|_{\mathbf{A}^\alpha}^2 \,.$$
The kernel ratio of $\nu(x) = x^\alpha$ is `rpow_mul_add_le`. The factor is optimal
[ChenPersson2026, Theorem 2] (stage K2b).
[ChenPersson2026, Theorem 1]; there with $\kappa(\mathbf{A})$ and the unsquared norms, here
for any interval containing the spectrum (the $\kappa$ form is
`Matrix.PosDef.re_quadForm_rpow_cfc_mulVec_sub_lanczosFA_le_pseudoConditionNumber`); it
strengthens [Schweitzer2025, Theorems 3.1 and 4.1].
Result: lanczos-fa-near-optimality -/
theorem _root_.Matrix.IsHermitian.re_quadForm_rpow_cfc_mulVec_sub_lanczosFA_le
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ A ⊆ Set.Icc a a') {f : ℝ → ℝ}
    (hf : IsStieltjes f ∨ IsStieltjes fun z => f z / z) (α : ℝ) (b : n → 𝕜) {q : ℕ}
    {y : n → 𝕜} (hy : y ∈ krylovSpace A b q) :
    RCLike.re (quadForm (A ^ α) (cfc f A *ᵥ b - lanczosFA A f b q)) ≤
      (((a' / a) ^ (max α (1 - α) / 2) + (a' / a) ^ (-(max α (1 - α) / 2))) / 2) ^ 2 *
        RCLike.re (quadForm (A ^ α) (cfc f A *ᵥ b - y)) := by
  rcases isEmpty_or_nonempty n with hn | hn
  · simp [quadForm_eq_sum]
  have hpd : A.PosDef := hA.posDef_iff_eigenvalue_pos.mpr fun k hk =>
    ha.trans_le (hA.spectrum_subset_iff.mp hs k hk).1
  have hx := hs (hA.eigenvalue_mem_spectrum Fintype.card_pos)
  have hK : 0 < a' / a := div_pos (ha.trans_le (hx.1.trans hx.2)) ha
  rw [CFC.rpow_eq_cfc_real hpd.posSemidef.nonneg, ← add_one_sq_div_rpow_eq hK]
  exact hpd.re_quadForm_cfc_cfc_mulVec_sub_lanczosFA_le hf (ν := fun x => x ^ α)
    (fun x hx => Real.rpow_pos_of_pos (hpd.spectrum_subset_Ioi hx) α)
    (fun x hx y hy t ht => rpow_mul_add_le ha (hs hx) (hs hy) ht α) b hy

/-- **The same in the condition number**: for positive definite $\mathbf{A}$ with
$\kappa = \kappa(\mathbf{A})$, $f$ or $f(z)/z$ Stieltjes, real $\alpha$,
$E = \max(\alpha, 1 - \alpha)$ and every $\mathbf{y} \in \mathcal{K}_q(\mathbf{A}, \mathbf{b})$,
$$\|f(\mathbf{A})\mathbf{b} -
\mathsf{lanczosFA}(\mathbf{A}, f, \mathbf{b}, q)\|_{\mathbf{A}^\alpha}^2
\le \Bigl(\frac{\kappa^{E/2} + \kappa^{-E/2}}{2}\Bigr)^2
\|f(\mathbf{A})\mathbf{b} - \mathbf{y}\|_{\mathbf{A}^\alpha}^2 \,.$$
The interval form at $[\lambda_{\min}, \lambda_{\max}]$. [ChenPersson2026, Theorem 1]. -/
theorem _root_.Matrix.PosDef.re_quadForm_rpow_cfc_mulVec_sub_lanczosFA_le_pseudoConditionNumber
    {A : Matrix n n 𝕜} (hA : A.PosDef) {f : ℝ → ℝ}
    (hf : IsStieltjes f ∨ IsStieltjes fun z => f z / z) (α : ℝ) (b : n → 𝕜) {q : ℕ}
    {y : n → 𝕜} (hy : y ∈ krylovSpace A b q) :
    RCLike.re (quadForm (A ^ α) (cfc f A *ᵥ b - lanczosFA A f b q)) ≤
      ((pseudoConditionNumber A ^ (max α (1 - α) / 2) +
          pseudoConditionNumber A ^ (-(max α (1 - α) / 2))) / 2) ^ 2 *
        RCLike.re (quadForm (A ^ α) (cfc f A *ᵥ b - y)) := by
  rcases isEmpty_or_nonempty n with hn | hn
  · simp [quadForm_eq_sum]
  obtain ⟨k, hk⟩ : ∃ k, k + 1 = Fintype.card n := ⟨Fintype.card n - 1, by
    have := Fintype.card_pos (α := n)
    omega⟩
  have hpos : 0 < eigenvalue A k :=
    hA.isHermitian.posDef_iff_eigenvalue_pos.mp hA k (by omega)
  have hs : spectrum ℝ A ⊆ Set.Icc (eigenvalue A k) (eigenvalue A 0) := by
    rw [hA.isHermitian.spectrum_subset_iff]
    intro i hi
    exact ⟨hA.isHermitian.eigenvalue_le_eigenvalue (by omega) (by omega),
      hA.isHermitian.eigenvalue_le_eigenvalue (Nat.zero_le i) hi⟩
  have h := hA.isHermitian.re_quadForm_rpow_cfc_mulVec_sub_lanczosFA_le hpos hs hf α b hy
  rwa [← hA.pseudoConditionNumber_eq hk] at h

/-- The Euclidean form of an $\mathbf{A}^0$-norm bound: from the squared bound with factor
$\bigl(\tfrac12(\kappa^{1/2} + \kappa^{-1/2})\bigr)^2$ to the unsquared one with
$\tfrac12(\sqrt\kappa + 1/\sqrt\kappa)$. -/
private theorem norm_toLp_le_of_re_quadForm_one_le {u v : n → 𝕜} {K : ℝ}
    (hK : Nonempty n → 0 ≤ K)
    (h : RCLike.re (quadForm 1 u) ≤
      ((K ^ (max (0 : ℝ) (1 - 0) / 2) + K ^ (-(max (0 : ℝ) (1 - 0) / 2))) / 2) ^ 2 *
        RCLike.re (quadForm 1 v)) :
    ‖WithLp.toLp 2 u‖ ≤ (Real.sqrt K + (Real.sqrt K)⁻¹) / 2 * ‖WithLp.toLp 2 v‖ := by
  rcases isEmpty_or_nonempty n with hn | hn
  · rw [Subsingleton.elim u 0, Subsingleton.elim v 0, WithLp.toLp_zero, norm_zero, mul_zero]
  have hK0 := hK hn
  have hc : 0 ≤ (Real.sqrt K + (Real.sqrt K)⁻¹) / 2 := by positivity
  rw [quadForm_one, quadForm_one, RCLike.ofReal_re, RCLike.ofReal_re,
    show max (0 : ℝ) (1 - 0) / 2 = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
    Real.rpow_neg hK0, ← Real.sqrt_eq_rpow, ← mul_pow] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h

/-- **Near-optimality in the Euclidean norm**: for Hermitian $\mathbf{A}$ with spectrum in
$[a, a']$, $0 < a$, $f$ or $f(z)/z$ Stieltjes and every
$\mathbf{y} \in \mathcal{K}_q(\mathbf{A}, \mathbf{b})$,
$$\|f(\mathbf{A})\mathbf{b} - \mathsf{lanczosFA}(\mathbf{A}, f, \mathbf{b}, q)\| \le
\frac{\sqrt{a'/a} + 1/\sqrt{a'/a}}{2}\,\|f(\mathbf{A})\mathbf{b} - \mathbf{y}\| \,,$$
the case $\alpha = 0$ ($E = 1$). [ChenPersson2026, Theorem 1].
Result: lanczos-fa-near-optimality -/
theorem _root_.Matrix.IsHermitian.norm_cfc_mulVec_sub_lanczosFA_le_mul_norm_sub
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ A ⊆ Set.Icc a a') {f : ℝ → ℝ}
    (hf : IsStieltjes f ∨ IsStieltjes fun z => f z / z) (b : n → 𝕜) {q : ℕ}
    {y : n → 𝕜} (hy : y ∈ krylovSpace A b q) :
    ‖WithLp.toLp 2 (cfc f A *ᵥ b - lanczosFA A f b q)‖ ≤
      (Real.sqrt (a' / a) + (Real.sqrt (a' / a))⁻¹) / 2 *
        ‖WithLp.toLp 2 (cfc f A *ᵥ b - y)‖ := by
  have hpd : A.PosDef := hA.posDef_iff_eigenvalue_pos.mpr fun k hk =>
    ha.trans_le (hA.spectrum_subset_iff.mp hs k hk).1
  have h := hA.re_quadForm_rpow_cfc_mulVec_sub_lanczosFA_le ha hs hf 0 b hy
  rw [CFC.rpow_zero A hpd.posSemidef.nonneg] at h
  refine norm_toLp_le_of_re_quadForm_one_le (fun hn => ?_) h
  have hx := hs (hA.eigenvalue_mem_spectrum Fintype.card_pos)
  exact div_nonneg (ha.le.trans (hx.1.trans hx.2)) ha.le

/-! ### CG -/

/-- **CG on a shifted system is near-optimal in every $\mathbf{A}^\alpha$-norm**: for Hermitian
$\mathbf{A}$ with spectrum in $[a, a']$, $0 < a$, a shift $s \ge 0$,
$(\mathbf{A} + s\mathbf{I})\mathbf{x}_\star = \mathbf{b}$, a start $\mathbf{x}_0$ with
residual $\mathbf{r}_0 = \mathbf{b} - (\mathbf{A} + s\mathbf{I})\mathbf{x}_0$, real $\alpha$,
$E = \max(\alpha, 1 - \alpha)$ and every $\mathbf{y}$ in the affine Krylov space
$\mathbf{x}_0 + \mathcal{K}_q(\mathbf{A} + s\mathbf{I}, \mathbf{r}_0)$ (which equals
$\mathbf{x}_0 + \mathcal{K}_q(\mathbf{A}, \mathbf{r}_0)$),
$$\|\mathbf{x}_\star -
\mathsf{cgIterate}(\mathbf{A} + s\mathbf{I}, \mathbf{b}, \mathbf{x}_0, q)\|_{\mathbf{A}^\alpha}^2
\le \Bigl(\frac{(a'/a)^{E/2} + (a'/a)^{-E/2}}{2}\Bigr)^2
\|\mathbf{x}_\star - \mathbf{y}\|_{\mathbf{A}^\alpha}^2 \,.$$
Shifted CG from $\mathbf{x}_0$ is $\mathbf{x}_0$ plus Lanczos-FA for $(z + s)^{-1}$ on
$\mathbf{r}_0$ (`Matrix.IsHermitian.lanczosFA_inv_add_eq_cgIterate`), and $(z + s)^{-1}$ is a
Stieltjes function. [ChenPersson2026, Theorem 1] for $f(z) = (z + s)^{-1}$. -/
theorem _root_.Matrix.IsHermitian.re_quadForm_rpow_sub_cgIterate_add_smul_one_le
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a a' : ℝ} (ha : 0 < a)
    (hσ : spectrum ℝ A ⊆ Set.Icc a a') {s : ℝ} (hs : 0 ≤ s) (α : ℝ) {b xs : n → 𝕜}
    (hxs : (A + s • (1 : Matrix n n 𝕜)) *ᵥ xs = b) (x₀ : n → 𝕜) {q : ℕ} {y : n → 𝕜}
    (hy : y ∈ AffineSubspace.mk' x₀
      (krylovSpace (A + s • (1 : Matrix n n 𝕜)) (b - (A + s • (1 : Matrix n n 𝕜)) *ᵥ x₀) q)) :
    RCLike.re (quadForm (A ^ α) (xs - cgIterate (A + s • (1 : Matrix n n 𝕜)) b x₀ q)) ≤
      (((a' / a) ^ (max α (1 - α) / 2) + (a' / a) ^ (-(max α (1 - α) / 2))) / 2) ^ 2 *
        RCLike.re (quadForm (A ^ α) (xs - y)) := by
  have hA' : IsSelfAdjoint A := hA
  have hc : ∀ φ : ℝ → ℝ, ContinuousOn φ (spectrum ℝ A) := fun φ =>
    A.finite_real_spectrum.continuousOn φ
  -- shifted CG is Lanczos-FA for the shifted inverse
  have hcg : cgIterate (A + s • (1 : Matrix n n 𝕜)) b x₀ q =
      x₀ + lanczosFA A (fun x => (x + s)⁻¹) (b - (A + s • (1 : Matrix n n 𝕜)) *ᵥ x₀) q := by
    rw [hA.lanczosFA_inv_add_eq_cgIterate, cgIterate, cgIterate, Matrix.mulVec_zero, sub_zero,
      zero_add]
  have hpos : ∀ x ∈ spectrum ℝ A, 0 < x + s := fun x hx => by
    linarith [ha.trans_le (hσ hx).1]
  have hxs' : xs - x₀ =
      cfc (fun x => (x + s)⁻¹) A *ᵥ (b - (A + s • (1 : Matrix n n 𝕜)) *ᵥ x₀) := by
    have h₁ : cfc (fun x : ℝ => x + s) A = cfc (fun x : ℝ => x) A + algebraMap ℝ _ s :=
      cfc_add_const s (fun x : ℝ => x) A (hc _) hA'
    have hMc : A + s • (1 : Matrix n n 𝕜) = cfc (fun x : ℝ => x + s) A := by
      rw [h₁, cfc_id' ℝ A hA', Algebra.algebraMap_eq_smul_one]
    have h1 : cfc (fun x => (x + s)⁻¹) A * (A + s • (1 : Matrix n n 𝕜)) = 1 := by
      rw [hMc, ← cfc_mul _ _ A (hc _) (hc _), ← cfc_one ℝ A]
      exact cfc_congr fun x hx => inv_mul_cancel₀ (hpos x hx).ne'
    rw [← hxs, ← Matrix.mulVec_sub, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  have hy' : y - x₀ ∈ krylovSpace A (b - (A + s • (1 : Matrix n n 𝕜)) *ᵥ x₀) q := by
    rw [AffineSubspace.mem_mk', vsub_eq_sub, krylovSpace_add_smul_one] at hy
    exact hy
  have h := hA.re_quadForm_rpow_cfc_mulVec_sub_lanczosFA_le ha hσ
    (Or.inl ⟨_, hasStieltjesMeasure_inv_add hs⟩) α _ hy'
  rw [← hxs'] at h
  rw [hcg, show ∀ u v w : n → 𝕜, u - (v + w) = u - v - w from fun u v w => by abel,
    show xs - y = xs - x₀ - (y - x₀) by abel]
  exact h

/-- **CG is near-optimal in every $\mathbf{A}^\alpha$-norm**: for Hermitian $\mathbf{A}$ with
spectrum in $[a, a']$, $0 < a$, $\mathbf{A}\mathbf{x}_\star = \mathbf{b}$, a start
$\mathbf{x}_0$ with $\mathbf{r}_0 = \mathbf{b} - \mathbf{A}\mathbf{x}_0$, real $\alpha$,
$E = \max(\alpha, 1 - \alpha)$ and every
$\mathbf{y} \in \mathbf{x}_0 + \mathcal{K}_q(\mathbf{A}, \mathbf{r}_0)$,
$$\|\mathbf{x}_\star -
\mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q)\|_{\mathbf{A}^\alpha}^2
\le \Bigl(\frac{(a'/a)^{E/2} + (a'/a)^{-E/2}}{2}\Bigr)^2
\|\mathbf{x}_\star - \mathbf{y}\|_{\mathbf{A}^\alpha}^2 \,.$$
At $\alpha = 1$ CG is optimal (`Matrix.PosDef.isMinOn_cgIterate`), so this bound is useful for
$\alpha \ne 1$. [ChenPersson2026, Theorem 1 and (5)]. -/
theorem _root_.Matrix.IsHermitian.re_quadForm_rpow_sub_cgIterate_le
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a a' : ℝ} (ha : 0 < a)
    (hσ : spectrum ℝ A ⊆ Set.Icc a a') (α : ℝ) {b xs : n → 𝕜} (hxs : A *ᵥ xs = b)
    (x₀ : n → 𝕜) {q : ℕ} {y : n → 𝕜}
    (hy : y ∈ AffineSubspace.mk' x₀ (krylovSpace A (b - A *ᵥ x₀) q)) :
    RCLike.re (quadForm (A ^ α) (xs - cgIterate A b x₀ q)) ≤
      (((a' / a) ^ (max α (1 - α) / 2) + (a' / a) ^ (-(max α (1 - α) / 2))) / 2) ^ 2 *
        RCLike.re (quadForm (A ^ α) (xs - y)) := by
  have h0 : A + (0 : ℝ) • (1 : Matrix n n 𝕜) = A := by rw [zero_smul, add_zero]
  have h := hA.re_quadForm_rpow_sub_cgIterate_add_smul_one_le ha hσ le_rfl α
    (b := b) (xs := xs) (by rwa [h0]) x₀ (y := y) (by rwa [h0])
  rwa [h0] at h

/-- **CG in the Euclidean norm**: for Hermitian $\mathbf{A}$ with spectrum in $[a, a']$,
$0 < a$, $\mathbf{A}\mathbf{x}_\star = \mathbf{b}$, a start $\mathbf{x}_0$ and every
$\mathbf{y} \in \mathbf{x}_0 + \mathcal{K}_q(\mathbf{A}, \mathbf{b} - \mathbf{A}\mathbf{x}_0)$,
$$\|\mathbf{x}_\star - \mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q)\| \le
\frac{\sqrt{a'/a} + 1/\sqrt{a'/a}}{2}\,\|\mathbf{x}_\star - \mathbf{y}\| \,,$$
improving the factor $\sqrt{a'/a}$ from $\mathbf{A}$-norm optimality and norm equivalence.
[ChenPersson2026, Remark 3]. -/
theorem _root_.Matrix.IsHermitian.norm_sub_cgIterate_le_mul_norm_sub
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a a' : ℝ} (ha : 0 < a)
    (hσ : spectrum ℝ A ⊆ Set.Icc a a') {b xs : n → 𝕜} (hxs : A *ᵥ xs = b) (x₀ : n → 𝕜)
    {q : ℕ} {y : n → 𝕜} (hy : y ∈ AffineSubspace.mk' x₀ (krylovSpace A (b - A *ᵥ x₀) q)) :
    ‖WithLp.toLp 2 (xs - cgIterate A b x₀ q)‖ ≤
      (Real.sqrt (a' / a) + (Real.sqrt (a' / a))⁻¹) / 2 * ‖WithLp.toLp 2 (xs - y)‖ := by
  have hpd : A.PosDef := hA.posDef_iff_eigenvalue_pos.mpr fun k hk =>
    ha.trans_le (hA.spectrum_subset_iff.mp hσ k hk).1
  have h := hA.re_quadForm_rpow_sub_cgIterate_le ha hσ 0 hxs x₀ hy
  rw [CFC.rpow_zero A hpd.posSemidef.nonneg] at h
  refine norm_toLp_le_of_re_quadForm_one_le (fun hn => ?_) h
  have hx := hσ (hA.eigenvalue_mem_spectrum Fintype.card_pos)
  exact div_nonneg (ha.le.trans (hx.1.trans hx.2)) ha.le

end NLAlib
