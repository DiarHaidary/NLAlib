/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Functions.NearOptimality
public import NLAlib.Matrix.Functions.Polynomial
public import NLAlib.Matrix.Pseudoinverse.ConditionNumber
public import NLAlib.Polynomial.Interpolation.DividedDifference

/-!
# The near-optimality factor of Lanczos-FA cannot be improved

For every positive definite $\mathbf{A}$ with at least $q + 1 \ge 2$ distinct eigenvalues,
every real $\alpha$ and every $\eta \in (0, 1]$ there are a starting vector $\mathbf{b}$ and a
shift $s \ge 0$ for which the Lanczos-FA error for $f(z) = (z + s)^{-1}$ in the
$\mathbf{A}^\alpha$-norm is at least $(1 - \eta)\,\tfrac12(\kappa^{E/2} + \kappa^{-E/2})$
times the error of some, hence of the best, approximation from the Krylov space,
$\kappa = \kappa(\mathbf{A})$, $E = \max(\alpha, 1 - \alpha)$ [ChenPersson2026, Theorem 2].
So the factor of `Matrix.IsHermitian.re_quadForm_rpow_cfc_mulVec_sub_lanczosFA_le` and of
`Matrix.PosDef.re_quadForm_rpow_cfc_mulVec_sub_lanczosFA_le_pseudoConditionNumber` is optimal.
For $\alpha \le 1/2$ the shift is $0$, so the instance is CG: the Euclidean factor
$\tfrac12(\sqrt\kappa + 1/\sqrt\kappa)$ of `Matrix.IsHermitian.norm_sub_cgIterate_le_mul_norm_sub`
is optimal too [ChenPersson2026, Remark 3].

Behind both is one statement for a fixed shift and any norm $\nu(\mathbf{A})$: for any two
eigenvalues $x_1, x_2$, the ratio of squared errors comes arbitrarily close to
$(R + 1)^2/(4R)$, $R = \nu(x_1)(x_2 + s)/(\nu(x_2)(x_1 + s))$, which is the factor of
`Matrix.PosDef.re_quadForm_cfc_cfc_mulVec_sub_lanczosFA_le_of_hasStieltjesMeasure` for the
measure $\delta_s$ when $x_1, x_2$ maximise $R$. So that theorem is optimal for every $\nu$ and
every $s \ge 0$.

The construction: $q + 1$ eigenvalues $T$ containing $x_1, x_2$, and $\mathbf{b}$ with
spectral weights $w$ supported on $T$
(`Matrix.IsHermitian.exists_star_aeval_mulVec_dotProduct_cfc_mulVec_eq_sum`). Lanczos-FA for
$(z + s)^{-1}$ is CG on $\mathbf{A} + s\mathbf{I}$
(`Matrix.IsHermitian.lanczosFA_inv_add_eq_cgIterate`),
whose residual polynomial $\pi$ is orthogonal to the polynomials of degree less than $q$ in the
weights $w$ on $T$; so $w\,\pi$ is a multiple of the nodal weights of $T$
(`exists_eq_mul_nodalWeight`), the paper's Lemma 8 without Ritz values. The best error is a
weighted least-squares distance on $T$ (`isLeast_sum_mul_sq_sub_eval`, the paper's Lemma 9).
For free positive weights $h$ on $T$ this gives the exact ratio [ChenPersson2026, (15)]
$$\frac{\sum_T h\varphi^2\,\sum_T h}{(\sum_T h\varphi)^2} \,, \qquad
\varphi(x) = \frac{\nu(x)}{x + s} \,,$$
and $h = 1/\varphi$ at $x_1, x_2$, $h = \delta$ elsewhere, with $\delta$ explicit, gives the
factor up to $(1 - \eta)^2$. No limit is taken: the paper's two limits ($\delta \to 0$ and
$s \to \infty$ for $\alpha > 1/2$) are explicit choices.

The names carry `inv_add` because the conclusion is about the shifted inverse
$(x + s)^{-1}$ that the witness uses, as in `Matrix.IsHermitian.lanczosFA_inv_add_eq_cgIterate`.

## Main results

* `Matrix.PosDef.exists_inv_add_le_re_quadForm_cfc_cfc_mulVec_sub_lanczosFA`: a fixed shift,
  any $\nu$, any two eigenvalues.
* `Matrix.PosDef.exists_inv_add_le_re_quadForm_rpow_cfc_mulVec_sub_lanczosFA`:
  [ChenPersson2026, Theorem 2].
* `Matrix.PosDef.exists_le_norm_sub_cgIterate`: CG in the Euclidean norm
  [ChenPersson2026, Remark 3].
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder
open Polynomial Finset

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The exact ratio for a prescribed weighting -/

/-- The squared $g(\mathbf{A})$-norm of $r(\mathbf{A})\mathbf{b}$ for $\mathbf{b}$ with spectral
weights $w$ on $T$ (`hb`): $\sum_T w_x\,g(x)\,\lvert r(x) \rvert^2$. -/
private theorem re_quadForm_cfc_aeval_mulVec_eq_sum {A : Matrix n n 𝕜} {T : Finset ℝ}
    {w : ℝ → ℝ} {b : n → 𝕜}
    (hb : ∀ (g : ℝ → ℝ) (p r : 𝕜[X]),
      star (aeval A p *ᵥ b) ⬝ᵥ (cfc g A *ᵥ (aeval A r *ᵥ b)) =
      ∑ x ∈ T, ((w x * g x : ℝ) : 𝕜) * (star (p.eval (x : 𝕜)) * r.eval (x : 𝕜)))
    (g : ℝ → ℝ) (r : 𝕜[X]) :
    RCLike.re (quadForm (cfc g A) (aeval A r *ᵥ b)) =
      ∑ x ∈ T, w x * g x * ‖r.eval (x : 𝕜)‖ ^ 2 := by
  rw [quadForm_def, hb g r r, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [RCLike.star_def, RCLike.conj_mul, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul,
    RCLike.ofReal_re]

/-- A real polynomial mapped to $\Bbbk$ and evaluated at a real point. -/
private theorem eval_map_algebraMap_ofReal (p : ℝ[X]) (x : ℝ) :
    (p.map (algebraMap ℝ 𝕜)).eval (x : 𝕜) = ((p.eval x : ℝ) : 𝕜) := by
  rw [eval_map_algebraMap]
  exact (Polynomial.ofReal_eval p x).symm

/-- **The residual polynomial of shifted CG on $q + 1$ eigenvalues** (the content of
[ChenPersson2026, Lemma 8]): let $\mathbf{A}$ be positive definite and $\mathbf{b}$ have
spectral weights $w > 0$ on $q + 1$ eigenvalues $T$ and none elsewhere (hypothesis `hb`, the
conclusion of `Matrix.IsHermitian.exists_star_aeval_mulVec_dotProduct_cfc_mulVec_eq_sum`), let
$s \ge 0$ and let Lanczos-FA for $(z + s)^{-1}$ be $p(\mathbf{A})\mathbf{b}$ with $\deg p < q$.
Then $\pi = 1 - (X + s)p$ satisfies $w_x\pi(x) = c\,W_x$ on $T$ for some $c \ne 0$, $W$ the
nodal weights of $T$: the Galerkin condition of CG on $\mathbf{A} + s\mathbf{I}$ makes
$w\,\overline{\pi}$ orthogonal to the polynomials of degree less than $q$ on $T$
(`exists_eq_mul_nodalWeight`), and $\pi(-s) = 1$ excludes $c = 0$. -/
private theorem exists_mul_eval_eq_mul_nodalWeight {A : Matrix n n 𝕜} (hA : A.PosDef)
    {T : Finset ℝ} {q : ℕ} (hT : #T = q + 1) {w : ℝ → ℝ}
    (hw : ∀ x ∈ T, 0 < w x) {b : n → 𝕜}
    (hb : ∀ (g : ℝ → ℝ) (p r : 𝕜[X]),
      star (aeval A p *ᵥ b) ⬝ᵥ (cfc g A *ᵥ (aeval A r *ᵥ b)) =
      ∑ x ∈ T, ((w x * g x : ℝ) : 𝕜) * (star (p.eval (x : 𝕜)) * r.eval (x : 𝕜)))
    {s : ℝ} (hs : 0 ≤ s) {p : 𝕜[X]} (hp : p.degree < q)
    (hpL : lanczosFA A (fun x => (x + s)⁻¹) b q = aeval A p *ᵥ b) :
    ∃ c : 𝕜, c ≠ 0 ∧ ∀ x ∈ T, (w x : 𝕜) * (1 - (X + C (s : 𝕜)) * p).eval (x : 𝕜) =
      c * ((Lagrange.nodalWeight T (id : ℝ → ℝ) x : ℝ) : 𝕜) := by
  set M : Matrix n n 𝕜 := A + s • (1 : Matrix n n 𝕜) with hMdef
  set π : 𝕜[X] := 1 - (X + C (s : 𝕜)) * p with hπdef
  have hM : M.PosDef := hA.add_posSemidef (Matrix.PosSemidef.one.smul hs)
  have hMa : aeval A (X + C (s : 𝕜)) = M := by
    rw [map_add, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one, hMdef,
      RCLike.real_smul_eq_coe_smul (K := 𝕜)]
  -- the residual of shifted CG is `π(A) b`, orthogonal to the Krylov space
  have hres : b - M *ᵥ cgIterate M b 0 q = aeval A π *ᵥ b := by
    rw [← hA.isHermitian.lanczosFA_inv_add_eq_cgIterate, hpL, ← hMa, Matrix.mulVec_mulVec,
      ← map_mul, hπdef, map_sub, map_one, Matrix.sub_mulVec, Matrix.one_mulVec]
  have horth : ∀ r : 𝕜[X], r.degree < q → star (aeval A π *ᵥ b) ⬝ᵥ (aeval A r *ᵥ b) = 0 := by
    intro r hr
    have hmem : aeval A r *ᵥ b ∈ krylovSpace M (b - M *ᵥ 0) q := by
      rw [Matrix.mulVec_zero, sub_zero, hMdef, krylovSpace_add_smul_one]
      exact aeval_mulVec_mem_krylovSpace A b hr
    obtain ⟨c, hc⟩ := hmem
    have hG := hM.conjTranspose_krylovMatrix_mulVec_sub_mulVec_cgIterate_eq_zero b 0 q
    rw [hres] at hG
    rw [← hc, Matrix.mulVecLin_apply, Matrix.dotProduct_mulVec,
      ← Matrix.conjTranspose_conjTranspose (krylovMatrix M (b - M *ᵥ 0) q), ← Matrix.star_mulVec,
      hG, star_zero, zero_dotProduct]
  have hz : ∀ r : 𝕜[X], r.degree < q →
      ∑ x ∈ T, (w x : 𝕜) * star (π.eval (x : 𝕜)) * r.eval (x : 𝕜) = 0 := by
    intro r hr
    have h := hb (fun _ => 1) π r
    rw [cfc_const_one ℝ A, Matrix.one_mulVec, horth r hr] at h
    refine Eq.trans (Finset.sum_congr rfl fun x _ => ?_) h.symm
    rw [mul_one, mul_assoc]
  obtain ⟨c, hc⟩ := exists_eq_mul_nodalWeight (v := fun x : ℝ => (x : 𝕜))
    (fun x _ y _ h => RCLike.ofReal_injective h) hT hz
  have hW : ∀ x, Lagrange.nodalWeight T (fun x : ℝ => (x : 𝕜)) x =
      ((Lagrange.nodalWeight T (id : ℝ → ℝ) x : ℝ) : 𝕜) := fun x =>
    nodalWeight_map (algebraMap ℝ 𝕜) T id x
  have hmain : ∀ x ∈ T, (w x : 𝕜) * π.eval (x : 𝕜) =
      star c * ((Lagrange.nodalWeight T (id : ℝ → ℝ) x : ℝ) : 𝕜) := by
    intro x hx
    have h := congrArg star (hc x hx)
    rw [hW, star_mul', star_mul', star_star, RCLike.star_def, RCLike.conj_ofReal,
      RCLike.conj_ofReal] at h
    rw [RCLike.star_def]
    exact h
  refine ⟨star c, fun hc0 => ?_, hmain⟩
  -- `c = 0` would make `π` vanish on the `q + 1` nodes, but `π(-s) = 1`
  have hzero : ∀ x : T, π.eval ((x : ℝ) : 𝕜) = 0 := fun x => by
    have h := hmain x x.2
    rw [hc0, zero_mul] at h
    exact (mul_eq_zero.mp h).resolve_left (RCLike.ofReal_ne_zero.mpr (hw x x.2).ne')
  have hdeg : π.natDegree < Fintype.card T := by
    rw [Fintype.card_coe, hT, Nat.lt_succ_iff]
    rcases eq_or_ne p 0 with hp0 | hp0
    · rw [hπdef, hp0, mul_zero, sub_zero, natDegree_one]
      exact Nat.zero_le q
    · have := (natDegree_lt_iff_degree_lt hp0).mpr hp
      refine (natDegree_sub_le _ _).trans (max_le (by rw [natDegree_one]; exact Nat.zero_le q) ?_)
      refine natDegree_mul_le.trans ?_
      rw [natDegree_X_add_C]
      omega
  have hπ0 : π = 0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero π
    (f := fun x : T => ((x : ℝ) : 𝕜)) (fun x y h => Subtype.ext (RCLike.ofReal_injective h))
    hzero hdeg
  have h1 : π.eval (-(s : 𝕜)) = 1 := by
    rw [hπdef, eval_sub, eval_one, eval_mul, eval_add, eval_X, eval_C, neg_add_cancel, zero_mul,
      sub_zero]
  rw [hπ0, eval_zero] at h1
  exact zero_ne_one h1

/-- **The error of a Krylov vector in spectral weights**: for $\mathbf{b}$ with spectral
weights $w$ on eigenvalues $T$ (`hb`), every $p \in \Bbbk[X]$ has
$\|f(\mathbf{A})\mathbf{b} - p(\mathbf{A})\mathbf{b}\|_{\nu(\mathbf{A})}^2 =
\sum_T w_x\nu(x)\lvert(x + s)^{-1} - p(x)\rvert^2$, $f(z) = (z + s)^{-1}$, since
$f(\mathbf{A}) = L(\mathbf{A})$ for the real interpolant $L$ of $f$ on the spectrum. -/
private theorem re_quadForm_cfc_inv_add_mulVec_sub_aeval_mulVec_eq {A : Matrix n n 𝕜}
    (hA : A.PosDef) {T : Finset ℝ} (hTA : ↑T ⊆ spectrum ℝ A) {w : ℝ → ℝ} {b : n → 𝕜}
    (hb : ∀ (g : ℝ → ℝ) (p r : 𝕜[X]),
      star (aeval A p *ᵥ b) ⬝ᵥ (cfc g A *ᵥ (aeval A r *ᵥ b)) =
      ∑ x ∈ T, ((w x * g x : ℝ) : 𝕜) * (star (p.eval (x : 𝕜)) * r.eval (x : 𝕜)))
    (ν : ℝ → ℝ) (s : ℝ) (p : 𝕜[X]) :
    RCLike.re (quadForm (cfc ν A) (cfc (fun x => (x + s)⁻¹) A *ᵥ b - aeval A p *ᵥ b)) =
      ∑ x ∈ T, w x * ν x * ‖(((x + s)⁻¹ : ℝ) : 𝕜) - p.eval (x : 𝕜)‖ ^ 2 := by
  obtain ⟨L, hL, -⟩ := exists_eval_eq_of_mem_spectrum A A (fun x => (x + s)⁻¹)
  have hf : cfc (fun x => (x + s)⁻¹) A = aeval A (L.map (algebraMap ℝ 𝕜)) := by
    rw [hA.isHermitian.cfc_eq_aeval_of_forall_eval_eq hL, aeval_map_algebraMap]
  rw [hf, ← Matrix.sub_mulVec, ← map_sub, re_quadForm_cfc_aeval_mulVec_eq_sum hb]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [eval_sub, eval_map_algebraMap_ofReal, hL x (hTA hx)]

/-- **The comparison vector**: for $\mathbf{b}$ with spectral weights $w > 0$ on $q + 1$
eigenvalues $T$, $\nu > 0$ on $T$, and $p_0 \in \Bbbk[X]$ with $\deg p_0 < q$ whose error
function is $c$ times a real function $e$ on $T$, some $\mathbf{y} \in \mathcal{K}_q$ has
$\|f(\mathbf{A})\mathbf{b} - \mathbf{y}\|_{\nu(\mathbf{A})}^2 = \lvert c\rvert^2\,
e[T]^2/\sum_T W^2/(w\nu)$: $\mathbf{y} = (p_0 + c\tilde p)(\mathbf{A})\mathbf{b}$ for the
weighted least-squares polynomial $\tilde p$ of `isLeast_sum_mul_sq_sub_eval`. -/
private theorem exists_mem_krylovSpace_re_quadForm_eq {A : Matrix n n 𝕜} (hA : A.PosDef)
    {T : Finset ℝ} (hTA : ↑T ⊆ spectrum ℝ A) {q : ℕ} (hT : #T = q + 1) {w ν : ℝ → ℝ}
    (hw : ∀ x ∈ T, 0 < w x) (hν : ∀ x ∈ T, 0 < ν x) {b : n → 𝕜}
    (hb : ∀ (g : ℝ → ℝ) (p r : 𝕜[X]),
      star (aeval A p *ᵥ b) ⬝ᵥ (cfc g A *ᵥ (aeval A r *ᵥ b)) =
      ∑ x ∈ T, ((w x * g x : ℝ) : 𝕜) * (star (p.eval (x : 𝕜)) * r.eval (x : 𝕜)))
    {s : ℝ} {p₀ : 𝕜[X]} (hp₀ : p₀.degree < q) {c : 𝕜} {e : ℝ → ℝ}
    (he : ∀ x ∈ T, (((x + s)⁻¹ : ℝ) : 𝕜) - p₀.eval (x : 𝕜) = c * (e x : 𝕜)) :
    ∃ y ∈ krylovSpace A b q,
      RCLike.re (quadForm (cfc ν A) (cfc (fun x => (x + s)⁻¹) A *ᵥ b - y)) =
        ‖c‖ ^ 2 * (dividedDifference T id e ^ 2 /
          ∑ x ∈ T, Lagrange.nodalWeight T id x ^ 2 / (w x * ν x)) := by
  obtain ⟨⟨pt, hpt, hpt_eq⟩, -⟩ := isLeast_sum_mul_sq_sub_eval (v := id) (Set.injOn_id _) hT
    (u := fun x => w x * ν x) (fun x hx => mul_pos (hw x hx) (hν x hx)) e
  have hpk : (p₀ + c • pt.map (algebraMap ℝ 𝕜)).degree < q := by
    refine (degree_add_le _ _).trans_lt (max_lt hp₀ ((degree_smul_le _ _).trans_lt ?_))
    rw [degree_map]
    exact hpt
  refine ⟨_, aeval_mulVec_mem_krylovSpace A b hpk, ?_⟩
  rw [re_quadForm_cfc_inv_add_mulVec_sub_aeval_mulVec_eq hA hTA hb ν s, ← hpt_eq,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hdiff : (((x + s)⁻¹ : ℝ) : 𝕜) - (p₀ + c • pt.map (algebraMap ℝ 𝕜)).eval (x : 𝕜) =
      c * ((e x - pt.eval x : ℝ) : 𝕜) := by
    rw [eval_add, eval_smul, eval_map_algebraMap_ofReal, smul_eq_mul, RCLike.ofReal_sub,
      mul_sub, ← he x hx]
    ring
  rw [hdiff, norm_mul, RCLike.norm_ofReal, mul_pow, sq_abs, id]
  ring

/-- **The exact ratio** [ChenPersson2026, (15)]: for positive definite $\mathbf{A}$ with spectrum
$S$, $q + 1$ eigenvalues $T \subseteq S$, $\nu > 0$ on $S$, $s \ge 0$ and weights $h > 0$ on $T$,
there are $\mathbf{b}$ and $C > 0$ with, $\varphi(x) = \nu(x)/(x + s)$,
$\|f(\mathbf{A})\mathbf{b} - \mathsf{lanczosFA}\|_\nu^2 = C\sum_T h\varphi^2$ and some
$\mathbf{y} \in \mathcal{K}_q$ with $\|f(\mathbf{A})\mathbf{b} - \mathbf{y}\|_\nu^2 =
C(\sum_T h\varphi)^2/\sum_T h$. The spectral weights of $\mathbf{b}$ are $W^2/(h\nu)$ on $T$,
$W$ the nodal weights, and $0$ off $T$; $C = \lvert c \rvert^2$ for the constant of
`exists_mul_eval_eq_mul_nodalWeight`. -/
private theorem exists_re_quadForm_eq_mul_sum {A : Matrix n n 𝕜} (hA : A.PosDef)
    {S : Finset ℝ} (hS : spectrum ℝ A = ↑S) {T : Finset ℝ} (hTS : T ⊆ S) {q : ℕ}
    (hT : #T = q + 1) {ν : ℝ → ℝ} (hν : ∀ x ∈ S, 0 < ν x) {s : ℝ} (hs : 0 ≤ s)
    {h : ℝ → ℝ} (hh : ∀ x ∈ T, 0 < h x) :
    ∃ (b : n → 𝕜) (C : ℝ), 0 < C ∧
      RCLike.re (quadForm (cfc ν A)
          (cfc (fun x => (x + s)⁻¹) A *ᵥ b - lanczosFA A (fun x => (x + s)⁻¹) b q)) =
        C * ∑ x ∈ T, h x * (ν x / (x + s)) ^ 2 ∧
      ∃ y ∈ krylovSpace A b q,
        RCLike.re (quadForm (cfc ν A) (cfc (fun x => (x + s)⁻¹) A *ᵥ b - y)) =
          C * (∑ x ∈ T, h x * (ν x / (x + s))) ^ 2 / ∑ x ∈ T, h x := by
  have hTA : ↑T ⊆ spectrum ℝ A := by rw [hS]; exact_mod_cast hTS
  have hpos : ∀ x ∈ T, 0 < x + s := fun x hx => by
    linarith [hA.spectrum_subset_Ioi (hTA hx) |>.out]
  have hνT : ∀ x ∈ T, 0 < ν x := fun x hx => hν x (hTS hx)
  have hW : ∀ x ∈ T, Lagrange.nodalWeight T id x ≠ 0 := fun x hx =>
    Lagrange.nodalWeight_ne_zero (Set.injOn_id _) hx
  set w : ℝ → ℝ := fun x =>
    if x ∈ T then Lagrange.nodalWeight T id x ^ 2 / h x / ν x else 0 with hwdef
  have hwT : ∀ x ∈ T, w x = Lagrange.nodalWeight T id x ^ 2 / h x / ν x := fun x hx => if_pos hx
  have hwpos : ∀ x ∈ T, 0 < w x := fun x hx => by
    have := hW x hx; have := hh x hx; have := hνT x hx
    rw [hwT x hx]; positivity
  obtain ⟨b, hb₀⟩ := hA.isHermitian.exists_star_aeval_mulVec_dotProduct_cfc_mulVec_eq_sum hS
    (w := w) fun x _ => by
      by_cases hxT : x ∈ T
      · exact (hwpos x hxT).le
      · simp only [w, if_neg hxT, le_refl]
  have hb : ∀ (g : ℝ → ℝ) (p r : 𝕜[X]),
      star (aeval A p *ᵥ b) ⬝ᵥ (cfc g A *ᵥ (aeval A r *ᵥ b)) =
      ∑ x ∈ T, ((w x * g x : ℝ) : 𝕜) * (star (p.eval (x : 𝕜)) * r.eval (x : 𝕜)) := by
    intro g p r
    rw [hb₀, ← Finset.sum_subset hTS fun x _ hx => by
      simp only [w, if_neg hx, zero_mul, RCLike.ofReal_zero]]
  obtain ⟨p, hp, hpL⟩ :=
    mem_krylovSpace_iff.mp (lanczosFA_mem_krylovSpace A (fun x => (x + s)⁻¹) b q)
  obtain ⟨c, hc0, hc⟩ := exists_mul_eval_eq_mul_nodalWeight hA hT hwpos hb hs hp hpL.symm
  -- the error function is `c` times `e = h φ / W` on `T`
  have he : ∀ x ∈ T, (((x + s)⁻¹ : ℝ) : 𝕜) - p.eval (x : 𝕜) =
      c * ((h x * (ν x / (x + s)) / Lagrange.nodalWeight T id x : ℝ) : 𝕜) := by
    intro x hx
    have h1 := hc x hx
    rw [hwT x hx, eval_sub, eval_one, eval_mul, eval_add, eval_X, eval_C] at h1
    have hxs : ((x : 𝕜) + (s : 𝕜)) ≠ 0 := by exact_mod_cast (hpos x hx).ne'
    have hW' : ((Lagrange.nodalWeight T id x : ℝ) : 𝕜) ≠ 0 := by exact_mod_cast hW x hx
    have hh' : ((h x : ℝ) : 𝕜) ≠ 0 := by exact_mod_cast (hh x hx).ne'
    have hν' : ((ν x : ℝ) : 𝕜) ≠ 0 := by exact_mod_cast (hνT x hx).ne'
    push_cast at h1 ⊢
    have hw0 : ((Lagrange.nodalWeight T id x : ℝ) : 𝕜) ^ 2 / (h x : 𝕜) / (ν x : 𝕜) ≠ 0 := by
      positivity
    have hY : 1 - ((x : 𝕜) + s) * p.eval (x : 𝕜) =
        c * ((h x : 𝕜) * (ν x : 𝕜) / ((Lagrange.nodalWeight T id x : ℝ) : 𝕜)) := by
      apply mul_left_cancel₀ hw0
      rw [h1]
      field_simp
    calc ((x : 𝕜) + s)⁻¹ - p.eval (x : 𝕜) =
          ((x : 𝕜) + s)⁻¹ * (1 - ((x : 𝕜) + s) * p.eval (x : 𝕜)) := by
          rw [mul_sub, mul_one, ← mul_assoc, inv_mul_cancel₀ hxs, one_mul]
      _ = _ := by rw [hY]; ring
  refine ⟨b, ‖c‖ ^ 2, by positivity, ?_, ?_⟩
  · rw [← hpL, re_quadForm_cfc_inv_add_mulVec_sub_aeval_mulVec_eq hA hTA hb ν s p,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    have := hW x hx; have := hh x hx; have := hνT x hx; have := hpos x hx
    rw [he x hx, norm_mul, RCLike.norm_ofReal, mul_pow, sq_abs, hwT x hx]
    field_simp
  · obtain ⟨y, hy, hyE⟩ := exists_mem_krylovSpace_re_quadForm_eq hA hTA hT hwpos
      (ν := ν) hνT hb hp he
    refine ⟨y, hy, ?_⟩
    have hDD : dividedDifference T id (fun x => h x * (ν x / (x + s)) /
        Lagrange.nodalWeight T id x) = ∑ x ∈ T, h x * (ν x / (x + s)) :=
      Finset.sum_congr rfl fun x hx => mul_div_cancel₀ _ (hW x hx)
    have hden : ∑ x ∈ T, Lagrange.nodalWeight T id x ^ 2 / (w x * ν x) = ∑ x ∈ T, h x :=
      Finset.sum_congr rfl fun x hx => by
        have := hW x hx; have := hh x hx; have := hνT x hx
        rw [hwT x hx]
        field_simp
    rw [hyE, hDD, hden, mul_div_assoc]

/-- **The weighting**: for a finite $T$, two points $x_1 \ne x_2$ of $T$, values
$\varphi > 0$ on $T$ and $0 < \eta \le 1$ there are weights $h > 0$ on $T$ with
$$(1 - \eta)^2\,\frac{(\varphi_1 + \varphi_2)^2}{4\varphi_1\varphi_2}\,
\frac{(\sum_T h\varphi)^2}{\sum_T h} \le \sum_T h\varphi^2 \,:$$
$h = 1/\varphi$ at $x_1, x_2$ and $h = \delta = \eta/(1 + \sum_T\varphi)$ elsewhere, since
$(1 - \eta)(2 + \eta) \le 2$. -/
private theorem exists_mul_sq_div_le_sum {T : Finset ℝ} {x₁ x₂ : ℝ} (hx₁ : x₁ ∈ T)
    (hx₂ : x₂ ∈ T) (hx : x₁ ≠ x₂) {φ : ℝ → ℝ} (hφ : ∀ x ∈ T, 0 < φ x) {η : ℝ} (hη : 0 < η)
    (hη₁ : η ≤ 1) :
    ∃ h : ℝ → ℝ, (∀ x ∈ T, 0 < h x) ∧
      (1 - η) ^ 2 * ((φ x₁ + φ x₂) ^ 2 / (4 * φ x₁ * φ x₂)) *
          ((∑ x ∈ T, h x * φ x) ^ 2 / ∑ x ∈ T, h x) ≤ ∑ x ∈ T, h x * φ x ^ 2 := by
  have hM : 0 ≤ ∑ x ∈ T, φ x := Finset.sum_nonneg fun x hx => (hφ x hx).le
  set δ := η / (1 + ∑ x ∈ T, φ x) with hδdef
  have hδ : 0 < δ := by positivity
  set R := (T.erase x₁).erase x₂
  have hRT : R ⊆ T := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
  set h : ℝ → ℝ := fun x => if x = x₁ then (φ x₁)⁻¹ else if x = x₂ then (φ x₂)⁻¹ else δ
    with hdef
  have h₁ : h x₁ = (φ x₁)⁻¹ := if_pos rfl
  have h₂ : h x₂ = (φ x₂)⁻¹ := by rw [hdef]; simp only [if_neg hx.symm, if_true]
  have hR : ∀ x ∈ R, h x = δ := fun x hxR => by
    obtain ⟨hne₂, hxR'⟩ := Finset.mem_erase.mp hxR
    obtain ⟨hne₁, -⟩ := Finset.mem_erase.mp hxR'
    rw [hdef]; simp only [if_neg hne₁, if_neg hne₂]
  have hsplit : ∀ F : ℝ → ℝ, ∑ x ∈ T, F x = F x₁ + F x₂ + ∑ x ∈ R, F x := fun F => by
    rw [← Finset.add_sum_erase T F hx₁,
      ← Finset.add_sum_erase (T.erase x₁) F (Finset.mem_erase.mpr ⟨hx.symm, hx₂⟩), add_assoc]
  have hφ₁ := hφ x₁ hx₁
  have hφ₂ := hφ x₂ hx₂
  refine ⟨h, fun x hx => ?_, ?_⟩
  · rw [hdef]; dsimp only; split_ifs
    · exact inv_pos.mpr hφ₁
    · exact inv_pos.mpr hφ₂
    · exact hδ
  have hS1 : ∑ x ∈ R, h x * φ x = δ * ∑ x ∈ R, φ x := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x hx => by rw [hR x hx]
  have hS2 : ∑ x ∈ R, h x * φ x ^ 2 = δ * ∑ x ∈ R, φ x ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x hx => by rw [hR x hx]
  have hS0 : ∑ x ∈ R, h x = δ * #R := by
    rw [Finset.sum_congr rfl hR, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hb2 : 0 ≤ ∑ x ∈ R, φ x ^ 2 := Finset.sum_nonneg fun x _ => sq_nonneg _
  have ha : 0 ≤ ∑ x ∈ R, φ x := Finset.sum_nonneg fun x hx => (hφ x (hRT hx)).le
  have haM : ∑ x ∈ R, φ x ≤ ∑ x ∈ T, φ x :=
    Finset.sum_le_sum_of_subset_of_nonneg hRT fun x hx _ => (hφ x hx).le
  have hδa : δ * ∑ x ∈ R, φ x ≤ η := by
    rw [hδdef, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  rw [hsplit (fun x => h x * φ x ^ 2), hsplit (fun x => h x * φ x), hsplit h, hS1, hS2, hS0,
    h₁, h₂, inv_mul_cancel₀ hφ₁.ne', inv_mul_cancel₀ hφ₂.ne']
  have hq : (1 - η) * (2 + η) ≤ 2 := by nlinarith
  calc (1 - η) ^ 2 * ((φ x₁ + φ x₂) ^ 2 / (4 * φ x₁ * φ x₂)) *
          ((1 + 1 + δ * ∑ x ∈ R, φ x) ^ 2 / ((φ x₁)⁻¹ + (φ x₂)⁻¹ + δ * #R))
      ≤ (1 - η) ^ 2 * ((φ x₁ + φ x₂) ^ 2 / (4 * φ x₁ * φ x₂)) *
          ((2 + η) ^ 2 / ((φ x₁)⁻¹ + (φ x₂)⁻¹)) := by
        have hδa₀ := mul_nonneg hδ.le ha
        have hδR := mul_nonneg hδ.le (Nat.cast_nonneg (α := ℝ) #R)
        refine mul_le_mul_of_nonneg_left (div_le_div₀ (sq_nonneg _)
          (pow_le_pow_left₀ (by linarith) (by linarith) 2) (by positivity) (by linarith))
          (by positivity)
    _ = ((1 - η) * (2 + η)) ^ 2 / 4 * (φ x₁ + φ x₂) := by
        field_simp
        ring
    _ ≤ 2 ^ 2 / 4 * (φ x₁ + φ x₂) := by gcongr
    _ ≤ (φ x₁)⁻¹ * φ x₁ ^ 2 + (φ x₂)⁻¹ * φ x₂ ^ 2 + δ * ∑ x ∈ R, φ x ^ 2 := by
        have e₁ : (φ x₁)⁻¹ * φ x₁ ^ 2 = φ x₁ := by field_simp
        have e₂ : (φ x₂)⁻¹ * φ x₂ ^ 2 = φ x₂ := by field_simp
        rw [e₁, e₂]
        nlinarith [mul_nonneg hδ.le hb2]

/-! ### A fixed shift and any norm -/

/-- **The factor $(R + 1)^2/(4R)$ is attained for a shifted inverse**: for positive definite
$\mathbf{A}$ with at least $q + 1 \ge 2$ distinct eigenvalues, $\nu > 0$ on the spectrum, a shift
$s \ge 0$, any two eigenvalues $x_1, x_2$ and $0 < \eta \le 1$, there is $\mathbf{b}$ such that,
for $f(z) = (z + s)^{-1}$, the Lanczos-FA error $\mathbf{e} = f(\mathbf{A})\mathbf{b} -
\mathsf{lanczosFA}(\mathbf{A}, f, \mathbf{b}, q)$ is nonzero and some
$\mathbf{y} \in \mathcal{K}_q(\mathbf{A}, \mathbf{b})$ has
$$(1 - \eta)^2\,\frac{(R + 1)^2}{4R}\,\|f(\mathbf{A})\mathbf{b} - \mathbf{y}\|_{\nu(\mathbf{A})}^2
\le \|\mathbf{e}\|_{\nu(\mathbf{A})}^2 \,, \qquad
R = \frac{\nu(x_1)(x_2 + s)}{\nu(x_2)(x_1 + s)} \,,$$
written in the statement as
$(\nu(x_1)(x_2 + s) + \nu(x_2)(x_1 + s))^2/(4\,\nu(x_1)(x_2 + s)\,\nu(x_2)(x_1 + s))$.
For the pair maximising $R$ this is the factor of
`Matrix.PosDef.re_quadForm_cfc_cfc_mulVec_sub_lanczosFA_le_of_hasStieltjesMeasure` for
$\mu = \delta_s$: the near-optimality factor cannot be improved, for any $\nu$ and any $s$.
The vector $\mathbf{b}$ lives on $q + 1$ eigenvalues containing $x_1, x_2$, with spectral
weights for which the error ratio is [ChenPersson2026, (15)].
[ChenPersson2026, proof of Theorem 2]; the method is Greenbaum's [Greenbaum1979].
Result: lanczos-fa-near-optimality-lower-bound -/
theorem _root_.Matrix.PosDef.exists_inv_add_le_re_quadForm_cfc_cfc_mulVec_sub_lanczosFA
    {A : Matrix n n 𝕜} (hA : A.PosDef) {q : ℕ} (hq : 0 < q)
    (hcard : q + 1 ≤ (spectrum ℝ A).ncard) {ν : ℝ → ℝ} (hν : ∀ x ∈ spectrum ℝ A, 0 < ν x)
    {s : ℝ} (hs : 0 ≤ s) {x₁ x₂ : ℝ} (hx₁ : x₁ ∈ spectrum ℝ A) (hx₂ : x₂ ∈ spectrum ℝ A)
    {η : ℝ} (hη : 0 < η) (hη₁ : η ≤ 1) :
    ∃ b : n → 𝕜,
      0 < RCLike.re (quadForm (cfc ν A)
        (cfc (fun x => (x + s)⁻¹) A *ᵥ b - lanczosFA A (fun x => (x + s)⁻¹) b q)) ∧
      ∃ y ∈ krylovSpace A b q,
        (1 - η) ^ 2 * ((ν x₁ * (x₂ + s) + ν x₂ * (x₁ + s)) ^ 2 /
            (4 * (ν x₁ * (x₂ + s)) * (ν x₂ * (x₁ + s)))) *
          RCLike.re (quadForm (cfc ν A) (cfc (fun x => (x + s)⁻¹) A *ᵥ b - y)) ≤
        RCLike.re (quadForm (cfc ν A)
          (cfc (fun x => (x + s)⁻¹) A *ᵥ b - lanczosFA A (fun x => (x + s)⁻¹) b q)) := by
  obtain ⟨S, hS⟩ := A.finite_real_spectrum.exists_finset_coe
  rw [← hS, Set.ncard_coe_finset] at hcard
  rw [← hS, Finset.mem_coe] at hx₁ hx₂
  have hνS : ∀ x ∈ S, 0 < ν x := fun x hx => hν x (by rw [← hS]; exact hx)
  have hxs : ∀ x ∈ S, 0 < x + s := fun x hx => by
    linarith [(hA.spectrum_subset_Ioi (show x ∈ spectrum ℝ A by rw [← hS]; exact hx)).out]
  obtain ⟨T, hT12, hTS, hT⟩ := Finset.exists_subsuperset_card_eq (s := {x₁, x₂}) (t := S)
    (n := q + 1) (Finset.insert_subset hx₁ (Finset.singleton_subset_iff.mpr hx₂))
    ((Finset.card_le_two).trans (by omega)) hcard
  have hxT₁ : x₁ ∈ T := hT12 (Finset.mem_insert_self _ _)
  have hxT₂ : x₂ ∈ T := hT12 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hφ : ∀ x ∈ T, 0 < ν x / (x + s) := fun x hx => div_pos (hνS x (hTS hx)) (hxs x (hTS hx))
  have hfac : (ν x₁ * (x₂ + s) + ν x₂ * (x₁ + s)) ^ 2 /
      (4 * (ν x₁ * (x₂ + s)) * (ν x₂ * (x₁ + s))) =
      (ν x₁ / (x₁ + s) + ν x₂ / (x₂ + s)) ^ 2 /
        (4 * (ν x₁ / (x₁ + s)) * (ν x₂ / (x₂ + s))) := by
    have := hxs x₁ hx₁; have := hxs x₂ hx₂; have := hνS x₁ hx₁; have := hνS x₂ hx₂
    field_simp
  rcases eq_or_ne x₁ x₂ with rfl | hx
  · -- the factor is `1`; any `b` from the exact ratio, `y` the Lanczos-FA vector
    obtain ⟨b, C, hC, hE, -⟩ := exists_re_quadForm_eq_mul_sum hA hS.symm hTS hT hνS hs
      (h := fun _ => 1) fun _ _ => one_pos
    have hEpos : 0 < RCLike.re (quadForm (cfc ν A)
        (cfc (fun x => (x + s)⁻¹) A *ᵥ b - lanczosFA A (fun x => (x + s)⁻¹) b q)) := by
      rw [hE]
      exact mul_pos hC (Finset.sum_pos (fun x hx => by have := hφ x hx; positivity)
        ⟨x₁, hxT₁⟩)
    refine ⟨b, hEpos, _, lanczosFA_mem_krylovSpace A (fun x => (x + s)⁻¹) b q, ?_⟩
    have h1 : (ν x₁ * (x₁ + s) + ν x₁ * (x₁ + s)) ^ 2 /
        (4 * (ν x₁ * (x₁ + s)) * (ν x₁ * (x₁ + s))) = 1 := by
      have := hxs x₁ hx₁; have := hνS x₁ hx₁
      field_simp
      ring
    rw [h1, mul_one]
    exact mul_le_of_le_one_left hEpos.le (pow_le_one₀ (by linarith) (by linarith))
  · obtain ⟨h, hh, hineq⟩ := exists_mul_sq_div_le_sum hxT₁ hxT₂ hx hφ hη hη₁
    obtain ⟨b, C, hC, hE, y, hy, hyE⟩ := exists_re_quadForm_eq_mul_sum hA hS.symm hTS hT hνS hs hh
    refine ⟨b, ?_, y, hy, ?_⟩
    · rw [hE]
      exact mul_pos hC (Finset.sum_pos (fun x hx => by
        have := hφ x hx; have := hh x hx; positivity) ⟨x₁, hxT₁⟩)
    · rw [hE, hyE, hfac, mul_div_assoc]
      calc _ = C * ((1 - η) ^ 2 * ((ν x₁ / (x₁ + s) + ν x₂ / (x₂ + s)) ^ 2 /
              (4 * (ν x₁ / (x₁ + s)) * (ν x₂ / (x₂ + s)))) *
              ((∑ x ∈ T, h x * (ν x / (x + s))) ^ 2 / ∑ x ∈ T, h x)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hineq hC.le

/-! ### The $\mathbf{A}^\alpha$-norms: the near-optimality factor cannot be improved -/

/-- The factor $(P + Q)^2/(4PQ)$ when $Q/P = tK^E$, $0 < t \le 1$: at least
$t\,\bigl(\tfrac12(K^{E/2} + K^{-E/2})\bigr)^2$. -/
private theorem mul_sq_rpow_add_rpow_neg_le {K E t P Q : ℝ} (hK : 0 < K) (ht : 0 < t)
    (ht₁ : t ≤ 1) (hP : 0 < P) (hPQ : Q = t * K ^ E * P) :
    t * ((K ^ (E / 2) + K ^ (-(E / 2))) / 2) ^ 2 ≤ (P + Q) ^ 2 / (4 * P * Q) := by
  have hu : 0 < K ^ (E / 2) := Real.rpow_pos_of_pos hK _
  have hKE : K ^ E = (K ^ (E / 2)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hK.le]
    norm_num
  rw [Real.rpow_neg hK.le, hPQ, hKE]
  set u := K ^ (E / 2)
  rw [le_div_iff₀ (by positivity)]
  have key : t * (u ^ 2 + 1) ≤ 1 + t * u ^ 2 := by nlinarith
  calc t * ((u + u⁻¹) / 2) ^ 2 * (4 * P * (t * u ^ 2 * P)) = P ^ 2 * (t * (u ^ 2 + 1)) ^ 2 := by
        field_simp
        ring
    _ ≤ P ^ 2 * (1 + t * u ^ 2) ^ 2 := by gcongr
    _ = (P + t * u ^ 2 * P) ^ 2 := by ring

/-- **The shift for the $\mathbf{A}^\alpha$-norm**: for $0 < a < a'$, real $\alpha$,
$E = \max(\alpha, 1 - \alpha)$, $\kappa = a'/a$ and $0 < \theta < 1$ there is $s \ge 0$ with,
$\varphi(x) = x^\alpha/(x + s)$,
$$\theta\Bigl(\frac{\kappa^{E/2} + \kappa^{-E/2}}{2}\Bigr)^2 \le
\frac{(\varphi(a) + \varphi(a'))^2}{4\varphi(a)\varphi(a')} \,:$$
$s = 0$ if $\alpha \le 1/2$ (then $\varphi(a)/\varphi(a') = \kappa^E$), and
$s = a'/(1 - \theta)$ if $\alpha > 1/2$ (then $\varphi(a')/\varphi(a) =
\kappa^\alpha(a + s)/(a' + s)$ with $\theta \le (a + s)/(a' + s) \le 1$). -/
private theorem exists_mul_sq_le_rpow {a a' : ℝ} (ha : 0 < a) (haa : a < a') (α : ℝ) {θ : ℝ}
    (hθ : 0 < θ) (hθ₁ : θ < 1) :
    ∃ s : ℝ, 0 ≤ s ∧
      θ * (((a' / a) ^ (max α (1 - α) / 2) + (a' / a) ^ (-(max α (1 - α) / 2))) / 2) ^ 2 ≤
        (a ^ α * (a' + s) + a' ^ α * (a + s)) ^ 2 /
          (4 * (a ^ α * (a' + s)) * (a' ^ α * (a + s))) := by
  have ha' : 0 < a' := ha.trans haa
  have hK : 0 < a' / a := div_pos ha' ha
  have hpa : 0 < a ^ α := Real.rpow_pos_of_pos ha α
  have hpa' : 0 < a' ^ α := Real.rpow_pos_of_pos ha' α
  have hX : 0 ≤ (((a' / a) ^ (max α (1 - α) / 2) + (a' / a) ^ (-(max α (1 - α) / 2))) / 2) ^ 2 :=
    sq_nonneg _
  rcases le_or_gt α (1 / 2) with hα | hα
  · refine ⟨0, le_rfl, ?_⟩
    rw [max_eq_right (by linarith)]
    have h := mul_sq_rpow_add_rpow_neg_le hK one_pos le_rfl (E := 1 - α)
      (P := a' ^ α * (a + 0)) (Q := a ^ α * (a' + 0)) (by positivity) (by
        rw [Real.div_rpow ha'.le ha.le, Real.rpow_sub ha', Real.rpow_sub ha, Real.rpow_one,
          Real.rpow_one]
        field_simp
        ring)
    rw [max_eq_right (by linarith)] at hX
    calc _ ≤ 1 * (((a' / a) ^ ((1 - α) / 2) + (a' / a) ^ (-((1 - α) / 2))) / 2) ^ 2 :=
          mul_le_mul_of_nonneg_right hθ₁.le hX
      _ ≤ _ := h.trans_eq (by ring)
  · set s := a' / (1 - θ) with hsdef
    have hs : 0 ≤ s := div_nonneg ha'.le (by linarith)
    have h1θ : 1 - θ ≠ 0 := by linarith
    have hs1 : (1 - θ) * s = a' := by rw [hsdef]; field_simp
    refine ⟨s, hs, ?_⟩
    rw [max_eq_left (by linarith)]
    rw [max_eq_left (by linarith)] at hX
    have ht : 0 < (a + s) / (a' + s) := by positivity
    have ht₁ : (a + s) / (a' + s) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    have hθt : θ ≤ (a + s) / (a' + s) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have h := mul_sq_rpow_add_rpow_neg_le hK ht ht₁ (E := α) (P := a ^ α * (a' + s))
      (Q := a' ^ α * (a + s)) (by positivity) (by
        rw [Real.div_rpow ha'.le ha.le]
        field_simp)
    exact (mul_le_mul_of_nonneg_right hθt hX).trans h

/-- The extreme eigenvalues of a positive definite matrix with two distinct eigenvalues:
$0 < \lambda_{\min} < \lambda_{\max}$ and $\kappa(\mathbf{A}) = \lambda_{\max}/\lambda_{\min}$. -/
private theorem exists_mem_spectrum_lt_pseudoConditionNumber_eq {A : Matrix n n 𝕜}
    (hA : A.PosDef) (hcard : 2 ≤ (spectrum ℝ A).ncard) :
    ∃ a a' : ℝ, a ∈ spectrum ℝ A ∧ a' ∈ spectrum ℝ A ∧ 0 < a ∧ a < a' ∧
      pseudoConditionNumber A = a' / a := by
  obtain ⟨x, hx⟩ := Set.nonempty_of_ncard_ne_zero (by omega : (spectrum ℝ A).ncard ≠ 0)
  have : Nonempty n := by
    rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, -⟩ := hx
    exact ⟨i⟩
  obtain ⟨k, hk⟩ : ∃ k, k + 1 = Fintype.card n := ⟨Fintype.card n - 1, by
    have := Fintype.card_pos (α := n)
    omega⟩
  have hpos : 0 < eigenvalue A k :=
    hA.isHermitian.posDef_iff_eigenvalue_pos.mp hA k (by omega)
  have hsub : spectrum ℝ A ⊆ Set.Icc (eigenvalue A k) (eigenvalue A 0) := by
    rw [hA.isHermitian.spectrum_subset_iff]
    intro i hi
    exact ⟨hA.isHermitian.eigenvalue_le_eigenvalue (by omega) (by omega),
      hA.isHermitian.eigenvalue_le_eigenvalue (Nat.zero_le i) hi⟩
  refine ⟨eigenvalue A k, eigenvalue A 0, hA.isHermitian.eigenvalue_mem_spectrum (by omega),
    hA.isHermitian.eigenvalue_mem_spectrum (by omega), hpos,
    lt_of_le_of_ne (hA.isHermitian.eigenvalue_le_eigenvalue (Nat.zero_le k) (by omega))
      fun heq => ?_, hA.pseudoConditionNumber_eq hk⟩
  rw [← heq, Set.Icc_self] at hsub
  have := (Set.ncard_le_ncard hsub (Set.finite_singleton _)).trans_eq (Set.ncard_singleton _)
  omega

/-- **The near-optimality factor cannot be improved**: for positive definite $\mathbf{A}$ with
at least $q + 1 \ge 2$ distinct eigenvalues (`q + 1 ≤ (spectrum ℝ A).ncard`), real $\alpha$,
$E = \max(\alpha, 1 - \alpha)$, $\kappa = \kappa(\mathbf{A})$ and $0 < \eta \le 1$, there are
$\mathbf{b}$ and $s \ge 0$ such that, for $f(z) = (z + s)^{-1}$, the Lanczos-FA error is
nonzero and some $\mathbf{y} \in \mathcal{K}_q(\mathbf{A}, \mathbf{b})$ has
$$(1 - \eta)^2\Bigl(\frac{\kappa^{E/2} + \kappa^{-E/2}}{2}\Bigr)^2
\|f(\mathbf{A})\mathbf{b} - \mathbf{y}\|_{\mathbf{A}^\alpha}^2 \le
\|f(\mathbf{A})\mathbf{b} -
\mathsf{lanczosFA}(\mathbf{A}, f, \mathbf{b}, q)\|_{\mathbf{A}^\alpha}^2 \,.$$
So the factor of
`Matrix.PosDef.re_quadForm_rpow_cfc_mulVec_sub_lanczosFA_le_pseudoConditionNumber` is optimal.
For $\alpha \le 1/2$ the shift is $0$, so the instance is CG. The positive error
excludes the trivial instances, and "some $\mathbf{y}$" is the bound against the best
approximation. The paper's $\kappa > 1$ follows from two distinct positive eigenvalues; the
instance is that of `Matrix.PosDef.exists_inv_add_le_re_quadForm_cfc_cfc_mulVec_sub_lanczosFA`
at the extreme eigenvalues with $\nu(x) = x^\alpha$.
[ChenPersson2026, Theorem 2]; there "a Stieltjes function", here the shifted inverse the
proof uses.
Result: lanczos-fa-near-optimality-lower-bound -/
theorem _root_.Matrix.PosDef.exists_inv_add_le_re_quadForm_rpow_cfc_mulVec_sub_lanczosFA
    {A : Matrix n n 𝕜} (hA : A.PosDef) {q : ℕ} (hq : 0 < q)
    (hcard : q + 1 ≤ (spectrum ℝ A).ncard) (α : ℝ) {η : ℝ} (hη : 0 < η) (hη₁ : η ≤ 1) :
    ∃ (b : n → 𝕜) (s : ℝ), 0 ≤ s ∧
      0 < RCLike.re (quadForm (A ^ α)
        (cfc (fun x => (x + s)⁻¹) A *ᵥ b - lanczosFA A (fun x => (x + s)⁻¹) b q)) ∧
      ∃ y ∈ krylovSpace A b q,
        ((1 - η) * ((pseudoConditionNumber A ^ (max α (1 - α) / 2) +
            pseudoConditionNumber A ^ (-(max α (1 - α) / 2))) / 2)) ^ 2 *
          RCLike.re (quadForm (A ^ α) (cfc (fun x => (x + s)⁻¹) A *ᵥ b - y)) ≤
        RCLike.re (quadForm (A ^ α)
          (cfc (fun x => (x + s)⁻¹) A *ᵥ b - lanczosFA A (fun x => (x + s)⁻¹) b q)) := by
  obtain ⟨a, a', ha, ha', ha0, haa, hκ⟩ :=
    exists_mem_spectrum_lt_pseudoConditionNumber_eq hA (by omega)
  obtain ⟨s, hs, hsle⟩ := exists_mul_sq_le_rpow ha0 haa α (θ := (1 - η / 2) ^ 2)
    (by nlinarith) (by nlinarith)
  have hν : ∀ x ∈ spectrum ℝ A, 0 < (fun x : ℝ => x ^ α) x := fun x hx =>
    Real.rpow_pos_of_pos (hA.spectrum_subset_Ioi hx) α
  obtain ⟨b, hpos, y, hy, hle⟩ :=
    hA.exists_inv_add_le_re_quadForm_cfc_cfc_mulVec_sub_lanczosFA (𝕜 := 𝕜) hq hcard hν hs ha
      ha' (η := η / 2) (half_pos hη) (by linarith)
  rw [CFC.rpow_eq_cfc_real hA.posSemidef.nonneg]
  refine ⟨b, s, hs, hpos, y, hy, le_trans ?_ hle⟩
  have hEy : 0 ≤ RCLike.re (quadForm (cfc (fun x : ℝ => x ^ α) A)
      (cfc (fun x => (x + s)⁻¹) A *ᵥ b - y)) :=
    (Matrix.nonneg_iff_posSemidef.mp (cfc_nonneg fun x hx => (hν x hx).le)).re_quadForm_nonneg _
  rw [hκ]
  refine mul_le_mul_of_nonneg_right ?_ hEy
  have h4 : (1 - η) ^ 2 ≤ (1 - η / 2) ^ 2 * (1 - η / 2) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) (by nlinarith) 2
  rw [mul_pow]
  calc _ ≤ (1 - η / 2) ^ 2 * (1 - η / 2) ^ 2 *
        (((a' / a) ^ (max α (1 - α) / 2) + (a' / a) ^ (-(max α (1 - α) / 2))) / 2) ^ 2 :=
        mul_le_mul_of_nonneg_right h4 (sq_nonneg _)
    _ ≤ _ := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hsle (sq_nonneg _)

/-! ### CG in the Euclidean norm -/

/-- **The Euclidean factor for CG cannot be improved**: for positive definite $\mathbf{A}$ with
at least $q + 1 \ge 2$ distinct eigenvalues, $\kappa = \kappa(\mathbf{A})$ and
$0 < \eta \le 1$, there is $\mathbf{x}_\star$ such that, for $\mathbf{b} =
\mathbf{A}\mathbf{x}_\star$ and the zero start, the CG error is nonzero and some
$\mathbf{y} \in \mathcal{K}_q(\mathbf{A}, \mathbf{b})$ has
$$(1 - \eta)\,\frac{\sqrt\kappa + 1/\sqrt\kappa}{2}\,\|\mathbf{x}_\star - \mathbf{y}\| \le
\|\mathbf{x}_\star - \mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, \mathbf{0}, q)\| \,.$$
So the factor of `Matrix.IsHermitian.norm_sub_cgIterate_le_mul_norm_sub` is optimal. The
instance is that of `Matrix.PosDef.exists_inv_add_le_re_quadForm_cfc_cfc_mulVec_sub_lanczosFA`
with $\nu = 1$, $s = 0$ and the extreme eigenvalues, where Lanczos-FA for $z^{-1}$ is CG
(`Matrix.IsHermitian.lanczosFA_inv_eq_cgIterate`). [ChenPersson2026, Remark 3].
Result: cg-near-optimality-lower-bound -/
theorem _root_.Matrix.PosDef.exists_le_norm_sub_cgIterate {A : Matrix n n 𝕜} (hA : A.PosDef)
    {q : ℕ} (hq : 0 < q) (hcard : q + 1 ≤ (spectrum ℝ A).ncard) {η : ℝ} (hη : 0 < η)
    (hη₁ : η ≤ 1) :
    ∃ xs : n → 𝕜, 0 < ‖WithLp.toLp 2 (xs - cgIterate A (A *ᵥ xs) 0 q)‖ ∧
      ∃ y ∈ krylovSpace A (A *ᵥ xs) q,
        (1 - η) * ((Real.sqrt (pseudoConditionNumber A) +
            (Real.sqrt (pseudoConditionNumber A))⁻¹) / 2) * ‖WithLp.toLp 2 (xs - y)‖ ≤
          ‖WithLp.toLp 2 (xs - cgIterate A (A *ᵥ xs) 0 q)‖ := by
  obtain ⟨a, a', ha, ha', ha0, haa, hκ⟩ :=
    exists_mem_spectrum_lt_pseudoConditionNumber_eq hA (by omega)
  obtain ⟨b, hpos, y, hy, hle⟩ :=
    hA.exists_inv_add_le_re_quadForm_cfc_cfc_mulVec_sub_lanczosFA (𝕜 := 𝕜) hq hcard
      (ν := fun _ => 1) (fun _ _ => one_pos) le_rfl ha ha' hη hη₁
  have h0 : (fun x : ℝ => (x + 0)⁻¹) = fun x => x⁻¹ := funext fun x => by rw [add_zero]
  rw [h0, cfc_const_one ℝ A, hA.isHermitian.lanczosFA_inv_eq_cgIterate, ← hA.inv_eq_cfc,
    quadForm_one, RCLike.ofReal_re] at hpos hle
  rw [quadForm_one, RCLike.ofReal_re] at hle
  have hxs : A *ᵥ (A⁻¹ *ᵥ b) = b := by
    rw [Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit), Matrix.one_mulVec]
  refine ⟨A⁻¹ *ᵥ b, ?_, y, by rwa [hxs], ?_⟩
  · rw [hxs]
    exact lt_of_le_of_ne (norm_nonneg _) fun h =>
      lt_irrefl (0 : ℝ) (by rwa [← h, zero_pow two_ne_zero] at hpos)
  · rw [hxs]
    have hK : ((Real.sqrt (pseudoConditionNumber A) +
        (Real.sqrt (pseudoConditionNumber A))⁻¹) / 2) ^ 2 =
        (1 * (a' + 0) + 1 * (a + 0)) ^ 2 / (4 * (1 * (a' + 0)) * (1 * (a + 0))) := by
      have hK0 : 0 < a' / a := div_pos (ha0.trans haa) ha0
      have hu := Real.sqrt_pos.mpr hK0
      have hsq := Real.sq_sqrt hK0.le
      rw [hκ]
      set u := Real.sqrt (a' / a)
      have ha'eq : a' = u ^ 2 * a := by rw [hsq, div_mul_cancel₀ _ ha0.ne']
      rw [ha'eq]
      field_simp
      ring
    have hc : 0 ≤ (1 - η) * ((Real.sqrt (pseudoConditionNumber A) +
        (Real.sqrt (pseudoConditionNumber A))⁻¹) / 2) := by
      have := Real.sqrt_nonneg (pseudoConditionNumber A)
      exact mul_nonneg (by linarith) (by positivity)
    refine (pow_le_pow_iff_left₀ (mul_nonneg hc (norm_nonneg _)) (norm_nonneg _)
      two_ne_zero).mp ?_
    rw [mul_pow, mul_pow, hK]
    exact hle

end NLAlib
