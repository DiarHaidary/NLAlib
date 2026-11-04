/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.LinearSystems.Richardson
public import NLAlib.Regression.Embedding
public import NLAlib.Sketching.Properties.FixedSubspace

/-!
# Iterative sketching

`NLAlib.iterativeSketching A S ω y x₀ q` is iterative refinement on the normal equations of the
least-squares problem $\min_{\mathbf{x}}\|\mathbf{y} - \mathbf{A}\mathbf{x}\|$, preconditioned by
the sketched Gram matrix $\mathbf{G} = (\mathbf{S}\mathbf{A})^{\mathsf{H}}\mathbf{S}\mathbf{A}$
with step $\omega$:
$\mathbf{x}_{i+1} = \mathbf{x}_i + \omega\mathbf{G}^{+}\mathbf{A}^{\mathsf{H}}(\mathbf{y} -
\mathbf{A}\mathbf{x}_i)$, one sketch for all steps. It is the rectangular Richardson iterate
`NLAlib.richardsonIterate` with $\mathbf{M} = \omega\mathbf{G}^{+}\mathbf{A}^{\mathsf{H}}$, and
Richardson on the normal equations with $\omega\mathbf{G}^{+}$ (`NLAlib.iterativeSketching_eq`).
Step $\omega = 1$ is Epperly's iterative sketching; $\omega = 1 - \varepsilon^2$ is the optimal
damping for an embedding with constants $1 \mp \varepsilon$ in squared norms.

If $\mathbf{S}$ embeds $\operatorname{range}\mathbf{A}$ with constants $a, b$ in squared norms, the
energy error contracts at the rate $\max(\lvert 1 - \omega/b\rvert, \lvert 1 - \omega/a\rvert)$
per step, with no prefactor. Sketch-and-precondition (`NLAlib.sketchAndPrecondition`),
preconditioned CG with the same preconditioner, is never worse
(`Matrix.PosDef.re_quadForm_sub_pcgIterate_le_re_quadForm_sub_richardsonIterate`).
[Epperly2024]; [MartinssonTropp2020].

## Main definitions

* `NLAlib.iterativeSketching`: the iterative sketching iterate with step $\omega$.

## Main results

* `NLAlib.iterativeSketching_eq`: Richardson on the normal equations.
* `NLAlib.IsQR.iterativeSketching_succ`, `NLAlib.IsSVD.iterativeSketching_succ`: the step through
  a factorization of the sketch.
* `NLAlib.IsSubspaceEmbedding.norm_mulVec_sub_iterativeSketching_sq_le`: geometric convergence of
  the energy error for every step.
* `NLAlib.IsSubspaceEmbedding.norm_mulVec_sub_iterativeSketching_one_sq_le`,
  `NLAlib.IsSubspaceEmbedding.norm_mulVec_sub_iterativeSketching_one_sub_sq_sq_le`: undamped and
  optimally damped.
* `NLAlib.IsSubspaceEmbedding.norm_sub_mulVec_iterativeSketching_one_sub_sq_sq_le`: the residual
  from the sketch-and-solve start.
* `NLAlib.HasSubspaceEmbedding.measureReal_norm_mulVec_sub_iterativeSketching_sq_gt_le`,
  `NLAlib.HasSubspaceEmbedding.measureReal_norm_sub_mulVec_iterativeSketching_one_sub_sq_sq_gt_le`:
  the same with a random embedding.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix ComplexOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {k m n : Type*} [Fintype k] [Fintype m] [Fintype n]

/-- The **iterative sketching iterate** with step $\omega$, for
$\mathbf{A} \in \Bbbk^{m \times n}$, a sketch $\mathbf{S} \in \Bbbk^{k \times m}$ and
$\mathbf{y} \in \Bbbk^m$:
$$\mathsf{iterativeSketching}(\mathbf{A}, \mathbf{S}, \omega, \mathbf{y}, \mathbf{x}_0, q) :=
\mathsf{richardsonIterate}(\mathbf{A}, \omega\mathbf{G}^{+}\mathbf{A}^{\mathsf{H}}, \mathbf{y},
\mathbf{x}_0, q)$$
with $\mathbf{G} = (\mathbf{S}\mathbf{A})^{\mathsf{H}}\mathbf{S}\mathbf{A}$, that is
$\mathbf{x}_{i+1} = \mathbf{x}_i + \omega\mathbf{G}^{+}\mathbf{A}^{\mathsf{H}}(\mathbf{y} -
\mathbf{A}\mathbf{x}_i)$. One sketch, fixed for all steps. $\omega = 1$ is Epperly's iterative
sketching; his damped variant is $\omega = (1 - \eta^2)^2/(1 + \eta^2)$ in the unsquared distortion
$\eta$, which is $1 - \varepsilon^2$ for an embedding with constants $1 \mp \varepsilon$ in squared
norms. [Epperly2024, (3.2)], there with $\omega = 1$; [Epperly2024, (B.2)], the damping;
[MartinssonTropp2020, §10.4], there with a fresh sketch at every step. -/
noncomputable def iterativeSketching (A : Matrix m n 𝕜) (S : Matrix k m 𝕜) (ω : ℝ) (y : m → 𝕜)
    (x₀ : n → 𝕜) (q : ℕ) : n → 𝕜 :=
  richardsonIterate A (ω • (pinv ((S * A)ᴴ * (S * A)) * Aᴴ)) y x₀ q

/-- **Iterative sketching is Richardson on the normal equations** with $\omega\mathbf{G}^{+}$,
$\mathbf{G} = (\mathbf{S}\mathbf{A})^{\mathsf{H}}\mathbf{S}\mathbf{A}$:
$$\mathsf{iterativeSketching}(\mathbf{A}, \mathbf{S}, \omega, \mathbf{y}, \mathbf{x}_0, q) =
\mathsf{richardsonIterate}(\mathbf{A}^{\mathsf{H}}\mathbf{A}, \omega\mathbf{G}^{+},
\mathbf{A}^{\mathsf{H}}\mathbf{y}, \mathbf{x}_0, q)\,.$$
[Epperly2024, (3.2)], there as iterative refinement on the normal equations. -/
theorem iterativeSketching_eq (A : Matrix m n 𝕜) (S : Matrix k m 𝕜) (ω : ℝ) (y : m → 𝕜)
    (x₀ : n → 𝕜) (q : ℕ) :
    iterativeSketching A S ω y x₀ q =
      richardsonIterate (Aᴴ * A) (ω • pinv ((S * A)ᴴ * (S * A))) (Aᴴ *ᵥ y) x₀ q := by
  rw [iterativeSketching, ← Matrix.smul_mul, richardsonIterate_mul_conjTranspose]

variable {S : Matrix k m 𝕜} {A : Matrix m n 𝕜} {y : m → 𝕜} {xs x₀ : n → 𝕜}
  {a b ε : ℝ}

/-- **The iterative sketching step through QR**: for a thin QR factorization
$\mathbf{S}\mathbf{A} = \mathbf{Q}\mathbf{R}$ with $\mathbf{R}$ invertible, the iterates
$\mathbf{x}_q = \mathsf{iterativeSketching}(\mathbf{A}, \mathbf{S}, \omega, \mathbf{y},
\mathbf{x}_0, q)$ satisfy
$$\mathbf{x}_{q+1} = \mathbf{x}_q + \omega\mathbf{R}^{-1}\mathbf{R}^{-\mathsf{H}}
\mathbf{A}^{\mathsf{H}}(\mathbf{y} - \mathbf{A}\mathbf{x}_q)\,,$$
two triangular solves per step. [Epperly2024, Algorithm 2], there with $\omega = 1$. -/
theorem IsQR.iterativeSketching_succ [DecidableEq n] [LinearOrder n] {Q : Matrix k n 𝕜}
    {R : Matrix n n 𝕜} (hQR : IsQR (S * A) Q R) (hR : IsUnit R) (ω : ℝ) (y : m → 𝕜)
    (x₀ : n → 𝕜) (q : ℕ) :
    iterativeSketching A S ω y x₀ (q + 1) = iterativeSketching A S ω y x₀ q +
      ω • (R⁻¹ *ᵥ ((R⁻¹)ᴴ *ᵥ (Aᴴ *ᵥ (y - A *ᵥ iterativeSketching A S ω y x₀ q)))) := by
  have hQ : HasOrthonormalCols (S * A * R⁻¹) := hQR.mul_inv_eq hR ▸ hQR.hasOrthonormalCols
  rw [iterativeSketching, iterativeSketching, richardsonIterate_succ]
  congr 1
  rw [hQ.pinv_conjTranspose_mul_self_eq_mul_conjTranspose, Matrix.smul_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

/-- **The iterative sketching step through an SVD**: for a singular value decomposition
$\mathbf{S}\mathbf{A} = \mathbf{U}\mathbf{\Sigma}\mathbf{V}^{\mathsf{H}}$ with square $\mathbf{V}$
and every $\sigma_i > 0$, the iterates
$\mathbf{x}_q = \mathsf{iterativeSketching}(\mathbf{A}, \mathbf{S}, \omega, \mathbf{y},
\mathbf{x}_0, q)$ satisfy
$$\mathbf{x}_{q+1} = \mathbf{x}_q + \omega\mathbf{V}\mathbf{\Sigma}^{-2}\mathbf{V}^{\mathsf{H}}
\mathbf{A}^{\mathsf{H}}(\mathbf{y} - \mathbf{A}\mathbf{x}_q)\,.$$
[EpperlyMeierNakatsukasa2024, §2.1], there the change of variables for any orthogonal
factorization. -/
theorem IsSVD.iterativeSketching_succ [DecidableEq n] {U : Matrix k n 𝕜} {σ : n → ℝ}
    {V : Matrix n n 𝕜} (hSVD : IsSVD (S * A) U σ V) (hσ : ∀ i, 0 < σ i) (ω : ℝ) (y : m → 𝕜)
    (x₀ : n → 𝕜) (q : ℕ) :
    iterativeSketching A S ω y x₀ (q + 1) = iterativeSketching A S ω y x₀ q +
      ω • ((V * Matrix.diagonal (fun i => (((σ i) ^ 2)⁻¹ : 𝕜)) * Vᴴ) *ᵥ
        (Aᴴ *ᵥ (y - A *ᵥ iterativeSketching A S ω y x₀ q))) := by
  have hV := hSVD.hasOrthonormalCols_right
  have hd : ∀ i, ((σ i : ℝ) : 𝕜) ≠ 0 := fun i => RCLike.ofReal_ne_zero.mpr (hσ i).ne'
  have hDD : (Matrix.diagonal fun i => ((σ i : ℝ) : 𝕜)) *
      (Matrix.diagonal fun i => ((σ i)⁻¹ : 𝕜)) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (hd i)
  have hN : HasOrthonormalCols (S * A * (V * Matrix.diagonal fun i => ((σ i)⁻¹ : 𝕜))) := by
    rw [hSVD.eq, show U * Matrix.diagonal (fun i => ((σ i : ℝ) : 𝕜)) * Vᴴ *
        (V * Matrix.diagonal fun i => ((σ i)⁻¹ : 𝕜)) = U * (Matrix.diagonal (fun i =>
          ((σ i : ℝ) : 𝕜)) * (Vᴴ * V) * Matrix.diagonal fun i => ((σ i)⁻¹ : 𝕜)) by
        simp only [Matrix.mul_assoc],
      hV.conjTranspose_mul_self, Matrix.mul_one, hDD, Matrix.mul_one]
    exact hSVD.hasOrthonormalCols_left
  have hE : (V * Matrix.diagonal fun i => ((σ i)⁻¹ : 𝕜)) *
      (V * Matrix.diagonal fun i => ((σ i)⁻¹ : 𝕜))ᴴ =
      V * Matrix.diagonal (fun i => (((σ i) ^ 2)⁻¹ : 𝕜)) * Vᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose,
      show V * Matrix.diagonal (fun i => ((σ i)⁻¹ : 𝕜)) * (Matrix.diagonal (star fun i =>
        ((σ i)⁻¹ : 𝕜)) * Vᴴ) = V * (Matrix.diagonal (fun i => ((σ i)⁻¹ : 𝕜)) *
          Matrix.diagonal (star fun i => ((σ i)⁻¹ : 𝕜))) * Vᴴ by simp only [Matrix.mul_assoc],
      Matrix.diagonal_mul_diagonal]
    congr 3
    funext i
    simp only [Pi.star_apply, RCLike.star_def, map_inv₀, RCLike.conj_ofReal]
    ring
  rw [iterativeSketching, iterativeSketching, richardsonIterate_succ]
  congr 1
  rw [hN.pinv_conjTranspose_mul_self_eq_mul_conjTranspose, hE, Matrix.smul_mulVec,
    Matrix.mulVec_mulVec _ (V * _ * Vᴴ) Aᴴ]

/-! ### Deterministic convergence -/

/-- **Iterative sketching converges geometrically**: if $\mathbf{S}$ is a subspace embedding of
$\operatorname{range}\mathbf{A}$ with constants $a > 0$, $b$ in squared norms
($a\|\mathbf{v}\|^2 \le \|\mathbf{S}\mathbf{v}\|^2 \le b\|\mathbf{v}\|^2$ for
$\mathbf{v} \in \operatorname{range}\mathbf{A}$), $\mathbf{A}$ has full column rank,
$\mathbf{x}_\star$ is a least-squares solution of $\mathbf{A}\mathbf{x} \approx \mathbf{y}$ and
$\omega > 0$, then for every start $\mathbf{x}_0$
$$\|\mathbf{A}(\mathbf{x}_\star - \mathsf{iterativeSketching}(\mathbf{A}, \mathbf{S}, \omega,
\mathbf{y}, \mathbf{x}_0, q))\|^2 \le \bigl(\max(\lvert 1 - \omega/b\rvert,
\lvert 1 - \omega/a\rvert)\bigr)^{2q}\|\mathbf{A}(\mathbf{x}_\star - \mathbf{x}_0)\|^2\,.$$
In Epperly's unsquared distortion $\eta$ ($a = (1 - \eta)^2$, $b = (1 + \eta)^2$) the rate at
$\omega = 1$ is his $g_{\mathrm{IS}} = (2 - \eta)\eta/(1 - \eta)^2$, and at
$\omega = (1 - \eta^2)^2/(1 + \eta^2)$ it is $g_{\mathrm{damp}} = 2\eta/(1 + \eta^2)$.
[Epperly2024, Theorem 5 and Theorem 10]; there through $\|\mathbf{S}\mathbf{A}\cdot\|$ with the
prefactor $(1 + \eta)/(1 - \eta)$, here in the energy norm without one.
Result: iterative-sketching-convergence -/
theorem IsSubspaceEmbedding.norm_mulVec_sub_iterativeSketching_sq_le
    (h : IsSubspaceEmbedding S A a b) (ha : 0 < a) (hA : Function.Injective A.mulVec)
    {ω : ℝ} (hω : 0 < ω) (hxs : IsLeastSquaresSolution A y xs) (x₀ : n → 𝕜) (q : ℕ) :
    ‖WithLp.toLp 2 (A *ᵥ (xs - iterativeSketching A S ω y x₀ q))‖ ^ 2 ≤
      (max |1 - ω / b| |1 - ω / a|) ^ (2 * q) * ‖WithLp.toLp 2 (A *ᵥ (xs - x₀))‖ ^ 2 := by
  classical
  rcases isEmpty_or_nonempty n with hn | hn
  · have h0 : ∀ v : n → 𝕜, v = 0 := fun v => Subsingleton.elim v 0
    rw [h0 (xs - iterativeSketching A S ω y x₀ q), h0 (xs - x₀), Matrix.mulVec_zero,
      WithLp.toLp_zero, norm_zero]
    simp
  have hb := h.pos_right_of_injective ha hA
  have hG : ((S * A)ᴴ * (S * A)).PosDef :=
    posDef_conjTranspose_mul_self_iff.mpr (h.lower.injective_mulVec ha hA)
  have hM : (ω • pinv ((S * A)ᴴ * (S * A))).PosDef := by
    rw [pinv_of_isUnit hG.isUnit]
    exact hG.inv.smul hω
  have hAA : (Aᴴ * A).PosDef := posDef_conjTranspose_mul_self_iff.mpr hA
  have hxs' : (Aᴴ * A) *ᵥ xs = Aᴴ *ᵥ y := by
    rw [← Matrix.mulVec_mulVec]
    exact isLeastSquaresSolution_iff_normal_equations.mp hxs
  have hs : spectrum ℝ ((ω • pinv ((S * A)ᴴ * (S * A))) * (Aᴴ * A)) ⊆
      Set.Icc (ω * b⁻¹) (ω * a⁻¹) := by
    have hs0 := h.spectrum_pinv_mul_subset_Icc ha hA
    rw [smul_mul_assoc, ← Units.val_mk0 hω.ne', ← Units.smul_def, spectrum.unit_smul_eq_smul]
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨h1, h2⟩ := hs0 hz
    simp only [Units.val_mk0, smul_eq_mul, Set.mem_Icc]
    exact ⟨mul_le_mul_of_nonneg_left h1 hω.le, mul_le_mul_of_nonneg_left h2 hω.le⟩
  have hc := hAA.re_quadForm_sub_richardsonIterate_le hM hs hxs' x₀ q
  rw [quadForm_conjTranspose_mul_self, quadForm_conjTranspose_mul_self, RCLike.ofReal_re,
    RCLike.ofReal_re, ← iterativeSketching_eq A S ω y x₀ q, ← div_eq_mul_inv,
    ← div_eq_mul_inv] at hc
  exact hc

/-- **Undamped iterative sketching, $\varepsilon$ form**: if $\mathbf{S}$ is a subspace embedding
of $\operatorname{range}\mathbf{A}$ with constants $1 \mp \varepsilon$ in squared norms
($(1 - \varepsilon)\|\mathbf{v}\|^2 \le \|\mathbf{S}\mathbf{v}\|^2 \le
(1 + \varepsilon)\|\mathbf{v}\|^2$ for $\mathbf{v} \in \operatorname{range}\mathbf{A}$),
$0 < \varepsilon < 1$, $\mathbf{A}$ has full column rank and $\mathbf{x}_\star$ is a
least-squares solution of $\mathbf{A}\mathbf{x} \approx \mathbf{y}$, then for every start
$$\|\mathbf{A}(\mathbf{x}_\star - \mathsf{iterativeSketching}(\mathbf{A}, \mathbf{S}, 1,
\mathbf{y}, \mathbf{x}_0, q))\|^2 \le \Bigl(\frac{\varepsilon}{1 - \varepsilon}\Bigr)^{2q}
\|\mathbf{A}(\mathbf{x}_\star - \mathbf{x}_0)\|^2\,,$$
a contraction for $\varepsilon < 1/2$. [Epperly2024, Theorem 5], there in the unsquared
convention with a prefactor. -/
theorem IsSubspaceEmbedding.norm_mulVec_sub_iterativeSketching_one_sq_le
    (h : IsSubspaceEmbedding S A (1 - ε) (1 + ε)) (hε : 0 < ε) (hε1 : ε < 1)
    (hA : Function.Injective A.mulVec) (hxs : IsLeastSquaresSolution A y xs) (x₀ : n → 𝕜)
    (q : ℕ) :
    ‖WithLp.toLp 2 (A *ᵥ (xs - iterativeSketching A S 1 y x₀ q))‖ ^ 2 ≤
      (ε / (1 - ε)) ^ (2 * q) * ‖WithLp.toLp 2 (A *ᵥ (xs - x₀))‖ ^ 2 := by
  have h1 : 0 < 1 - ε := by linarith
  have hne1 : 1 + ε ≠ 0 := by linarith
  have hne2 : 1 - ε ≠ 0 := h1.ne'
  refine (h.norm_mulVec_sub_iterativeSketching_sq_le (by linarith) hA one_pos hxs x₀ q).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg _)) ?_ _)
      (sq_nonneg _))
  have e1 : 1 - 1 / (1 + ε) = ε / (1 + ε) := by
    field_simp
    ring
  have e2 : 1 - 1 / (1 - ε) = -(ε / (1 - ε)) := by
    field_simp
    ring
  rw [e1, e2, abs_neg, abs_of_nonneg (div_nonneg hε.le (by linarith)),
    abs_of_nonneg (div_nonneg hε.le h1.le)]
  exact max_le (div_le_div_of_nonneg_left hε.le h1 (by linarith)) le_rfl

/-- **Optimally damped iterative sketching, $\varepsilon$ form**: if $\mathbf{S}$ is a subspace
embedding of $\operatorname{range}\mathbf{A}$ with constants $1 \mp \varepsilon$ in squared norms
($(1 - \varepsilon)\|\mathbf{v}\|^2 \le \|\mathbf{S}\mathbf{v}\|^2 \le
(1 + \varepsilon)\|\mathbf{v}\|^2$ for $\mathbf{v} \in \operatorname{range}\mathbf{A}$),
$0 < \varepsilon < 1$, $\mathbf{A}$ has full column rank and $\mathbf{x}_\star$ is a
least-squares solution of $\mathbf{A}\mathbf{x} \approx \mathbf{y}$, then with step
$\omega = 1 - \varepsilon^2$, for every start
$$\|\mathbf{A}(\mathbf{x}_\star - \mathsf{iterativeSketching}(\mathbf{A}, \mathbf{S},
1 - \varepsilon^2, \mathbf{y}, \mathbf{x}_0, q))\|^2 \le \varepsilon^{2q}
\|\mathbf{A}(\mathbf{x}_\star - \mathbf{x}_0)\|^2\,,$$
a contraction for every $\varepsilon < 1$. Sketch-and-precondition is never worse
(`Matrix.PosDef.re_quadForm_sub_pcgIterate_le_re_quadForm_sub_richardsonIterate`).
[Epperly2024, Theorem 10], there in the unsquared convention with a prefactor. -/
theorem IsSubspaceEmbedding.norm_mulVec_sub_iterativeSketching_one_sub_sq_sq_le
    (h : IsSubspaceEmbedding S A (1 - ε) (1 + ε)) (hε : 0 < ε) (hε1 : ε < 1)
    (hA : Function.Injective A.mulVec) (hxs : IsLeastSquaresSolution A y xs) (x₀ : n → 𝕜)
    (q : ℕ) :
    ‖WithLp.toLp 2 (A *ᵥ (xs - iterativeSketching A S (1 - ε ^ 2) y x₀ q))‖ ^ 2 ≤
      ε ^ (2 * q) * ‖WithLp.toLp 2 (A *ᵥ (xs - x₀))‖ ^ 2 := by
  have hne1 : 1 + ε ≠ 0 := by linarith
  have hne2 : 1 - ε ≠ 0 := by linarith
  have hc := h.norm_mulVec_sub_iterativeSketching_sq_le (ω := 1 - ε ^ 2) (by linarith) hA
    (by nlinarith) hxs x₀ q
  have e1 : 1 - (1 - ε ^ 2) / (1 + ε) = ε := by
    field_simp
    ring
  have e2 : 1 - (1 - ε ^ 2) / (1 - ε) = -ε := by
    field_simp
    ring
  rwa [e1, e2, abs_neg, abs_of_pos hε, max_self] at hc

/-- **Damped iterative sketching from the sketch-and-solve start**: if $\mathbf{S}$ is a subspace
embedding of $\operatorname{range}[\mathbf{A}\ \mathbf{y}]$ with constants $1 \mp \varepsilon$ in
squared norms ($(1 - \varepsilon)\|\mathbf{v}\|^2 \le \|\mathbf{S}\mathbf{v}\|^2 \le
(1 + \varepsilon)\|\mathbf{v}\|^2$ on that range), $0 < \varepsilon < 1$, $\mathbf{A}$ has full
column rank and $\mathbf{x}_0$ minimizes $\|\mathbf{S}(\mathbf{A}\mathbf{x} - \mathbf{y})\|$, then
$$\|\mathbf{y} - \mathbf{A}\,\mathsf{iterativeSketching}(\mathbf{A}, \mathbf{S},
1 - \varepsilon^2, \mathbf{y}, \mathbf{x}_0, q)\|^2 \le
\Bigl(1 + \frac{2\varepsilon^{2q+1}}{1 - \varepsilon}\Bigr)
\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{y}\|^2\,,$$
the last factor being the optimal squared residual. [Epperly2024, Theorem 10, (B.4)], there
unsquared with a prefactor. -/
theorem IsSubspaceEmbedding.norm_sub_mulVec_iterativeSketching_one_sub_sq_sq_le [DecidableEq m]
    (h : IsSubspaceEmbedding S (Matrix.fromCols A (Matrix.replicateCol Unit y)) (1 - ε) (1 + ε))
    (hε : 0 < ε) (hε1 : ε < 1) (hA : Function.Injective A.mulVec)
    (hx₀ : IsLeastSquaresSolution (S * A) (S *ᵥ y) x₀) (q : ℕ) :
    ‖WithLp.toLp 2 (y - A *ᵥ iterativeSketching A S (1 - ε ^ 2) y x₀ q)‖ ^ 2 ≤
      (1 + 2 * ε ^ (2 * q + 1) / (1 - ε)) *
        ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2 := by
  have hne2 : 1 - ε ≠ 0 := by linarith
  have h' : IsSubspaceEmbedding S A (1 - ε) (1 + ε) :=
    h.of_range_le (Matrix.range_le_range_fromCols_left A _)
  obtain ⟨xs, hxs⟩ := exists_isLeastSquaresSolution A y
  have hc := h'.norm_mulVec_sub_iterativeSketching_one_sub_sq_sq_le hε hε1 hA hxs x₀ q
  have hss := h.norm_sub_mulVec_sq_le_of_fromCols (by linarith) hx₀
  have hp0 := hxs.norm_sub_mulVec_sq_eq_add x₀
  have hpq := hxs.norm_sub_mulVec_sq_eq_add (iterativeSketching A S (1 - ε ^ 2) y x₀ q)
  rw [hxs.norm_sub_mulVec_eq] at hp0 hpq
  have e1 : (1 + ε) / (1 - ε) = 1 + 2 * ε / (1 - ε) := by
    field_simp
    ring
  rw [e1] at hss
  have hE0 : ‖WithLp.toLp 2 (A *ᵥ (xs - x₀))‖ ^ 2 ≤
      2 * ε / (1 - ε) * ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2 := by linarith
  have hεq : 0 ≤ ε ^ (2 * q) := by positivity
  have h3 : ε ^ (2 * q) * (2 * ε / (1 - ε)) = 2 * ε ^ (2 * q + 1) / (1 - ε) := by
    rw [pow_succ]
    field_simp
  rw [hpq]
  nlinarith [mul_le_mul_of_nonneg_left hE0 hεq]

/-! ### With a random embedding -/

section Random

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {δ : ℝ}

/-- Iterative sketching with a random embedding, any start: if the random sketch $\mathbf{S}$
is a subspace embedding of $\operatorname{range}\mathbf{A}$ with constants $a > 0$, $b$ in squared
norms ($a\|\mathbf{v}\|^2 \le \|\mathbf{S}\mathbf{v}\|^2 \le b\|\mathbf{v}\|^2$ for
$\mathbf{v} \in \operatorname{range}\mathbf{A}$) except with probability $\delta$, $\mathbf{A}$ has
full column rank, $\mathbf{x}_\star$ is a least-squares solution of
$\mathbf{A}\mathbf{x} \approx \mathbf{y}$ and the step is $\omega' > 0$, then for a fixed start
$\mathbf{x}_0$
$$\mathbb{P}\Bigl[\bigl(\max(\lvert 1 - \omega'/b\rvert, \lvert 1 - \omega'/a\rvert)\bigr)^{2q}
\|\mathbf{A}(\mathbf{x}_\star - \mathbf{x}_0)\|^2 < \|\mathbf{A}(\mathbf{x}_\star -
\mathsf{iterativeSketching}(\mathbf{A}, \mathbf{S}, \omega', \mathbf{y}, \mathbf{x}_0,
q))\|^2\Bigr] \le \delta\,.$$
No law is assumed: any distribution with the embedding property qualifies. -/
theorem HasSubspaceEmbedding.measureReal_norm_mulVec_sub_iterativeSketching_sq_gt_le
    [IsFiniteMeasure μ] {S : Ω → Matrix k m 𝕜} (h : HasSubspaceEmbedding S A a b δ μ)
    (ha : 0 < a) (hA : Function.Injective A.mulVec) {ω' : ℝ} (hω : 0 < ω')
    (hxs : IsLeastSquaresSolution A y xs) (x₀ : n → 𝕜) (q : ℕ) :
    μ.real {ω | (max |1 - ω' / b| |1 - ω' / a|) ^ (2 * q) *
        ‖WithLp.toLp 2 (A *ᵥ (xs - x₀))‖ ^ 2 <
      ‖WithLp.toLp 2 (A *ᵥ (xs - iterativeSketching A (S ω) ω' y x₀ q))‖ ^ 2} ≤ δ := by
  refine (measureReal_mono fun ω₁ hω₁ => ?_).trans h
  change ¬ IsSubspaceEmbedding (S ω₁) A a b
  intro hemb
  exact (not_le.mpr hω₁) (hemb.norm_mulVec_sub_iterativeSketching_sq_le ha hA hω hxs x₀ q)

/-- Damped iterative sketching with a random embedding, sketch-and-solve start: if the random
sketch $\mathbf{S}$ is a subspace embedding of $\operatorname{range}[\mathbf{A}\ \mathbf{y}]$ with
constants $1 \mp \varepsilon$ in squared norms ($(1 - \varepsilon)\|\mathbf{v}\|^2 \le
\|\mathbf{S}\mathbf{v}\|^2 \le (1 + \varepsilon)\|\mathbf{v}\|^2$ on that range),
$0 < \varepsilon < 1$, except with probability $\delta$, $\mathbf{A}$ has full column rank and
almost surely $\mathbf{x}_0$ minimizes $\|\mathbf{S}(\mathbf{A}\mathbf{x} - \mathbf{y})\|$, then
$$\mathbb{P}\Bigl[\Bigl(1 + \frac{2\varepsilon^{2q+1}}{1 - \varepsilon}\Bigr)
\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{y}\|^2 < \|\mathbf{y} -
\mathbf{A}\,\mathsf{iterativeSketching}(\mathbf{A}, \mathbf{S}, 1 - \varepsilon^2, \mathbf{y},
\mathbf{x}_0, q)\|^2\Bigr] \le \delta\,.$$
No law is assumed: any distribution with the embedding property qualifies. -/
theorem HasSubspaceEmbedding.measureReal_norm_sub_mulVec_iterativeSketching_one_sub_sq_sq_gt_le
    [DecidableEq m] [IsFiniteMeasure μ] {S : Ω → Matrix k m 𝕜}
    (h : HasSubspaceEmbedding S (Matrix.fromCols A (Matrix.replicateCol Unit y))
      (1 - ε) (1 + ε) δ μ)
    (hε : 0 < ε) (hε1 : ε < 1) (hA : Function.Injective A.mulVec) {x₀ : Ω → n → 𝕜}
    (hx₀ : ∀ᵐ ω ∂μ, IsLeastSquaresSolution (S ω * A) (S ω *ᵥ y) (x₀ ω)) (q : ℕ) :
    μ.real {ω | (1 + 2 * ε ^ (2 * q + 1) / (1 - ε)) *
        ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2 <
      ‖WithLp.toLp 2 (y - A *ᵥ iterativeSketching A (S ω) (1 - ε ^ 2) y (x₀ ω) q)‖ ^ 2} ≤ δ := by
  refine le_trans ?_ h
  rw [measureReal_def, measureReal_def]
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
  filter_upwards [hx₀] with ω hω hbad
  change ¬ IsSubspaceEmbedding (S ω) (Matrix.fromCols A (Matrix.replicateCol Unit y))
    (1 - ε) (1 + ε)
  intro hemb
  exact (not_le.mpr hbad) (hemb.norm_sub_mulVec_iterativeSketching_one_sub_sq_sq_le hε hε1 hA hω q)

end Random

end NLAlib
