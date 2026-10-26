/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Norms.Projector
public import NLAlib.Matrix.Pseudoinverse.Pinv

/-!
# Norms and singular values of the pseudoinverse

The singular values of $\mathbf{A}^{+}$ are the inverses of the nonzero singular values of
$\mathbf{A}$, in reverse order. In particular $\|\mathbf{A}^{+}\|_2$ is the inverse of the smallest
nonzero singular value, and a lower Loewner bound on the Gram matrix of $\mathbf{A}$ bounds
$\|\mathbf{A}^{+}\|_2$ above. The latter is how a subspace embedding controls
$(\mathbf{S}\mathbf{U})^{+}$.

## Main results

* `NLAlib.singularValues_pinv`: the singular values of the pseudoinverse.
* `NLAlib.specNorm_pinv`, `NLAlib.specNorm_pinv_of_injective`: its spectral norm.
* `NLAlib.specNorm_pinv_sq_le_inv_of_smul_one_le`: from
  $a\mathbf{I} \preceq \mathbf{A}^{\mathsf{H}}\mathbf{A}$.
* `NLAlib.norm_le_specNorm_pinv_mul_norm_mulVec`:
  $\|\mathbf{x}\| \le \|\mathbf{A}^{+}\|_2 \|\mathbf{A}\mathbf{x}\|$ for full column rank.
* `NLAlib.frobNorm_pinv_sq_eq_re_trace_inv`:
  $\|\mathbf{A}^{+}\|_{\mathsf{F}}^2
  = \operatorname{Re} \operatorname{tr}\bigl((\mathbf{A}^{\mathsf{H}}\mathbf{A})^{-1}\bigr)$ for
  full column rank.
* `NLAlib.frobNorm_pinv_le_frobNorm_pinv_conjTranspose_mul_mul_conjTranspose`: an invertible
  weight does not shrink the pseudoinverse (Epperly and Webber's Lemma 5.8).
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

/-- **Singular values of the pseudoinverse.** For $i + j + 1 = \operatorname{rank} \mathbf{A}$,
$\sigma_i(\mathbf{A}^{+}) = \sigma_j(\mathbf{A})^{-1}$, singular values non-increasing and indexed
from $0$: the nonzero singular values are inverted and their order reversed.
[HornJohnson2013, Problem 7.3.P7]. -/
theorem singularValues_pinv (A : Matrix m n 𝕜) {i j : ℕ} (h : i + j + 1 = A.rank) :
    singularValues (pinv A) i = (singularValues A j)⁻¹ := by
  obtain ⟨U, V, hsvd⟩ := exists_isSVD A le_rfl A.rank_le_card_height A.rank_le_card_width
  have hanti : Antitone ((fun k : Fin A.rank => (singularValues A k)⁻¹) ∘ Fin.revPerm) := by
    intro a b hab
    have hpos : 0 < singularValues A (Fin.rev a) := (singularValues_pos_iff A).mpr (Fin.rev a).2
    exact inv_anti₀ hpos (singularValues_antitone A (Fin.rev_le_rev.mpr hab))
  have hi := (hsvd.pinv.reindex Fin.revPerm).singularValues_eq hanti ⟨i, by omega⟩
  have hj : A.rank - (i + 1) = j := by omega
  rw [hi, Function.comp_apply, Fin.revPerm_apply, Fin.val_rev]
  exact congrArg (fun t => (singularValues A t)⁻¹) hj

/-- **The spectral norm of the pseudoinverse** is the inverse of the smallest nonzero singular
value: for $k + 1 = \operatorname{rank} \mathbf{A}$, $\|\mathbf{A}^{+}\|_2 =
\sigma_k(\mathbf{A})^{-1}$.
[GolubVanLoan2013, §5.5.2].
Port of `NLAlib.specNorm_moorePenroseInverse_eq_inv_singularValues_last_positive`. -/
theorem specNorm_pinv (A : Matrix m n 𝕜) {k : ℕ} (hk : k + 1 = A.rank) :
    specNorm (pinv A) = (singularValues A k)⁻¹ := by
  rw [← singularValues_zero_eq_specNorm]
  exact singularValues_pinv A (by omega)

/-- With full column rank, the spectral norm of the pseudoinverse is the inverse of the smallest
singular value: $\|\mathbf{A}^{+}\|_2 = \sigma_k(\mathbf{A})^{-1}$ for $k + 1 = \lvert n \rvert$. -/
theorem specNorm_pinv_of_injective {A : Matrix m n 𝕜} (hA : Function.Injective A.mulVec) {k : ℕ}
    (hk : k + 1 = Fintype.card n) : specNorm (pinv A) = (singularValues A k)⁻¹ := by
  exact specNorm_pinv A (hk.trans (mulVec_injective_iff_rank_eq.mp hA).symm)

/-- $\|\mathbf{A}^{+}\|_2^2 = \|(\mathbf{A}^{\mathsf{H}}\mathbf{A})^{+}\|_2$.
Port of `NLAlib.specNorm_moorePenroseInverse_sq`. -/
theorem specNorm_pinv_sq (A : Matrix m n 𝕜) :
    specNorm (pinv A) ^ 2 = specNorm (pinv (Aᴴ * A)) := by
  rw [pinv_conjTranspose_mul_self, specNorm_mul_conjTranspose_self]

/-- A lower bound on the Gram matrix bounds the pseudoinverse: if
$a\mathbf{I} \preceq \mathbf{A}^{\mathsf{H}}\mathbf{A}$ with $0 < a$, then $\|\mathbf{A}^{+}\|_2^2
\le a^{-1}$. With $\mathbf{A} = \mathbf{S}\mathbf{U}$ and $a = 1 - \varepsilon$ this is the bound on
$(\mathbf{S}\mathbf{U})^{+}$ delivered by a subspace embedding. -/
theorem specNorm_pinv_sq_le_inv_of_smul_one_le [DecidableEq n] {A : Matrix m n 𝕜} {a : ℝ}
    (ha : 0 < a) (h : a • (1 : Matrix n n 𝕜) ≤ Aᴴ * A) : specNorm (pinv A) ^ 2 ≤ a⁻¹ := by
  classical
  rw [specNorm_sq_le_iff_conjTranspose_mul_self_le (inv_pos.mpr ha).le,
    conjTranspose_mul_self_le_smul_one_iff]
  intro y
  have h₁ := smul_one_le_conjTranspose_mul_self_iff.mp h (pinv A *ᵥ y)
  have h₂ := (isStarProjection_rangeProjector A).norm_toLp_mulVec_le y
  rw [Matrix.mulVec_mulVec, mul_pinv] at h₁
  rw [le_inv_mul_iff₀ ha]
  exact h₁.trans (pow_le_pow_left₀ (norm_nonneg _) h₂ 2)

/-- The pseudoinverse bounds the vector below: with full column rank,
$\|\mathbf{x}\| \le \|\mathbf{A}^{+}\|_2 \|\mathbf{A}\mathbf{x}\|$.
Port of `NLAlib.inv_specNorm_pinvL_sq_mul_dotProduct_le`, there over $\mathbb{R}$ in squared
form. -/
theorem norm_le_specNorm_pinv_mul_norm_mulVec {A : Matrix m n 𝕜}
    (hA : Function.Injective A.mulVec) (x : n → 𝕜) :
    ‖WithLp.toLp 2 x‖ ≤ specNorm (pinv A) * ‖WithLp.toLp 2 (A *ᵥ x)‖ := by
  have h := norm_toLp_mulVec_le (pinv A) (A *ᵥ x)
  rwa [pinv_mulVec_mulVec_of_injective hA] at h

/-- For a vector $\mathbf{x}$ in the row space of $\mathbf{A}$ (the range of
$\mathbf{A}^{\mathsf{H}}$), $\|\mathbf{x}\| \le \|\mathbf{A}^{+}\|_2 \|\mathbf{A}\mathbf{x}\|$, with
no rank assumption.
Port of `NLAlib.inv_specNorm_moorePenroseInverse_sq_mul_dotProduct_le`, there over $\mathbb{R}$. -/
theorem norm_le_specNorm_pinv_mul_norm_mulVec_of_mem_range (A : Matrix m n 𝕜) {x : n → 𝕜}
    (hx : x ∈ LinearMap.range Aᴴ.mulVecLin) :
    ‖WithLp.toLp 2 x‖ ≤ specNorm (pinv A) * ‖WithLp.toLp 2 (A *ᵥ x)‖ := by
  have h := norm_toLp_mulVec_le (pinv A) (A *ᵥ x)
  rwa [Matrix.mulVec_mulVec, pinv_mul, rangeProjector_mulVec_eq_self_iff.mpr hx] at h

/-- A lower Gram bound is a bound on the pseudoinverse: with full column rank and $0 < a$,
$a\mathbf{I} \preceq \mathbf{A}^{\mathsf{H}}\mathbf{A}$ exactly when $\|\mathbf{A}^{+}\|_2^2 \le
a^{-1}$. -/
theorem smul_one_le_conjTranspose_mul_self_iff_specNorm_pinv_sq_le [DecidableEq n]
    {A : Matrix m n 𝕜} (hA : Function.Injective A.mulVec) {a : ℝ} (ha : 0 < a) :
    a • (1 : Matrix n n 𝕜) ≤ Aᴴ * A ↔ specNorm (pinv A) ^ 2 ≤ a⁻¹ := by
  refine ⟨specNorm_pinv_sq_le_inv_of_smul_one_le ha, fun h => ?_⟩
  refine smul_one_le_conjTranspose_mul_self_iff.mpr fun x => ?_
  have hx := pow_le_pow_left₀ (norm_nonneg _) (norm_le_specNorm_pinv_mul_norm_mulVec hA x) 2
  rw [mul_pow] at hx
  have hx' := hx.trans (mul_le_mul_of_nonneg_right h (sq_nonneg _))
  rwa [le_inv_mul_iff₀ ha] at hx'

/-- The squared Frobenius norm of the pseudoinverse is the sum of the inverse squared
nonzero singular values:
$\|\mathbf{A}^{+}\|_{\mathsf{F}}^2 = \sum_{k < \operatorname{rank} \mathbf{A}}
\sigma_k(\mathbf{A})^{-2}$. -/
theorem frobNorm_pinv_sq (A : Matrix m n 𝕜) :
    frobNorm (pinv A) ^ 2 = ∑ k ∈ Finset.range A.rank, (singularValues A k ^ 2)⁻¹ := by
  obtain ⟨U, V, hsvd⟩ := exists_isSVD A le_rfl A.rank_le_card_height A.rank_le_card_width
  rw [hsvd.pinv.frobNorm_sq_eq, ← Fin.sum_univ_eq_sum_range fun k => (singularValues A k ^ 2)⁻¹]
  exact Finset.sum_congr rfl fun i _ => inv_pow _ _

/-- With full column rank,
$\|\mathbf{A}^{+}\|_{\mathsf{F}}^2 = \operatorname{Re}
\operatorname{tr}\bigl((\mathbf{A}^{\mathsf{H}}\mathbf{A})^{-1}\bigr)$. This is the quantity whose
expectation for a Gaussian matrix drives the randomized range finder bounds.
[HalkoMartinssonTropp2011, Proposition 10.2] uses it in this form.
Port of `NLAlib.frobSq_pinvL_eq_trace_inv`. -/
theorem frobNorm_pinv_sq_eq_re_trace_inv [DecidableEq n] {A : Matrix m n 𝕜}
    (hA : Function.Injective A.mulVec) :
    frobNorm (pinv A) ^ 2 = RCLike.re ((Aᴴ * A)⁻¹).trace := by
  rw [frobNorm_sq_eq_re_trace, Matrix.trace_mul_comm, ← pinv_conjTranspose_mul_self,
    pinv_of_isUnit (isUnit_conjTranspose_mul_self_iff.mpr hA)]

/-- With full row rank,
$\|\mathbf{A}^{+}\|_{\mathsf{F}}^2 = \operatorname{Re}
\operatorname{tr}\bigl((\mathbf{A}\mathbf{A}^{\mathsf{H}})^{-1}\bigr)$. This is the form the
randomized range finder uses, for the full-row-rank Gaussian block $\mathbf{\Omega}_1$.
[HalkoMartinssonTropp2011, Proposition 10.2].
Port of `NLAlib.frobSq_pinvR_eq_trace_inv`. -/
theorem frobNorm_pinv_sq_eq_re_trace_inv_of_injective_conjTranspose [DecidableEq m]
    {A : Matrix m n 𝕜} (hA : Function.Injective Aᴴ.mulVec) :
    frobNorm (pinv A) ^ 2 = RCLike.re ((A * Aᴴ)⁻¹).trace := by
  have h := frobNorm_pinv_sq_eq_re_trace_inv hA
  rwa [pinv_conjTranspose, frobNorm_conjTranspose, Matrix.conjTranspose_conjTranspose] at h

/-- $\|\mathbf{A}^{+}\|_{\mathsf{F}}^2 = \operatorname{Re}
\operatorname{tr}\bigl((\mathbf{A}\mathbf{A}^{\mathsf{H}})^{+}\bigr)$, with no rank assumption.
Port of `NLAlib.frobSq_moorePenroseInverse_eq_trace_moorePenroseInverse`. -/
theorem frobNorm_pinv_sq_eq_re_trace_pinv (A : Matrix m n 𝕜) :
    frobNorm (pinv A) ^ 2 = RCLike.re (pinv (A * Aᴴ)).trace := by
  rw [frobNorm_sq_eq_re_trace, pinv_mul_conjTranspose_self]

/-! ### Weighting does not shrink the pseudoinverse -/

section Weighted

variable {l r : Type*} [Fintype l] [Fintype r] [DecidableEq l]

omit [DecidableEq l] in
private theorem pinv_mul_self_eq (A : Matrix l r 𝕜) : pinv A * A = Aᴴ * (pinv A)ᴴ := by
  rw [pinv_mul, ← pinv_conjTranspose, mul_pinv]

omit [DecidableEq l] in
private theorem pinv_mul_self_conjTranspose (A : Matrix l r 𝕜) :
    (pinv A * A)ᴴ = pinv A * A := by
  rw [pinv_mul]
  exact (isStarProjection_rangeProjector Aᴴ).conjTranspose_eq

/-- **Weighting does not shrink the pseudoinverse** (Epperly and Webber's "weighting hurts"): for
$\mathbf{M} \in \Bbbk^{\ell \times r}$ and invertible $\mathbf{R} \in \Bbbk^{\ell \times \ell}$,
$$\|\mathbf{M}^{+}\|_{\mathsf{F}} \le
\|(\mathbf{R}^{\mathsf{H}}\mathbf{M})^{+}\mathbf{R}^{\mathsf{H}}\|_{\mathsf{F}}\,.$$
Any $\mathbf{M}$ (no rank hypothesis).
[EpperlyWebber2026, Lemma 5.8]. -/
theorem frobNorm_pinv_le_frobNorm_pinv_conjTranspose_mul_mul_conjTranspose (M : Matrix l r 𝕜)
    {R : Matrix l l 𝕜} (hR : IsUnit R) :
    frobNorm (pinv M) ≤ frobNorm (pinv (Rᴴ * M) * Rᴴ) := by
  obtain ⟨S, hS⟩ := hR.exists_right_inv
  -- `Mᴴ = (RᴴM)ᴴ S`, since `R S = 1`
  have hMH : Mᴴ = (Rᴴ * M)ᴴ * S := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, hS,
      Matrix.mul_one]
  -- the projector `(RᴴM)⁺(RᴴM)` fixes `Mᴴ`
  have hQMH : pinv (Rᴴ * M) * (Rᴴ * M) * Mᴴ = Mᴴ := by
    have hQ := pinv_mul_self_conjTranspose (Rᴴ * M)
    have h1 : pinv (Rᴴ * M) * (Rᴴ * M) * (Rᴴ * M)ᴴ = (Rᴴ * M)ᴴ := by
      calc pinv (Rᴴ * M) * (Rᴴ * M) * (Rᴴ * M)ᴴ
          = ((Rᴴ * M) * (pinv (Rᴴ * M) * (Rᴴ * M)))ᴴ := by
            rw [Matrix.conjTranspose_mul (Rᴴ * M) (pinv (Rᴴ * M) * (Rᴴ * M)), hQ]
        _ = (Rᴴ * M)ᴴ := by rw [← Matrix.mul_assoc, mul_pinv_mul_self]
    rw [hMH, ← Matrix.mul_assoc, h1]
  -- hence `(RᴴM)⁺(RᴴM) M⁺ = M⁺`
  have hZ : pinv M = Mᴴ * ((pinv M)ᴴ * pinv M) := by
    calc pinv M = pinv M * M * pinv M := (pinv_mul_mul_pinv M).symm
      _ = Mᴴ * (pinv M)ᴴ * pinv M := by rw [pinv_mul_self_eq M]
      _ = Mᴴ * ((pinv M)ᴴ * pinv M) := Matrix.mul_assoc _ _ _
  have hQP : pinv (Rᴴ * M) * (Rᴴ * M) * pinv M = pinv M := by
    calc pinv (Rᴴ * M) * (Rᴴ * M) * pinv M
        = pinv (Rᴴ * M) * (Rᴴ * M) * (Mᴴ * ((pinv M)ᴴ * pinv M)) := by rw [← hZ]
      _ = (pinv (Rᴴ * M) * (Rᴴ * M) * Mᴴ) * ((pinv M)ᴴ * pinv M) := by
            rw [Matrix.mul_assoc _ Mᴴ]
      _ = Mᴴ * ((pinv M)ᴴ * pinv M) := by rw [hQMH]
      _ = pinv M := hZ.symm
  have key : pinv M = pinv (Rᴴ * M) * Rᴴ * (rangeProjector M) := by
    rw [← mul_pinv M]
    calc pinv M = pinv (Rᴴ * M) * (Rᴴ * M) * pinv M := hQP.symm
      _ = pinv (Rᴴ * M) * Rᴴ * (M * pinv M) := by simp only [Matrix.mul_assoc]
  rw [key]
  exact (frobNorm_mul_le_frobNorm_mul_specNorm _ _).trans
    (mul_le_of_le_one_right (frobNorm_nonneg _)
      (isStarProjection_rangeProjector M).specNorm_le_one)

end Weighted

end NLAlib
