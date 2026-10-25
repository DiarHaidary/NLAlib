/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Data.Matrix.Mul
public import NLAlib.Krylov.LinearSystems.GMRES
public import NLAlib.Krylov.Processes.ArnoldiRecurrence
public import NLAlib.Matrix.Factorizations.GivensHessenberg

/-!
# GMRES through the Arnoldi process

For every square $\mathbf{A}$ and every $q$, the GMRES iterate is
$\mathbf{x}_0 + \|\mathbf{r}_0\|\,\mathbf{Q}_q\underline{\mathbf{H}}_q^{+}\mathbf{e}_0$, with
$\mathbf{Q}_q$ the Arnoldi basis of $\mathcal{K}_q(\mathbf{A}, \mathbf{r}_0)$ and
$\underline{\mathbf{H}}_q = \mathbf{Q}_{q+1}^{\mathsf{H}}\mathbf{A}\mathbf{Q}_q$ the
$(q + 1) \times q$ Hessenberg matrix: the small least-squares problem
$\min_{\mathbf{y}}\|\|\mathbf{r}_0\|\mathbf{e}_0 - \underline{\mathbf{H}}_q\mathbf{y}\|$, whose
minimum-norm solution the pseudoinverse names. The same holds with the basis and Hessenberg matrix
computed by the Arnoldi process. No grade hypothesis: past the grade the canonical basis has zero
columns, $\mathbf{Q}\mathbf{Q}^{\mathsf{H}}\mathbf{Q} = \mathbf{Q}$ still holds, and
`pinv_mul_of_conjTranspose_mul_self_mul_eq` applies.

The standard implementation solves the small problem by Givens QR of $\underline{\mathbf{H}}_q$
(`NLAlib.givensHessenbergState`) and back substitution (`NLAlib.backSubst`):
`gmresIterate_eq_backSubst_givensHessenberg` is that realisation, for invertible $\mathbf{A}$
and every $q$, with no hypothesis on the grade or on computed pivots (maintainer, 2026-10-17:
the algorithm returns the same iterate once it reaches the grade). Past the grade the Arnoldi
columns and the Hessenberg rows and columns from $\nu$ on are zero, Givens QR keeps them zero
(`givensHessenbergState_apply_eq_zero_of_le`, `givensHessenbergState_snd_apply_eq_zero_of_col`),
the pivots from $\nu$ on are zero and `backSubst` returns zero coefficients for them without
disturbing the others (`backSubst_castLE_of_apply_eq_zero`). Invertibility is the
problem-level hypothesis: for singular $\mathbf{A}$ the last pivot before the grade can vanish
while its column is not zero, and back substitution then differs from the least-norm solution.
Up to the grade the pivots are nonzero
(`forall_givensHessenbergR_mgsArnoldiHessenberg_ne_zero_iff`, a lemma, not a hypothesis). The
residual norm is read off the rotated right-hand side
(`norm_sub_mulVec_gmresIterate_eq_norm_givensHessenbergQ`).

## Main results

* `NLAlib.gmresIterate_eq_arnoldiMatrix`: the canonical Arnoldi basis yields GMRES.
* `NLAlib.gmresIterate_eq_mgsArnoldiMatrix`: the Arnoldi process yields GMRES.
* `NLAlib.gmresIterate_eq_backSubst_givensHessenberg`: Arnoldi with Givens QR and back
  substitution yields GMRES.
* `NLAlib.norm_sub_mulVec_gmresIterate_eq_norm_givensHessenbergQ`: the residual estimate.
* `NLAlib.forall_givensHessenbergR_mgsArnoldiHessenberg_ne_zero_iff`: the pivots are nonzero
  exactly up to the grade.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- **The Arnoldi basis yields GMRES**, for every $\mathbf{A}$ and $q$: with
$\mathbf{r}_0 = \mathbf{b} - \mathbf{A}\mathbf{x}_0$, the canonical bases
$\mathbf{Q}_j = \mathsf{arnoldiMatrix}(\mathbf{A}, \mathbf{r}_0, j)$ and
$\underline{\mathbf{H}}_q = \mathbf{Q}_{q+1}^{\mathsf{H}}\mathbf{A}\mathbf{Q}_q$,
$\mathsf{gmresIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q) = \mathbf{x}_0 +
\|\mathbf{r}_0\|\,\mathbf{Q}_q\underline{\mathbf{H}}_q^{+}\mathbf{e}_0$, with no grade
hypothesis. [SaadSchultz1986, §3.1]; [Saad2003, §6.5.1]. It is (8) there, and (6.29)–(6.30) in
Saad's book, with the least-squares minimiser of
$\|\|\mathbf{r}_0\|\mathbf{e}_0 - \underline{\mathbf{H}}_q\mathbf{y}\|$ in place of the
pseudoinverse, for $q$ up to the breakdown step.
Result: gmres-arnoldi -/
theorem gmresIterate_eq_arnoldiMatrix (A : Matrix n n 𝕜) (b x₀ : n → 𝕜) (q : ℕ) :
    gmresIterate A b x₀ q = x₀ + (‖WithLp.toLp 2 (b - A *ᵥ x₀)‖ : 𝕜) •
      (arnoldiMatrix A (b - A *ᵥ x₀) q *ᵥ
        (pinv ((arnoldiMatrix A (b - A *ᵥ x₀) (q + 1))ᴴ * A * arnoldiMatrix A (b - A *ᵥ x₀) q)
          *ᵥ Pi.single 0 1)) := by
  have hQ := gramSchmidtQ_mul_conjTranspose_gramSchmidtQ_mul_self
    (krylovMatrix A (b - A *ᵥ x₀) q)
  have hQ' := gramSchmidtQ_mul_conjTranspose_gramSchmidtQ_mul_self
    (krylovMatrix A (b - A *ᵥ x₀) (q + 1))
  rw [← arnoldiMatrix] at hQ hQ'
  have hQ'' : (arnoldiMatrix A (b - A *ᵥ x₀) (q + 1))ᴴ * arnoldiMatrix A (b - A *ᵥ x₀) (q + 1) *
      (arnoldiMatrix A (b - A *ᵥ x₀) (q + 1))ᴴ = (arnoldiMatrix A (b - A *ᵥ x₀) (q + 1))ᴴ := by
    have h := congrArg Matrix.conjTranspose hQ'
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      at h
  rw [gmresIterate, minResidualInverse, ← gramSchmidtQ_mul_conjTranspose, ← arnoldiMatrix,
    ← Matrix.mul_assoc A, mul_arnoldiMatrix,
    Matrix.mul_assoc (arnoldiMatrix A (b - A *ᵥ x₀) (q + 1)),
    pinv_mul_of_conjTranspose_mul_self_mul_eq (by simp only [← Matrix.mul_assoc, hQ'']),
    pinv_mul_conjTranspose_of_mul_conjTranspose_mul_self_eq (by simp only [Matrix.mul_assoc, hQ]),
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, conjTranspose_arnoldiMatrix_mulVec_self,
    Matrix.mulVec_smul, Matrix.mulVec_smul]

/-- **The Arnoldi process yields GMRES**, for every $\mathbf{A}$ and $q$, with the basis
$\mathbf{V}_q$ and the Hessenberg matrix $\underline{\mathbf{H}}_q$ computed by `arnoldiState`
from $\mathbf{r}_0 = \mathbf{b} - \mathbf{A}\mathbf{x}_0$:
$\mathsf{gmresIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q) = \mathbf{x}_0 +
\|\mathbf{r}_0\|\,\mathbf{V}_q\underline{\mathbf{H}}_q^{+}\mathbf{e}_0$.
[SaadSchultz1986, Algorithm 3]; [Saad2003, Algorithm 6.9]; both stop at the first zero
$h_{j+1,j}$, here the formula holds for every $q$.
Result: gmres-arnoldi -/
theorem gmresIterate_eq_mgsArnoldiMatrix (A : Matrix n n 𝕜) (b x₀ : n → 𝕜) (q : ℕ) :
    gmresIterate A b x₀ q = x₀ + (‖WithLp.toLp 2 (b - A *ᵥ x₀)‖ : 𝕜) •
      (mgsArnoldiMatrix A (b - A *ᵥ x₀) q *ᵥ
        (pinv (mgsArnoldiHessenberg A (b - A *ᵥ x₀) q) *ᵥ Pi.single 0 1)) := by
  rw [mgsArnoldiMatrix_eq_arnoldiMatrix, mgsArnoldiHessenberg_eq, gmresIterate_eq_arnoldiMatrix]

/-! ### Pivots and the computed basis past the grade -/

/-- When the pivots are nonzero: for invertible $\mathbf{A}$, the computed Givens pivots of
$\underline{\mathbf{H}}_q$ are all nonzero exactly for $q \le \nu$, the grade of $\mathbf{r}_0$. A
lemma used inside the realisation, never its hypothesis. -/
theorem forall_givensHessenbergR_mgsArnoldiHessenberg_ne_zero_iff {A : Matrix n n 𝕜}
    (hA : IsUnit A) (r : n → 𝕜) (q : ℕ) :
    (∀ i : Fin q, givensHessenbergR (mgsArnoldiHessenberg A r q) i.castSucc i ≠ 0) ↔
      q ≤ krylovGrade A r :=
  (forall_givensHessenbergR_apply_self_ne_zero_iff (isUpperHessenberg_mgsArnoldiHessenberg A r q)
    (Nat.le_succ q)).trans (injective_mulVec_mgsArnoldiHessenberg_iff hA r q)

/-- The computed basis past the grade: its columns from $\nu$ on vanish. -/
private theorem mgsArnoldiMatrix_col_eq_zero (A : Matrix n n 𝕜) (r : n → 𝕜) {q : ℕ} (b : Fin q)
    (hb : krylovGrade A r ≤ (b : ℕ)) : (mgsArnoldiMatrix A r q).col b = 0 := by
  rw [mgsArnoldiMatrix_eq_arnoldiMatrix, arnoldiMatrix_col_eq_col_last,
    arnoldiMatrix_col_last_eq_zero_iff.mpr hb]

omit [DecidableEq n] in
/-- $\|\mathbf{r}\|\,\mathbf{Q}_{q+1}\mathbf{e}_0 = \mathbf{r}$ for the computed basis. -/
private theorem norm_smul_mgsArnoldiMatrix_mulVec_single (A : Matrix n n 𝕜) (r : n → 𝕜) (q : ℕ) :
    (‖WithLp.toLp 2 r‖ : 𝕜) • (mgsArnoldiMatrix A r (q + 1) *ᵥ Pi.single 0 1) = r := by
  classical
  rw [mgsArnoldiMatrix_eq_arnoldiMatrix, ← Matrix.mulVec_smul,
    ← conjTranspose_arnoldiMatrix_mulVec_self A r q, Matrix.mulVec_mulVec, arnoldiMatrix,
    gramSchmidtQ_mul_conjTranspose]
  exact rangeProjector_mulVec_eq_self_iff.mpr (self_mem_krylovSpace A r (Nat.succ_pos q))

/-! ### Givens QR and back substitution -/

/-- **Arnoldi with Givens QR yields GMRES**, the standard implementation: with
$\underline{\mathbf{H}}_q$ computed by the Arnoldi process, $\mathbf{R}$ the leading
$q \times q$ block of its Givens factor and $\mathbf{g}$ the first $q$ entries of the rotated
$\mathbf{e}_0$, for invertible $\mathbf{A}$ and every $q$,
$\mathsf{gmresIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q) = \mathbf{x}_0 +
\|\mathbf{r}_0\|\,\mathbf{Q}_q\,\mathsf{backSubst}(\mathbf{R}, \mathbf{g})$, with no
hypothesis on the grade or on the computed pivots.
[SaadSchultz1986, §3.2]; [Saad2003, Proposition 6.9]. Both solve the small least-squares problem
by plane rotations and back substitution on the triangular system left after deleting the last
row; the rotation signs here follow `NLAlib.givens`.
Result: gmres-givens -/
theorem gmresIterate_eq_backSubst_givensHessenberg {A : Matrix n n 𝕜} (hA : IsUnit A)
    (b x₀ : n → 𝕜) (q : ℕ) :
    gmresIterate A b x₀ q = x₀ + (‖WithLp.toLp 2 (b - A *ᵥ x₀)‖ : 𝕜) •
      (mgsArnoldiMatrix A (b - A *ᵥ x₀) q *ᵥ
        backSubst ((givensHessenbergR (mgsArnoldiHessenberg A (b - A *ᵥ x₀) q)).submatrix
            Fin.castSucc id)
          (fun i => ((givensHessenbergQ (mgsArnoldiHessenberg A (b - A *ᵥ x₀) q))ᴴ *ᵥ
            Pi.single 0 1) i.castSucc)) := by
  set r := b - A *ᵥ x₀ with hr
  set H := mgsArnoldiHessenberg A r q with hH
  have hHH := isUpperHessenberg_mgsArnoldiHessenberg A r q
  rcases le_or_gt q (krylovGrade A r) with hq | hq
  · have key : pinv H *ᵥ Pi.single 0 1 =
        backSubst ((givensHessenbergR H).submatrix Fin.castSucc id)
          (fun i => ((givensHessenbergQ H)ᴴ *ᵥ Pi.single 0 1) i.castSucc) :=
      pinv_submatrix_mulVec_single_eq_backSubst hHH le_rfl le_rfl
        ((injective_mulVec_mgsArnoldiHessenberg_iff hA r q).mpr hq)
    rw [gmresIterate_eq_mgsArnoldiMatrix, key]
  · set ν := krylovGrade A r with hν
    have hdet := (Matrix.isUnit_iff_isUnit_det A).mp hA
    have hxs : A *ᵥ (A⁻¹ *ᵥ b) = b := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hdet, Matrix.one_mulVec]
    rw [gmresIterate_eq_of_krylovGrade_le hA hxs x₀ hq.le,
      ← gmresIterate_eq_of_krylovGrade_le hA hxs x₀ (le_refl ν), gmresIterate_eq_mgsArnoldiMatrix]
    have hsub : H.submatrix (Fin.castLE (Nat.succ_le_succ hq.le)) (Fin.castLE hq.le) =
        mgsArnoldiHessenberg A r ν := rfl
    have key := pinv_submatrix_mulVec_single_eq_backSubst hHH hq.le (Nat.succ_le_succ hq.le)
      (hsub ▸ (injective_mulVec_mgsArnoldiHessenberg_iff hA r ν).mpr le_rfl)
    rw [hsub] at key
    rw [key, Matrix.mulVec_eq_submatrix_castLE_mulVec hq.le (mgsArnoldiMatrix A r q)
      (fun c hc => mgsArnoldiMatrix_col_eq_zero A r c hc)]
    have hrows := (givensHessenbergState_apply_eq_zero_of_le (H := H) (r := ν)
      (fun a c ha => mgsArnoldiHessenberg_apply_eq_zero_of_le A r (Or.inl ha))
      (v := 0) (fun _ _ => rfl) q).1
    congr 2
    refine congrArg₂ (· *ᵥ ·) rfl ?_
    funext i
    rw [Function.comp_apply, backSubst_castLE_of_apply_eq_zero hq.le (fun a c hac => by
      rcases hac with ha | hc
      · exact hrows a.castSucc c ha
      · exact givensHessenbergState_snd_apply_eq_zero_of_col
          (fun a => mgsArnoldiHessenberg_apply_eq_zero_of_le A r (Or.inr hc)) q a.castSucc)]
    congr 1
    · ext a c
      exact ((givensHessenbergState_apply_of_lt H (Pi.single 0 1) hq.le
        (a := (Fin.castLE hq.le a).castSucc) a.2).1 _).symm
    · funext a
      exact ((givensHessenbergState_apply_of_lt H (Pi.single 0 1) hq.le
        (a := (Fin.castLE hq.le a).castSucc) a.2).2).symm

/-- **The GMRES residual estimate**: for invertible $\mathbf{A}$ and every $q$, with
$\mathbf{r}_0 = \mathbf{b} - \mathbf{A}\mathbf{x}_0$, $\underline{\mathbf{H}}_q$ computed by the
Arnoldi process and $\mathbf{G}$ its Givens factor,
$\|\mathbf{b} - \mathbf{A}\,\mathsf{gmresIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q)\| =
\|\mathbf{r}_0\|\,\lvert(\mathbf{G}^{\mathsf{H}}\mathbf{e}_0)_q\rvert$, the modulus of the last
entry of the rotated $\mathbf{e}_0$, available without forming the iterate.
[SaadSchultz1986, Proposition 1]; [Saad2003, Proposition 6.9]. It is (6.42) in Saad's book.
Result: gmres-residual-estimate -/
theorem norm_sub_mulVec_gmresIterate_eq_norm_givensHessenbergQ {A : Matrix n n 𝕜}
    (hA : IsUnit A) (b x₀ : n → 𝕜) (q : ℕ) :
    ‖WithLp.toLp 2 (b - A *ᵥ gmresIterate A b x₀ q)‖ = ‖WithLp.toLp 2 (b - A *ᵥ x₀)‖ *
      ‖((givensHessenbergQ (mgsArnoldiHessenberg A (b - A *ᵥ x₀) q))ᴴ *ᵥ Pi.single 0 1)
        (Fin.last q)‖ := by
  set r := b - A *ᵥ x₀ with hr
  set H := mgsArnoldiHessenberg A r q with hH
  rcases lt_or_ge q (krylovGrade A r) with hq | hq
  · have key : ‖WithLp.toLp 2 (Pi.single 0 1 - H *ᵥ (pinv H *ᵥ Pi.single 0 1))‖ =
        ‖((givensHessenbergQ H)ᴴ *ᵥ Pi.single 0 1) (Fin.last q)‖ :=
      norm_sub_mulVec_pinv_submatrix_mulVec_single_eq
        (isUpperHessenberg_mgsArnoldiHessenberg A r q) le_rfl le_rfl
        ((injective_mulVec_mgsArnoldiHessenberg_iff hA r q).mpr hq.le)
    have hQ : HasOrthonormalCols (mgsArnoldiMatrix A r (q + 1)) := by
      rw [mgsArnoldiMatrix_eq_arnoldiMatrix]
      exact hasOrthonormalCols_arnoldiMatrix_iff.mpr hq
    have hres : b - A *ᵥ gmresIterate A b x₀ q = (‖WithLp.toLp 2 r‖ : 𝕜) •
        (mgsArnoldiMatrix A r (q + 1) *ᵥ (Pi.single 0 1 - H *ᵥ (pinv H *ᵥ Pi.single 0 1))) := by
      rw [gmresIterate_eq_mgsArnoldiMatrix, Matrix.mulVec_add, Matrix.mulVec_smul,
        Matrix.mulVec_mulVec, mul_mgsArnoldiMatrix, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub,
        smul_sub, norm_smul_mgsArnoldiMatrix_mulVec_single, ← hH, sub_add_eq_sub_sub, ← hr]
    rw [hres, WithLp.toLp_smul, norm_smul, RCLike.norm_ofReal, abs_norm, hQ.norm_toLp_mulVec, key]
  · have hdet := (Matrix.isUnit_iff_isUnit_det A).mp hA
    have hxs : A *ᵥ (A⁻¹ *ᵥ b) = b := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hdet, Matrix.one_mulVec]
    rw [gmresIterate_eq_of_krylovGrade_le hA hxs x₀ hq, hxs, sub_self, WithLp.toLp_zero, norm_zero]
    rcases Nat.eq_zero_or_pos (krylovGrade A r) with h0 | h0
    · have hr0 : r = 0 := by
        have h1 := self_mem_krylovSpace A r (q := 1) one_pos
        rw [krylovSpace_eq_of_krylovGrade_le (h0.le.trans zero_le_one), h0, krylovSpace_zero,
          Submodule.mem_bot] at h1
        exact h1
      rw [hr0, WithLp.toLp_zero, norm_zero, zero_mul]
    · have hv : ∀ a : Fin (q + 1), krylovGrade A r ≤ (a : ℕ) →
          (Pi.single 0 1 : Fin (q + 1) → 𝕜) a = 0 :=
        fun a ha => Pi.single_eq_of_ne (fun h => by rw [h, Fin.val_zero] at ha; omega) 1
      have hz := (givensHessenbergState_apply_eq_zero_of_le (H := H) (r := krylovGrade A r)
        (fun a c ha => mgsArnoldiHessenberg_apply_eq_zero_of_le A r (Or.inl ha)) hv q).2
        (Fin.last q) hq
      rw [givensHessenbergQ, hz, norm_zero, mul_zero]

end NLAlib
