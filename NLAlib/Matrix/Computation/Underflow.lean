/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BLAS.Underflow
public import NLAlib.Matrix.Norms.Compare

/-!
# Matrix-product executions with absolute rounding errors

The actual rectangular `gemv` and `gemm` kernels retain their successful execution and exact
output-block write witnesses. Input-only bounds certify the range of every product and sum.
The forward errors have a relative matrix-norm term and a separate absolute term proportional
to the square root of the number of output entries. In particular the absolute term is not
hidden in a homogeneous oracle error coefficient. The operation order is that of [Higham2002].

## Main results

* `NLAlib.Computation.IsArithErrSem.exec_gemv_norm_sub_le_frobNorm_mul_of_absRelErr`:
  rectangular matrix-vector execution with Frobenius-norm error.
* `NLAlib.Computation.IsArithErrSem.exec_gemv_norm_sub_le_specNorm_mul_of_absRelErr`:
  the corresponding spectral-norm consequence.
* `NLAlib.Computation.IsArithErrSem.exec_gemm_frobNorm_sub_le_of_absRelErr`:
  rectangular matrix-product execution with Frobenius-norm error.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Computation

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]
  (I : Interp P ι K C) (tag : P) (st : St P K C)
  {dec : P → K → ℝ} {u η : P → ℝ} {safe : P → ℝ → Prop}

/-- The actual rectangular `gemv` run succeeds and changes only its output block under
decoded-input, writable-output, and disjointness assumptions. Assume $u,\eta\ge0$ and a safe
radius $L$. For each row, require $P\sum_j\lvert a_{ij}x_j\rvert+D\le L$, with
$P=(1+u)^{2n}$ and $D=nP(2+u)\eta$. The Euclidean error is at most
$(P-1)\|\mathbf{A}\|_{\mathsf{F}}\|\mathbf{x}\|+\sqrt m D$.
No smallness condition on $nu$ is needed. [Higham2002, §2.2 and §3.5]. -/
theorem IsArithErrSem.exec_gemv_norm_sub_le_frobNorm_mul_of_absRelErr
    (h : IsArithErrSem (fun p _ => AbsRelErr (u p) (η p)) dec safe I.sem)
    (hz : AddsZeroExactly dec I.sem) (m n : IExp ℕ) (A : ℕ) (ao : IExp ℕ)
    (x : ℕ) (xo : IExp ℕ) (y : ℕ) (yo : IExp ℕ)
    (M : Matrix (Fin m.eval) (Fin n.eval) ℝ) (xv : Fin n.eval → ℝ)
    (L : ℝ) (hu : 0 ≤ u tag) (hη : 0 ≤ η tag)
    (hA : HoldsDecoded st.store dec tag A ao.eval M)
    (hx : ∀ j : Fin n.eval, ∃ w, st.store.read tag x (xo.eval + j) = some w ∧
      dec tag w = xv j)
    (hyA : y = A → yo.eval + m.eval ≤ ao.eval ∨ ao.eval + m.eval * n.eval ≤ yo.eval)
    (hyx : y = x → yo.eval + m.eval ≤ xo.eval ∨ xo.eval + n.eval ≤ yo.eval)
    (hy : ∀ i < m.eval, ∃ v s, st.store.write tag y (yo.eval + i) v = some s)
    (hinput : ∀ i : Fin m.eval,
      (1 + u tag) ^ (2 * n.eval) * (∑ j, |M i j * xv j|) +
        n.eval * (1 + u tag) ^ (2 * n.eval) * (2 + u tag) * η tag ≤ L)
    (hball : ∀ b, |b| ≤ L → safe tag b) :
    ∃ out, ∃ W : ℕ → K, exec I (gemv tag m n A ao x xo y yo).run st = some out ∧
      st.store.writeBlock tag y yo.eval ((List.range m.eval).toArray.map W) = some out.store ∧
      ‖WithLp.toLp 2 (M *ᵥ xv - fun i : Fin m.eval => dec tag (W i))‖ ≤
        ((1 + u tag) ^ (2 * n.eval) - 1) * frobNorm M * ‖WithLp.toLp 2 xv‖ +
        Real.sqrt m.eval * (n.eval * (1 + u tag) ^ (2 * n.eval) * (2 + u tag) * η tag) := by
  obtain ⟨out, W, hrun, hwrite, herr⟩ :=
    h.exec_gemv_abs_sum_mul_sub_le_of_absRelErr I tag hz st m n A ao x xo y yo
      (fun i j => if h : i < m.eval ∧ j < n.eval then M ⟨i, h.1⟩ ⟨j, h.2⟩ else 0)
      (fun j => if h : j < n.eval then xv ⟨j, h⟩ else 0) L hu hη
      (fun i hi j hj => by simpa [hi, hj] using hA ⟨i, hi⟩ ⟨j, hj⟩)
      (fun j hj => by simpa [hj] using hx ⟨j, hj⟩) hyA hyx hy
      (fun i hi => by
        rw [← Fin.sum_univ_eq_sum_range]
        simpa [hi] using hinput ⟨i, hi⟩) hball
  have hc : 0 ≤ (1 + u tag) ^ (2 * n.eval) - 1 :=
    sub_nonneg.mpr (one_le_pow₀ (by linarith))
  have hpoint (i : Fin m.eval) :
      |(M *ᵥ xv - fun i : Fin m.eval => dec tag (W i)) i| ≤
        ((1 + u tag) ^ (2 * n.eval) - 1) *
          |(M.map abs *ᵥ fun j => |xv j|) i| +
        n.eval * (1 + u tag) ^ (2 * n.eval) * (2 + u tag) * η tag := by
    have hr := herr i i.isLt
    rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range] at hr
    have hr' : |(M *ᵥ xv - fun i : Fin m.eval => dec tag (W i)) i| ≤
        ((1 + u tag) ^ (2 * n.eval) - 1) * (M.map abs *ᵥ fun j => |xv j|) i +
          n.eval * (1 + u tag) ^ (2 * n.eval) * (2 + u tag) * η tag := by
      simpa [Matrix.mulVec, dotProduct, i.isLt, abs_mul] using hr
    exact hr'.trans (by gcongr; exact le_abs_self _)
  have hn := EuclideanSpace.norm_toLp_le_mul_add_of_forall_abs_le hc
    (show 0 ≤ n.eval * (1 + u tag) ^ (2 * n.eval) * (2 + u tag) * η tag by positivity)
    hpoint
  have hF : frobNorm (M.map abs) = frobNorm M := by simp [frobNorm]
  have hxnorm : ‖WithLp.toLp 2 (fun j => |xv j|)‖ = ‖WithLp.toLp 2 xv‖ := by
    simpa only [Real.norm_eq_abs] using EuclideanSpace.norm_toLp_norm xv
  refine ⟨out, W, hrun, hwrite, hn.trans ?_⟩
  simpa only [Fintype.card_fin, hF, hxnorm, mul_assoc] using
    add_le_add (mul_le_mul_of_nonneg_left
      (norm_toLp_mulVec_le_frobNorm_mul (M.map abs) (fun j => |xv j|)) hc) (le_refl _)

/-- The actual rectangular `gemv` run has Euclidean error at most
$(P-1)\sqrt n\|\mathbf{A}\|_2\|\mathbf{x}\|+\sqrt m D$ under nonnegative allowances,
decoded inputs, writable disjoint output, exact addition of zero, and the input-only safe
radius condition $P\sum_j\lvert a_{ij}x_j\rvert+D\le L$ for every row, where
$P=(1+u)^{2n}$ and $D=nP(2+u)\eta$. No smallness condition on $nu$ is needed.
This is the Frobenius-to-spectral consequence of [Higham2002, §3.5]. -/
theorem IsArithErrSem.exec_gemv_norm_sub_le_specNorm_mul_of_absRelErr
    (h : IsArithErrSem (fun p _ => AbsRelErr (u p) (η p)) dec safe I.sem)
    (hz : AddsZeroExactly dec I.sem) (m n : IExp ℕ) (A : ℕ) (ao : IExp ℕ)
    (x : ℕ) (xo : IExp ℕ) (y : ℕ) (yo : IExp ℕ)
    (M : Matrix (Fin m.eval) (Fin n.eval) ℝ) (xv : Fin n.eval → ℝ)
    (L : ℝ) (hu : 0 ≤ u tag) (hη : 0 ≤ η tag)
    (hA : HoldsDecoded st.store dec tag A ao.eval M)
    (hx : ∀ j : Fin n.eval, ∃ w, st.store.read tag x (xo.eval + j) = some w ∧
      dec tag w = xv j)
    (hyA : y = A → yo.eval + m.eval ≤ ao.eval ∨ ao.eval + m.eval * n.eval ≤ yo.eval)
    (hyx : y = x → yo.eval + m.eval ≤ xo.eval ∨ xo.eval + n.eval ≤ yo.eval)
    (hy : ∀ i < m.eval, ∃ v s, st.store.write tag y (yo.eval + i) v = some s)
    (hinput : ∀ i : Fin m.eval,
      (1 + u tag) ^ (2 * n.eval) * (∑ j, |M i j * xv j|) +
        n.eval * (1 + u tag) ^ (2 * n.eval) * (2 + u tag) * η tag ≤ L)
    (hball : ∀ b, |b| ≤ L → safe tag b) :
    ∃ out, ∃ W : ℕ → K, exec I (gemv tag m n A ao x xo y yo).run st = some out ∧
      st.store.writeBlock tag y yo.eval ((List.range m.eval).toArray.map W) = some out.store ∧
      ‖WithLp.toLp 2 (M *ᵥ xv - fun i : Fin m.eval => dec tag (W i))‖ ≤
        ((1 + u tag) ^ (2 * n.eval) - 1) * Real.sqrt n.eval * specNorm M *
          ‖WithLp.toLp 2 xv‖ +
        Real.sqrt m.eval * (n.eval * (1 + u tag) ^ (2 * n.eval) * (2 + u tag) * η tag) := by
  obtain ⟨out, W, hrun, hwrite, herr⟩ :=
    h.exec_gemv_norm_sub_le_frobNorm_mul_of_absRelErr I tag st hz m n A ao x xo y yo
      M xv L hu hη hA hx hyA hyx hy hinput hball
  have hc : 0 ≤ (1 + u tag) ^ (2 * n.eval) - 1 :=
    sub_nonneg.mpr (one_le_pow₀ (by linarith))
  refine ⟨out, W, hrun, hwrite, herr.trans ?_⟩
  have hF := frobNorm_le_sqrt_card_mul_specNorm M
  simp only [Fintype.card_fin] at hF
  calc
    _ ≤ ((1 + u tag) ^ (2 * n.eval) - 1) * (Real.sqrt n.eval * specNorm M) *
        ‖WithLp.toLp 2 xv‖ +
        Real.sqrt m.eval * (n.eval * (1 + u tag) ^ (2 * n.eval) * (2 + u tag) * η tag) := by
      gcongr
    _ = _ := by ring

/-- The actual rectangular `gemm` run succeeds and changes only its output block under
decoded column-major inputs, writable output, and disjointness assumptions. Assume
$u,\eta\ge0$, exact addition of zero, and a safe radius $L$. For each output entry, require
$P\sum_k\lvert a_{ik}b_{kj}\rvert+D\le L$, where $P=(1+u)^{2n}$ and $D=nP(2+u)\eta$.
Its Frobenius error is at most
$(P-1)\|\mathbf{A}\|_{\mathsf{F}}\|\mathbf{B}\|_{\mathsf{F}}+\sqrt{ml}D$.
No smallness condition on $nu$ is needed. [Higham2002, §2.2 and §3.5]. -/
theorem IsArithErrSem.exec_gemm_frobNorm_sub_le_of_absRelErr
    (h : IsArithErrSem (fun p _ => AbsRelErr (u p) (η p)) dec safe I.sem)
    (hz : AddsZeroExactly dec I.sem) (m n l : IExp ℕ) (A : ℕ) (ao : IExp ℕ)
    (B : ℕ) (bo : IExp ℕ) (Cb : ℕ) (co : IExp ℕ)
    (M : Matrix (Fin m.eval) (Fin n.eval) ℝ) (N : Matrix (Fin n.eval) (Fin l.eval) ℝ)
    (L : ℝ) (hu : 0 ≤ u tag) (hη : 0 ≤ η tag)
    (hA : HoldsDecoded st.store dec tag A ao.eval M)
    (hB : HoldsDecoded st.store dec tag B bo.eval N)
    (hCA : Cb = A → co.eval + m.eval * l.eval ≤ ao.eval ∨ ao.eval + m.eval * n.eval ≤ co.eval)
    (hCB : Cb = B → co.eval + m.eval * l.eval ≤ bo.eval ∨ bo.eval + n.eval * l.eval ≤ co.eval)
    (hC : ∀ k < m.eval * l.eval, ∃ v s, st.store.write tag Cb (co.eval + k) v = some s)
    (hinput : ∀ (i : Fin m.eval) (j : Fin l.eval),
      (1 + u tag) ^ (2 * n.eval) * (∑ k, |M i k * N k j|) +
        n.eval * (1 + u tag) ^ (2 * n.eval) * (2 + u tag) * η tag ≤ L)
    (hball : ∀ b, |b| ≤ L → safe tag b) :
    ∃ out, ∃ W : ℕ → K, exec I (gemm tag m n l A ao B bo Cb co).run st = some out ∧
      st.store.writeBlock tag Cb co.eval ((List.range (m.eval * l.eval)).toArray.map W) =
        some out.store ∧
      frobNorm (M * N - Matrix.of fun (i : Fin m.eval) (j : Fin l.eval) =>
        dec tag (W (i + m.eval * j))) ≤
        ((1 + u tag) ^ (2 * n.eval) - 1) * frobNorm M * frobNorm N +
        Real.sqrt ((m.eval * l.eval : ℕ) : ℝ) *
          (n.eval * (1 + u tag) ^ (2 * n.eval) * (2 + u tag) * η tag) := by
  obtain ⟨out, W, hrun, hwrite, herr⟩ :=
    h.exec_gemm_abs_sum_mul_sub_le_of_absRelErr I tag hz st m n l A ao B bo Cb co
      (fun i k => if h : i < m.eval ∧ k < n.eval then M ⟨i, h.1⟩ ⟨k, h.2⟩ else 0)
      (fun k j => if h : k < n.eval ∧ j < l.eval then N ⟨k, h.1⟩ ⟨j, h.2⟩ else 0)
      L hu hη (fun i hi k hk => by simpa [hi, hk] using hA ⟨i, hi⟩ ⟨k, hk⟩)
      (fun k hk j hj => by simpa [hk, hj] using hB ⟨k, hk⟩ ⟨j, hj⟩) hCA hCB hC
      (fun i hi j hj => by
        rw [← Fin.sum_univ_eq_sum_range]
        simpa [hi, hj] using hinput ⟨i, hi⟩ ⟨j, hj⟩) hball
  have hc : 0 ≤ (1 + u tag) ^ (2 * n.eval) - 1 :=
    sub_nonneg.mpr (one_le_pow₀ (by linarith))
  let E : Matrix (Fin m.eval) (Fin l.eval) ℝ :=
    M * N - Matrix.of fun (i : Fin m.eval) (j : Fin l.eval) =>
      dec tag (W (i + m.eval * j))
  have hpoint (ij : Fin m.eval × Fin l.eval) :
      |Function.uncurry E ij| ≤ ((1 + u tag) ^ (2 * n.eval) - 1) *
        |Function.uncurry (M.map abs * N.map abs) ij| +
        n.eval * (1 + u tag) ^ (2 * n.eval) * (2 + u tag) * η tag := by
    have hr := herr ij.1 ij.1.isLt ij.2 ij.2.isLt
    rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range] at hr
    have hr' : |Function.uncurry E ij| ≤ ((1 + u tag) ^ (2 * n.eval) - 1) *
        Function.uncurry (M.map abs * N.map abs) ij +
          n.eval * (1 + u tag) ^ (2 * n.eval) * (2 + u tag) * η tag := by
      simpa [E, Function.uncurry, Matrix.mul_apply, ij.1.isLt, ij.2.isLt, abs_mul] using hr
    exact hr'.trans (by gcongr; exact le_abs_self _)
  have hn := EuclideanSpace.norm_toLp_le_mul_add_of_forall_abs_le hc
    (show 0 ≤ n.eval * (1 + u tag) ^ (2 * n.eval) * (2 + u tag) * η tag by positivity)
    hpoint
  rw [← frobNorm_eq_norm_toLp_uncurry, ← frobNorm_eq_norm_toLp_uncurry] at hn
  have hM : frobNorm (M.map abs) = frobNorm M := by simp [frobNorm]
  have hN : frobNorm (N.map abs) = frobNorm N := by simp [frobNorm]
  refine ⟨out, W, hrun, hwrite, hn.trans ?_⟩
  simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, hM, hN, mul_assoc] using
    add_le_add (mul_le_mul_of_nonneg_left
      (frobNorm_mul_le (M.map abs) (N.map abs)) hc) (le_refl _)

end NLAlib.Computation
