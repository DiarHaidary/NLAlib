/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BLAS.RoundingErrors
public import NLAlib.ForMathlib.Analysis.InnerProductSpace.PiL2
public import NLAlib.Matrix.Norms.Compare

/-!
# Euclidean error bounds for rounded BLAS executions

The actual decoded outputs of `dot`, `axpy` and `gemv` satisfy Euclidean norm
bounds under the input-only relative-error arithmetic contract. Successful execution
and the precise storage write witnesses are retained from the componentwise bounds
of [Higham2002]. These are arithmetic-contract results, not an IEEE implementation
instance.

## Main results

* `NLAlib.Computation.IsRelErrSem.exec_dot_abs_dotProduct_sub_le`: normwise dot error.
* `NLAlib.Computation.IsRelErrSem.exec_dot_self_relErr`: relative self-dot error, including zero.
* `NLAlib.Computation.IsRelErrSem.exec_axpy_norm_sub_le`: Euclidean axpy error.
* `NLAlib.Computation.IsRelErrSem.exec_gemv_norm_sub_le_frobNorm_mul`: Frobenius gemv bound.
* `NLAlib.Computation.IsRelErrSem.exec_gemv_norm_sub_le_specNorm_mul`: spectral gemv bound.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Computation

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]
  (I : Interp P ι K C) (p : P) (st : St P K C)
  {dec : P → K → ℝ} {u : P → ℝ}

/-- Normwise forward error of the actual `dot` run under the input-only relative-error
contract, exact addition of zero and $nu_p < 1$, with decoded inputs and a disjoint writable
destination. Cauchy–Schwarz applied to [Higham2002, (3.5)]. -/
theorem IsRelErrSem.exec_dot_abs_dotProduct_sub_le (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem) (dst : Cell ℕ ℕ) (x : ℕ) (xo : IExp ℕ) (y : ℕ)
    (yo n : IExp ℕ) (xs ys : ℕ → ℝ) (hn : n.eval * u p < 1)
    (hx : ∀ i < n.eval, ∃ w, st.store.read p x (xo.eval + i) = some w ∧ dec p w = xs i)
    (hy : ∀ i < n.eval, ∃ w, st.store.read p y (yo.eval + i) = some w ∧ dec p w = ys i)
    (hdx : dst.buf = x → ∀ i < n.eval, dst.idx.eval ≠ xo.eval + i)
    (hdy : dst.buf = y → ∀ i < n.eval, dst.idx.eval ≠ yo.eval + i)
    (hdst : ∃ v s₁, st.store.write p dst.buf dst.idx.eval v = some s₁) :
    ∃ st' w, exec I (dot p dst x xo y yo n).run st = some st' ∧
      st.store.write p dst.buf dst.idx.eval w = some st'.store ∧
      |(fun i : Fin n.eval => xs i) ⬝ᵥ (fun i : Fin n.eval => ys i) - dec p w| ≤
        roundingFactor n.eval (u p) * ‖WithLp.toLp 2 (fun i : Fin n.eval => xs i)‖ *
          ‖WithLp.toLp 2 (fun i : Fin n.eval => ys i)‖ := by
  obtain ⟨st', w, hrun, hwrite, herr⟩ := h.exec_dot_abs_sum_mul_sub_le I p st
    hz dst x xo y yo n xs ys hn hx hy hdx hdy hdst
  refine ⟨st', w, hrun, hwrite, ?_⟩
  have hsum : (∑ i ∈ Finset.range n.eval, |xs i| * |ys i|) ≤
      ‖WithLp.toLp 2 (fun i : Fin n.eval => xs i)‖ *
        ‖WithLp.toLp 2 (fun i : Fin n.eval => ys i)‖ := by
    rw [← Fin.sum_univ_eq_sum_range]
    calc
      _ ≤ |(fun i : Fin n.eval => |xs i|) ⬝ᵥ (fun i : Fin n.eval => |ys i|)| :=
        le_abs_self _
      _ ≤ _ := by
        simpa [EuclideanSpace.norm_eq] using EuclideanSpace.abs_dotProduct_le_norm
          (fun i : Fin n.eval => |xs i|) (fun i : Fin n.eval => |ys i|)
  rw [← Fin.sum_univ_eq_sum_range] at herr
  exact herr.trans (by simpa [mul_assoc] using
    mul_le_mul_of_nonneg_left hsum (roundingFactor_nonneg (h.nonneg trivial) hn))

/-- Relative forward error of the actual self-`dot` run under the input-only relative-error
contract, exact addition of zero, $nu_p < 1$, decoded inputs and a disjoint writable
destination. Zero vectors are permitted. This is [Higham2002, (3.5)] without cancellation. -/
theorem IsRelErrSem.exec_dot_self_relErr (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem) (dst : Cell ℕ ℕ) (x : ℕ) (xo n : IExp ℕ)
    (xs : ℕ → ℝ) (hn : n.eval * u p < 1)
    (hx : ∀ i < n.eval, ∃ w, st.store.read p x (xo.eval + i) = some w ∧ dec p w = xs i)
    (hdx : dst.buf = x → ∀ i < n.eval, dst.idx.eval ≠ xo.eval + i)
    (hdst : ∃ v s₁, st.store.write p dst.buf dst.idx.eval v = some s₁) :
    ∃ st' w, exec I (dot p dst x xo x xo n).run st = some st' ∧
      st.store.write p dst.buf dst.idx.eval w = some st'.store ∧
      RelErr (roundingFactor n.eval (u p))
        (‖WithLp.toLp 2 (fun i : Fin n.eval => xs i)‖ ^ 2) (dec p w) := by
  obtain ⟨st', w, hrun, hwrite, herr⟩ := h.exec_dot_abs_dotProduct_sub_le I p st
    hz dst x xo x xo n xs xs hn hx hx hdx hdx hdst
  refine ⟨st', w, hrun, hwrite, ?_⟩
  rw [← EuclideanSpace.norm_toLp_sq_eq_dotProduct_self] at herr
  have herr' : |‖WithLp.toLp 2 (fun i : Fin n.eval => xs i)‖ ^ 2 - dec p w| ≤
      roundingFactor n.eval (u p) * ‖WithLp.toLp 2 (fun i : Fin n.eval => xs i)‖ ^ 2 := by
    simpa [pow_two, mul_assoc] using herr
  have hq : 0 ≤ ‖WithLp.toLp 2 (fun i : Fin n.eval => xs i)‖ ^ 2 := sq_nonneg _
  generalize ‖WithLp.toLp 2 (fun i : Fin n.eval => xs i)‖ ^ 2 = q at herr' hq ⊢
  by_cases hzero : q = 0
  · refine ⟨0, by simpa using roundingFactor_nonneg (h.nonneg trivial) hn, ?_⟩
    simp only [hzero, zero_sub, abs_neg, mul_zero] at herr'
    have hw := abs_eq_zero.mp (le_antisymm herr' (abs_nonneg _))
    simp [hzero, hw]
  · refine ⟨(dec p w - q) / q, ?_, ?_⟩
    · rw [abs_div, abs_of_pos (lt_of_le_of_ne hq (Ne.symm hzero))]
      exact (div_le_iff₀ (lt_of_le_of_ne hq (Ne.symm hzero))).2
        (by simpa [abs_sub_comm] using herr')
    · field_simp [hzero]
      ring

/-- Euclidean forward error of the actual `axpy` run under the input-only relative-error
contract and $2u_p < 1$, with decoded inputs, a scalar outside the output, and equal or
disjoint vector blocks. The two-operation bound of [Higham2002, §2.2] in Euclidean norm. -/
theorem IsRelErrSem.exec_axpy_norm_sub_le
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (a : Cell ℕ ℕ)
    (x : ℕ) (xo : IExp ℕ) (y : ℕ) (yo n : IExp ℕ) (av : ℝ) (xs ys : ℕ → ℝ) (hu : 2 * u p < 1)
    (ha : ∃ w, st.store.read p a.buf a.idx.eval = some w ∧ dec p w = av)
    (hx : ∀ i < n.eval, ∃ w, st.store.read p x (xo.eval + i) = some w ∧ dec p w = xs i)
    (hy : ∀ i < n.eval, ∃ w, st.store.read p y (yo.eval + i) = some w ∧ dec p w = ys i)
    (hay : a.buf = y → ∀ i < n.eval, a.idx.eval ≠ yo.eval + i)
    (hxy : x = y → ∀ i < n.eval, ∀ j < n.eval, xo.eval + i = yo.eval + j → i = j) :
    ∃ st', ∃ W : ℕ → K, exec I (axpy p a x xo y yo n).run st = some st' ∧
      st.store.writeBlock p y yo.eval ((List.range n.eval).toArray.map W) = some st'.store ∧
      ‖WithLp.toLp 2 (fun i : Fin n.eval => ys i + av * xs i - dec p (W i))‖ ≤
        roundingFactor 2 (u p) * (‖WithLp.toLp 2 (fun i : Fin n.eval => ys i)‖ +
          |av| * ‖WithLp.toLp 2 (fun i : Fin n.eval => xs i)‖) := by
  obtain ⟨st', W, hrun, hwrite, hW⟩ := h.exec_axpy I p st a x xo y yo n av xs ys
    hu ha hx hy hay hxy
  refine ⟨st', W, hrun, hwrite, ?_⟩
  have hγ := roundingFactor_nonneg (h.nonneg trivial) hu
  have huγ : u p ≤ roundingFactor 2 (u p) := by
    have := le_roundingFactor (h.nonneg trivial) hu
    norm_num at this
    linarith [h.nonneg (p := p) trivial]
  have hpoint (i : Fin n.eval) :
      |ys i + av * xs i - dec p (W i)| ≤
        roundingFactor 2 (u p) * (|ys i| + |av| * |xs i|) := by
    obtain ⟨θ, δ, hθ, hδ, hw⟩ := hW i i.isLt
    rw [hw]
    calc
      _ = |-(ys i * δ + av * xs i * θ)| := by congr 1; ring
      _ ≤ |ys i * δ| + |av * xs i * θ| := by rw [abs_neg]; exact abs_add_le _ _
      _ ≤ |ys i| * roundingFactor 2 (u p) +
          (|av| * |xs i|) * roundingFactor 2 (u p) := by
        simp only [abs_mul]
        gcongr
        exact hδ.trans huγ
      _ = _ := by ring
  have hnorm := EuclideanSpace.norm_toLp_le_norm_toLp
    (x := fun i : Fin n.eval => ys i + av * xs i - dec p (W i))
    (y := roundingFactor 2 (u p) •
      ((fun i : Fin n.eval => |ys i|) + |av| • (fun i : Fin n.eval => |xs i|)))
    (fun i => by
      change |ys i + av * xs i - dec p (W i)| ≤
        |roundingFactor 2 (u p) * (|ys i| + |av| * |xs i|)|
      rw [abs_mul, abs_of_nonneg hγ,
        abs_of_nonneg (show 0 ≤ |ys i| + |av| * |xs i| by positivity)]
      exact hpoint i)
  have habs (z : Fin n.eval → ℝ) : ‖WithLp.toLp 2 (fun i => |z i|)‖ =
      ‖WithLp.toLp 2 z‖ := by simp [EuclideanSpace.norm_eq]
  calc
    _ ≤ _ := hnorm
    _ = roundingFactor 2 (u p) * ‖WithLp.toLp 2
        ((fun i : Fin n.eval => |ys i|) + |av| • (fun i : Fin n.eval => |xs i|))‖ := by
      rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ]
    _ ≤ _ := by
      rw [WithLp.toLp_add, WithLp.toLp_smul]
      exact mul_le_mul_of_nonneg_left (norm_add_le _ _) hγ |>.trans_eq (by
        rw [norm_smul, Real.norm_eq_abs, abs_abs, habs, habs])

/-- Frobenius-norm forward error of the actual rectangular `gemv` run under the input-only
relative-error contract, exact addition of zero, $nu_p < 1$, decoded inputs, and a writable
output block disjoint from both inputs. The Euclidean consequence of [Higham2002, (3.12)]. -/
theorem IsRelErrSem.exec_gemv_norm_sub_le_frobNorm_mul
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem) (m n : IExp ℕ) (A : ℕ) (ao : IExp ℕ) (x : ℕ) (xo : IExp ℕ)
    (y : ℕ) (yo : IExp ℕ) (M : Matrix (Fin m.eval) (Fin n.eval) ℝ) (xv : Fin n.eval → ℝ)
    (hn : n.eval * u p < 1) (hA : HoldsDecoded st.store dec p A ao.eval M)
    (hx : ∀ j : Fin n.eval, ∃ w, st.store.read p x (xo.eval + j) = some w ∧ dec p w = xv j)
    (hyA : y = A → yo.eval + m.eval ≤ ao.eval ∨ ao.eval + m.eval * n.eval ≤ yo.eval)
    (hyx : y = x → yo.eval + m.eval ≤ xo.eval ∨ xo.eval + n.eval ≤ yo.eval)
    (hy : ∀ i < m.eval, ∃ v s₁, st.store.write p y (yo.eval + i) v = some s₁) :
    ∃ st', ∃ W : ℕ → K, exec I (gemv p m n A ao x xo y yo).run st = some st' ∧
      st.store.writeBlock p y yo.eval ((List.range m.eval).toArray.map W) = some st'.store ∧
      ‖WithLp.toLp 2 (M *ᵥ xv - fun i : Fin m.eval => dec p (W i))‖ ≤
        roundingFactor n.eval (u p) * frobNorm M * ‖WithLp.toLp 2 xv‖ := by
  obtain ⟨st', W, hrun, hwrite, herr⟩ := h.exec_gemv_abs_mulVec_sub_le I p st
    hz m n A ao x xo y yo M xv hn hA hx hyA hyx hy
  refine ⟨st', W, hrun, hwrite, ?_⟩
  have hγ := roundingFactor_nonneg (h.nonneg trivial) hn
  have hnorm := EuclideanSpace.norm_toLp_le_norm_toLp
    (x := M *ᵥ xv - fun i : Fin m.eval => dec p (W i))
    (y := roundingFactor n.eval (u p) • ((M.map abs) *ᵥ (fun j => |xv j|)))
    (fun i => by
      simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg hγ] using
        (herr i).trans (mul_le_mul_of_nonneg_left (le_abs_self _) hγ))
  have hF : frobNorm (M.map abs) = frobNorm M := by simp [frobNorm]
  have hxnorm : ‖WithLp.toLp 2 (fun j => |xv j|)‖ = ‖WithLp.toLp 2 xv‖ := by
    simp [EuclideanSpace.norm_eq]
  calc
    _ ≤ _ := hnorm
    _ = roundingFactor n.eval (u p) *
        ‖WithLp.toLp 2 ((M.map abs) *ᵥ (fun j => |xv j|))‖ := by
      rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ]
    _ ≤ _ := by
      simpa [hF, hxnorm, mul_assoc] using mul_le_mul_of_nonneg_left
        (norm_toLp_mulVec_le_frobNorm_mul (M.map abs) (fun j => |xv j|)) hγ

/-- Spectral-norm forward error of the actual rectangular `gemv` run under the input-only
relative-error contract, exact addition of zero, $nu_p < 1$, decoded inputs, and a writable
output block disjoint from both inputs. Uses the column dimension in the Frobenius-to-spectral
comparison, together with [Higham2002, (3.12)]. -/
theorem IsRelErrSem.exec_gemv_norm_sub_le_specNorm_mul
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem) (m n : IExp ℕ) (A : ℕ) (ao : IExp ℕ) (x : ℕ) (xo : IExp ℕ)
    (y : ℕ) (yo : IExp ℕ) (M : Matrix (Fin m.eval) (Fin n.eval) ℝ) (xv : Fin n.eval → ℝ)
    (hn : n.eval * u p < 1) (hA : HoldsDecoded st.store dec p A ao.eval M)
    (hx : ∀ j : Fin n.eval, ∃ w, st.store.read p x (xo.eval + j) = some w ∧ dec p w = xv j)
    (hyA : y = A → yo.eval + m.eval ≤ ao.eval ∨ ao.eval + m.eval * n.eval ≤ yo.eval)
    (hyx : y = x → yo.eval + m.eval ≤ xo.eval ∨ xo.eval + n.eval ≤ yo.eval)
    (hy : ∀ i < m.eval, ∃ v s₁, st.store.write p y (yo.eval + i) v = some s₁) :
    ∃ st', ∃ W : ℕ → K, exec I (gemv p m n A ao x xo y yo).run st = some st' ∧
      st.store.writeBlock p y yo.eval ((List.range m.eval).toArray.map W) = some st'.store ∧
      ‖WithLp.toLp 2 (M *ᵥ xv - fun i : Fin m.eval => dec p (W i))‖ ≤
        roundingFactor n.eval (u p) * √(n.eval : ℝ) * specNorm M * ‖WithLp.toLp 2 xv‖ := by
  obtain ⟨st', W, hrun, hwrite, herr⟩ := h.exec_gemv_norm_sub_le_frobNorm_mul I p st
    hz m n A ao x xo y yo M xv hn hA hx hyA hyx hy
  refine ⟨st', W, hrun, hwrite, herr.trans ?_⟩
  have hγ := roundingFactor_nonneg (h.nonneg trivial) hn
  have hF := frobNorm_le_sqrt_card_mul_specNorm M
  simp only [Fintype.card_fin] at hF
  calc
    _ ≤ roundingFactor n.eval (u p) * (√(n.eval : ℝ) * specNorm M) *
        ‖WithLp.toLp 2 xv‖ := by gcongr
    _ = _ := by ring

end NLAlib.Computation
