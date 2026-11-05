/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Underflow
public import NLAlib.Computation.BLAS.RoundingErrors
public import NLAlib.Computation.VectorErrors

/-!
# BLAS kernels with absolute rounding errors

The actual `dot` kernel produces a trace under the existing arithmetic contract, including
its explicit range assumptions. This file bounds that trace when each multiplication and
addition permits both relative and absolute error. An absolute allowance describes gradual
underflow or fixed-point quantization; it does not imply that operations avoid overflow.

The geometric bound is valid for every nonnegative relative allowance, without a condition
on the product of dimension and precision. It is conservative: the pure relative bounds in
`RoundingErrors.lean` exploit exact zero addition to count fewer rounding factors.
[Higham2002, §2.2 and §3.1].

## Main results

* `NLAlib.Computation.IsDotTrace.abs_sum_mul_sub_le_of_absRelErr`: mixed-error trace bound.
* `NLAlib.Computation.IsDotTrace.abs_add_le_of_absRelErr`:
  input-only range control for the next accumulation with mixed errors.
* `NLAlib.Computation.IsDotTrace.abs_add_le_of_absRelErr_zero`:
  input-only range control for the next accumulation with absolute errors.
* `NLAlib.Computation.IsArithErrSem.exec_dot_abs_sum_mul_sub_le_of_absRelErr`:
  actual range-certified execution and error bound.
* `NLAlib.Computation.IsArithErrSem.exec_axpy_norm_sub_le_of_absRelErr`:
  Euclidean error and input-only range control for the actual vector update.
* `NLAlib.Computation.IsArithErrSem.exec_gemv_abs_sum_mul_sub_le_of_absRelErr`,
  `NLAlib.Computation.IsArithErrSem.exec_gemm_abs_sum_mul_sub_le_of_absRelErr`:
  componentwise matrix-product errors with input-only range control.
-/

@[expose] public section

namespace NLAlib.Computation

private theorem abs_add_sub_le_of_absRelErr {u η S s a q z B E : ℝ}
    (hu : 0 ≤ u) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hm : AbsRelErr u η a q) (ha : AbsRelErr u η (s + q) z)
    (hS : |S - s| ≤ E) (hb : |S| ≤ B) :
    |S + a - z| ≤ (1 + u) ^ 2 * E + ((1 + u) ^ 2 - 1) * (B + |a|) +
      (2 + u) * η := by
  have hs : |s| ≤ B + E := by
    calc
      |s| = |S - (S - s)| := by congr 1; ring
      _ ≤ |S| + |S - s| := abs_sub _ _
      _ ≤ B + E := add_le_add hb hS
  have hsq : |s + q| ≤ B + E + ((1 + u) * |a| + η) :=
    (abs_add_le _ _).trans (add_le_add hs hm.abs_le)
  have hz : |S + a - z| ≤ E + (u * |a| + η) +
      (u * (B + E + ((1 + u) * |a| + η)) + η) := by
    calc
      |S + a - z| = |(S - s) + (a - q) + (s + q - z)| := by congr 1; ring
      _ ≤ |S - s| + |a - q| + |s + q - z| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ _ := add_le_add (add_le_add hS hm.abs_sub_le)
        (ha.abs_sub_le.trans (by gcongr))
  have h₁ : 0 ≤ (u + u ^ 2) * E := mul_nonneg (by positivity) hE
  have h₂ : 0 ≤ (u + u ^ 2) * B := mul_nonneg (by positivity) hB
  nlinarith

/-- A dot trace with relative allowance $u \ge 0$ and absolute allowance $\eta \ge 0$ on
each product and addition has error at most
$$\bigl((1+u)^{2n}-1\bigr)\sum_{i<n}\lvert x_i y_i\rvert
  \quad + n(1+u)^{2n}(2+u)\eta\,.$$
No smallness assumption on $nu$ is needed. This supports underflow-aware consumers of the
actual kernel; it is not a no-overflow assertion. [Higham2002, §2.2 and §3.1]. -/
theorem IsDotTrace.abs_sum_mul_sub_le_of_absRelErr {u η : ℝ}
    (hu : 0 ≤ u) (hη : 0 ≤ η) {x y s : ℕ → ℝ} {n : ℕ}
    (h : IsDotTrace (fun _ => AbsRelErr u η) x y n s) :
    |∑ k ∈ Finset.range n, x k * y k - s n| ≤
      ((1 + u) ^ (2 * n) - 1) * (∑ k ∈ Finset.range n, |x k * y k|) +
      n * (1 + u) ^ (2 * n) * (2 + u) * η := by
  have hb : 1 ≤ 1 + u := by linarith
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, h.1, sub_self,
      abs_zero, mul_zero, Nat.cast_zero, zero_mul, add_zero, le_refl]
  | succ n ih =>
    have ht : IsDotTrace (fun _ => AbsRelErr u η) x y n s :=
      ⟨h.1, fun k hk => h.2 k (by omega)⟩
    have hp : 1 ≤ (1 + u) ^ (2 * n) := one_le_pow₀ hb
    have hpow : (1 + u) ^ (2 * (n + 1)) = (1 + u) ^ (2 * n) * (1 + u) ^ 2 := by
      rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
    have hp₂ : 1 ≤ (1 + u) ^ 2 := one_le_pow₀ hb
    let B : ℝ := ∑ k ∈ Finset.range n, |x k * y k|
    let E : ℝ := ((1 + u) ^ (2 * n) - 1) * B + n * (1 + u) ^ (2 * n) * (2 + u) * η
    have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hE : 0 ≤ E := by dsimp [E]; positivity
    have hs : |∑ k ∈ Finset.range n, x k * y k - s n| ≤ E := ih ht
    obtain ⟨q, hm, ha, _⟩ := h.2 n (by omega)
    have hstep := abs_add_sub_le_of_absRelErr hu hB hE hm ha hs
      (Finset.abs_sum_le_sum_abs _ _)
    rw [Finset.sum_range_succ, Finset.sum_range_succ, hpow, Nat.cast_add, Nat.cast_one]
    have hp₀ : 0 ≤ (1 + u) ^ (2 * n) := by positivity
    have hc₀ : 0 ≤ (2 + u) * η := mul_nonneg (by linarith) hη
    have htail : 0 ≤ ((1 + u) ^ (2 * n) * (1 + u) ^ 2 - 1) * ((2 + u) * η) :=
      mul_nonneg (by nlinarith) hc₀
    have hprod : 0 ≤ ((1 + u) ^ (2 * n) - 1) * (1 + u) ^ 2 * |x n * y n| :=
      mul_nonneg (mul_nonneg (by linarith) (by positivity)) (abs_nonneg _)
    dsimp [E, B] at hstep
    nlinarith [sq_nonneg (1 + u)]

/-- Every next exact accumulation in a mixed-error dot prefix of length $k<N$ has magnitude
at most
$$ (1+u)^{2N}\sum_{i<N}\lvert x_i y_i\rvert + N(1+u)^{2N}(2+u)\eta\,.$$
The allowances $u$ and $\eta$ must be nonnegative. This input-only bound can discharge a
finite-format backend's range condition without observing intermediate states, and does not
require a dimension-precision smallness assumption. -/
theorem IsDotTrace.abs_add_le_of_absRelErr {u η : ℝ} {x y s : ℕ → ℝ}
    {k N : ℕ} {q : ℝ} (h : IsDotTrace (fun _ => AbsRelErr u η) x y k s)
    (hu : 0 ≤ u) (hη : 0 ≤ η) (hkn : k < N) (hq : AbsRelErr u η (x k * y k) q) :
    |s k + q| ≤ (1 + u) ^ (2 * N) * (∑ i ∈ Finset.range N, |x i * y i|) +
      N * (1 + u) ^ (2 * N) * (2 + u) * η := by
  have hb : 1 ≤ 1 + u := by linarith
  have hPN : 1 ≤ (1 + u) ^ (2 * N) := one_le_pow₀ hb
  have hPk : (1 + u) ^ (2 * k) ≤ (1 + u) ^ (2 * N) :=
    pow_le_pow_right₀ hb (by omega)
  have hbN : 1 + u ≤ (1 + u) ^ (2 * N) := by
    calc
      1 + u = (1 + u) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hb (by omega)
  have herr := h.abs_sum_mul_sub_le_of_absRelErr hu hη
  have hs : |s k| ≤ (1 + u) ^ (2 * k) * (∑ i ∈ Finset.range k, |x i * y i|) +
      k * (1 + u) ^ (2 * k) * (2 + u) * η := by
    calc
      |s k| = |(∑ i ∈ Finset.range k, x i * y i) -
          ((∑ i ∈ Finset.range k, x i * y i) - s k)| := by congr 1; ring
      _ ≤ |∑ i ∈ Finset.range k, x i * y i| +
          |(∑ i ∈ Finset.range k, x i * y i) - s k| := abs_sub _ _
      _ ≤ _ := (add_le_add (Finset.abs_sum_le_sum_abs _ _) herr).trans_eq (by ring)
  have hsum : (∑ i ∈ Finset.range k, |x i * y i|) + |x k * y k| ≤
      ∑ i ∈ Finset.range N, |x i * y i| := by
    rw [← Finset.sum_range_succ]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hkn)
      (fun _ _ _ => abs_nonneg _)
  have hsN : |s k| ≤ (1 + u) ^ (2 * N) * (∑ i ∈ Finset.range k, |x i * y i|) +
      k * (1 + u) ^ (2 * N) * (2 + u) * η := hs.trans (by gcongr)
  have hqN : |q| ≤ (1 + u) ^ (2 * N) * |x k * y k| + η :=
    hq.abs_le.trans (by gcongr)
  have hpadding : η ≤ (1 + u) ^ (2 * N) * (2 + u) * η := by
    have : 1 ≤ (1 + u) ^ (2 * N) * (2 + u) := by nlinarith
    exact le_mul_of_one_le_left hη this
  have hsumN := mul_le_mul_of_nonneg_left hsum
    (show 0 ≤ (1 + u) ^ (2 * N) by positivity)
  have hcount : (k : ℝ) + 1 ≤ N := by exact_mod_cast hkn
  have htail := mul_le_mul_of_nonneg_right hcount
    (show 0 ≤ (1 + u) ^ (2 * N) * (2 + u) * η by positivity)
  have hbound := (abs_add_le (s k) q).trans (add_le_add hsN hqN)
  nlinarith

/-- With absolute allowance $\eta\ge0$ and zero relative allowance, every next exact
accumulation in a dot trace of length $k<N$ has magnitude at most
$\sum_{i<N}\lvert x_i y_i\rvert+2N\eta$. This bound uses only input entries, dimension and
precision; it can discharge a backend's safe-range condition without observing intermediate
states. -/
theorem IsDotTrace.abs_add_le_of_absRelErr_zero {η : ℝ} {x y s : ℕ → ℝ}
    {k N : ℕ} {q : ℝ} (h : IsDotTrace (fun _ => AbsRelErr 0 η) x y k s)
    (hη : 0 ≤ η) (hkn : k < N) (hq : AbsRelErr 0 η (x k * y k) q) :
    |s k + q| ≤ (∑ i ∈ Finset.range N, |x i * y i|) + 2 * N * η := by
  have hbound := h.abs_add_le_of_absRelErr (by norm_num) hη hkn hq
  simpa only [add_zero, one_pow, one_mul, mul_one, mul_comm (N : ℝ) 2] using hbound

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]
  {u η : P → ℝ} {dec : P → K → ℝ} {safe : P → ℝ → Prop}

/-- The actual `dot` kernel succeeds when every next product and accumulation is in range,
and its returned word satisfies the mixed-error trace bound. Only the destination cell changes
in the final store. Relative and absolute allowances must be nonnegative at the kernel tag;
no dimension-precision smallness assumption is imposed. -/
theorem IsArithErrSem.exec_dot_abs_sum_mul_sub_le_of_absRelErr
    (I : Interp P ι K C) (tag : P)
    (h : IsArithErrSem (fun p _ => AbsRelErr (u p) (η p)) dec safe I.sem)
    (hz : AddsZeroExactly dec I.sem) (st : St P K C)
    (dst : Cell ℕ ℕ) (x : ℕ) (xo : IExp ℕ) (y : ℕ) (yo n : IExp ℕ)
    (xs ys : ℕ → ℝ) (hu : 0 ≤ u tag) (hη : 0 ≤ η tag)
    (hx : ∀ i < n.eval, ∃ w, st.store.read tag x (xo.eval + i) = some w ∧ dec tag w = xs i)
    (hy : ∀ i < n.eval, ∃ w, st.store.read tag y (yo.eval + i) = some w ∧ dec tag w = ys i)
    (hdx : dst.buf = x → ∀ i < n.eval, dst.idx.eval ≠ xo.eval + i)
    (hdy : dst.buf = y → ∀ i < n.eval, dst.idx.eval ≠ yo.eval + i)
    (hdst : ∃ v s, st.store.write tag dst.buf dst.idx.eval v = some s)
    (hsafe : ∀ k < n.eval, ∀ s : ℕ → ℝ,
      IsDotTrace (fun _ => AbsRelErr (u tag) (η tag)) xs ys k s →
      safe tag (xs k * ys k) ∧ ∀ q, AbsRelErr (u tag) (η tag) (xs k * ys k) q →
        safe tag (s k + q)) :
    ∃ out w, exec I (dot tag dst x xo y yo n).run st = some out ∧
      st.store.write tag dst.buf dst.idx.eval w = some out.store ∧
      |∑ k ∈ Finset.range n.eval, xs k * ys k - dec tag w| ≤
        ((1 + u tag) ^ (2 * n.eval) - 1) *
          (∑ k ∈ Finset.range n.eval, |xs k * ys k|) +
        n.eval * (1 + u tag) ^ (2 * n.eval) * (2 + u tag) * η tag := by
  obtain ⟨out, w, s, hrun, hwrite, htrace, hvalue⟩ :=
    h.exec_dot I tag st hz dst x xo y yo n xs ys hx hy hdx hdy hdst hsafe
  refine ⟨out, w, hrun, hwrite, ?_⟩
  rw [hvalue]
  exact htrace.abs_sum_mul_sub_le_of_absRelErr hu hη

private theorem dot_safe_of_absRelErr {u η L : ℝ} {x y : ℕ → ℝ} {N : ℕ}
    {safe : ℝ → Prop} (hu : 0 ≤ u) (hη : 0 ≤ η)
    (hball : ∀ a, |a| ≤ L → safe a)
    (hinput : (1 + u) ^ (2 * N) * (∑ i ∈ Finset.range N, |x i * y i|) +
      N * (1 + u) ^ (2 * N) * (2 + u) * η ≤ L)
    (k : ℕ) (hk : k < N) (s : ℕ → ℝ)
    (hs : IsDotTrace (fun _ => AbsRelErr u η) x y k s) :
    safe (x k * y k) ∧ ∀ q, AbsRelErr u η (x k * y k) q → safe (s k + q) := by
  have hP : 1 ≤ (1 + u) ^ (2 * N) := one_le_pow₀ (by linarith)
  have hB : 0 ≤ ∑ i ∈ Finset.range N, |x i * y i| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hpad : (∑ i ∈ Finset.range N, |x i * y i|) ≤
      (1 + u) ^ (2 * N) * (∑ i ∈ Finset.range N, |x i * y i|) +
        N * (1 + u) ^ (2 * N) * (2 + u) * η := by
    have := mul_le_mul_of_nonneg_right hP hB
    have : 0 ≤ N * (1 + u) ^ (2 * N) * (2 + u) * η := by positivity
    linarith
  refine ⟨hball _ ((Finset.single_le_sum (fun _ _ => abs_nonneg _)
    (Finset.mem_range.mpr hk)).trans (hpad.trans hinput)), fun q hq => ?_⟩
  exact hball _ ((hs.abs_add_le_of_absRelErr hu hη hk hq).trans hinput)

/-- The actual `axpy` run succeeds and changes only the output block when decoded inputs and
the usual alias restrictions hold. If $u,\eta\ge0$, every exact operation of magnitude at most
$L$ is safe, and $(1+u)\lvert ax_i\rvert+\lvert y_i\rvert+\eta\le L$, its Euclidean
error is at most $u\|\mathbf{y}\|+u(2+u)\lvert a\rvert\|\mathbf{x}\|+
\sqrt n(2+u)\eta$. No dimension-precision smallness assumption is needed.
The operation order is that of [Higham2002, §2.2, (2.4)]. -/
theorem IsArithErrSem.exec_axpy_norm_sub_le_of_absRelErr
    (I : Interp P ι K C) (tag : P)
    (h : IsArithErrSem (fun p _ => AbsRelErr (u p) (η p)) dec safe I.sem)
    (st : St P K C) (a : Cell ℕ ℕ) (x : ℕ) (xo : IExp ℕ) (y : ℕ) (yo n : IExp ℕ)
    (av : ℝ) (xs ys : ℕ → ℝ) (L : ℝ) (hu : 0 ≤ u tag) (hη : 0 ≤ η tag)
    (ha : ∃ w, st.store.read tag a.buf a.idx.eval = some w ∧ dec tag w = av)
    (hx : ∀ i < n.eval, ∃ w, st.store.read tag x (xo.eval + i) = some w ∧ dec tag w = xs i)
    (hy : ∀ i < n.eval, ∃ w, st.store.read tag y (yo.eval + i) = some w ∧ dec tag w = ys i)
    (hay : a.buf = y → ∀ i < n.eval, a.idx.eval ≠ yo.eval + i)
    (hxy : x = y → ∀ i < n.eval, ∀ j < n.eval, xo.eval + i = yo.eval + j → i = j)
    (hball : ∀ b, |b| ≤ L → safe tag b)
    (hinput : ∀ i < n.eval, (1 + u tag) * |av * xs i| + |ys i| + η tag ≤ L) :
    ∃ out, ∃ W : ℕ → K, exec I (axpy tag a x xo y yo n).run st = some out ∧
      st.store.writeBlock tag y yo.eval ((List.range n.eval).toArray.map W) = some out.store ∧
      ‖WithLp.toLp 2 (fun i : Fin n.eval => ys i + av * xs i - dec tag (W i))‖ ≤
        u tag * ‖WithLp.toLp 2 (fun i : Fin n.eval => ys i)‖ +
        u tag * (2 + u tag) * |av| * ‖WithLp.toLp 2 (fun i : Fin n.eval => xs i)‖ +
        Real.sqrt n.eval * (2 + u tag) * η tag := by
  have hsafe i (hi : i < n.eval) : safe tag (av * xs i) ∧
      ∀ q, AbsRelErr (u tag) (η tag) (av * xs i) q → safe tag (q + ys i) := by
    refine ⟨hball _ ?_, fun q hq => hball _ ?_⟩
    · have : 0 ≤ u tag * |av * xs i| := mul_nonneg hu (abs_nonneg _)
      have := abs_nonneg (ys i)
      linarith [hinput i hi]
    · exact ((abs_add_le _ _).trans (add_le_add hq.abs_le le_rfl)).trans
        (by linarith [hinput i hi])
  obtain ⟨out, W, hrun, hwrite, hW⟩ :=
    h.exec_axpy I tag st a x xo y yo n av xs ys ha hx hy hay hxy hsafe
  choose q hq hz using fun i : Fin n.eval => hW i i.isLt
  refine ⟨out, W, hrun, hwrite, ?_⟩
  have hv := norm_sub_add_smul_le_of_absRelErr
    (x := fun i : Fin n.eval => xs i) (y := fun i : Fin n.eval => ys i)
    (z := fun i : Fin n.eval => dec tag (W i)) hq
    (fun i => by simpa only [add_comm] using hz i) hu hu hη hη
  change ‖WithLp.toLp 2 (fun i : Fin n.eval => ys i + av * xs i - dec tag (W i))‖ ≤ _ at hv
  simpa only [Fintype.card_fin, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, show u tag + u tag + u tag * u tag = u tag * (2 + u tag) by ring,
    show (1 + u tag) * η tag + η tag = (2 + u tag) * η tag by ring, mul_assoc] using hv

/-- The actual rectangular `gemv` run has the mixed dot-product error in each output row,
and changes only its writable output block. Assume nonnegative allowances, exact addition
of zero, decoded inputs, disjoint input/output blocks, and a safe radius $L$. For every row,
the input-only condition $P\sum_j\lvert a_{ij}x_j\rvert+D\le L$, where
$P=(1+u)^{2n}$ and $D=nP(2+u)\eta$, certifies every product and accumulation. No smallness
condition on $nu$ is required. [Higham2002, §2.2 and §3.5]. -/
theorem IsArithErrSem.exec_gemv_abs_sum_mul_sub_le_of_absRelErr
    (I : Interp P ι K C) (tag : P)
    (h : IsArithErrSem (fun p _ => AbsRelErr (u p) (η p)) dec safe I.sem)
    (hz : AddsZeroExactly dec I.sem) (st : St P K C)
    (m n : IExp ℕ) (A : ℕ) (ao : IExp ℕ) (x : ℕ) (xo : IExp ℕ)
    (y : ℕ) (yo : IExp ℕ) (av : ℕ → ℕ → ℝ) (xv : ℕ → ℝ)
    (L : ℝ) (hu : 0 ≤ u tag) (hη : 0 ≤ η tag)
    (hA : ∀ i < m.eval, ∀ j < n.eval, ∃ w,
      st.store.read tag A (ao.eval + i + m.eval * j) = some w ∧ dec tag w = av i j)
    (hx : ∀ j < n.eval, ∃ w, st.store.read tag x (xo.eval + j) = some w ∧ dec tag w = xv j)
    (hyA : y = A → yo.eval + m.eval ≤ ao.eval ∨ ao.eval + m.eval * n.eval ≤ yo.eval)
    (hyx : y = x → yo.eval + m.eval ≤ xo.eval ∨ xo.eval + n.eval ≤ yo.eval)
    (hy : ∀ i < m.eval, ∃ v s, st.store.write tag y (yo.eval + i) v = some s)
    (hinput : ∀ i < m.eval,
      (1 + u tag) ^ (2 * n.eval) * (∑ j ∈ Finset.range n.eval, |av i j * xv j|) +
        n.eval * (1 + u tag) ^ (2 * n.eval) * (2 + u tag) * η tag ≤ L)
    (hball : ∀ b, |b| ≤ L → safe tag b) :
    ∃ out, ∃ W : ℕ → K, exec I (gemv tag m n A ao x xo y yo).run st = some out ∧
      st.store.writeBlock tag y yo.eval ((List.range m.eval).toArray.map W) = some out.store ∧
      ∀ i < m.eval, |∑ j ∈ Finset.range n.eval, av i j * xv j - dec tag (W i)| ≤
        ((1 + u tag) ^ (2 * n.eval) - 1) * (∑ j ∈ Finset.range n.eval, |av i j * xv j|) +
        n.eval * (1 + u tag) ^ (2 * n.eval) * (2 + u tag) * η tag := by
  obtain ⟨out, W, s, hrun, hwrite, htrace⟩ :=
    h.exec_gemv I tag st hz m n A ao x xo y yo av xv hA hx hyA hyx hy
      (fun i hi => dot_safe_of_absRelErr hu hη hball (hinput i hi))
  refine ⟨out, W, hrun, hwrite, fun i hi => ?_⟩
  rw [(htrace i hi).2]
  exact (htrace i hi).1.abs_sum_mul_sub_le_of_absRelErr hu hη

/-- The actual rectangular `gemm` run has the mixed dot-product error in each entry and
changes only its writable output block. Assume nonnegative allowances, exact addition of
zero, decoded column-major inputs, disjoint input/output blocks, and a safe radius $L$.
For each output entry the input-only condition $P\sum_k\lvert a_{ik}b_{kj}\rvert+D\le L$,
where $P=(1+u)^{2n}$ and $D=nP(2+u)\eta$, certifies every product and accumulation.
No smallness condition on $nu$ is required. [Higham2002, §2.2 and §3.5]. -/
theorem IsArithErrSem.exec_gemm_abs_sum_mul_sub_le_of_absRelErr
    (I : Interp P ι K C) (tag : P)
    (h : IsArithErrSem (fun p _ => AbsRelErr (u p) (η p)) dec safe I.sem)
    (hz : AddsZeroExactly dec I.sem) (st : St P K C)
    (m n l : IExp ℕ) (A : ℕ) (ao : IExp ℕ) (B : ℕ) (bo : IExp ℕ)
    (Cb : ℕ) (co : IExp ℕ) (av bv : ℕ → ℕ → ℝ)
    (L : ℝ) (hu : 0 ≤ u tag) (hη : 0 ≤ η tag)
    (hA : ∀ i < m.eval, ∀ k < n.eval, ∃ w,
      st.store.read tag A (ao.eval + i + m.eval * k) = some w ∧ dec tag w = av i k)
    (hB : ∀ k < n.eval, ∀ j < l.eval, ∃ w,
      st.store.read tag B (bo.eval + k + n.eval * j) = some w ∧ dec tag w = bv k j)
    (hCA : Cb = A → co.eval + m.eval * l.eval ≤ ao.eval ∨ ao.eval + m.eval * n.eval ≤ co.eval)
    (hCB : Cb = B → co.eval + m.eval * l.eval ≤ bo.eval ∨ bo.eval + n.eval * l.eval ≤ co.eval)
    (hC : ∀ k < m.eval * l.eval, ∃ v s, st.store.write tag Cb (co.eval + k) v = some s)
    (hinput : ∀ i < m.eval, ∀ j < l.eval,
      (1 + u tag) ^ (2 * n.eval) * (∑ k ∈ Finset.range n.eval, |av i k * bv k j|) +
        n.eval * (1 + u tag) ^ (2 * n.eval) * (2 + u tag) * η tag ≤ L)
    (hball : ∀ b, |b| ≤ L → safe tag b) :
    ∃ out, ∃ W : ℕ → K, exec I (gemm tag m n l A ao B bo Cb co).run st = some out ∧
      st.store.writeBlock tag Cb co.eval ((List.range (m.eval * l.eval)).toArray.map W) =
        some out.store ∧
      ∀ i < m.eval, ∀ j < l.eval,
        |∑ k ∈ Finset.range n.eval, av i k * bv k j - dec tag (W (i + m.eval * j))| ≤
        ((1 + u tag) ^ (2 * n.eval) - 1) * (∑ k ∈ Finset.range n.eval, |av i k * bv k j|) +
        n.eval * (1 + u tag) ^ (2 * n.eval) * (2 + u tag) * η tag := by
  obtain ⟨out, W, s, hrun, hwrite, htrace⟩ :=
    h.exec_gemm I tag st hz m n l A ao B bo Cb co av bv hA hB hCA hCB hC
      (fun i hi j hj => dot_safe_of_absRelErr hu hη hball (hinput i hi j hj))
  refine ⟨out, W, hrun, hwrite, fun i hi j hj => ?_⟩
  rw [(htrace i hi j hj).2]
  exact (htrace i hi j hj).1.abs_sum_mul_sub_le_of_absRelErr hu hη

end NLAlib.Computation
