/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BLAS.RoundingErrors
public import NLAlib.ForMathlib.Analysis.InnerProductSpace.PiL2

/-!
# Rounded norm and normalization kernels

The actual `nrm2` kernel accumulates a dot product and then takes a rounded square root.
The actual `rscl` kernel divides each component by the stored norm. These results use the
standard relative-error contract for an arbitrary carrier of stored words and prove successful
execution from input and roundoff premises. They make the dimension dependence explicit.

## Main results

* `NLAlib.Computation.IsRelErrSem.exec_nrm2_abs_norm_sub_le`: successful rounded norm.
* `NLAlib.Computation.IsRelErrSem.exec_nrm2_rscl`: actual normalization, near-unit output,
  and an initial-direction mismatch certificate.
* `NLAlib.Computation.RelErr.norm_sub_smul_inv_norm_le`: input-direction error after rounding.
-/

@[expose] public section

namespace NLAlib.Computation

open Finset

/-- Squared norm defect after a rounded norm and componentwise rounded division. The value is
currently <!-- value Computation.normalizationRoundingFactor n u -->
$$\frac{u+(1-u)^{-(n+1)}-1}{2-(1-u)^{-(n+1)}}
\left(2+\frac{u+(1-u)^{-(n+1)}-1}{2-(1-u)^{-(n+1)}}\right).$$
The divisions are total; theorems require the accumulated norm rounding factor to be below one. -/
noncomputable irreducible_def normalizationRoundingFactor (n : ℕ) (u : ℝ) : ℝ :=
  let t := (u + roundingFactor (n + 1) u) / (1 - roundingFactor (n + 1) u)
  t * (2 + t)

/-- The normalization defect factor is nonnegative at a nonnegative unit roundoff and
an accumulated rounding factor below one. -/
theorem normalizationRoundingFactor_nonneg {n : ℕ} {u : ℝ} (hu : 0 ≤ u)
    (hn : (n + 1 : ℕ) * u < 1) (hg : roundingFactor (n + 1) u < 1) :
    0 ≤ normalizationRoundingFactor n u := by
  rw [normalizationRoundingFactor_def]
  have hu1 : u < 1 := by
    have : u ≤ (n + 1 : ℕ) * u := le_mul_of_one_le_left hu
      (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
    exact this.trans_lt hn
  have hγ := roundingFactor_nonneg (n := n + 1) hu hu1
  positivity

private theorem roundingFactor_succ_le_two_mul {n : ℕ} {u : ℝ} (hu : 0 ≤ u)
    (hsmall : (n + 1 : ℕ) * u ≤ 1 / 100) :
    roundingFactor (n + 1) u ≤ 2 * ((n + 1 : ℕ) * u) := by
  let q : ℝ := (n + 1 : ℕ) * u
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hn : (n + 1 : ℕ) * u < 1 := by linarith
  apply (roundingFactor_le hu hn).trans
  change q / (1 - q) ≤ 2 * q
  apply (div_le_iff₀ (by change 0 < 1 - q; change q ≤ _ at hsmall; linarith)).mpr
  have hprod : 0 ≤ q * (1 - 2 * q) := mul_nonneg hq (by change q ≤ _ at hsmall; linarith)
  nlinarith

/-- At $(n+1)u\le1/100$, the squared normalization defect is at most $12(n+1)u$.
This explicitly retains the dimension dependence of the ordered dot product. -/
theorem normalizationRoundingFactor_le {n : ℕ} {u : ℝ} (hu : 0 ≤ u)
    (hsmall : (n + 1 : ℕ) * u ≤ 1 / 100) :
    normalizationRoundingFactor n u ≤ 12 * (n + 1 : ℕ) * u := by
  let q : ℝ := (n + 1 : ℕ) * u
  let g := roundingFactor (n + 1) u
  let t := (u + g) / (1 - g)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hqs : q ≤ 1 / 100 := hsmall
  have hn : (n + 1 : ℕ) * u < 1 := by linarith
  have hu1 : u < 1 :=
    (le_mul_of_one_le_left hu (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))).trans_lt hn
  have hg : 0 ≤ g := roundingFactor_nonneg hu hu1
  have hgle : g ≤ 2 * q := roundingFactor_succ_le_two_mul hu hsmall
  have hgl : g < 1 := by linarith
  have huq : u ≤ q := by
    dsimp [q]
    push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hu]
  have ht : 0 ≤ t := div_nonneg (add_nonneg hu hg) (by linarith)
  have htle : t ≤ 4 * q := by
    apply (div_le_iff₀ (by linarith : 0 < 1 - g)).mpr
    have hmult := mul_le_mul_of_nonneg_right hgle (by positivity : 0 ≤ 4 * q)
    have hprod : 0 ≤ q * (1 - 8 * q) := mul_nonneg hq (by linarith)
    nlinarith
  rw [normalizationRoundingFactor_def]
  change t * (2 + t) ≤ 12 * (n + 1 : ℕ) * u
  calc _ ≤ (4 * q) * (2 + 4 * q) :=
      mul_le_mul htle (by linarith) (by linarith) (by positivity)
    _ ≤ 12 * q := by
      have hprod : 0 ≤ q * (1 - 4 * q) := mul_nonneg hq (by linarith)
      nlinarith
    _ = _ := by dsimp [q]; ring

private theorem roundingFactor_add_mul_le {n : ℕ} {u : ℝ} (hu : 0 ≤ u)
    (hn : (n + 1 : ℕ) * u < 1) :
    roundingFactor n u + u * (1 + roundingFactor n u) ≤ roundingFactor (n + 1) u := by
  have hu1 : u < 1 := by
    have hcast : (1 : ℝ) ≤ n + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    exact (le_mul_of_one_le_left hu hcast).trans_lt (by simpa using hn)
  have hγ := roundingFactor_nonneg (n := n) hu hu1
  have h₁ := le_roundingFactor_one (u := u) hu1
  have hprod := roundingFactor_add_add_mul (k := n) (j := 1) (u := u)
  nlinarith

private theorem abs_sub_sqrt_le_roundingFactor {n : ℕ} {u r s : ℝ}
    (hu : 0 ≤ u) (hn : n * u < 1) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (h : |r ^ 2 - s| ≤ roundingFactor n u * r ^ 2) :
    |r - Real.sqrt s| ≤ roundingFactor n u * r := by
  have hγ := roundingFactor_nonneg_of_mul_lt_one hu hn
  have hsq := Real.sq_sqrt hs
  have hroot := Real.sqrt_nonneg s
  have hprod : |r - Real.sqrt s| * (r + Real.sqrt s) = |r ^ 2 - s| := by
    rw [← abs_of_nonneg (add_nonneg hr hroot), ← abs_mul]
    congr 1
    nlinarith
  rcases hr.eq_or_lt with rfl | hr
  · have hs0 : s = 0 := by
      simp only [zero_pow (show (2 : ℕ) ≠ 0 by omega), mul_zero, zero_sub, abs_neg] at h
      exact le_antisymm ((le_abs_self s).trans h) hs
    simp only [hs0, Real.sqrt_zero, sub_self, abs_zero, mul_zero, le_refl]
  · have hmul : |r - Real.sqrt s| * r ≤ roundingFactor n u * r ^ 2 := by
      nlinarith [mul_nonneg (abs_nonneg (r - Real.sqrt s)) hroot]
    exact (mul_le_mul_iff_left₀ hr).mp (by nlinarith [hmul])

/-- Componentwise relative error bounds the Euclidean forward error by the same coefficient. -/
theorem RelErr.norm_sub_le {ι : Type*} [Fintype ι] {u : ℝ} {x y : ι → ℝ}
    (hu : 0 ≤ u) (h : ∀ i, RelErr u (x i) (y i)) :
    ‖WithLp.toLp 2 (x - y)‖ ≤ u * ‖WithLp.toLp 2 x‖ := by
  have hpoint : ∀ i, |x i - y i| ≤ u * |x i| := by
    intro i
    obtain ⟨δ, hδ, hy⟩ := h i
    rw [hy, show x i - x i * (1 + δ) = -δ * x i by ring, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_right hδ (abs_nonneg _)
  have hnorm := EuclideanSpace.norm_toLp_le_norm_toLp (x := x - y) (y := u • x)
    (fun i => by
      change |x i - y i| ≤ |u * x i|
      rw [abs_mul, abs_of_nonneg hu]
      exact hpoint i)
  simpa only [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hu] using hnorm

/-- Rounded componentwise normalization need not preserve the exact input direction.
If the stored scale $q$ is nonnegative and approximates the input norm with relative bound $g$,
and each rescaled component has relative error at most $u$, the initial-direction mismatch
obeys $\|\mathbf{x}-q\mathbf{y}/\|\mathbf{y}\|\|\le(2u+g)\|\mathbf{x}\|$.
The statement also permits zero vectors; normalization uses total real inversion. -/
theorem RelErr.norm_sub_smul_inv_norm_le {ι : Type*} [Fintype ι]
    {u q g : ℝ} {x y : ι → ℝ} (hu : 0 ≤ u) (hq : 0 ≤ q)
    (hscale : |‖WithLp.toLp 2 x‖ - q| ≤ g * ‖WithLp.toLp 2 x‖)
    (h : ∀ i, RelErr u (x i) (q * y i)) :
    ‖WithLp.toLp 2 (x - q • (‖WithLp.toLp 2 y‖⁻¹ • y))‖ ≤
      (2 * u + g) * ‖WithLp.toLp 2 x‖ := by
  have hres := RelErr.norm_sub_le hu h
  change ‖WithLp.toLp 2 (x - q • y)‖ ≤ u * ‖WithLp.toLp 2 x‖ at hres
  have hresnorm : |q * ‖WithLp.toLp 2 y‖ - ‖WithLp.toLp 2 x‖| ≤
      u * ‖WithLp.toLp 2 x‖ := by
    have hnorm := abs_norm_sub_norm_le (WithLp.toLp 2 x) (WithLp.toLp 2 (q • y))
    rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hq] at hnorm
    rw [abs_sub_comm, ← WithLp.toLp_sub] at hnorm
    exact hnorm.trans hres
  have hqa : q * |‖WithLp.toLp 2 y‖ - 1| ≤ (u + g) * ‖WithLp.toLp 2 x‖ := by
    have htri := abs_sub_le (q * ‖WithLp.toLp 2 y‖) ‖WithLp.toLp 2 x‖ q
    rw [show q * ‖WithLp.toLp 2 y‖ - q = q * (‖WithLp.toLp 2 y‖ - 1) by ring,
      abs_mul, abs_of_nonneg hq] at htri
    nlinarith
  have hnear : ‖WithLp.toLp 2 (q • y - q • (‖WithLp.toLp 2 y‖⁻¹ • y))‖ ≤
      q * |‖WithLp.toLp 2 y‖ - 1| := by
    rw [smul_smul, ← sub_smul, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]
    by_cases ha : ‖WithLp.toLp 2 y‖ = 0
    · simp [ha, hq]
    · calc
        _ = |(q - q * ‖WithLp.toLp 2 y‖⁻¹) * ‖WithLp.toLp 2 y‖| := by
          rw [abs_mul, abs_of_nonneg (norm_nonneg _)]
        _ = |q * (‖WithLp.toLp 2 y‖ - 1)| := by congr 1; field_simp
        _ ≤ _ := by rw [abs_mul, abs_of_nonneg hq]
  have heq : x - q • (‖WithLp.toLp 2 y‖⁻¹ • y) =
      (x - q • y) + (q • y - q • (‖WithLp.toLp 2 y‖⁻¹ • y)) := by abel
  rw [heq, WithLp.toLp_add]
  exact (norm_add_le _ _).trans (by linarith [hnear.trans hqa])

/-- Relative error in a stored norm and componentwise error in division give a squared
Euclidean norm defect bounded by the normalization factor. -/
theorem RelErr.abs_norm_sq_sub_one_le {n : ℕ} {u q : ℝ} {x y : Fin n → ℝ}
    (hu : 0 ≤ u) (hn : (n + 1 : ℕ) * u < 1) (hsmall : roundingFactor (n + 1) u < 1)
    (hx : 0 < ‖WithLp.toLp 2 x‖)
    (hq : |‖WithLp.toLp 2 x‖ - q| ≤ roundingFactor (n + 1) u * ‖WithLp.toLp 2 x‖)
    (h : ∀ i, RelErr u (x i) (q * y i)) :
    |‖WithLp.toLp 2 y‖ ^ 2 - 1| ≤ normalizationRoundingFactor n u := by
  let r := ‖WithLp.toLp 2 x‖
  let a := ‖WithLp.toLp 2 y‖
  let g := roundingFactor (n + 1) u
  let t := (u + g) / (1 - g)
  have hu1 : u < 1 :=
    (le_mul_of_one_le_left hu (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))).trans_lt hn
  have hg : 0 ≤ g := roundingFactor_nonneg hu hu1
  have ht : 0 ≤ t := div_nonneg (add_nonneg hu hg) (by linarith)
  have hqpos : 0 < q := by
    have hupper := (abs_le.mp hq).2
    nlinarith [mul_pos (sub_pos.mpr hsmall) hx]
  have hres := RelErr.norm_sub_le hu h
  have hresnorm : |r - q * a| ≤ u * r := by
    have hnorm := abs_norm_sub_norm_le (WithLp.toLp 2 x) (WithLp.toLp 2 (q • y))
    rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hqpos] at hnorm
    refine hnorm.trans ?_
    rw [← WithLp.toLp_smul, ← WithLp.toLp_sub]
    exact hres
  have hqa : q * |a - 1| ≤ (u + g) * r := by
    have htri := abs_sub_le (q * a) r q
    rw [show q * a - q = q * (a - 1) by ring, abs_mul, abs_of_pos hqpos] at htri
    have hres' : |q * a - r| ≤ u * r := by rwa [abs_sub_comm] at hresnorm
    nlinarith
  have hqlo : (1 - g) * r ≤ q := by
    have hupper := (abs_le.mp hq).2
    dsimp [r, g]
    nlinarith
  have hprod := mul_le_mul_of_nonneg_right hqlo (abs_nonneg (a - 1))
  have hcancel : (1 - g) * |a - 1| ≤ u + g :=
    (mul_le_mul_iff_right₀ hx).mp (by nlinarith [hqa, hprod])
  have hnear : |a - 1| ≤ t := (le_div_iff₀ (by linarith : 0 < 1 - g)).mpr
    (by nlinarith [hcancel])
  rw [normalizationRoundingFactor_def]
  change |a ^ 2 - 1| ≤ t * (2 + t)
  rw [show a ^ 2 - 1 = (a - 1) * (a + 1) by ring, abs_mul,
    abs_of_nonneg (by dsimp [a]; positivity : 0 ≤ a + 1)]
  have ha : a + 1 ≤ 2 + t := by have := (abs_le.mp hnear).2; linarith
  exact mul_le_mul hnear ha (by dsimp [a]; positivity) ht

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]
  (I : Interp P ι K C) (p : P) (st : St P K C) {dec : P → K → ℝ} {u : P → ℝ}

/-- The rounded dot-then-square-root norm succeeds under the standard relative-error model,
with every value in range and exact addition of zero. For $(n+1)u_p<1$ and
$\gamma_{n+1}<1$, it writes a nonnegative decoded norm $q$ satisfying
$$\lvert\|\mathbf{x}\|-q\rvert\le\gamma_{n+1}\|\mathbf{x}\|.$$
The square root is the actual final operation of `nrm2`, not exact postprocessing.
[Higham2002, §3.1], composed with the square-root clause of the standard model. -/
theorem IsRelErrSem.exec_nrm2_abs_norm_sub_le
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (dst : Cell ℕ ℕ) (x : ℕ) (xo n : IExp ℕ) (xs : ℕ → ℝ)
    (hn : (n.eval + 1 : ℕ) * u p < 1)
    (hsmall : roundingFactor (n.eval + 1) (u p) < 1)
    (hx : ∀ i < n.eval, ∃ w, st.store.read p x (xo.eval + i) = some w ∧ dec p w = xs i)
    (hdx : dst.buf = x → ∀ i < n.eval, dst.idx.eval ≠ xo.eval + i)
    (hdst : ∃ v s₁, st.store.write p dst.buf dst.idx.eval v = some s₁) :
    ∃ st' w, exec I (nrm2 p dst x xo n).run st = some st' ∧
      st.store.write p dst.buf dst.idx.eval w = some st'.store ∧ 0 ≤ dec p w ∧
      |‖WithLp.toLp 2 (fun i : Fin n.eval => xs i)‖ - dec p w| ≤
        roundingFactor (n.eval + 1) (u p) *
          ‖WithLp.toLp 2 (fun i : Fin n.eval => xs i)‖ := by
  have hu := h.nonneg (p := p) trivial
  have hn' : (n.eval : ℝ) * u p < 1 := by
    have hcast : (n.eval : ℝ) ≤ n.eval + 1 := by linarith
    exact (mul_le_mul_of_nonneg_right hcast hu).trans_lt (by simpa using hn)
  have hu1 : u p < 1 := by
    have hcast : (1 : ℝ) ≤ n.eval + 1 := by
      have := Nat.cast_nonneg (α := ℝ) n.eval
      linarith
    exact (le_mul_of_one_le_left hu hcast).trans_lt (by simpa using hn)
  have hγ := roundingFactor_nonneg (n := n.eval) hu hu1
  have hγ1 := roundingFactor_le_roundingFactor hu hu1 (Nat.le_succ n.eval)
  obtain ⟨st₁, w, hrun, hwrite, herr⟩ :=
    h.exec_dot_abs_sum_mul_sub_le I p st hz dst x xo x xo n xs xs hu1 hx hx hdx hdx hdst
  let r := ‖WithLp.toLp 2 (fun i : Fin n.eval => xs i)‖
  have hr : 0 ≤ r := norm_nonneg _
  have hsq : r ^ 2 = ∑ i ∈ range n.eval, xs i * xs i := by
    rw [EuclideanSpace.norm_toLp_sq_eq_dotProduct_self, dotProduct]
    exact Fin.sum_univ_eq_sum_range (fun i => xs i * xs i) n.eval
  have herr' : |r ^ 2 - dec p w| ≤ roundingFactor n.eval (u p) * r ^ 2 := by
    simpa only [hsq, ← abs_mul, ← sq, sq_abs] using herr
  have hs : 0 ≤ dec p w := by
    have hlow := (abs_le.mp herr').2
    have hγlt := hγ1.trans_lt hsmall
    nlinarith [sq_nonneg r, mul_nonneg (sub_nonneg.mpr hγlt.le) (sq_nonneg r)]
  obtain ⟨q, hq⟩ := h.sqrt_ok p w hs
  obtain ⟨δ, hδ, heq⟩ := h.sqrt_err p w q hq
  obtain ⟨s₂, hs₂⟩ := Store.exists_write_eq_some_of_write_eq_some hwrite q
  have hsuccess : ∃ st', exec I (nrm2 p dst x xo n).run st = some st' ∧ st'.store = s₂ := by
    rw [run_nrm2, exec_seq_skip, exec_named,
      exec_run_bind I (b := dot p dst x xo x xo n) (fun _ => rfl), hrun, Option.bind_some]
    refine ⟨_, (exec_seq_instr_un I (Store.read_of_write_eq_some hwrite) hq
      (by rw [Store.write_of_write_eq_some hwrite]; exact hs₂)).trans (exec_skip I _), rfl⟩
  obtain ⟨st₂, hrun₂, hstore₂⟩ := hsuccess
  refine ⟨st₂, q, hrun₂, hstore₂ ▸ hs₂, ?_, ?_⟩
  · rw [heq]
    exact mul_nonneg (Real.sqrt_nonneg _) (by have := (abs_le.mp hδ).1; linarith)
  · have hroot := abs_sub_sqrt_le_roundingFactor hu hn' hr hs herr'
    have hrootup : Real.sqrt (dec p w) ≤ (1 + roundingFactor n.eval (u p)) * r := by
      have := (abs_le.mp hroot).1
      nlinarith
    have hsqrt : |Real.sqrt (dec p w) - dec p q| ≤
        u p * ((1 + roundingFactor n.eval (u p)) * r) := by
      rw [heq, show Real.sqrt (dec p w) - Real.sqrt (dec p w) * (1 + δ) =
        -δ * Real.sqrt (dec p w) by ring, abs_mul, abs_neg,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_mul hδ hrootup (Real.sqrt_nonneg _) hu
    calc |r - dec p q| ≤ |r - Real.sqrt (dec p w)| +
          |Real.sqrt (dec p w) - dec p q| := abs_sub_le _ _ _
      _ ≤ roundingFactor n.eval (u p) * r +
          u p * ((1 + roundingFactor n.eval (u p)) * r) := add_le_add hroot hsqrt
      _ = (roundingFactor n.eval (u p) + u p * (1 + roundingFactor n.eval (u p))) * r :=
        by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (roundingFactor_add_mul_le hu hn) hr

/-- The rounded norm bound for a finite vector stored through `HoldsDecoded` as one column.
This is the finite-dimensional storage interface used by algorithm realization theorems. -/
theorem IsRelErrSem.exec_nrm2_abs_norm_sub_le_of_holdsDecoded
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (dst : Cell ℕ ℕ) (x : ℕ) (xo : IExp ℕ) (n : ℕ) (xs : Fin n → ℝ)
    (hn : (n + 1 : ℕ) * u p < 1) (hsmall : roundingFactor (n + 1) (u p) < 1)
    (hx : HoldsDecoded st.store dec p x xo.eval (Matrix.of fun i (_j : Fin 1) => xs i))
    (hdx : dst.buf = x → ∀ i < n, dst.idx.eval ≠ xo.eval + i)
    (hdst : ∃ v s₁, st.store.write p dst.buf dst.idx.eval v = some s₁) :
    ∃ st' w, exec I (nrm2 p dst x xo (.const n)).run st = some st' ∧
      st.store.write p dst.buf dst.idx.eval w = some st'.store ∧ 0 ≤ dec p w ∧
      |‖WithLp.toLp 2 xs‖ - dec p w| ≤
        roundingFactor (n + 1) (u p) * ‖WithLp.toLp 2 xs‖ := by
  let xs' : ℕ → ℝ := fun i => if hi : i < n then xs ⟨i, hi⟩ else 0
  have hx' : ∀ i < n, ∃ w, st.store.read p x (xo.eval + i) = some w ∧ dec p w = xs' i := by
    intro i hi
    simpa only [xs', dif_pos hi, Matrix.of_apply, Fin.val_zero, mul_zero, add_zero] using
      hx ⟨i, hi⟩ 0
  have hvec : (fun i : Fin n => xs' i) = xs := by
    ext i
    exact dif_pos i.2
  obtain ⟨st', w, hrun, hwrite, hnonneg, herr⟩ :=
    h.exec_nrm2_abs_norm_sub_le I p st hz dst x xo (.const n) xs' hn hsmall hx' hdx hdst
  change |‖WithLp.toLp 2 (fun i : Fin n => xs' i)‖ - dec p w| ≤
    roundingFactor (n + 1) (u p) * ‖WithLp.toLp 2 (fun i : Fin n => xs' i)‖ at herr
  exact ⟨st', w, hrun, hwrite, hnonneg, by simpa only [hvec] using herr⟩

/-- A zero decoded input vector has a successfully computed decoded norm equal to zero,
including an input vector of length zero. -/
theorem IsRelErrSem.exec_nrm2_eq_zero
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (dst : Cell ℕ ℕ) (x : ℕ) (xo n : IExp ℕ) (xs : ℕ → ℝ)
    (hn : (n.eval + 1 : ℕ) * u p < 1)
    (hsmall : roundingFactor (n.eval + 1) (u p) < 1)
    (hx : ∀ i < n.eval, ∃ w, st.store.read p x (xo.eval + i) = some w ∧ dec p w = xs i)
    (hdx : dst.buf = x → ∀ i < n.eval, dst.idx.eval ≠ xo.eval + i)
    (hdst : ∃ v s₁, st.store.write p dst.buf dst.idx.eval v = some s₁)
    (hzero : ∀ i < n.eval, xs i = 0) :
    ∃ st' w, exec I (nrm2 p dst x xo n).run st = some st' ∧
      st.store.write p dst.buf dst.idx.eval w = some st'.store ∧ dec p w = 0 := by
  obtain ⟨st', w, hrun, hwrite, -, herr⟩ :=
    h.exec_nrm2_abs_norm_sub_le I p st hz dst x xo n xs hn hsmall hx hdx hdst
  have hv : (fun i : Fin n.eval => xs i) = 0 := funext fun i => hzero i i.2
  rw [hv, WithLp.toLp_zero, norm_zero, mul_zero, zero_sub, abs_neg] at herr
  exact ⟨st', w, hrun, hwrite, (abs_eq_zero.mp (le_antisymm herr (abs_nonneg _)))⟩

/-- A nonzero decoded input vector has a strictly positive rounded norm. -/
theorem IsRelErrSem.exec_nrm2_pos
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (dst : Cell ℕ ℕ) (x : ℕ) (xo n : IExp ℕ) (xs : ℕ → ℝ)
    (hn : (n.eval + 1 : ℕ) * u p < 1)
    (hsmall : roundingFactor (n.eval + 1) (u p) < 1)
    (hx : ∀ i < n.eval, ∃ w, st.store.read p x (xo.eval + i) = some w ∧ dec p w = xs i)
    (hdx : dst.buf = x → ∀ i < n.eval, dst.idx.eval ≠ xo.eval + i)
    (hdst : ∃ v s₁, st.store.write p dst.buf dst.idx.eval v = some s₁)
    (hpos : 0 < ‖WithLp.toLp 2 (fun i : Fin n.eval => xs i)‖) :
    ∃ st' w, exec I (nrm2 p dst x xo n).run st = some st' ∧
      st.store.write p dst.buf dst.idx.eval w = some st'.store ∧ 0 < dec p w ∧
      |‖WithLp.toLp 2 (fun i : Fin n.eval => xs i)‖ - dec p w| ≤
        roundingFactor (n.eval + 1) (u p) *
          ‖WithLp.toLp 2 (fun i : Fin n.eval => xs i)‖ := by
  obtain ⟨st', w, hrun, hwrite, -, herr⟩ :=
    h.exec_nrm2_abs_norm_sub_le I p st hz dst x xo n xs hn hsmall hx hdx hdst
  refine ⟨st', w, hrun, hwrite, ?_, herr⟩
  have hupper := (abs_le.mp herr).2
  nlinarith [mul_pos (sub_pos.mpr hsmall) hpos]

/-- Running the actual norm kernel followed by componentwise division succeeds for nonzero
input. The computed norm is positive, its error is at most $\gamma_{n+1}$ times the input
norm, the rescaling residual has norm at most $u_p\|\mathbf{x}\|$, and the decoded output
has squared norm defect at most the normalization rounding factor. The factor accounts for
both the rounded norm and the rounded divisions. The initial-direction mismatch after
normalizing the computed vector is at most $(2u_p+\gamma_{n+1})\|\mathbf{x}\|$.
[Higham2002, §3.1], applied in the order of the library's two kernels. -/
theorem IsRelErrSem.exec_nrm2_rscl
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (dst : Cell ℕ ℕ) (x : ℕ) (xo n : IExp ℕ) (xs : ℕ → ℝ)
    (hn : (n.eval + 1 : ℕ) * u p < 1)
    (hsmall : roundingFactor (n.eval + 1) (u p) < 1)
    (hx : ∀ i < n.eval, ∃ w, st.store.read p x (xo.eval + i) = some w ∧ dec p w = xs i)
    (hdx : dst.buf = x → ∀ i < n.eval, dst.idx.eval ≠ xo.eval + i)
    (hdst : ∃ v s₁, st.store.write p dst.buf dst.idx.eval v = some s₁)
    (hpos : 0 < ‖WithLp.toLp 2 (fun i : Fin n.eval => xs i)‖) :
    ∃ st₁ st₂ w, ∃ W : ℕ → K,
      exec I (nrm2 p dst x xo n).run st = some st₁ ∧
      st.store.write p dst.buf dst.idx.eval w = some st₁.store ∧
      exec I (rscl p dst x xo n).run st₁ = some st₂ ∧
      st₁.store.writeBlock p x xo.eval ((List.range n.eval).toArray.map W) = some st₂.store ∧
      0 < dec p w ∧
      |‖WithLp.toLp 2 (fun i : Fin n.eval => xs i)‖ - dec p w| ≤
        roundingFactor (n.eval + 1) (u p) *
          ‖WithLp.toLp 2 (fun i : Fin n.eval => xs i)‖ ∧
      ‖WithLp.toLp 2 (fun i : Fin n.eval => xs i - dec p w * dec p (W i))‖ ≤
        u p * ‖WithLp.toLp 2 (fun i : Fin n.eval => xs i)‖ ∧
      |‖WithLp.toLp 2 (fun i : Fin n.eval => dec p (W i))‖ ^ 2 - 1| ≤
        normalizationRoundingFactor n.eval (u p) ∧
      ‖WithLp.toLp 2 ((fun i : Fin n.eval => xs i) -
        dec p w • (‖WithLp.toLp 2 (fun i : Fin n.eval => dec p (W i))‖⁻¹ •
          (fun i : Fin n.eval => dec p (W i))))‖ ≤
        (2 * u p + roundingFactor (n.eval + 1) (u p)) *
          ‖WithLp.toLp 2 (fun i : Fin n.eval => xs i)‖ := by
  have hu := h.nonneg (p := p) trivial
  obtain ⟨st₁, w, hnorm, hwrite, hwpos, herr⟩ :=
    h.exec_nrm2_pos I p st hz dst x xo n xs hn hsmall hx hdx hdst hpos
  have hx₁ : ∀ i < n.eval, ∃ w, st₁.store.read p x (xo.eval + i) = some w ∧
      dec p w = xs i := by
    intro i hi
    rw [Store.read_of_write_eq_some_of_ne hwrite ?_]
    · exact hx i hi
    · by_cases hb : x = dst.buf
      · exact Or.inr (Ne.symm (hdx hb.symm i hi))
      · exact Or.inl hb
  obtain ⟨st₂, W, hscale, hblock, hW⟩ := h.exec_rscl I p st₁ dst x xo n (dec p w) xs
    hwpos.ne' ⟨w, Store.read_of_write_eq_some hwrite, rfl⟩ hx₁ hdx
  have hrel : ∀ i : Fin n.eval, RelErr (u p) (xs i) (dec p w * dec p (W i)) := by
    intro i
    obtain ⟨δ, hδ, hval⟩ := hW i i.2
    refine ⟨δ, hδ, ?_⟩
    rw [hval]
    field_simp [hwpos.ne']
  exact ⟨st₁, st₂, w, W, hnorm, hwrite, hscale, hblock, hwpos, herr,
    RelErr.norm_sub_le hu hrel, RelErr.abs_norm_sq_sub_one_le hu hn hsmall hpos herr hrel,
    RelErr.norm_sub_smul_inv_norm_le hu hwpos.le herr hrel⟩

end NLAlib.Computation
