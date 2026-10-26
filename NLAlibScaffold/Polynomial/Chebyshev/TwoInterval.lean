/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Algebra.Polynomial.Expand
public import NLAlib.Polynomial.Chebyshev.ResidualMinimax
public import NLAlib.Polynomial.Chebyshev.TwoInterval

/-!
# Residual polynomials on two symmetric intervals (scaffold)

Statements for `NLAlib/Polynomial/Chebyshev/TwoInterval.lean` (stage LB-C1, design note
`docs/design/LowerBounds-HiddenRotationLowerBounds.md` §3.3): the two-interval dual certificate,
the residual minimax value of $[-a', -a] \cup [a, a']$, its exponential lower bound
([Shamir2026, Lemma 1]), the weighted form with at most $q + 2$ points ([Shamir2026, Lemma 2]),
and the weighted bound on a Chebyshev two-interval spectrum.

## Main results

* `NLAlib.inv_eval_T_real_le_sum_chebyshevWeight_mul_norm_sq_add_norm_sq`: the dual certificate.
* `NLAlib.residualMinimax_Icc_union_Icc`: the value $T_{\lfloor q/2 \rfloor}(\cdot)^{-1}$.
* `NLAlib.exp_neg_le_inv_eval_T_real`, `NLAlib.exp_neg_le_residualMinimax_Icc_union_Icc`: at
  least $e^{-2q/\kappa}$ on $[-\kappa, -1] \cup [1, \kappa]$.
* `NLAlib.exists_residualMinimax_Icc_union_Icc_sq_le_sum_mul_norm_sq`: the weighted form.
* `NLAlib.IsChebyshevTwoIntervalSpectrum.mem_Icc_union_Icc`,
  `NLAlib.IsChebyshevTwoIntervalSpectrum.inv_sq_le_sum_card_sub_mul_eval_sq`,
  `NLAlib.exists_isChebyshevTwoIntervalSpectrum`.
-/

@[expose] public section

open Polynomial Polynomial.Chebyshev

namespace NLAlib

/-- **The even part does at least as well**: with $u = p(x)$, $v = p(-x)$ and $\omega \ge 0$,
$\omega\lvert(\operatorname{contract}_2 p)(x^2)\rvert^2 \le
\tfrac{\omega}{2}(\lvert u \rvert^2 + \lvert v \rvert^2)$. -/
private lemma mul_norm_eval_contract_two_sq_le {𝕜 : Type*} [RCLike 𝕜] (p : 𝕜[X]) (x : 𝕜)
    {ω : ℝ} (hω : 0 ≤ ω) :
    ω * ‖(contract 2 p).eval (x ^ 2)‖ ^ 2 ≤ ω / 2 * (‖p.eval x‖ ^ 2 + ‖p.eval (-x)‖ ^ 2) := by
  have hle : ‖(contract 2 p).eval (x ^ 2)‖ ≤ (‖p.eval x‖ + ‖p.eval (-x)‖) / 2 := by
    have h := congrArg norm (two_mul_eval_contract_two_sq p x)
    rw [norm_mul, RCLike.norm_two] at h
    have := norm_add_le (p.eval x) (p.eval (-x))
    linarith
  have h3 := pow_le_pow_left₀ (norm_nonneg _) hle 2
  have h4 : ((‖p.eval x‖ + ‖p.eval (-x)‖) / 2) ^ 2 ≤ (‖p.eval x‖ ^ 2 + ‖p.eval (-x)‖ ^ 2) / 2 := by
    nlinarith [sq_nonneg (‖p.eval x‖ - ‖p.eval (-x)‖)]
  nlinarith

/-- **Dual certificate on two symmetric intervals**: for $0 < a < a'$ and $k = \lfloor q/2
\rfloor$, every $p \in \Bbbk[X]$ with $\deg p \le q$ and $p(0) = 1$ has
$$T_k\Bigl(\frac{a'^2 + a^2}{a'^2 - a^2}\Bigr)^{-1} \le \sum_{j=0}^{k} \frac{\omega_j}{2}
\Bigl(\lvert p(\sqrt{\xi_j}) \rvert^2 + \lvert p(-\sqrt{\xi_j}) \rvert^2\Bigr) \,,$$
with $\xi_j$ the Chebyshev extrema of $[a^2, a'^2]$ and $\omega_j$ their dual weights
(`chebyshevExtremum`, `chebyshevWeight`).
[Greenbaum1997, §3.1]; locator to verify; the bound behind the two-interval MINRES worst case.
Proof: $\lvert u \rvert^2 + \lvert v \rvert^2 \ge 2\lvert (u + v)/2 \rvert^2$ with
$(u + v)/2$ the even part $P(\xi_j)$, $P$ = `Polynomial.contract 2` of $p$
(`Polynomial.degree_contract_le_of_degree_le`, `Polynomial.eval_zero_contract`); then
`NLAlib.inv_eval_T_real_le_sum_chebyshevWeight_mul_norm_sq` on $[a^2, a'^2]$. The even-part
inequality is the private lemma of `NLAlib/Krylov/LinearSystems/WorstCase.lean` (the step
`hterm` of the two-interval MINRES theorem there); move it here as a public lemma, and let that
proof use this theorem. M, about 40 lines. -/
theorem inv_eval_T_real_le_sum_chebyshevWeight_mul_norm_sq_add_norm_sq {𝕜 : Type*} [RCLike 𝕜]
    {a a' : ℝ} (ha : 0 < a) (haa : a < a') {q : ℕ} {p : 𝕜[X]} (hp : p.degree ≤ q)
    (hp₀ : p.eval 0 = 1) :
    ((T ℝ ((q / 2 : ℕ) : ℤ)).eval ((a' ^ 2 + a ^ 2) / (a' ^ 2 - a ^ 2)))⁻¹ ≤
      ∑ j : Fin (q / 2 + 1), chebyshevWeight (a ^ 2) (a' ^ 2) (q / 2) j / 2 *
        (‖p.eval ((Real.sqrt (chebyshevExtremum (a ^ 2) (a' ^ 2) (q / 2) j) : ℝ) : 𝕜)‖ ^ 2 +
          ‖p.eval (-((Real.sqrt (chebyshevExtremum (a ^ 2) (a' ^ 2) (q / 2) j) : ℝ) : 𝕜))‖ ^ 2) :=
    by
  have ha2 : 0 < a ^ 2 := pow_pos ha 2
  have haa2 : a ^ 2 < a' ^ 2 := pow_lt_pow_left₀ haa ha.le two_ne_zero
  have hPd := degree_contract_le_of_degree_le two_ne_zero hp
  have hP₀ : (contract 2 p).eval 0 = 1 := by rw [eval_zero_contract two_ne_zero, hp₀]
  have hterm : ∀ j : Fin (q / 2 + 1),
      chebyshevWeight (a ^ 2) (a' ^ 2) (q / 2) j *
        ‖(contract 2 p).eval (chebyshevExtremum (a ^ 2) (a' ^ 2) (q / 2) j : 𝕜)‖ ^ 2 ≤
      chebyshevWeight (a ^ 2) (a' ^ 2) (q / 2) j / 2 *
        (‖p.eval ((Real.sqrt (chebyshevExtremum (a ^ 2) (a' ^ 2) (q / 2) j) : ℝ) : 𝕜)‖ ^ 2 +
          ‖p.eval (-((Real.sqrt (chebyshevExtremum (a ^ 2) (a' ^ 2) (q / 2) j) : ℝ) : 𝕜))‖ ^ 2) :=
    fun j => by
      have hξ0 : 0 ≤ chebyshevExtremum (a ^ 2) (a' ^ 2) (q / 2) j :=
        ha2.le.trans (chebyshevExtremum_mem_Icc haa2.le (q / 2) j).1
      have hx2 : ((Real.sqrt (chebyshevExtremum (a ^ 2) (a' ^ 2) (q / 2) j) : ℝ) : 𝕜) ^ 2 =
          (chebyshevExtremum (a ^ 2) (a' ^ 2) (q / 2) j : 𝕜) := by
        rw [← RCLike.ofReal_pow, Real.sq_sqrt hξ0]
      have h := mul_norm_eval_contract_two_sq_le p
        ((Real.sqrt (chebyshevExtremum (a ^ 2) (a' ^ 2) (q / 2) j) : ℝ) : 𝕜)
        (chebyshevWeight_pos ha2 haa2 (q / 2) j).le
      rwa [hx2] at h
  exact (inv_eval_T_real_le_sum_chebyshevWeight_mul_norm_sq ha2 haa2 hPd hP₀).trans
    (Finset.sum_le_sum fun j _ => hterm j)

/-- **Residual minimax value of two symmetric intervals**: for $0 < a < a'$,
$$\min_{\deg p \le q,\ p(0) = 1}\ \max_{x \in [-a', -a] \cup [a, a']} \lvert p(x) \rvert =
T_{\lfloor q/2 \rfloor}\Bigl(\frac{a'^2 + a^2}{a'^2 - a^2}\Bigr)^{-1} \,,$$
attained by the even Chebyshev residual $r_{\lfloor q/2 \rfloor}(x^2)$ of $[a^2, a'^2]$.
[Greenbaum1997, §3.1]; locator to verify; [Shamir2026, Lemma 1] uses the lower half.
Proof: upper bound: `NLAlib.residualMinimax_le` with the even residual
(`NLAlib.degree_chebyshevResidual_comp_X_sq_le`, `NLAlib.eval_chebyshevResidual_comp_X_sq_zero`,
`NLAlib.abs_eval_chebyshevResidual_comp_X_sq_le`). Lower bound: `le_ciInf`; for a residual $p$
with $\sup_S \lvert p \rvert = \eta$, the points $\pm\sqrt{\xi_j}$ lie in $S$
(`NLAlib.chebyshevExtremum_mem_Icc`, `Real.sqrt_le_sqrt`), so the right side of
`NLAlib.inv_eval_T_real_le_sum_chebyshevWeight_mul_norm_sq_add_norm_sq` is at most
$\eta^2 \sum_j \omega_j = \eta^2\,T_k(\cdot)$ (`NLAlib.sum_chebyshevWeight`), hence
$T_k(\cdot)^{-1} \le \eta$. M, about 50 lines. -/
theorem residualMinimax_Icc_union_Icc {a a' : ℝ} (q : ℕ) (ha : 0 < a) (haa : a < a') :
    residualMinimax (Set.Icc (-a') (-a) ∪ Set.Icc a a') q =
      ((T ℝ ((q / 2 : ℕ) : ℤ)).eval ((a' ^ 2 + a ^ 2) / (a' ^ 2 - a ^ 2)))⁻¹ := by
  sorry

/-- The Chebyshev value on $[1, \kappa^2]$ decays at most like $e^{-4k/\kappa}$: for
$\kappa \ge 2$ and every $k$,
$$e^{-4k/\kappa} \le T_k\Bigl(\frac{\kappa^2 + 1}{\kappa^2 - 1}\Bigr)^{-1} \,.$$
[Shamir2026, Lemma 1]; there through $T_k(\cosh\theta) = \cosh(k\theta) \le e^{k\theta}$ with
$\theta = \log((\kappa + 1)/(\kappa - 1)) \le 4/\kappa$.
Proof: `NLAlib.inv_eval_T_real_eq_two_mul_pow_div` with $a = 1$, $a' = \kappa^2$ gives
$2\rho^k/(1 + \rho^{2k}) \ge \rho^k$ for $\rho = (\kappa - 1)/(\kappa + 1) \in [0, 1)$
(`Real.sqrt_sq`); and $\rho \ge e^{-4/\kappa}$ because
$\log(1 + 2/(\kappa - 1)) \le 2/(\kappa - 1) \le 4/\kappa$ for $\kappa \ge 2$
(`Real.add_one_le_exp`, `Real.exp_le_exp`, `pow_le_pow_left₀`). S, about 25 lines. -/
theorem exp_neg_le_inv_eval_T_real {κ : ℝ} (hκ : 2 ≤ κ) (k : ℕ) :
    Real.exp (-(4 * k / κ)) ≤ ((T ℝ (k : ℤ)).eval ((κ ^ 2 + 1) / (κ ^ 2 - 1)))⁻¹ := by
  have hk := inv_eval_T_real_eq_two_mul_pow_div (a := 1) (a' := κ ^ 2) k one_pos (by nlinarith)
  rw [hk, div_one, Real.sqrt_sq (by linarith)]
  have hκ1 : 0 < κ - 1 := by linarith
  have hκ2 : 0 < κ + 1 := by linarith
  have hρ0 : 0 ≤ (κ - 1) / (κ + 1) := (div_pos hκ1 hκ2).le
  have hρ1 : (κ - 1) / (κ + 1) ≤ 1 := (div_le_one hκ2).mpr (by linarith)
  have hexp : Real.exp (-(4 / κ)) ≤ (κ - 1) / (κ + 1) := by
    have h2 : (κ + 1) / (κ - 1) = 1 + 2 / (κ - 1) := by
      field_simp
      ring
    have h3 : 2 / (κ - 1) ≤ 4 / κ := by
      rw [div_le_div_iff₀ hκ1 (by linarith)]
      linarith
    have h4 : (κ + 1) / (κ - 1) ≤ Real.exp (4 / κ) := by
      have := Real.add_one_le_exp (2 / (κ - 1))
      have := Real.exp_le_exp.mpr h3
      rw [h2]
      linarith
    rw [Real.exp_neg, show (κ - 1) / (κ + 1) = ((κ + 1) / (κ - 1))⁻¹ by rw [inv_div]]
    exact inv_anti₀ (div_pos hκ2 hκ1) h4
  have hexpk : Real.exp (-(4 * k / κ)) = (Real.exp (-(4 / κ))) ^ k := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexpk]
  refine (pow_le_pow_left₀ (Real.exp_nonneg _) hexp k).trans ?_
  have hpow : ((κ - 1) / (κ + 1)) ^ (2 * k) ≤ 1 := pow_le_one₀ hρ0 hρ1
  rw [le_div_iff₀ (by positivity)]
  nlinarith [mul_le_of_le_one_right (pow_nonneg hρ0 k) hpow, pow_nonneg hρ0 k]

/-- **Polynomial inapproximability on two intervals**: for $\kappa \ge 2$ and every $q$, every
real polynomial $p$ of degree at most $q$ with $p(0) = 0$ has
$\max_{\lambda \in [-\kappa, -1] \cup [1, \kappa]} \lvert 1 - p(\lambda) \rvert \ge e^{-2q/\kappa}$:
$$e^{-2q/\kappa} \le \mathsf{residualMinimax}\bigl([-\kappa, -1] \cup [1, \kappa], q\bigr) \,.$$
[Shamir2026, Lemma 1]; there $\rho_d(\kappa)$, the infimum over $p(0) = 0$ of the maximum of
$\lvert 1 - p \rvert$, which is `NLAlib.residualMinimax` of the residual $1 - p$.
Proof: `NLAlib.residualMinimax_Icc_union_Icc` with $a = 1$, $a' = \kappa$, then
`NLAlib.exp_neg_le_inv_eval_T_real` with $k = \lfloor q/2 \rfloor$ and $4k \le 2q$
(`Nat.mul_div_le`, `Real.exp_le_exp`). S, 10 lines.
Result: polynomial-two-interval-inapproximability -/
theorem exp_neg_le_residualMinimax_Icc_union_Icc {κ : ℝ} (hκ : 2 ≤ κ) (q : ℕ) :
    Real.exp (-(2 * q / κ)) ≤ residualMinimax (Set.Icc (-κ) (-1) ∪ Set.Icc 1 κ) q := by
  sorry

/-- **Weighted inapproximability on two intervals**: for $0 < a < a'$ there are at most $q + 2$
points of $S = [-a', -a] \cup [a, a']$ and positive weights summing to $1$ on them such that every
$p \in \Bbbk[X]$ with $\deg p \le q$ and $p(0) = 1$ has
$$\mathsf{residualMinimax}(S, q)^2 \le \sum_x w_x \lvert p(x) \rvert^2 \,.$$
The points are $\pm\sqrt{\xi_j}$ for the Chebyshev extrema $\xi_j$ of $[a^2, a'^2]$, with weights
$\omega_j/(2\tau)$, $\tau = \sum_j \omega_j$. The reverse inequality holds for every probability
vector, so the infimum over residuals of the weighted sum is the squared minimax value.
[Shamir2026, Lemma 2]; there with at most $q + 1$ points, from the Kroó–Pinkus
characterization (Kroó and Pinkus 2010, Theorem 2.3), here with the explicit Chebyshev points
($2\lfloor q/2 \rfloor + 2$ of them) and no characterization theorem.
Proof: the image of $(j, \pm) \mapsto \pm\sqrt{\xi_j}$ (`Finset.image`, injective by
`NLAlib.strictMono_chebyshevExtremum` and positivity), weights from `NLAlib.chebyshevWeight_pos`
and `NLAlib.sum_chebyshevWeight`; the bound is
`NLAlib.inv_eval_T_real_le_sum_chebyshevWeight_mul_norm_sq_add_norm_sq` divided by $\tau$, with
`NLAlib.residualMinimax_Icc_union_Icc` for the left side. M, about 45 lines. -/
theorem exists_residualMinimax_Icc_union_Icc_sq_le_sum_mul_norm_sq (𝕜 : Type*) [RCLike 𝕜]
    {a a' : ℝ} (ha : 0 < a) (haa : a < a') (q : ℕ) :
    ∃ s : Finset ℝ, (↑s : Set ℝ) ⊆ Set.Icc (-a') (-a) ∪ Set.Icc a a' ∧ s.card ≤ q + 2 ∧
      ∃ w : ℝ → ℝ, (∀ x ∈ s, 0 < w x) ∧ ∑ x ∈ s, w x = 1 ∧
        ∀ p : 𝕜[X], p.degree ≤ q → p.eval 0 = 1 →
          residualMinimax (Set.Icc (-a') (-a) ∪ Set.Icc a a') q ^ 2 ≤
            ∑ x ∈ s, w x * ‖p.eval (x : 𝕜)‖ ^ 2 := by
  sorry

variable {n : Type*} [Fintype n]

/-- The values of a Chebyshev two-interval spectrum lie in $[-\kappa, -1] \cup [1, \kappa]$ for
$\kappa > 1$.
Proof: each value is $\pm\sqrt{\xi_j}$ (`NLAlib.IsChebyshevTwoIntervalSpectrum.exists_eq`) with
$\xi_j \in [1, \kappa^2]$ (`NLAlib.chebyshevExtremum_mem_Icc`); `Real.sqrt_le_sqrt`,
`Real.sqrt_sq`, `Real.one_le_sqrt`. S, 10 lines. -/
theorem IsChebyshevTwoIntervalSpectrum.mem_Icc_union_Icc {κ : ℝ} {s M : ℕ} {d : n → ℝ}
    (hd : IsChebyshevTwoIntervalSpectrum κ s M d) (hκ : 1 < κ) (i : n) :
    d i ∈ Set.Icc (-κ) (-1) ∪ Set.Icc 1 κ := by
  obtain ⟨j, h | h⟩ := hd.exists_eq i
  · have hξ := chebyshevExtremum_mem_Icc (a := 1) (a' := κ ^ 2) (by nlinarith) (s / 2) j
    have h1 : 1 ≤ Real.sqrt (chebyshevExtremum 1 (κ ^ 2) (s / 2) j) :=
      Real.one_le_sqrt.mpr hξ.1
    have h2 : Real.sqrt (chebyshevExtremum 1 (κ ^ 2) (s / 2) j) ≤ κ :=
      (Real.sqrt_le_sqrt hξ.2).trans_eq (Real.sqrt_sq (by linarith))
    rw [h]
    exact Set.mem_union_right _ ⟨h1, h2⟩
  · have hξ := chebyshevExtremum_mem_Icc (a := 1) (a' := κ ^ 2) (by nlinarith) (s / 2) j
    have h1 : 1 ≤ Real.sqrt (chebyshevExtremum 1 (κ ^ 2) (s / 2) j) :=
      Real.one_le_sqrt.mpr hξ.1
    have h2 : Real.sqrt (chebyshevExtremum 1 (κ ^ 2) (s / 2) j) ≤ κ :=
      (Real.sqrt_le_sqrt hξ.2).trans_eq (Real.sqrt_sq (by linarith))
    rw [h]
    exact Set.mem_union_left _ ⟨by linarith, by linarith⟩

/-- **Weighted residual bound on a Chebyshev two-interval spectrum**: for $\kappa > 1$, a
Chebyshev two-interval spectrum $d$ with depth $s$ and margin $M$, and every real $p$ with
$\deg p \le s$ and $p(0) = 1$,
$$\frac{\lvert n \rvert}{4}\,T_k\Bigl(\frac{\kappa^2 + 1}{\kappa^2 - 1}\Bigr)^{-2} \le
\sum_{t} \bigl(m_t - M\bigr)\,p(t)^2 \,,$$
the sum over the distinct values $t$ of $d$, $m_t$ the number of $i$ with $d_i = t$, and
$k = \lfloor s/2 \rfloor$.
Proof: each of the $2(k + 1)$ points has $m_t - M \ge \lvert n \rvert\omega_j/(8\tau)$
(`NLAlib.IsChebyshevTwoIntervalSpectrum.le_card_pos`, `le_card_neg`); every value of $d$ is a
point (`NLAlib.IsChebyshevTwoIntervalSpectrum.exists_eq`), so the sum over values is the sum over
the points (`Finset.sum_image`, `Finset.sum_le_sum`); then
`NLAlib.inv_eval_T_real_le_sum_chebyshevWeight_mul_norm_sq_add_norm_sq` with $a = 1$, $a' =
\kappa$ times $\lvert n \rvert/(4\tau)$. M, about 40 lines. -/
theorem IsChebyshevTwoIntervalSpectrum.inv_sq_le_sum_card_sub_mul_eval_sq {κ : ℝ} {s M : ℕ}
    {d : n → ℝ} (hd : IsChebyshevTwoIntervalSpectrum κ s M d) (hκ : 1 < κ) {p : ℝ[X]}
    (hp : p.degree ≤ s) (hp₀ : p.eval 0 = 1) :
    (Fintype.card n : ℝ) / 4 * ((T ℝ ((s / 2 : ℕ) : ℤ)).eval ((κ ^ 2 + 1) / (κ ^ 2 - 1)))⁻¹ ^ 2 ≤
      ∑ t ∈ Finset.univ.image d,
        (((Finset.univ.filter fun i => d i = t).card : ℝ) - M) * p.eval t ^ 2 := by
  sorry

/-- Realize prescribed multiplicities: an injective list of values `v` on `ι` and counts `c`
summing to `|n|` give `d : n → ℝ` with values in `range v` and fibre cardinalities `c`. -/
private lemma exists_fun_card_fiber {ι : Type*} [Fintype ι] (v : ι → ℝ)
    (hv : Function.Injective v) (c : ι → ℕ) (hc : ∑ t, c t = Fintype.card n) :
    ∃ d : n → ℝ, (∀ i, ∃ t, d i = v t) ∧
      ∀ t, (Finset.univ.filter fun i => d i = v t).card = c t := by
  classical
  have hcard : Fintype.card n = Fintype.card (Σ t, Fin (c t)) := by
    rw [Fintype.card_sigma]; simp only [Fintype.card_fin]; exact hc.symm
  let e : n ≃ Σ t, Fin (c t) := Fintype.equivOfCardEq hcard
  refine ⟨fun i => v (e i).1, fun i => ⟨(e i).1, rfl⟩, fun t => ?_⟩
  have hfilt : (Finset.univ.filter fun i => v (e i).1 = v t) =
      Finset.univ.filter fun i => (e i).1 = t :=
    Finset.filter_congr fun i _ => hv.eq_iff
  rw [hfilt, Finset.card_filter]
  refine (e.sum_comp (fun x => if x.1 = t then (1 : ℕ) else 0)).trans ?_
  rw [Fintype.sum_sigma,Finset.sum_eq_single t (fun b _ hb => by simp [hb]) (by simp)]
  simp

/-- The signed Chebyshev points `(j, true) ↦ √ξ_j`, `(j, false) ↦ -√ξ_j` are injective. -/
private lemma chebyshevPoint_injective {κ : ℝ} (hκ : 1 < κ) (s : ℕ) :
    Function.Injective fun t : Fin (s / 2 + 1) × Bool =>
      if t.2 then √(chebyshevExtremum 1 (κ ^ 2) (s / 2) t.1)
      else -√(chebyshevExtremum 1 (κ ^ 2) (s / 2) t.1) := by
  have hlt : (1 : ℝ) < κ ^ 2 := by nlinarith
  have hpos : ∀ j : Fin (s / 2 + 1), 0 < √(chebyshevExtremum 1 (κ ^ 2) (s / 2) j) :=
    fun j => Real.sqrt_pos.2 (by linarith [(chebyshevExtremum_mem_Icc hlt.le (s / 2) j).1])
  have hnn : ∀ j : Fin (s / 2 + 1), 0 ≤ chebyshevExtremum 1 (κ ^ 2) (s / 2) j :=
    fun j => by linarith [(chebyshevExtremum_mem_Icc hlt.le (s / 2) j).1]
  have hinj : ∀ j j' : Fin (s / 2 + 1), chebyshevExtremum 1 (κ ^ 2) (s / 2) j =
      chebyshevExtremum 1 (κ ^ 2) (s / 2) j' → j = j' := fun j j' h =>
    (strictMono_chebyshevExtremum hlt (s / 2)).injective h
  rintro ⟨j, b⟩ ⟨j', b'⟩ h
  cases b <;> cases b' <;> simp only [if_true, if_false, Bool.false_eq_true] at h
  all_goals first
    | (exfalso; linarith [hpos j, hpos j'])
    | rw [hinj j j' ((Real.sqrt_inj (hnn j) (hnn j')).1 h)]
    | rw [hinj j j' ((Real.sqrt_inj (hnn j) (hnn j')).1 (neg_inj.1 h))]

/-- **Chebyshev two-interval spectra exist** in every dimension
$\lvert n \rvert \ge \tfrac43 (s + 2)(M + 1)$: for $\kappa > 1$ and
$4(s + 2)(M + 1) \le 3\lvert n \rvert$ there is a Chebyshev two-interval spectrum on $n$ with
depth $s$ and margin $M$.
Proof: list the $L = 2(\lfloor s/2 \rfloor + 1) \le s + 2$ points; give point $j$ multiplicity
$\lceil \lvert n \rvert w_j/4 \rceil + M$ ($w_j = \omega_j/(2\tau)$, `Nat.ceil`), the last point
the rest; the total is at most $\lvert n \rvert/4 + L(M + 1) \le \lvert n \rvert$
(`NLAlib.sum_chebyshevWeight`, `Nat.ceil_lt_add_one`). Realize the multiplicities by a function
on `Fin (Fintype.card n)` through `Fintype.equivFin`, constant on consecutive blocks. M, about 60
lines. -/
theorem exists_isChebyshevTwoIntervalSpectrum {κ : ℝ} (hκ : 1 < κ) {s M : ℕ}
    (hn : 4 * ((s + 2) * (M + 1)) ≤ 3 * Fintype.card n) :
    ∃ d : n → ℝ, IsChebyshevTwoIntervalSpectrum κ s M d := by
  classical
  -- points: `(j, true) ↦ √ξ_j`, `(j, false) ↦ -√ξ_j`
  set ξ : Fin (s / 2 + 1) → ℝ := fun j => chebyshevExtremum 1 (κ ^ 2) (s / 2) j with hξ
  set ω : Fin (s / 2 + 1) → ℝ := fun j => chebyshevWeight 1 (κ ^ 2) (s / 2) j with hω
  set τ : ℝ := (T ℝ ((s / 2 : ℕ) : ℤ)).eval ((κ ^ 2 + 1) / (κ ^ 2 - 1)) with hτ
  have hτ1 : 1 ≤ τ := one_le_eval_T_real _ (by rw [le_div_iff₀ (by nlinarith)]; nlinarith)
  have hsum : ∑ j, ω j = τ := sum_chebyshevWeight zero_lt_one (by nlinarith) (s / 2)
  let v : Fin (s / 2 + 1) × Bool → ℝ := fun t => if t.2 then √(ξ t.1) else -√(ξ t.1)
  have hv : Function.Injective v := chebyshevPoint_injective hκ s
  -- real multiplicity bounds
  let B : Fin (s / 2 + 1) → ℝ := fun j => (Fintype.card n : ℝ) / 4 * (ω j / (2 * τ)) + M
  have hB0 : ∀ j, 0 ≤ B j := fun j => by
    have h1 : 0 ≤ ω j / (2 * τ) := div_nonneg (abs_nonneg _) (by linarith)
    have h2 : (0 : ℝ) ≤ (Fintype.card n : ℝ) / 4 := by positivity
    have h3 : (0 : ℝ) ≤ M := by positivity
    exact add_nonneg (mul_nonneg h2 h1) h3
  have hsumU : ∀ f : Fin (s / 2 + 1) → ℝ,
      ∑ u : Fin (s / 2 + 1) × Bool, f u.1 = 2 * ∑ j, f j := by
    intro f
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, two_mul, Finset.sum_add_distrib]
  have hsumB8 : ∑ j, B j = (Fintype.card n : ℝ) / 8 + ((s / 2 + 1 : ℕ) : ℝ) * M := by
    simp only [B, div_eq_mul_inv]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hsum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hτne : τ ≠ 0 := by linarith
    field_simp
    ring
  have hPR : 2 * ((s / 2 + 1 : ℕ) : ℝ) ≤ (s : ℝ) + 2 := by
    have : 2 * (s / 2 + 1) ≤ s + 2 := by omega
    exact_mod_cast this
  have hnR : 4 * (((s : ℝ) + 2) * ((M : ℝ) + 1)) ≤ 3 * (Fintype.card n : ℝ) := by
    exact_mod_cast hn
  have hsumB : ∑ u : Fin (s / 2 + 1) × Bool, ⌈B u.1⌉₊ ≤ Fintype.card n := by
    have h3 : ((∑ u : Fin (s / 2 + 1) × Bool, ⌈B u.1⌉₊ : ℕ) : ℝ) ≤ (Fintype.card n : ℝ) := by
      push_cast
      calc ∑ u : Fin (s / 2 + 1) × Bool, (⌈B u.1⌉₊ : ℝ)
          ≤ ∑ u : Fin (s / 2 + 1) × Bool, (B u.1 + 1) :=
            Finset.sum_le_sum fun u _ => (Nat.ceil_lt_add_one (hB0 u.1)).le
        _ = (Fintype.card n : ℝ) / 4 + 2 * ((s / 2 + 1 : ℕ) : ℝ) * (M + 1) := by
            rw [Finset.sum_add_distrib, hsumU B]
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
              Fintype.card_bool, nsmul_eq_mul, hsumB8]
            push_cast
            ring
        _ ≤ Fintype.card n := by
            nlinarith [mul_le_mul_of_nonneg_right hPR (by positivity : (0 : ℝ) ≤ (M : ℝ) + 1)]
    exact_mod_cast h3
  let c : Fin (s / 2 + 1) × Bool → ℕ := fun t =>
    ⌈B t.1⌉₊ + if t = (0, true) then Fintype.card n - ∑ u : Fin (s / 2 + 1) × Bool, ⌈B u.1⌉₊
      else 0
  have hc : ∑ t, c t = Fintype.card n := by
    simp only [c, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    omega
  obtain ⟨d, hd1, hd2⟩ := exists_fun_card_fiber v hv c hc
  refine ⟨d, ⟨fun i => ?_, fun j => ?_, fun j => ?_⟩⟩
  · obtain ⟨⟨j, b⟩, hi⟩ := hd1 i
    cases b
    · exact ⟨j, Or.inr hi⟩
    · exact ⟨j, Or.inl hi⟩
  · have key : (Finset.univ.filter fun i => d i = √(ξ j)).card = c (j, true) := hd2 (j, true)
    have hc1 : ((⌈B j⌉₊ : ℕ) : ℝ) ≤ (c (j, true) : ℝ) := by
      exact_mod_cast Nat.le_add_right _ _
    change B j ≤ ((Finset.univ.filter fun i => d i =√(ξ j)).card : ℝ)
    rw [key]
    linarith [Nat.le_ceil (B j)]
  · have key : (Finset.univ.filter fun i => d i = -√(ξ j)).card = c (j, false) := hd2 (j, false)
    have hc1 : ((⌈B j⌉₊ : ℕ) : ℝ) ≤ (c (j, false) : ℝ) := by
      exact_mod_cast Nat.le_add_right _ _
    change B j ≤ ((Finset.univ.filter fun i => d i =-√(ξ j)).card : ℝ)
    rw [key]
    linarith [Nat.le_ceil (B j)]

end NLAlib
