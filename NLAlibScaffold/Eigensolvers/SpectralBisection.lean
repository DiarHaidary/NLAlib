/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.Global
public import NLAlibScaffold.Eigensolvers.RandomizedDeflation
public import NLAlibScaffold.Matrix.Computation.SpectralBisection

/-!
# Hermitian diagonalization with a sharper precision bound (scaffold, stage HDIAG-BOUNDS)

Statements for `NLAlib/Eigensolvers/SpectralBisection.lean` and its `Global` file (design note
`docs/design/Eigensolvers-HermitianDiagonalization-Bounds.md`): the node bad-event bound with the
sharper Gaussian tails (EV2'), and [Shah2024, Theorem 4.2] with a size-weighted union bound, in
tail form (EV6') and in bits (EV7'):
$$\log_2\frac1u \ge \log_2\frac1\varepsilon + \frac32\log_2\frac1\theta + \log_2(n\nu) +
\tfrac12\log_2\bigl(n\min(n, \ell + 1)\min(n, e)\bigr) + \log_2\hat T + 3\log_2\ell +
\log_2 20 + 13 + o(1) \,,$$
$\nu = 4\mu_{\mathrm{MM}}(n) + 10 + 10\sqrt n$, against EV7's
$\log_2(n^4(n + 1)(8 + \mu_{\mathrm{MM}})) + \log_2(N_* + 1) + 26$ for the same leading terms.

## Main results

* `NLAlib.FloatMachine.IsAccurate.measure_not_isEighGoodSample_le_of_isEighNodeBudget` (EV2').
* [EV6'](https://nla-lib.org/explore/#d/NLAlib.FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_hasLaw_eighSampleLaw').
* [EV7'](https://nla-lib.org/explore/#d/NLAlib.FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_logb_le_of_hasLaw_eighSampleLaw').
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder ENNReal

namespace NLAlib

-- A docstring line exceeds 100 characters.
set_option linter.style.longLine false in
/-- **Bad events of one node under a node budget** (EV2'): at an internal node of size
$2 \le k \le N$ with budget `NLAlib.FloatMachine.IsEighNodeBudget` at $x = \sqrt{15\rho/(16
\min(k^2, e k))}$ and $t = 2\sqrt2\sqrt k + \sqrt{\log(16/\rho)}$, $0 < \rho \le 1$, the sample
law gives the complement of the good event mass at most $kw\ell/R + 2\rho\,\mathbb{P}[\text{the
step splits}]$. [Shah2024, Lemma 4.1], the probabilities of Events I and II.
Proof: EV2's proof with EB1b' for the split criterion and DP1'
(`NLAlib.FloatMachine.IsAccurate.measureReal_not_exists_specNorm_mul_sub_deflate_le_le_of_hasLaw_complexGaussianMatrix'`)
in place of DP1, or directly its two tails: the norm event fails with probability at most
$e^{-\log(16/\rho)} = \rho/16$
(`NLAlib.measureReal_specNorm_ge_add_le_of_hasLaw_complexGaussianMatrix` on the leading block),
the singular value event at most $\min(r^2, e r)x^2 \le 15\rho/16$ for $r < k$
(CG6 and `NLAlib.measureReal_singularValues_le_le_exp_one_mul_of_hasLaw_complexGaussianMatrix`),
for each side; Event I by `NLAlib.measureReal_exists_abs_sub_lt_le`. L, about 150 lines (EV2's
measurable-superset route reused). -/
theorem FloatMachine.IsAccurate.measure_not_isEighGoodSample_le_of_isEighNodeBudget
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ}
    {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) {N signFuel : ℕ} {R₀ β : F}
    {ρ w : ℝ} {y : EighNode F}
    (hB : M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel w
      (√(15 * ρ / (16 * min ((y.k : ℝ) ^ 2) (Real.exp 1 * y.k))))
      (2 * √2 * √(y.k : ℝ) + √(Real.log (16 / ρ))) y)
    (hk : 2 ≤ y.k) (hkN : y.k ≤ N) (hint : M.le y.R (M.mul y.ε R₀) = false) (hρ : 0 < ρ)
    (hρ₁ : ρ ≤ 1) :
    eighSampleLaw N {s | ¬ IsEighGoodSample dec w
      (√(15 * ρ / (16 * min ((y.k : ℝ) ^ 2) (Real.exp 1 * y.k))))
      (2 * √2 * √(y.k : ℝ) + √(Real.log (16 / ρ))) y s} ≤
      ENNReal.ofReal (y.k * w * y.ℓ / dec y.R) + ENNReal.ofReal (2 * ρ) *
        eighSampleLaw N {s | (eighStep M N signFuel R₀ β y.A y.R y.ε y.ℓ s).IsSplit} := by
  sorry

/-- **Hermitian diagonalization in linear precision, sharp budget** (EV6'): under the hypotheses
of EB5' (`NLAlib.FloatMachine.IsAccurate.isApproxDiagonalization_eigh_of_forall_isEighGoodSample'`)
without its good-sample hypothesis, with samplers with measurable fibres and countable ranges and
independent node samples, each of law `NLAlib.eighSampleLaw` $n$, the probability that
`NLAlib.eigh` is not an approximate diagonalization with residual $2\varepsilon R_0$ and singular
values within $\varepsilon/3$ of $1$ is at most $\theta$. [Shah2024, Theorem 4.2].
Proof: EV6's route (UB1 with the measurability and independence of EV3–EV5) with EB5' and the
charge of a node $y$: $q_y = k_y w_y\ell_y/R_y + 2\rho_y[\text{split}] =
4\theta k_y\ell_y/(9n\ell(\ell + 1)) + \theta k_y/(3nm)[\text{split}]$ (EV2', at
$\rho_y = \theta k_y/(6nm)$). Surely
$\sum_y q_y \le \theta$: by EB3' the sizes at each depth $j \le \ell$ (EB2) sum to at most $n$, so
the first part is at most $\tfrac{4\theta}{9\ell(\ell + 1)}\sum_{j=0}^{\ell}(\ell + j) =
\tfrac23\theta$; the split sizes sum to at most $n\min(n, \ell + 1)$ (EB3' over the depths, and
EB4 with $k_y \le n$), so the second part is at most $\theta/3$. L, about 250 lines (EV6's
assembly reused; the charge sum replaces `tsum_eighNodeAt_charge_le`). -/
theorem
    FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_hasLaw_eighSampleLaw'
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hunifm : ∀ c z, MeasurableSet (M.unif c ⁻¹' {z}))
    (hunifc : ∀ c, (Set.range (M.unif c)).Countable)
    (hnormalm : ∀ z, MeasurableSet (M.normal ⁻¹' {z})) (hnormalc : (Set.range M.normal).Countable)
    (hμM : Monotone μM) (hμQ : Monotone μQ) (hμM₀ : 0 ≤ μM 0) (hμQ₀ : 0 ≤ μQ 0) (hcN : 0 ≤ cN)
    {n : ℕ} {A : Matrix (Fin n) (Fin n) (F × F)} (hA : (decodeMatrix dec A).IsHermitian)
    {R₀ ε β : F} {θ : ℝ} (hR₀ : specNorm (decodeMatrix dec A) ≤ dec R₀) (hR₀pos : 0 < dec R₀)
    (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) {ℓ : ℕ}
    (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hβ : 0 < dec β)
    (hβle : dec β ≤ ((ℓ : ℝ) - 1) ^ 2 * dec ε * √θ / (52 * (ℓ : ℝ) ^ 2 * (2 * ℓ - 1) *
      √(n * min (n : ℝ) (ℓ + 1) * min (n : ℝ) (Real.exp 1)) *
      (2 * √2 * √(n : ℝ) + √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ))))) {Nst : ℝ}
    (hN : Nst = newtonSchulzSteps (θ / (12 * n * ℓ * (ℓ + 1))) (dec β / (16 * n)))
    (husign : 146 * n * ℓ * (ℓ + 1) * (4 * μM n + 10 + 10 * √(n : ℝ)) * u ≤ θ * dec β)
    (hustop : 2048 * (n + Nst + 1) * (4 * μM n + 10 + 10 * √(n : ℝ)) * u ≤ dec β)
    (hudefl : 16 * (4 * μQ n + 4 * √(n : ℝ) * (cN + 1) + 2 * μM n + 1) * u ≤ dec β)
    {signFuel : ℕ} (hfuel : Nst ≤ signFuel) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (100 * n * √(n : ℝ)) ≤
      min (√(θ / (8 * n * min (n : ℝ) (ℓ + 1)))) (dec ε * min (dec R₀) 1))
    (hΩ : 16 * (2 * dec R₀ + n + 2 * ℓ + 2 * √2 * √(n : ℝ) +
      √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ))) ≤ Ω) {Ω' : Type*}
    {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'} {ζ : List Bool → Ω' → EighSample ℝ ℂ n}
    (hind : iIndepFun ζ μ) (hlaw : ∀ a, HasLaw (ζ a) (eighSampleLaw n) μ) :
    μ.real {ω | ¬ IsApproxDiagonalization (decodeMatrix dec A)
      (decodeMatrix dec (eigh M signFuel ℓ A R₀ ε β fun a => ζ a ω).1)
      (fun i => dec ((eigh M signFuel ℓ A R₀ ε β fun a => ζ a ω).2 i)) (2 * dec ε * dec R₀)
      (dec ε / 3)} ≤ θ := by
  sorry

-- The declaration name and a docstring line exceed 100 characters.
set_option linter.style.longLine false in
/-- **The bit count of Hermitian diagonalization, sharp budget** (EV7'): under the hypotheses of
EV6' with the precision conditions replaced by $u > 0$, the accuracy within $1 + 2^{-6}$ of its
bound, $\hat\beta/(1 + 2^{-6}) \le \beta \le \hat\beta$, and
$$\begin{aligned}\log_2\frac1u \ge{}& \log_2\frac1\varepsilon + \frac32\log_2\frac1\theta +
\log_2\bigl(n(4\mu_{\mathrm{MM}}(n) + 10 + 10\sqrt n)\bigr) +
\tfrac12\log_2\bigl(n\min(n, \ell + 1)\min(n, e)\bigr) \\ &+ \log_2\hat T + \log_2(\ell(\ell + 1)) +
\log_2\frac{\ell^2(2\ell - 1)}{(\ell - 1)^2} + 13 \,,\end{aligned}$$
$\hat T = 2\sqrt2\sqrt n + \sqrt{\log(96n\min(n, \ell + 1)/\theta)}$, together with the
non-binding condition $\log_2(1/u) \ge \log_2(1/\beta) + \log_2(2048(n + N_* + 1)\nu +
16(4\mu_{\mathrm{QR}}(n) + 4\sqrt n(c_{\mathrm N} + 1) + 2\mu_{\mathrm{MM}}(n) + 1))$, the failure
probability is at most $\theta$. This is $\log_2(1/\varepsilon) + \tfrac32\log_2(1/\theta) +
O(\log n + \log\log(1/\varepsilon))$ with $n^{2.5}\max(\mu_{\mathrm{MM}}, \sqrt n)$ in place of
EV7's $n^5\mu_{\mathrm{MM}}$ and no $\log_2(N_* + 1)$ term. [Shah2024, Theorem 4.2], there
$\log_2\max(n^{1.5}\mu_{\mathrm{QR}}, n^2c_{\mathrm N}, n^{4.5}\mu_{\mathrm{MM}}) +
2\log_2\log_2(1/\varepsilon) + \log_2\log_2(n\log_2(1/\varepsilon)/\theta) + 23$.
Proof: exponentiate the first condition as in EV7 (`mul_le_mul_mul_sqrt_of_logb_le`'s pattern):
with $\beta \ge \hat\beta/(1 + 2^{-6})$ it gives $146n\ell(\ell + 1)\nu u \le \theta\beta$, since
$146 \cdot 52 \cdot (1 + 2^{-6}) \le 2^{13}$; the second gives the stopping and deflation
conditions of EV6'; then EV6'. M, about 120 lines. -/
theorem
    FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_logb_le_of_hasLaw_eighSampleLaw'
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hunifm : ∀ c z, MeasurableSet (M.unif c ⁻¹' {z}))
    (hunifc : ∀ c, (Set.range (M.unif c)).Countable)
    (hnormalm : ∀ z, MeasurableSet (M.normal ⁻¹' {z})) (hnormalc : (Set.range M.normal).Countable)
    (hμM : Monotone μM) (hμQ : Monotone μQ) (hμM₀ : 0 ≤ μM 0) (hμQ₀ : 0 ≤ μQ 0) (hcN : 0 ≤ cN)
    {n : ℕ} {A : Matrix (Fin n) (Fin n) (F × F)} (hA : (decodeMatrix dec A).IsHermitian)
    {R₀ ε β : F} {θ : ℝ} (hR₀ : specNorm (decodeMatrix dec A) ≤ dec R₀) (hR₀pos : 0 < dec R₀)
    (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) {ℓ : ℕ}
    (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hβ : 0 < dec β)
    (hβle : dec β ≤ ((ℓ : ℝ) - 1) ^ 2 * dec ε * √θ / (52 * (ℓ : ℝ) ^ 2 * (2 * ℓ - 1) *
      √(n * min (n : ℝ) (ℓ + 1) * min (n : ℝ) (Real.exp 1)) *
      (2 * √2 * √(n : ℝ) + √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ)))))
    (hβge : ((ℓ : ℝ) - 1) ^ 2 * dec ε * √θ / (52 * (ℓ : ℝ) ^ 2 * (2 * ℓ - 1) *
        √(n * min (n : ℝ) (ℓ + 1) * min (n : ℝ) (Real.exp 1)) *
        (2 * √2 * √(n : ℝ) + √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ)))) /
      (1 + 2⁻¹ ^ 6) ≤ dec β) {Nst : ℝ}
    (hN : Nst = newtonSchulzSteps (θ / (12 * n * ℓ * (ℓ + 1))) (dec β / (16 * n)))
    (hu : 0 < u)
    (hbits : Real.logb 2 (dec ε)⁻¹ + 3 / 2 * Real.logb 2 θ⁻¹ +
      Real.logb 2 (n * (4 * μM n + 10 + 10 * √(n : ℝ))) +
      1 / 2 * Real.logb 2 (n * min (n : ℝ) (ℓ + 1) * min (n : ℝ) (Real.exp 1)) +
      Real.logb 2 (2 * √2 * √(n : ℝ) + √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ))) +
      Real.logb 2 (ℓ * (ℓ + 1)) + Real.logb 2 ((ℓ : ℝ) ^ 2 * (2 * ℓ - 1) / ((ℓ : ℝ) - 1) ^ 2) +
      13 ≤ Real.logb 2 u⁻¹)
    (hbits' : Real.logb 2 (dec β)⁻¹ +
      Real.logb 2 (2048 * (n + Nst + 1) * (4 * μM n + 10 + 10 * √(n : ℝ)) +
      16 * (4 * μQ n + 4 * √(n : ℝ) * (cN + 1) + 2 * μM n + 1)) ≤ Real.logb 2 u⁻¹)
    {signFuel : ℕ} (hfuel : Nst ≤ signFuel) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (100 * n * √(n : ℝ)) ≤
      min (√(θ / (8 * n * min (n : ℝ) (ℓ + 1)))) (dec ε * min (dec R₀) 1))
    (hΩ : 16 * (2 * dec R₀ + n + 2 * ℓ + 2 * √2 * √(n : ℝ) +
      √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ))) ≤ Ω) {Ω' : Type*}
    {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'} {ζ : List Bool → Ω' → EighSample ℝ ℂ n}
    (hind : iIndepFun ζ μ) (hlaw : ∀ a, HasLaw (ζ a) (eighSampleLaw n) μ) :
    μ.real {ω | ¬ IsApproxDiagonalization (decodeMatrix dec A)
      (decodeMatrix dec (eigh M signFuel ℓ A R₀ ε β fun a => ζ a ω).1)
      (fun i => dec ((eigh M signFuel ℓ A R₀ ε β fun a => ζ a ω).2 i)) (2 * dec ε * dec R₀)
      (dec ε / 3)} ≤ θ := by
  sorry

end NLAlib
