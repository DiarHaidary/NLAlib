/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Eigenvalues.PowerIteration
public import NLAlib.Krylov.Eigenvalues.Ritz
public import NLAlib.Probability.Distributions.GaussianLogOverlap
public import NLAlib.Probability.Measurability.Krylov
public import NLAlib.Probability.Measurability.Matrix

/-!
# Estimating the largest eigenvalue from a random start

For a positive semidefinite real $\mathbf{A}$ and a standard Gaussian start $\mathbf{g}$, the
power method and the Lanczos method estimate $\lambda_0 = \lambda_0(\mathbf{A})$ with an expected
error that depends on the dimension $N = \lvert n\rvert$ only through $\log N$, with no gap:
after $q$ multiplications the power method's Rayleigh quotient is within
$\lambda_0(\log(2N) + 2)/(2q + 1)$ of $\lambda_0$ on average, and the largest Ritz value of
$\mathcal{K}_{q+1}(\mathbf{A}, \mathbf{g})$ within $O(\lambda_0\log(N)^2/q^2)$. The bounds hold
for every dimension, repeated top eigenvalues and $\mathbf{A} = \mathbf{0}$.

The proofs compose, pointwise in the sample, the deterministic gap-free steps of
`NLAlib.Krylov.Eigenvalues` with the logarithmic moments of the overlap of a Gaussian vector with
a unit eigenvector (`NLAlib.Probability.Distributions.GaussianLogOverlap`): the weight of the top
eigenvalue in the spectral measure dominates the squared overlap, which is almost surely nonzero.
The Ritz value is written in projector form,
$\lambda_0(\mathbf{P}\mathbf{A}\mathbf{P})$ with $\mathbf{P}$ the orthogonal projector onto
$\mathcal{K}_{q+1}(\mathbf{A}, \mathbf{g})$, which is a measurable function of $\mathbf{g}$.

The constants are named bounds whose values are those the proof gives.

## Main definitions

* `NLAlib.randomStartPowerBound`: the power factor, <!-- value randomStartPowerBound N q -->
  $(\log(2N) + 2)/(2q + 1)$.
* `NLAlib.randomStartLanczosBound`: the Lanczos factor, <!-- value randomStartLanczosBound N q -->
  $4((\log(2N) + 2 + \log 2)^2 + 4)/((\log 2)^2 q^2)$.

## Main results

* `NLAlib.integral_eigenvalue_sub_rayleighQuotient_pow_mulVec_le_of_hasLaw_gaussianVector`: the
  power method.
* `NLAlib.integral_eigenvalue_sub_eigenvalue_rangeProjector_mul_mul_le_of_hasLaw_gaussianVector`:
  the Lanczos method.
* Their asymptotic forms, $O(\log(N)/\varepsilon)$ and $O(\log(N)/\sqrt{\varepsilon})$
  multiplications.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : Type*} [Fintype n]
  [DecidableEq n] {g : Ω → n → ℝ} {A : Matrix n n ℝ}

/-! ### The named bounds -/

/-- The random-start power-method factor <!-- value randomStartPowerBound N q -->
$(\log(2N) + 2)/(2q + 1)$, for dimension $N$ and $q$ multiplications: the mean logarithmic
overlap of a Gaussian vector with a unit vector, $\log(2N) + 2$, over the $2q + 1$ of the
deterministic step. Source:
[KuczynskiWozniakowski1992, Theorem 4.1] (locator to check), whose printed constant is to be
compared with this one; the value here is the one the proof gives and is not optimised (the exact
mean overlap is $\log(2N) + \gamma + o(1)$). -/
noncomputable irreducible_def randomStartPowerBound (N q : ℕ) : ℝ :=
  (Real.log (2 * N) + 2) / (2 * q + 1)

/-- The random-start Lanczos factor <!-- value randomStartLanczosBound N q -->
$4((\log(2N) + 2 + \log 2)^2 + 4)/((\log 2)^2 q^2)$, for dimension $N$ and $q$
multiplications: $4/q^2$ times the bound $((\log(2N) + 2 + \log 2)^2 + 4)/(\log 2)^2$ on
$\mathbb{E}(1 + L/\log 2)^2$, $L$ the logarithmic overlap of a Gaussian vector with a unit
vector. Source: [KuczynskiWozniakowski1992, Theorem 4.2] (locator to check), whose printed
constant is to be compared with this one; the value here is the one the proof gives and is not
optimised. -/
noncomputable irreducible_def randomStartLanczosBound (N q : ℕ) : ℝ :=
  4 * ((Real.log (2 * N) + 2 + Real.log 2) ^ 2 + 4) / (Real.log 2 ^ 2 * q ^ 2)

/-- The random-start power-method factor is nonnegative: <!-- value randomStartPowerBound N q -->
$0 \le (\log(2N) + 2)/(2q + 1)$. -/
theorem randomStartPowerBound_nonneg (N q : ℕ) : 0 ≤ randomStartPowerBound N q := by
  rw [randomStartPowerBound_def]
  have h : 0 ≤ Real.log (2 * N) := by
    have := Real.log_natCast_nonneg (2 * N)
    rwa [Nat.cast_mul, Nat.cast_ofNat] at this
  positivity

/-- The random-start Lanczos factor is nonnegative: <!-- value randomStartLanczosBound N q -->
$0 \le 4((\log(2N) + 2 + \log 2)^2 + 4)/((\log 2)^2 q^2)$.
-/
theorem randomStartLanczosBound_nonneg (N q : ℕ) : 0 ≤ randomStartLanczosBound N q := by
  rw [randomStartLanczosBound_def]
  positivity

/-- A coarse form of the random-start power-method factor: for $N \ge 2$ and
$q \ge 1$, <!-- value randomStartPowerBound N q -->
$(\log(2N) + 2)/(2q + 1) \le 3\log(N)/q$. -/
theorem randomStartPowerBound_le {N q : ℕ} (hN : 2 ≤ N) (hq : 1 ≤ q) :
    randomStartPowerBound N q ≤ 3 * Real.log N / q := by
  rw [randomStartPowerBound_def]
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlog : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN'
  have hl2 : 1 / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    linarith
  have hsplit : Real.log (2 * N) = Real.log 2 + Real.log N :=
    Real.log_mul (by norm_num) (by positivity)
  rw [hsplit, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ q)]

/-! ### Expected errors -/

-- A backticked declaration name in the docstring exceeds 100 characters.
set_option linter.style.longLine false in
/-- **Random-start power method**: for positive semidefinite real $\mathbf{A}$ and a standard
Gaussian start $\mathbf{g}$ (law $\mathcal{N}(\mathbf{0}, \mathbf{I})$ on $\mathbb{R}^n$), after
$q$ multiplications, <!-- value randomStartPowerBound {\lvert n \rvert} q -->
$$\mathbb{E}\bigl[\lambda_0(\mathbf{A}) - \rho_{\mathbf{A}}(\mathbf{A}^q\mathbf{g})\bigr] \le
\frac{\log(2\lvert n \rvert) + 2}{2q + 1}\,\lambda_0(\mathbf{A})\,,$$
$\rho_{\mathbf{A}}$ the Rayleigh quotient, for every $q$ (including $0$), every dimension,
repeated top eigenvalues and $\mathbf{A} = \mathbf{0}$; no gap. The factor is
`randomStartPowerBound`. Asymptotic form:
`NLAlib.exists_forall_integral_eigenvalue_sub_rayleighQuotient_pow_mulVec_le_of_hasLaw_gaussianVector`.
[MartinssonTropp2020, Theorems 6.1 and 6.2] (verified per PORT_KRYLOV §9; which of the two is the
power method is to check); [KuczynskiWozniakowski1992, Theorem 4.1] (locator to check); there as
a relative error with a different constant; constants composed here.
Result: random-start-power -/
theorem integral_eigenvalue_sub_rayleighQuotient_pow_mulVec_le_of_hasLaw_gaussianVector
    (hg : HasLaw g (gaussianVector n) μ) (hA : A.PosSemidef) (q : ℕ) :
    ∫ ω, (eigenvalue A 0 - rayleighQuotient A (A ^ q *ᵥ g ω)) ∂μ ≤
      randomStartPowerBound (Fintype.card n) q * eigenvalue A 0 := by
  sorry

-- A backticked declaration name in the docstring exceeds 100 characters.
set_option linter.style.longLine false in
/-- **Random-start Lanczos**: for positive semidefinite real $\mathbf{A}$, a standard Gaussian
start $\mathbf{g}$ (law $\mathcal{N}(\mathbf{0}, \mathbf{I})$ on $\mathbb{R}^n$) and $q \ge 1$,
the largest Ritz value $\theta_0$ of $\mathcal{K}_{q+1}(\mathbf{A}, \mathbf{g})$ ($q$
multiplications), written as $\lambda_0(\mathbf{P}\mathbf{A}\mathbf{P})$ with $\mathbf{P}$ the
orthogonal projector onto it, satisfies <!-- value randomStartLanczosBound {\lvert n \rvert} q -->
$$\mathbb{E}\bigl[\lambda_0(\mathbf{A}) - \theta_0\bigr] \le
\frac{4((\log(2\lvert n \rvert) + 2 + \log 2)^2 + 4)}{(\log 2)^2 q^2}\,\lambda_0(\mathbf{A})\,,$$
for every dimension, repeated top eigenvalues and $\mathbf{A} = \mathbf{0}$; no gap. The factor
is `randomStartLanczosBound`. Asymptotic form:
`NLAlib.exists_forall_integral_eigenvalue_sub_eigenvalue_rangeProjector_mul_mul_le_of_hasLaw_gaussianVector`.
[KuczynskiWozniakowski1992, Theorem 4.2] (locator to check); there as a relative error with a
different constant; constants composed here.
Result: random-start-lanczos -/
theorem integral_eigenvalue_sub_eigenvalue_rangeProjector_mul_mul_le_of_hasLaw_gaussianVector
    (hg : HasLaw g (gaussianVector n) μ) (hA : A.PosSemidef) {q : ℕ} (hq : 1 ≤ q) :
    ∫ ω, (eigenvalue A 0 -
        eigenvalue (rangeProjector (krylovMatrix A (g ω) (q + 1)) * A *
          rangeProjector (krylovMatrix A (g ω) (q + 1))) 0) ∂μ ≤
      randomStartLanczosBound (Fintype.card n) q * eigenvalue A 0 := by
  sorry

/-- The power-method error $\lambda_0(\mathbf{A}) - \rho_{\mathbf{A}}(\mathbf{A}^q\mathbf{g})$ of
a standard Gaussian start $\mathbf{g}$, $\rho_{\mathbf{A}}$ the Rayleigh quotient, is integrable
for every real square $\mathbf{A}$: it is measurable and bounded. -/
theorem integrable_eigenvalue_sub_rayleighQuotient_pow_mulVec_of_hasLaw_gaussianVector
    (hg : HasLaw g (gaussianVector n) μ) (A : Matrix n n ℝ) (q : ℕ) :
    Integrable (fun ω => eigenvalue A 0 - rayleighQuotient A (A ^ q *ᵥ g ω)) μ := by
  sorry

/-- The Lanczos error $\lambda_0(\mathbf{A}) - \lambda_0(\mathbf{P}\mathbf{A}\mathbf{P})$ of a
standard Gaussian start $\mathbf{g}$, $\mathbf{P}$ the orthogonal projector onto
$\mathcal{K}_{q+1}(\mathbf{A}, \mathbf{g})$, is integrable for every real square $\mathbf{A}$: it
is measurable and bounded. -/
theorem integrable_eigenvalue_sub_eigenvalue_rangeProjector_mul_mul_of_hasLaw_gaussianVector
    (hg : HasLaw g (gaussianVector n) μ) (A : Matrix n n ℝ) (q : ℕ) :
    Integrable (fun ω => eigenvalue A 0 -
      eigenvalue (rangeProjector (krylovMatrix A (g ω) (q + 1)) * A *
        rangeProjector (krylovMatrix A (g ω) (q + 1))) 0) μ := by
  sorry

/-! ### Asymptotic forms -/

/-- **$O(\log(N)/\varepsilon)$ multiplications suffice for the random-start power method**:
there is an absolute constant $C > 0$ such that for every positive semidefinite real
$\mathbf{A}$ of size $N = \lvert n\rvert$, a standard Gaussian start $\mathbf{g}$ (law
$\mathcal{N}(\mathbf{0}, \mathbf{I})$ on $\mathbb{R}^n$), $\varepsilon > 0$ and
$q \ge C\log(2N)/\varepsilon$ multiplications,
$$\mathbb{E}\bigl[\lambda_0(\mathbf{A}) - \rho_{\mathbf{A}}(\mathbf{A}^q\mathbf{g})\bigr] \le
\varepsilon\,\lambda_0(\mathbf{A})\,,$$
$\rho_{\mathbf{A}}$ the Rayleigh quotient. The asymptotic form of
`NLAlib.integral_eigenvalue_sub_rayleighQuotient_pow_mulVec_le_of_hasLaw_gaussianVector`.
[KuczynskiWozniakowski1992, Theorem 4.1] (locator to check).
Asymptotic:
NLAlib.integral_eigenvalue_sub_rayleighQuotient_pow_mulVec_le_of_hasLaw_gaussianVector
Result: random-start-power -/
theorem
exists_forall_integral_eigenvalue_sub_rayleighQuotient_pow_mulVec_le_of_hasLaw_gaussianVector :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {n : Type} [Fintype n]
      [DecidableEq n] {g : Ω → n → ℝ}, HasLaw g (gaussianVector n) μ →
      ∀ {A : Matrix n n ℝ}, A.PosSemidef → ∀ (ε : ℝ) (q : ℕ), 0 < ε →
        C * Real.log (2 * Fintype.card n) / ε ≤ q →
          ∫ ω, (eigenvalue A 0 - rayleighQuotient A (A ^ q *ᵥ g ω)) ∂μ ≤ ε * eigenvalue A 0 := by
  sorry

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **$O(\log(N)/\sqrt{\varepsilon})$ multiplications suffice for random-start Lanczos**: there
is an absolute constant $C > 0$ such that for every positive semidefinite real $\mathbf{A}$ of
size $N = \lvert n\rvert$, a standard Gaussian start $\mathbf{g}$ (law
$\mathcal{N}(\mathbf{0}, \mathbf{I})$ on $\mathbb{R}^n$), $\varepsilon > 0$ and
$q \ge C\log(2N)/\sqrt{\varepsilon}$ multiplications, the largest Ritz value $\theta_0$ of
$\mathcal{K}_{q+1}(\mathbf{A}, \mathbf{g})$, written as $\lambda_0(\mathbf{P}\mathbf{A}\mathbf{P})$
with $\mathbf{P}$ the orthogonal projector onto it, satisfies
$$\mathbb{E}\bigl[\lambda_0(\mathbf{A}) - \theta_0\bigr] \le \varepsilon\,\lambda_0(\mathbf{A})\,.$$
The asymptotic form of
`NLAlib.integral_eigenvalue_sub_eigenvalue_rangeProjector_mul_mul_le_of_hasLaw_gaussianVector`.
[KuczynskiWozniakowski1992, Theorem 4.2] (locator to check).
Asymptotic:
NLAlib.integral_eigenvalue_sub_eigenvalue_rangeProjector_mul_mul_le_of_hasLaw_gaussianVector
Result: random-start-lanczos -/
theorem
exists_forall_integral_eigenvalue_sub_eigenvalue_rangeProjector_mul_mul_le_of_hasLaw_gaussianVector :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {n : Type} [Fintype n]
      [DecidableEq n] {g : Ω → n → ℝ}, HasLaw g (gaussianVector n) μ →
      ∀ {A : Matrix n n ℝ}, A.PosSemidef → ∀ (ε : ℝ) (q : ℕ), 0 < ε →
        C * Real.log (2 * Fintype.card n) / √ε ≤ q →
          ∫ ω, (eigenvalue A 0 -
              eigenvalue (rangeProjector (krylovMatrix A (g ω) (q + 1)) * A *
                rangeProjector (krylovMatrix A (g ω) (q + 1))) 0) ∂μ ≤ ε * eigenvalue A 0 := by
  sorry

end NLAlib
