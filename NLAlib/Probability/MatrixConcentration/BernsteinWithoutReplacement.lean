/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.MatrixConcentration.Bernstein
public import NLAlib.Probability.MatrixConcentration.ChernoffWithoutReplacement

/-!
# Matrix Bernstein for sampling without replacement

For a centred population of Hermitian matrices, $\sum_i \mathbf{X}_i = \mathbf{0}$ with
$\mathbf{X}_i \preceq L\mathbf{I}$, $i \in n$, and a uniformly random injection $\iota : k \to n$
(sampling $\lvert k \rvert$ members without replacement), the sum
$\mathbf{Y} = \sum_j \mathbf{X}_{\iota(j)}$ satisfies the matrix Bernstein trace bound of the
i.i.d. sum with the same variance $(\lvert k\rvert/\lvert n\rvert)\sum_i \mathbf{X}_i^2$:
Hoeffding's comparison (`NLAlib.integral_uniformOn_injective_le_integral_pi`) with
$f = \operatorname{re}\operatorname{tr} e^{\theta\,\cdot}$, convex on the Hermitian matrices
(`NLAlib.convexOn_re_trace_exp`), and the i.i.d. bound
(`NLAlib.HasMatrixMGFBound.integral_re_trace_exp_sum_le` with
`NLAlib.hasMatrixMGFBound_of_integral_eq_zero_of_le`). The trace-form tails of
`NLAlib.Probability.MatrixConcentration.Bernstein` then give the tail and the mean of
$\lambda_0(\mathbf{Y})$; rectangular populations go through the Hermitian dilation, with
dimension $\lvert q\rvert + \lvert r\rvert$, and the $1 \times 1$ case is Bernstein's inequality
without replacement, Hoeffding's setting [Hoeffding1963].

The population is centred (`docs/design/Sketching-Moments.md` §8 Q7): a consumer with a population
of mean $\bar{\mathbf{X}}$ centres its atoms in one line. Lower tails follow by
$\mathbf{X} \mapsto -\mathbf{X}$; the rectangular form covers two-sided Hermitian use.

Degenerate cases. For $\lvert n \rvert < \lvert k \rvert$ there is no injection, the law of $\iota$
is the zero measure, `HasLaw` forces $\mu = 0$, and every statement holds; so no
$\lvert k \rvert \le \lvert n \rvert$ is assumed. Design: `docs/design/Sketching-Moments.md` §5.

## Main results

* `NLAlib.integral_re_trace_exp_sum_le_bernstein_of_hasLaw_uniformOn_injective`: the trace bound.
* `NLAlib.measureReal_eigenvalue_zero_sum_ge_le_bernstein_of_hasLaw_uniformOn_injective`,
  `NLAlib.integral_eigenvalue_zero_sum_le_bernstein_of_hasLaw_uniformOn_injective`: Hermitian
  populations.
* `NLAlib.measureReal_specNorm_sum_ge_le_bernstein_of_hasLaw_uniformOn_injective`,
  `NLAlib.integral_specNorm_sum_le_bernstein_of_hasLaw_uniformOn_injective`: rectangular
  populations.
* `NLAlib.measureReal_sum_ge_le_bernstein_of_hasLaw_uniformOn_injective`: the scalar case.

## References

* [J. A. Tropp, *An Introduction to Matrix Concentration Inequalities*][Tropp2015], chapter 6.
* [D. Gross and V. Nesme, *Note on sampling without replacing from a finite collection of
  matrices*][GrossNesme2010].
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open NormedSpace (exp)

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {k m n : Type*} [Fintype k] [Fintype m] [Fintype n] [DecidableEq m] [MeasurableSpace n]
  [MeasurableSingletonClass n] {ι : Ω → k → n} {L : ℝ}

section Hermitian

variable {X : n → Matrix m m 𝕜}

/-- **The matrix Bernstein trace bound without replacement**: for Hermitian $\mathbf{X}_i$ with
$\sum_i \mathbf{X}_i = \mathbf{0}$ and $\mathbf{X}_i \preceq L\mathbf{I}$, $L > 0$, a uniformly
random injection $\iota : k \to n$ and $0 < \theta < 3/L$,
$$\mathbb{E}\operatorname{tr}\exp\Bigl(\theta\sum_j\mathbf{X}_{\iota(j)}\Bigr) \le
\operatorname{tr}\exp\Bigl(\frac{\theta^2/2}{1 - L\theta/3}\cdot
\frac{\lvert k\rvert}{\lvert n\rvert}\sum_i\mathbf{X}_i^2\Bigr)\,,$$
the bound of the i.i.d. sum with the same variance; the hypothesis of the trace-form tails
`NLAlib.measureReal_eigenvalue_zero_ge_le_bernstein_of_integral_le` and
`NLAlib.integral_eigenvalue_zero_le_bernstein_of_integral_le`. Hoeffding's comparison on the
Hermitian matrices and [Tropp2015, Lemma 6.6.2]; [GrossNesme2010, Section D]; [Tropp2011a, proof
of Theorem 2.1] (the same comparison for the Chernoff bound,
`NLAlib.integral_re_trace_exp_sum_le_of_hasLaw_uniformOn_injective`). -/
theorem integral_re_trace_exp_sum_le_bernstein_of_hasLaw_uniformOn_injective
    (hι : HasLaw ι (uniformOn {f : k → n | Function.Injective f}) μ) (hL : 0 < L)
    (hX : ∀ i, (X i).IsHermitian) (hsum : ∑ i, X i = 0)
    (hle : ∀ i, X i ≤ L • (1 : Matrix m m 𝕜)) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (3 / L)) :
    ∫ ω, RCLike.re (exp (θ • ∑ j, X (ι ω j))).trace ∂μ ≤
      RCLike.re (exp ((θ ^ 2 / 2 / (1 - L * θ / 3)) •
        (((Fintype.card k : ℝ) / Fintype.card n) • ∑ i, X i ^ 2))).trace := by
  sorry

/-- **Matrix Bernstein without replacement**, Hermitian population: for Hermitian
$\mathbf{X}_i$, $i \in n$, with $\sum_i \mathbf{X}_i = \mathbf{0}$ and
$\mathbf{X}_i \preceq L\mathbf{I}$, $L > 0$, $m$ nonempty, a uniformly random injection
$\iota : k \to n$ and $t \ge 0$,
$$\mathbb{P}\Bigl[\lambda_0\Bigl(\sum_j \mathbf{X}_{\iota(j)}\Bigr) \ge t\Bigr]
\le \lvert m\rvert \exp\Bigl(\frac{-t^2/2}{v + Lt/3}\Bigr), \qquad
v = \frac{\lvert k\rvert}{\lvert n\rvert}\Bigl\|\sum_i \mathbf{X}_i^2\Bigr\|_2\,.$$
The trace bound `NLAlib.integral_re_trace_exp_sum_le_bernstein_of_hasLaw_uniformOn_injective`
in `NLAlib.measureReal_eigenvalue_zero_ge_le_bernstein_of_integral_le`. [Tropp2015,
Theorem 6.6.1] (the i.i.d. form, the same bound); [GrossNesme2010, Section D] for the
comparison.
Result: matrix-bernstein-without-replacement -/
theorem measureReal_eigenvalue_zero_sum_ge_le_bernstein_of_hasLaw_uniformOn_injective
    [Nonempty m] (hι : HasLaw ι (uniformOn {f : k → n | Function.Injective f}) μ) (hL : 0 < L)
    (hX : ∀ i, (X i).IsHermitian) (hsum : ∑ i, X i = 0)
    (hle : ∀ i, X i ≤ L • (1 : Matrix m m 𝕜)) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ eigenvalue (∑ j, X (ι ω j)) 0} ≤
      Fintype.card m * Real.exp (-(t ^ 2 / 2) /
        ((Fintype.card k : ℝ) / Fintype.card n * specNorm (∑ i, X i ^ 2) + L * t / 3)) := by
  sorry

/-- **Matrix Bernstein without replacement for the mean**, Hermitian population: for Hermitian
$\mathbf{X}_i$, $i \in n$, with $\sum_i \mathbf{X}_i = \mathbf{0}$ and
$\mathbf{X}_i \preceq L\mathbf{I}$, $L > 0$, $m$ nonempty and a uniformly random injection
$\iota : k \to n$,
$$\mathbb{E}\,\lambda_0\Bigl(\sum_j \mathbf{X}_{\iota(j)}\Bigr) \le \sqrt{2v\log\lvert m\rvert}
+ \frac{L\log\lvert m\rvert}{3}, \qquad
v = \frac{\lvert k\rvert}{\lvert n\rvert}\Bigl\|\sum_i \mathbf{X}_i^2\Bigr\|_2\,.$$
The mean form of
`NLAlib.measureReal_eigenvalue_zero_sum_ge_le_bernstein_of_hasLaw_uniformOn_injective`.
[Tropp2015, Theorem 6.6.1] (the i.i.d. form). -/
theorem integral_eigenvalue_zero_sum_le_bernstein_of_hasLaw_uniformOn_injective [Nonempty m]
    (hι : HasLaw ι (uniformOn {f : k → n | Function.Injective f}) μ) (hL : 0 < L)
    (hX : ∀ i, (X i).IsHermitian) (hsum : ∑ i, X i = 0)
    (hle : ∀ i, X i ≤ L • (1 : Matrix m m 𝕜)) :
    ∫ ω, eigenvalue (∑ j, X (ι ω j)) 0 ∂μ ≤
      √(2 * ((Fintype.card k : ℝ) / Fintype.card n * specNorm (∑ i, X i ^ 2)) *
        Real.log (Fintype.card m)) + L * Real.log (Fintype.card m) / 3 := by
  sorry

end Hermitian

section Rectangular

variable {q r : Type*} [Fintype q] [Fintype r] {S : n → Matrix q r 𝕜}

/-- **Matrix Bernstein without replacement**, rectangular population: for
$\mathbf{S}_i \in \Bbbk^{q \times r}$, $i \in n$, with $\sum_i \mathbf{S}_i = \mathbf{0}$ and
$\|\mathbf{S}_i\|_2 \le L$, $L > 0$, $r$ nonempty, a uniformly random injection $\iota : k \to n$
and $t \ge 0$,
$$\mathbb{P}\Bigl[\Bigl\|\sum_j \mathbf{S}_{\iota(j)}\Bigr\|_2 \ge t\Bigr]
\le (\lvert q\rvert + \lvert r\rvert)\exp\Bigl(\frac{-t^2/2}{v + Lt/3}\Bigr)$$
with variance
$v = (\lvert k\rvert/\lvert n\rvert)\max(\|\sum_i\mathbf{S}_i\mathbf{S}_i^{\mathsf{H}}\|_2,
\|\sum_i\mathbf{S}_i^{\mathsf{H}}\mathbf{S}_i\|_2)$: the Hermitian form on the dilations.
[Tropp2015, Theorem 6.1.1] (the i.i.d. form).
Result: matrix-bernstein-without-replacement -/
theorem measureReal_specNorm_sum_ge_le_bernstein_of_hasLaw_uniformOn_injective [Nonempty r]
    (hι : HasLaw ι (uniformOn {f : k → n | Function.Injective f}) μ) (hL : 0 < L)
    (hsum : ∑ i, S i = 0) (hle : ∀ i, specNorm (S i) ≤ L) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ specNorm (∑ j, S (ι ω j))} ≤
      (Fintype.card q + Fintype.card r) * Real.exp (-(t ^ 2 / 2) /
        ((Fintype.card k : ℝ) / Fintype.card n *
          max (specNorm (∑ i, S i * (S i)ᴴ)) (specNorm (∑ i, (S i)ᴴ * S i)) + L * t / 3)) := by
  sorry

/-- **Matrix Bernstein without replacement for the mean**, rectangular population: for
$\mathbf{S}_i \in \Bbbk^{q \times r}$, $i \in n$, with $\sum_i \mathbf{S}_i = \mathbf{0}$ and
$\|\mathbf{S}_i\|_2 \le L$, $L > 0$, $r$ nonempty and a uniformly random injection
$\iota : k \to n$,
$$\mathbb{E}\Bigl\|\sum_j \mathbf{S}_{\iota(j)}\Bigr\|_2 \le \sqrt{2v\log d} + \frac{L\log d}{3}$$
with variance
$v = (\lvert k\rvert/\lvert n\rvert)\max(\|\sum_i\mathbf{S}_i\mathbf{S}_i^{\mathsf{H}}\|_2,
\|\sum_i\mathbf{S}_i^{\mathsf{H}}\mathbf{S}_i\|_2)$ and $d = \lvert q\rvert + \lvert r\rvert$.
The mean form of
`NLAlib.measureReal_specNorm_sum_ge_le_bernstein_of_hasLaw_uniformOn_injective`.
[Tropp2015, Theorem 6.1.1] (the i.i.d. form). -/
theorem integral_specNorm_sum_le_bernstein_of_hasLaw_uniformOn_injective [Nonempty r]
    (hι : HasLaw ι (uniformOn {f : k → n | Function.Injective f}) μ) (hL : 0 < L)
    (hsum : ∑ i, S i = 0) (hle : ∀ i, specNorm (S i) ≤ L) :
    ∫ ω, specNorm (∑ j, S (ι ω j)) ∂μ ≤
      √(2 * ((Fintype.card k : ℝ) / Fintype.card n *
          max (specNorm (∑ i, S i * (S i)ᴴ)) (specNorm (∑ i, (S i)ᴴ * S i))) *
        Real.log (Fintype.card q + Fintype.card r)) +
      L * Real.log (Fintype.card q + Fintype.card r) / 3 := by
  sorry

end Rectangular

/-- **Bernstein's inequality without replacement**, the $1 \times 1$ case: for a centred
population $a : n \to \mathbb{R}$, $\sum_i a_i = 0$, with $a_i \le L$, $L > 0$, a uniformly random
injection $\iota : k \to n$ and $t \ge 0$,
$$\mathbb{P}\Bigl[\sum_j a_{\iota(j)} \ge t\Bigr] \le
\exp\Bigl(\frac{-t^2/2}{(\lvert k\rvert/\lvert n\rvert)\sum_i a_i^2 + Lt/3}\Bigr)\,,$$
the bound of the i.i.d. sum with the same variance. [Hoeffding1963, Theorem 4] for the comparison
of sampling with and without replacement; the $1 \times 1$ case of
`NLAlib.measureReal_eigenvalue_zero_sum_ge_le_bernstein_of_hasLaw_uniformOn_injective`. -/
theorem measureReal_sum_ge_le_bernstein_of_hasLaw_uniformOn_injective {a : n → ℝ}
    (hι : HasLaw ι (uniformOn {f : k → n | Function.Injective f}) μ) (hL : 0 < L)
    (hsum : ∑ i, a i = 0) (hle : ∀ i, a i ≤ L) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ∑ j, a (ι ω j)} ≤
      Real.exp (-(t ^ 2 / 2) /
        ((Fintype.card k : ℝ) / Fintype.card n * ∑ i, a i ^ 2 + L * t / 3)) := by
  sorry

end NLAlib
