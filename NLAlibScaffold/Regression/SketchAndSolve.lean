/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Regression.SketchAndSolve
public import NLAlibScaffold.RandomMatrix.Haar.Blocks

/-!
# No sketch beats a random orthonormal one for sketch-and-solve (stage S10)

Epperly and Webber's Theorem 2.2: for every sketch with full column rank, some rotation of
any least-squares problem with $\operatorname{rank}\mathbf{A} = r$ has expected sketch-and-solve
residual at least the random orthonormal factor <!-- value haarProjectionFactor m \ell r -->
$1 + (m - \ell)/(m - r) \cdot (r/(\ell - r - 1))$ times the optimum, the exact value for a Haar
sketch (`NLAlib.integral_frobNorm_sub_mul_sketchAndSolve_sq_of_hasLaw_haarFrame`). Three forms:
averaged over a Haar rotation for a fixed sketch, a single rotation for a fixed sketch, and a
single rotation for a random sketch of any law (in `lintegral`, since the expectation may be
infinite). They join `NLAlib/Regression/SketchAndSolve.lean`; proofs deferred. Design:
`docs/design/LowRank-EstimatorLowerBounds.md` §3.3.

## Main results

* `NLAlib.le_integral_frobNorm_mul_sub_mul_sketchAndSolve_sq_of_hasLaw_haarFrame`
* `NLAlib.exists_hasOrthonormalCols_le_frobNorm_mul_sub_mul_sketchAndSolve_sq`
* `NLAlib.exists_hasOrthonormalCols_le_lintegral_frobNorm_mul_sub_mul_sketchAndSolve_sq`
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n l r : Type*} [Fintype m]
  [Fintype n] [Fintype l] [Fintype r] [DecidableEq m]

/-- **A Haar rotation of the problem defeats every fixed sketch**: for a fixed sketch
$\mathbf{\Omega}_0 \in \mathbb{R}^{m \times \ell}$ of full column rank, $\mathbf{A} \in
\mathbb{R}^{m \times n}$
with $r = \operatorname{rank}\mathbf{A}$, $r + 2 \le \ell$, any $\mathbf{B} \in \mathbb{R}^{m \times
r'}$ and
an $m \times m$ Haar orthogonal $\mathbf{U}$, <!-- value haarProjectionFactor m \ell r -->
$$\Bigl(1 + \frac{m - \ell}{m - r}\cdot\frac{r}{\ell - r - 1}\Bigr)
\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{B}\|_{\mathsf{F}}^2 \le
\mathbb{E}\|\mathbf{U}\mathbf{B} -
\mathbf{U}\mathbf{A}\,\mathsf{sketchAndSolve}(\mathbf{U}\mathbf{A},
\mathbf{\Omega}_0^{\mathsf{H}}, \mathbf{U}\mathbf{B})\|_{\mathsf{F}}^2\,,$$
the factor being `haarProjectionFactor m ℓ r` and the left side's minimum the optimum of every
rotated problem.
[EpperlyWebber2026, Theorem 2.2 (§5.5)]; there as a supremum over problems for a random sketch,
here averaged over the rotation for a fixed one (the core of their proof).
Proof: L, about 100 lines. Polar/QR factor $\mathbf{\Omega}_0 = \mathbf{W}\mathbf{R}$ with
$\mathbf{W}$ orthonormal, $\mathbf{R}$ invertible (`polarFactor`, full column rank). The estimator
on
$(\mathbf{U}\mathbf{A}, \mathbf{U}\mathbf{B})$ with sketch $\mathbf{\Omega}_0^{\mathsf{H}}$ is the
estimator on $(\mathbf{A}, \mathbf{B})$ with sketch
$(\mathbf{U}^{\mathsf{H}}\mathbf{\Omega}_0)^{\mathsf{H}}$,
and $\mathbf{U}^{\mathsf{H}}\mathbf{W}$ is an $m \times \ell$ Haar frame
(`isRightUnitarilyInvariant_haarFrame`, `haarFrame_eq_map_haarMeasure`). Split
$\mathbf{B}$ along $\operatorname{range}\mathbf{A}$ with an orthonormal basis $\mathbf{V}_1$ and its
complement $\mathbf{V}_2$ (`exists_hasOrthonormalCols_range_eq`): the residual is
$\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{B}\|_{\mathsf{F}}^2$ plus the weighted block term
(EW Lemma 5.1, the rank-$r$ decomposition used in
`integral_frobNorm_sub_mul_sketchAndSolve_sq_of_hasLaw_haarFrame`), whose mean is bounded below by
`mul_le_integral_frobNorm_pinv_conjTranspose_mul_mul_sq_of_hasLaw_haarFrame` with weight
$\mathbf{R}$. -/
theorem le_integral_frobNorm_mul_sub_mul_sketchAndSolve_sq_of_hasLaw_haarFrame {r' : Type*}
    [Fintype r'] {U : Ω → Matrix m m ℝ} (hU : HasLaw U (haarFrame m m) μ) {Ω₀ : Matrix m l ℝ}
    (hΩ₀ : Ω₀.rank = Fintype.card l) {A : Matrix m n ℝ} (hA : A.rank + 2 ≤ Fintype.card l)
    (B : Matrix m r' ℝ) :
    haarProjectionFactor (Fintype.card m) (Fintype.card l) A.rank *
        frobNorm ((1 - rangeProjector A) * B) ^ 2 ≤
      ∫ ω, frobNorm (U ω * B - U ω * A * sketchAndSolve (U ω * A) Ω₀ᴴ (U ω * B)) ^ 2 ∂μ := by
  sorry

/-- **Some rotation of the problem defeats a fixed sketch**: for a fixed sketch
$\mathbf{\Omega}_0 \in \mathbb{R}^{m \times \ell}$ of full column rank, $\mathbf{A} \in
\mathbb{R}^{m \times n}$
with $r = \operatorname{rank}\mathbf{A}$, $r + 2 \le \ell$ and any $\mathbf{B}$, there is an
orthogonal
$\mathbf{U}$ with <!-- value haarProjectionFactor m \ell r -->
$$\Bigl(1 + \frac{m - \ell}{m - r}\cdot\frac{r}{\ell - r - 1}\Bigr)
\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{B}\|_{\mathsf{F}}^2 \le
\|\mathbf{U}\mathbf{B} - \mathbf{U}\mathbf{A}\,\mathsf{sketchAndSolve}(\mathbf{U}\mathbf{A},
\mathbf{\Omega}_0^{\mathsf{H}}, \mathbf{U}\mathbf{B})\|_{\mathsf{F}}^2\,.$$
[EpperlyWebber2026, Theorem 2.2]; there for a random sketch.
Proof: S, about 20 lines. Apply
`le_integral_frobNorm_mul_sub_mul_sketchAndSolve_sq_of_hasLaw_haarFrame` on the probability space
`haarFrame m m` with `U = id`; an integrable function exceeds its mean somewhere on a set of
positive measure (`MeasureTheory.exists_not_mem_null_le_integral`, or by contradiction with
`integral_mono_ae`), and almost every sample is orthogonal
(`ae_hasOrthonormalCols_of_hasLaw_haarFrame`). -/
theorem exists_hasOrthonormalCols_le_frobNorm_mul_sub_mul_sketchAndSolve_sq {r' : Type*}
    [Fintype r'] {Ω₀ : Matrix m l ℝ} (hΩ₀ : Ω₀.rank = Fintype.card l) {A : Matrix m n ℝ}
    (hA : A.rank + 2 ≤ Fintype.card l) (B : Matrix m r' ℝ) :
    ∃ U : Matrix m m ℝ, HasOrthonormalCols U ∧
      haarProjectionFactor (Fintype.card m) (Fintype.card l) A.rank *
          frobNorm ((1 - rangeProjector A) * B) ^ 2 ≤
        frobNorm (U * B - U * A * sketchAndSolve (U * A) Ω₀ᴴ (U * B)) ^ 2 := by
  sorry

/-- **No random sketch beats a random orthonormal one** (Epperly and Webber's minimax lower bound
for sketch-and-solve): for a random sketch $\mathbf{\Omega} \in \mathbb{R}^{m \times \ell}$ of any
law with full column rank almost surely, $\mathbf{A} \in \mathbb{R}^{m \times n}$ with
$r = \operatorname{rank}\mathbf{A}$, $r + 2 \le \ell$ and any $\mathbf{B}$, there is an orthogonal
$\mathbf{U}$ with <!-- value haarProjectionFactor m \ell r -->
$$\Bigl(1 + \frac{m - \ell}{m - r}\cdot\frac{r}{\ell - r - 1}\Bigr)
\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{B}\|_{\mathsf{F}}^2 \le
\mathbb{E}\|\mathbf{U}\mathbf{B} -
\mathbf{U}\mathbf{A}\,\mathsf{sketchAndSolve}(\mathbf{U}\mathbf{A},
\mathbf{\Omega}^{\mathsf{H}}, \mathbf{U}\mathbf{B})\|_{\mathsf{F}}^2\,,$$
in extended reals (the expectation may be infinite). With
`NLAlib.integral_frobNorm_sub_mul_sketchAndSolve_sq_of_hasLaw_haarFrame` (equality for a Haar
sketch): the random orthonormal sketch is minimax optimal.
[EpperlyWebber2026, Theorem 2.2]; there as a supremum over problems of rank $r$.
Proof: M, about 50 lines. Tonelli on $\mu \otimes$ `haarFrame m m` (`lintegral_lintegral_swap`,
measurability of the integrand from `measurable_pinv`-type lemmas): for almost every $\omega$
the inner Haar average is at least the factor
(`le_integral_frobNorm_mul_sub_mul_sketchAndSolve_sq_of_hasLaw_haarFrame` with
`ofReal_integral_eq_lintegral_ofReal`), so the double integral is; then some $\mathbf{U}$ in the
support has $\int^-$ at least the factor (`exists_le_lintegral`-type argument on the Haar
probability space, by contradiction if every $\mathbf{U}$ is below; the value $\infty$ is
harmless), and a.e. $\mathbf{U}$ is orthogonal.
Result: sketch-and-solve-lower-bound -/
theorem exists_hasOrthonormalCols_le_lintegral_frobNorm_mul_sub_mul_sketchAndSolve_sq
    {r' : Type*} [Fintype r'] [IsProbabilityMeasure μ] {X : Ω → Matrix m l ℝ}
    (hX : AEMeasurable X μ) (hXr : ∀ᵐ ω ∂μ, (X ω).rank = Fintype.card l) {A : Matrix m n ℝ}
    (hA : A.rank + 2 ≤ Fintype.card l) (B : Matrix m r' ℝ) :
    ∃ U : Matrix m m ℝ, HasOrthonormalCols U ∧
      ENNReal.ofReal (haarProjectionFactor (Fintype.card m) (Fintype.card l) A.rank *
          frobNorm ((1 - rangeProjector A) * B) ^ 2) ≤
        ∫⁻ ω, ENNReal.ofReal
          (frobNorm (U * B - U * A * sketchAndSolve (U * A) (X ω)ᴴ (U * B)) ^ 2) ∂μ := by
  sorry

end NLAlib
