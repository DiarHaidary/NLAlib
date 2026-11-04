# Finite inverse-power Gram potentials

The five atlas cards `inverse-power-gram-def`, `inverse-power-gram-euler`,
`inverse-power-gram-gradient-energy`, `inverse-power-gram-laplacian`, and
`gram-cutoff-vector-field` give the deterministic and integrability inputs to
the finite inverse-power method for the smallest Gaussian singular value. The
source is the original atlas at `77514ce42a0e437d837797a063ac161f41022730`,
under the source ID `operator-rederivations` (an unpublished operator proof).

## Objects and hypotheses

Use Mathlib matrices, their total inverse, `PosDef`, `PosSemidef`, `HasDerivAt`,
and `Matrix.single`. `inversePowerSoftMin n A` is the reciprocal $n$th root of
the trace of the inverse power. Its `First`, `Second`, and `Weight` operations
are the first directional coefficient, second directional coefficient, and
trace-pairing weight. `inversePowerHessianKernel` records the trace sum in the
second coefficient. `regularizedGram ε G` is the Gram matrix shifted by
`ε • 1`. `gramSoftMinGradient`, `gramSoftMinSecond`, and `gramSoftMinLaplacian`
are its gradient, second directional coefficient, and sum of coordinate second
coefficients. Bridge these coefficients to actual coordinate derivatives on the
positive definite domain. Mathlib has the trace, inverse, and derivative
interfaces but no corresponding inverse-power potential or coefficient API.

Use arbitrary finite index types. The real differential results use one real
coordinate line per matrix entry. A complex Laplacian would also sum imaginary
coordinate directions and has a different dimension factor. The scalar
coefficients are real trace formulas for the real Gaussian application.
`regularizedGram` works over `RCLike`, and the trace-product estimate uses the
existing Hermitian real-part trace API over `RCLike`. No extra hypothesis
interface is needed. A smooth positive compact cutoff uses `ContDiff ℝ ∞`,
`HasCompactSupport`, and `tsupport ψ ⊆ Set.Ioi 0`.

## Statement shapes

For finite types `ι` and `κ` with decidable equality and a nonempty row type,
let `G : Matrix ι κ ℝ`, `n : ℕ`, `hn : 0 < n`, `A := G * Gᴴ`,
`F := inversePowerSoftMin n A`, and `D := gramSoftMinGradient n 0 G`.

```lean
frobInner G D = 2 * F
frobNorm D ^ 2 ≤ 4 * F
-- With hA : A.PosDef and hdim : 0 ≤ (Fintype.card κ : ℝ) - Fintype.card ι + 1:
gramSoftMinLaplacian n 0 G ≤ 2 * ((Fintype.card κ : ℝ) - Fintype.card ι + 1)
```

The global positive-power Euler and energy statements cover singular Gram
matrices under Mathlib's total inverse convention. The positive-definite Euler
calculation, which also works at power zero, stays a private proof step. On
the positive definite domain, the exact energy and Laplacian trace identities
make the finite bound reusable.
In the Laplacian identity, set `R := A⁻¹`, `S a := (R ^ a).trace`, and
`c := S n ^ (-(n : ℝ)⁻¹ - 1)`. The expression is

```lean
2 * ((Fintype.card κ : ℝ) - Fintype.card ι + 1) * c * S (n + 1) -
  4 * ((n : ℝ) + 1) * c * (S (n + 1) - S (2 * n + 1) / S n) -
  2 * c * ∑ a ∈ Finset.range n, (S (a + 1) * S (n - a) - S (n + 1))
```

For a coordinate `i, j`, write `E := Matrix.single i j (1 : ℝ)` and
`V H := ψ (inversePowerSoftMin n (H * Hᴴ)) * gramSoftMinGradient n 0 H i j`.
The global calculus theorem proves

```lean
HasDerivAt (fun t : ℝ => V (G + t • E))
  (deriv ψ F * D i j ^ 2 + ψ F * gramSoftMinSecond n 0 G E) 0
```

The calculus statement uses differentiability of the test with closed support
in the positive half-line. The first two Gaussian conclusions use continuity
and compact support. The derivative integrability conclusion uses all the
source hypotheses.

The cutoff keeps the second coefficient bounded by
`2 + 4 * b ^ (n + 1) * ((n : ℝ) + 1) * a⁻¹ ^ (n + 2) * frobNorm G ^ 2`
on the active interval `0 < a ≤ F ≤ b`. The Gaussian results state
`Integrable V (gaussianMatrix ι κ)`, integrability of `fun G => G i j * V G`,
and integrability of the displayed derivative under the same law.

## Placement and consumers

* `Matrix/Functions/InversePowerSoftMin.lean` owns the matrix potential,
  its coefficients, and their derivative bridges. It reuses
  `Matrix.hasDerivAt_iff_forall_apply`, `Matrix.hasDerivAt_inv_apply`, and
  `Matrix.hasDerivAt_trace_pow_succ` from
  `ForMathlib/Analysis/Calculus/Deriv/Matrix.lean`, and the existing
  `Matrix.IsHermitian.re_trace_mul_diagonal_mul_mul_diagonal` identity.
  The positive trace-power and trace-product estimates are general-purpose
  additions to `Matrix/Functions/TracePowers.lean`.
* `Matrix/Perturbation/GramSoftMin.lean` owns the Gram chain rule and
  the exact and bounded unshifted Laplacian and energy. The Laplacian bridge
  identifies the coefficient sum with the actual iterated coordinate derivatives.
  The proof reuses `frobInner_eq_re_trace` and `frobNorm_sq_eq_re_trace` to
  express the first and second contractions in trace form.
* `Matrix/Perturbation/GramCutoff.lean` owns the globally differentiated field
  and the active-region estimate. The singular-branch proof uses
  `continuous_singularValues` for continuity of the smallest Gram singular
  value. On the nonsingular branch `pinv_of_isUnit` and
  `specNorm_pinv_of_injective` express the inverse norm in terms of that
  singular value, which bounds the potential above.
* `RandomMatrix/Gaussian/InverseMoments/GramCutoff.lean` owns the three
  Gaussian integrability results. It uses the existing matrix measurability
  API and `integrable_norm_sq_rpow_of_hasLaw_gaussianVector` at power one,
  via `hasLaw_uncurry_of_hasLaw_gaussianMatrix`. The coordinate product and
  the derivative both have majorants affine in the squared Frobenius norm.

The finite Laplacian and Gaussian integrability lemmas are inputs to Gaussian
integration by parts. The older asymptotic limit proofs, Wishart tail result,
and regularized growth variants are outside these cards. Preserve the actual
derivative at singular points by proving local vanishing of the cutoff field.
