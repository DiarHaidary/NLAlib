# Polynomial Lipschitz estimates for finite-precision Lanczos

Design, 2026-11-04. Supporting material for the requested computed matrix-function vector bound.
No new mathematical object or hypothesis interface is introduced. Polynomial bounds use ordinary
real polynomials and `LipschitzOnWith`; matrix functions use Mathlib `cfc`.

## Statements and consumers

In `Polynomial/Approximation/Markov.lean`, prove an endpoint derivative bound from Mathlib's
`Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one`, then a coarse interval
bound `abs (p.derivative.eval x) ≤ 4*n^2*M/(b-a)` and the corresponding Lipschitz estimate,
for `p.degree ≤ n`, `a<b`, and `abs(p.eval x)≤M` on `[a,b]`. This polynomial dependence supplies
the precision-dependent remainder in `Krylov/FinitePrecision/LanczosFunctions.lean` without
assuming that the target function is Lipschitz. The scalar result belongs in Polynomial and
imports no Matrix or Krylov module. The bound is a factor two weaker than classical Markov;
the endpoint extremal theorem is reused, not reproved. Searches found no full-interval Markov
inequality in pinned Mathlib or NLAlib.

In `Matrix/Functions/HermitianCalculus.lean`, generalize the existing Frobenius Lipschitz
functional-calculus theorem to an arbitrary NNReal Lipschitz constant on a common set containing
both spectra:

```lean
theorem Matrix.IsHermitian.frobNorm_cfc_sub_cfc_le_of_lipschitzOnWith
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAs : spectrum ℝ A ⊆ s) (hBs : spectrum ℝ B ⊆ s)
    (hf : LipschitzOnWith ℓ f s) :
    frobNorm (cfc f A - cfc f B) ≤ (ℓ : ℝ) * frobNorm (A - B)
```

The old globally 1-Lipschitz theorem becomes a one-line specialization. This reuses its
unitary-eigenbasis proof and exposes the more general statement needed for polynomial
perturbation, with no twin proof. Both fields and arbitrary finite matrix index types remain
supported. The consumer is the physical-vector perturbation term after orthonormal dilation.

Parent and matrix-function agent reviewed the interfaces before implementation. No target,
check, pin, allowlist or probabilistic model is changed.

The relaxed derivative coefficient is the registered irreducible bound
`polynomialDerivativeFactor n`, currently `4*n^2`, with nonnegativity, monotonicity and an
explicit upper-comparison theorem. Consumers use that API so a later improvement does not
require changing their statements. The scalar estimates carry no claim of a new classical
inequality: they reuse Mathlib's endpoint result and relax the classical interval constant.
