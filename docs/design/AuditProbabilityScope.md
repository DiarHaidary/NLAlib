# Probability, quadrature and dilation audit corrections

2026-11-04. This amendment corrects the scope of existing documentation, four public theorem
names, and the placement of one deterministic interface. It introduces no probability theory,
quadrature definition or hypothesis predicate.

## Statements and scope

* `variance_quadForm_le_of_hasLaw_rademacherVector` compares independent, centred real
  coordinates of variance one that belong to `L^4` and have a common fourth moment. Its
  statement and proof remain unchanged. Both the headline and the module summary must say
  this; independent mixed Gaussian/Rademacher coordinates are outside this particular API.
* Gaussian logarithmic-overlap bounds retain all their dimensions. Only the explanatory
  assertion that the inverse squared overlap has infinite expectation requires dimension at
  least two. In dimension one that quotient is one almost surely and its logarithm is zero.
* `IsMomentPosDef` remains a total integral predicate for any measure. The support-count
  interpretation is stated for finite measures carried by a bounded interval, exactly as in
  `isMomentPosDef_iff_forall_finset`. Outside integrability hypotheses, a nonintegrable Bochner
  integral is zero; the predicate is not an unconditional support criterion.
* The Radau spectral-measure identification is stated for a finite measure carried by
  `[a,b]`, `IsMomentPosDef μ (k + 1)`, and `c = a ∨ c = b`. The separate prescribed-eigenvalue
  result needs the nonvanishing denominator. These are the existing hypotheses in
  `spectralMeasure_radauJacobiMatrix` and
  `IsMomentPosDef.mem_spectrum_radauJacobiMatrix`; total definitions are not unguarded
  spectral identities.

## Names

The four nonsymmetric real variance identities retain their statements and Result metadata.
The right-side discriminator `hermitianPart` moves before the first `_of_`, with an explicit
`eq` separating it from the left side. Gaussian, Rademacher, Haar-frame and uniform-sphere law
suffixes therefore remain hypothesis tokens. The rename map records the four full names;
Girard–Hutchinson consumers use the new names.

## Deterministic interface and placement

The existing map and its application lemma move from
`Probability/MatrixConcentration/Bernstein.lean` to `Matrix/Norms/Block.lean`, beside the norm
identities for the same Hermitian dilation. Its signature is unchanged:

```lean
noncomputable def dilationCLM (m : Type*) [Fintype m] :
    Matrix m n 𝕜 →L[ℝ] Matrix (m ⊕ n) (m ⊕ n) 𝕜

@[simp] theorem dilationCLM_apply (A : Matrix m n 𝕜) :
    dilationCLM m A = dilation A
```

Here `𝕜` is `RCLike`, `n` is finite, and the matrix norm scope is `Matrix.Norms.L2Operator`.
This is real-linear, not complex-linear. Its bridge to the existing `dilation` is definitional.
Mathlib was searched for a Hermitian-dilation continuous map: none. The implementation reuses
`LinearMap.toContinuousLinearMap`, `dilation_add` and `dilation_smul_real` unchanged. No new
Mathlib deviation is introduced.

Bernstein still owns the probabilistic consequences (integrals, independence, `L^p`). Freedman
and `Probability/MatrixConditionalExpectation.lean` use the same deterministic map instead of
local reconstructions. The latter directly imports the norm module in place of the algebraic
dilation module. No upward import or additional root module is needed. No question remains
about the intended placement.
