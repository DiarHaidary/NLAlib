# Conditioning of a matrix and a differentiable map

The classical spectral condition number has codomain `ℝ≥0∞`. A singular
matrix has infinite condition number even when its pseudoinverse is bounded.
The definition `spectralConditionNumber` in `Matrix/Pseudoinverse/ConditionNumber.lean`
extends the existing finite `pseudoConditionNumber` on invertible square matrices.
The defining test is Mathlib's `IsUnit`, also valid for the empty matrix.
The two public rewrites needed for the atlas are

```lean
spectralConditionNumber A = ⊤ ↔ ¬ IsUnit A
spectralConditionNumber A = ENNReal.ofReal (pseudoConditionNumber A) -- if IsUnit A
```

The second rewrite transports the existing extremal singular-value formula and
attained distance to singularity without repeating their proofs.

For the conditioning of a differentiable map between Euclidean spaces,
`Matrix/Perturbation/MapConditioning.lean` uses Mathlib's Fréchet derivative,
Euclidean coordinate matrices and continuous linear maps. Scalars can be real
or complex, the dimensions need not agree, and division uses the field's total
inverse. The relative interpretation requires nonzero reference scales.
Absolute conditioning uses the derivative operator norm. Normwise relative
conditioning scales that norm by the ratio of input and output norms. The
componentwise condition uses the spectral norm of the matrix with entries
`(f x i)⁻¹ * (fderiv 𝕜 f x (EuclideanSpace.single j 1)) i * x j`.
The matrix also represents the derivative at zero when the input and output
are measured in relative coordinates.

The bounds used by perturbation analyses are

```lean
normwiseRelativeCondition 𝕜 (Matrix.toEuclideanCLM (𝕜 := 𝕜) A) x ≤ pseudoConditionNumber A
specNorm (componentwiseJacobian f x) ≤
  specNorm (Matrix.diagonal fun i => (f x i)⁻¹) * ‖fderiv 𝕜 f x‖ *
    specNorm (Matrix.diagonal fun j => x j)
```

The linear bound assumes invertibility. Scalar derivative formulas are valid
in one dimension. Matrix multiplication and Mathlib's chain rule handle the
two diagonal maps, and the library's spectral norm API handles all norm bounds.
The definitions and distinctions follow Gautschi (2004), Definitions 2.3–2.6, and the
two condition-number cards in the original atlas.
