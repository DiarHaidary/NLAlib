# Iterations for the rectangular polar factor

The target on arbitrary finite real or complex matrices is the existing `polarFactor A`;
a full-rank input gives its polar isometry. The proofs use the current `IsSVD A U σ V`
relation, `pinv`, `HasOrthonormalCols`, `specNorm`, and Mathlib polynomial evaluation.
Newton averaging fixes the singular directions. For a positive singular value s write
c=(s−1)/(s+1). Its kth coefficient is (1+c^(2^k))/(1−c^(2^k)).
The inverse-free cubic iteration admits the broader initial domain ‖A‖₂<√3. Its
defect bounds begin at the first step, when every retained coefficient lies in (0,1].
An arbitrary odd polynomial acts on these directions as s p(s²). Composition of
greedy odd minimax updates gives the worst-case scalar bound and a Horner realization.

~~~lean
Tendsto (polarNewtonIterate A) atTop (𝓝 (polarFactor A))
specNorm A < Real.sqrt 3 → Tendsto (polarSchulzIterate A) atTop (𝓝 (polarFactor A))
~~~

The matrix statements belong to the matrix-functions layer, and scalar approximation
arguments belong with the library's polynomial approximation results. The sources are
Higham (1986), §3, Higham and Schreiber (1990), §3, and the polar-iteration files in the
[original atlas](https://github.com/tchen-research/NLAlib/tree/77514ce42a0e437d837797a063ac161f41022730/NLAlib/Matrix/Functions).

## Horner evaluation and the operation target

The mathematical implementation `gramHorner` handles degree zero and one directly.
Each further degree appends exactly one left multiplication by the Gram matrix.
`oddMatrixIterate` forms that Gram matrix once and applies the resulting polynomial once
per update. Thus evaluating the displayed recursion uses at most $(q+1)k$ matrix products
for $q≥1$ in $k$ stages, counting a Gram product as one full matrix product.
