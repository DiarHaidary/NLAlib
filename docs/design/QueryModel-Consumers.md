# Existing algorithms in the query model

This addition connects existing numerical linear algebra objects with `QueryAlgorithm`.
The interfaces are `QueryAlgorithm.IsMeasurableFamily`, `IsNonAdaptive`, and
`IsPassStructured`; no alternative oracle or algorithm interface is introduced.

The seed of power iteration is its start vector. Each response is the next query, so the
query matrix is exactly `krylovMatrix`, and its range is `krylovSpace`. Returning the last
response computes the power vector in q rounds. The Rayleigh estimator takes q+1 rounds:
the extra product is essential to evaluate the quadratic form. Its mathematical guarantee
is obtained from the existing gapped power theorem by exact execution equality. A separate
certificate shows that at least two power rounds are genuinely response-dependent.
