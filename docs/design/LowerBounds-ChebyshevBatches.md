# Fixed-batch lower bounds with polynomial dependence on the batch count

**Status: implemented (2026-10-27).** Branch `stage/lbc-chebyshev`, based on `main` at `96d9f77`.

The fixed-batch Frobenius and nuclear lower bounds of `LowerBounds-FixedBatches.md` and
`LowerBounds-Nuclear.md` have query factor $256\cdot4^{r+1}(r+1)(r+2)$, exponential in the batch
count $r$. The $4^{r+1}$ is the squared extrapolation constant of degree-$r$ polynomials from the
equispaced levels $1,\ldots,r+1$ to the head $r+2$. Placing the tail levels at shifted Chebyshev
extrema and the head within $1/(8(r+1)^2)$ of them makes that constant four, and the bound becomes
$$q > \frac{k}{12544\,(r+1)^3\,\varepsilon} \,.$$
The construction follows the maintainer's draft "Frobenius and nuclear low-rank approximation in
few passes" (its lower-bound theorem: $q \ge k/(4096\varepsilon r^3)$ for $r \ge 1$, proved in
expectation; unpublished, so the docstrings say "No printed source.").
The formal proof keeps the library's high-probability Gaussian argument; only the hard spectrum and
the interpolation constant change.

## Structure

1. `NLAlib/Polynomial/Chebyshev/ExtremaEvaluation.lean` (new):
   * `eval_zero_sq_le_eval_T_real_sq_mul_sum_eval_chebyshevExtremum_sq`: for $0<a<a'$ and
     $\deg p\le q$, $p(0)^2 \le T_q(\tfrac{a'+a}{a'-a})^2\sum_k p(\xi_k)^2$, from the existing
     signed dual weights (`sum_neg_one_pow_mul_chebyshevWeight_mul_eval`, `sum_chebyshevWeight`)
     and Cauchy–Schwarz.
   * `eval_T_real_le_two`: $T_q(\tfrac{a'+a}{a'-a}) \le 2$ when $a' \ge 4(q+1)^2a$, from
     `inv_eval_T_real_eq_two_mul_pow_div` and $\rho^q \ge e^{-1}$.
2. `FiniteSpectrum.lean`: the level spectrum `levelSpectrum k m L ν` (head $L$, levels
   $\nu_j\in[0,\tau]$), the predicate `IsExtrapolationControl L ν C`
   ($p(L)^2\le C\sum_j p(\nu_j)^2$ for $\deg p\le r$), and every spectrum lemma stated for it:
   PSD, both optima, both missed-head-mass losses (coefficients $L^2-\tau^2$ and $L-\tau$), and
   the Krylov head-mass bound. The equispaced spectrum is the instance
   (`equispacedLevelSpectrum_eq_levelSpectrum`, `isExtrapolationControl_equispacedInterpolationFactor`).
   The Chebyshev spectrum: head $1+\delta_r$, $\delta_r = 1/(8(r+1)^2)$ (`chebyshevHeadGap`),
   levels $\nu_j = 1+\delta_r-\xi_j$ with $\xi_j$ the extrema of $[\delta_r,\delta_r+1/2]$
   (`chebyshevTailLevel`, in $[1/2,1]$), and `isExtrapolationControl_chebyshevTailLevel` with
   $C=4$ (reflect $x\mapsto1+\delta_r-x$; $(2(r+1))^2\delta_r = 1/2$).
3. `Minimax.lean`, `NuclearMinimax.lean`: the Gaussian capture, Haar and Yao theorems take
   $(L,\nu,\tau,C,\gamma)$ with $36C\le(\gamma-2)^2$ and width $\gamma^2(q+k)\le m$. The
   equispaced headline theorems keep their statements ($\gamma = 8\cdot2^{r+1}$). The Chebyshev
   headline theorems use $\gamma=14$, $m=\lfloor k/(16\varepsilon(r+1)^3)\rfloor$, and accuracy
   $\varepsilon \le 1/(25088(r+1)^3(r+2))$.

Arithmetic of the Chebyshev case: the tail optimum is at most $(r+1)m$ in both norms; the
squared Frobenius threshold is $(L^2-1)k/2 \ge k/(8(r+1)^2)$ and the nuclear one
$(L-1)\cdot2k/3 = k/(12(r+1)^2)$, both above $\varepsilon(r+1)m \le k/(16(r+1)^2)$.

## Comparison and scope

The equispaced bound has the smaller query factor for $r\le2$ (2048, 24576, 196608 against
12544, 100352, 338688); from $r=3$ on the Chebyshev bound is smaller, and the gap grows like
$4^r/r$. Both are kept, so neither is deprecated (CONTRIBUTING §5.2 rule 6). The two-pass and
one-pass theorems of `FewPasses.lean` are unchanged.

Out of scope: the optimal exponent of $r$ (the note does not claim it either); arbitrary
dimensions by zero padding; unsquared Frobenius error; an expectation-based proof.

Renames and statement changes are listed in `docs/renames/2026-10-chebyshev-batches.json`.
