# Finite-precision Lanczos: constants and iteration dependence

Implementation, 2026-11-02. Base: `0f7521ba`. Requested work: improve the constants and dependence on the
iteration count in the existing finite-precision Lanczos backward model. This note records the
reviewed derivation and its Lean implementation. The final cubic and conditional quadratic bounds compile with warnings fatal. The final
full audit passed on 2026-11-02.

Independent read-only mathematical review, 2026-11-02: **ACCEPT**. The reviewer checked the
exchange convolution (signs and indices), zero-padded shift range, contraction argument,
Frobenius commutator estimate, all scalar constants, and terminal breakdown. No additional
hypothesis is needed for the cubic improvement. The conditional quadratic result has its own
explicit smallness hypothesis, reviewed separately below.

## Retaining the absorption factor (2026-11-02 amendment)

Design reviewed separately from the earlier validated implementation above. The existing proof
already gives $D\le q(N+D)$ with $D$ the model distance, $N=\|\mathbf H\|_2$, and
$q=500k^2\varepsilon$. The condition $q\le1/2$ only simplifies the reciprocal. Retain it:
$D\le qN/(1-q)$ for $q<1$. This requires no positive definiteness of $\mathbf H$; it is a
bound for symmetric Lanczos, including indefinite inputs and terminal breakdown. It still
inherited the run's $k\varepsilon\le1/100$ assumption at that stage. The later amendment
`Krylov-FinitePrecision-Runs.md` removes this run field and gives a geometric bound for all
horizons. The cubic bound remains available with an explicit $k\varepsilon\le1/100$ premise.

Use the existing factor $1000k^2$, without new definitions or interfaces. Add in
`BackwardBounds.lean`, before its quadratic corollary:

```lean
theorem LanczosRun.frobNorm_backwardH_sub_dilatedH_le_of_sq_mul_lt
    (hsmall : (k : ℝ) ^ 2 * L.ε < 1 / 500) :
    frobNorm (L.backwardH - L.dilatedH) ≤
      (lanczosSmallRoundoffBackwardFactor k * L.ε /
        (2 - lanczosSmallRoundoffBackwardFactor k * L.ε)) * specNorm L.H
```

Reprove `frobNorm_backwardH_sub_dilatedH_le_of_sq_mul_le` from this general estimate. Downstream
consumers are spectral localization for Lanczos and a posteriori CG: the shared normalized
recurrence/dilation layer already retains the defects without a precision assumption. Mathlib
scalar order/division lemmas suffice for absorption; no new scalar lemma is needed. This
amendment changes neither the model construction nor the coefficient-error bounds.

Validation of this amendment: independent mathematical review accepted the statement and proof.
Warning-fatal targeted builds passed. The full stage audit completed with exit 0 on 2026-11-02
(`/tmp/krylov-parameter-stage.log`), including zero build
warnings, successful kernel replay, and reference/constant/LaTeX checks. No checks, build pins,
target registries, or baselines were changed. The changes remain uncommitted.

### Audit of the shared assumptions

The normalized recurrence/dilation layer is already parameterized correctly:
`NormalizedLanczosData` contains no precision parameter or horizon restriction, and its bound
$22k^2f+17k\sqrt{k}p$ accepts arbitrary certified defects. It requires unit vectors, symmetry,
and nonnegative coefficients with no breakdown before the terminal step. Neither this model
nor its spectral localization requires positive definiteness.

At the time of this audit, both arithmetic-run structures, `LanczosRun` and `CGRun`, contained
$k\varepsilon\le1/100$. That restriction is stronger than local normalization needs.
For $0\le\varepsilon<1$, the near-unit condition implies norm bounds
$\ell=\sqrt{1-\varepsilon}$ and $u=\sqrt{1+\varepsilon}$, with $\ell>0$.
Normalization can retain $1/\ell$ and $u/\ell-1$ instead of fixed constants. More generally,
certified vector-norm bounds $0<\ell\le\|v_j\|\le u$ suffice. The unused terminal vector
when $\beta_k=0$ must keep the existing replacement convention.

In `LocalErrors.lean`, the horizon restriction enters the linear coefficient estimate.
Before simplification its proof gives
$$\beta_{j+1}\le(1+8\varepsilon)
  [\beta_j+(1+\varepsilon)\|\mathbf H\|_2].$$
Retaining this recurrence gives the geometric sum
$$\beta_j\le(1+\varepsilon)\|\mathbf H\|_2
  \sum_{r=1}^{j}(1+8\varepsilon)^r.$$
The local estimates supporting this recurrence use $\varepsilon\le1/100$; it is the
replacement of geometric accumulation by linear growth that uses the horizon. Likewise,
`CGRunModel.lean` linearizes transported orthogonality defects using its horizon assumption.

A further algebraic derivation, not yet formalized, retains local factors for every
$0\le\varepsilon<1$. The near-unit condition gives
$\|w-(v^{\mathsf T}w)v\|\le\|w\|$; including dot-product and subtraction errors yields
$\|z\|\le(1+\varepsilon)^3\|w\|$. Combining this with matrix-vector, subtraction, and
normalization errors gives
$$\beta_{j+1}\le Q[\beta_j+(1+\varepsilon)\|\mathbf H\|_2],\qquad
Q=(1+\varepsilon)^5\sqrt{\frac{1+\varepsilon}{1-\varepsilon}}.$$
Thus geometric sums can bound the coefficients for arbitrary finite horizons. The resulting
local-error and model bounds can be large; finite upper bounds do not imply stability or
convergence. A terminal zero coefficient is bounded trivially and does not require a norm
lower bound for the unused last vector.

Recommended next shared change: separate arithmetic-run data from horizon hypotheses,
retain local norm-denominator conditions, and expose geometric accumulation before its
small-error corollaries. Reuse Mathlib finite-sum/product induction rather than inventing a
second recurrence framework. Feed the resulting certificates into the existing normalized
backend. Only CG then adds a positive lower spectral endpoint for inverse/error estimates.
This run-interface refactor and the geometric estimates are **not implemented** by the
absorption amendment. They are implemented separately in the subsequent
`Krylov-FinitePrecision-Runs.md` amendment, retaining local $\varepsilon\le1/100$ rather than
the full $\varepsilon<1$ normalization generalization discussed above.

## Previous result and source of losses

`LanczosRun.frobNorm_backwardH_sub_dilatedH_le` previously used `lanczosBackwardFactor k = 2000 k^4`.
The normalized interface previously had `normalizedBackwardBound k f p = 102 k^3 f + 96 k^2 p`.
It takes uniform recurrence-error bound `f` and weighted adjacent-inner-product bound `p`.
For a run, the current normalization lemmas supply `f = 12 k ε ‖H‖₂` and
`p = 8 k ε ‖H‖₂`. These definitions, the local arithmetic model, and terminal breakdown
conventions are retained.

The previous proof in `FinitePrecision/Backward.lean` bounded each block separately, used
`‖Y_r - Y_(r+1)‖₂ ≤ (2r+1) ‖Y_1‖₂`, multiplies by `‖W‖F = √(k+1)`, and finally pays another
`√(k+1)` to stack the blocks. This loses the isometry already present in the dilation.

The construction remains Chen's nilpotent dilation: `C = (I+R)⁻¹`, `K = I-C`, and
`Q_r = W C K^r`. The stacked `Q` has orthonormal columns. The source is the library proof
and the primary paper [Chen, §4](https://arxiv.org/html/2608.21268v1#S4); the estimates derived
here are a separate derivation, not a claim about the constants printed there.

## Implemented estimate

Let `J` embed the first `k` coordinates into `k+1`, `M` be the Gram commutator, and
`B = J M C_k`. The exchange recurrence gives

```
W (Y_r - Y_(r+1))
  = sum_{s < r} Q_(r-1-s) B K_k^s C_k - Q_r B.
```

Here the leading blocks `C_k` and `K_k` commute. For each fixed `s`, the stacked blocks
`Q_(r-1-s)` (zero for `r ≤ s`) are a shifted, truncated part of the isometry `Q`; their
operator norm is at most one. Thus the norm of a *whole stacked summand* is bounded by
`4 ‖M‖F`, rather than bounding its blocks individually. Summing the `k` possible shifts and
bounding `Q B` by `2 ‖M‖F` gives

```
‖dilatedResidual‖F ≤ 2 √(k+1) ‖residual‖F + (4k+2) ‖gramCommutator‖F.
```

For unit-vector data, the existing upper-triangular commutator identity also gives

```
‖gramCommutator‖F ≤ 2 √k p + 2 ‖basis‖F ‖residual‖F
                   ≤ 2 √k p + 2k f.
```

The first inequality follows by splitting off the diagonal: its Frobenius norm is at most
`2√k p`, while the strict upper part is bounded by the existing
`Matrix.IsUpperTriangular.frobNorm_sub_diagonal_le` and the recurrence residual identity.

The two completion summands have orthogonal row spaces, so Pythagoras improves its factor
from two to `√2`. Combining the residual and commutator estimates, using
`√(k(k+1)) ≤ 3k/2` for `k ≥ 1`, gives `‖E‖F ≤ 15k² f + 12k√k p`, and hence

```
normalizedBackwardBound k f p = 22 k² f + 17 k √k p.
```

For the current run normalization, this is at most `400 k³ ε ‖H‖₂`. The registered factors are
`lanczosDilatedResidualFactor k = 280 k³` and `lanczosBackwardFactor k = 400 k³`.
This improves the polynomial degree from four to three without strengthening the run hypotheses
or changing the backward matrix, starting vector, or exact recurrence claims.

## API and homes

No new hypothesis structure is needed. Auxiliary declarations concern existing objects, existing
named bounds keep their names, and the conditional theorem has one additional registered factor.

1. `NLAlib/Matrix/Subspaces/OrthonormalDilation.lean`: a reusable bound for shifted/truncated
   dilation blocks, or the generic partial-row-reindex norm fact in its natural Matrix home if
   search finds none. Search Mathlib and NLAlib before introducing a helper.
2. `NLAlib/Krylov/FinitePrecision/LanczosData.lean`: `frobNorm_gramCommutator_le`, the Frobenius
   analogue of `specNorm_gramCommutator_le`, reusing its existing structural lemmas.
3. `NLAlib/Krylov/FinitePrecision/Backward.lean`: the stacked exchange identity and residual
   estimate. The existing operator-commutator bound can remain a corollary through
   `frobNorm_le_sqrt_card_mul_specNorm`, rather than a duplicated
   blockwise proof. Keep each proof below 80 lines and this file below the hard size ceiling;
   split by topic into a dilation-estimates module if necessary, with the amendment recorded here.
4. `NLAlib/Krylov/FinitePrecision/NormalizedBackward.lean`: normalized commutator estimate and
   the improved bound, preserving the existing theorem names and constructions.
5. `docs/constants.toml` and the marked values/docstrings of consumers: update all three named
   bounds together, using the constants updater. No edits to checks, allowlists, build pins,
   target statements, or the approved target registry.

Central statements (existing namespaces and variables):

```lean
theorem LanczosData.frobNorm_gramCommutator_le {a b g : ℝ}
    (ha : ∀ j < k, |D.adjacentInner j| ≤ a)
    (hb : ∀ j < k, |D.β j| ≤ b)
    (hg : ∀ i, |D.normSqDefect i| ≤ g) :
    frobNorm D.gramCommutator ≤ 2 * Real.sqrt k * a +
      2 * (frobNorm D.basis * frobNorm D.residual) + k * (b * (2 * g))

theorem LanczosData.frobNorm_dilatedResidual_le_of_frobNorm_gramCommutator_le
    (hW : ∀ j, (D.basisSuccᵀ * D.basisSucc) j j = 1)
    {F G : ℝ} (hF : frobNorm D.residual ≤ F) (hG : frobNorm D.gramCommutator ≤ G) :
    frobNorm D.dilatedResidual ≤ 2 * Real.sqrt (k + 1) * F + (4 * k + 2) * G
```

Both central signatures now elaborate and their proofs compile. The independent review checked
the exchange identity, shift range, row-isometry bound, and constants before implementation.

## Consumers and checks

Implementation amendment, 2026-11-02: the reusable partial-row-reindex estimate is
`frobNorm_le_of_row_eq` in `Matrix/Norms/Block.lean`. It takes a selected-row finset, a row map
injective on that finset, equality on selected rows, and zero rows elsewhere. It introduces no
new data definition. `LanczosData.frobNorm_gramCommutator_sub_transpose_le` is shared by the
existing operator estimate and the new Frobenius estimate, avoiding a second residual-identity proof.

File-split amendment, 2026-11-02: the previous `Backward.lean` was already 989 lines. Its generic
`LanczosData` constructions/identities move, with unchanged names and statements, to
`FinitePrecision/Dilation.lean`; residual bounds live in `FinitePrecision/DilationEstimates.lean`;
`Backward.lean` imports both and keeps run-specific definitions, factors and corollaries.
This avoids an import cycle while keeping each file below the size limit. No proof is duplicated.

The improved run factor propagates to spectral localization and spectral-measure bounds in
`BackwardSpectral.lean`. The normalized bound propagates to CG backward/accuracy results;
inspect every consumer before changing its body. Do not narrow the statement to Lanczos-only
data or silently add a no-breakdown-last-step hypothesis.

First verify the scalar arithmetic independently. Then elaborate the fixed statement forms,
prove the generic Matrix and LanczosData steps, specialize to normalized data and runs, update
the named-bound registry and marked documentation, and run the required checks. Acceptance needs
warning-fatal builds, standard-axiom checks, source/rule/reference/constant checks and the full
`scripts/stage_check.sh` with no parallel build in this checkout.

Implementation amendment: generic leading-block multiplication and powers of an upper-triangular
matrix live in `ForMathlib/LinearAlgebra/Matrix/Block.lean`. They generalize the former private
multiplication helpers; the power identity is needed by the exchange convolution.
`commute_dilationC_dilationK` lives with the dilation constructions. The original operator-input
residual theorem is now a corollary of the stacked Frobenius estimate. The existing CG a priori
constant is preserved using `normalizedBackwardBound_le`, which compares the new bound with the
former coarse estimate for nonnegative inputs and at least one step.

## Completion improvement (implemented)

The user requested a further improvement after the first update. Independent read-only review
accepted the following extension, including the complex case, on 2026-11-02.

For orthonormal-column `Q`, let `P = I - Q Qᴴ`. The two summands of
`S = A Qᴴ + Q Aᴴ P` have orthogonal Frobenius inner product because `P Q = 0`.
The first has norm `‖A‖F`, and the second has norm at most `‖A‖F`. Thus
`‖S‖F ≤ √2 ‖A‖F`, without a symmetry or compatibility hypothesis. The arbitrary `S` need
not be Hermitian; the Lanczos completion uses its existing compatibility hypothesis separately.
The generic factor `√2` is sharp (`Q = e₁`, `A = e₂` in dimension two).

The implemented helper, with finite index types and decidable equality, belongs in
`Matrix/Norms/Projector.lean`, under `HasOrthonormalCols`:

```lean
theorem frobNorm_add_mul_conjTranspose_le {Q : Matrix m n 𝕜}
    (hQ : HasOrthonormalCols Q) (A : Matrix m n 𝕜) :
    frobNorm (A * Qᴴ + Q * Aᴴ * (1 - Q * Qᴴ)) ≤ Real.sqrt 2 * frobNorm A
```

Use existing `frobInner_mul_right`, `frobNorm_add_sq_of_frobInner_eq_zero`,
`HasOrthonormalCols.frobNorm_mul_conjTranspose_right`, `frobNorm_mul_left`, and
`IsStarProjection.frobNorm_mul_right_le`; do not reprove the isometry or Pythagoras API.
The old factor-two theorem remains as a corollary.

The normalized residual argument gives `‖E‖F ≤ 15k² f + 12k√k p`.
Since `15√2 ≤ 22` and `12√2 ≤ 17`, the normalized backward bound becomes
`22k² f + 17k√k p`. Substituting the run bounds gives `(264+136)k³ = 400k³`.
The residual scalar polynomial is `160k³ + 116k² ≤ 276k³`; register the readable
factor `280k³`. Update the same three named constants and all their consumers together.

## Conditional quadratic bound (implemented)

The mathematical reviewer verified the following extension and normalization helper signatures.
The existing unconditional cubic result remains the main general estimate. The additional theorem
assumes `k² ε ≤ 1/1000` and bounds the same backward model by `1000 k² ε ‖H‖₂`.
The current `k ε ≤ 1/100` run hypothesis does not imply this stronger condition.

A new `lanczosSmallRoundoffBackwardFactor k := 1000 k²` is registered in `docs/constants.toml`,
following docs/contributing/statements.md §2; its condition-specific name permits later numerical improvements.
The main theorem in new `FinitePrecision/BackwardBounds.lean`, importing `NormalizedBackward`, is:

```lean
theorem LanczosRun.frobNorm_backwardH_sub_dilatedH_le_of_sq_mul_le
    (hsmall : (k : ℝ) ^ 2 * L.ε ≤ 1 / 1000) :
    frobNorm (L.backwardH - L.dilatedH) ≤
      lanczosSmallRoundoffBackwardFactor k * L.ε * specNorm L.H
```

Set `Δ = ‖H_backward - H_dilated‖F` and `B = ‖H‖₂ + Δ`. Compression of the exact model recurrence
by its two orthonormal frames gives `‖T_succ‖₂ ≤ B`, hence every alpha and every beta, including
`β_k`, is bounded by `B`. Uniform local arithmetic estimates then give raw residual `10 εB`
and raw weighted adjacent product `(19/2) εB`, using the existing update-error identities.

Generalize the two proofs in `Normalized.lean` into public shared helpers (existing bounds become
corollaries), so the new theorem does not duplicate normalization:

```lean
theorem LanczosRun.norm_normalized_recurrenceError_le_of_le (hj : j < k) {F B : ℝ}
    (hF : ‖WithLp.toLp 2 (L.recurrenceError j)‖ ≤ F)
    (hβ : ∀ i ≤ j + 1, L.β i ≤ B) :
    ‖WithLp.toLp 2 (L.normalized.recurrenceError j)‖ ≤ (100 / 99) * F + 4 * L.ε * B

theorem LanczosRun.abs_normalized_adjacentInner_le_of_le (hj : j < k) {p : ℝ}
    (hp : |L.adjacentInner j| ≤ p) :
    |L.normalized.adjacentInner j| ≤ (100 / 99) ^ 2 * p
```

Their sign hypotheses follow from `hF`, `hp`, and `hβ` at zero. The reviewer checked terminal
breakdown: the beta-weighted normalization correction and adjacent product vanish. The helpers
give normalized `f ≤ 15 εB`, `p ≤ 10 εB`, so the new normalized bound implies
`Δ ≤ (330 k² + 170 k√k) εB ≤ 500 k² εB`. Absorb the `Δ` contribution under the stated smallness
condition, with no division by beta or new no-breakdown assumption.

## Obstruction to a generic exchange shortcut

An independently checked algebraic example shows that the linear multiplier on `‖M‖F` in a
generic exchange estimate cannot be replaced uniformly by a square-root multiplier. This example
is explanatory mathematics, not a new Lean lower-bound theorem.

For scalar `H=h`, take `v₀=0`, `v_j=(-1)^(j-1)` for `j≥1`, `β_j=j`, and
`α_j=h+2j-1`. These are normalized recurrence data with zero raw residual and positive beta.
The actual weighted adjacent products are `p_i=-(i+1)`. The commutator is upper triangular and
symmetric by the residual identity; its diagonal is `(-i)-(-(i+1))=1`, including the terminal
correction. Thus `M=I_k`. The dilation has `K` equal to minus the upper shift and
`Q_r=(-1)^r e_rᵀ`. Its residual satisfies

```
‖E‖F² = Σ(j<k) (6j²+6j+2) = 2k³,    ‖M‖F = √k.
```

The exchange amplification is exactly `√2 k`. This is not a `LanczosRun` counterexample: its alpha
coefficients do not satisfy the local dot-product update. It rules out the generic shortcut, not
a better run-specific theorem or an optimality claim for cubic backward error. The implemented
quadratic theorem exploits precisely the additional local run structure and a smallness condition.

## Final validation

`LEAN_NUM_THREADS=2 bash scripts/stage_check.sh` exited 0 on the final sources:

- 510 proved library modules, zero not-yet-proved modules; warning-fatal build passed with zero warnings.
- Axiom/unsafe/partial audit: 15,568 declarations, zero violations; all 14 environment linters passed.
- Import-root and build freshness checks passed.
- Kernel replay: 15,798 constants of 515 library/tool modules, zero violations; eight replay fixtures passed.
- Program checks, all five approved cost targets, and all nine access-model fixtures passed.
- References, all 51 registered constants, and all 35,229 documentation math spans passed.
- All 109 source/naming rules passed with zero unbaselined errors. Existing baseline/style warnings
  remain; no rule, baseline, allowlist, target approval, workflow, or build pin was changed.
- Duplicate report: eight existing private-only classes; no private/public or public/public duplicates.

Final independent read-only source and documentation review: **ACCEPT**. It checked both scopes,
terminal breakdown, the complex completion statement, the named factor, and the explanatory
counterexample. Targeted warning-fatal builds also passed for `BackwardBounds` and `CGBackward`.
The full audit log is `/tmp/fp-stage-final.log` in this workspace.
