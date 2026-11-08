# Matrix audit corrections (2026-11-04)

This amendment fixes findings F07, F08 and the matrix part of F12. It changes no
matrix objects or hypothesis interfaces.

## Objects and placement

The existing `IsBestRankApprox`, `truncatedSVD`, `rangeProjector`, `specNorm` and
`frobNorm` interfaces stay unchanged. Four absolute numerical coefficients live
beside their owning results in `Matrix/Perturbation/BestRankApprox.lean`:

| Coefficient | Current value | Role |
|---|---:|---|
| `localTruncationNoiseConstant` | 483 | squared noise in the factor-two window bound |
| `localTruncationWindowConstant` | 32 | compressed noise in that bound |
| `reciprocalWindowNoiseConstant` | 69 | squared noise in the reciprocal-window bound |
| `reciprocalWindowCrossConstant` | 320/21 | compressed noise in that bound |

These are `irreducible_def`s over `ℝ`, with `_pos` and `_le` API. The latter
compares to the current explicit upper bound, so future improvements preserve the
API. Their definitions are registered in `docs/constants.toml`. Mathlib and the
library were searched: there is no existing named coefficient for these bounds.
No new mathematical notion or Mathlib deviation is introduced.

## Statement shapes

For `𝕜 : Type*` with `RCLike 𝕜`, arbitrary finite row and column types,
`hY : IsBestRankApprox (B + N) k Y`, `1 ≤ k`, and the existing window hypotheses,
the unchanged primary theorem name concludes

```lean
frobNorm (B - Y) ^ 2 ≤ frobNorm (B - truncatedSVD B k) ^ 2 +
  localTruncationNoiseConstant * k * specNorm N ^ 2 +
  localTruncationWindowConstant * singularValues B (k - 1) *
    ((min k (b - k) : ℕ) : ℝ) *
    specNorm ((rangeProjector (truncatedSVD B b) - rangeProjector (truncatedSVD B a)) * N *
      (rangeProjector (truncatedSVD B b)ᴴ - rangeProjector (truncatedSVD B a)ᴴ))
```

Its exact hypotheses remain `a ≤ k ≤ b`, `2 * singularValues B (k - 1) ≤
singularValues B i` for every `i < a`, `singularValues B a ≤
2 * singularValues B (k - 1)`, and `singularValues B b ≤
singularValues B (k - 1) / 2`. The existing proof yields 483 and 32;
the former public values 500 and 40 discarded this improvement.

The reciprocal-window variant retains its distinct hypotheses with `5 / 3` in
place of `2`; its conclusion uses `reciprocalWindowNoiseConstant` and
`reciprocalWindowCrossConstant`. Neither variant is claimed to dominate the
other because their windows differ. Both retain their public theorem names.

## Consumers and documentation

The two localized generalized Nyström bounds in `LowRank/Structural/Truncation.lean`
use the corresponding named coefficients directly. No duplicate numeric theorem
is added. All four result docstrings state their window conditions and show the
current coefficients in their equations, with registry value markers.

The Gaussian expected-rate proof in `LowRank/Gaussian/TruncatedGeneralizedNystromRate.lean`
uses the stable comparison lemmas to recover its existing internal 500/40 estimate. Its
coarser public rate is unchanged; it does not unfold or depend on the new coefficient bodies.
The private Gaussian moment step in `LowRank/Gaussian/TruncatedGeneralizedNystromWindow.lean`
likewise recovers its existing 69 and 320/21 coefficients through the comparison API.

Four oblique-projector error docstrings explicitly state
`(S * X).rank = X.rank`, and define their projectors without referring readers to
an unnamed hypothesis. Their Lean statements and proofs are unchanged.

The three squared sesquilinear norm theorems in `Matrix/Inequalities/Block.lean`
and `Kantorovich.lean` move `sq` after the complete norm argument (N6). The
`EntrywiseFunctions.lean` consumer follows the rename. The rename map records all
three and the four changed bound statements. No compatibility aliases are
needed before v0.1.

## Verification and review

Compile all changed modules and their consumers; run the constants, source-rule,
naming, full build, audit, replay and metadata checks. Review the theorem
read-back against these exact assumptions, including zero rank and empty index
types: no new dimensional or nonemptiness assumptions are introduced.
