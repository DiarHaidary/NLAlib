/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Norms.Net
public import NLAlib.Sketching.Properties.FixedSubspace
public import NLAlib.Sketching.Properties.JohnsonLindenstrauss
public import NLAlib.Sketching.Properties.Oblivious

/-!
# From the Johnson–Lindenstrauss property to subspace embeddings

A distributional JL tail at `ε` makes any sketch a `1 ∓ 2ε` embedding of a fixed `U` with
orthonormal columns, failing with probability at most `9^{dim_ℝ} δ`: on a `1/4`-net of the unit
sphere of `p → 𝕜` (`NLAlib.exists_finset_specNorm_le_div_of_isHermitian`, at most
`9 ^ finrank ℝ (p → 𝕜)` points), the Hermitian error `(S U)ᴴ (S U) - 1` has
`|re xᴴ E x| = |‖S (U x)‖² - 1| < ε` off the union of the JL events, hence `specNorm E < 2ε`. The
real dimension of the net is `card p` over `ℝ` and `2 card p` over `ℂ`, so the factor is
`9 ^ card p` and `81 ^ card p`. Any later family with a JL tail and no Gram-level tail gets its
OSE here.

Degenerate cases: for empty `p` every sketch is an embedding (the case split the proof starts
with, `docs/design/Sketching-S3.md` §8, item 6); for `ε ≤ 0` and nonempty `p` the JL hypothesis
bounds the whole space. No hypothesis on `ε`; `0 ≤ δ` is needed for the union bound over an empty
net and for `mono`.

This file is a skeleton of Sketching stage S3 (`docs/design/Sketching-S3.md` §3.1). At the
wrap-up it merges into `NLAlib/Sketching/Properties/JohnsonLindenstrauss.lean`.

## Main results

* `NLAlib.HasJLProperty.hasSubspaceEmbedding`: JL plus a net, for a fixed `U`.
* `NLAlib.HasJLProperty.isObliviousSubspaceEmbedding`: the oblivious form.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {k n p : Type*} [Fintype k] [Fintype n] {S : Ω → Matrix k n 𝕜} {ε δ : ℝ}

/-- **JL plus a net**: a JL tail at `ε` with failure `δ` gives a random `1 ∓ 2ε` embedding of a
fixed `U` with orthonormal columns, failing with probability at most `9 ^ (card p · dim_ℝ 𝕜) δ`.
[Vershynin2018, proof of Theorem 4.6.1, (4.22) (2020 draft)]; [Woodruff2014, Lemma 5 and
Theorem 6], there with a `1/2`-net and `O(ε)`. The net has radius `1/4`; another radius gives an
incomparable family in the radius, to be added when wanted. -/
theorem HasJLProperty.hasSubspaceEmbedding [IsFiniteMeasure μ] [Fintype p] [DecidableEq p]
    {U : Matrix n p 𝕜} (h : HasJLProperty S ε δ μ) (hδ : 0 ≤ δ) (hU : HasOrthonormalCols U) :
    HasSubspaceEmbedding S U (1 - 2 * ε) (1 + 2 * ε)
      (9 ^ (Fintype.card p * Module.finrank ℝ 𝕜) * δ) μ := by
  sorry

/-- **JL plus a net, oblivious form**: a JL tail at `ε` with failure `δ` makes `S` an oblivious
subspace embedding for dimension `d` with constants `1 ∓ 2ε` and failure
`9 ^ (d · dim_ℝ 𝕜) δ`. From `NLAlib.HasJLProperty.hasSubspaceEmbedding` at
`Fin (min d (card n))` by `NLAlib.IsObliviousSubspaceEmbedding.of_hasOrthonormalCols` and `mono`.
[Vershynin2018, proof of Theorem 4.6.1, (4.22) (2020 draft)]; [Woodruff2014, Theorem 6]. -/
theorem HasJLProperty.isObliviousSubspaceEmbedding [IsFiniteMeasure μ]
    (h : HasJLProperty S ε δ μ) (hδ : 0 ≤ δ) (d : ℕ) :
    IsObliviousSubspaceEmbedding S d (1 - 2 * ε) (1 + 2 * ε)
      (9 ^ (d * Module.finrank ℝ 𝕜) * δ) μ := by
  sorry

end NLAlib
