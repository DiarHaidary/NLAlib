# Nyström constants: Lean formalization amendment (2026-11-02)

Status: implementation authorized by the maintainer's explicit request in the current session,
"okay formalize in lean. im just interested in the lean stuff", following approval of the
independently audited mathematical statements. This is an amendment to the completed
TruncatedGN-Upper stage and EarlyTruncation portion of LowRank-S6, not a new algorithm or
hypothesis interface. Worktree: proof/nystrom-constants-2026-11-02, based on research/tgn-upper.
The maintainer requested a PR on 2026-11-03; committing and publishing this branch are authorized.

Mathematics: /home/ubuntu/nystrom-constants-2026-11-02/research.tex.
Only checked Lean proofs count as completed. The paper's universal constants do not become
library claims until their complete expectation theorems are proved, compiled, and axiom-audited.

## Interfaces and vocabulary

Reuse IsBestRankApprox, IsStarProjection, HasOrthonormalCols, HasLaw gaussianMatrix,
IndepFun, rangeProjector, truncatedSVD, and the existing matrix norm names. No new predicate,
parallel definition, Mathlib deviation, real transpose twin, or bare existential constant.
Deterministic statements remain over RCLike; Gaussian statements over real matrices.
Index types remain arbitrary Fintype. Statements use conjugate transpose.
Improved bounds preserve names and arities where hypotheses remain identical.
Incomparable sample-size hypotheses receive separate corollaries and named dimension functions.
Source: no printed source for the new constants; Gaussian ingredients retain their existing
HalkoMartinssonTropp2011 / TroppWebber2023 citations.

## Files and ownership

1. Matrix/Perturbation/TruncationWindow.lean: specialized rank3k lemma, then parameterized
   reciprocal-window Frobenius and nuclear estimates. Deterministic owner.
2. Matrix/Perturbation/BestRankApprox.lean: assemble localized deterministic estimate from
   preceding geometry, using the existing IsBestRankApprox API. Deterministic owner after item1.
3. RandomMatrix/Gaussian/InverseMoments/SpectralTail.lean (new): Gaussian smallest-singular
   tail and higher inverse moment combined by Hölder. Gaussian-moment owner.
4. RandomMatrix/Gaussian/BlockMoments.lean: supplied-second-moment Chevet bound and weighted
   window bound, reusing or moving the existing oracle's private weighted inverse moment.
   Gaussian-moment owner after item3; do not duplicate that proof.
5. Matrix/Spectral/LowRank.lean: coupled residual-tail energy lemma. Gaussian-moment owner.
6. LowRank/Gaussian/RangeFinderMoments.lean (new): comparison-rank moment estimates and residual
   constant10 under200k<=ell, plus spectrum-dependent baseline. Gaussian-moment owner.
7. ForMathlib/Analysis/Real/Sqrt.lean: scalar optimization of the free Young parameter.
   Early-truncation owner; this scalar theorem belongs in ForMathlib.
8. LowRank/Gaussian/EarlyTruncationRSVD.lean (new): move the RSVD-only factor/moment/expectation
   block out of EarlyTruncation.lean (currently1050lines), preserve declaration names, and
   generalize its private integration proof to a free parameter. Early-truncation owner.
9. LowRank/Gaussian/EarlyTruncation.lean: retain Gaussian GN completion; import item8 and
   derive the new500 right-width corollary. Early-truncation owner.
10. LowRank/Gaussian/TruncatedGeneralizedNystromRate.lean and Structural/Truncation.lean:
    strengthen conditional/unconditional assembly and complete200/14 and800/4 corollaries.
    Integrator, only after the proved dependencies.
11. docs/constants.toml: register every new named factor/dimension and update existing factor
    LaTeX/body markers with check_constants.py. Early owner initially owns this shared file.
12. NLAlib.lean: regenerate with mk_all after new modules have compiled. Integrator.
13. docs/port/status.md and ledger.json: record completed and remaining statements at stopping.
    Integrator. Do not list an unproved target as proved.

New imports:
- SpectralTail imports InverseMoments.Spectral and ExtremeSingularValues.
- RangeFinderMoments imports Gaussian.RangeFinder, Matrix.Spectral.LowRank, BlockMoments,
  and SpectralTail only when its proofs need the split moment.
- EarlyTruncationRSVD imports the RSVD block's existing dependencies, never EarlyTruncation.
- EarlyTruncation imports EarlyTruncationRSVD and retains GN-specific imports.
No scaffold file is imported by NLAlib; no sorry is introduced into NLAlib.

## Fixed initial signatures

The right window projector below is n×n, not the adjoint of the m×m left projector.

~~~lean
theorem rank_sub_mul_mul_truncatedSVD_le
    (B : Matrix m n 𝕜) (k : ℕ) {a b : ℕ}
    (hak : a ≤ k) (hkb : k ≤ b)
    {Z : Matrix m m 𝕜} (hZk : Z.rank ≤ k) :
    ((Z - rangeProjector (truncatedSVD B k)) * B -
      (rangeProjector (truncatedSVD B b) -
        rangeProjector (truncatedSVD B a)) *
      (Z - rangeProjector (truncatedSVD B k)) * B *
      (rangeProjector ((truncatedSVD B b)ᴴ) -
        rangeProjector ((truncatedSVD B a)ᴴ))).rank ≤ 3 * k
~~~

The remaining geometry retains the current window theorem's complete hypotheses and projector
expressions, with reciprocal-window scalar c>1. Constants are
(c^2+1)/(c^2-1) for residual Frobenius energy,
2min(k,b-k)+(c^2/(c^2-1))*D/theta^2 for compressed nuclear norm.
Specialization c=5/3 gives69 and320/21 in the complete perturbation theorem.
The full-basis completion uses HasOrthonormalCols.exists_fromCols rather than an unrelated
eigenbasis, preserving the chosen truncations at ties.

~~~lean
theorem integral_specNorm_pinv_sq_le_add_exp_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix r t) μ)
    {p u : ℝ} (hp : 2 < p)
    (hpt : p ≤ (Fintype.card t : ℝ) - Fintype.card r)
    (hu : 0 < u)
    (hu' : u < √(Fintype.card t : ℝ) - √(Fintype.card r : ℝ)) :
    ∫ ω, specNorm (pinv (X ω)) ^ 2 ∂μ ≤
      (√(Fintype.card t : ℝ) - √(Fintype.card r : ℝ) - u)⁻¹ ^ 2 +
        gaussianPinvSpecNormBound (Fintype.card r) (Fintype.card t) ^ 2 *
          Real.exp (-u ^ 2 / 2 * (1 - 2 / p))

theorem frobNorm_sub_truncatedSVD_sq_add_natCast_mul_singularValues_sq_le
    (A : Matrix m n 𝕜) (k d : ℕ) :
    frobNorm (A - truncatedSVD A (k + d)) ^ 2 +
        (d : ℝ) * singularValues A (k + d) ^ 2 ≤
      frobNorm (A - truncatedSVD A k) ^ 2

theorem integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_add_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ)
    {k j : ℕ} (hkj : k ≤ j) (hjl : j + 2 ≤ Fintype.card l) :
    ∫ ω, frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 ∂μ ≤
      frobNorm (A - truncatedSVD A k) ^ 2 +
        (k : ℝ) / ((Fintype.card l : ℝ) - j - 1) *
          frobNorm (A - truncatedSVD A j) ^ 2

theorem Real.le_add_sqrt_of_forall_le_div_one_sub
    {x a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ θ : ℝ, 0 < θ → θ < 1 →
      x ≤ (a + b / θ) / (1 - θ)) :
    x ≤ a + 2 * b + √(4 * b * (a + b))
~~~

## Early-truncation factor and sample-size API

Let a=(1+sqrt(2k/ell))*((1-sqrt(k/ell))^(-2)+10/sqrtell) and
b=(k/ell)*sqrt(1+2/(kell))*sqrt((1-sqrt(k/ell))^(-8)+263/sqrtell).
Register earlyTruncatedRSVDYoungFactor(k ell)(theta):=(a+b/theta)/(1-theta).
Strengthen existing earlyTruncatedRSVDFactor body to a+2b+sqrt(4b(a+b)); retain its arity.
The private frame expectation proof takes arbitrary0<theta<1, and its public parameterized
theorem has100k<=ell and900<=ell, matching the current factor theorem.
The existing fixed-factor expectation theorem follows by scalar optimization.

Register real-valued dimensions:
earlyTruncatedRSVDRelativeErrorDim k eps := max900 (400*k/eps^2),
earlyTruncatedGNRangeDim k eps := max900 (500*k/eps^2),
earlyTruncatedGNCorangeDim k eps := 10*k/eps+10*k+1.
Use these in new dimension-based sample-size corollaries; retain existing900/3600 forms as
consequences when useful. They are incomparable at small absoluteell, so do not silently
replace the old hypothesis by400k alone.

The complete new earlyGN conclusion is the existing expected squared-error conclusion with
HasLaw X gaussianMatrix, HasLaw Psi gaussianMatrix, IndepFun X Psi,0<eps<=1,
earlyTruncatedGNRangeDim k eps<=cardl,earlyTruncatedGNCorangeDim k eps<=cardp.
Use RSVD accuracy9eps/10 and exact completion. No independent sketch assumption is dropped.

## Proof dependencies and checks

First parallel work is rank3, the inverse moment / coupled tail, and early scalar optimization.
The deterministic residual geometry must precede the final69 theorem, which must precede
late-truncation constants. New sample constants are not obtained by replacing literals.
The early400 proof uses the monotone algebraic envelope at y=1/20, not numerical fitting.
The late200/14 proof uses residual10, inverse moment20 and split13/4.

All library edits are reversible and within the explicit formalization request.
The filesystem is read-only by default; request execution escalation for file writes/builds.
Use a global flock /tmp/nystrom-lean-build.lock for Lean commands, LEAN_NUM_THREADS=2, and
lake lean <file> -- -M8000 or targeted lake build, never a bare build.
No two builds run concurrently. Logs stay outside tracked source.
Before acceptance: compile, inspect #print axioms, check_rules --files, refs, constants,
generated root import check, and a separate statement/proof review.
No user-facing prose/PDF work is in scope for this implementation.

## Dated API amendment 1 (2026-11-02)

For the residual10 theorem, register `gaussianRangeFinderResidualDim k := 200*k` (natural-valued)
and `gaussianRangeFinderResidualConstant := 10`. The hypothesis is a comparison with the named dimension;
the bound uses the named constant. This is incomparable with the existing121 theorem at4k<=ell,
so it receives a separate hypothesis-distinguished name rather than silently changing that theorem's scope.

## Dated API amendment 2 (2026-11-02)

Necessary generic entrywise Hermitian/Frobenius identities may be added to existing
`Matrix/Norms/Frobenius.lean` (507 lines at start), and chosen-SVD basis completion identities
to existing `Matrix/Spectral/SVD.lean` (637 lines), rather than exceeding the window file's topic budget.
Both additions are owned by the deterministic track and must remain generic, not duplicate chosen SVDs.

The inverse-moment track may add a general restricted-integral Hölder helper in
`ForMathlib/MeasureTheory/Integral/Bochner/Set.lean`, in the `MeasureTheory` namespace, after searching
Mathlib's `MemLp` and exponent-comparison APIs. Its subject is a scalar restricted integral, so it
belongs in ForMathlib rather than a Gaussian-specific file.

The existing private weighted pseudoinverse Frobenius moment in
`LowRank/Gaussian/TruncatedGeneralizedNystromOracle.lean` may be moved, not copied, into
`RandomMatrix/Gaussian/InverseMoments/Frobenius.lean`; the oracle then imports and reuses its public
version. This is a vocabulary-preserving helper promotion, not a new hypothesis interface.

Early GN keeps the existing completion-width form when strengthening its old3600 right coefficient
to1600. The separate500 right-width result has the larger explicitly named left dimension;
it does not silently change the old theorem's left-sketch hypothesis.

## Dated API amendment 3 (2026-11-02)

The reciprocal-window geometry is split by norm. The generic Frobenius result belongs in
`Matrix/Perturbation/TruncationWindowFrobenius.lean`; the sharp compressed nuclear result belongs
in `Matrix/Perturbation/TruncationWindowNuclear.lean`. Both import the existing
`TruncationWindow.lean`. The nuclear module proves its reciprocal tail weight and weighted
residual inequality before deriving the public bound
`2*min(k,b-k)+(c^2/(c^2-1))*D/theta^2` for `c>1`. It needs only the lower-window inclusion
`a<=k`, upper-window inclusion `k<=b`, the upper-window spectral threshold, positive theta,
and an orthogonal projector of rank at most k; no lower-window spectral threshold is added.

The existing private `nuclearNorm_mul_mul_eq_frobNorm_sq` and
`nuclearNorm_mul_sub_mul_le_of_mul_eq` in `TruncationWindow.lean` are promoted with their
existing documentation so the new module can reuse their generic projector geometry.
No proof is copied and no chosen-SVD convention changes. The coefficients depending on c
remain inline algebraic expressions rather than additional named constants.

## Dated API amendment 4 (2026-11-02)

The complete late-truncation conditional and unconditional 200/14 estimates and their numeric
helpers belong in the existing `LowRank/Gaussian/TruncatedGeneralizedNystromRate.lean` while its
total remains below 1500 lines. If the conditional window-moment interface requires a topical
split to keep modules near 1000 lines, use a new
`LowRank/Gaussian/TruncatedGeneralizedNystromWindow.lean` and import it from the rate module.
The general parametric Gaussian inverse-moment theorem belongs in
`RandomMatrix/Gaussian/InverseMoments/SpectralTail.lean`. A private 2800/14 numerical
certificate used only by the rate proof may remain in the rate module; it introduces no
additional public constant or registry entry. The deterministic track owns the
69 structural estimate and conditional moment assembly; the integrator owns the linear-majorant
unconditional assembly. Only compiled complete matrix-error theorems support the final
sample-size claim. The implementation scope remains Lean proofs and their repository metadata.

## Dated API amendment 5 (2026-11-02)

Supplied inverse-moment wrappers for Gaussian oblique completion belong in the topical new
`Regression/SketchAndSolveMoments.lean`, importing `SketchAndSolve.lean`, so the existing
Gaussian/Haar module stays near its original size. Promote its existing almost-sure Gaussian
block representation as `ae_specNorm_obliqueProjector_mul_eq_of_hasLaw_gaussianMatrix`,
reusing the proof and documenting the full Gaussian/frame hypotheses. Both wrappers take the
canonical Gaussian inverse second-moment bound on matrices of size rank(X) by p; no selected
frame enters their public hypotheses. The weighted term retains the exact denominator p-rank(X)-1.

## Dated API amendment 6 (2026-11-03)

The complete conditional late-truncation theorem belongs in the new
`LowRank/Gaussian/TruncatedGeneralizedNystromWindow.lean`, which imports the base
`TruncatedGeneralizedNystrom.lean` rather than the rate module. The rate module may import
this new window module for unconditional assembly without an import cycle. The reusable
numeric inverse second-moment corollary, at least 2800 columns and fourteen times the height,
belongs in `RandomMatrix/Gaussian/InverseMoments/SpectralTail.lean` beside its general
split theorem. Promote the existing row-space truncation monotonicity lemma
`range_conjTranspose_truncatedSVD_le` in `BestRankApprox.lean` so conditional assembly
reuses the same chosen-SVD geometry rather than copying its proof.

## Dated API amendment 7 (2026-11-03)

The final unconditional relative-error theorem lives in the topical
LowRank/Gaussian/TruncatedGeneralizedNystromRelativeError.lean, importing Window and
RangeFinderMoments. Its 309 lines keep the conditional window analysis and the old rate
module below their topic budgets. It registers truncatedGeneralizedNystromRangeDim(k,eps)
=200*k/eps and truncatedGeneralizedNystromCorangeDim(ell)=14*ell, and retains both Gaussian
laws, independence, and 0<eps<=1. Every rank and shape is allowed, including k=0.
Its private composition proof integrates the actual conditional theorem, then uses the
proved coefficient196<200. No hypothesis interface or algorithm changes.

## Dated integration amendment 8 (2026-11-03)

The fixed 5/3-window BestRankApprox and structural corollaries use the hypothesis suffix
of_singularValues_le; only the parameterized reciprocal-window results use of_one_lt.
Their statements and proofs are unchanged. Required Result displays use the registered
algorithm names. The ledger scanner now also unions declarations from the existing canonical
Lean-source parser, preserving its old structure-field handling and recognizing valid
multiline theorem names. An independent corpus check found no lost declarations.
