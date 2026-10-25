/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Probability.IdentDistrib
public import NLAlib.Probability.Measurability.Matrix
public import NLAlib.RandomMatrix.DeferredDecision
public import NLAlib.RandomMatrix.Gaussian.Rank
public import NLAlib.RandomMatrix.Haar.Basic
public import NLAlib.RandomMatrix.UnitaryInvariance
public import NLAlibScaffold.ForMathlib.Probability.Independence.Basic
public import NLAlibScaffold.Probability.QueryModel.Basic
public import NLAlibScaffold.RandomMatrix.Gaussian.Invariance

/-!
# Deferred decision for adaptive matrix–vector queries: the theorems of stage LB-A

Statements for `NLAlib/RandomMatrix/DeferredDecision.lean` whose proofs are deferred
(`docs/design/Probability-MatvecQueryModel.md`, §3.4).

**Gaussian matrices, two-sided queries.** An algorithm queries a standard Gaussian
$\mathbf{X} \in \mathbb{R}^{d \times k}$ through `twoSidedMulVec` (pair queries
$(\mathbf{w}, \mathbf{u})$ answered by $(\mathbf{X}\mathbf{w}, \mathbf{X}^{\mathsf{H}}\mathbf{u})$,
chosen adaptively). Replacing the unqueried block
$\mathbf{E}\mathbf{X}\mathbf{F}$ by the same block of an independent copy changes neither the
transcript (`QueryAlgorithm.transcript_resample`) nor the joint law of transcript and matrix
(`QueryAlgorithm.IsMeasurable.identDistrib_resample_of_hasLaw_gaussianMatrix`); in frames, the
unqueried block is a standard Gaussian matrix independent of the transcript.

**Unitarily invariant laws.** For a right unitarily invariant law (Gaussian, Haar), the matrix may
be rotated on the right by any orthogonal matrix that fixes what the transcript has revealed,
chosen as a function of the transcript: the right parts of the queries and the second components
(products $\mathbf{X}^{\mathsf{H}}\mathbf{u}$) of the responses.
Non-adaptive (one block of queries $\mathbf{V}$) and adaptive forms.

## Main results

* `NLAlib.QueryAlgorithm.transcript_resample`.
* `NLAlib.QueryAlgorithm.IsMeasurable.identDistrib_resample_of_hasLaw_gaussianMatrix`: adaptive
  deferred decision, resampling form.
* `NLAlib.QueryAlgorithm.IsMeasurable.hasLaw_prodMk_conjTranspose_mul_mul_of_hasLaw_gaussianMatrix`:
  adaptive deferred decision, frame form.
* `NLAlib.identDistrib_prodMk_mul_of_isRightUnitarilyInvariant`: the non-adaptive stabilizer
  form.
* `NLAlib.QueryAlgorithm.IsMeasurable.identDistrib_prodMk_mul_of_isRightUnitarilyInvariant`: the
  adaptive stabilizer form.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

namespace QueryAlgorithm

variable {d k β : Type*} [Fintype d] [Fintype k] {q : ℕ}

/-! ### Gaussian matrices -/

/-- **The resampled matrix gives the same transcript**: an algorithm making `q` pair queries to
`twoSidedMulVec X`, $\mathbf{X} \in \Bbbk^{d \times k}$, gets the same responses from
`alg.resample X X'`, which differs from $\mathbf{X}$ only in the block
$\mathbf{E}\mathbf{X}\mathbf{F}$ orthogonal to all left queries and all right queries.
Proof: M, about 25 lines. `QueryAlgorithm.transcript_eq_of_forall_apply_queries_eq`. For the
`j`-th query $(\mathbf{w}, \mathbf{u})$, $\mathbf{w}$ is column `j` of `alg.rightQueryMatrix τ`
and $\mathbf{u}$ column `j` of `alg.leftQueryMatrix τ`, so
$\mathbf{E}\mathbf{u} = \mathbf{0}$ and $\mathbf{F}\mathbf{w} = \mathbf{0}$ (`rangeProjector`
fixes its range: `rangeProjector_mul_self` or `Matrix.mul_apply` at a column). Then
`twoSidedMulVec Y (w, u)` is $(\mathbf{Y}\mathbf{w}, \mathbf{Y}^{\mathsf{H}}\mathbf{u})$
(`twoSidedMulVec`, `Prod.ext`), and the two correction terms vanish:
$\mathbf{E}\mathbf{Z}\mathbf{F}\mathbf{w} = \mathbf{0}$ and
$(\mathbf{E}\mathbf{Z}\mathbf{F})^{\mathsf{H}}\mathbf{u}
= \mathbf{F}\mathbf{Z}^{\mathsf{H}}\mathbf{E}\mathbf{u} = \mathbf{0}$ (projectors are Hermitian,
`IsStarProjection` of `rangeProjector`). -/
theorem transcript_resample [DecidableEq d] [DecidableEq k] {𝕜 : Type*} [RCLike 𝕜]
    (alg : QueryAlgorithm ((k → 𝕜) × (d → 𝕜)) ((d → 𝕜) × (k → 𝕜)) q β) (X X' : Matrix d k 𝕜) :
    alg.transcript (twoSidedMulVec (alg.resample X X')) = alg.transcript (twoSidedMulVec X) := by
  sorry

/-- **Adaptive deferred decision for a Gaussian matrix, resampling form**: let
$\mathbf{X}, \mathbf{X}'$ be independent standard Gaussian $d \times k$ matrices and $\tau$ the
transcript of a measurable algorithm making `q` adaptive pair queries to `twoSidedMulVec X`
(products $\mathbf{X}\mathbf{w}$ and $\mathbf{X}^{\mathsf{H}}\mathbf{u}$). With
$\mathbf{E}$, $\mathbf{F}$ the projectors onto the orthogonal complements of the left and right
queries, $(\tau, \mathbf{X})$ has the law of $(\tau, \widetilde{\mathbf{X}})$,
$$\widetilde{\mathbf{X}} = \mathbf{X} - \mathbf{E}\mathbf{X}\mathbf{F} +
\mathbf{E}\mathbf{X}'\mathbf{F}\,:$$
conditionally on the transcript, the unqueried block is a fresh Gaussian block. With
`QueryAlgorithm.transcript_resample`, $\tau$ is also the transcript of $\widetilde{\mathbf{X}}$.
[ZhangEtAl2026, Lemma 4.1]; [BravermanHazanSimchowitzWoodworth2020, Lemma 3.4]; there with
entries $\mathcal{N}(0, 1/d)$, orthonormal queries, at most $s$ of them, and a $\sigma$-field,
conditional laws and a transcript-measurable rotation; here unit variance, basis-free (no
orthonormality assumption on the queries) and no bound on `q`.
Proof: L, about 70 lines. Induction on `q` for all algorithms, through the truncated algorithm
`alg.truncate i` (`QueryAlgorithm.truncate`, measurable by
`QueryAlgorithm.IsMeasurable.truncate`), whose transcript is `alg.history _ i`
(`QueryAlgorithm.transcript_truncate`);
state the invariant for `history i` with the projectors $\mathbf{E}_i$, $\mathbf{F}_i$ of the
first `i` queries. Base `i = 0`: the projectors are `1` (`rangeProjector` of a matrix with no
columns is `0`), $\widetilde{\mathbf{X}} = \mathbf{X}'$, and $\mathbf{X}$, $\mathbf{X}'$ have the
same law. Step: the next query is a measurable function of the history, so (history, response,
matrix) is a measurable image of (history, matrix); apply the invariant at `i` jointly with a
third independent copy $\mathbf{X}''$ (extend $\Omega$ by `Measure.prod` with
`gaussianMatrix d k`, `IdentDistrib` transfers back through the projection). Then freeze
(`ProbabilityTheory.IndepFun.identDistrib_prodMk_of_forall_map_eq` with
$T = (\text{history}, \mathbf{X})$, $Z = (\mathbf{X}', \mathbf{X}'')$); for fixed $T$ the needed
identity of laws is `NLAlib.identDistrib_mul_mul_of_hasLaw_gaussianMatrix` with
$\mathbf{E}_1 = \mathbf{E}_i \succeq \mathbf{E}_2 = \mathbf{E}_{i+1}$ (range inclusion of the
query matrices, `rangeProjector` monotone), plus the observations that the new response does not
see the block $\mathbf{E}_{i+1}(\cdot)\mathbf{F}_{i+1}$ and that
$\mathbf{E}_i\mathbf{E}_{i+1} = \mathbf{E}_{i+1}$ (the hypothesis `E₁ * E₂ = E₂` of G1).
Measurability of the projectors:
`QueryAlgorithm.IsMeasurable.measurable_leftQueryMatrix`,
`QueryAlgorithm.IsMeasurable.measurable_rightQueryMatrix`, `measurable_rangeProjector`. Split the
step into a private lemma if it exceeds 80 lines. -/
theorem IsMeasurable.identDistrib_resample_of_hasLaw_gaussianMatrix [DecidableEq d]
    [DecidableEq k] [MeasurableSpace β]
    {alg : QueryAlgorithm ((k → ℝ) × (d → ℝ)) ((d → ℝ) × (k → ℝ)) q β} (halg : alg.IsMeasurable)
    {X X' : Ω → Matrix d k ℝ} (hX : HasLaw X (gaussianMatrix d k) μ)
    (hX' : HasLaw X' (gaussianMatrix d k) μ) (hXX' : IndepFun X X' μ) :
    IdentDistrib (fun ω => (alg.transcript (twoSidedMulVec (X ω)), X ω))
      (fun ω => (alg.transcript (twoSidedMulVec (X ω)), alg.resample (X ω) (X' ω))) μ μ := by
  sorry

/-- **Adaptive deferred decision for a Gaussian matrix, frame form**: let $\tau$ be the transcript
of a measurable algorithm making `q` adaptive pair queries to `twoSidedMulVec X`, for a standard
Gaussian $\mathbf{X} \in \mathbb{R}^{d \times k}$. For frames
$\mathbf{W}_L(\tau) \in \mathbb{R}^{d \times r}$ and
$\mathbf{W}_R(\tau) \in \mathbb{R}^{k \times s}$ (orthonormal columns), chosen measurably
from the transcript and orthogonal to all left, respectively right, queries, the block
$\mathbf{W}_L^{\mathsf{H}}\mathbf{X}\mathbf{W}_R$ is a standard Gaussian $r \times s$ matrix
independent of $\tau$: $(\tau, \mathbf{W}_L^{\mathsf{H}}\mathbf{X}\mathbf{W}_R)$ has law
$\mathbb{P}_\tau \otimes \mathcal{N}(0, 1)^{r \times s}$.
[ZhangEtAl2026, Lemma 4.1] (the block $\mathbf{D}_t$; there entries $\mathcal{N}(0, 1/d)$,
orthonormal queries and at most $s$ of them, here unit variance, any queries, no bound on `q`);
[Shamir2026, Lemma 3] (the Haar analogue, non-adaptive).
For a non-adaptive algorithm the frames may be fixed, and this is
`NLAlib.indepFun_conjTranspose_mul_of_hasLaw_gaussianMatrix` on both sides.
Proof: M, about 40 lines. On the extended space `μ.prod (gaussianMatrix d k)` take
$\mathbf{X}'$ the second coordinate (independent of $\mathbf{X}$). By
`QueryAlgorithm.IsMeasurable.identDistrib_resample_of_hasLaw_gaussianMatrix` composed with the
measurable map $(t, \mathbf{Y}) \mapsto (t, \mathbf{W}_L(t)^{\mathsf{H}}\mathbf{Y}\mathbf{W}_R(t))$
(`IdentDistrib.comp`), the pair has the law of
$(\tau, \mathbf{W}_L^{\mathsf{H}}\widetilde{\mathbf{X}}\mathbf{W}_R)$, and
$\mathbf{W}_L^{\mathsf{H}}\widetilde{\mathbf{X}}\mathbf{W}_R
= \mathbf{W}_L^{\mathsf{H}}\mathbf{X}'\mathbf{W}_R$ because
$\mathbf{W}_L^{\mathsf{H}}\mathbf{E} = \mathbf{W}_L^{\mathsf{H}}$ and
$\mathbf{F}\mathbf{W}_R = \mathbf{W}_R$ (from `hWL`, `hWR`: the frames are orthogonal to the
ranges of the left and right query matrices, `rangeProjector`).
Then freeze with $T = \tau$, $Z = \mathbf{X}'$
(`ProbabilityTheory.IndepFun.hasLaw_prodMk_prod_of_forall_map_eq`): for fixed $t$ the law of
$\mathbf{W}_L(t)^{\mathsf{H}}\mathbf{X}'\mathbf{W}_R(t)$ is `gaussianMatrix r s`
(`hasLaw_mul_mul_of_hasLaw_gaussianMatrix`). -/
theorem IsMeasurable.hasLaw_prodMk_conjTranspose_mul_mul_of_hasLaw_gaussianMatrix
    [MeasurableSpace β] {r s : Type*} [Fintype r] [Fintype s] [DecidableEq r] [DecidableEq s]
    {alg : QueryAlgorithm ((k → ℝ) × (d → ℝ)) ((d → ℝ) × (k → ℝ)) q β} (halg : alg.IsMeasurable)
    {X : Ω → Matrix d k ℝ} (hX : HasLaw X (gaussianMatrix d k) μ)
    {WL : (Fin q → (d → ℝ) × (k → ℝ)) → Matrix d r ℝ}
    {WR : (Fin q → (d → ℝ) × (k → ℝ)) → Matrix k s ℝ}
    (hWLm : Measurable WL) (hWRm : Measurable WR) (hWLo : ∀ τ, HasOrthonormalCols (WL τ))
    (hWRo : ∀ τ, HasOrthonormalCols (WR τ)) (hWL : ∀ τ, (WL τ)ᴴ * alg.leftQueryMatrix τ = 0)
    (hWR : ∀ τ, (WR τ)ᴴ * alg.rightQueryMatrix τ = 0) :
    HasLaw (fun ω => (alg.transcript (twoSidedMulVec (X ω)),
        (WL (alg.transcript (twoSidedMulVec (X ω))))ᴴ * X ω *
          WR (alg.transcript (twoSidedMulVec (X ω)))))
      ((μ.map fun ω => alg.transcript (twoSidedMulVec (X ω))).prod (gaussianMatrix r s)) μ := by
  sorry

end QueryAlgorithm

/-! ### Unitarily invariant laws -/

variable {m n : Type*} [Fintype n] [DecidableEq n]

/-- **Deferred decision for a unitarily invariant law, non-adaptive stabilizer form**: let the law
$\nu$ of $\mathbf{X} \in \mathbb{R}^{m \times n}$ be right unitarily invariant (Gaussian, Haar),
$\mathbf{V} \in \mathbb{R}^{n \times p}$ fixed, and $\mathbf{S}(\mathbf{Y})$ an orthogonal matrix
chosen measurably from the response $\mathbf{Y} = \mathbf{X}\mathbf{V}$ with
$\mathbf{S}(\mathbf{Y})\mathbf{V} = \mathbf{V}$. Then $(\mathbf{X}\mathbf{V}, \mathbf{X})$ has the
law of $(\mathbf{X}\mathbf{V}, \mathbf{X}\mathbf{S}(\mathbf{X}\mathbf{V}))$: given what the
queries revealed, $\mathbf{X}$ is invariant under the rotations that fix the queries.
[Shamir2026, Lemma 3]; there for a Haar orthogonal matrix and a fixed subspace, stated with
conditional laws.
Proof: L, about 60 lines. Fix a frame $\mathbf{W} \in \mathbb{R}^{n \times c}$ of the orthogonal
complement of the column span of $\mathbf{V}$
(`c := Fin (card n - finrank (span (range Vᵀ)))` internally, so `p` need not be finite; the
library's orthonormal completion), and on the extended space `μ.prod (haarFrame c c)` let
$\mathbf{O}_s = \mathbf{I} - \mathbf{W}\mathbf{W}^{\mathsf{H}} +
\mathbf{W}\mathbf{O}\mathbf{W}^{\mathsf{H}}$,
a random orthogonal matrix fixing $\mathbf{V}$, independent of $\mathbf{X}$. (1)
$(\mathbf{X}\mathbf{V}, \mathbf{X})$ and $(\mathbf{X}\mathbf{V}, \mathbf{X}\mathbf{O}_s)$ have
the same law by
freezing `ProbabilityTheory.IndepFun.identDistrib_prodMk_of_forall_map_eq` with $T = \mathbf{O}$
and right invariance (`hasLaw_mul_const_of_isRightUnitarilyInvariant`), since
$\mathbf{O}_s\mathbf{V} = \mathbf{V}$. (2) Every orthogonal $\mathbf{S}$ fixing $\mathbf{V}$ is
$\mathbf{I} - \mathbf{W}\mathbf{W}^{\mathsf{H}} + \mathbf{W}\mathbf{s}\mathbf{W}^{\mathsf{H}}$ with
$\mathbf{s}$ orthogonal, so $\mathbf{O}_s\mathbf{S}$ has the law of $\mathbf{O}_s$
(`isRightUnitarilyInvariant_haarFrame`). Freezing with $T = \mathbf{X}$, $Z = \mathbf{O}$ shows
that $(\mathbf{X}\mathbf{V}, \mathbf{X}\mathbf{O}_s\mathbf{S}(\mathbf{X}\mathbf{V}))$ and
$(\mathbf{X}\mathbf{V}, \mathbf{X}\mathbf{O}_s)$ have the same law. (3) Pushing (1) forward by
the measurable $\Phi(\mathbf{Y}, \mathbf{Z}) = (\mathbf{Y}, \mathbf{Z}\mathbf{S}(\mathbf{Y}))$
(`IdentDistrib.comp`) and using $\mathbf{X}\mathbf{O}_s\mathbf{V} = \mathbf{X}\mathbf{V}$, the
pair $(\mathbf{X}\mathbf{V}, \mathbf{X}\mathbf{S}(\mathbf{X}\mathbf{V}))$ has the law of
$(\mathbf{X}\mathbf{V}, \mathbf{X}\mathbf{O}_s\mathbf{S}(\mathbf{X}\mathbf{V}))$; chain (3), (2),
(1). -/
theorem identDistrib_prodMk_mul_of_isRightUnitarilyInvariant [IsProbabilityMeasure μ]
    {p : Type*} {ν : Measure (Matrix m n ℝ)} [IsRightUnitarilyInvariant ν]
    {X : Ω → Matrix m n ℝ} (hX : HasLaw X ν μ) (V : Matrix n p ℝ)
    {S : Matrix m p ℝ → Matrix n n ℝ} (hSm : Measurable S) (hSo : ∀ Y, HasOrthonormalCols (S Y))
    (hSV : ∀ Y, S Y * V = V) :
    IdentDistrib (fun ω => (X ω * V, X ω)) (fun ω => (X ω * V, X ω * S (X ω * V))) μ μ := by
  sorry

/-- **Adaptive deferred decision for a unitarily invariant law, stabilizer form**: let the law
$\nu$ of $\mathbf{X} \in \mathbb{R}^{m \times n}$ be right unitarily invariant (Gaussian, Haar)
and $\tau$ the transcript of a measurable algorithm making `q` adaptive pair queries
$(\mathbf{w}, \mathbf{u})$ to `twoSidedMulVec X` (products $\mathbf{X}\mathbf{w}$ and
$\mathbf{X}^{\mathsf{H}}\mathbf{u}$). Let $\mathbf{S}(\tau)$ be an orthogonal matrix chosen
measurably from the transcript that fixes every vector of $\mathbb{R}^n$ the transcript reveals:
the right parts $\mathbf{w}_i$ of the queries (`QueryAlgorithm.rightQueryMatrix`) and the second
components $\mathbf{X}^{\mathsf{H}}\mathbf{u}_i$ of the responses. Then $(\tau, \mathbf{X})$ has
the law of $(\tau, \mathbf{X}\mathbf{S}(\tau))$; the rotated matrix gives the same transcript, by
`QueryAlgorithm.transcript_eq_of_forall_apply_queries_eq`.
[DerezinskiEpperlyMeyer2026, Theorem 3.1]; [Shamir2026, Lemma 4]; there for a Haar orthogonal
matrix with the oracles $\mathbf{x} \mapsto \mathbf{A}\mathbf{x}$,
$\mathbf{A}^{\mathsf{H}}\mathbf{x}$ and $(\mathbf{A}\mathbf{x}, \mathbf{U}^{\mathsf{H}}\mathbf{x})$,
each a two-sided query sequence to $\mathbf{U}$; here for every right unitarily invariant law.
The hypotheses quantify over every `τ`, also those no run produces; for a one-sided algorithm the
second components of actual transcripts vanish, and `S` may be anything off them that is
measurable and orthogonal.
Proof: H, about 300 lines, in six private lemmas; no transcript-dependent frames (their column
count would vary with the history). For a fixed $\mathbf{V} \in \mathbb{R}^{n \times c}$ let the
*stabilizer randomizer* be $\mathbf{R}_{\mathbf{V}}(\mathbf{G}) =
\operatorname{polar}(\mathbf{P}_{\mathbf{V}} + \mathbf{E}\mathbf{G}\mathbf{E})$,
$\mathbf{E} = \mathbf{I} - \mathbf{P}_{\mathbf{V}}$ (`rangeProjector`, `polarFactor`), with
$\mathbf{G}$ an independent `gaussianMatrix n n` (as `haarFrame` is the polar factor of a
Gaussian), set to `1` on the null set where it is not orthogonal.
(0) Almost surely $\mathbf{R}_{\mathbf{V}}(\mathbf{G})$ is orthogonal (`HasOrthonormalCols`)
and fixes $\mathbf{V}$ (block diagonal: identity on
the range of $\mathbf{V}$, an a.s. invertible block on its complement, through a frame of the
*fixed* $\mathbf{V}$); for every orthogonal $\mathbf{s}$ with $\mathbf{s}\mathbf{V} = \mathbf{V}$,
$\mathbf{R}_{\mathbf{V}}\mathbf{s} \overset{d}{=} \mathbf{R}_{\mathbf{V}} \overset{d}{=}
\mathbf{s}\mathbf{R}_{\mathbf{V}}$ ($\mathbf{s}$ commutes with $\mathbf{P}_{\mathbf{V}}$ and
$\mathbf{E}$; `polarFactor` equivariance; two-sided invariance of the Gaussian,
`hasLaw_mul_const_of_isRightUnitarilyInvariant` and its transpose).
(i′) One right query on the stabilizer: with $\mathbf{R} = \mathbf{R}_{\mathbf{V}}(\mathbf{G})$,
$(\mathbf{R}\mathbf{w}, \mathbf{R}) \overset{d}{=} (\mathbf{R}\mathbf{w},
\mathbf{R}\mathbf{s}(\mathbf{R}\mathbf{w}))$ for measurable $\mathbf{s}$ fixing $\mathbf{V}$ and
$\mathbf{w}$: right-multiply by the randomizer of $[\mathbf{V}\;\mathbf{w}]$ (an independent
copy, extend $\Omega$ by `Measure.prod`), freeze
(`ProbabilityTheory.IndepFun.identDistrib_prodMk_of_forall_map_eq`) and use (0), as in steps
(1)–(3) of `NLAlib.identDistrib_prodMk_mul_of_isRightUnitarilyInvariant`.
(i″) One left query on the stabilizer: $(\mathbf{R}^{\mathsf{H}}\mathbf{g}, \mathbf{R})
\overset{d}{=}
(\mathbf{R}^{\mathsf{H}}\mathbf{g}, \mathbf{R}\mathbf{s}(\mathbf{R}^{\mathsf{H}}\mathbf{g}))$
for $\mathbf{s}$ fixing $\mathbf{V}$ and $\mathbf{h}$ at $\mathbf{h}$: left-multiply by the
randomizer of $[\mathbf{V}\;\mathbf{g}]$ (it does not change
$\mathbf{R}^{\mathsf{H}}\mathbf{g}$), and for fixed $\mathbf{r}$,
$\mathbf{r}\mathbf{s}\mathbf{r}^{\mathsf{H}}$ fixes $[\mathbf{V}\;\mathbf{g}]$, so (0) applies.
(i‴) One pair round: $(\mathbf{R}\mathbf{w}, \mathbf{R}^{\mathsf{H}}\mathbf{g}, \mathbf{R})
\overset{d}{=} (\mathbf{R}\mathbf{w}, \mathbf{R}^{\mathsf{H}}\mathbf{g},
\mathbf{R}\mathbf{s}(\mathbf{R}\mathbf{w}, \mathbf{R}^{\mathsf{H}}\mathbf{g}))$: (i′), then for
frozen $\mathbf{R} = \mathbf{r}$ (i″) on the stabilizer of $[\mathbf{V}\;\mathbf{w}]$ with
the vector $\mathbf{r}^{\mathsf{H}}\mathbf{g}$, pushed forward by
$\mathbf{R}' \mapsto \mathbf{r}\mathbf{R}'$ (`IdentDistrib.comp`), chained.
(ii) Haar, adaptive, two-sided ($\mathbf{O}$ with law `haarFrame n n`): induction on the rounds
through `alg.truncate i` (`QueryAlgorithm.truncate`, `QueryAlgorithm.IsMeasurable.truncate`,
`QueryAlgorithm.transcript_truncate`), invariant: for every measurable $\mathbf{S}$ fixing the
vectors revealed by the length-`i` history $h_i$, $(h_i, \mathbf{O}) \overset{d}{=}
(h_i, \mathbf{O}\mathbf{S}(h_i))$. With $\mathbf{V}(h)$ the matrix of revealed vectors (right
query matrix and second response components side by side, `Matrix.fromCols`), the invariant and
freezing over $\mathbf{G}$ give $(h_i, \mathbf{O}) \overset{d}{=}
(h_i, \mathbf{O}\mathbf{R}_{\mathbf{V}(h_i)}(\mathbf{G}))$; push both sides through
$(h, \mathbf{O}) \mapsto (h, \text{next response}, \mathbf{O})$ and
$(h, \mathbf{O}) \mapsto (h, \text{next response}, \mathbf{O}\mathbf{S}(\cdot))$, freeze
$(h_i, \mathbf{O}) = (h, \mathbf{o})$ and apply (i‴) with $\mathbf{V} = \mathbf{V}(h)$,
$\mathbf{w}$ the next right part, $\mathbf{g} = \mathbf{o}^{\mathsf{H}}\mathbf{u}$,
$\mathbf{s}(a, b) = \mathbf{S}(h, (\mathbf{o}a, b))$, pushed forward by
$(a, b, \mathbf{R}) \mapsto (\mathbf{o}a, b, \mathbf{o}\mathbf{R})$.
(iii) General $\nu$. With $\mathbf{O}$ Haar independent of $\mathbf{X}$, $\mathbf{X}\mathbf{O}$
has law $\nu$ (`hasLaw_mul_const_of_isRightUnitarilyInvariant`, freezing $T = \mathbf{O}$), so
$(\tau, \mathbf{X}) \overset{d}{=} (\tau(\mathbf{X}\mathbf{O}), \mathbf{X}\mathbf{O})$. Freeze
$\mathbf{Y} = \mathbf{X}$: queries to $\mathbf{Y}\mathbf{O}$ are queries to $\mathbf{O}$ (right
part $\mathbf{w}$ answered by $\mathbf{O}\mathbf{w}$ and multiplied by $\mathbf{Y}$, left part
$\mathbf{u}$ sent as $\mathbf{Y}^{\mathsf{H}}\mathbf{u}$), with the same revealed vectors in
$\mathbb{R}^n$; apply (ii) to that algorithm and push forward by
$\mathbf{Z} \mapsto \mathbf{Y}\mathbf{Z}$. Throughout, the transcript of
$\mathbf{X}\mathbf{S}$ is that of $\mathbf{X}$
(`QueryAlgorithm.transcript_eq_of_forall_apply_queries_eq`:
$\mathbf{X}\mathbf{S}\mathbf{w} = \mathbf{X}\mathbf{w}$,
$\mathbf{S}^{\mathsf{H}}\mathbf{X}^{\mathsf{H}}\mathbf{u} = \mathbf{X}^{\mathsf{H}}\mathbf{u}$).
State (0), (i′), (i″), (i‴) as private lemmas first; escalate early if (ii) does not close. -/
theorem QueryAlgorithm.IsMeasurable.identDistrib_prodMk_mul_of_isRightUnitarilyInvariant
    [Fintype m] [IsProbabilityMeasure μ] {β : Type*} [MeasurableSpace β] {q : ℕ}
    {alg : QueryAlgorithm ((n → ℝ) × (m → ℝ)) ((m → ℝ) × (n → ℝ)) q β} (halg : alg.IsMeasurable)
    {ν : Measure (Matrix m n ℝ)} [IsRightUnitarilyInvariant ν] {X : Ω → Matrix m n ℝ}
    (hX : HasLaw X ν μ) {S : (Fin q → (m → ℝ) × (n → ℝ)) → Matrix n n ℝ} (hSm : Measurable S)
    (hSo : ∀ τ, HasOrthonormalCols (S τ))
    (hSq : ∀ τ, S τ * alg.rightQueryMatrix τ = alg.rightQueryMatrix τ)
    (hSr : ∀ τ, S τ * Matrix.of (fun r j => (τ j).2 r) = Matrix.of fun r j => (τ j).2 r) :
    IdentDistrib (fun ω => (alg.transcript (twoSidedMulVec (X ω)), X ω))
      (fun ω => (alg.transcript (twoSidedMulVec (X ω)),
        X ω * S (alg.transcript (twoSidedMulVec (X ω))))) μ μ := by
  sorry

end NLAlib
