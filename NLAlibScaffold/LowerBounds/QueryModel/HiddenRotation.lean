/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowerBounds.QueryModel.HiddenRotation
public import NLAlib.LowerBounds.QueryModel.HiddenHaar
public import NLAlib.RandomMatrix.Gaussian.Invariance
public import NLAlibScaffold.LowerBounds.QueryModel.Basic
public import NLAlibScaffold.RandomMatrix.Haar.Uniqueness

/-!
# The Krylov coupling of the hidden-rotation oracle (scaffold)

Statements for `NLAlib/LowerBounds/QueryModel/HiddenRotation.lean` (stage LB-C1, design note
`docs/design/LowerBounds-HiddenRotationLowerBounds.md` §3.2). The headline is the **Krylov
coupling theorem**: for $\mathbf{A} = \mathbf{U}\mathbf{D}\mathbf{U}^{\mathsf{H}}$ with
$\mathbf{U}$ Haar and $\mathbf{D}$ fixed, a $p$-pass algorithm with $q$ queries to the oracle
$\mathbf{x} \mapsto (\mathbf{A}\mathbf{x}, \mathbf{U}^{\mathsf{H}}\mathbf{x})$ and an
$n \times k$ output $\mathbf{W}$ has a Krylov coupling at depth $p + 1$: almost surely
$$\operatorname{range}(\mathbf{U}^{\mathsf{H}}\mathbf{W}) \subseteq
\mathcal{K}_{p+1}(\mathbf{D}, [\mathbf{U}^{\mathsf{H}}\mathbf{B}, \mathbf{G}])$$
with $\mathbf{G}$ a standard Gaussian $n \times (q + k)$ matrix independent of
$\mathbf{U}^{\mathsf{H}}\mathbf{B}$, for any fixed initial block $\mathbf{B}$ (the right-hand
side of a linear system). The fully adaptive case (one query per pass) is [Shamir2026, Lemma 4].

## Main results

* `NLAlib.Measurable.hiddenRotationOracle`.
* `NLAlib.QueryAlgorithm.hiddenRotationDecode_history_hiddenRotationSimulation`,
  `NLAlib.QueryAlgorithm.run_hiddenRotationSimulation`,
  `NLAlib.QueryAlgorithm.IsMeasurable.hiddenRotationSimulation`.
* `NLAlib.IsKrylovCoupling.mono`, `NLAlib.IsKrylovCoupling.ae_range_le_of_isEmpty`.
* `NLAlib.QueryAlgorithm.IsPassStructured.exists_isKrylovCoupling_of_hasLaw_haarFrame`: the
  coupling theorem.
* `NLAlib.QueryAlgorithm.IsPassStructured.exists_isKrylovCoupling_mulVec_of_hasLaw_haarFrame`:
  the same for the matrix–vector oracle.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

/-- The hidden-rotation oracle is jointly measurable in the rotation and the query.
Proof: both components are matrix–vector products of measurable maps; as
`NLAlib.Measurable.twoSidedMulVec` (`Measurable.matrix_mul`, `Measurable.matrix_conjTranspose`,
`Measurable.matrix_mulVec`, `Measurable.prodMk`). S, 3 lines. -/
@[fun_prop]
theorem Measurable.hiddenRotationOracle {α n : Type*} [MeasurableSpace α] [Fintype n]
    {f : α → Matrix n n ℝ} {v : α → n → ℝ} (hf : Measurable f) (hv : Measurable v)
    (D : Matrix n n ℝ) : Measurable fun a => hiddenRotationOracle (f a) D (v a) := by
  sorry

namespace QueryAlgorithm

variable {𝕜 n β : Type*} [RCLike 𝕜] [Fintype n] {q : ℕ}

/-- The hidden-rotation simulation reproduces the history: after `2 * i` rounds of
`alg.hiddenRotationSimulation D` against `twoSidedMulVec U`, the decoded responses are the first
`i` responses of `alg` against `hiddenRotationOracle U D`. Holds for every `i`.
Proof: as `NLAlib.QueryAlgorithm.gramDecode_history_gramSimulation`: strong induction on the
round; round `2l` returns $(\mathbf{0}, \mathbf{U}^{\mathsf{H}}\mathbf{x}_l)$ and round `2l + 1`
returns $(\mathbf{U}\mathbf{D}\mathbf{U}^{\mathsf{H}}\mathbf{x}_l, \mathbf{0})$
(`QueryAlgorithm.history_apply`, `Matrix.mulVec_mulVec`, `Matrix.mulVec_zero`). M, about 40 lines
(copy the parity bookkeeping of the Gram simulation). -/
theorem hiddenRotationDecode_history_hiddenRotationSimulation
    (alg : QueryAlgorithm (n → 𝕜) ((n → 𝕜) × (n → 𝕜)) q β) (U D : Matrix n n 𝕜) (i : ℕ) :
    hiddenRotationDecode ((alg.hiddenRotationSimulation D).history (twoSidedMulVec U) (2 * i)) =
      alg.history (hiddenRotationOracle U D) i := by
  sorry

/-- **The hidden-rotation simulation runs the original algorithm**: the `2q`-round algorithm
`alg.hiddenRotationSimulation D` against `twoSidedMulVec U` outputs what `alg` outputs against
`hiddenRotationOracle U D`. So the transcript of an algorithm against the hidden-rotation oracle
reveals $\mathbf{U}$ only through two-sided products, and the stabilizer form of deferred
decision applies to it.
[Shamir2026, Section 3.2]; there implicit, the responses $\mathbf{U}^{\mathsf{T}}\mathbf{x}_t$,
$\mathbf{U}\mathbf{D}\mathbf{v}_t$ reveal $\mathbf{U}$ on $\mathbf{v}_t$, $\mathbf{D}\mathbf{v}_t$.
Proof: unfold `QueryAlgorithm.run`, `QueryAlgorithm.transcript`; congruence of `alg.output` with
`QueryAlgorithm.hiddenRotationDecode_history_hiddenRotationSimulation` at `i = q`. S, 2 lines. -/
theorem run_hiddenRotationSimulation (alg : QueryAlgorithm (n → 𝕜) ((n → 𝕜) × (n → 𝕜)) q β)
    (U D : Matrix n n 𝕜) :
    (alg.hiddenRotationSimulation D).run (twoSidedMulVec U) =
      alg.run (hiddenRotationOracle U D) := by
  sorry

/-- The hidden-rotation simulation of a measurable algorithm is measurable.
Proof: as `NLAlib.QueryAlgorithm.IsMeasurable.gramSimulation`, split on the parity of the round;
the odd rounds apply the continuous map $\mathbf{y} \mapsto \mathbf{D}\mathbf{y}$
(`Continuous.measurable`, `measurable_pi_apply`, `measurable_snd`). S, 10 lines. -/
theorem IsMeasurable.hiddenRotationSimulation {β : Type*} [MeasurableSpace β]
    {alg : QueryAlgorithm (n → ℝ) ((n → ℝ) × (n → ℝ)) q β} (halg : alg.IsMeasurable)
    (D : Matrix n n ℝ) : (alg.hiddenRotationSimulation D).IsMeasurable := by
  sorry

end QueryAlgorithm

section Coupling

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n c k c' : Type*} [Fintype n]
  [DecidableEq n] [Fintype c] [Fintype k] [Fintype c']

/-- A Krylov coupling at depth $s$ is one at every larger depth.
Proof: the fields `IsKrylovCoupling.hasLaw_gaussianMatrix`, `IsKrylovCoupling.indepFun` carry
over; `IsKrylovCoupling.ae_range_le` composes with `NLAlib.blockKrylovSpace_mono`
(`Filter.Eventually.mono`, `le_trans`). S, 4 lines. -/
theorem IsKrylovCoupling.mono {D : Matrix n n ℝ} {s s' : ℕ} {G₀ : Ω → Matrix n c ℝ}
    {V : Ω → Matrix n k ℝ} {G : Ω → Matrix n c' ℝ} (h : IsKrylovCoupling μ D s G₀ V G)
    (hs : s ≤ s') : IsKrylovCoupling μ D s' G₀ V G := by
  sorry

/-- With no initial block the Krylov space is that of the Gaussian block alone: almost surely
$\operatorname{range}(\mathbf{V}) \subseteq \mathcal{K}_s(\mathbf{D}, \mathbf{G})$.
Proof: for `c` empty, `Matrix.fromCols (G₀ ω) (G ω)` is `G ω` reindexed by the equivalence
`Equiv.emptySum`; block Krylov spaces only depend on the range of the columns
(`NLAlib.blockKrylovSpace_eq_iSup_krylovSpace`, the column-reindexing is `iSup` over an
equivalent index, `Equiv.iSup_comp`). S, 8 lines. -/
theorem IsKrylovCoupling.ae_range_le_of_isEmpty [IsEmpty c] {D : Matrix n n ℝ} {s : ℕ}
    {G₀ : Ω → Matrix n c ℝ} {V : Ω → Matrix n k ℝ} {G : Ω → Matrix n c' ℝ}
    (h : IsKrylovCoupling μ D s G₀ V G) :
    ∀ᵐ ω ∂μ, LinearMap.range (V ω).mulVecLin ≤ blockKrylovSpace D (G ω) s := by
  sorry

/-- **Krylov coupling of a pass-structured algorithm against a hidden rotation**: let
$\mathbf{U}$ be Haar on the orthogonal $n \times n$ matrices, $\mathbf{D} \in \mathbb{R}^{n \times
n}$ and $\mathbf{B} \in \mathbb{R}^{n \times c}$ fixed, and let a measurable algorithm make $q$
queries in at most $p$ passes (`QueryAlgorithm.IsPassStructured`, every pass index below $p$) to
the oracle $\mathbf{x} \mapsto (\mathbf{A}\mathbf{x}, \mathbf{U}^{\mathsf{H}}\mathbf{x})$,
$\mathbf{A} = \mathbf{U}\mathbf{D}\mathbf{U}^{\mathsf{H}}$, and output
$\mathbf{W} \in \mathbb{R}^{n \times k}$. If the probability space carries a standard Gaussian
$n \times (q + k)$ matrix $\mathbf{Z}$ independent of $\mathbf{U}$, there is a standard Gaussian
$n \times (q + k)$ matrix $\mathbf{G}$, independent of $\mathbf{U}^{\mathsf{H}}\mathbf{B}$, with
almost surely
$$\operatorname{range}(\mathbf{U}^{\mathsf{H}}\mathbf{W}) \subseteq
\mathcal{K}_{p+1}(\mathbf{D}, [\mathbf{U}^{\mathsf{H}}\mathbf{B}, \mathbf{G}]) \,:$$
a Krylov coupling at depth $p + 1$ (`IsKrylovCoupling`). One Gaussian column per query and per
output column; the algorithm need not know $\mathbf{B}$, which only fixes what is conditioned on.
[Shamir2026, Lemma 4]; there for one query per pass ($p = q$, `QueryAlgorithm.isPassStructured_id`),
a vector output that is the last query, $\mathbf{B} = \mathbf{b}$ Gaussian, and the conclusion
$\mathbf{D}\mathbf{v}_t \in \operatorname{span}\{\mathbf{D}^j\mathbf{g}_i : i \le t,
1 \le j \le t\}$; here blocks of queries per pass, a matrix output as one more block, any fixed
initial block, and the depth counted in passes.
Proof: the transcript is that of `QueryAlgorithm.hiddenRotationSimulation` against
`twoSidedMulVec U` (`QueryAlgorithm.run_hiddenRotationSimulation`). Induct over the passes
$j \le p$ with the revealed subspace $\mathcal{L}_j$ (spanned by $\mathbf{U}^{\mathsf{H}}
\mathbf{B}$, the coupled blocks $\mathbf{G}_1, \dots, \mathbf{G}_j$ and $\mathbf{D}\mathbf{V}_i$
for the rotated query blocks $\mathbf{V}_i = \mathbf{U}^{\mathsf{H}}\mathbf{X}_i$, $i \le j$), and
the invariant: $\mathcal{L}_j \subseteq \mathcal{K}_{j+1}(\mathbf{D}, [\mathbf{U}^{\mathsf{H}}
\mathbf{B}, \mathbf{G}_{\le j}])$, $\mathbf{G}_{\le j}$ is Gaussian independent of
$\mathbf{U}^{\mathsf{H}}\mathbf{B}$, and given the history the restriction of $\mathbf{U}$ to
$\mathcal{L}_j^{\perp}$ is Haar (the randomized stabilizer form
`QueryAlgorithm.IsMeasurable.identDistrib_prodMk_mul_of_isRightUnitarilyInvariant_of_indepFun`
for the truncated simulation, `QueryAlgorithm.truncate`). Step: the block $\mathbf{X}_{j+1}$ is a
function of the history (`QueryAlgorithm.IsPassStructured.query_eq`); split it along
$\mathbf{U}\mathcal{L}_j$, choose measurably a frame $\mathbf{E}$ of width $b_{j+1}$ in
$(\mathbf{U}\mathcal{L}_j)^{\perp}$ containing the range of the orthogonal part, and set
$\mathbf{G}_{j+1} = \mathbf{P}\mathbf{Z}_{j+1} + \mathbf{U}^{\mathsf{H}}\mathbf{E}\,
\mathbf{R}(\mathbf{Z}_{j+1})$, with $\mathbf{P}$ the projector onto $\mathcal{L}_j$ and
$\mathbf{R}$ the radial factor of $(\mathbf{I} - \mathbf{P})\mathbf{Z}_{j+1}$; then
$\mathbf{V}_{j+1} \subseteq \mathcal{L}_j + \operatorname{range}\mathbf{G}_{j+1}$, and
$\mathbf{G}_{j+1}$ is Gaussian given the history because $\mathbf{U}^{\mathsf{H}}\mathbf{E}$ is a
Haar frame of $\mathcal{L}_j^{\perp}$ independent of $\mathbf{Z}$
(`NLAlib.hasLaw_mul_mul_of_hasLaw_gaussianMatrix`,
`NLAlib.hasLaw_polarFactor_of_hasLaw_gaussianMatrix`,
`NLAlib.indepFun_polarFactor_conjTranspose_mul_self_of_hasLaw_gaussianMatrix`,
the freezing lemma `ProbabilityTheory.IndepFun.identDistrib_prodMk_of_forall_map_eq`). The output
is one more block with no response. Depth: $\mathcal{L}_{j+1} \subseteq \mathcal{L}_j +
\operatorname{range}\mathbf{G}_{j+1} + \mathbf{D}(\mathcal{L}_j +
\operatorname{range}\mathbf{G}_{j+1})$ (`NLAlib.mulVec_mem_blockKrylovSpace_succ`,
`NLAlib.blockKrylovSpace_mono`). H, several hundred lines; split into private lemmas: the one-pass
step (L), the deterministic depth count (M), the induction (L). -/
theorem QueryAlgorithm.IsPassStructured.exists_isKrylovCoupling_of_hasLaw_haarFrame {q p : ℕ}
    {alg : QueryAlgorithm (n → ℝ) ((n → ℝ) × (n → ℝ)) q (Matrix n k ℝ)} {pass : ℕ → ℕ}
    (hpass : alg.IsPassStructured pass) (hp : ∀ i < q, pass i < p) (halg : alg.IsMeasurable)
    (D : Matrix n n ℝ) (B : Matrix n c ℝ) {U : Ω → Matrix n n ℝ}
    (hU : HasLaw U (haarFrame n n) μ) {Z : Ω → Matrix n (Fin q ⊕ k) ℝ}
    (hZ : HasLaw Z (gaussianMatrix n (Fin q ⊕ k)) μ) (hUZ : IndepFun U Z μ) :
    ∃ G : Ω → Matrix n (Fin q ⊕ k) ℝ, IsKrylovCoupling μ D (p + 1) (fun ω => (U ω)ᴴ * B)
      (fun ω => (U ω)ᴴ * alg.run (hiddenRotationOracle (U ω) D)) G := by
  sorry

/-- **Krylov coupling for the matrix–vector oracle**: the coupling theorem
`QueryAlgorithm.IsPassStructured.exists_isKrylovCoupling_of_hasLaw_haarFrame` for an algorithm
that sees only the products $\mathbf{A}\mathbf{x}$, $\mathbf{A} =
\mathbf{U}\mathbf{D}\mathbf{U}^{\mathsf{H}}$ with $\mathbf{U}$ Haar: with $\mathbf{Z}$ a standard
Gaussian $n \times (q + k)$ matrix independent of $\mathbf{U}$, there is a standard Gaussian
$\mathbf{G}$ independent of $\mathbf{U}^{\mathsf{H}}\mathbf{B}$ with almost surely
$\operatorname{range}(\mathbf{U}^{\mathsf{H}}\mathbf{W}) \subseteq
\mathcal{K}_{p+1}(\mathbf{D}, [\mathbf{U}^{\mathsf{H}}\mathbf{B}, \mathbf{G}])$ for the output
$\mathbf{W}$ of a measurable $p$-pass algorithm with $q$ queries.
[Shamir2026, Theorem 1]; the matrix–vector oracle is weaker than the oracle used there.
Proof: apply the coupling theorem to `alg.comapResponse Prod.fst`
(`QueryAlgorithm.IsPassStructured.comapResponse`, `QueryAlgorithm.IsMeasurable.comapResponse`
with `measurable_fst`) and rewrite its output with `QueryAlgorithm.run_comapResponse`; the first
component of `hiddenRotationOracle` is the product. S, 6 lines. -/
theorem QueryAlgorithm.IsPassStructured.exists_isKrylovCoupling_mulVec_of_hasLaw_haarFrame
    {q p : ℕ} {alg : QueryAlgorithm (n → ℝ) (n → ℝ) q (Matrix n k ℝ)} {pass : ℕ → ℕ}
    (hpass : alg.IsPassStructured pass) (hp : ∀ i < q, pass i < p) (halg : alg.IsMeasurable)
    (D : Matrix n n ℝ) (B : Matrix n c ℝ) {U : Ω → Matrix n n ℝ}
    (hU : HasLaw U (haarFrame n n) μ) {Z : Ω → Matrix n (Fin q ⊕ k) ℝ}
    (hZ : HasLaw Z (gaussianMatrix n (Fin q ⊕ k)) μ) (hUZ : IndepFun U Z μ) :
    ∃ G : Ω → Matrix n (Fin q ⊕ k) ℝ, IsKrylovCoupling μ D (p + 1) (fun ω => (U ω)ᴴ * B)
      (fun ω => (U ω)ᴴ * alg.run (U ω * D * (U ω)ᴴ).mulVec) G := by
  sorry

end Coupling

end NLAlib
