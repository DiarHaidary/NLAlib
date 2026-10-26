/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowerBounds.QueryModel.HiddenRotation
public import NLAlib.LowerBounds.QueryModel.HiddenHaar
public import NLAlib.RandomMatrix.Gaussian.Invariance
public import NLAlibScaffold.Krylov.Basic.BlockSpace
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
    (D : Matrix n n ℝ) : Measurable fun a => hiddenRotationOracle (f a) D (v a) :=
  ((((hf.matrix_mul measurable_const).matrix_mul
    (Measurable.matrix_conjTranspose continuous_star.measurable hf)).matrix_mulVec hv).prodMk
    ((Measurable.matrix_conjTranspose continuous_star.measurable hf).matrix_mulVec hv))

namespace QueryAlgorithm

variable {𝕜 n β : Type*} [RCLike 𝕜] [Fintype n] {q : ℕ}

/-- Queries of an algorithm at equal indices, with the responses reindexed along the equality. -/
private theorem query_eq_of_index_hr {Q R : Type*} {q : ℕ} (alg : QueryAlgorithm Q R q β)
    {a b : ℕ} (hab : a = b) (F : Fin a → R) (G : Fin b → R)
    (hFG : ∀ m : Fin b, F (Fin.cast hab.symm m) = G m) : alg.query a F = alg.query b G := by
  subst hab
  congr 1
  funext m
  exact hFG m

/-- Entries of a history do not depend on the length of the history. -/
private theorem history_eq_history_hr {Q R : Type*} {q : ℕ} (alg : QueryAlgorithm Q R q β)
    (f : Q → R) {n m j : ℕ} (hn : j < n) (hm : j < m) :
    alg.history f n ⟨j, hn⟩ = alg.history f m ⟨j, hm⟩ := by
  rw [history_apply, history_apply]

/-- Even rounds of the hidden-rotation simulation are `(0, x)`. -/
private theorem hiddenRotationSimulation_query_even (alg : QueryAlgorithm (n → 𝕜)
    ((n → 𝕜) × (n → 𝕜)) q β) (D : Matrix n n 𝕜) (l : ℕ) (h : Fin (2 * l) → (n → 𝕜) × (n → 𝕜)) :
    (alg.hiddenRotationSimulation D).query (2 * l) h =
      (0, alg.query l (hiddenRotationDecode h)) := by
  simp only [hiddenRotationSimulation]
  rw [dif_pos (Nat.mul_mod_right 2 l)]
  congr 1
  exact query_eq_of_index_hr alg (Nat.mul_div_cancel_left l two_pos) _ _ fun m => rfl

/-- Odd rounds of the hidden-rotation simulation are `(D v, 0)`, with `v` the left response of the
round before. -/
private theorem hiddenRotationSimulation_query_odd (alg : QueryAlgorithm (n → 𝕜)
    ((n → 𝕜) × (n → 𝕜)) q β) (D : Matrix n n 𝕜) (l : ℕ)
    (h : Fin (2 * l + 1) → (n → 𝕜) × (n → 𝕜)) :
    (alg.hiddenRotationSimulation D).query (2 * l + 1) h = (D *ᵥ (h ⟨2 * l, by omega⟩).2, 0) := by
  simp only [hiddenRotationSimulation]
  rw [dif_neg (by omega)]
  rfl

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
  -- Round `2l + 1` returns `U * (D * (Uᴴ * x_l))`, and round `2l` returns `Uᴴ * x_l` second.
  have key : ∀ l : ℕ,
      ((alg.hiddenRotationSimulation D).history (twoSidedMulVec U) (2 * l + 2)
        ⟨2 * l + 1, by omega⟩).1 = (U * D * Uᴴ) *ᵥ alg.queryAt (hiddenRotationOracle U D) l ∧
      ((alg.hiddenRotationSimulation D).history (twoSidedMulVec U) (2 * l + 2)
        ⟨2 * l, by omega⟩).2 = Uᴴ *ᵥ alg.queryAt (hiddenRotationOracle U D) l := by
    intro l
    induction l using Nat.strong_induction_on with
    | _ l ih =>
    have e1 : ((alg.hiddenRotationSimulation D).history (twoSidedMulVec U) (2 * l + 2)
        ⟨2 * l + 1, by omega⟩).1
        = U *ᵥ (D *ᵥ ((alg.hiddenRotationSimulation D).history (twoSidedMulVec U) (2 * l + 1)
          ⟨2 * l, by omega⟩).2) := by
      rw [history_apply]
      simp only [queryAt, hiddenRotationSimulation_query_odd, twoSidedMulVec, Matrix.mulVec_zero]
    have e2 : ((alg.hiddenRotationSimulation D).history (twoSidedMulVec U) (2 * l + 1)
        ⟨2 * l, by omega⟩).2
        = Uᴴ *ᵥ alg.query l (hiddenRotationDecode
          ((alg.hiddenRotationSimulation D).history (twoSidedMulVec U) (2 * l))) := by
      rw [history_apply]
      simp only [queryAt, hiddenRotationSimulation_query_even, twoSidedMulVec, Matrix.mulVec_zero]
    have e3 : hiddenRotationDecode ((alg.hiddenRotationSimulation D).history
        (twoSidedMulVec U) (2 * l)) = alg.history (hiddenRotationOracle U D) l := by
      funext m
      unfold hiddenRotationDecode
      refine Prod.ext ?_ ?_
      · rw [history_eq_history_hr _ _ (n := 2 * l) (m := 2 * m.val + 2) (j := 2 * m.val + 1)
          (by omega) (by omega), (ih m m.isLt).1, history_apply]
        rfl
      · rw [history_eq_history_hr _ _ (n := 2 * l) (m := 2 * m.val + 2) (j := 2 * m.val)
          (by omega) (by omega), (ih m m.isLt).2, history_apply]
        rfl
    refine ⟨?_, ?_⟩
    · rw [e1, e2, e3, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      rfl
    · rw [history_eq_history_hr _ _ (n := 2 * l + 2) (m := 2 * l + 1) (j := 2 * l)
        (by omega) (by omega), e2, e3]
      rfl
  funext l
  obtain ⟨k1, k2⟩ := key l.val
  rw [history_apply]
  unfold hiddenRotationDecode
  refine Prod.ext ?_ ?_
  · rw [history_eq_history_hr _ _ (n := 2 * i) (m := 2 * l.val + 2) (j := 2 * l.val + 1)
      (by have := l.isLt; omega) (by omega), k1]
    rfl
  · rw [history_eq_history_hr _ _ (n := 2 * i) (m := 2 * l.val + 2) (j := 2 * l.val)
      (by have := l.isLt; omega) (by omega), k2]
    rfl

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
    (hs : s ≤ s') : IsKrylovCoupling μ D s' G₀ V G :=
  ⟨h.hasLaw_gaussianMatrix, h.indepFun,
    h.ae_range_le.mono fun _ hω => hω.trans (blockKrylovSpace_mono _ _ hs)⟩

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
Proof: OP5 (research note) Lemma C, with an augmented simulation. (1) *The augmented
algorithm* $\mathcal{A}^+$ (a private definition), $\lvert c \rvert + 3q + \lvert k \rvert$
two-sided rounds against `twoSidedMulVec U`: first the left rounds
$(\mathbf{0}, \mathbf{B}\mathbf{e}_a)$, which reveal $\mathbf{U}^{\mathsf{H}}\mathbf{B}$ (H2's
stabilizer must fix it, or $\mathbf{G}$ is not independent of it); then for each pass $j < p$, of
width $b_j$: the left rounds $(\mathbf{0}, \mathbf{x}_i)$ of all its queries (by
`QueryAlgorithm.IsPassStructured.query_eq` they depend only on earlier passes, so they are
computed before any product of the pass), $b_j$ dummy left rounds $(\mathbf{0}, \mathbf{q})$ for
the columns of a frame $\mathbf{Q}_j$, then the right rounds $(\mathbf{D}\mathbf{v}_i,
\mathbf{0})$; last the output block $\mathbf{W}$ as a pass of width $\lvert k \rvert$ with dummy
rounds and no right rounds. It decodes to `alg.run (hiddenRotationOracle U D)` (as
`QueryAlgorithm.run_hiddenRotationSimulation`) and is measurable (as
`QueryAlgorithm.IsMeasurable.hiddenRotationSimulation`). Let $\mathcal{L}_j$ be the span of the
vectors revealed before pass $j$ (H2's: right parts $\mathbf{D}\mathbf{v}_i$, second components
$\mathbf{U}^{\mathsf{H}}\mathbf{B}\mathbf{e}_a$, $\mathbf{v}_i$,
$\mathbf{U}^{\mathsf{H}}\mathbf{Q}_l$), $\mathbf{E}_j$ the projector onto
$\mathcal{L}_j^{\perp}$, $d_j = \operatorname{rank}\mathbf{E}_j$, $\mathbf{Z}_j$ the columns of
$\mathbf{Z}$ of pass $j$. (2) *The coupled block.* Tall pass, $b_j \le d_j$: $\mathbf{Q}_j$ is a
frame of width $b_j$ in $(\mathbf{U}\mathcal{L}_j)^{\perp}$, chosen measurably from the transcript
(the ambient $\mathbf{U}\mathcal{L}_j$ is spanned by $\mathbf{B}$, the queries, the products and
the earlier $\mathbf{Q}_l$), whose range contains the component of the query block orthogonal to
$\mathbf{U}\mathcal{L}_j$, and $\mathbf{G}_j := (\mathbf{I} - \mathbf{E}_j)\mathbf{Z}_j +
\mathbf{U}^{\mathsf{H}}\mathbf{Q}_j((\mathbf{E}_j\mathbf{Z}_j)^{\mathsf{H}}
\mathbf{E}_j\mathbf{Z}_j)^{1/2}$. The padding columns of $\mathbf{Q}_j$ must be revealed (the dummy
rounds): otherwise $\mathbf{G}_j$ depends on $\mathbf{U}$ off $\mathcal{L}_{j+1}$ and the next
pass's invariant fails. Wide pass, $b_j > d_j$: the dummy rounds are zero and
$\mathbf{G}_j := \mathbf{Z}_j$, whose compression $\mathbf{E}_j\mathbf{Z}_j$ has range
$\mathcal{L}_j^{\perp}$ a.s. (3) *Law*, by induction over the passes: $\mathbf{G}_j$ is standard
Gaussian and independent of the transcript before pass $j$ and $\mathbf{Z}_{<j}$ (which determine
$\mathbf{U}^{\mathsf{H}}\mathbf{B}$ and $\mathbf{G}_{<j}$). H2 in the randomized form
(`QueryAlgorithm.IsMeasurable.identDistrib_prodMk_mul_of_isRightUnitarilyInvariant_of_indepFun`)
for $\mathcal{A}^+$ truncated before pass $j$ (`QueryAlgorithm.truncate`), with the stabilizer
`NLAlib.stabRand` of the revealed vectors and a Gaussian $n \times n$ variable on a product
extension, shows that given the transcript $\mathbf{U}^{\mathsf{H}}\mathbf{Q}_j$ has the law of
$\operatorname{polar}(\mathbf{E}_j\mathbf{Z}')$ (`NLAlib.map_mul_right_stabRand`,
`NLAlib.stabRand_spec`, `NLAlib.eq_map_polarFactor_mul_of_forall_map_mul_left_eq`); then freeze the
transcript (`ProbabilityTheory.IndepFun.identDistrib_prodMk_of_forall_map_eq`) and apply
`NLAlib.hasLaw_one_sub_mul_add_mul_sqrt_of_hasLaw_gaussianMatrix`; in the wide case the law of
the column block $\mathbf{Z}_j$ suffices. The column blocks of $\mathbf{Z}$ are
independent (`NLAlib.iIndepFun_col_of_hasLaw_gaussianMatrix`). (4) *Depth*, a.s. ($\mathbf{U}$
orthogonal, `NLAlib.ae_hasOrthonormalCols_of_hasLaw_haarFrame`; $\mathbf{E}_j\mathbf{Z}_j$ of rank
$\min(b_j, d_j)$, `NLAlib.ae_rank_eq_min_of_hasLaw_gaussianMatrix` after freezing): with
$\mathcal{V}_j = \operatorname{range}[\mathbf{U}^{\mathsf{H}}\mathbf{X}_j,
\mathbf{U}^{\mathsf{H}}\mathbf{Q}_j] \le \mathcal{L}_j \sqcup \operatorname{range}\mathbf{G}_j$
and $\mathcal{L}_{j+1} \le \mathcal{L}_j \sqcup \mathcal{V}_j \sqcup \mathbf{D}\mathcal{V}_j$,
`NLAlib.sup_sup_map_mulVecLin_le_blockKrylovSpace_add_two` and
`NLAlib.blockKrylovSpace_le_of_range_le` give $\mathcal{L}_j \le
\mathcal{K}_{j+1}(\mathbf{D}, [\mathbf{U}^{\mathsf{H}}\mathbf{B}, \mathbf{G}])$; the output block
adds $\operatorname{range}\mathbf{G}_{\mathrm{out}}$ and no products, so depth $p + 1$. H, about
600 lines; private lemmas: the augmented algorithm and its decoding (M), the frame choice (M), the
law of one pass (L), the depth count (M), the assembly (M). -/
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
