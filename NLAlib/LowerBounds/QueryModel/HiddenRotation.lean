/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Probability.Independence.Basic
public import NLAlib.Krylov.Basic.BlockSpace
public import NLAlib.LowerBounds.QueryModel.Basic
public import NLAlib.LowerBounds.QueryModel.HiddenHaar
public import NLAlib.RandomMatrix.Gaussian.Basic
public import NLAlib.RandomMatrix.Gaussian.Invariance
public import NLAlib.RandomMatrix.Haar.Uniqueness

/-!
# The hidden-rotation oracle and Krylov couplings

The hard instances of the matrix–vector lower bounds for linear systems, low-rank approximation
and matrix functions are $\mathbf{A} = \mathbf{U}\mathbf{D}\mathbf{U}^{\mathsf{H}}$ with a fixed
$\mathbf{D}$ and a Haar orthogonal $\mathbf{U}$. The lower bounds hold even for the stronger
oracle $\mathbf{x} \mapsto (\mathbf{A}\mathbf{x}, \mathbf{U}^{\mathsf{H}}\mathbf{x})$
([Shamir2026, Section 2]), `hiddenRotationOracle U D`, which reveals the rotated query
$\mathbf{v} = \mathbf{U}^{\mathsf{H}}\mathbf{x}$ besides the product. Its responses are two-sided
queries to $\mathbf{U}$, $(\mathbf{0}, \mathbf{x}) \mapsto \mathbf{U}^{\mathsf{H}}\mathbf{x}$ and
then $(\mathbf{D}\mathbf{v}, \mathbf{0}) \mapsto \mathbf{U}\mathbf{D}\mathbf{v}$, so an algorithm
against it runs as the algorithm `QueryAlgorithm.hiddenRotationSimulation D alg` against
`twoSidedMulVec U`, to which the stabilizer form of deferred decision applies
(`NLAlib.QueryAlgorithm.IsMeasurable.identDistrib_prodMk_mul_of_isRightUnitarilyInvariant`).

A **Krylov coupling** (`IsKrylovCoupling`) is the conclusion of the coupling theorem (in the
scaffold): after $p$ passes, the rotated output $\mathbf{U}^{\mathsf{H}}\mathbf{W}$ of the
algorithm lies in the block Krylov space
$\mathcal{K}_{p+1}(\mathbf{D}, [\mathbf{U}^{\mathsf{H}}\mathbf{B}, \mathbf{G}])$ of $\mathbf{D}$,
for a standard Gaussian $\mathbf{G}$ with one column per query and per output column, independent
of the rotated initial data $\mathbf{U}^{\mathsf{H}}\mathbf{B}$. Design note
`docs/design/LowerBounds-HiddenRotationLowerBounds.md`.

## Main definitions

* `NLAlib.hiddenRotationOracle`: $\mathbf{x} \mapsto (\mathbf{U}\mathbf{D}\mathbf{U}^{\mathsf{H}}
  \mathbf{x}, \mathbf{U}^{\mathsf{H}}\mathbf{x})$.
* `NLAlib.QueryAlgorithm.hiddenRotationSimulation`, `NLAlib.QueryAlgorithm.hiddenRotationDecode`:
  the `2q`-round two-sided algorithm against $\mathbf{U}$ that runs a `q`-query algorithm against
  the hidden-rotation oracle, and the decoding of its history.
* `NLAlib.IsKrylovCoupling`: a Gaussian block Krylov coupling of a rotated output.

## Main results

* `NLAlib.Measurable.hiddenRotationOracle`.
* `NLAlib.QueryAlgorithm.hiddenRotationDecode_history_hiddenRotationSimulation`,
  `NLAlib.QueryAlgorithm.run_hiddenRotationSimulation`,
  `NLAlib.QueryAlgorithm.IsMeasurable.hiddenRotationSimulation`.
* `NLAlib.IsKrylovCoupling.mono`, `NLAlib.IsKrylovCoupling.ae_range_le_of_isEmpty`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

/-- The **hidden-rotation oracle** of $\mathbf{A} = \mathbf{U}\mathbf{D}\mathbf{U}^{\mathsf{H}}$:
the query $\mathbf{x}$ returns $(\mathbf{A}\mathbf{x}, \mathbf{U}^{\mathsf{H}}\mathbf{x})$, the
product and the query in the hidden coordinates. It is stronger than the matrix–vector oracle,
which is its first component (`QueryAlgorithm.comapResponse Prod.fst`). [Shamir2026, Theorem 1],
the oracle (2) there. -/
def hiddenRotationOracle {𝕜 n : Type*} [Fintype n] [NonUnitalNonAssocSemiring 𝕜] [Star 𝕜]
    (U D : Matrix n n 𝕜) (x : n → 𝕜) : (n → 𝕜) × (n → 𝕜) :=
  ((U * D * Uᴴ) *ᵥ x, Uᴴ *ᵥ x)

namespace QueryAlgorithm

variable {𝕜 n β : Type*} {q : ℕ}

/-- The decoding of the hidden-rotation simulation: from a history of `2 * i` two-sided rounds,
the responses $(\mathbf{A}\mathbf{x}_l, \mathbf{U}^{\mathsf{H}}\mathbf{x}_l)$ of the simulated
algorithm, the first component of the odd round and the second of the even round before it. -/
def hiddenRotationDecode {i : ℕ} (h : Fin (2 * i) → (n → 𝕜) × (n → 𝕜)) :
    Fin i → (n → 𝕜) × (n → 𝕜) :=
  fun l => ((h ⟨2 * l + 1, by have := l.isLt; omega⟩).1, (h ⟨2 * l, by have := l.isLt; omega⟩).2)

/-- The **hidden-rotation simulation**: from an algorithm with `q` queries to
`hiddenRotationOracle U D`, an algorithm with `2q` rounds against `twoSidedMulVec U` with the
same output. Round `2l` is the left query $(\mathbf{0}, \mathbf{x}_l)$, which returns
$\mathbf{v}_l = \mathbf{U}^{\mathsf{H}}\mathbf{x}_l$ in the second component; round `2l + 1` is
the right query $(\mathbf{D}\mathbf{v}_l, \mathbf{0})$, which returns
$\mathbf{U}\mathbf{D}\mathbf{v}_l = \mathbf{A}\mathbf{x}_l$ in the first. What the transcript
reveals about $\mathbf{U}$ is its action on the vectors $\mathbf{v}_l$, $\mathbf{D}\mathbf{v}_l$.
With $\mathbf{D} = \mathbf{I}$ the rounds are those of `QueryAlgorithm.gramSimulation`. -/
def hiddenRotationSimulation [Fintype n] [NonUnitalNonAssocSemiring 𝕜] (D : Matrix n n 𝕜)
    (alg : QueryAlgorithm (n → 𝕜) ((n → 𝕜) × (n → 𝕜)) q β) :
    QueryAlgorithm ((n → 𝕜) × (n → 𝕜)) ((n → 𝕜) × (n → 𝕜)) (2 * q) β where
  query j h :=
    if hj : j % 2 = 0 then
      (0, alg.query (j / 2) (hiddenRotationDecode (h ∘ Fin.castLE (by omega))))
    else
      (D *ᵥ (h ⟨j - 1, by omega⟩).2, 0)
  output h := alg.output (hiddenRotationDecode h)

end QueryAlgorithm

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- A **Krylov coupling** at depth $s$ of a random $n \times k$ matrix $\mathbf{V}$ with initial
block $\mathbf{G}_0$ ($n \times c$) and $\mathbf{D} \in \mathbb{R}^{n \times n}$: a standard
Gaussian $n \times c'$ matrix $\mathbf{G}$, independent of $\mathbf{G}_0$, such that almost
surely the range of $\mathbf{V}$ lies in the block Krylov space
$$\mathcal{K}_s(\mathbf{D}, [\mathbf{G}_0, \mathbf{G}]) = \operatorname{range}[\mathbf{G}_0,
\mathbf{G}, \mathbf{D}\mathbf{G}_0, \mathbf{D}\mathbf{G}, \dots, \mathbf{D}^{s-1}\mathbf{G}_0,
\mathbf{D}^{s-1}\mathbf{G}] \,.$$
So every column of $\mathbf{V}$ is $\sum_j f_j(\mathbf{D})\mathbf{g}_j$ over the columns
$\mathbf{g}_j$ of $[\mathbf{G}_0, \mathbf{G}]$, with polynomials of degree less than $s$. The
coupling theorem (in the scaffold) gives one for the rotated output
$\mathbf{V} = \mathbf{U}^{\mathsf{H}}\mathbf{W}$ of a $p$-pass algorithm against
`hiddenRotationOracle U D` at depth $p + 1$, with
$\mathbf{G}_0 = \mathbf{U}^{\mathsf{H}}\mathbf{B}$; lower bounds take it as their hypothesis and
need no query model. -/
structure IsKrylovCoupling (μ : Measure Ω) {n c k c' : Type*} [Fintype n] [DecidableEq n]
    [Fintype c] [Fintype k] [Fintype c'] (D : Matrix n n ℝ) (s : ℕ) (G₀ : Ω → Matrix n c ℝ)
    (V : Ω → Matrix n k ℝ) (G : Ω → Matrix n c' ℝ) : Prop where
  /-- The coupled block is a standard Gaussian matrix. -/
  hasLaw_gaussianMatrix : HasLaw G (gaussianMatrix n c') μ
  /-- It is independent of the initial block. -/
  indepFun : IndepFun G₀ G μ
  /-- Almost surely the range of `V` lies in the block Krylov space of `[G₀, G]`. -/
  ae_range_le : ∀ᵐ ω ∂μ, LinearMap.range (V ω).mulVecLin ≤
    blockKrylovSpace D (Matrix.fromCols (G₀ ω) (G ω)) s

end NLAlib

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

/-- The hidden-rotation oracle is jointly measurable in the rotation and the query. -/
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
`i` responses of `alg` against `hiddenRotationOracle U D`. Holds for every `i`. -/
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
$\mathbf{U}\mathbf{D}\mathbf{v}_t$ reveal $\mathbf{U}$ on $\mathbf{v}_t$,
$\mathbf{D}\mathbf{v}_t$. -/
theorem run_hiddenRotationSimulation (alg : QueryAlgorithm (n → 𝕜) ((n → 𝕜) × (n → 𝕜)) q β)
    (U D : Matrix n n 𝕜) :
    (alg.hiddenRotationSimulation D).run (twoSidedMulVec U) =
      alg.run (hiddenRotationOracle U D) := by
  unfold QueryAlgorithm.run QueryAlgorithm.transcript
  exact congrArg alg.output (hiddenRotationDecode_history_hiddenRotationSimulation alg U D q)

/-- The hidden-rotation simulation of a measurable algorithm is measurable. -/
theorem IsMeasurable.hiddenRotationSimulation {β : Type*} [MeasurableSpace β]
    {alg : QueryAlgorithm (n → ℝ) ((n → ℝ) × (n → ℝ)) q β} (halg : alg.IsMeasurable)
    (D : Matrix n n ℝ) : (alg.hiddenRotationSimulation D).IsMeasurable := by
  refine ⟨fun j hj => ?_, ?_⟩
  · unfold QueryAlgorithm.hiddenRotationSimulation
    by_cases hjm : j % 2 = 0
    · simp only [hjm, dite_true]
      refine measurable_const.prodMk ((halg.measurable_query (j / 2) (by omega)).comp ?_)
      exact measurable_pi_iff.2 fun l => (measurable_fst.comp (measurable_pi_apply _)).prodMk
        (measurable_snd.comp (measurable_pi_apply _))
    · simp only [hjm, dite_false]
      exact ((continuous_const.matrix_mulVec continuous_id).measurable.comp
        (measurable_snd.comp (measurable_pi_apply _))).prodMk measurable_const
  · refine halg.measurable_output.comp ?_
    exact measurable_pi_iff.2 fun l => (measurable_fst.comp (measurable_pi_apply _)).prodMk
      (measurable_snd.comp (measurable_pi_apply _))

end QueryAlgorithm

section Coupling

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n c k c' : Type*} [Fintype n]
  [DecidableEq n] [Fintype c] [Fintype k] [Fintype c']

/-- A Krylov coupling at depth $s$ is one at every larger depth. -/
theorem IsKrylovCoupling.mono {D : Matrix n n ℝ} {s s' : ℕ} {G₀ : Ω → Matrix n c ℝ}
    {V : Ω → Matrix n k ℝ} {G : Ω → Matrix n c' ℝ} (h : IsKrylovCoupling μ D s G₀ V G)
    (hs : s ≤ s') : IsKrylovCoupling μ D s' G₀ V G :=
  ⟨h.hasLaw_gaussianMatrix, h.indepFun,
    h.ae_range_le.mono fun _ hω => hω.trans (blockKrylovSpace_mono _ _ hs)⟩

/-- With no initial block the Krylov space is that of the Gaussian block alone: almost surely
$\operatorname{range}(\mathbf{V}) \subseteq \mathcal{K}_s(\mathbf{D}, \mathbf{G})$. -/
theorem IsKrylovCoupling.ae_range_le_of_isEmpty [IsEmpty c] {D : Matrix n n ℝ} {s : ℕ}
    {G₀ : Ω → Matrix n c ℝ} {V : Ω → Matrix n k ℝ} {G : Ω → Matrix n c' ℝ}
    (h : IsKrylovCoupling μ D s G₀ V G) :
    ∀ᵐ ω ∂μ, LinearMap.range (V ω).mulVecLin ≤ blockKrylovSpace D (G ω) s := by
  refine h.ae_range_le.mono fun ω hω => hω.trans (le_of_eq ?_)
  simp only [blockKrylovSpace_eq_iSup_krylovSpace, iSup_sum, iSup_of_empty, bot_sup_eq]
  rfl

end Coupling

end NLAlib
