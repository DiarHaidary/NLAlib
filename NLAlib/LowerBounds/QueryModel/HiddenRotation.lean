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
public import NLAlib.LowerBounds.QueryModel.GaussianCoupling
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

A **Krylov coupling** (`IsKrylovCoupling`) is the conclusion of the coupling theorem: after $p$
passes, the rotated output $\mathbf{U}^{\mathsf{H}}\mathbf{W}$ of the
algorithm lies in the block Krylov space
$\mathcal{K}_{p+1}(\mathbf{D}, [\mathbf{U}^{\mathsf{H}}\mathbf{B}, \mathbf{G}])$ of $\mathbf{D}$,
for a standard Gaussian $\mathbf{G}$ with one column per query and per output column, independent
of the rotated initial data $\mathbf{U}^{\mathsf{H}}\mathbf{B}$.

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
* `NLAlib.QueryAlgorithm.IsPassStructured.exists_isKrylovCoupling_of_hasLaw_haarFrame`:
  the passwise coupling for the hidden-rotation oracle.
* `NLAlib.QueryAlgorithm.IsPassStructured.exists_isKrylovCoupling_mulVec_of_hasLaw_haarFrame`:
  the coupling for the matrix–vector oracle.
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
coupling theorem gives one for the rotated output
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


/-- Read an unavailable response as zero; this lets a pass simulation decode partial histories. -/
private def couplingRead {i : ℕ} (h : Fin i → (n → ℝ) × (n → ℝ)) (j : ℕ) :
    (n → ℝ) × (n → ℝ) := if hj : j < i then h ⟨j, hj⟩ else 0

omit [Fintype n] [DecidableEq n] in
/-- Reading a fixed response from a partial history is measurable. -/
private theorem measurable_couplingRead (i j : ℕ) :
    Measurable (fun h : Fin i → (n → ℝ) × (n → ℝ) => couplingRead h j) := by
  unfold couplingRead
  split_ifs with hj
  · exact measurable_pi_apply (⟨j, hj⟩ : Fin i)
  · exact measurable_const

/-- The start of a pass after the initial-data queries, with three blocks of `q` slots per pass. -/
private def couplingStart (q t : ℕ) : ℕ := Fintype.card c + 3 * q * t

/-- Decode the responses of the original algorithm from the left and right simulation slots. -/
private def couplingDecode {i : ℕ} (q : ℕ) (pass : ℕ → ℕ)
    (h : Fin i → (n → ℝ) × (n → ℝ)) (j : ℕ) : (n → ℝ) × (n → ℝ) :=
  ((couplingRead h (couplingStart (c := c) q (pass j) + 2 * q + j)).1,
    (couplingRead h (couplingStart (c := c) q (pass j) + j)).2)

omit [Fintype n] [DecidableEq n] in
/-- A fixed decoded response is measurable in the simulation history. -/
private theorem measurable_couplingDecode (i q : ℕ) (pass : ℕ → ℕ) (j : ℕ) :
    Measurable (fun h : Fin i → (n → ℝ) × (n → ℝ) =>
      couplingDecode (c := c) q pass h j) :=
  (measurable_fst.comp (measurable_couplingRead i _)).prodMk
    (measurable_snd.comp (measurable_couplingRead i _))

/-- Restrict a partial transcript to a fixed prefix, filling missing entries with zero. -/
private def couplingPrefix {i : ℕ} (h : Fin i → (n → ℝ) × (n → ℝ)) (j : ℕ) :
    Fin j → (n → ℝ) × (n → ℝ) := fun l => couplingRead h l

omit [Fintype n] [DecidableEq n] in
/-- Taking a fixed prefix of the simulation history is measurable. -/
private theorem measurable_couplingPrefix (i j : ℕ) :
    Measurable (fun h : Fin i → (n → ℝ) × (n → ℝ) => couplingPrefix h j) :=
  measurable_pi_iff.2 fun l => measurable_couplingRead i l

/-- An augmented simulation with separate left, frame-padding and right blocks in each pass.
The frame callbacks see only the history before their pass. Extra zero slots avoid any dependence
of the schedule's index type on the width of a particular pass. -/
private noncomputable def couplingSimulation {q : ℕ}
    (alg : QueryAlgorithm (n → ℝ) ((n → ℝ) × (n → ℝ)) q (Matrix n k ℝ))
    (p : ℕ) (pass : ℕ → ℕ) (D : Matrix n n ℝ) (B : Matrix n c ℝ)
    (Q : (t : ℕ) → (Fin (Fintype.card c + 3 * q * t) → (n → ℝ) × (n → ℝ)) →
      Matrix n (Fin q) ℝ)
    (Qout : (Fin (Fintype.card c + 3 * q * p) → (n → ℝ) × (n → ℝ)) → Matrix n k ℝ) :
    QueryAlgorithm ((n → ℝ) × (n → ℝ)) ((n → ℝ) × (n → ℝ))
      (couplingStart (c := c) q p + Fintype.card k) (Matrix n k ℝ) where
  query i h :=
    if hi : i < Fintype.card c then
      (0, B.col ((Fintype.equivFin c).symm ⟨i, hi⟩))
    else if hi : i < couplingStart (c := c) q p then
      let t := (i - Fintype.card c) / (3 * q)
      let j := (i - Fintype.card c) % (3 * q)
      if hj : j < q then
        if pass j = t then
          (0, alg.query j (fun l => couplingDecode (c := c) q pass h l))
        else 0
      else if hj : j < 2 * q then
        (0, (Q t (couplingPrefix h (couplingStart (c := c) q t))).col
          ⟨j - q, by omega⟩)
      else if hj : j - 2 * q < q then
        if pass (j - 2 * q) = t then
          (D *ᵥ (couplingRead h
            (couplingStart (c := c) q t + (j - 2 * q))).2, 0)
        else 0
      else 0
    else if hi : i - couplingStart (c := c) q p < Fintype.card k then
      (0, (Qout (couplingPrefix h (couplingStart (c := c) q p))).col
        ((Fintype.equivFin k).symm ⟨i - couplingStart (c := c) q p, hi⟩))
    else 0
  output h := alg.output (fun j => couplingDecode (c := c) q pass h j)

omit [DecidableEq n] in
/-- The augmented simulation is measurable when its padding-frame choices are measurable. -/
private theorem measurable_couplingSimulation {q p : ℕ}
    {alg : QueryAlgorithm (n → ℝ) ((n → ℝ) × (n → ℝ)) q (Matrix n k ℝ)}
    (halg : alg.IsMeasurable) (pass : ℕ → ℕ) (D : Matrix n n ℝ) (B : Matrix n c ℝ)
    (Q : (t : ℕ) → (Fin (Fintype.card c + 3 * q * t) → (n → ℝ) × (n → ℝ)) →
      Matrix n (Fin q) ℝ)
    (Qout : (Fin (Fintype.card c + 3 * q * p) → (n → ℝ) × (n → ℝ)) → Matrix n k ℝ)
    (hQ : ∀ t, Measurable (Q t)) (hQout : Measurable Qout) :
    (couplingSimulation alg p pass D B Q Qout).IsMeasurable := by
  classical
  constructor
  · intro i hi
    unfold couplingSimulation
    dsimp only
    split_ifs with h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈
    · exact measurable_const
    · exact measurable_const.prodMk ((halg.measurable_query _ h₃).comp
        (measurable_pi_iff.2 fun l => measurable_couplingDecode i q pass l))
    · exact measurable_const
    · refine measurable_const.prodMk (measurable_pi_iff.2 fun r => ?_)
      change Measurable (fun h => Q _ (couplingPrefix h _) r _)
      exact (measurable_pi_apply _).comp ((measurable_pi_apply r).comp
        ((hQ _).comp (measurable_couplingPrefix i _)))
    · exact (((continuous_const.matrix_mulVec continuous_id).measurable.comp
        (measurable_snd.comp (measurable_couplingRead i _))).prodMk measurable_const)
    · exact measurable_const
    · exact measurable_const
    · refine measurable_const.prodMk (measurable_pi_iff.2 fun r => ?_)
      change Measurable (fun h => Qout (couplingPrefix h _) r _)
      exact (measurable_pi_apply _).comp ((measurable_pi_apply r).comp
        (hQout.comp (measurable_couplingPrefix i _)))
    · exact measurable_const
  · exact halg.measurable_output.comp
      (measurable_pi_iff.2 fun l => measurable_couplingDecode _ q pass l)

omit [DecidableEq n] [Fintype k] in
/-- The zero-filled reader agrees with the response to the indexed query once it is available. -/
private theorem couplingRead_history {a : ℕ}
    (alg : QueryAlgorithm ((n → ℝ) × (n → ℝ)) ((n → ℝ) × (n → ℝ)) a (Matrix n k ℝ))
    (U : Matrix n n ℝ) {i j : ℕ} (hj : j < i) :
    couplingRead (alg.history (twoSidedMulVec U) i) j =
      twoSidedMulVec U (alg.queryAt (twoSidedMulVec U) j) := by
  rw [couplingRead, dif_pos hj, QueryAlgorithm.history_apply]

/-- A slot of an earlier pass precedes every slot of a later pass. -/
private theorem couplingStart_add_lt {q t t' j : ℕ} (htt' : t < t') (hj : j < 3 * q) :
    couplingStart (c := c) q t + j < couplingStart (c := c) q t' := by
  have hmul := Nat.mul_le_mul_left (3 * q) (Nat.succ_le_of_lt htt')
  unfold couplingStart
  nlinarith

section Simulation

variable {q p : ℕ}
  (alg : QueryAlgorithm (n → ℝ) ((n → ℝ) × (n → ℝ)) q (Matrix n k ℝ))
  (pass : ℕ → ℕ) (D : Matrix n n ℝ) (B : Matrix n c ℝ)
  (Q : (t : ℕ) → (Fin (Fintype.card c + 3 * q * t) → (n → ℝ) × (n → ℝ)) →
    Matrix n (Fin q) ℝ)
  (Qout : (Fin (Fintype.card c + 3 * q * p) → (n → ℝ) × (n → ℝ)) → Matrix n k ℝ)

include Q Qout

omit [DecidableEq n] in
/-- Left-query slots submit the original pass's query before its right-product replies. -/
private theorem couplingSimulation_query_left {j : ℕ} (hj : j < q) (hpj : pass j < p)
    (h : Fin (couplingStart (c := c) q (pass j) + j) → (n → ℝ) × (n → ℝ)) :
    (couplingSimulation alg p pass D B Q Qout).query
      (couplingStart (c := c) q (pass j) + j) h =
      (0, alg.query j (fun l => couplingDecode (c := c) q pass h l)) := by
  have hq : 0 < 3 * q := by omega
  have hj' : j < 3 * q := by omega
  have hlt := couplingStart_add_lt (c := c) hpj hj'
  have hge : ¬couplingStart (c := c) q (pass j) + j < Fintype.card c := by
    unfold couplingStart
    omega
  have hs : couplingStart (c := c) q (pass j) + j - Fintype.card c =
      3 * q * pass j + j := by unfold couplingStart; omega
  have hd : (3 * q * pass j + j) / (3 * q) = pass j := by
    rw [Nat.mul_add_div hq, Nat.div_eq_of_lt hj', Nat.add_zero]
  have hm : (3 * q * pass j + j) % (3 * q) = j := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj']
  have hd' : (couplingStart (c := c) q (pass j) + j - Fintype.card c) / (3 * q) =
      pass j := by rw [hs, hd]
  have hm' : (couplingStart (c := c) q (pass j) + j - Fintype.card c) % (3 * q) =
      j := by rw [hs, hm]
  simp only [couplingSimulation, dif_neg hge, dif_pos hlt, hd', hm', dif_pos hj, ite_true]
  apply congrArg (fun x => (0, x))
  exact QueryAlgorithm.query_eq_of_index_hr alg hm' _ _ fun _ => rfl

omit [DecidableEq n] in
/-- Right-product slots use the rotated query already obtained in the same pass. -/
private theorem couplingSimulation_query_right {j : ℕ} (hj : j < q) (hpj : pass j < p)
    (h : Fin (couplingStart (c := c) q (pass j) + 2 * q + j) →
      (n → ℝ) × (n → ℝ)) :
    (couplingSimulation alg p pass D B Q Qout).query
      (couplingStart (c := c) q (pass j) + 2 * q + j) h =
      (D *ᵥ (couplingRead h (couplingStart (c := c) q (pass j) + j)).2, 0) := by
  have hq : 0 < 3 * q := by omega
  have hj' : 2 * q + j < 3 * q := by omega
  have hlt : couplingStart (c := c) q (pass j) + 2 * q + j <
      couplingStart (c := c) q p := by
    simpa only [Nat.add_assoc] using couplingStart_add_lt (c := c) hpj hj'
  have hge : ¬couplingStart (c := c) q (pass j) + 2 * q + j < Fintype.card c := by
    unfold couplingStart
    omega
  have hs : couplingStart (c := c) q (pass j) + 2 * q + j - Fintype.card c =
      3 * q * pass j + (2 * q + j) := by unfold couplingStart; omega
  have hd : (3 * q * pass j + (2 * q + j)) / (3 * q) = pass j := by
    rw [Nat.mul_add_div hq, Nat.div_eq_of_lt hj', Nat.add_zero]
  have hm : (3 * q * pass j + (2 * q + j)) % (3 * q) = 2 * q + j := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj']
  have hsub : 2 * q + j - 2 * q = j := by omega
  have hd' : (couplingStart (c := c) q (pass j) + 2 * q + j - Fintype.card c) /
      (3 * q) = pass j := by rw [hs, hd]
  have hm' : (couplingStart (c := c) q (pass j) + 2 * q + j - Fintype.card c) %
      (3 * q) = 2 * q + j := by rw [hs, hm]
  simp only [couplingSimulation, dif_neg hge, dif_pos hlt, hd', hm',
    dif_neg (show ¬2 * q + j < q by omega), dif_neg (show ¬2 * q + j < 2 * q by omega),
    hsub, dif_pos hj, ite_true]

omit [DecidableEq n] in
/-- The augmented simulation makes the same queries as the original algorithm, with every
left query in a pass submitted before the corresponding right-product phase. -/
private theorem couplingSimulation_queryAt (hpass : alg.IsPassStructured pass)
    (hp : ∀ i < q, pass i < p) (U : Matrix n n ℝ) :
    ∀ j < q,
      (couplingSimulation alg p pass D B Q Qout).queryAt (twoSidedMulVec U)
        (couplingStart (c := c) q (pass j) + j) =
          (0, alg.queryAt (hiddenRotationOracle U D) j) ∧
      (couplingSimulation alg p pass D B Q Qout).queryAt (twoSidedMulVec U)
        (couplingStart (c := c) q (pass j) + 2 * q + j) =
          (D *ᵥ (Uᴴ *ᵥ alg.queryAt (hiddenRotationOracle U D) j), 0) := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj
    let sim := couplingSimulation alg p pass D B Q Qout
    have hleft : sim.queryAt (twoSidedMulVec U) (couplingStart (c := c) q (pass j) + j) =
        (0, alg.queryAt (hiddenRotationOracle U D) j) := by
      change sim.query _ _ = _
      rw [couplingSimulation_query_left alg pass D B Q Qout hj (hp j hj)]
      apply congrArg (fun x => (0, x))
      apply hpass.query_eq j hj
      intro l hl
      have hlq : (l : ℕ) < q := l.isLt.trans hj
      have hprev := ih l l.isLt hlq
      have hL : couplingStart (c := c) q (pass l) + l <
          couplingStart (c := c) q (pass j) + j :=
        (couplingStart_add_lt (c := c) hl (by omega)).trans_le (Nat.le_add_right _ _)
      have hR : couplingStart (c := c) q (pass l) + 2 * q + l <
          couplingStart (c := c) q (pass j) + j := by
        have := couplingStart_add_lt (c := c) hl (show 2 * q + l < 3 * q by omega)
        omega
      rw [couplingDecode, couplingRead_history sim U hR, couplingRead_history sim U hL,
        hprev.1, hprev.2, QueryAlgorithm.history_apply]
      simp only [twoSidedMulVec, hiddenRotationOracle, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    refine ⟨hleft, ?_⟩
    change sim.query _ _ = _
    rw [couplingSimulation_query_right alg pass D B Q Qout hj (hp j hj),
      couplingRead_history sim U (show couplingStart (c := c) q (pass j) + j <
        couplingStart (c := c) q (pass j) + 2 * q + j by omega), hleft]
    rfl

omit [DecidableEq n] in
/-- After all pass blocks have finished, the decoded transcript is the original transcript. -/
private theorem couplingDecode_history (hpass : alg.IsPassStructured pass)
    (hp : ∀ i < q, pass i < p) (U : Matrix n n ℝ) {i : ℕ}
    (hi : couplingStart (c := c) q p ≤ i) (j : Fin q) :
    couplingDecode (c := c) q pass
      ((couplingSimulation alg p pass D B Q Qout).history (twoSidedMulVec U) i) j =
      alg.transcript (hiddenRotationOracle U D) j := by
  have hqueries := couplingSimulation_queryAt alg pass D B Q Qout hpass hp U j j.isLt
  have hL : couplingStart (c := c) q (pass j) + j < i :=
    (couplingStart_add_lt (c := c) (hp j j.isLt) (by omega)).trans_le hi
  have hR : couplingStart (c := c) q (pass j) + 2 * q + j < i := by
    have := couplingStart_add_lt (c := c) (hp j j.isLt)
      (show 2 * q + j < 3 * q by omega)
    omega
  rw [couplingDecode, couplingRead_history _ U hR, couplingRead_history _ U hL,
    hqueries.1, hqueries.2, QueryAlgorithm.transcript, QueryAlgorithm.history_apply]
  simp only [twoSidedMulVec, hiddenRotationOracle, Matrix.mulVec_mulVec, Matrix.mul_assoc]

omit [DecidableEq n] in
/-- Padding-frame queries change the revealed history but do not change the simulated output. -/
private theorem run_couplingSimulation (hpass : alg.IsPassStructured pass)
    (hp : ∀ i < q, pass i < p) (U : Matrix n n ℝ) :
    (couplingSimulation alg p pass D B Q Qout).run (twoSidedMulVec U) =
      alg.run (hiddenRotationOracle U D) := by
  unfold QueryAlgorithm.run QueryAlgorithm.transcript
  apply congrArg alg.output
  funext j
  exact couplingDecode_history alg pass D B Q Qout hpass hp U (Nat.le_add_right _ _) j

end Simulation

/-- The singleton construction uses no padded-frame queries and exposes the actual output. -/
private noncomputable def couplingAlgorithm {q : ℕ}
    (alg : QueryAlgorithm (n → ℝ) ((n → ℝ) × (n → ℝ)) q (Matrix n k ℝ))
    (p : ℕ) (pass : ℕ → ℕ) (D : Matrix n n ℝ) (B : Matrix n c ℝ) :=
  couplingSimulation alg p pass D B (fun _ _ => 0)
    (fun h => alg.output (fun j => couplingDecode (c := c) q pass h j))

omit [DecidableEq n] in
/-- The singleton augmented simulation is measurable. -/
private theorem measurable_couplingAlgorithm {q : ℕ}
    {alg : QueryAlgorithm (n → ℝ) ((n → ℝ) × (n → ℝ)) q (Matrix n k ℝ)}
    (halg : alg.IsMeasurable) (p : ℕ) (pass : ℕ → ℕ) (D : Matrix n n ℝ)
    (B : Matrix n c ℝ) : (couplingAlgorithm alg p pass D B).IsMeasurable :=
  measurable_couplingSimulation halg pass D B _ _ (fun _ => measurable_const)
    (halg.measurable_output.comp
      (measurable_pi_iff.2 fun j => measurable_couplingDecode _ q pass j))

omit [DecidableEq n] in
/-- The singleton simulation has the same output as the original algorithm. -/
private theorem run_couplingAlgorithm {q p : ℕ}
    {alg : QueryAlgorithm (n → ℝ) ((n → ℝ) × (n → ℝ)) q (Matrix n k ℝ)}
    {pass : ℕ → ℕ} (hpass : alg.IsPassStructured pass) (hp : ∀ i < q, pass i < p)
    (D : Matrix n n ℝ) (B : Matrix n c ℝ) (U : Matrix n n ℝ) :
    (couplingAlgorithm alg p pass D B).run (twoSidedMulVec U) =
      alg.run (hiddenRotationOracle U D) :=
  run_couplingSimulation alg pass D B _ _ hpass hp U

/-- One left-response slot per original query and per output column. -/
private noncomputable def couplingRound (q p : ℕ) (pass : ℕ → ℕ) : Fin q ⊕ k → ℕ
  | Sum.inl j => couplingStart (c := c) q (pass j) + j
  | Sum.inr j => couplingStart (c := c) q p + Fintype.equivFin k j

omit [DecidableEq n] in
/-- The slots carrying the output occur after all the product-query passes. -/
private theorem couplingAlgorithm_query_output {q p : ℕ}
    (alg : QueryAlgorithm (n → ℝ) ((n → ℝ) × (n → ℝ)) q (Matrix n k ℝ))
    (pass : ℕ → ℕ) (D : Matrix n n ℝ) (B : Matrix n c ℝ) (j : k)
    (h : Fin (couplingStart (c := c) q p + Fintype.equivFin k j) →
      (n → ℝ) × (n → ℝ)) :
    (couplingAlgorithm alg p pass D B).query
      (couplingStart (c := c) q p + Fintype.equivFin k j) h =
      (0, (alg.output (fun l => couplingDecode (c := c) q pass
        (couplingPrefix h (couplingStart (c := c) q p)) l)).col j) := by
  classical
  have hge : ¬couplingStart (c := c) q p + Fintype.equivFin k j < Fintype.card c := by
    unfold couplingStart
    omega
  have hge' : ¬couplingStart (c := c) q p + Fintype.equivFin k j <
      couplingStart (c := c) q p := by omega
  have hsub : couplingStart (c := c) q p + Fintype.equivFin k j -
      couplingStart (c := c) q p = Fintype.equivFin k j := by omega
  simp only [couplingAlgorithm, couplingSimulation, dif_neg hge, dif_neg hge', hsub,
    dif_pos (Fintype.equivFin k j).isLt]
  congr 2
  exact (Fintype.equivFin k).symm_apply_apply j

omit [DecidableEq n] [Fintype k] in
/-- Restricting an actual simulation history gives its shorter history. -/
private theorem couplingPrefix_history {a : ℕ}
    (alg : QueryAlgorithm ((n → ℝ) × (n → ℝ)) ((n → ℝ) × (n → ℝ)) a (Matrix n k ℝ))
    (U : Matrix n n ℝ) {i j : ℕ} (hij : i ≤ j) :
    couplingPrefix (alg.history (twoSidedMulVec U) j) i = alg.history (twoSidedMulVec U) i := by
  funext l
  unfold couplingPrefix couplingRead
  rw [dif_pos (l.isLt.trans_le hij), QueryAlgorithm.history_apply, QueryAlgorithm.history_apply]

omit [DecidableEq n] in
/-- The initial left queries expose every column of the fixed initial block. -/
private theorem couplingAlgorithm_query_initial {q p : ℕ}
    (alg : QueryAlgorithm (n → ℝ) ((n → ℝ) × (n → ℝ)) q (Matrix n k ℝ))
    (pass : ℕ → ℕ) (D : Matrix n n ℝ) (B : Matrix n c ℝ) (j : c)
    (h : Fin (Fintype.equivFin c j) → (n → ℝ) × (n → ℝ)) :
    (couplingAlgorithm alg p pass D B).query (Fintype.equivFin c j) h = (0, B.col j) := by
  classical
  simp only [couplingAlgorithm, couplingSimulation, dif_pos (Fintype.equivFin c j).isLt]
  congr 2
  exact (Fintype.equivFin c).symm_apply_apply j

omit [DecidableEq n] in
/-- The output-exposure rounds submit the true output columns of the original algorithm. -/
private theorem couplingAlgorithm_queryAt_output {q p : ℕ}
    {alg : QueryAlgorithm (n → ℝ) ((n → ℝ) × (n → ℝ)) q (Matrix n k ℝ)}
    {pass : ℕ → ℕ} (hpass : alg.IsPassStructured pass) (hp : ∀ i < q, pass i < p)
    (D : Matrix n n ℝ) (B : Matrix n c ℝ) (U : Matrix n n ℝ) (j : k) :
    (couplingAlgorithm alg p pass D B).queryAt (twoSidedMulVec U)
      (couplingStart (c := c) q p + Fintype.equivFin k j) =
        (0, (alg.run (hiddenRotationOracle U D)).col j) := by
  change (couplingAlgorithm alg p pass D B).query _ _ = _
  rw [couplingAlgorithm_query_output, couplingPrefix_history _ U (Nat.le_add_right _ _)]
  have hdecode : (fun l : Fin q => couplingDecode (c := c) q pass
      ((couplingAlgorithm alg p pass D B).history (twoSidedMulVec U)
        (couplingStart (c := c) q p)) l) = alg.transcript (hiddenRotationOracle U D) := by
    funext l
    exact couplingDecode_history alg pass D B _ _ hpass hp U le_rfl l
  rw [hdecode]
  rfl

omit [DecidableEq n] in
/-- Every nonzero slot inside the pass blocks is an original left query or right product. -/
private theorem couplingAlgorithm_queryAt_pass_cases {q p : ℕ}
    {alg : QueryAlgorithm (n → ℝ) ((n → ℝ) × (n → ℝ)) q (Matrix n k ℝ)}
    {pass : ℕ → ℕ} (hpass : alg.IsPassStructured pass) (hp : ∀ j < q, pass j < p)
    (D : Matrix n n ℝ) (B : Matrix n c ℝ) (U : Matrix n n ℝ) {i : ℕ}
    (hci : Fintype.card c ≤ i) (hbi : i < couplingStart (c := c) q p) :
    (couplingAlgorithm alg p pass D B).queryAt (twoSidedMulVec U) i = 0 ∨
      (∃ j : Fin q, i = couplingStart (c := c) q (pass j) + j ∧
        (couplingAlgorithm alg p pass D B).queryAt (twoSidedMulVec U) i =
          (0, alg.queryAt (hiddenRotationOracle U D) j)) ∨
      (∃ j : Fin q, i = couplingStart (c := c) q (pass j) + 2 * q + j ∧
        (couplingAlgorithm alg p pass D B).queryAt (twoSidedMulVec U) i =
          (D *ᵥ (Uᴴ *ᵥ alg.queryAt (hiddenRotationOracle U D) j), 0)) := by
  classical
  have hq : 0 < q := by
    unfold couplingStart at hbi
    by_contra h
    simp [Nat.eq_zero_of_not_pos h] at hbi
    omega
  let t := (i - Fintype.card c) / (3 * q)
  let j := (i - Fintype.card c) % (3 * q)
  have hjlt : j < 3 * q := Nat.mod_lt _ (by omega)
  have heq : i = couplingStart (c := c) q t + j := by
    have := Nat.mod_add_div (i - Fintype.card c) (3 * q)
    unfold couplingStart
    dsimp only [j, t]
    omega
  have hnot : ¬i < Fintype.card c := Nat.not_lt.mpr hci
  by_cases hj : j < q
  · by_cases ht : pass j = t
    · right; left
      refine ⟨⟨j, hj⟩, by simpa only [ht] using heq, ?_⟩
      rw [heq, ← ht]
      exact (couplingSimulation_queryAt alg pass D B _ _ hpass hp U j hj).1
    · left
      simp only [QueryAlgorithm.queryAt, couplingAlgorithm, couplingSimulation, dif_neg hnot,
        dif_pos hbi]
      change (if _h : j < q then if pass j = t then _ else 0 else _) = 0
      rw [dif_pos hj, if_neg ht]
  · by_cases hj' : j < 2 * q
    · left
      simp only [QueryAlgorithm.queryAt, couplingAlgorithm, couplingSimulation, dif_neg hnot,
        dif_pos hbi]
      change (if _h : j < q then _ else if _h : j < 2 * q then _ else _) = 0
      simp only [dif_neg hj, dif_pos hj']
      rfl
    · have hd : j - 2 * q < q := by omega
      by_cases ht : pass (j - 2 * q) = t
      · right; right
        have hidx : i = couplingStart (c := c) q (pass (j - 2 * q)) + 2 * q +
            (j - 2 * q) := by rw [ht]; omega
        refine ⟨⟨j - 2 * q, hd⟩, hidx, ?_⟩
        rw [hidx]
        exact (couplingSimulation_queryAt alg pass D B _ _ hpass hp U _ hd).2
      · left
        simp only [QueryAlgorithm.queryAt, couplingAlgorithm, couplingSimulation, dif_neg hnot,
          dif_pos hbi]
        change (if _h : j < q then _ else if _h : j < 2 * q then _ else
          if _h : j - 2 * q < q then if pass (j - 2 * q) = t then _ else 0 else _) = 0
        rw [dif_neg hj, dif_neg hj', dif_pos hd, if_neg ht]

omit [DecidableEq n] in
/-- The augmented transcript contains only the initial block, original queries and products,
the output columns, and zero padding. -/
private theorem couplingAlgorithm_queryAt_cases {q p : ℕ}
    {alg : QueryAlgorithm (n → ℝ) ((n → ℝ) × (n → ℝ)) q (Matrix n k ℝ)}
    {pass : ℕ → ℕ} (hpass : alg.IsPassStructured pass) (hp : ∀ j < q, pass j < p)
    (D : Matrix n n ℝ) (B : Matrix n c ℝ) (U : Matrix n n ℝ) {i : ℕ}
    (hi : i < couplingStart (c := c) q p + Fintype.card k) :
    (∃ a : c, i = Fintype.equivFin c a ∧
      (couplingAlgorithm alg p pass D B).queryAt (twoSidedMulVec U) i = (0, B.col a)) ∨
    (∃ j : Fin q, i = couplingStart (c := c) q (pass j) + j ∧
      (couplingAlgorithm alg p pass D B).queryAt (twoSidedMulVec U) i =
        (0, alg.queryAt (hiddenRotationOracle U D) j)) ∨
    (∃ j : Fin q, i = couplingStart (c := c) q (pass j) + 2 * q + j ∧
      (couplingAlgorithm alg p pass D B).queryAt (twoSidedMulVec U) i =
        (D *ᵥ (Uᴴ *ᵥ alg.queryAt (hiddenRotationOracle U D) j), 0)) ∨
    (∃ a : k, i = couplingStart (c := c) q p + Fintype.equivFin k a ∧
      (couplingAlgorithm alg p pass D B).queryAt (twoSidedMulVec U) i =
        (0, (alg.run (hiddenRotationOracle U D)).col a)) ∨
    (couplingAlgorithm alg p pass D B).queryAt (twoSidedMulVec U) i = 0 := by
  classical
  by_cases hc : i < Fintype.card c
  · let a := (Fintype.equivFin c).symm ⟨i, hc⟩
    have heq : i = Fintype.equivFin c a := by simp [a]
    left
    refine ⟨a, heq, ?_⟩
    rw [heq]
    exact couplingAlgorithm_query_initial alg pass D B a _
  · by_cases hb : i < couplingStart (c := c) q p
    · rcases couplingAlgorithm_queryAt_pass_cases hpass hp D B U (Nat.le_of_not_gt hc) hb
        with hz | hleft | hright
      · exact Or.inr (Or.inr (Or.inr (Or.inr hz)))
      · exact Or.inr (Or.inl hleft)
      · exact Or.inr (Or.inr (Or.inl hright))
    · let a := (Fintype.equivFin k).symm
          ⟨i - couplingStart (c := c) q p, by omega⟩
      have heq : i = couplingStart (c := c) q p + Fintype.equivFin k a := by
        simp only [a, Equiv.apply_symm_apply]
        omega
      right; right; right; left
      refine ⟨a, heq, ?_⟩
      rw [heq]
      exact couplingAlgorithm_queryAt_output hpass hp D B U a

/-- The hidden vectors exposed by the first `i` two-sided simulation rounds. -/
private def couplingRevealedAt {a : ℕ}
    (sim : QueryAlgorithm ((n → ℝ) × (n → ℝ)) ((n → ℝ) × (n → ℝ)) a (Matrix n k ℝ))
    (U : Matrix n n ℝ) (i : ℕ) : Matrix n (Fin i ⊕ Fin i) ℝ :=
  let τ := (sim.truncate i).transcript (twoSidedMulVec U)
  Matrix.fromCols ((sim.truncate i).rightQueryMatrix τ) (Matrix.of fun r j => (τ j).2 r)

omit [DecidableEq n] [Fintype k] in
/-- Membership of every previously exposed vector bounds the whole revealed column space. -/
private theorem range_couplingRevealedAt_le {a : ℕ}
    (sim : QueryAlgorithm ((n → ℝ) × (n → ℝ)) ((n → ℝ) × (n → ℝ)) a (Matrix n k ℝ))
    (U : Matrix n n ℝ) (i : ℕ) (T : Submodule ℝ (n → ℝ))
    (h : ∀ j < i, (sim.queryAt (twoSidedMulVec U) j).1 ∈ T ∧
      Uᴴ *ᵥ (sim.queryAt (twoSidedMulVec U) j).2 ∈ T) :
    LinearMap.range (couplingRevealedAt sim U i).mulVecLin ≤ T := by
  rw [Matrix.range_mulVecLin]
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  rcases j with j | j
  · change ((sim.truncate i).queries ((sim.truncate i).transcript (twoSidedMulVec U)) j).1 ∈ T
    rw [← QueryAlgorithm.queryAt_eq_queries_transcript]
    change (sim.query j ((sim.truncate i).history (twoSidedMulVec U) j)).1 ∈ T
    rw [QueryAlgorithm.history_truncate]
    exact (h j j.isLt).1
  · change (((sim.truncate i).transcript (twoSidedMulVec U)) j).2 ∈ T
    rw [QueryAlgorithm.transcript, QueryAlgorithm.history_truncate, QueryAlgorithm.history_apply]
    exact (h j j.isLt).2

/-- Every starting column belongs to every positive-depth block Krylov space. -/
private theorem col_mem_blockKrylovSpace_of_pos {b : Type*} [Fintype b]
    (D : Matrix n n ℝ) (S : Matrix n b ℝ) {s : ℕ} (hs : 0 < s) (j : b) :
    S.col j ∈ blockKrylovSpace D S s := by
  have hcol : S.col j ∈ LinearMap.range S.mulVecLin := by
    rw [Matrix.range_mulVecLin]
    exact Submodule.subset_span ⟨j, rfl⟩
  have hle : LinearMap.range S.mulVecLin ≤ blockKrylovSpace D S s := by
    rw [← blockKrylovSpace_one D S]
    exact blockKrylovSpace_mono D S hs
  exact hle hcol

/-- Before an original left query, all revealed vectors have the depth of its pass, assuming
this has already been proved for the earlier queries. -/
private theorem range_revealed_before_query_le {q p : ℕ}
    {alg : QueryAlgorithm (n → ℝ) ((n → ℝ) × (n → ℝ)) q (Matrix n k ℝ)}
    {pass : ℕ → ℕ} (hpass : alg.IsPassStructured pass) (hp : ∀ l < q, pass l < p)
    (D : Matrix n n ℝ) (B : Matrix n c ℝ) (U : Matrix n n ℝ)
    (G : Matrix n (Fin q ⊕ k) ℝ) (j : Fin q)
    (hprev : ∀ l : Fin q, (l : ℕ) < j → Uᴴ *ᵥ alg.queryAt (hiddenRotationOracle U D) l ∈
      blockKrylovSpace D (Matrix.fromCols (Uᴴ * B) G) (pass l + 1)) :
    LinearMap.range (couplingRevealedAt (couplingAlgorithm alg p pass D B) U
      (couplingStart (c := c) q (pass j) + j)).mulVecLin ≤
        blockKrylovSpace D (Matrix.fromCols (Uᴴ * B) G) (pass j + 1) := by
  let S := Matrix.fromCols (Uᴴ * B) G
  let T := blockKrylovSpace D S (pass j + 1)
  have hjend : couplingStart (c := c) q (pass j) + j < couplingStart (c := c) q p :=
    couplingStart_add_lt (c := c) (hp j j.isLt) (by omega)
  apply range_couplingRevealedAt_le
  intro m hm
  have hmtotal : m < couplingStart (c := c) q p + Fintype.card k := by omega
  rcases couplingAlgorithm_queryAt_cases hpass hp D B U hmtotal with
    ⟨a, hidx, hquery⟩ | ⟨l, hidx, hquery⟩ | ⟨l, hidx, hquery⟩ |
      ⟨a, hidx, hquery⟩ | hquery
  · rw [hquery]
    refine ⟨T.zero_mem, ?_⟩
    exact col_mem_blockKrylovSpace_of_pos D S (by omega) (Sum.inl a)
  · have hlj : (l : ℕ) < j := by
      by_contra h
      have hmul := Nat.mul_le_mul_left (3 * q) (hpass.monotone (Nat.le_of_not_gt h))
      unfold couplingStart at hidx hm
      omega
    rw [hquery]
    refine ⟨T.zero_mem, ?_⟩
    exact blockKrylovSpace_mono D S (Nat.add_le_add_right (hpass.monotone hlj.le) 1)
      (hprev l hlj)
  · have hpasslt : pass l < pass j := by
      by_contra h
      have hmul := Nat.mul_le_mul_left (3 * q) (Nat.le_of_not_gt h)
      have hjq := j.isLt
      unfold couplingStart at hidx hm
      omega
    have hlj : (l : ℕ) < j := by
      by_contra h
      exact (Nat.not_le_of_gt hpasslt) (hpass.monotone (Nat.le_of_not_gt h))
    rw [hquery]
    refine ⟨?_, ?_⟩
    · exact blockKrylovSpace_mono D S (by omega)
        (mulVec_mem_blockKrylovSpace_succ (hprev l hlj))
    · change Uᴴ *ᵥ (0 : n → ℝ) ∈ T
      rw [Matrix.mulVec_zero]
      exact T.zero_mem
  · have : couplingStart (c := c) q p ≤ m := by omega
    omega
  · rw [hquery]
    refine ⟨T.zero_mem, ?_⟩
    change Uᴴ *ᵥ (0 : n → ℝ) ∈ T
    rw [Matrix.mulVec_zero]
    exact T.zero_mem

/-- Capturing each original query by one innovation gives the expected degree per pass. -/
private theorem query_mem_blockKrylovSpace_of_captures {q p : ℕ}
    {alg : QueryAlgorithm (n → ℝ) ((n → ℝ) × (n → ℝ)) q (Matrix n k ℝ)}
    {pass : ℕ → ℕ} (hpass : alg.IsPassStructured pass) (hp : ∀ l < q, pass l < p)
    (D : Matrix n n ℝ) (B : Matrix n c ℝ) (U : Matrix n n ℝ)
    (G : Matrix n (Fin q ⊕ k) ℝ)
    (hcap : ∀ j : Fin q, Uᴴ *ᵥ alg.queryAt (hiddenRotationOracle U D) j ∈
      LinearMap.range (couplingRevealedAt (couplingAlgorithm alg p pass D B) U
        (couplingStart (c := c) q (pass j) + j)).mulVecLin ⊔
          LinearMap.range G.mulVecLin) :
    ∀ j : Fin q, Uᴴ *ᵥ alg.queryAt (hiddenRotationOracle U D) j ∈
      blockKrylovSpace D (Matrix.fromCols (Uᴴ * B) G) (pass j + 1) := by
  have h : ∀ j < q, Uᴴ *ᵥ alg.queryAt (hiddenRotationOracle U D) j ∈
      blockKrylovSpace D (Matrix.fromCols (Uᴴ * B) G) (pass j + 1) := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro hj
      have hrevealed := range_revealed_before_query_le hpass hp D B U G ⟨j, hj⟩
        (fun l hl => ih l hl l.isLt)
      have hnew : LinearMap.range G.mulVecLin ≤
          blockKrylovSpace D (Matrix.fromCols (Uᴴ * B) G) (pass j + 1) := by
        rw [Matrix.range_mulVecLin]
        apply Submodule.span_le.mpr
        rintro _ ⟨a, rfl⟩
        exact col_mem_blockKrylovSpace_of_pos D (Matrix.fromCols (Uᴴ * B) G)
          (Nat.succ_pos _) (Sum.inr a)
      exact sup_le hrevealed hnew (hcap ⟨j, hj⟩)
  exact fun j => h j j.isLt

/-- Once all product passes are finished, earlier output innovations add no further degree. -/
private theorem range_revealed_before_output_le {q p : ℕ}
    {alg : QueryAlgorithm (n → ℝ) ((n → ℝ) × (n → ℝ)) q (Matrix n k ℝ)}
    {pass : ℕ → ℕ} (hpass : alg.IsPassStructured pass) (hp : ∀ l < q, pass l < p)
    (D : Matrix n n ℝ) (B : Matrix n c ℝ) (U : Matrix n n ℝ)
    (G : Matrix n (Fin q ⊕ k) ℝ) (j : k)
    (hqueries : ∀ l : Fin q, Uᴴ *ᵥ alg.queryAt (hiddenRotationOracle U D) l ∈
      blockKrylovSpace D (Matrix.fromCols (Uᴴ * B) G) (pass l + 1))
    (hprev : ∀ a : k, Fintype.equivFin k a < Fintype.equivFin k j →
      Uᴴ *ᵥ (alg.run (hiddenRotationOracle U D)).col a ∈
        blockKrylovSpace D (Matrix.fromCols (Uᴴ * B) G) (p + 1)) :
    LinearMap.range (couplingRevealedAt (couplingAlgorithm alg p pass D B) U
      (couplingStart (c := c) q p + Fintype.equivFin k j)).mulVecLin ≤
        blockKrylovSpace D (Matrix.fromCols (Uᴴ * B) G) (p + 1) := by
  let S := Matrix.fromCols (Uᴴ * B) G
  let T := blockKrylovSpace D S (p + 1)
  apply range_couplingRevealedAt_le
  intro m hm
  have hmtotal : m < couplingStart (c := c) q p + Fintype.card k := by
    have := (Fintype.equivFin k j).isLt
    omega
  rcases couplingAlgorithm_queryAt_cases hpass hp D B U hmtotal with
    ⟨a, hidx, hquery⟩ | ⟨l, hidx, hquery⟩ | ⟨l, hidx, hquery⟩ |
      ⟨a, hidx, hquery⟩ | hquery
  · rw [hquery]
    exact ⟨T.zero_mem, col_mem_blockKrylovSpace_of_pos D S (by omega) (Sum.inl a)⟩
  · rw [hquery]
    exact ⟨T.zero_mem, blockKrylovSpace_mono D S (by have := hp l l.isLt; omega) (hqueries l)⟩
  · rw [hquery]
    refine ⟨?_, ?_⟩
    · exact blockKrylovSpace_mono D S (by have := hp l l.isLt; omega)
        (mulVec_mem_blockKrylovSpace_succ (hqueries l))
    · change Uᴴ *ᵥ (0 : n → ℝ) ∈ T
      rw [Matrix.mulVec_zero]
      exact T.zero_mem
  · rw [hquery]
    exact ⟨T.zero_mem, hprev a (by omega)⟩
  · rw [hquery]
    refine ⟨T.zero_mem, ?_⟩
    change Uᴴ *ᵥ (0 : n → ℝ) ∈ T
    rw [Matrix.mulVec_zero]
    exact T.zero_mem

/-- Innovation captures of the queries and output columns imply the full block Krylov inclusion. -/
private theorem range_output_le_blockKrylovSpace_of_captures {q p : ℕ}
    {alg : QueryAlgorithm (n → ℝ) ((n → ℝ) × (n → ℝ)) q (Matrix n k ℝ)}
    {pass : ℕ → ℕ} (hpass : alg.IsPassStructured pass) (hp : ∀ l < q, pass l < p)
    (D : Matrix n n ℝ) (B : Matrix n c ℝ) (U : Matrix n n ℝ)
    (G : Matrix n (Fin q ⊕ k) ℝ)
    (hcap : ∀ j : Fin q, Uᴴ *ᵥ alg.queryAt (hiddenRotationOracle U D) j ∈
      LinearMap.range (couplingRevealedAt (couplingAlgorithm alg p pass D B) U
        (couplingStart (c := c) q (pass j) + j)).mulVecLin ⊔
          LinearMap.range G.mulVecLin)
    (hcapout : ∀ j : k, Uᴴ *ᵥ (alg.run (hiddenRotationOracle U D)).col j ∈
      LinearMap.range (couplingRevealedAt (couplingAlgorithm alg p pass D B) U
        (couplingStart (c := c) q p + Fintype.equivFin k j)).mulVecLin ⊔
          LinearMap.range G.mulVecLin) :
    LinearMap.range (Uᴴ * alg.run (hiddenRotationOracle U D)).mulVecLin ≤
      blockKrylovSpace D (Matrix.fromCols (Uᴴ * B) G) (p + 1) := by
  classical
  let T := blockKrylovSpace D (Matrix.fromCols (Uᴴ * B) G) (p + 1)
  have hqueries := query_mem_blockKrylovSpace_of_captures hpass hp D B U G hcap
  have hout : ∀ d (hd : d < Fintype.card k),
      Uᴴ *ᵥ (alg.run (hiddenRotationOracle U D)).col ((Fintype.equivFin k).symm ⟨d, hd⟩) ∈ T := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro hd
      let j := (Fintype.equivFin k).symm ⟨d, hd⟩
      have hrevealed := range_revealed_before_output_le hpass hp D B U G j hqueries
        (fun a ha => by
          have had : (Fintype.equivFin k a : ℕ) < d := by
            have hfin : Fintype.equivFin k a < (⟨d, hd⟩ : Fin (Fintype.card k)) := by
              simpa only [j, Equiv.apply_symm_apply] using ha
            exact hfin
          have hih := ih (Fintype.equivFin k a) had (Fintype.equivFin k a).isLt
          change Uᴴ *ᵥ (alg.run (hiddenRotationOracle U D)).col
            ((Fintype.equivFin k).symm (Fintype.equivFin k a)) ∈ T at hih
          rw [Equiv.symm_apply_apply] at hih
          exact hih)
      have hnew : LinearMap.range G.mulVecLin ≤ T := by
        rw [Matrix.range_mulVecLin]
        apply Submodule.span_le.mpr
        rintro _ ⟨a, rfl⟩
        exact col_mem_blockKrylovSpace_of_pos D (Matrix.fromCols (Uᴴ * B) G)
          (Nat.succ_pos _) (Sum.inr a)
      exact sup_le hrevealed hnew (hcapout j)
  rw [Matrix.range_mulVecLin]
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  have hj := hout (Fintype.equivFin k j) (Fintype.equivFin k j).isLt
  change Uᴴ *ᵥ (alg.run (hiddenRotationOracle U D)).col
    ((Fintype.equivFin k).symm (Fintype.equivFin k j)) ∈ T at hj
  rw [Equiv.symm_apply_apply] at hj
  exact hj

/-- Column order: all original query innovations precede the output innovations. -/
private noncomputable def couplingColumnIndex (q : ℕ) : Fin q ⊕ k → ℕ
  | Sum.inl j => j
  | Sum.inr j => q + Fintype.equivFin k j

omit [DecidableEq n] [Fintype n] in
/-- Selected left-response rounds respect the order of their Gaussian columns. -/
private theorem couplingRound_lt_of_columnIndex_lt {q p : ℕ}
    {alg : QueryAlgorithm (n → ℝ) ((n → ℝ) × (n → ℝ)) q (Matrix n k ℝ)}
    {pass : ℕ → ℕ} (hpass : alg.IsPassStructured pass) (hp : ∀ j < q, pass j < p)
    {a b : Fin q ⊕ k} (hab : couplingColumnIndex q a < couplingColumnIndex q b) :
    couplingRound (c := c) q p pass a < couplingRound (c := c) q p pass b := by
  rcases a with j | a <;> rcases b with l | b
  · simp only [couplingColumnIndex, couplingRound] at hab ⊢
    have hmul := Nat.mul_le_mul_left (3 * q) (hpass.monotone (Nat.le_of_lt hab))
    unfold couplingStart
    omega
  · simp only [couplingRound]
    have hlt := couplingStart_add_lt (c := c) (hp j j.isLt) (show (j : ℕ) < 3 * q by omega)
    omega
  · simp only [couplingColumnIndex] at hab
    have := l.isLt
    omega
  · simp only [couplingColumnIndex, couplingRound] at hab ⊢
    omega

/-- Every selected innovation follows the initial block and lies within the simulation budget. -/
private theorem couplingRound_bounds {q p : ℕ} {pass : ℕ → ℕ} (hp : ∀ j < q, pass j < p)
    (a : Fin q ⊕ k) : Fintype.card c ≤ couplingRound (c := c) q p pass a ∧
      couplingRound (c := c) q p pass a < couplingStart (c := c) q p + Fintype.card k := by
  rcases a with j | a
  · simp only [couplingRound]
    have hlt := couplingStart_add_lt (c := c) (hp j j.isLt) (show (j : ℕ) < 3 * q by omega)
    unfold couplingStart at *
    omega
  · simp only [couplingRound]
    have := (Fintype.equivFin k a).isLt
    unfold couplingStart
    omega

/-- Recover the initial block in hidden coordinates from the simulation's initial left replies. -/
private noncomputable def couplingInitialSummary {i : ℕ}
    (τ : Fin i → (n → ℝ) × (n → ℝ)) : Matrix n c ℝ :=
  fun r a => (couplingRead τ (Fintype.equivFin c a)).2 r

omit [Fintype n] [DecidableEq n] in
/-- The initial summary is a measurable function of every partial transcript. -/
private theorem measurable_couplingInitialSummary (i : ℕ) :
    Measurable (couplingInitialSummary (n := n) (c := c) (i := i)) :=
  measurable_pi_iff.2 fun r => measurable_pi_iff.2 fun a =>
    (measurable_pi_apply r).comp
      (measurable_snd.comp (measurable_couplingRead i (Fintype.equivFin c a)))

omit [DecidableEq n] in
/-- Every transcript after initialization determines the rotated initial block. -/
private theorem couplingInitialSummary_history {q p : ℕ}
    (alg : QueryAlgorithm (n → ℝ) ((n → ℝ) × (n → ℝ)) q (Matrix n k ℝ))
    (pass : ℕ → ℕ) (D : Matrix n n ℝ) (B : Matrix n c ℝ) (U : Matrix n n ℝ)
    {i : ℕ} (hi : Fintype.card c ≤ i) :
    couplingInitialSummary (c := c)
      ((couplingAlgorithm alg p pass D B).history (twoSidedMulVec U) i) = Uᴴ * B := by
  ext r a
  unfold couplingInitialSummary
  rw [couplingRead_history _ U ((Fintype.equivFin c a).isLt.trans_le hi)]
  change (twoSidedMulVec U ((couplingAlgorithm alg p pass D B).query
    (Fintype.equivFin c a) _)).2 r = _
  rw [couplingAlgorithm_query_initial]
  rfl

/-- Enumerate query columns followed by output columns. -/
private noncomputable def couplingOrder (q : ℕ) : Fin q ⊕ k ≃ Fin (q + Fintype.card k) :=
  (Equiv.sumCongr (Equiv.refl (Fin q)) (Fintype.equivFin k)).trans finSumFinEquiv

/-- The explicit column index is the natural value of the enumeration. -/
private theorem couplingColumnIndex_eq_order (q : ℕ) (a : Fin q ⊕ k) :
    couplingColumnIndex q a = couplingOrder q a := by
  rcases a with j | a
  · simp only [couplingColumnIndex, couplingOrder, Equiv.trans_apply, Equiv.sumCongr_apply,
      Equiv.refl_apply, Sum.map_inl, finSumFinEquiv_apply_left, Fin.val_castAdd]
  · simp only [couplingColumnIndex, couplingOrder, Equiv.trans_apply, Equiv.sumCongr_apply,
      Sum.map_inr, finSumFinEquiv_apply_right, Fin.val_natAdd]

omit [DecidableEq n] [Fintype n] in
/-- The selected simulation rounds are strictly increasing in their enumerated order. -/
private theorem strictMono_couplingRound_order {q p : ℕ}
    {alg : QueryAlgorithm (n → ℝ) ((n → ℝ) × (n → ℝ)) q (Matrix n k ℝ)}
    {pass : ℕ → ℕ} (hpass : alg.IsPassStructured pass) (hp : ∀ j < q, pass j < p) :
    StrictMono (fun j : Fin (q + Fintype.card k) =>
      couplingRound (c := c) q p pass ((couplingOrder (k := k) q).symm j)) := by
  intro a b hab
  apply couplingRound_lt_of_columnIndex_lt hpass hp
  have hab' : (a : ℕ) < b := hab
  simpa only [couplingColumnIndex_eq_order, Equiv.apply_symm_apply] using hab'

/-- The coupling on the canonical space $(\mathbf{U}, \mathbf{Z})$ with the product law: a
measurable coupled block, jointly Gaussian with $\mathbf{U}^{\mathsf{H}}\mathbf{B}$ in product
form, and the depth inclusion almost surely. -/
private theorem exists_coupling_canonical {q p : ℕ}
    {alg : QueryAlgorithm (n → ℝ) ((n → ℝ) × (n → ℝ)) q (Matrix n k ℝ)} {pass : ℕ → ℕ}
    (hpass : alg.IsPassStructured pass) (hp : ∀ i < q, pass i < p) (halg : alg.IsMeasurable)
    (D : Matrix n n ℝ) (B : Matrix n c ℝ) :
    ∃ Gf : Matrix n n ℝ × Matrix n (Fin q ⊕ k) ℝ → Matrix n (Fin q ⊕ k) ℝ, Measurable Gf ∧
      ((haarFrame n n).prod (gaussianMatrix n (Fin q ⊕ k))).map (fun x => (x.1ᴴ * B, Gf x)) =
        ((haarFrame n n).map fun u => uᴴ * B).prod (gaussianMatrix n (Fin q ⊕ k)) ∧
      ∀ᵐ x ∂(haarFrame n n).prod (gaussianMatrix n (Fin q ⊕ k)),
        LinearMap.range (x.1ᴴ * alg.run (hiddenRotationOracle x.1 D)).mulVecLin ≤
          blockKrylovSpace D (Matrix.fromCols (x.1ᴴ * B) (Gf x)) (p + 1) := by
  classical
  let sim := couplingAlgorithm alg p pass D B
  let times := couplingRound (c := c) (k := k) q p pass
  have hsim : sim.IsMeasurable := measurable_couplingAlgorithm halg p pass D B
  have ht : ∀ a : Fin q ⊕ k, times a < couplingStart (c := c) q p + Fintype.card k :=
    fun a => (couplingRound_bounds (c := c) hp a).2
  have hcard : q + Fintype.card k = Fintype.card (Fin q ⊕ k) := by simp
  let e : Fin q ⊕ k ≃ Fin (Fintype.card (Fin q ⊕ k)) :=
    (couplingOrder (k := k) q).trans (finCongr hcard)
  have horder : ∀ a b, (e a).val < (e b).val → times a < times b := by
    intro a b hab
    apply couplingRound_lt_of_columnIndex_lt hpass hp
    change (couplingOrder (k := k) q a : ℕ) < couplingOrder (k := k) q b at hab
    simpa only [couplingColumnIndex_eq_order] using hab
  have hstartq : Fintype.card c ≤ couplingStart (c := c) q p + Fintype.card k := by
    unfold couplingStart
    omega
  let b := couplingInitialSummary (n := n) (c := c) (i := Fintype.card c)
  obtain ⟨Gf, hGm, hlaw, hcapture⟩ := exists_measurable_gaussianBlock_of_ordered_queries
    hsim times ht e horder hstartq (fun a => (couplingRound_bounds (c := c) hp a).1)
    b (measurable_couplingInitialSummary (n := n) (c := c) _)
  have hsummary (U : Matrix n n ℝ) :
      b ((sim.truncate (Fintype.card c)).transcript (twoSidedMulVec U)) = Uᴴ * B := by
    change couplingInitialSummary (c := c)
      ((sim.truncate (Fintype.card c)).history (twoSidedMulVec U) (Fintype.card c)) = _
    rw [QueryAlgorithm.history_truncate]
    exact couplingInitialSummary_history alg pass D B U le_rfl
  refine ⟨Gf, hGm, ?_, ?_⟩
  · simpa only [hsummary] using hlaw
  · filter_upwards [hcapture] with x hx
    apply range_output_le_blockKrylovSpace_of_captures hpass hp D B x.1 (Gf x)
    · intro j
      have hc := hx (Sum.inl j)
      change x.1ᴴ *ᵥ (sim.queryAt (twoSidedMulVec x.1)
        (couplingStart (c := c) q (pass j) + j)).2 ∈
          LinearMap.range (couplingRevealedAt sim x.1
            (couplingStart (c := c) q (pass j) + j)).mulVecLin ⊔
              LinearMap.range (Gf x).mulVecLin at hc
      have hquery := (couplingSimulation_queryAt alg pass D B (fun _ _ => 0)
        (fun h => alg.output (fun l => couplingDecode (c := c) q pass h l))
        hpass hp x.1 j j.isLt).1
      change sim.queryAt (twoSidedMulVec x.1)
        (couplingStart (c := c) q (pass j) + j) = _ at hquery
      rw [hquery] at hc
      exact hc
    · intro j
      have hc := hx (Sum.inr j)
      change x.1ᴴ *ᵥ (sim.queryAt (twoSidedMulVec x.1)
        (couplingStart (c := c) q p + Fintype.equivFin k j)).2 ∈
          LinearMap.range (couplingRevealedAt sim x.1
            (couplingStart (c := c) q p + Fintype.equivFin k j)).mulVecLin ⊔
              LinearMap.range (Gf x).mulVecLin at hc
      rw [couplingAlgorithm_queryAt_output hpass hp D B x.1 j] at hc
      exact hc

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
The construction first exposes the rotated initial block, then exposes all query directions of
each pass before its products. Each newly revealed direction is coupled with one Gaussian column
using its component outside the previously exposed subspace. A zero component uses an unchanged
independent Gaussian column. The output columns are exposed in the same way after the final pass.
Only the product phases increase the Krylov degree. -/
theorem QueryAlgorithm.IsPassStructured.exists_isKrylovCoupling_of_hasLaw_haarFrame {q p : ℕ}
    {alg : QueryAlgorithm (n → ℝ) ((n → ℝ) × (n → ℝ)) q (Matrix n k ℝ)} {pass : ℕ → ℕ}
    (hpass : alg.IsPassStructured pass) (hp : ∀ i < q, pass i < p) (halg : alg.IsMeasurable)
    (D : Matrix n n ℝ) (B : Matrix n c ℝ) {U : Ω → Matrix n n ℝ}
    (hU : HasLaw U (haarFrame n n) μ) {Z : Ω → Matrix n (Fin q ⊕ k) ℝ}
    (hZ : HasLaw Z (gaussianMatrix n (Fin q ⊕ k)) μ) (hUZ : IndepFun U Z μ) :
    ∃ G : Ω → Matrix n (Fin q ⊕ k) ℝ, IsKrylovCoupling μ D (p + 1) (fun ω => (U ω)ᴴ * B)
      (fun ω => (U ω)ᴴ * alg.run (hiddenRotationOracle (U ω) D)) G := by
  obtain ⟨Gf, hGm, hlaw, hae⟩ := exists_coupling_canonical hpass hp halg D B
  have := hU.isProbabilityMeasure
  have hUZm : AEMeasurable (fun ω => (U ω, Z ω)) μ := hU.aemeasurable.prodMk hZ.aemeasurable
  have hρ : μ.map (fun ω => (U ω, Z ω)) =
      (haarFrame n n).prod (gaussianMatrix n (Fin q ⊕ k)) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hU.aemeasurable hZ.aemeasurable).1 hUZ,
      hU.map_eq, hZ.map_eq]
  have hBm : Measurable fun x : Matrix n n ℝ × Matrix n (Fin q ⊕ k) ℝ => x.1ᴴ * B := by
    fun_prop
  have hpair : HasLaw (fun ω => ((U ω)ᴴ * B, Gf (U ω, Z ω)))
      (((haarFrame n n).map fun u => uᴴ * B).prod (gaussianMatrix n (Fin q ⊕ k))) μ := by
    have h1 : HasLaw (fun x : Matrix n n ℝ × Matrix n (Fin q ⊕ k) ℝ => (x.1ᴴ * B, Gf x))
        (((haarFrame n n).map fun u => uᴴ * B).prod (gaussianMatrix n (Fin q ⊕ k)))
        ((haarFrame n n).prod (gaussianMatrix n (Fin q ⊕ k))) :=
      ⟨(hBm.prodMk hGm).aemeasurable, hlaw⟩
    exact h1.comp ⟨hUZm, hρ⟩
  have hB : HasLaw (fun ω => (U ω)ᴴ * B) ((haarFrame n n).map fun u => uᴴ * B) μ :=
    measurePreserving_fst.hasLaw.comp hpair
  have : IsProbabilityMeasure ((haarFrame n n).map fun u : Matrix n n ℝ => uᴴ * B) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  have hG : HasLaw (fun ω => Gf (U ω, Z ω)) (gaussianMatrix n (Fin q ⊕ k)) μ :=
    (measurePreserving_snd (μ := (haarFrame n n).map fun u => uᴴ * B)).hasLaw.comp hpair
  refine ⟨fun ω => Gf (U ω, Z ω), hG, (indepFun_iff_hasLaw_prodMk_prod hB hG).2 hpair, ?_⟩
  rw [← hρ] at hae
  exact ae_of_ae_map hUZm hae

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
-/
theorem QueryAlgorithm.IsPassStructured.exists_isKrylovCoupling_mulVec_of_hasLaw_haarFrame
    {q p : ℕ} {alg : QueryAlgorithm (n → ℝ) (n → ℝ) q (Matrix n k ℝ)} {pass : ℕ → ℕ}
    (hpass : alg.IsPassStructured pass) (hp : ∀ i < q, pass i < p) (halg : alg.IsMeasurable)
    (D : Matrix n n ℝ) (B : Matrix n c ℝ) {U : Ω → Matrix n n ℝ}
    (hU : HasLaw U (haarFrame n n) μ) {Z : Ω → Matrix n (Fin q ⊕ k) ℝ}
    (hZ : HasLaw Z (gaussianMatrix n (Fin q ⊕ k)) μ) (hUZ : IndepFun U Z μ) :
    ∃ G : Ω → Matrix n (Fin q ⊕ k) ℝ, IsKrylovCoupling μ D (p + 1) (fun ω => (U ω)ᴴ * B)
      (fun ω => (U ω)ᴴ * alg.run (U ω * D * (U ω)ᴴ).mulVec) G := by
  obtain ⟨G, hG⟩ := (hpass.comapResponse Prod.fst).exists_isKrylovCoupling_of_hasLaw_haarFrame hp
    (halg.comapResponse measurable_fst) D B hU hZ hUZ
  refine ⟨G, ?_⟩
  have hfst : ∀ ω, (Prod.fst ∘ hiddenRotationOracle (U ω) D) = (U ω * D * (U ω)ᴴ).mulVec :=
    fun ω => rfl
  simpa only [QueryAlgorithm.run_comapResponse, hfst] using hG

end Coupling

end NLAlib
