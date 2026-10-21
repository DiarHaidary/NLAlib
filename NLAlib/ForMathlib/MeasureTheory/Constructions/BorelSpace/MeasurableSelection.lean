/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Topology.Maps.Proper.Basic
public import NLAlib.ForMathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Measurable selection from a closed set with locally compact sections

Let $S \subseteq X \times Y$ be closed, with sections $S_x = \{y \mid (x, y) \in S\}$ lying locally
uniformly inside compact sets, and $Y$ a finite-dimensional real topological vector space. Then
the map sending $x$ to the lexicographically least point of $S_x$ (in the coordinates of a basis)
is Borel measurable, and so a closed set with nonempty sections of this kind has a measurable
section. This is the case of the Kuratowski–Ryll-Nardzewski selection theorem that best
approximations and singular value decompositions need, with a canonical selection and a proof by
closed sets only: for each coordinate, the set of $x$ where the least value is at most $t$ is a
countable intersection of projections of closed sets, closed because the sections lie in compact
sets (a tube argument). The general theorem, for weakly measurable closed-valued correspondences
into a Polish space, needs completeness of $Y$; this form does not, the compact bound supplying the
limits. Upstream candidate; Mathlib has no measurable selection theorem (see the comment in
`Mathlib.Probability.Decision.BayesEstimator`).

## Main results

* `IsClosed.measurable_of_forall_toLex_equivFun_le`: the lexicographically least selection is
  measurable.
* `IsClosed.exists_measurable_forall_prodMk_mem`: a measurable selection exists.
-/

@[expose] public section

open Filter Module Set Topology

/-- If one tuple is lexicographically below another and above it at every index before $i$, it is
below it at $i$. -/
private theorem Pi.apply_le_of_toLex_le {N : ℕ} {a b : Fin N → ℝ} (h : toLex a ≤ toLex b)
    {i : Fin N} (hi : ∀ j < i, b j ≤ a j) : a i ≤ b i := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨j₀, hj₀, hmin⟩ := WellFounded.has_min wellFounded_lt {j | a j ≠ b j} ⟨i, hlt.ne'⟩
  have hj₀i : j₀ ≤ i := not_lt.mp fun hij => hmin i hlt.ne' hij
  have hlt₀ : b j₀ < a j₀ := by
    rcases hj₀i.lt_or_eq with hj | hj
    · exact lt_of_le_of_ne (hi j₀ hj) (Ne.symm hj₀)
    · exact hj ▸ hlt
  have hba : toLex b < toLex a :=
    ⟨j₀, fun j hj => (not_not.mp fun hne => hmin j (Ne.symm hne) hj), hlt₀⟩
  exact lt_irrefl _ (h.trans_lt hba)

/-- **The tube argument.** If $S \subseteq X \times Y$ is closed with sections lying locally inside
compact sets and $C \subseteq Z \times Y$ is closed, the set of $(x, z)$ for which some $y$ has
$(x, y) \in S$ and $(z, y) \in C$ is closed. -/
private theorem IsClosed.isClosed_setOf_exists_mem_and_mem {X Y Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] {S : Set (X × Y)} (hS : IsClosed S)
    (hK : ∀ x, ∃ U ∈ 𝓝 x, ∃ K : Set Y, IsCompact K ∧ ∀ x' ∈ U, ∀ y, (x', y) ∈ S → y ∈ K)
    {C : Set (Z × Y)} (hC : IsClosed C) :
    IsClosed {p : X × Z | ∃ y, (p.1, y) ∈ S ∧ (p.2, y) ∈ C} := by
  refine isOpen_compl_iff.mp (isOpen_iff_mem_nhds.mpr fun p hp => ?_)
  obtain ⟨x, z⟩ := p
  obtain ⟨U, hU, K, hKc, hUK⟩ := hK x
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  let T : Set ((X × Z) × K) := {q | (q.1.1, (q.2 : Y)) ∈ S ∧ (q.1.2, (q.2 : Y)) ∈ C}
  have hT : IsClosed T :=
    (hS.preimage (by fun_prop)).inter (hC.preimage (by fun_prop))
  have hF : IsClosed (Prod.fst '' T) := isClosedMap_fst_of_compactSpace T hT
  have hpF : (x, z) ∉ Prod.fst '' T := by
    rintro ⟨q, hq, hqp⟩
    exact hp ⟨q.2, hqp ▸ hq.1, hqp ▸ hq.2⟩
  filter_upwards [hF.isOpen_compl.mem_nhds hpF, prod_mem_nhds hU univ_mem] with p hpF' hpU hpW
  obtain ⟨y, hyS, hyC⟩ := hpW
  exact hpF' ⟨(p, ⟨y, hUK p.1 hpU.1 y hyS⟩), ⟨hyS, hyC⟩, rfl⟩

variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
  [ContinuousSMul ℝ Y] [T2Space Y] {S : Set (X × Y)}

/-- The $i$-th coordinate of the lexicographically least selection is measurable once the earlier
ones are: the set where it is at most $t$ is the intersection over $n$ of the sets of $x$ for which
some $y \in S_x$ has its earlier coordinates within $1/(n+1)$ of the least ones and its $i$-th at
most $t$, each the preimage of a closed set. -/
private theorem IsClosed.measurable_equivFun_apply_of_forall_lt {N : ℕ} (b : Basis (Fin N) ℝ Y)
    (hS : IsClosed S)
    (hK : ∀ x, ∃ U ∈ 𝓝 x, ∃ K : Set Y, IsCompact K ∧ ∀ x' ∈ U, ∀ y, (x', y) ∈ S → y ∈ K)
    {f : X → Y} (hf : ∀ x, (x, f x) ∈ S ∧
      ∀ y, (x, y) ∈ S → toLex (b.equivFun (f x)) ≤ toLex (b.equivFun y))
    (i : Fin N) (hprev : ∀ j < i, Measurable fun x => b.equivFun (f x) j) :
    Measurable fun x => b.equivFun (f x) i := by
  have hc : Continuous fun y : Y => b.equivFun y := continuous_equivFun_basis b
  refine measurable_of_Iic fun t => ?_
  let C : Set ((Fin N → ℝ) × Y) :=
    {q | (∀ j, j < i → b.equivFun q.2 j ≤ q.1 j) ∧ b.equivFun q.2 i ≤ t}
  have hC : IsClosed C := by
    refine IsClosed.inter ?_
      (_root_.isClosed_le ((continuous_apply i).comp (hc.comp continuous_snd)) continuous_const)
    change IsClosed {q : (Fin N → ℝ) × Y | ∀ j, j < i → b.equivFun q.2 j ≤ q.1 j}
    rw [ofPred_forall]
    refine isClosed_iInter fun j => ?_
    by_cases hj : j < i
    · simp only [hj, forall_true_left]
      exact _root_.isClosed_le ((continuous_apply j).comp (hc.comp continuous_snd))
        ((continuous_apply j).comp continuous_fst)
    · simp only [hj, false_imp_iff, ofPred_true, isClosed_univ]
  have hH := hS.isClosed_setOf_exists_mem_and_mem hK hC
  let v : ℕ → X → Fin N → ℝ := fun k x j =>
    if j < i then b.equivFun (f x) j + 1 / ((k : ℝ) + 1) else 0
  have hv : ∀ k, Measurable (v k) := fun k => measurable_pi_lambda _ fun j => by
    by_cases hj : j < i
    · simp only [v, hj, if_true]
      exact (hprev j hj).add_const _
    · simp only [v, hj, if_false]
      exact measurable_const
  have hset : (fun x => b.equivFun (f x) i) ⁻¹' Iic t =
      ⋂ k : ℕ, (fun x => (x, v k x)) ⁻¹'
        {p : X × (Fin N → ℝ) | ∃ y, (p.1, y) ∈ S ∧ (p.2, y) ∈ C} := by
    ext x
    simp only [mem_preimage, mem_Iic, mem_iInter, mem_ofPred_eq, C, v]
    constructor
    · intro hx k
      refine ⟨f x, (hf x).1, fun j hj => ?_, hx⟩
      rw [if_pos hj]
      exact le_add_of_nonneg_right (by positivity)
    · intro hx
      obtain ⟨U, hU, K, hKc, hUK⟩ := hK x
      let T : ℕ → Set Y := fun k => {y | (x, y) ∈ S ∧
        (∀ j, j < i → b.equivFun y j ≤ b.equivFun (f x) j + 1 / ((k : ℝ) + 1)) ∧
          b.equivFun y i ≤ t}
      have hTcl : ∀ k, IsClosed (T k) := fun k => by
        refine (hS.preimage (continuous_const.prodMk continuous_id)).inter (IsClosed.inter ?_
          (_root_.isClosed_le ((continuous_apply i).comp hc) continuous_const))
        change IsClosed {y | ∀ j, j < i → b.equivFun y j ≤ b.equivFun (f x) j + 1 / ((k : ℝ) + 1)}
        simp only [ofPred_forall]
        exact isClosed_iInter fun j => isClosed_iInter fun _ =>
          _root_.isClosed_le ((continuous_apply j).comp hc) continuous_const
      have hTd : ∀ k, T (k + 1) ⊆ T k := by
        intro k y ⟨hyS, hyj, hyi⟩
        refine ⟨hyS, fun j hj => (hyj j hj).trans (add_le_add_right ?_ _), hyi⟩
        push_cast
        gcongr
        linarith
      have hTn : ∀ k, (T k).Nonempty := fun k => by
        obtain ⟨y, hyS, hyj, hyi⟩ := hx k
        exact ⟨y, hyS, fun j hj => by simpa only [if_pos hj] using hyj j hj, hyi⟩
      have hT0 : IsCompact (T 0) :=
        hKc.of_isClosed_subset (hTcl 0) fun y hy => hUK x (mem_of_mem_nhds hU) y hy.1
      obtain ⟨y, hy⟩ :=
        IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed T hTd hTn hT0 hTcl
      rw [mem_iInter] at hy
      have hyj : ∀ j < i, b.equivFun y j ≤ b.equivFun (f x) j := by
        intro j hj
        refine le_of_forall_pos_lt_add fun ε hε => ?_
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
        exact ((hy k).2.1 j hj).trans_lt (by linarith)
      exact (Pi.apply_le_of_toLex_le ((hf x).2 y (hy 0).1) hyj).trans (hy 0).2.2
  rw [hset]
  exact MeasurableSet.iInter fun k => (measurable_id.prodMk (hv k)) hH.measurableSet

/-- **The lexicographically least selection is measurable.** Let $S \subseteq X \times Y$ be
closed with sections $S_x$ lying locally uniformly inside compact sets (each $x$ has a
neighbourhood $U$ and a compact $K$ with $S_{x'} \subseteq K$ for $x' \in U$), $Y$ a
finite-dimensional real topological vector space with a basis. If $f(x) \in S_x$ has
lexicographically least coordinates in $S_x$ for every $x$, then $f$ is Borel measurable.
The local compact bound cannot be weakened to compact sections without the projection theorems of
descriptive set theory (Novikov, Arsenin–Kunugui). Upstream candidate.
[KuratowskiRyllNardzewski1965]; [Kechris1995, Theorem 12.13]; there an arbitrary measurable
selection for weakly measurable closed-valued correspondences into a Polish space, here the
canonical one for a closed set with locally compact sections. -/
theorem IsClosed.measurable_of_forall_toLex_equivFun_le [MeasurableSpace Y] [BorelSpace Y]
    {N : ℕ} (b : Basis (Fin N) ℝ Y) (hS : IsClosed S)
    (hK : ∀ x, ∃ U ∈ 𝓝 x, ∃ K : Set Y, IsCompact K ∧ ∀ x' ∈ U, ∀ y, (x', y) ∈ S → y ∈ K)
    {f : X → Y} (hf : ∀ x, (x, f x) ∈ S ∧
      ∀ y, (x, y) ∈ S → toLex (b.equivFun (f x)) ≤ toLex (b.equivFun y)) :
    Measurable f := by
  have hg : Measurable fun x => b.equivFun (f x) := by
    refine measurable_pi_iff.mpr fun i => ?_
    induction i using WellFoundedLT.induction with
    | ind i ih => exact hS.measurable_equivFun_apply_of_forall_lt b hK hf i ih
  have hsymm : Continuous (b.equivFun.symm : (Fin N → ℝ) → Y) :=
    LinearMap.continuous_of_finiteDimensional b.equivFun.symm.toLinearMap
  have hfg : f = fun x => b.equivFun.symm (b.equivFun (f x)) :=
    funext fun x => (b.equivFun.symm_apply_apply (f x)).symm
  rw [hfg]
  exact hsymm.measurable.comp hg

/-- **Measurable selection from a closed set with compact sections**: let $X$ be a topological
space whose open sets are measurable, $Y$ a finite-dimensional Hausdorff real topological vector
space with its Borel $\sigma$-algebra, and $S \subseteq X \times Y$ closed with every section
$S_x = \{y \mid (x, y) \in S\}$ nonempty and the sections lying locally uniformly inside compact
sets (each $x$ has a neighbourhood $U$ and a compact $K$ with $S_{x'} \subseteq K$ for
$x' \in U$). Then there is a Borel measurable $f : X \to Y$ with $(x, f(x)) \in S$ for every $x$
(the lexicographically least point of each section, in the coordinates of a basis, measurable
by `IsClosed.measurable_of_forall_toLex_equivFun_le`). Upstream candidate.
[KuratowskiRyllNardzewski1965]; [Kechris1995, Theorem 12.13]; there for weakly measurable
closed-valued correspondences into a Polish space, here a closed set with locally compact
sections in a finite-dimensional space.
Result: measurable-selection -/
theorem IsClosed.exists_measurable_forall_prodMk_mem [FiniteDimensional ℝ Y] [MeasurableSpace Y]
    [BorelSpace Y] (hS : IsClosed S) (hne : ∀ x, ∃ y, (x, y) ∈ S)
    (hK : ∀ x, ∃ U ∈ 𝓝 x, ∃ K : Set Y, IsCompact K ∧ ∀ x' ∈ U, ∀ y, (x', y) ∈ S → y ∈ K) :
    ∃ f : X → Y, Measurable f ∧ ∀ x, (x, f x) ∈ S := by
  let b := Module.finBasis ℝ Y
  have hsel : ∀ x, ∃ y, (x, y) ∈ S ∧
      ∀ y', (x, y') ∈ S → toLex (b.equivFun y) ≤ toLex (b.equivFun y') := by
    intro x
    obtain ⟨U, hU, K, hKc, hUK⟩ := hK x
    have hc : IsCompact {y | (x, y) ∈ S} :=
      hKc.of_isClosed_subset (hS.preimage (continuous_const.prodMk continuous_id))
        fun y hy => hUK x (mem_of_mem_nhds hU) y hy
    obtain ⟨y, hy, hmin⟩ := hc.exists_forall_toLex_equivFun_le b (hne x)
    exact ⟨y, hy, hmin⟩
  choose f hf using hsel
  exact ⟨f, hS.measurable_of_forall_toLex_equivFun_le b hK hf, fun x => (hf x).1⟩
