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

A distributional JL tail at $\varepsilon$ makes any sketch $\mathbf{S}$ a subspace embedding with
constants $1 \mp 2\varepsilon$ of a fixed $\mathbf{U}$ with orthonormal columns, failing with
probability at most $9^{D} \delta$, $D = \lvert p \rvert \dim_{\mathbb{R}} \Bbbk$ the real
dimension of $\Bbbk^p$: on a $1/4$-net of the unit sphere of $\Bbbk^p$
(`NLAlib.exists_finset_specNorm_le_div_of_isHermitian`, at most $9^{D}$ points), the Hermitian
error $\mathbf{E} = (\mathbf{S}\mathbf{U})^{\mathsf{H}} (\mathbf{S}\mathbf{U}) - \mathbf{I}$ has
$\lvert \operatorname{Re} \mathbf{x}^{\mathsf{H}} \mathbf{E} \mathbf{x} \rvert
= \lvert \|\mathbf{S}\mathbf{U}\mathbf{x}\|^2 - 1 \rvert < \varepsilon$ off the union of the JL
events, hence $\|\mathbf{E}\|_2 < 2\varepsilon$. The real dimension is $\lvert p \rvert$ over
$\mathbb{R}$ and $2 \lvert p \rvert$ over $\mathbb{C}$, so the factor is $9^{\lvert p \rvert}$
and $81^{\lvert p \rvert}$. Any later family with a JL tail and no Gram-level tail gets its OSE
here.

Degenerate cases: for empty $p$ every sketch is an embedding (the case split the proof starts
with, `docs/design/Sketching-S3.md` §8, item 6); for $\varepsilon \le 0$ and nonempty $p$ the JL
hypothesis bounds the whole space. No hypothesis on $\varepsilon$; $\delta \ge 0$ is needed for
the union bound over an empty net and for `mono`.

This file is Sketching stage S3's (`docs/design/Sketching-S3.md` §3.1). At the
wrap-up it merges into `NLAlib/Sketching/Properties/JohnsonLindenstrauss.lean`.

## Main results

* `NLAlib.HasJLProperty.hasSubspaceEmbedding`: JL plus a net, for a fixed $\mathbf{U}$.
* `NLAlib.HasJLProperty.isObliviousSubspaceEmbedding`: the oblivious form.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {k n p : Type*} [Fintype k] [Fintype n] {S : Ω → Matrix k n 𝕜} {ε δ : ℝ}

/-- A finite family of reals below $s > 0$ has a common bound $M$ with $0 \le M < s$. -/
private theorem exists_le_lt_of_forall_lt {ι : Type*} (N : Finset ι) (f : ι → ℝ) {s : ℝ}
    (hs : 0 < s) (h : ∀ i ∈ N, f i < s) : ∃ M, 0 ≤ M ∧ M < s ∧ ∀ i ∈ N, f i ≤ M := by
  classical
  refine ⟨(insert 0 (N.image f)).max' (Finset.insert_nonempty _ _),
    Finset.le_max' _ _ (Finset.mem_insert_self _ _), ?_, fun i hi => Finset.le_max' _ _
      (Finset.mem_insert_of_mem (Finset.mem_image_of_mem f hi))⟩
  rw [Finset.max'_lt_iff]
  intro y hy
  rcases Finset.mem_insert.mp hy with rfl | hy
  · exact hs
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    exact h i hi

/-- A matrix with orthonormal columns preserves the Euclidean norm. -/
private theorem norm_mulVec_of_hasOrthonormalCols [Fintype p] [DecidableEq p]
    {U : Matrix n p 𝕜} (hU : HasOrthonormalCols U) (x : p → 𝕜) :
    ‖WithLp.toLp 2 (U *ᵥ x)‖ = ‖WithLp.toLp 2 x‖ := by
  have h := quadForm_conjTranspose_mul_self U x
  rw [hU.conjTranspose_mul_self, quadForm_one] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1
    (RCLike.ofReal_injective h).symm

/-- The quadratic form of the Gram error of $\mathbf{A}\mathbf{U}$ at $\mathbf{x}$ is the
distortion of $\mathbf{U}\mathbf{x}$:
$\operatorname{Re} \mathbf{x}^{\mathsf{H}} \bigl((\mathbf{A}\mathbf{U})^{\mathsf{H}}
(\mathbf{A}\mathbf{U}) - \mathbf{I}\bigr) \mathbf{x}
= \|\mathbf{A}\mathbf{U}\mathbf{x}\|^2 - \|\mathbf{x}\|^2$. -/
private theorem re_quadForm_gram_sub_one [Fintype p] [DecidableEq p] (U : Matrix n p 𝕜)
    (A : Matrix k n 𝕜) (x : p → 𝕜) :
    RCLike.re (quadForm ((A * U)ᴴ * (A * U) - 1) x) =
      ‖WithLp.toLp 2 (A *ᵥ (U *ᵥ x))‖ ^ 2 - ‖WithLp.toLp 2 x‖ ^ 2 := by
  rw [quadForm_sub_left, map_sub, quadForm_conjTranspose_mul_self, quadForm_one,
    RCLike.ofReal_re, RCLike.ofReal_re, Matrix.mulVec_mulVec]

/-- **JL plus a net**: a JL tail at $\varepsilon$ with failure probability $\delta \ge 0$, under a
finite measure, makes $\mathbf{S}$ a subspace embedding of a fixed $\mathbf{U}$ with orthonormal
columns with constants $1 \mp 2\varepsilon$, failing with probability at most
$9^{\lvert p \rvert \dim_{\mathbb{R}} \Bbbk} \delta$.
[Vershynin2018, proof of Theorem 4.6.1, (4.22) (2020 draft)]; [Woodruff2014, Lemma 5 and
Theorem 6], there with a $1/2$-net and $O(\varepsilon)$. The net has radius $1/4$; another radius
gives an incomparable family in the radius, to be added when wanted. -/
theorem HasJLProperty.hasSubspaceEmbedding [IsFiniteMeasure μ] [Fintype p] [DecidableEq p]
    {U : Matrix n p 𝕜} (h : HasJLProperty S ε δ μ) (hδ : 0 ≤ δ) (hU : HasOrthonormalCols U) :
    HasSubspaceEmbedding S U (1 - 2 * ε) (1 + 2 * ε)
      (9 ^ (Fintype.card p * Module.finrank ℝ 𝕜) * δ) μ := by
  rcases isEmpty_or_nonempty p with hp | hp
  · have hall : ∀ ω, IsSubspaceEmbedding (S ω) U (1 - 2 * ε) (1 + 2 * ε) := fun ω =>
      ⟨by unfold IsSubspaceInjection; exact le_of_eq (Subsingleton.elim _ _),
        le_of_eq (Subsingleton.elim _ _)⟩
    unfold HasSubspaceEmbedding
    simp only [hall, not_true_eq_false, Set.ofPred_false, measureReal_empty]
    positivity
  have h9 : (1 : ℝ) ≤ 9 ^ (Fintype.card p * Module.finrank ℝ 𝕜) := one_le_pow₀ (by norm_num)
  obtain ⟨x₀⟩ := hp
  rcases le_or_gt ε 0 with hε | hε
  · -- the JL event at any unit vector is everything
    have hx₀ : ‖WithLp.toLp 2 (U *ᵥ Pi.single x₀ (1 : 𝕜))‖ = 1 := by
      rw [norm_mulVec_of_hasOrthonormalCols hU, PiLp.toLp_single, PiLp.norm_single, norm_one]
    have huniv := h _ hx₀
    have e : {ω | ε ≤ |‖WithLp.toLp 2 (S ω *ᵥ (U *ᵥ Pi.single x₀ (1 : 𝕜)))‖ ^ 2 - 1|} =
        Set.univ := Set.eq_univ_of_forall fun ω => hε.trans (abs_nonneg _)
    rw [e] at huniv
    unfold HasSubspaceEmbedding
    calc _ ≤ μ.real Set.univ := measureReal_mono (Set.subset_univ _)
      _ ≤ δ := huniv
      _ ≤ _ := le_mul_of_one_le_left hδ h9
  obtain ⟨net, hcard, hunit, hnet⟩ :=
    exists_finset_specNorm_le_div_of_isHermitian 𝕜 p (ε := 1 / 4) (by norm_num) (by norm_num)
  rw [finrank_real_fun] at hcard
  norm_num at hcard
  refine hU.hasSubspaceEmbedding_of_measureReal_le ?_
  have hsub : {ω | 2 * ε ≤ specNorm ((S ω * U)ᴴ * (S ω * U) - 1)} ⊆
      ⋃ x ∈ net, {ω | ε ≤ |‖WithLp.toLp 2 (S ω *ᵥ (U *ᵥ x))‖ ^ 2 - 1|} := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_le] at hnot hω
    obtain ⟨M, hM0, hMε, hM⟩ := exists_le_lt_of_forall_lt net
      (fun x => |‖WithLp.toLp 2 (S ω *ᵥ (U *ᵥ x))‖ ^ 2 - 1|) hε hnot
    have hH : ((S ω * U)ᴴ * (S ω * U) - 1).IsHermitian :=
      (Matrix.isHermitian_conjTranspose_mul_self _).sub Matrix.isHermitian_one
    have hn := hnet _ hH hM0 fun x hx => by
      rw [re_quadForm_gram_sub_one, hunit x hx, one_pow]
      exact hM x hx
    rw [show M / (1 - 2 * (1 / 4 : ℝ)) = 2 * M by ring] at hn
    linarith
  calc μ.real {ω | 2 * ε ≤ specNorm ((S ω * U)ᴴ * (S ω * U) - 1)}
    _ ≤ μ.real (⋃ x ∈ net, {ω | ε ≤ |‖WithLp.toLp 2 (S ω *ᵥ (U *ᵥ x))‖ ^ 2 - 1|}) :=
      measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ x ∈ net, μ.real {ω | ε ≤ |‖WithLp.toLp 2 (S ω *ᵥ (U *ᵥ x))‖ ^ 2 - 1|} :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _x ∈ net, δ := Finset.sum_le_sum fun x hx =>
      h _ (by rw [norm_mulVec_of_hasOrthonormalCols hU, hunit x hx])
    _ = net.card * δ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by gcongr

/-- **JL plus a net, oblivious form**: a JL tail at $\varepsilon$ with failure probability
$\delta \ge 0$, under a finite measure, makes $\mathbf{S}$ an oblivious subspace embedding for
dimension $d$ with constants $1 \mp 2\varepsilon$ and failure probability
$9^{d \dim_{\mathbb{R}} \Bbbk} \delta$. From `NLAlib.HasJLProperty.hasSubspaceEmbedding` at
`Fin (min d (card n))` by `NLAlib.IsObliviousSubspaceEmbedding.of_hasOrthonormalCols` and `mono`.
[Vershynin2018, proof of Theorem 4.6.1, (4.22) (2020 draft)]; [Woodruff2014, Theorem 6]. -/
theorem HasJLProperty.isObliviousSubspaceEmbedding [IsFiniteMeasure μ]
    (h : HasJLProperty S ε δ μ) (hδ : 0 ≤ δ) (d : ℕ) :
    IsObliviousSubspaceEmbedding S d (1 - 2 * ε) (1 + 2 * ε)
      (9 ^ (d * Module.finrank ℝ 𝕜) * δ) μ := by
  have hd : Fintype.card (Fin (min d (Fintype.card n))) ≤ Fintype.card n := by
    rw [Fintype.card_fin]; exact min_le_right _ _
  have h' := IsObliviousSubspaceEmbedding.of_hasOrthonormalCols hd
    fun U hU => h.hasSubspaceEmbedding hδ hU
  rw [Fintype.card_fin] at h'
  intro U hU
  refine (h' U (le_min hU (Matrix.rank_le_card_width U))).mono le_rfl le_rfl ?_
  gcongr
  · norm_num
  · exact min_le_left _ _

end NLAlib
