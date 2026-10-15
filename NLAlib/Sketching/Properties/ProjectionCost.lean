/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Norms.Projector
public import NLAlib.Sketching.Properties.SubspaceEmbedding

/-!
# Projection-cost-preserving sketches

For $\mathbf{A} \in \Bbbk^{m \times n}$, a matrix $\tilde{\mathbf{A}} \in \Bbbk^{m \times l}$ with
the same rows, for instance a sketch $\mathbf{A}\mathbf{\Omega}$, is a *rank-$k$
projection-cost-preserving sketch* of $\mathbf{A}$ with constants $a$, $b$ when, up to one offset
$c \ge 0$ that does not depend on the projector, the cost
$\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{\mathsf{F}}^2$ of every orthogonal projector $\mathbf{P}$ of
rank at most $k$ is preserved:
$$a\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{\mathsf{F}}^2 \le
\|\tilde{\mathbf{A}} - \mathbf{P}\tilde{\mathbf{A}}\|_{\mathsf{F}}^2 + c \le
b\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{\mathsf{F}}^2\,.$$
The literature's $\varepsilon$ is $a = 1 - \varepsilon$, $b = 1 + \varepsilon$ (two-sided) or
$a = 1$ (one-sided), written so. A projector that is nearly optimal for the sketch is then nearly
optimal for $\mathbf{A}$ (`NLAlib.IsProjectionCostPreserving.mul_frobNorm_sub_mul_sq_le`), which is
how a constrained low-rank problem (a set of rank-$k$ projectors, $k$-means) is solved on a sketch.
A subspace embedding of the row space of $\mathbf{A}$ gives one for every $k$ with offset $0$.

Degenerate cases: for $a \le 0$ the lower half holds automatically and the consequence is vacuous;
at $k = 0$ the only projector is $\mathbf{0}$ and the predicate is a scaled preservation of
$\|\mathbf{A}\|_{\mathsf{F}}^2$; for $k \ge \lvert m \rvert$ the projector $\mathbf{I}$ forces
$c = 0$. Design: `docs/design/LowRank-S2b.md` §3.2, §8.

## Main definitions

* `NLAlib.IsProjectionCostPreserving A Ã k a b`: the predicate.

## Main results

* `NLAlib.IsProjectionCostPreserving.mono`: monotonicity in the rank and the constants.
* `NLAlib.IsSubspaceEmbedding.isProjectionCostPreserving`: a subspace embedding of the row space
  is a projection-cost-preserving sketch for every rank.
* `NLAlib.IsProjectionCostPreserving.mul_frobNorm_sub_mul_sq_le`: constrained low-rank
  approximation through the sketch.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]

/-- $\tilde{\mathbf{A}}$ is a **rank-$k$ projection-cost-preserving sketch** of $\mathbf{A}$ with
constants $a$, $b$: for some offset $c \ge 0$, independent of the projector, every orthogonal
projector $\mathbf{P}$ of rank at most $k$ has
$$a\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{\mathsf{F}}^2 \le
\|\tilde{\mathbf{A}} - \mathbf{P}\tilde{\mathbf{A}}\|_{\mathsf{F}}^2 + c \le
b\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{\mathsf{F}}^2\,.$$
The two-sided form is $a = 1 - \varepsilon$, $b = 1 + \varepsilon$; the one-sided form is $a = 1$.
The sketch $\tilde{\mathbf{A}}$ is any matrix with the rows of $\mathbf{A}$, not only
$\mathbf{A}\mathbf{\Omega}$.
[CohenElderMuscoMuscoPersu2015, Definitions 1 and 2]; there over $\mathbb{R}$, with $\varepsilon$,
and for projectors of rank exactly $k$; here constants $a$, $b$, any `RCLike` field, rank at most
$k$, so that projectors of smaller rank (a rank-deficient truncation) are covered.
Result: projection-cost-preserving-sketch -/
def IsProjectionCostPreserving (A : Matrix m n 𝕜) (Ã : Matrix m l 𝕜) (k : ℕ) (a b : ℝ) : Prop :=
  ∃ c : ℝ, 0 ≤ c ∧ ∀ P : Matrix m m 𝕜, IsStarProjection P → P.rank ≤ k →
    a * frobNorm (A - P * A) ^ 2 ≤ frobNorm (Ã - P * Ã) ^ 2 + c ∧
      frobNorm (Ã - P * Ã) ^ 2 + c ≤ b * frobNorm (A - P * A) ^ 2

/-- A projection-cost-preserving sketch of rank $k$ with constants $a$, $b$ is one of every rank
$k' \le k$ with every $a' \le a$ and $b' \ge b$. -/
theorem IsProjectionCostPreserving.mono {A : Matrix m n 𝕜} {Ã : Matrix m l 𝕜} {k k' : ℕ}
    {a a' b b' : ℝ} (h : IsProjectionCostPreserving A Ã k a b) (hk : k' ≤ k) (ha : a' ≤ a)
    (hb : b ≤ b') : IsProjectionCostPreserving A Ã k' a' b' := by
  obtain ⟨c, hc, h⟩ := h
  refine ⟨c, hc, fun P hP hPk => ?_⟩
  obtain ⟨h₁, h₂⟩ := h P hP (hPk.trans hk)
  have hx := sq_nonneg (frobNorm (A - P * A))
  exact ⟨(mul_le_mul_of_nonneg_right ha hx).trans h₁,
    h₂.trans (mul_le_mul_of_nonneg_right hb hx)⟩

/-- A subspace embedding for $\operatorname{range}\mathbf{U}$ bounds the squared Frobenius norm of
every $\mathbf{U}\mathbf{C}$ from both sides, column by column. -/
private theorem frobNorm_sq_le_and_le_of_isSubspaceEmbedding {q : Type*} [Fintype q]
    {S : Matrix l n 𝕜} {U : Matrix n m 𝕜} {a b : ℝ} (h : IsSubspaceEmbedding S U a b)
    (C : Matrix m q 𝕜) :
    a * frobNorm (U * C) ^ 2 ≤ frobNorm (S * (U * C)) ^ 2 ∧
      frobNorm (S * (U * C)) ^ 2 ≤ b * frobNorm (U * C) ^ 2 := by
  have hv := isSubspaceEmbedding_iff_forall_mem_range.mp h
  have hcol : ∀ j, (U * C).col j ∈ LinearMap.range U.mulVecLin := fun j =>
    ⟨C.col j, by
      ext i
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec, Matrix.col_apply, Matrix.mul_apply,
        dotProduct]⟩
  have hS : ∀ j, (S * (U * C)).col j = S *ᵥ (U * C).col j := fun j => by
    ext i
    simp only [Matrix.mulVec, Matrix.col_apply, Matrix.mul_apply, dotProduct]
  rw [frobNorm_sq_eq_sum_col, frobNorm_sq_eq_sum_col, Finset.mul_sum, Finset.mul_sum]
  simp only [hS]
  exact ⟨Finset.sum_le_sum fun j _ => (hv _ (hcol j)).1,
    Finset.sum_le_sum fun j _ => (hv _ (hcol j)).2⟩

/-- **A subspace embedding of the row space is a projection-cost-preserving sketch** for every
rank, with offset $0$: if $\mathbf{\Omega}^{\mathsf{H}}$ is a subspace embedding for
$\operatorname{range}\mathbf{A}^{\mathsf{H}}$ with constants $a$, $b$, then
$\mathbf{A}\mathbf{\Omega}$ is a rank-$k$ projection-cost-preserving sketch of $\mathbf{A}$ with
the same constants, for every $k$. The bound holds for every left factor, not only the complement
of a projector, which is why $k$ is free; the embedding dimension is at least
$\operatorname{rank}\mathbf{A}$.
[CohenElderMuscoMuscoPersu2015, §1.1]; [Woodruff2014, proof of Theorem 61]; there a remark and a
proof step, in Woodruff transposed (his column space of $\mathbf{A}$ is the row space here); here
every $k$, offset $0$ and the embedding's constants carried over. -/
theorem IsSubspaceEmbedding.isProjectionCostPreserving {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜}
    {a b : ℝ} (h : IsSubspaceEmbedding Ωᴴ Aᴴ a b) (k : ℕ) :
    IsProjectionCostPreserving A (A * Ω) k a b := by
  classical
  refine ⟨0, le_rfl, fun P _ _ => ?_⟩
  have e₁ : A - P * A = (Aᴴ * (1 - P)ᴴ)ᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_conjTranspose, Matrix.sub_mul, Matrix.one_mul]
  have e₂ : A * Ω - P * (A * Ω) = (Ωᴴ * (Aᴴ * (1 - P)ᴴ))ᴴ := by
    rw [Matrix.conjTranspose_mul, ← e₁, Matrix.conjTranspose_conjTranspose, Matrix.sub_mul,
      Matrix.mul_assoc]
  rw [add_zero, e₁, e₂, frobNorm_conjTranspose, frobNorm_conjTranspose]
  exact frobNorm_sq_le_and_le_of_isSubspaceEmbedding h _

/-- **Constrained low-rank approximation through a projection-cost-preserving sketch.** If
$\mathbf{P}$ is $\gamma$-optimal for the sketch against a competitor $\mathbf{P}'$, both orthogonal
projectors of rank at most $k$ and $\gamma \ge 1$, then it is $\gamma b / a$-optimal for
$\mathbf{A}$:
$$a\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{\mathsf{F}}^2 \le
\gamma\, b\,\|\mathbf{A} - \mathbf{P}'\mathbf{A}\|_{\mathsf{F}}^2\,.$$
In the two-sided form the factor is $\gamma(1+\varepsilon)/(1-\varepsilon)$. The multiplied form
needs no $a > 0$ and is vacuous for $a \le 0$.
[CohenElderMuscoMuscoPersu2015, Lemmas 3 and 4]; there for the minimizer over a set of rank-$k$
projectors and the factors $(1+\varepsilon)/(1-\varepsilon)$ or $1 + \varepsilon$; here any
competitor and constants $a$, $b$.
Result: projection-cost-preserving-sketch -/
theorem IsProjectionCostPreserving.mul_frobNorm_sub_mul_sq_le {A : Matrix m n 𝕜}
    {Ã : Matrix m l 𝕜} {k : ℕ} {a b : ℝ} (h : IsProjectionCostPreserving A Ã k a b)
    {P P' : Matrix m m 𝕜} (hP : IsStarProjection P) (hPk : P.rank ≤ k)
    (hP' : IsStarProjection P') (hP'k : P'.rank ≤ k) {γ : ℝ} (hγ : 1 ≤ γ)
    (hopt : frobNorm (Ã - P * Ã) ^ 2 ≤ γ * frobNorm (Ã - P' * Ã) ^ 2) :
    a * frobNorm (A - P * A) ^ 2 ≤ γ * b * frobNorm (A - P' * A) ^ 2 := by
  obtain ⟨c, hc, h⟩ := h
  have h₁ := (h P hP hPk).1
  have h₂ := mul_le_mul_of_nonneg_left (h P' hP' hP'k).2 (zero_le_one.trans hγ)
  have h₃ := mul_nonneg (sub_nonneg.mpr hγ) hc
  linarith

end NLAlib
