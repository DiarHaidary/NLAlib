/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.SketchedLowRank
public import NLAlib.Sketching.Properties.ProjectionCost

/-!
# Early truncation: structural bounds

Early truncation projects $\mathbf{A} \in \Bbbk^{m \times n}$ onto the range of a best rank-$k$
approximation of the sketch $\mathbf{A}\mathbf{\Omega}$: the early-truncated randomized SVD
`NLAlib.earlyTruncatedRSVD A Ω k` is
$\mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)$. The projector is optimal
for the sketch, not for $\mathbf{A}$, and the statements here transfer that optimality to
$\mathbf{A}$ by two deterministic routes.

**The structural bound.** Fix any $\mathbf{Z} \in \Bbbk^{n \times r}$ with orthonormal columns and
write
$$\mathbf{E} = \mathbf{A} - \mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}},\qquad
w = \|\mathbf{E}\mathbf{\Omega}\mathbf{\Omega}^{\mathsf{H}}\mathbf{E}^{\mathsf{H}} -
\mathbf{E}\mathbf{E}^{\mathsf{H}}\|_{\mathsf{F}},\qquad
\chi = \|\mathbf{E}\mathbf{\Omega}\mathbf{\Omega}^{\mathsf{H}}\mathbf{Z} -
\mathbf{E}\mathbf{Z}\|_{\mathsf{F}},$$
spelled inline as `A - A * Z * Zᴴ` and so on. With $\lambda$ the constant of a subspace injection
$\mathbf{\Omega}^{\mathsf{H}}$ for $\operatorname{range}\mathbf{Z}$ (the head), $w$ and $\chi$
are approximate-multiplication errors (tail–tail and tail–head;
$\mathbf{E}\mathbf{Z} = \mathbf{0}$, kept for that shape). Every orthogonal projector $\mathbf{P}$
of rank at most $k$ whose sketch residual is at most that of the frame's competitor
$\mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega}$ then has
$$\lambda\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{\mathsf{F}}^2 \le \|\mathbf{E}\|_{\mathsf{F}}^2 +
\sqrt{k}\,w + 2\chi\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{\mathsf{F}}\,,$$
with no Frobenius preservation of the tail. The projector of the early-truncated output qualifies
when $\lvert r \rvert \le k$ (Eckart–Young), and so does the projector of any other best
approximation of the sketch, for instance a measurable selector. For a frame with
$\mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}} = \llbracket\mathbf{A}\rrbracket_k$
(`NLAlib.exists_hasOrthonormalCols_mul_mul_conjTranspose_eq_truncatedSVD`),
$\|\mathbf{E}\|_{\mathsf{F}}$ is the optimal error.

**The uniform route.** If $\mathbf{A}\mathbf{\Omega}$ is a rank-$k$ projection-cost-preserving
sketch of $\mathbf{A}$ with constants $a$, $b$, then
$$a\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)
\|_{\mathsf{F}}^2 \le b\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,;$$
a subspace embedding of the row space gives one.

Every statement holds for every choice of the truncation under ties. Degenerate cases: for empty
`r` the frame is $\mathbf{0}$, $\mathbf{E} = \mathbf{A}$ and $\chi = 0$; at $k = 0$ the output is
$\mathbf{0}$. Design: `docs/design/LowRank-S2b.md` §3.3, §3.4, §8.

## Main results

* `NLAlib.IsSubspaceInjection.mul_frobNorm_sub_mul_sq_add_le`: the structural bound, head and tail
  of the residual separately.
* `NLAlib.IsSubspaceInjection.mul_frobNorm_sub_mul_sq_le`: the structural bound in the error alone.
* `NLAlib.IsSubspaceInjection.frobNorm_sub_mul_sq_le`: the bound with all unboundedness in the
  head constant.
* `NLAlib.IsSubspaceInjection.frobNorm_sub_earlyTruncatedRSVD_sq_le`: the early-truncated
  randomized SVD.
* `NLAlib.IsProjectionCostPreserving.mul_frobNorm_sub_earlyTruncatedRSVD_sq_le`,
  `NLAlib.IsSubspaceEmbedding.mul_frobNorm_sub_earlyTruncatedRSVD_sq_le`: the uniform routes.
-/

@[expose] public section

open scoped Matrix MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n r : Type*} [Fintype l] [Fintype m] [Fintype n]
  [Fintype r] [DecidableEq r]

/-! ### Proof-local facts about a star projection and a frame -/

section Aux

variable {q : Type*} [Fintype q]

omit [Fintype r] [DecidableEq r] in
/-- The residual of a star projection is orthogonal to its range part:
$$\langle \mathbf{B} - \mathbf{P}\mathbf{B}, \mathbf{X} - \mathbf{P}\mathbf{X} \rangle_{\mathsf{F}}
= \langle \mathbf{B} - \mathbf{P}\mathbf{B}, \mathbf{X} \rangle_{\mathsf{F}}\,.$$ -/
private theorem frobInner_sub_mul_sub_mul {P : Matrix m m 𝕜} (hP : IsStarProjection P)
    (B X : Matrix m q 𝕜) : frobInner (B - P * B) (X - P * X) = frobInner (B - P * B) X := by
  have h0 : frobInner (B - P * B) (P * X) = 0 := by
    rw [frobInner_comm, frobInner_mul_left, hP.conjTranspose_eq, Matrix.mul_sub,
      ← Matrix.mul_assoc, hP.mul_self, sub_self, frobInner_zero_right]
  rw [frobInner_sub_right, h0, sub_zero]

omit [Fintype r] [DecidableEq r] in
/-- The squared residual of a star projection:
$$\|\mathbf{X} - \mathbf{P}\mathbf{X}\|_{\mathsf{F}}^2 = \|\mathbf{X}\|_{\mathsf{F}}^2 -
\langle \mathbf{P}, \mathbf{X}\mathbf{X}^{\mathsf{H}} \rangle_{\mathsf{F}}\,.$$ -/
private theorem frobNorm_sub_mul_sq_eq {P : Matrix m m 𝕜} (hP : IsStarProjection P)
    (X : Matrix m q 𝕜) :
    frobNorm (X - P * X) ^ 2 = frobNorm X ^ 2 - frobInner P (X * Xᴴ) := by
  rw [← frobInner_self (X - P * X), frobInner_sub_mul_sub_mul hP, frobInner_sub_left,
    frobInner_self, frobInner_mul_right]

omit [Fintype r] [DecidableEq r] in
/-- A star projection of rank at most $k$ meets any matrix in at most
$\sqrt{k}\,\|\mathbf{W}\|_{\mathsf{F}}$. -/
private theorem frobInner_le_sqrt_mul {P : Matrix m m 𝕜} (hP : IsStarProjection P) {k : ℕ}
    (hPk : P.rank ≤ k) (W : Matrix m m 𝕜) : frobInner P W ≤ √(k : ℝ) * frobNorm W := by
  have h1 : frobNorm P ^ 2 = P.rank := by
    have h := frobNorm_rangeProjector_sq P
    rwa [hP.rangeProjector_eq] at h
  have hPF : frobNorm P ≤ √(k : ℝ) := by
    rw [← Real.sqrt_sq (frobNorm_nonneg P), h1]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hPk)
  exact (frobInner_le P W).trans (mul_le_mul_of_nonneg_right hPF (frobNorm_nonneg W))

/-- **The head–tail split of a projection residual** for a frame $\mathbf{Z}$ and any
$\mathbf{P}$: with $\mathbf{E} = \mathbf{A} - \mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}}$,
$$\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{\mathsf{F}}^2 =
\|\mathbf{A}\mathbf{Z} - \mathbf{P}\mathbf{A}\mathbf{Z}\|_{\mathsf{F}}^2 +
\|\mathbf{E} - \mathbf{P}\mathbf{E}\|_{\mathsf{F}}^2\,;$$
`IsStarProjection.frobNorm_sq_eq_add` at $\mathbf{Z}\mathbf{Z}^{\mathsf{H}}$, transposed. -/
private theorem frobNorm_sub_mul_sq_eq_add {Z : Matrix n r 𝕜} (hZ : HasOrthonormalCols Z)
    (A : Matrix m n 𝕜) (P : Matrix m m 𝕜) :
    frobNorm (A - P * A) ^ 2 =
      frobNorm (A * Z - P * (A * Z)) ^ 2 +
        frobNorm (A - A * Z * Zᴴ - P * (A - A * Z * Zᴴ)) ^ 2 := by
  classical
  have h := hZ.isStarProjection_mul_conjTranspose.frobNorm_sq_eq_add (A - P * A)ᴴ
  have e₁ : (Z * Zᴴ * (A - P * A)ᴴ)ᴴ = (A * Z - P * (A * Z)) * Zᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.sub_mul,
      Matrix.mul_assoc]
  have e₂ : ((1 - Z * Zᴴ) * (A - P * A)ᴴ)ᴴ = A - A * Z * Zᴴ - P * (A - A * Z * Zᴴ) := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul,
      Matrix.mul_assoc]
  rw [frobNorm_conjTranspose, ← frobNorm_conjTranspose (Z * Zᴴ * _), e₁,
    hZ.frobNorm_mul_conjTranspose_right, ← frobNorm_conjTranspose ((1 - Z * Zᴴ) * _), e₂] at h
  exact h

end Aux

/-! ### The structural bound -/

/-- **The early-truncation structural bound.** Let $\mathbf{Z}$ have orthonormal columns,
$\mathbf{\Omega}^{\mathsf{H}}$ be a subspace injection for $\operatorname{range}\mathbf{Z}$ with
constant $\lambda$, and $\mathbf{P}$ an orthogonal projector of rank at most $k$ whose sketch
residual is at most that of the frame's competitor
$\mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega}$,
$$\|\mathbf{A}\mathbf{\Omega} - \mathbf{P}\mathbf{A}\mathbf{\Omega}\|_{\mathsf{F}} \le
\|\mathbf{E}\mathbf{\Omega}\|_{\mathsf{F}}$$
with
$\mathbf{E} = \mathbf{A} - \mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}}$ (implied by being at least
as good on the sketch as $\mathbf{P}_{\mathbf{A}\mathbf{Z}}$). With
$r_1 = \|\mathbf{A}\mathbf{Z} - \mathbf{P}\mathbf{A}\mathbf{Z}\|_{\mathsf{F}}$,
$r_2 = \|\mathbf{E} - \mathbf{P}\mathbf{E}\|_{\mathsf{F}}$ and
$$w = \|\mathbf{E}\mathbf{\Omega}\mathbf{\Omega}^{\mathsf{H}}\mathbf{E}^{\mathsf{H}} -
\mathbf{E}\mathbf{E}^{\mathsf{H}}\|_{\mathsf{F}},\qquad
\chi = \|\mathbf{E}\mathbf{\Omega}\mathbf{\Omega}^{\mathsf{H}}\mathbf{Z} -
\mathbf{E}\mathbf{Z}\|_{\mathsf{F}},$$
$$\lambda r_1^2 + r_2^2 \le \|\mathbf{E}\|_{\mathsf{F}}^2 + \sqrt{k}\,w + 2\chi r_1\,.$$
Only the lower side of the head embedding and the two approximate-multiplication errors enter; the
Frobenius preservation of the tail cancels. True for every real $\lambda$. Proved without a
literature source; the sketch quantities are those of
[CohenElderMuscoMuscoPersu2015, proof of Theorem 12].
Result: early-truncation-structural-bound -/
theorem IsSubspaceInjection.mul_frobNorm_sub_mul_sq_add_le {A : Matrix m n 𝕜}
    {Ω : Matrix n l 𝕜} {Z : Matrix n r 𝕜} {a : ℝ} (h : IsSubspaceInjection Ωᴴ Z a)
    (hZ : HasOrthonormalCols Z) {P : Matrix m m 𝕜} (hP : IsStarProjection P) {k : ℕ}
    (hPk : P.rank ≤ k)
    (hopt : frobNorm (A * Ω - P * (A * Ω)) ≤ frobNorm ((A - A * Z * Zᴴ) * Ω)) :
    a * frobNorm (A * Z - P * (A * Z)) ^ 2 +
        frobNorm (A - A * Z * Zᴴ - P * (A - A * Z * Zᴴ)) ^ 2 ≤
      frobNorm (A - A * Z * Zᴴ) ^ 2 +
        √(k : ℝ) * frobNorm ((A - A * Z * Zᴴ) * Ω * Ωᴴ * (A - A * Z * Zᴴ)ᴴ -
          (A - A * Z * Zᴴ) * (A - A * Z * Zᴴ)ᴴ) +
        2 * frobNorm ((A - A * Z * Zᴴ) * Ω * Ωᴴ * Z - (A - A * Z * Zᴴ) * Z) *
          frobNorm (A * Z - P * (A * Z)) := by
  have hdec : A * Ω - P * (A * Ω) =
      (A * Z - P * (A * Z)) * (Zᴴ * Ω) + (A - A * Z * Zᴴ - P * (A - A * Z * Zᴴ)) * Ω := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
    abel
  have hEZ : (A - A * Z * Zᴴ) * Z = 0 := by
    rw [Matrix.sub_mul, Matrix.mul_assoc (A * Z), hZ.conjTranspose_mul_self, Matrix.mul_one,
      sub_self]
  generalize hE : A - A * Z * Zᴴ = E at hopt hdec hEZ ⊢
  set R₁ := A * Z - P * (A * Z) with hR₁
  -- sketch optimality, expanded
  have hopt2 := pow_le_pow_left₀ (frobNorm_nonneg _) hopt 2
  rw [hdec, frobNorm_add_sq] at hopt2
  -- head
  have hhead : a * frobNorm R₁ ^ 2 ≤ frobNorm (R₁ * (Zᴴ * Ω)) ^ 2 := by
    have h' := mul_frobNorm_sq_le_of_smul_one_le (hZ.isSubspaceInjection_iff.mp h) R₁ᴴ
    have e : (R₁ * (Zᴴ * Ω))ᴴ = Ωᴴ * Z * R₁ᴴ := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rwa [frobNorm_conjTranspose, ← e, frobNorm_conjTranspose] at h'
  -- tail
  have htail : frobNorm ((E - P * E) * Ω) ^ 2 = frobNorm (E * Ω) ^ 2 -
      frobInner P (E * Ω * Ωᴴ * Eᴴ) := by
    rw [Matrix.sub_mul, Matrix.mul_assoc P, frobNorm_sub_mul_sq_eq hP, Matrix.conjTranspose_mul,
      ← Matrix.mul_assoc]
  have hr₂ := frobNorm_sub_mul_sq_eq hP E
  have hW := frobInner_le_sqrt_mul hP hPk (E * Ω * Ωᴴ * Eᴴ - E * Eᴴ)
  rw [frobInner_sub_right] at hW
  -- cross
  have hcross : frobInner (R₁ * (Zᴴ * Ω)) ((E - P * E) * Ω) =
      frobInner R₁ (E * Ω * Ωᴴ * Z - E * Z) := by
    rw [frobInner_mul_right, hEZ, sub_zero, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc P,
      Matrix.mul_assoc P, hR₁, frobInner_sub_mul_sub_mul hP]
    simp only [Matrix.mul_assoc]
  have hχ := neg_abs_le (frobInner R₁ (E * Ω * Ωᴴ * Z - E * Z))
  have hχ' := abs_frobInner_le R₁ (E * Ω * Ωᴴ * Z - E * Z)
  rw [hcross, htail] at hopt2
  linarith

/-- **The early-truncation structural bound, in the error alone**: under the hypotheses of
`NLAlib.IsSubspaceInjection.mul_frobNorm_sub_mul_sq_add_le` and $\lambda \le 1$, with
$\mathbf{E}$, $w$, $\chi$ as there,
$$\lambda\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{\mathsf{F}}^2 \le \|\mathbf{E}\|_{\mathsf{F}}^2 +
\sqrt{k}\,w + 2\chi\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{\mathsf{F}}\,.$$
For $\lambda > 1$ apply it at $1$ through `NLAlib.IsSubspaceInjection.mono`. Proved without a
literature source; the sketch quantities are those of
[CohenElderMuscoMuscoPersu2015, proof of Theorem 12].
Result: early-truncation-structural-bound -/
theorem IsSubspaceInjection.mul_frobNorm_sub_mul_sq_le {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜}
    {Z : Matrix n r 𝕜} {a : ℝ} (h : IsSubspaceInjection Ωᴴ Z a) (hZ : HasOrthonormalCols Z)
    (ha1 : a ≤ 1) {P : Matrix m m 𝕜} (hP : IsStarProjection P) {k : ℕ} (hPk : P.rank ≤ k)
    (hopt : frobNorm (A * Ω - P * (A * Ω)) ≤ frobNorm ((A - A * Z * Zᴴ) * Ω)) :
    a * frobNorm (A - P * A) ^ 2 ≤
      frobNorm (A - A * Z * Zᴴ) ^ 2 +
        √(k : ℝ) * frobNorm ((A - A * Z * Zᴴ) * Ω * Ωᴴ * (A - A * Z * Zᴴ)ᴴ -
          (A - A * Z * Zᴴ) * (A - A * Z * Zᴴ)ᴴ) +
        2 * frobNorm ((A - A * Z * Zᴴ) * Ω * Ωᴴ * Z - (A - A * Z * Zᴴ) * Z) *
          frobNorm (A - P * A) := by
  have h2 := h.mul_frobNorm_sub_mul_sq_add_le hZ hP hPk hopt
  have hs := frobNorm_sub_mul_sq_eq_add hZ A P
  have hr₁ : frobNorm (A * Z - P * (A * Z)) ≤ frobNorm (A - P * A) :=
    (sq_le_sq₀ (frobNorm_nonneg _) (frobNorm_nonneg _)).mp
      (by nlinarith [sq_nonneg (frobNorm (A - A * Z * Zᴴ - P * (A - A * Z * Zᴴ)))])
  have hχ := mul_le_mul_of_nonneg_left hr₁ (mul_nonneg zero_le_two
    (frobNorm_nonneg ((A - A * Z * Zᴴ) * Ω * Ωᴴ * Z - (A - A * Z * Zᴴ) * Z)))
  have hr₂ := mul_nonneg (sub_nonneg.mpr ha1)
    (sq_nonneg (frobNorm (A - A * Z * Zᴴ - P * (A - A * Z * Zᴴ))))
  rw [hs]
  nlinarith

/-- **The early-truncation bound with all unboundedness in the head constant**: under the
hypotheses of `NLAlib.IsSubspaceInjection.mul_frobNorm_sub_mul_sq_add_le`, for $0 < \lambda \le 1$
and $0 < \theta < 1$, with $\mathbf{E}$, $w$, $\chi$ as there,
$$\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{\mathsf{F}}^2 \le
\frac{\|\mathbf{E}\|_{\mathsf{F}}^2 + \sqrt{k}\,w}{(1-\theta)\lambda} +
\frac{\chi^2}{\theta(1-\theta)\lambda^2}\,.$$
A random head constant enters as $\min\{1, \lambda\}$ through `NLAlib.IsSubspaceInjection.mono`,
which is the form an expectation bound integrates. Proved without a literature source; the sketch
quantities are those of [CohenElderMuscoMuscoPersu2015, proof of Theorem 12].
Result: early-truncation-structural-bound -/
theorem IsSubspaceInjection.frobNorm_sub_mul_sq_le {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜}
    {Z : Matrix n r 𝕜} {a θ : ℝ} (h : IsSubspaceInjection Ωᴴ Z a) (hZ : HasOrthonormalCols Z)
    (ha : 0 < a) (ha1 : a ≤ 1) (hθ : 0 < θ) (hθ1 : θ < 1) {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) {k : ℕ} (hPk : P.rank ≤ k)
    (hopt : frobNorm (A * Ω - P * (A * Ω)) ≤ frobNorm ((A - A * Z * Zᴴ) * Ω)) :
    frobNorm (A - P * A) ^ 2 ≤
      (frobNorm (A - A * Z * Zᴴ) ^ 2 +
          √(k : ℝ) * frobNorm ((A - A * Z * Zᴴ) * Ω * Ωᴴ * (A - A * Z * Zᴴ)ᴴ -
            (A - A * Z * Zᴴ) * (A - A * Z * Zᴴ)ᴴ)) / ((1 - θ) * a) +
        frobNorm ((A - A * Z * Zᴴ) * Ω * Ωᴴ * Z - (A - A * Z * Zᴴ) * Z) ^ 2 /
          (θ * (1 - θ) * a ^ 2) := by
  have h3 := h.mul_frobNorm_sub_mul_sq_le hZ ha1 hP hPk hopt
  generalize frobNorm (A - P * A) = s at h3 ⊢
  generalize frobNorm ((A - A * Z * Zᴴ) * Ω * Ωᴴ * Z - (A - A * Z * Zᴴ) * Z) = χ at h3 ⊢
  generalize frobNorm (A - A * Z * Zᴴ) ^ 2 +
    √(k : ℝ) * frobNorm ((A - A * Z * Zᴴ) * Ω * Ωᴴ * (A - A * Z * Zᴴ)ᴴ -
      (A - A * Z * Zᴴ) * (A - A * Z * Zᴴ)ᴴ) = c at h3 ⊢
  have h1θ : 0 < 1 - θ := sub_pos.mpr hθ1
  have hD : 0 < θ * (1 - θ) * a ^ 2 := by positivity
  have key : θ * (1 - θ) * a ^ 2 * s ^ 2 ≤ θ * a * c + χ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left h3 (mul_pos hθ ha).le, sq_nonneg (θ * a * s - χ)]
  calc s ^ 2 ≤ (θ * a * c + χ ^ 2) / (θ * (1 - θ) * a ^ 2) := by
        rw [le_div_iff₀ hD]
        linarith
    _ = c / ((1 - θ) * a) + χ ^ 2 / (θ * (1 - θ) * a ^ 2) := by
        field_simp

/-! ### The early-truncated randomized SVD -/

/-- **Early-truncated randomized SVD, structural bound.** For $\mathbf{Z}$ with orthonormal
columns, $\lvert r \rvert \le k$, $\mathbf{\Omega}^{\mathsf{H}}$ a subspace injection for
$\operatorname{range}\mathbf{Z}$ with constant $0 < \lambda \le 1$, and $0 < \theta < 1$, with
$$\mathbf{E} = \mathbf{A} - \mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}},\qquad
w = \|\mathbf{E}\mathbf{\Omega}\mathbf{\Omega}^{\mathsf{H}}\mathbf{E}^{\mathsf{H}} -
\mathbf{E}\mathbf{E}^{\mathsf{H}}\|_{\mathsf{F}},\qquad
\chi = \|\mathbf{E}\mathbf{\Omega}\mathbf{\Omega}^{\mathsf{H}}\mathbf{Z} -
\mathbf{E}\mathbf{Z}\|_{\mathsf{F}},$$
$$\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)
\|_{\mathsf{F}}^2 \le \frac{\|\mathbf{E}\|_{\mathsf{F}}^2 + \sqrt{k}\,w}{(1-\theta)\lambda} +
\frac{\chi^2}{\theta(1-\theta)\lambda^2}\,,$$
for every choice of the truncation. With
$\mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}} = \llbracket\mathbf{A}\rrbracket_k$
(`NLAlib.exists_hasOrthonormalCols_mul_mul_conjTranspose_eq_truncatedSVD`, for
$k \le \lvert n \rvert$) $\|\mathbf{E}\|_{\mathsf{F}}$ is the optimal error. The hypothesis
$\lvert r \rvert \le k$ is needed ($\mathbf{A} = \mathbf{\Omega} = \mathbf{Z} = \mathbf{I}_2$,
$k = 1$). Proved without a literature source; the sketch quantities are those of
[CohenElderMuscoMuscoPersu2015, proof of Theorem 12].
Result: early-truncation-structural-bound -/
theorem IsSubspaceInjection.frobNorm_sub_earlyTruncatedRSVD_sq_le {Ω : Matrix n l 𝕜}
    {Z : Matrix n r 𝕜} {a θ : ℝ} (h : IsSubspaceInjection Ωᴴ Z a) (hZ : HasOrthonormalCols Z)
    {k : ℕ} (hk : Fintype.card r ≤ k) (ha : 0 < a) (ha1 : a ≤ 1) (hθ : 0 < θ) (hθ1 : θ < 1)
    (A : Matrix m n 𝕜) :
    frobNorm (A - earlyTruncatedRSVD A Ω k) ^ 2 ≤
      (frobNorm (A - A * Z * Zᴴ) ^ 2 +
          √(k : ℝ) * frobNorm ((A - A * Z * Zᴴ) * Ω * Ωᴴ * (A - A * Z * Zᴴ)ᴴ -
            (A - A * Z * Zᴴ) * (A - A * Z * Zᴴ)ᴴ)) / ((1 - θ) * a) +
        frobNorm ((A - A * Z * Zᴴ) * Ω * Ωᴴ * Z - (A - A * Z * Zᴴ) * Z) ^ 2 /
          (θ * (1 - θ) * a ^ 2) := by
  have hPk : (rangeProjector (truncatedSVD (A * Ω) k)).rank ≤ k :=
    (rank_rangeProjector _).trans_le (rank_truncatedSVD_le _ k)
  have hopt : frobNorm (A * Ω - rangeProjector (truncatedSVD (A * Ω) k) * (A * Ω)) ≤
      frobNorm ((A - A * Z * Zᴴ) * Ω) := by
    have hr : (A * Z * Zᴴ * Ω).rank ≤ k :=
      ((Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_left _ _).trans
        (Matrix.rank_le_card_width _))).trans hk
    rw [rangeProjector_truncatedSVD_mul, Matrix.sub_mul]
    exact frobNorm_sub_truncatedSVD_le_of_rank_le (A * Ω) hr
  rw [earlyTruncatedRSVD]
  exact h.frobNorm_sub_mul_sq_le hZ ha ha1 hθ hθ1 (isStarProjection_rangeProjector _) hPk hopt

/-- **Early truncation through a projection-cost-preserving sketch**: if
$\mathbf{A}\mathbf{\Omega}$ is a rank-$k$ projection-cost-preserving sketch of $\mathbf{A}$ with
constants $a$, $b$, then
$$a\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)
\|_{\mathsf{F}}^2 \le b\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,,$$
that is $(1+\varepsilon)/(1-\varepsilon)$ times the optimal error in the two-sided form, for every
choice of the truncations. A pointwise statement: off the event where the sketch is a
projection-cost-preserving sketch the error is bounded only by $\|\mathbf{A}\|_{\mathsf{F}}^2$, so
no expectation bound follows from it; the structural bound
`NLAlib.IsSubspaceInjection.frobNorm_sub_earlyTruncatedRSVD_sq_le` gives one.
[CohenElderMuscoMuscoPersu2015, Lemma 3, §7.2]; there with $\varepsilon$ and a set of rank-$k$
projectors; here constants $a$, $b$ and the named output.
Result: early-truncation-pcp-bound -/
theorem IsProjectionCostPreserving.mul_frobNorm_sub_earlyTruncatedRSVD_sq_le
    {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜} {k : ℕ} {a b : ℝ}
    (h : IsProjectionCostPreserving A (A * Ω) k a b) :
    a * frobNorm (A - earlyTruncatedRSVD A Ω k) ^ 2 ≤
      b * frobNorm (A - truncatedSVD A k) ^ 2 := by
  have hPk : (rangeProjector (truncatedSVD (A * Ω) k)).rank ≤ k :=
    (rank_rangeProjector _).trans_le (rank_truncatedSVD_le _ k)
  have hP'k : (rangeProjector (truncatedSVD A k)).rank ≤ k :=
    (rank_rangeProjector _).trans_le (rank_truncatedSVD_le _ k)
  have hopt : frobNorm (A * Ω - rangeProjector (truncatedSVD (A * Ω) k) * (A * Ω)) ^ 2 ≤
      1 * frobNorm (A * Ω - rangeProjector (truncatedSVD A k) * (A * Ω)) ^ 2 := by
    rw [one_mul, rangeProjector_truncatedSVD_mul]
    exact pow_le_pow_left₀ (frobNorm_nonneg _)
      (frobNorm_sub_truncatedSVD_le_of_rank_le _ ((Matrix.rank_mul_le_left _ _).trans hP'k)) 2
  have h' := h.mul_frobNorm_sub_mul_sq_le (isStarProjection_rangeProjector _) hPk
    (isStarProjection_rangeProjector _) hP'k le_rfl hopt
  rwa [one_mul, rangeProjector_truncatedSVD_mul] at h'

/-- **Early truncation under a subspace embedding of the row space**: if
$\mathbf{\Omega}^{\mathsf{H}}$ is a subspace embedding for
$\operatorname{range}\mathbf{A}^{\mathsf{H}}$ with constants $a$, $b$, then for every $k$
$$a\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)
\|_{\mathsf{F}}^2 \le b\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,.$$
The embedding dimension is at least $\operatorname{rank}\mathbf{A}$; a sketch of dimension
independent of the rank needs `NLAlib.IsSubspaceInjection.frobNorm_sub_earlyTruncatedRSVD_sq_le`.
[Woodruff2014, Theorem 61]; there transposed (Woodruff's column space of $\mathbf{A}$ is the row
space here), with unsquared constants $1 \pm \varepsilon$, here $a = (1-\varepsilon)^2$ and
$b = (1+\varepsilon)^2$, and the conclusion $1 + O(\varepsilon)$.
Result: early-truncation-pcp-bound -/
theorem IsSubspaceEmbedding.mul_frobNorm_sub_earlyTruncatedRSVD_sq_le {A : Matrix m n 𝕜}
    {Ω : Matrix n l 𝕜} {a b : ℝ} (h : IsSubspaceEmbedding Ωᴴ Aᴴ a b) (k : ℕ) :
    a * frobNorm (A - earlyTruncatedRSVD A Ω k) ^ 2 ≤
      b * frobNorm (A - truncatedSVD A k) ^ 2 :=
  (h.isProjectionCostPreserving k).mul_frobNorm_sub_earlyTruncatedRSVD_sq_le

end NLAlib
