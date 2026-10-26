/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowerBounds.LowRank.FewPasses
public import NLAlibScaffold.LowerBounds.QueryModel.Yao
public import NLAlib.Matrix.Spectral.LowRank
public import NLAlib.RandomMatrix.Gaussian.ExtremeSingularValues
public import NLAlibScaffold.LowerBounds.QueryModel.HiddenRotation
public import NLAlibScaffold.Polynomial.Interpolation.DividedDifference

/-!
# Two-pass low-rank approximation needs $\Omega(k/\varepsilon)$ products (scaffold)

Every randomized algorithm that makes its matrix–vector products in two passes (two blocks, the
second chosen from the responses to the first) and returns a rank-$k$ approximation within
$(1 + \varepsilon)$ of the best in Frobenius norm needs more than $k/(6400\varepsilon)$ products in
the worst case; one pass is a special case, and in spectral norm two passes need a number of
products proportional to the dimension. Randomized SVD meets the Frobenius rate with two passes,
so it is rate-optimal among two-pass algorithms. Stage LB-C1, design note
`docs/design/LowerBounds-HiddenRotationLowerBounds.md` §3.6; research note OP5
(`~/nlalib-harness/reports/OP5-TwoPassMinimax.md`, Theorems A and C, Corollary B).

The hard instance is $\mathbf{A} = \mathbf{U}\mathbf{D}\mathbf{U}^{\mathsf{H}}$, $\mathbf{U}$ Haar,
$\mathbf{D} = \operatorname{diag}(4\mathbf{I}_k, \mathbf{I}_m, 2\mathbf{I}_m, 3\mathbf{I}_m)$
(`NLAlib.equispacedLevelSpectrum k m 2`). Three steps: the error is at least the optimum
$14m$ plus $7(k - t)$, $t$ the head mass captured by the output range; by the Krylov coupling the
rotated output range lies in $\mathcal{K}_3(\mathbf{D}, \mathbf{G})$ for a Gaussian $\mathbf{G}$
with $q + k$ columns; a vector of that space is $\mathbf{G}_\lambda\mathbf{p}(\lambda)$ on level
$\lambda$ with $\deg\mathbf{p} \le 2$, and $\mathbf{p}(4) = \mathbf{p}(1) - 3\mathbf{p}(2) +
3\mathbf{p}(3)$, so the head part is small unless $q + k$ is of the order of $m$.

## Main results

* `NLAlib.HasOrthonormalCols.frobNorm_mul_diagonal_mul_sub_truncatedSVD_sq`,
  `NLAlib.HasOrthonormalCols.singularValues_mul_diagonal_mul_card`: the optimum.
* `NLAlib.le_frobNorm_diagonal_sub_mul_sq`, `NLAlib.le_specNorm_diagonal_sub_mul_sq`: error from
  head capture.
* `NLAlib.mul_sum_sq_le_mul_norm_sq_of_mem_blockKrylovSpace`: the interpolation bound.
* `NLAlib.measureReal_exists_mem_blockKrylovSpace_lt_sum_sq_le_of_hasLaw_gaussianMatrix`: Gaussian
  head capture.
* one deterministic two-pass algorithm, Frobenius and spectral:
  `NLAlib.QueryAlgorithm.IsPassStructured.measureReal_frobNorm_sub_mul_sq_lt_le_of_hasLaw_haarFrame`
  `NLAlib.QueryAlgorithm.IsPassStructured.measureReal_specNorm_sub_mul_sq_lt_le_of_hasLaw_haarFrame`
* `NLAlib.exists_le_measureReal_frobNorm_sub_mul_sq_ge`: randomized, worst case.
* `NLAlib.div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le`,
  `NLAlib.div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le_of_lt_one`,
  `NLAlib.lt_of_forall_le_measureReal_specNorm_sub_mul_le`: the query counts.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {k m : Type*} [Fintype k]
  [Fintype m] [DecidableEq k] [DecidableEq m]

/-- **The optimum of the two-pass hard instance**: for orthogonal $\mathbf{U}$ and
$\mathbf{A} = \mathbf{U}\operatorname{diag}(4\mathbf{I}_k, \mathbf{I}_m, 2\mathbf{I}_m,
3\mathbf{I}_m)\mathbf{U}^{\mathsf{H}}$,
$\|\mathbf{A} - \llbracket \mathbf{A} \rrbracket_k\|_{\mathsf{F}}^2 = 14\lvert m \rvert$.
Proof: `NLAlib.frobNorm_sub_truncatedSVD_sq`; the singular values of $\mathbf{A}$ are those of the
diagonal (unitary invariance) sorted, $4$ ($\lvert k \rvert$ times), then $3, 2, 1$
($\lvert m \rvert$ times each), so the tail sum is $(9 + 4 + 1)\lvert m \rvert$. M, about 50
lines. -/
theorem HasOrthonormalCols.frobNorm_mul_diagonal_mul_sub_truncatedSVD_sq
    {U : Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ} (hU : HasOrthonormalCols U) :
    frobNorm (U * Matrix.diagonal (equispacedLevelSpectrum k m 2) * Uᴴ -
        truncatedSVD (U * Matrix.diagonal (equispacedLevelSpectrum k m 2) * Uᴴ)
          (Fintype.card k)) ^ 2 = 14 * Fintype.card m := by
  sorry

/-- The $(k + 1)$-st singular value of the two-pass hard instance is $3$: for orthogonal
$\mathbf{U}$ and $m$ nonempty, $\sigma_k(\mathbf{U}\mathbf{D}\mathbf{U}^{\mathsf{H}}) = 3$
(indices from $0$).
Proof: as `NLAlib.HasOrthonormalCols.frobNorm_mul_diagonal_mul_sub_truncatedSVD_sq`, the sorted
singular values. M, about 30 lines. -/
theorem HasOrthonormalCols.singularValues_mul_diagonal_mul_card [Nonempty m]
    {U : Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ} (hU : HasOrthonormalCols U) :
    singularValues (U * Matrix.diagonal (equispacedLevelSpectrum k m 2) * Uᴴ) (Fintype.card k) =
      3 := by
  sorry

/-- **Frobenius error from head capture**: for every $\mathbf{W} \in \mathbb{R}^{n \times k}$ and
$\mathbf{M} \in \mathbb{R}^{k \times n}$, $n = k \oplus (\{0, 1, 2\} \times m)$ and
$\mathbf{D} = \operatorname{diag}(4\mathbf{I}_k, \mathbf{I}_m, 2\mathbf{I}_m, 3\mathbf{I}_m)$,
$$\|\mathbf{D} - \mathbf{W}\mathbf{M}\|_{\mathsf{F}}^2 \ge 14\lvert m \rvert + 7\bigl(\lvert k
\rvert - t\bigr) \,, \qquad t = \sum_{a \in k}\|\mathbf{P}_{\mathbf{W}}\mathbf{e}_a\|^2 \,,$$
$t$ the head mass captured by the range of $\mathbf{W}$.
OP5, Step 1 (eq. (1)).
Proof: $(\mathbf{I} - \mathbf{P}_{\mathbf{W}})(\mathbf{D} - \mathbf{W}\mathbf{M}) =
(\mathbf{I} - \mathbf{P}_{\mathbf{W}})\mathbf{D}$ (`NLAlib.rangeProjector_mul_self`), so the error
is at least $\|\mathbf{D}\|_{\mathsf{F}}^2 - \operatorname{tr}(\mathbf{P}_{\mathbf{W}}
\mathbf{D}^2)$; the diagonal of $\mathbf{P}_{\mathbf{W}}$ sums to its rank, at most $\lvert k
\rvert$ (`NLAlib.rank_rangeProjector`), and $d_i^2 \le 9$ off the head, so
$\operatorname{tr}(\mathbf{P}_{\mathbf{W}}\mathbf{D}^2) \le 16t + 9(\lvert k \rvert - t)$. M,
about 50 lines. -/
theorem le_frobNorm_diagonal_sub_mul_sq (W : Matrix (k ⊕ (Fin 3 × m)) k ℝ)
    (M : Matrix k (k ⊕ (Fin 3 × m)) ℝ) :
    14 * Fintype.card m + 7 * (Fintype.card k -
        ∑ a : k, ‖WithLp.toLp 2 (rangeProjector W *ᵥ Pi.single (Sum.inl a) 1)‖ ^ 2) ≤
      frobNorm (Matrix.diagonal (equispacedLevelSpectrum k m 2) - W * M) ^ 2 := by
  sorry

/-- **Spectral error from head capture**: with the notation of
`NLAlib.le_frobNorm_diagonal_sub_mul_sq` and $k$ nonempty,
$$\|\mathbf{D} - \mathbf{W}\mathbf{M}\|_2^2 \ge
\frac{16(\lvert k \rvert - t)}{\lvert k \rvert} \,.$$
OP5, Step 1 (eq. (1')).
Proof: $\|\mathbf{D} - \mathbf{W}\mathbf{M}\|_2 \ge \|(\mathbf{I} - \mathbf{P}_{\mathbf{W}})
\mathbf{D}\mathbf{P}_*\|_2 = 4\|(\mathbf{I} - \mathbf{P}_{\mathbf{W}})\mathbf{P}_*\|_2$, and the
spectral norm of a matrix of rank at most $\lvert k \rvert$ is at least its Frobenius norm over
$\sqrt{\lvert k \rvert}$ (`NLAlib.frobNorm_le_sqrt_rank_mul_specNorm` or the singular-value sum),
with $\|(\mathbf{I} - \mathbf{P}_{\mathbf{W}})\mathbf{P}_*\|_{\mathsf{F}}^2 = \lvert k \rvert - t$.
M, about 40 lines. -/
theorem le_specNorm_diagonal_sub_mul_sq [Nonempty k] (W : Matrix (k ⊕ (Fin 3 × m)) k ℝ)
    (M : Matrix k (k ⊕ (Fin 3 × m)) ℝ) :
    16 * (Fintype.card k -
        ∑ a : k, ‖WithLp.toLp 2 (rangeProjector W *ᵥ Pi.single (Sum.inl a) 1)‖ ^ 2) /
        Fintype.card k ≤
      specNorm (Matrix.diagonal (equispacedLevelSpectrum k m 2) - W * M) ^ 2 := by
  sorry

/-- **Interpolation bound for depth-3 Krylov vectors**: let
$\mathbf{G} \in \mathbb{R}^{n \times b}$ with tail blocks $\mathbf{G}_j$ (rows of level $j + 1$)
and head block $\mathbf{G}_h$, $s^2\mathbf{I} \preceq \mathbf{G}_j^{\mathsf{H}}\mathbf{G}_j$ for
$j = 0, 1, 2$ and $\|\mathbf{G}_h\|_2 \le S$. Every $\mathbf{z} \in \mathcal{K}_3(\mathbf{D},
\mathbf{G})$ has
$$s^2\sum_{a \in k} z_a^2 \le 19\,S^2\,\|\mathbf{z}\|^2 \,.$$
OP5, Step 3 (eq. (2)).
Proof: `NLAlib.mem_blockKrylovSpace_iff`: on level $\lambda$ the block of $\mathbf{z}$ is
$\mathbf{G}_\lambda\mathbf{p}(\lambda)$ for a vector polynomial of degree at most $2$; by
`NLAlib.sum_neg_one_pow_mul_choose_mul_eval_eq_zero` ($n = 3$, $x = h = 1$, coordinatewise)
$\mathbf{p}(4) = \mathbf{p}(1) - 3\mathbf{p}(2) + 3\mathbf{p}(3)$, so
$\|\mathbf{p}(4)\|^2 \le 19\sum_{j}\|\mathbf{p}(j)\|^2$ (Cauchy–Schwarz); then
$\|\mathbf{G}_h\mathbf{p}(4)\| \le S\|\mathbf{p}(4)\|$
(`NLAlib.norm_toLp_mulVec_le`) and
$s^2\|\mathbf{p}(j)\|^2 \le \|\mathbf{G}_j\mathbf{p}(j)\|^2$ (`NLAlib.quadForm` of the Loewner
bound). M, about 70 lines. -/
theorem mul_sum_sq_le_mul_norm_sq_of_mem_blockKrylovSpace {b : Type*} [Fintype b]
    [DecidableEq b] {G : Matrix (k ⊕ (Fin 3 × m)) b ℝ} {s S : ℝ}
    (hs : ∀ j : Fin 3, s ^ 2 • (1 : Matrix b b ℝ) ≤
      (G.submatrix (fun i : m => Sum.inr (j, i)) id)ᴴ *
        G.submatrix (fun i : m => Sum.inr (j, i)) id)
    (hS : specNorm (G.submatrix Sum.inl id) ≤ S) {z : k ⊕ (Fin 3 × m) → ℝ}
    (hz : z ∈ blockKrylovSpace (Matrix.diagonal (equispacedLevelSpectrum k m 2)) G 3) :
    s ^ 2 * ∑ a : k, z (Sum.inl a) ^ 2 ≤ 19 * S ^ 2 * ‖WithLp.toLp 2 z‖ ^ 2 := by
  sorry

/-- **Gaussian head capture of a depth-3 Krylov space**: let $\mathbf{G}$ be a standard Gaussian
$n \times b$ matrix, $n = k \oplus (\{0, 1, 2\} \times m)$, $\gamma > 2$, $\lvert k \rvert \le
\lvert b \rvert$ and $\gamma^2\lvert b \rvert \le \lvert m \rvert$. Then
$$\mathbb{P}\Bigl[\exists\,\mathbf{z} \in \mathcal{K}_3(\mathbf{D}, \mathbf{G}):\
\sum_{a \in k} z_a^2 > \frac{171}{(\gamma - 2)^2}\|\mathbf{z}\|^2\Bigr] \le
4\exp\Bigl(-\frac{\lvert m \rvert}{2\gamma^2}\Bigr) \,.$$
OP5, Step 3; there $\rho(\gamma) = 19(3/\gamma)^2/(1 - 2/\gamma)^2$, at $\gamma = 20$ and $26$.
Proof: on the event that $\sigma_{\min}(\mathbf{G}_j) > \sqrt{\lvert m \rvert}(1 - 2/\gamma)$ for
the three tail blocks and $\|\mathbf{G}_h\|_2 < 3\sqrt{\lvert m \rvert}/\gamma$ (blocks Gaussian,
`NLAlib.hasLaw_submatrix_of_hasLaw_gaussianMatrix`; tails
`NLAlib.measureReal_singularValues_le_le_of_hasLaw_gaussianMatrix` and
`NLAlib.measureReal_specNorm_ge_le_of_hasLaw_gaussianMatrix` with
$t = \sqrt{\lvert m \rvert}/\gamma$, $\sqrt{\lvert k \rvert} \le \sqrt{\lvert b \rvert} \le t$),
apply `NLAlib.mul_sum_sq_le_mul_norm_sq_of_mem_blockKrylovSpace`; the Loewner bound from the
smallest singular value is `NLAlib.smul_one_le_conjTranspose_mul_self_iff`-type. Union bound
`MeasureTheory.measureReal_union_le`. If $b$ is empty the space is $\{\mathbf{0}\}$. M, about 60
lines. -/
theorem measureReal_exists_mem_blockKrylovSpace_lt_sum_sq_le_of_hasLaw_gaussianMatrix
    {b : Type*} [Fintype b] {G : Ω → Matrix (k ⊕ (Fin 3 × m)) b ℝ}
    (hG : HasLaw G (gaussianMatrix (k ⊕ (Fin 3 × m)) b) μ) {γ : ℝ} (hγ : 2 < γ)
    (hkb : Fintype.card k ≤ Fintype.card b) (hbm : γ ^ 2 * Fintype.card b ≤ Fintype.card m) :
    μ.real {ω | ∃ z ∈ blockKrylovSpace (Matrix.diagonal (equispacedLevelSpectrum k m 2)) (G ω) 3,
        171 / (γ - 2) ^ 2 * ‖WithLp.toLp 2 z‖ ^ 2 < ∑ a : k, z (Sum.inl a) ^ 2} ≤
      4 * Real.exp (-(Fintype.card m / (2 * γ ^ 2))) := by
  sorry

/-- **Two-pass Frobenius lower bound for one deterministic algorithm**: let $\mathbf{U}$ be Haar,
$\mathbf{A} = \mathbf{U}\operatorname{diag}(4\mathbf{I}_k, \mathbf{I}_m, 2\mathbf{I}_m,
3\mathbf{I}_m)\mathbf{U}^{\mathsf{H}}$, and let a measurable algorithm make $q$ queries in at most
two passes to $\mathbf{x} \mapsto (\mathbf{A}\mathbf{x}, \mathbf{U}^{\mathsf{H}}\mathbf{x})$ and
output $\mathbf{W} \in \mathbb{R}^{n \times k}$, $\mathbf{M} \in \mathbb{R}^{k \times n}$. If
$400(q + \lvert k \rvert) \le \lvert m \rvert$, then
$$\mathbb{P}\Bigl[\|\mathbf{A} - \mathbf{W}\mathbf{M}\|_{\mathsf{F}}^2 < 14\lvert m \rvert +
3.3\lvert k \rvert\Bigr] \le 4e^{-\lvert m \rvert/800} \,,$$
and $14\lvert m \rvert = \|\mathbf{A} - \llbracket \mathbf{A} \rrbracket_k\|_{\mathsf{F}}^2$.
OP5, Theorem A.
Proof: extend the space by an independent standard Gaussian $n \times (q + k)$ matrix; apply
`NLAlib.QueryAlgorithm.IsPassStructured.exists_isKrylovCoupling_of_hasLaw_haarFrame` to
`alg.mapOutput Prod.fst` with no initial block (`Fin 0` columns,
`NLAlib.IsKrylovCoupling.ae_range_le_of_isEmpty`), depth $3$. On orthogonal $\mathbf{U}$,
$\|\mathbf{A} - \mathbf{W}\mathbf{M}\|_{\mathsf{F}} = \|\mathbf{D} - (\mathbf{U}^{\mathsf{H}}
\mathbf{W})(\mathbf{M}\mathbf{U})\|_{\mathsf{F}}$; by `NLAlib.le_frobNorm_diagonal_sub_mul_sq` the
error is at least $14\lvert m \rvert + 7(\lvert k \rvert - t)$, and $t$ is the sum over an
orthonormal basis of the range of $\mathbf{U}^{\mathsf{H}}\mathbf{W}$ (at most $\lvert k \rvert$
vectors, in $\mathcal{K}_3$) of their head mass, at most $\tfrac{19}{36}\lvert k \rvert$ outside
the event of `NLAlib.measureReal_exists_mem_blockKrylovSpace_lt_sum_sq_le_of_hasLaw_gaussianMatrix`
with $\gamma = 20$; $7 \cdot \tfrac{17}{36} > 3.3$. M, about 80 lines. -/
theorem QueryAlgorithm.IsPassStructured.measureReal_frobNorm_sub_mul_sq_lt_le_of_hasLaw_haarFrame
    {q : ℕ} {alg : QueryAlgorithm (k ⊕ (Fin 3 × m) → ℝ)
      ((k ⊕ (Fin 3 × m) → ℝ) × (k ⊕ (Fin 3 × m) → ℝ)) q
      (Matrix (k ⊕ (Fin 3 × m)) k ℝ × Matrix k (k ⊕ (Fin 3 × m)) ℝ)} {pass : ℕ → ℕ}
    (hpass : alg.IsPassStructured pass) (hp : ∀ i < q, pass i < 2) (halg : alg.IsMeasurable)
    (hm : 400 * (q + Fintype.card k) ≤ Fintype.card m)
    {U : Ω → Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ}
    (hU : HasLaw U (haarFrame (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m))) μ) :
    μ.real {ω | frobNorm (U ω * Matrix.diagonal (equispacedLevelSpectrum k m 2) * (U ω)ᴴ -
        (alg.run (hiddenRotationOracle (U ω) (Matrix.diagonal (equispacedLevelSpectrum k m 2)))).1 *
        (alg.run (hiddenRotationOracle (U ω)
          (Matrix.diagonal (equispacedLevelSpectrum k m 2)))).2) ^ 2 <
        14 * Fintype.card m + 33 / 10 * Fintype.card k} ≤
      4 * Real.exp (-(Fintype.card m / 800)) := by
  sorry

/-- **Two-pass spectral lower bound for one deterministic algorithm**: in the setting of
`NLAlib.QueryAlgorithm.IsPassStructured.measureReal_frobNorm_sub_mul_sq_lt_le_of_hasLaw_haarFrame`
($\mathbf{U}$ Haar, $\mathbf{A} = \mathbf{U}\operatorname{diag}(4\mathbf{I}_k, \mathbf{I}_m,
2\mathbf{I}_m, 3\mathbf{I}_m)\mathbf{U}^{\mathsf{H}}$, a measurable algorithm with $q$ queries in at
most two passes to the hidden-rotation oracle, output $\mathbf{W}\mathbf{M}$ of rank at most
$\lvert k \rvert$), with $k$ nonempty and $676(q + \lvert k \rvert) \le \lvert m \rvert$,
$$\mathbb{P}\Bigl[\|\mathbf{A} - \mathbf{W}\mathbf{M}\|_2^2 < \tfrac{45}{4}\Bigr] \le
4e^{-\lvert m \rvert/1352} \,,$$
while $\sigma_{k+1}(\mathbf{A})^2 = 9$: no $(1 + \varepsilon)\sigma_{k+1}$ approximation for
$\varepsilon \le 0.1$.
OP5, Theorem C.
Proof: as the Frobenius form, with `NLAlib.le_specNorm_diagonal_sub_mul_sq` and $\gamma = 26$
($t \le \tfrac{19}{64}\lvert k \rvert$, $16 \cdot \tfrac{45}{64} = \tfrac{45}{4}$). M, about 60
lines. -/
theorem QueryAlgorithm.IsPassStructured.measureReal_specNorm_sub_mul_sq_lt_le_of_hasLaw_haarFrame
    [Nonempty k] {q : ℕ} {alg : QueryAlgorithm (k ⊕ (Fin 3 × m) → ℝ)
      ((k ⊕ (Fin 3 × m) → ℝ) × (k ⊕ (Fin 3 × m) → ℝ)) q
      (Matrix (k ⊕ (Fin 3 × m)) k ℝ × Matrix k (k ⊕ (Fin 3 × m)) ℝ)} {pass : ℕ → ℕ}
    (hpass : alg.IsPassStructured pass) (hp : ∀ i < q, pass i < 2) (halg : alg.IsMeasurable)
    (hm : 676 * (q + Fintype.card k) ≤ Fintype.card m)
    {U : Ω → Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ}
    (hU : HasLaw U (haarFrame (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m))) μ) :
    μ.real {ω | specNorm (U ω * Matrix.diagonal (equispacedLevelSpectrum k m 2) * (U ω)ᴴ -
        (alg.run (hiddenRotationOracle (U ω) (Matrix.diagonal (equispacedLevelSpectrum k m 2)))).1 *
        (alg.run (hiddenRotationOracle (U ω)
          (Matrix.diagonal (equispacedLevelSpectrum k m 2)))).2) ^ 2 < 45 / 4} ≤
      4 * Real.exp (-(Fintype.card m / 1352)) := by
  sorry

/-- **Two-pass Frobenius lower bound, randomized worst case**: for every randomized algorithm (a
measurable seeded family, seed law $\rho$) making $q$ matrix–vector products in at most two passes
(per seed) with output $\mathbf{W}\mathbf{M}$, $\mathbf{W} \in \mathbb{R}^{n \times k}$, and
$400(q + \lvert k \rvert) \le \lvert m \rvert$, there is an orthogonal $\mathbf{U}$ such that for
$\mathbf{A} = \mathbf{U}\operatorname{diag}(4\mathbf{I}_k, \mathbf{I}_m, 2\mathbf{I}_m,
3\mathbf{I}_m)\mathbf{U}^{\mathsf{H}}$
$$\mathbb{P}_s\Bigl[\|\mathbf{A} - \mathbf{W}_s\mathbf{M}_s\|_{\mathsf{F}}^2 \ge
14\lvert m \rvert + 3.3\lvert k \rvert\Bigr] \ge 1 - 4e^{-\lvert m \rvert/800} \,.$$
OP5, Corollary B(i).
Proof: Yao's principle for a class of algorithms,
`NLAlib.QueryAlgorithm.IsMeasurableFamily.exists_le_measureReal_run_mem_of_forall`, for the
family `fun s => (alg s).comapResponse Prod.fst` against the hidden-rotation oracle
(`NLAlib.QueryAlgorithm.run_comapResponse`,
`NLAlib.QueryAlgorithm.IsMeasurableFamily.comapResponse`,
`NLAlib.Measurable.hiddenRotationOracle`), failure set restricted to orthogonal $\mathbf{U}$
(`NLAlib.isClosed_setOf_hasOrthonormalCols`); each deterministic member fails by
`NLAlib.QueryAlgorithm.IsPassStructured.measureReal_frobNorm_sub_mul_sq_lt_le_of_hasLaw_haarFrame`
(`NLAlib.QueryAlgorithm.IsPassStructured.comapResponse`). M, about 40 lines. -/
theorem exists_le_measureReal_frobNorm_sub_mul_sq_ge {q : ℕ}
    (hm : 400 * (q + Fintype.card k) ≤ Fintype.card m) {S : Type*} [MeasurableSpace S]
    {alg : S → QueryAlgorithm (k ⊕ (Fin 3 × m) → ℝ) (k ⊕ (Fin 3 × m) → ℝ) q
      (Matrix (k ⊕ (Fin 3 × m)) k ℝ × Matrix k (k ⊕ (Fin 3 × m)) ℝ)}
    (halg : QueryAlgorithm.IsMeasurableFamily alg) {pass : S → ℕ → ℕ}
    (hpass : ∀ s, (alg s).IsPassStructured (pass s)) (hp : ∀ s, ∀ i < q, pass s i < 2)
    (ρ : Measure S) [IsProbabilityMeasure ρ] :
    ∃ U : Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ, HasOrthonormalCols U ∧
      1 - 4 * Real.exp (-(Fintype.card m / 800)) ≤
        ρ.real {s | 14 * Fintype.card m + 33 / 10 * Fintype.card k ≤
          frobNorm (U * Matrix.diagonal (equispacedLevelSpectrum k m 2) * Uᴴ -
            ((alg s).run (U * Matrix.diagonal (equispacedLevelSpectrum k m 2) * Uᴴ).mulVec).1 *
            ((alg s).run (U * Matrix.diagonal (equispacedLevelSpectrum k m 2) * Uᴴ).mulVec).2) ^ 2}
    := by
  sorry

omit [DecidableEq k] [DecidableEq m] in
/-- **Two-pass low-rank approximation needs $\Omega(k/\varepsilon)$ matrix–vector products**: let
$k$ be nonempty, $0 < \varepsilon \le \min\{1/6500, \lvert k \rvert/14000\}$ and
$\lvert m \rvert = \lfloor \lvert k \rvert/(8\varepsilon) \rfloor$, so the dimension is
$n = \lvert k \rvert + 3\lvert m \rvert < \lvert k \rvert/(2\varepsilon)$. If a randomized
algorithm (a measurable seeded family, seed law $\rho$) making $q$ matrix–vector products in at
most two passes (per seed) returns $\mathbf{W}\mathbf{M}$ ($\mathbf{W} \in \mathbb{R}^{n \times
k}$) with
$\|\mathbf{A} - \mathbf{W}\mathbf{M}\|_{\mathsf{F}}^2 \le (1 + \varepsilon)
\|\mathbf{A} - \llbracket \mathbf{A} \rrbracket_k\|_{\mathsf{F}}^2$ with probability at least
$\tfrac12$ for every symmetric $\mathbf{A}$, then
$$q > \frac{\lvert k \rvert}{6400\,\varepsilon} \,.$$
Two passes of randomized SVD with $O(k/\varepsilon)$ products achieve this accuracy in
expectation, so the rate $k/\varepsilon$ is optimal for two-pass algorithms.
No printed source; research note OP5, Corollary B(i), there $q \ge k/(3200\varepsilon) - k$.
Proof: suppose $q \le \lvert k \rvert/(6400\varepsilon)$; then $400(q + \lvert k \rvert) \le
\lvert m \rvert$ and $\lvert m \rvert \ge 1750$ (`Nat.floor` bounds, `Nat.lt_floor_add_one`). Take
the $\mathbf{U}$ of `NLAlib.exists_le_measureReal_frobNorm_sub_mul_sq_ge`; the optimum is
$14\lvert m \rvert$ (`NLAlib.HasOrthonormalCols.frobNorm_mul_diagonal_mul_sub_truncatedSVD_sq`)
and $14\varepsilon\lvert m \rvert \le 1.75\lvert k \rvert < 3.3\lvert k \rvert$, so success and
failure are disjoint, while $1 - 4e^{-1750/800} > \tfrac12$ (`Real.exp_le_exp`, numerical bound on
$e^{-2}$). S, about 40 lines.
Result: two-pass-low-rank-lower-bound -/
theorem div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le [Nonempty k] {ε : ℝ} {q : ℕ}
    (hε : 0 < ε) (hε₁ : ε ≤ 1 / 6500) (hεk : ε ≤ Fintype.card k / 14000)
    (hm : Fintype.card m = ⌊(Fintype.card k : ℝ) / (8 * ε)⌋₊) {S : Type*} [MeasurableSpace S]
    {alg : S → QueryAlgorithm (k ⊕ (Fin 3 × m) → ℝ) (k ⊕ (Fin 3 × m) → ℝ) q
      (Matrix (k ⊕ (Fin 3 × m)) k ℝ × Matrix k (k ⊕ (Fin 3 × m)) ℝ)}
    (halg : QueryAlgorithm.IsMeasurableFamily alg) {pass : S → ℕ → ℕ}
    (hpass : ∀ s, (alg s).IsPassStructured (pass s)) (hp : ∀ s, ∀ i < q, pass s i < 2)
    (ρ : Measure S) [IsProbabilityMeasure ρ]
    (hsucc : ∀ A : Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ, A.IsHermitian →
      1 / 2 ≤ ρ.real {s | frobNorm (A - ((alg s).run A.mulVec).1 * ((alg s).run A.mulVec).2) ^ 2 ≤
        (1 + ε) * frobNorm (A - truncatedSVD A (Fintype.card k)) ^ 2}) :
    Fintype.card k / (6400 * ε) < q := by
  sorry

omit [DecidableEq k] [DecidableEq m] in
/-- **One-pass low-rank approximation needs $\Omega(k/\varepsilon)$ matrix–vector products**: the
statement of `NLAlib.div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le` for algorithms whose
products are all chosen in advance (one pass): with $k$ nonempty,
$0 < \varepsilon \le \min\{1/6500, \lvert k \rvert/14000\}$ and
$\lvert m \rvert = \lfloor \lvert k \rvert/(8\varepsilon) \rfloor$, an algorithm that is within
$(1 + \varepsilon)$ of the best rank-$k$ Frobenius error with probability at least $\tfrac12$ on
every symmetric input makes $q > \lvert k \rvert/(6400\varepsilon)$ products. The best one-pass
upper bound is $O(k/\varepsilon^2)$ (generalized Nyström); the gap is open.
No printed source; research note OP5, Corollary B(iii).
Proof: a one-pass algorithm is a two-pass one (`Nat.lt_succ_of_lt`); apply
`NLAlib.div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le`. S, 3 lines.
Result: one-pass-low-rank-lower-bound -/
theorem div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le_of_lt_one [Nonempty k] {ε : ℝ}
    {q : ℕ} (hε : 0 < ε) (hε₁ : ε ≤ 1 / 6500) (hεk : ε ≤ Fintype.card k / 14000)
    (hm : Fintype.card m = ⌊(Fintype.card k : ℝ) / (8 * ε)⌋₊) {S : Type*} [MeasurableSpace S]
    {alg : S → QueryAlgorithm (k ⊕ (Fin 3 × m) → ℝ) (k ⊕ (Fin 3 × m) → ℝ) q
      (Matrix (k ⊕ (Fin 3 × m)) k ℝ × Matrix k (k ⊕ (Fin 3 × m)) ℝ)}
    (halg : QueryAlgorithm.IsMeasurableFamily alg) {pass : S → ℕ → ℕ}
    (hpass : ∀ s, (alg s).IsPassStructured (pass s)) (hp : ∀ s, ∀ i < q, pass s i < 1)
    (ρ : Measure S) [IsProbabilityMeasure ρ]
    (hsucc : ∀ A : Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ, A.IsHermitian →
      1 / 2 ≤ ρ.real {s | frobNorm (A - ((alg s).run A.mulVec).1 * ((alg s).run A.mulVec).2) ^ 2 ≤
        (1 + ε) * frobNorm (A - truncatedSVD A (Fintype.card k)) ^ 2}) :
    Fintype.card k / (6400 * ε) < q := by
  sorry

omit [DecidableEq k] [DecidableEq m] in
/-- **Two-pass spectral low-rank approximation needs products proportional to the dimension**:
let $k$ be nonempty, $\lvert m \rvert \ge 2812$ and $0 \le \varepsilon \le 1/10$. If a randomized
algorithm (a measurable seeded family, seed law $\rho$) making $q$ matrix–vector products in at
most two passes (per seed) returns $\mathbf{W}\mathbf{M}$ ($\mathbf{W} \in \mathbb{R}^{n \times
k}$) with $\|\mathbf{A} - \mathbf{W}\mathbf{M}\|_2 \le (1 + \varepsilon)\sigma_{k+1}(\mathbf{A})$
with probability at least $\tfrac12$ for every symmetric $\mathbf{A} \in \mathbb{R}^{n \times n}$,
$n = \lvert k \rvert + 3\lvert m \rvert$, then
$$\lvert m \rvert < 676\,(q + \lvert k \rvert) \,,$$
i.e. $q > (n - \lvert k \rvert)/2028 - \lvert k \rvert$, whatever $\varepsilon \le 0.1$.
OP5, Theorem C.
Proof: by contradiction with Yao's principle
`NLAlib.QueryAlgorithm.IsMeasurableFamily.exists_le_measureReal_run_mem_of_forall` as in
`NLAlib.exists_le_measureReal_frobNorm_sub_mul_sq_ge`, from
`NLAlib.QueryAlgorithm.IsPassStructured.measureReal_specNorm_sub_mul_sq_lt_le_of_hasLaw_haarFrame`;
$\sigma_{k+1} = 3$ (`NLAlib.HasOrthonormalCols.singularValues_mul_diagonal_mul_card`),
$(1.1 \cdot 3)^2 = 10.89 < 11.25$, and $1 - 4e^{-2812/1352} > \tfrac12$. M, about 50 lines. -/
theorem lt_of_forall_le_measureReal_specNorm_sub_mul_le [Nonempty k] {ε : ℝ} {q : ℕ}
    (hε : 0 ≤ ε) (hε₁ : ε ≤ 1 / 10) (hm : 2812 ≤ Fintype.card m) {S : Type*}
    [MeasurableSpace S]
    {alg : S → QueryAlgorithm (k ⊕ (Fin 3 × m) → ℝ) (k ⊕ (Fin 3 × m) → ℝ) q
      (Matrix (k ⊕ (Fin 3 × m)) k ℝ × Matrix k (k ⊕ (Fin 3 × m)) ℝ)}
    (halg : QueryAlgorithm.IsMeasurableFamily alg) {pass : S → ℕ → ℕ}
    (hpass : ∀ s, (alg s).IsPassStructured (pass s)) (hp : ∀ s, ∀ i < q, pass s i < 2)
    (ρ : Measure S) [IsProbabilityMeasure ρ]
    (hsucc : ∀ A : Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ, A.IsHermitian →
      1 / 2 ≤ ρ.real {s | specNorm (A - ((alg s).run A.mulVec).1 * ((alg s).run A.mulVec).2) ≤
        (1 + ε) * singularValues A (Fintype.card k)}) :
    Fintype.card m < 676 * (q + Fintype.card k) := by
  sorry

end NLAlib
