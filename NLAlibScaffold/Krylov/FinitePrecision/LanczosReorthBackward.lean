/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlibScaffold.Krylov.FinitePrecision.LanczosReorthRun
public import NLAlibScaffold.Matrix.Perturbation.SymmetricBackward
public import NLAlib.Krylov.Processes.LanczosRecurrence

/-!
# The symmetric backward model of a reorthogonalized Lanczos run (scaffold)

Statements for `NLAlib/Krylov/FinitePrecision/LanczosReorthBackward.lean` (stage
LANCZOS-REORTH, design note `docs/design/Krylov-LanczosReorth.md` §3.2 S3, S5, §3.3, ids E3–E5):
with $\mathbf{U}$ the polar factor of the computed $\mathbf{V}_{k+1}$, there is a symmetric
$n \times n$ perturbation $\mathbf{E}$ of size `NLAlib.LanczosReorthRun.backwardRadius`
$= 100(k+1)(\mu + \varepsilon + \varepsilon_2)\|\mathbf{H}\|_2$ for which the computed
tridiagonal is exactly the Lanczos tridiagonal of $(\mathbf{H} + \mathbf{E}, \mathbf{u}_1)$, and,
after an orthogonal similarity close to the identity, of $(\mathbf{H}', \mathbf{b})$ for the
exact start vector. No dilation is needed (compare `NLAlib/Krylov/FinitePrecision/Backward.lean`
for plain Lanczos). [Paige1970] (primary, locator to verify); [Simon1984b]; [Stewart2002] for
Krylov decompositions.

Common hypotheses as in `NLAlibScaffold/Krylov/FinitePrecision/LanczosReorthRun.lean`.

## Main results

* `NLAlib.LanczosReorthRun.exists_backward`: S3, the identity and the bound (E3).
* `NLAlib.LanczosReorthRun.exists_lanczosState_backward`: exact Lanczos on the model (E4).
* `NLAlib.LanczosReorthRun.exists_pure_backward`: the exact start vector (E5).
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

namespace LanczosReorthRun

variable {n k : ℕ} (L : LanczosReorthRun n k)

/-- **The symmetric backward model** (E3, S3): with $\mathbf{U} = $ `NLAlib.polarFactor`
$\mathbf{V}_{k+1}$ and $\mathbf{U}_k$ its first $k$ columns, some symmetric $\mathbf{E}$ with
$\|\mathbf{E}\|_{\mathsf F} \le$ `NLAlib.LanczosReorthRun.backwardRadius` satisfies
$$(\mathbf{H} + \mathbf{E})\mathbf{U}_k = \mathbf{U}_k\mathbf{T}_k +
(\beta_k\mathbf{u}_{k+1})\mathbf{e}_{k-1}^{\mathsf{T}}$$
exactly. [Paige1970] (locator to verify); [KahanParlettJiang1982] for the completion.
Proof: $\mathbf{U}$ is orthonormal (`NLAlib.hasOrthonormalCols_polarFactor`, with
`frobNorm_gram_sub_one_le` at $m = k+1$ and `specNorm_le_frobNorm`), so are its first $k$
columns. Put $\mathbf{R} = \mathbf{H}\mathbf{U}_k - \mathbf{U}_k\mathbf{T}_k -
(\beta_k\mathbf{u}_{k+1})\mathbf{e}^{\mathsf{T}}$; $\mathbf{U}_k^{\mathsf{T}}\mathbf{R} =
\mathbf{U}_k^{\mathsf{T}}\mathbf{H}\mathbf{U}_k - \mathbf{T}_k$ is symmetric (`transpose_H`,
`NLAlib.LanczosData.transpose_tridiagonal`, orthonormality kills the last term). Apply
`NLAlib.exists_transpose_eq_mul_eq_neg_of_hasOrthonormalCols`. Bound: by
`NLAlib.LanczosData.mul_basis`, $\mathbf{R} = \mathbf{H}(\mathbf{U} - \mathbf{V})_k -
(\mathbf{U} - \mathbf{V})_k\mathbf{T}_k - \beta_k(\mathbf{u}_{k+1} - \mathbf{v}_{k+1})
\mathbf{e}^{\mathsf{T}} - \mathbf{F}_k$, so $\|\mathbf{R}\|_{\mathsf F} \le (\|\mathbf{H}\| +
\|\mathbf{T}_k\| + \beta_k)\|\mathbf{U} - \mathbf{V}\|_{\mathsf F} + \|\mathbf{F}_k\|_{\mathsf F}$
with
`NLAlib.frobNorm_polarFactor_sub_le`, `coeff_le` ($\|\mathbf{T}_k\|_2 \le \tfrac92\|\mathbf{H}\|$),
`frobNorm_residual_le`; numerically $\sqrt2(7 \cdot \sqrt3/1.99 +
20)(k+1)\,\mathrm{rec}\,\|\mathbf{H}\|
\le 100(k+1)\,\mathrm{rec}\,\|\mathbf{H}\|$. L, about 150 lines; intermediate lemmas: the
symmetry of $\mathbf{U}_k^{\mathsf{T}}\mathbf{R}$, the decomposition of $\mathbf{R}$. -/
theorem exists_backward (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) (hτ : L.τ ≤ 1) :
    ∃ E : Matrix (Fin n) (Fin n) ℝ, Eᵀ = E ∧ frobNorm E ≤ L.backwardRadius ∧
      (L.H + E) * (polarFactor (basisOf L.v (k + 1))).submatrix id Fin.castSucc =
        (polarFactor (basisOf L.v (k + 1))).submatrix id Fin.castSucc *
          L.toLanczosData.tridiagonal +
        Matrix.vecMulVec (L.β k • fun i => polarFactor (basisOf L.v (k + 1)) i (Fin.last k))
          (Pi.single L.toLanczosData.lastIndex 1) := by
  sorry

/-- **Exact Lanczos on the backward model computes the run** (E4): with $\mathbf{u}_j$ the
columns of the polar factor (`NLAlib.LanczosReorthRun.colSeq`), the exact Lanczos recurrence on
$(\mathbf{H} + \mathbf{E}, \mathbf{u}_1)$ has states $(\mathbf{u}_j, \mathbf{u}_{j+1}, \beta_j)$
for $j < k$ and tridiagonal $\mathbf{T}_k$; the start vector is within
$2\sqrt{3(k+1)}\,\mu$ of $\mathbf{v}_1$. [Paige1970] (locator to verify).
Proof: `NLAlib.LanczosReorthRun.exists_backward`; the columnwise form of its identity is the
three-term recurrence of `NLAlib.lanczosState_eq_of_orthonormal_recurrence` for
`colSeq U` (orthonormal $\mathbf{u}_1, \dots, \mathbf{u}_{k+1}$, $\beta_0 = 0$, $\beta_j > 0$ for
$1 \le j \le k$ by `admissible` and $\nu \ge 0$-type facts); $\mathbf{T}_k$ by
`NLAlib.lanczosState_beta_eq_of_orthonormal_recurrence` and $\alpha_{j+1} =$ `NLAlib.lanczosAlpha`
of the state (orthonormality). Start vector: $\|\mathbf{u}_1 - \mathbf{v}_1\| \le \|\mathbf{U} -
\mathbf{V}\|_{\mathsf F}$ and `NLAlib.frobNorm_polarFactor_sub_le`. M, about 90 lines. -/
theorem exists_lanczosState_backward (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) (hτ : L.τ ≤ 1) :
    ∃ E : Matrix (Fin n) (Fin n) ℝ, Eᵀ = E ∧ frobNorm E ≤ L.backwardRadius ∧
      (∀ j < k, lanczosState (L.H + E) (colSeq (polarFactor (basisOf L.v (k + 1))) 1) j =
        ⟨colSeq (polarFactor (basisOf L.v (k + 1))) j,
          colSeq (polarFactor (basisOf L.v (k + 1))) (j + 1), L.β j⟩) ∧
      lanczosTridiagonal (L.H + E) (colSeq (polarFactor (basisOf L.v (k + 1))) 1) k =
        L.toLanczosData.tridiagonal ∧
      ‖WithLp.toLp 2 (colSeq (polarFactor (basisOf L.v (k + 1))) 1 - L.v 1)‖ ≤
        2 * Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel := by
  sorry

/-- **The backward model with the exact start vector** (E5, S5): if the computed $\mathbf{v}_1$ is
within $\delta_b$ of $\mathbf{b}/\|\mathbf{b}\|$, some symmetric $\mathbf{H}'$ with
$$\|\mathbf{H}' - \mathbf{H}\|_{\mathsf F} \le \text{backwardRadius} + 3\|\mathbf{H}\|_2\,
(\delta_b + 2\sqrt{3(k+1)}\,\mu)$$
has Lanczos tridiagonal $\mathbf{T}_k$ from $\mathbf{b}$ itself. No printed source.
Proof: `NLAlib.LanczosReorthRun.exists_lanczosState_backward`; the unit vectors $\mathbf{u}_1$ and
$\hat{\mathbf{b}} = \mathbf{b}/\|\mathbf{b}\|$ ($\|\mathbf{u}_1\| = 1$ by orthonormality) are within
$\delta_b + 2\sqrt{3(k+1)}\,\mu$; `NLAlib.exists_orthogonal_mulVec_eq_specNorm_sub_one_le` gives
$\mathbf{Z}$; put $\mathbf{H}' = \mathbf{Z}(\mathbf{H} + \mathbf{E})\mathbf{Z}^{\mathsf{T}}$.
Exact Lanczos is equivariant under orthogonal similarity (states map by $\mathbf{Z}$, coefficients
unchanged: induction on `NLAlib.lanczosStep` with `Matrix.mulVec_mulVec`, `NLAlib.lanczosAlpha`
and norm invariance) and `NLAlib.lanczosState` normalizes $\mathbf{b}$. Bound:
$\mathbf{H}' - \mathbf{H} = \mathbf{Z}\mathbf{E}\mathbf{Z}^{\mathsf{T}} + (\mathbf{Z} - \mathbf{I})
\mathbf{H}\mathbf{Z}^{\mathsf{T}} + \mathbf{H}(\mathbf{Z}^{\mathsf{T}} - \mathbf{I})$ and
$\mathbf{Z} - \mathbf{I}$ has rank $\le 2$, so $\|\mathbf{Z} - \mathbf{I}\|_{\mathsf F} \le
\sqrt2\|\mathbf{Z} - \mathbf{I}\|_2$ and $2\sqrt2 \le 3$. M, about 100 lines; intermediate lemma:
the equivariance of `NLAlib.lanczosState`. -/
theorem exists_pure_backward (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) (hτ : L.τ ≤ 1) {b : Fin n → ℝ} (hb : b ≠ 0) {δb : ℝ}
    (hδ : ‖WithLp.toLp 2 (‖WithLp.toLp 2 b‖⁻¹ • b - L.v 1)‖ ≤ δb) :
    ∃ H' : Matrix (Fin n) (Fin n) ℝ, H'ᵀ = H' ∧
      frobNorm (H' - L.H) ≤ L.backwardRadius +
        3 * specNorm L.H * (δb + 2 * Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel) ∧
      lanczosTridiagonal H' b k = L.toLanczosData.tridiagonal := by
  sorry

end LanczosReorthRun

end NLAlib
