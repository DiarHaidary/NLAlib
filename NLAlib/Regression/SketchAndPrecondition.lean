/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.LinearSystems.PCGRecurrence
public import NLAlib.Regression.Embedding
public import NLAlib.Sketching.Properties.FixedSubspace

/-!
# Sketch-and-precondition

`NLAlib.sketchAndPrecondition A S y x₀ q` is the preconditioned conjugate gradient iterate on the
normal equations $\mathbf{A}^{\mathsf{H}}\mathbf{A}\mathbf{x} = \mathbf{A}^{\mathsf{H}}\mathbf{y}$
of the least-squares problem $\min_{\mathbf{x}}\|\mathbf{y} - \mathbf{A}\mathbf{x}\|$, with
preconditioner $\mathbf{G}^{+}$ for the sketched Gram matrix
$\mathbf{G} = (\mathbf{S}\mathbf{A})^{\mathsf{H}}\mathbf{S}\mathbf{A}$, after $q$ steps from
$\mathbf{x}_0$. The definition is basis-free. For any square $\mathbf{M}$ with
$\mathbf{S}\mathbf{A}\mathbf{M}$ orthonormal (QR's $\mathbf{R}^{-1}$, as in Blendenpik, or SVD's
$\mathbf{V}\mathbf{\Sigma}^{-1}$, as in LSRN) it is $\mathbf{M}$ times CGLS on
$\mathbf{A}\mathbf{M}$, which is preconditioned LSQR in exact arithmetic, and the preconditioned
Hestenes–Stiefel recurrence computes it.

If $\mathbf{S}$ is a subspace embedding of $\operatorname{range}\mathbf{A}$ with constants
$a, b$ in squared norms, the spectrum of $\mathbf{G}^{+}\mathbf{A}^{\mathsf{H}}\mathbf{A}$ lies in
$[b^{-1}, a^{-1}]$ (`NLAlib.IsSubspaceEmbedding.spectrum_pinv_mul_subset_Icc`), so the energy
error $\|\mathbf{A}(\mathbf{x}_\star - \mathbf{x}_q)\|^2$ contracts at the Chebyshev rate
$\bigl((\sqrt{b/a} - 1)/(\sqrt{b/a} + 1)\bigr)^2$ per step from every start. From the
sketch-and-solve start the residual is within a factor
$1 + 4(b/a - 1)\rho^{2q}$ of the optimal squared residual, and the forward error follows through
the smallest singular value. In the unsquared distortion $\eta$ of Epperly
($a = (1 - \eta)^2$, $b = (1 + \eta)^2$) the rate $\rho$ is exactly $\eta$.

The probabilistic statements take an embedding that fails with probability $\delta$
(`NLAlib.HasSubspaceEmbedding`); the sketch families are in `NLAlib.Regression.Gaussian`,
`NLAlib.Regression.SubGaussian`, `NLAlib.Regression.SRHT` and `NLAlib.Regression.CountSketch`.
[MartinssonTropp2020]; [Epperly2024]; [EpperlyMeierNakatsukasa2024].
Design: `docs/design/Regression-SketchPrecondition.md`.

## Main definitions

* `NLAlib.sketchAndPrecondition`: the sketch-and-precondition iterate.

## Main results

* `NLAlib.HasOrthonormalCols.sketchAndPrecondition_eq_mulVec_cgIterate`,
  `NLAlib.IsQR.sketchAndPrecondition_eq_mulVec_cgIterate`,
  `NLAlib.IsSVD.sketchAndPrecondition_eq_mulVec_cgIterate`: CGLS on the preconditioned matrix.
* `NLAlib.pcgState_x_eq_sketchAndPrecondition`: the recurrence computes it.
* `NLAlib.IsSubspaceEmbedding.norm_mulVec_sub_sketchAndPrecondition_sq_le_four_mul_pow`: geometric
  convergence of the energy error from any start.
* `NLAlib.IsSubspaceEmbedding.norm_sub_mulVec_sketchAndPrecondition_sq_le`: the residual from the
  sketch-and-solve start.
* `NLAlib.IsSubspaceEmbedding.norm_sub_mulVec_sketchAndPrecondition_sq_le_one_add_mul`: the
  iteration count for a relative residual $1 + \tau$.
* `NLAlib.IsSubspaceEmbedding.singularValues_sq_mul_norm_sub_sketchAndPrecondition_sq_le`: the
  forward error.
* `NLAlib.HasSubspaceEmbedding.measureReal_norm_mulVec_sub_sketchAndPrecondition_sq_gt_le`,
  `NLAlib.HasSubspaceEmbedding.measureReal_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le`: the
  same with a random embedding.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix ComplexOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {k m n r : Type*} [Fintype k] [Fintype m] [Fintype n]
  [DecidableEq n]

/-! ### The iterate and its realisations -/

/-- The **sketch-and-precondition iterate** after $q$ steps from $\mathbf{x}_0$, for
$\mathbf{A} \in \Bbbk^{m \times n}$, a sketch $\mathbf{S} \in \Bbbk^{k \times m}$ and
$\mathbf{y} \in \Bbbk^m$:
$$\mathsf{sketchAndPrecondition}(\mathbf{A}, \mathbf{S}, \mathbf{y}, \mathbf{x}_0, q) :=
\mathsf{pcgIterate}(\mathbf{A}^{\mathsf{H}}\mathbf{A}, \mathbf{G}^{+},
\mathbf{A}^{\mathsf{H}}\mathbf{y}, \mathbf{x}_0, q)$$
with $\mathbf{G} = (\mathbf{S}\mathbf{A})^{\mathsf{H}}\mathbf{S}\mathbf{A}$: preconditioned CG on
the normal equations, preconditioned by the sketched Gram matrix. Basis-free. For a QR
factorization $\mathbf{S}\mathbf{A} = \mathbf{Q}\mathbf{R}$ it is $\mathbf{R}^{-1}$ times CGLS on
$\mathbf{A}\mathbf{R}^{-1}$ (`NLAlib.IsQR.sketchAndPrecondition_eq_mulVec_cgIterate`), which is
preconditioned LSQR in exact arithmetic; for an SVD it uses LSRN's preconditioner
(`NLAlib.IsSVD.sketchAndPrecondition_eq_mulVec_cgIterate`); the preconditioned Hestenes–Stiefel
recurrence computes it (`NLAlib.pcgState_x_eq_sketchAndPrecondition`). The sketch-and-solve start
is $\mathbf{x}_0 = (\mathbf{S}\mathbf{A})^{+}\mathbf{S}\mathbf{y}$. Junk value: that of
`NLAlib.pcgIterate` when $\mathbf{A}$ is rank deficient.
[MartinssonTropp2020, §10.5]; [Epperly2024, Algorithm 1], there with LSQR and the QR
preconditioner. -/
noncomputable def sketchAndPrecondition (A : Matrix m n 𝕜) (S : Matrix k m 𝕜) (y : m → 𝕜)
    (x₀ : n → 𝕜) (q : ℕ) : n → 𝕜 :=
  pcgIterate (Aᴴ * A) (pinv ((S * A)ᴴ * (S * A))) (Aᴴ *ᵥ y) x₀ q

variable {S : Matrix k m 𝕜} {A : Matrix m n 𝕜} {y : m → 𝕜} {xs x₀ : n → 𝕜} {a b ε : ℝ}

/-- **Sketch-and-precondition is CGLS on $\mathbf{A}\mathbf{M}$**: for
$\mathbf{A} \in \Bbbk^{m \times n}$, a sketch $\mathbf{S}$, a square $\mathbf{M}$ with
$\mathbf{S}\mathbf{A}\mathbf{M}$ orthonormal and $\mathbf{M}\mathbf{z}_0 = \mathbf{x}_0$,
$$\mathsf{sketchAndPrecondition}(\mathbf{A}, \mathbf{S}, \mathbf{y}, \mathbf{x}_0, q) =
\mathbf{M}\,\mathsf{cgIterate}((\mathbf{A}\mathbf{M})^{\mathsf{H}}\mathbf{A}\mathbf{M},
(\mathbf{A}\mathbf{M})^{\mathsf{H}}\mathbf{y}, \mathbf{z}_0, q)\,.$$
Orthonormality makes $\mathbf{M}$ and $\mathbf{A}$ injective, so no rank hypothesis is needed.
[EpperlyMeierNakatsukasa2024, §2.1], there for $\mathbf{M} = \mathbf{R}^{-1}$, where CG on the
preconditioned normal equations is LSQR in exact arithmetic.
Result: sketch-and-precondition-realisation -/
theorem HasOrthonormalCols.sketchAndPrecondition_eq_mulVec_cgIterate {M : Matrix n n 𝕜}
    (hSAM : HasOrthonormalCols (S * A * M)) (y : m → 𝕜) {z₀ : n → 𝕜} (hz₀ : M *ᵥ z₀ = x₀)
    (q : ℕ) :
    sketchAndPrecondition A S y x₀ q =
      M *ᵥ cgIterate ((A * M)ᴴ * (A * M)) ((A * M)ᴴ *ᵥ y) z₀ q := by
  sorry

/-- **Sketch-and-precondition with QR** (Blendenpik): for a thin QR factorization
$\mathbf{S}\mathbf{A} = \mathbf{Q}\mathbf{R}$ with $\mathbf{R}$ invertible, the iterate is
$\mathbf{R}^{-1}$ times CGLS on $\mathbf{A}\mathbf{R}^{-1}$ from $\mathbf{R}\mathbf{x}_0$:
$$\mathsf{sketchAndPrecondition}(\mathbf{A}, \mathbf{S}, \mathbf{y}, \mathbf{x}_0, q) =
\mathbf{R}^{-1}\,\mathsf{cgIterate}((\mathbf{A}\mathbf{R}^{-1})^{\mathsf{H}}
\mathbf{A}\mathbf{R}^{-1},
(\mathbf{A}\mathbf{R}^{-1})^{\mathsf{H}}\mathbf{y}, \mathbf{R}\mathbf{x}_0, q)\,.$$
[Epperly2024, Algorithm 1], there with LSQR. -/
theorem IsQR.sketchAndPrecondition_eq_mulVec_cgIterate [LinearOrder n] {Q : Matrix k n 𝕜}
    {R : Matrix n n 𝕜} (hQR : IsQR (S * A) Q R) (hR : IsUnit R) (y : m → 𝕜) (q : ℕ) :
    sketchAndPrecondition A S y x₀ q =
      R⁻¹ *ᵥ cgIterate ((A * R⁻¹)ᴴ * (A * R⁻¹)) ((A * R⁻¹)ᴴ *ᵥ y) (R *ᵥ x₀) q := by
  sorry

/-- **Sketch-and-precondition with an SVD** (LSRN's preconditioner): for a singular value
decomposition $\mathbf{S}\mathbf{A} = \mathbf{U}\mathbf{\Sigma}\mathbf{V}^{\mathsf{H}}$ with square
$\mathbf{V}$ and every $\sigma_i > 0$, the iterate is $\mathbf{V}\mathbf{\Sigma}^{-1}$ times CGLS on
$\mathbf{A}\mathbf{V}\mathbf{\Sigma}^{-1}$ from
$\mathbf{\Sigma}\mathbf{V}^{\mathsf{H}}\mathbf{x}_0$:
with $\mathbf{N} = \mathbf{V}\mathbf{\Sigma}^{-1}$,
$$\mathsf{sketchAndPrecondition}(\mathbf{A}, \mathbf{S}, \mathbf{y}, \mathbf{x}_0, q) =
\mathbf{N}\,\mathsf{cgIterate}((\mathbf{A}\mathbf{N})^{\mathsf{H}}\mathbf{A}\mathbf{N},
(\mathbf{A}\mathbf{N})^{\mathsf{H}}\mathbf{y}, \mathbf{\Sigma}\mathbf{V}^{\mathsf{H}}\mathbf{x}_0,
q)\,.$$
Here $\mathbf{S}\mathbf{A}\mathbf{N} = \mathbf{U}$ has orthonormal columns.
[EpperlyMeierNakatsukasa2024, Fact 2.2], there for any orthogonal factorization. -/
theorem IsSVD.sketchAndPrecondition_eq_mulVec_cgIterate {U : Matrix k n 𝕜} {σ : n → ℝ}
    {V : Matrix n n 𝕜} (hSVD : IsSVD (S * A) U σ V) (hσ : ∀ i, 0 < σ i) (y : m → 𝕜) (q : ℕ) :
    sketchAndPrecondition A S y x₀ q =
      (V * Matrix.diagonal fun i => ((σ i)⁻¹ : 𝕜)) *ᵥ
        cgIterate ((A * (V * Matrix.diagonal fun i => ((σ i)⁻¹ : 𝕜)))ᴴ *
            (A * (V * Matrix.diagonal fun i => ((σ i)⁻¹ : 𝕜))))
          ((A * (V * Matrix.diagonal fun i => ((σ i)⁻¹ : 𝕜)))ᴴ *ᵥ y)
          ((Matrix.diagonal fun i => ((σ i : ℝ) : 𝕜)) *ᵥ (Vᴴ *ᵥ x₀)) q := by
  sorry

/-- **The preconditioned Hestenes–Stiefel recurrence computes sketch-and-precondition**: when
$\mathbf{S}\mathbf{A}$ has full column rank (so that $\mathbf{A}$ does), the $\mathbf{x}$-field of
`NLAlib.pcgState` for the normal equations
$\mathbf{A}^{\mathsf{H}}\mathbf{A}\mathbf{x} = \mathbf{A}^{\mathsf{H}}\mathbf{y}$ with
preconditioner
$((\mathbf{S}\mathbf{A})^{\mathsf{H}}\mathbf{S}\mathbf{A})^{+}$ after $q$ steps from
$\mathbf{x}_0$ is $\mathsf{sketchAndPrecondition}(\mathbf{A}, \mathbf{S}, \mathbf{y},
\mathbf{x}_0, q)$.
[Epperly2024, Algorithm 1], there through LSQR.
Result: sketch-and-precondition-realisation -/
theorem pcgState_x_eq_sketchAndPrecondition (hSA : Function.Injective (S * A).mulVec)
    (y : m → 𝕜) (x₀ : n → 𝕜) (q : ℕ) :
    (pcgState (Aᴴ * A) (pinv ((S * A)ᴴ * (S * A))) (Aᴴ *ᵥ y) x₀ q).x =
      sketchAndPrecondition A S y x₀ q := by
  sorry

/-! ### Deterministic convergence -/

/-- **Sketch-and-precondition converges geometrically**: if $\mathbf{S}$ is a subspace embedding
of $\operatorname{range}\mathbf{A}$ with constants $a > 0$, $b$ in squared norms
($a\|\mathbf{v}\|^2 \le \|\mathbf{S}\mathbf{v}\|^2 \le b\|\mathbf{v}\|^2$ for
$\mathbf{v} \in \operatorname{range}\mathbf{A}$), $\mathbf{A}$ has full column rank and
$\mathbf{x}_\star$ is a least-squares solution of $\mathbf{A}\mathbf{x} \approx \mathbf{y}$, then
for every start $\mathbf{x}_0$ and every $q$
$$\|\mathbf{A}(\mathbf{x}_\star - \mathsf{sketchAndPrecondition}(\mathbf{A}, \mathbf{S},
\mathbf{y}, \mathbf{x}_0, q))\|^2 \le 4\Bigl(\frac{\sqrt{b/a} - 1}{\sqrt{b/a} + 1}\Bigr)^{2q}
\|\mathbf{A}(\mathbf{x}_\star - \mathbf{x}_0)\|^2\,.$$
In the unsquared distortion $\eta$ of Epperly ($a = (1 - \eta)^2$, $b = (1 + \eta)^2$) the rate is
exactly $\eta$. [MartinssonTropp2020, §10.5], there a residual bound after
$j \sim \log(1/\varepsilon)$ steps with no constants; [EpperlyMeierNakatsukasa2024, Fact 2.2],
the conditioning that gives the rate.
Result: sketch-and-precondition-convergence -/
theorem IsSubspaceEmbedding.norm_mulVec_sub_sketchAndPrecondition_sq_le_four_mul_pow
    (h : IsSubspaceEmbedding S A a b) (ha : 0 < a) (hA : Function.Injective A.mulVec)
    (hxs : IsLeastSquaresSolution A y xs) (x₀ : n → 𝕜) (q : ℕ) :
    ‖WithLp.toLp 2 (A *ᵥ (xs - sketchAndPrecondition A S y x₀ q))‖ ^ 2 ≤
      4 * ((√(b / a) - 1) / (√(b / a) + 1)) ^ (2 * q) *
        ‖WithLp.toLp 2 (A *ᵥ (xs - x₀))‖ ^ 2 := by
  sorry

/-- **Sketch-and-precondition, $\varepsilon$ form**: if $\mathbf{S}$ is a subspace embedding of
$\operatorname{range}\mathbf{A}$ with constants $1 \mp \varepsilon$ in squared norms
($(1 - \varepsilon)\|\mathbf{v}\|^2 \le \|\mathbf{S}\mathbf{v}\|^2 \le
(1 + \varepsilon)\|\mathbf{v}\|^2$ for $\mathbf{v} \in \operatorname{range}\mathbf{A}$),
$0 < \varepsilon < 1$, $\mathbf{A}$ has full column rank and $\mathbf{x}_\star$ is a
least-squares solution of $\mathbf{A}\mathbf{x} \approx \mathbf{y}$, then for every start
$$\|\mathbf{A}(\mathbf{x}_\star - \mathsf{sketchAndPrecondition}(\mathbf{A}, \mathbf{S},
\mathbf{y}, \mathbf{x}_0, q))\|^2 \le 4\varepsilon^{2q}
\|\mathbf{A}(\mathbf{x}_\star - \mathbf{x}_0)\|^2\,.$$
The exact rate is $\varepsilon/(1 + \sqrt{1 - \varepsilon^2}) \le \varepsilon$. Here
$\varepsilon$ is the squared-norm distortion, not Epperly's unsquared $\eta$, for which the rate is
$\eta$. -/
theorem
    IsSubspaceEmbedding.norm_mulVec_sub_sketchAndPrecondition_sq_le_four_mul_pow_of_one_sub_one_add
    (h : IsSubspaceEmbedding S A (1 - ε) (1 + ε)) (hε : 0 < ε) (hε1 : ε < 1)
    (hA : Function.Injective A.mulVec) (hxs : IsLeastSquaresSolution A y xs) (x₀ : n → 𝕜)
    (q : ℕ) :
    ‖WithLp.toLp 2 (A *ᵥ (xs - sketchAndPrecondition A S y x₀ q))‖ ^ 2 ≤
      4 * ε ^ (2 * q) * ‖WithLp.toLp 2 (A *ᵥ (xs - x₀))‖ ^ 2 := by
  sorry

section Residual

variable [DecidableEq m]

/-- **Sketch-and-precondition from the sketch-and-solve start**: if $\mathbf{S}$ is a subspace
embedding with constants $a > 0$, $b$ in squared norms
($a\|\mathbf{v}\|^2 \le \|\mathbf{S}\mathbf{v}\|^2 \le b\|\mathbf{v}\|^2$ for
$\mathbf{v} \in \operatorname{range}\mathbf{U}$) of a subspace $\operatorname{range}\mathbf{U}$
containing $\operatorname{range}\mathbf{A}$ and $\mathbf{y}$, $\mathbf{A}$ has full column rank
and $\mathbf{x}_0$ is any minimizer of $\|\mathbf{S}(\mathbf{A}\mathbf{x} - \mathbf{y})\|$, then
$$\|\mathbf{y} - \mathbf{A}\,\mathsf{sketchAndPrecondition}(\mathbf{A}, \mathbf{S}, \mathbf{y},
\mathbf{x}_0, q)\|^2 \le \Bigl(1 + 4\Bigl(\frac{b}{a} - 1\Bigr)
\Bigl(\frac{\sqrt{b/a} - 1}{\sqrt{b/a} + 1}\Bigr)^{2q}\Bigr)
\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{y}\|^2\,,$$
the last factor being the optimal squared residual. In Epperly's unsquared $\eta$
($a = (1 - \eta)^2$, $b = (1 + \eta)^2$) the factor is $1 + 16\eta^{2q+1}/(1 - \eta)^2$. The
bound is squared; [MartinssonTropp2020, §10.5] states an unsquared $1 + \varepsilon$ after
$j \sim \log(1/\varepsilon)$ steps; [Epperly2024, Algorithm 1 and Fact 4], the start and its
error.
Result: sketch-and-precondition-ls -/
theorem IsSubspaceEmbedding.norm_sub_mulVec_sketchAndPrecondition_sq_le [Fintype r]
    {U : Matrix m r 𝕜} (h : IsSubspaceEmbedding S U a b) (ha : 0 < a)
    (hAU : LinearMap.range A.mulVecLin ≤ LinearMap.range U.mulVecLin)
    (hy : y ∈ LinearMap.range U.mulVecLin) (hA : Function.Injective A.mulVec)
    (hx₀ : IsLeastSquaresSolution (S * A) (S *ᵥ y) x₀) (q : ℕ) :
    ‖WithLp.toLp 2 (y - A *ᵥ sketchAndPrecondition A S y x₀ q)‖ ^ 2 ≤
      (1 + 4 * (b / a - 1) * ((√(b / a) - 1) / (√(b / a) + 1)) ^ (2 * q)) *
        ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2 := by
  sorry

/-- **Sketch-and-precondition from the sketch-and-solve start, $\varepsilon$ form**: if
$\mathbf{S}$ is a subspace embedding of $\operatorname{range}[\mathbf{A}\ \mathbf{y}]$ with
constants $1 \mp \varepsilon$ in squared norms
($(1 - \varepsilon)\|\mathbf{v}\|^2 \le \|\mathbf{S}\mathbf{v}\|^2 \le
(1 + \varepsilon)\|\mathbf{v}\|^2$ on that range), $0 < \varepsilon < 1$, $\mathbf{A}$ has full
column rank and $\mathbf{x}_0$ minimizes $\|\mathbf{S}(\mathbf{A}\mathbf{x} - \mathbf{y})\|$, then
$$\|\mathbf{y} - \mathbf{A}\,\mathsf{sketchAndPrecondition}(\mathbf{A}, \mathbf{S}, \mathbf{y},
\mathbf{x}_0, q)\|^2 \le \Bigl(1 + \frac{8\varepsilon^{2q+1}}{1 - \varepsilon}\Bigr)
\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{y}\|^2\,,$$
the last factor being the optimal squared residual. -/
theorem IsSubspaceEmbedding.norm_sub_mulVec_sketchAndPrecondition_sq_le_of_one_sub_one_add
    (h : IsSubspaceEmbedding S (Matrix.fromCols A (Matrix.replicateCol Unit y)) (1 - ε) (1 + ε))
    (hε : 0 < ε) (hε1 : ε < 1) (hA : Function.Injective A.mulVec)
    (hx₀ : IsLeastSquaresSolution (S * A) (S *ᵥ y) x₀) (q : ℕ) :
    ‖WithLp.toLp 2 (y - A *ᵥ sketchAndPrecondition A S y x₀ q)‖ ^ 2 ≤
      (1 + 8 * ε ^ (2 * q + 1) / (1 - ε)) *
        ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2 := by
  sorry

/-- **Sketch-and-precondition, iteration count**: if $\mathbf{S}$ is a subspace embedding of
$\operatorname{range}[\mathbf{A}\ \mathbf{y}]$ with constants $1 \mp \varepsilon$ in squared norms
($(1 - \varepsilon)\|\mathbf{v}\|^2 \le \|\mathbf{S}\mathbf{v}\|^2 \le
(1 + \varepsilon)\|\mathbf{v}\|^2$ on that range), $0 < \varepsilon \le 1/2$, $\mathbf{A}$ has full
column rank, $\mathbf{x}_0$ minimizes $\|\mathbf{S}(\mathbf{A}\mathbf{x} - \mathbf{y})\|$ and
$16\varepsilon^{2q+1} \le \tau$, then
$$\|\mathbf{y} - \mathbf{A}\,\mathsf{sketchAndPrecondition}(\mathbf{A}, \mathbf{S}, \mathbf{y},
\mathbf{x}_0, q)\|^2 \le (1 + \tau)\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{y}\|^2\,.$$
At $\varepsilon = 1/2$, $q \ge \log(8/\tau)/\log 4$ steps suffice. -/
theorem IsSubspaceEmbedding.norm_sub_mulVec_sketchAndPrecondition_sq_le_one_add_mul
    (h : IsSubspaceEmbedding S (Matrix.fromCols A (Matrix.replicateCol Unit y)) (1 - ε) (1 + ε))
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (hA : Function.Injective A.mulVec)
    (hx₀ : IsLeastSquaresSolution (S * A) (S *ᵥ y) x₀) {q : ℕ} {τ : ℝ}
    (hq : 16 * ε ^ (2 * q + 1) ≤ τ) :
    ‖WithLp.toLp 2 (y - A *ᵥ sketchAndPrecondition A S y x₀ q)‖ ^ 2 ≤
      (1 + τ) * ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2 := by
  sorry

/-- **Forward error of sketch-and-precondition from the sketch-and-solve start**: if $\mathbf{S}$
is a subspace embedding with constants $a > 0$, $b$ in squared norms
($a\|\mathbf{v}\|^2 \le \|\mathbf{S}\mathbf{v}\|^2 \le b\|\mathbf{v}\|^2$ for
$\mathbf{v} \in \operatorname{range}\mathbf{U}$) of a subspace $\operatorname{range}\mathbf{U}$
containing $\operatorname{range}\mathbf{A}$ and $\mathbf{y}$, $\mathbf{A}$ has full column rank,
$\mathbf{x}_\star$ is the least-squares solution, $\mathbf{x}_0$ is any minimizer of
$\|\mathbf{S}(\mathbf{A}\mathbf{x} - \mathbf{y})\|$ and
$\sigma_{\min}(\mathbf{A}) = \sigma_j(\mathbf{A})$ with $j + 1 = \lvert n\rvert$, then
$$\sigma_{\min}(\mathbf{A})^2\,\|\mathbf{x}_\star - \mathsf{sketchAndPrecondition}(\mathbf{A},
\mathbf{S}, \mathbf{y}, \mathbf{x}_0, q)\|^2 \le 4\Bigl(\frac{b}{a} - 1\Bigr)
\Bigl(\frac{\sqrt{b/a} - 1}{\sqrt{b/a} + 1}\Bigr)^{2q}
\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{y}\|^2\,.$$
Epperly's forward-error form, multiplied out so that no division appears.
[Epperly2024, Theorem 5], there for iterative sketching, as
$\|\mathbf{x} - \mathbf{x}_i\| \lesssim \kappa\,\|\mathbf{r}(\mathbf{x})\|/\|\mathbf{A}\|_2$. -/
theorem IsSubspaceEmbedding.singularValues_sq_mul_norm_sub_sketchAndPrecondition_sq_le
    [Fintype r] {U : Matrix m r 𝕜} (h : IsSubspaceEmbedding S U a b) (ha : 0 < a)
    (hAU : LinearMap.range A.mulVecLin ≤ LinearMap.range U.mulVecLin)
    (hy : y ∈ LinearMap.range U.mulVecLin) (hA : Function.Injective A.mulVec)
    (hxs : IsLeastSquaresSolution A y xs)
    (hx₀ : IsLeastSquaresSolution (S * A) (S *ᵥ y) x₀) {j : ℕ} (hj : j + 1 = Fintype.card n)
    (q : ℕ) :
    singularValues A j ^ 2 * ‖WithLp.toLp 2 (xs - sketchAndPrecondition A S y x₀ q)‖ ^ 2 ≤
      4 * (b / a - 1) * ((√(b / a) - 1) / (√(b / a) + 1)) ^ (2 * q) *
        ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2 := by
  sorry

end Residual

/-! ### With a random embedding -/

section Random

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {δ : ℝ}

/-- **Sketch-and-precondition with a random embedding, any start**: if the random sketch
$\mathbf{S}$ is a subspace embedding of $\operatorname{range}\mathbf{A}$ with constants $a > 0$,
$b$ in squared norms ($a\|\mathbf{v}\|^2 \le \|\mathbf{S}\mathbf{v}\|^2 \le b\|\mathbf{v}\|^2$
for $\mathbf{v} \in \operatorname{range}\mathbf{A}$) except with probability $\delta$,
$\mathbf{A}$ has full column rank and $\mathbf{x}_\star$ is a least-squares solution of
$\mathbf{A}\mathbf{x} \approx \mathbf{y}$, then for a fixed start $\mathbf{x}_0$
$$\mathbb{P}\Bigl[4\Bigl(\frac{\sqrt{b/a} - 1}{\sqrt{b/a} + 1}\Bigr)^{2q}
\|\mathbf{A}(\mathbf{x}_\star - \mathbf{x}_0)\|^2 < \|\mathbf{A}(\mathbf{x}_\star -
\mathsf{sketchAndPrecondition}(\mathbf{A}, \mathbf{S}, \mathbf{y}, \mathbf{x}_0, q))\|^2\Bigr]
\le \delta\,.$$
No law is assumed: any distribution with the embedding property qualifies. -/
theorem HasSubspaceEmbedding.measureReal_norm_mulVec_sub_sketchAndPrecondition_sq_gt_le
    [IsFiniteMeasure μ] {S : Ω → Matrix k m 𝕜} (h : HasSubspaceEmbedding S A a b δ μ)
    (ha : 0 < a) (hA : Function.Injective A.mulVec) (hxs : IsLeastSquaresSolution A y xs)
    (x₀ : n → 𝕜) (q : ℕ) :
    μ.real {ω | 4 * ((√(b / a) - 1) / (√(b / a) + 1)) ^ (2 * q) *
        ‖WithLp.toLp 2 (A *ᵥ (xs - x₀))‖ ^ 2 <
      ‖WithLp.toLp 2 (A *ᵥ (xs - sketchAndPrecondition A (S ω) y x₀ q))‖ ^ 2} ≤ δ := by
  sorry

/-- **Sketch-and-precondition with a random embedding, sketch-and-solve start**: if the random
sketch $\mathbf{S}$ is a subspace embedding of $\operatorname{range}[\mathbf{A}\ \mathbf{y}]$ with
constants $a > 0$, $b$ in squared norms ($a\|\mathbf{v}\|^2 \le \|\mathbf{S}\mathbf{v}\|^2 \le
b\|\mathbf{v}\|^2$ on that range) except with probability $\delta$, $\mathbf{A}$ has full column
rank and almost surely $\mathbf{x}_0$ minimizes $\|\mathbf{S}(\mathbf{A}\mathbf{x} - \mathbf{y})\|$,
then
$$\mathbb{P}\Bigl[\Bigl(1 + 4\Bigl(\frac{b}{a} - 1\Bigr)
\Bigl(\frac{\sqrt{b/a} - 1}{\sqrt{b/a} + 1}\Bigr)^{2q}\Bigr)
\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{y}\|^2 < \|\mathbf{y} -
\mathbf{A}\,\mathsf{sketchAndPrecondition}(\mathbf{A}, \mathbf{S}, \mathbf{y}, \mathbf{x}_0,
q)\|^2\Bigr] \le \delta\,.$$
Squared residuals; [MartinssonTropp2020, §10.5] states an unsquared $1 + \varepsilon$. No law is
assumed: any distribution with the embedding property qualifies.
Result: sketch-and-precondition-ls -/
theorem HasSubspaceEmbedding.measureReal_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le
    [DecidableEq m] [IsFiniteMeasure μ] {S : Ω → Matrix k m 𝕜}
    (h : HasSubspaceEmbedding S (Matrix.fromCols A (Matrix.replicateCol Unit y)) a b δ μ)
    (ha : 0 < a) (hA : Function.Injective A.mulVec) {x₀ : Ω → n → 𝕜}
    (hx₀ : ∀ᵐ ω ∂μ, IsLeastSquaresSolution (S ω * A) (S ω *ᵥ y) (x₀ ω)) (q : ℕ) :
    μ.real {ω | (1 + 4 * (b / a - 1) * ((√(b / a) - 1) / (√(b / a) + 1)) ^ (2 * q)) *
        ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2 <
      ‖WithLp.toLp 2 (y - A *ᵥ sketchAndPrecondition A (S ω) y (x₀ ω) q)‖ ^ 2} ≤ δ := by
  sorry

end Random

end NLAlib
