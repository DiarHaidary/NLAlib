/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.LinearSystems.Richardson
public import NLAlib.Regression.Embedding
public import NLAlib.Sketching.Properties.FixedSubspace

/-!
# Iterative sketching

`NLAlib.iterativeSketching A S ω y x₀ q` is iterative refinement on the normal equations of the
least-squares problem $\min_{\mathbf{x}}\|\mathbf{y} - \mathbf{A}\mathbf{x}\|$, preconditioned by
the sketched Gram matrix $\mathbf{G} = (\mathbf{S}\mathbf{A})^{\mathsf{H}}\mathbf{S}\mathbf{A}$
with step $\omega$:
$\mathbf{x}_{i+1} = \mathbf{x}_i + \omega\mathbf{G}^{+}\mathbf{A}^{\mathsf{H}}(\mathbf{y} -
\mathbf{A}\mathbf{x}_i)$, one sketch for all steps. It is the rectangular Richardson iterate
`NLAlib.richardsonIterate` with $\mathbf{M} = \omega\mathbf{G}^{+}\mathbf{A}^{\mathsf{H}}$, and
Richardson on the normal equations with $\omega\mathbf{G}^{+}$ (`NLAlib.iterativeSketching_eq`).
Step $\omega = 1$ is Epperly's iterative sketching; $\omega = 1 - \varepsilon^2$ is the optimal
damping for an embedding with constants $1 \mp \varepsilon$ in squared norms.

If $\mathbf{S}$ embeds $\operatorname{range}\mathbf{A}$ with constants $a, b$ in squared norms, the
energy error contracts at the rate $\max(\lvert 1 - \omega/b\rvert, \lvert 1 - \omega/a\rvert)$
per step, with no prefactor. Sketch-and-precondition (`NLAlib.sketchAndPrecondition`),
preconditioned CG with the same preconditioner, is never worse
(`Matrix.PosDef.re_quadForm_sub_pcgIterate_le_re_quadForm_sub_richardsonIterate`).
[Epperly2024]; [MartinssonTropp2020].
Design: `docs/design/Regression-SketchPrecondition.md`.

## Main definitions

* `NLAlib.iterativeSketching`: the iterative sketching iterate with step $\omega$.

## Main results

* `NLAlib.iterativeSketching_eq`: Richardson on the normal equations.
* `NLAlib.IsQR.iterativeSketching_succ`, `NLAlib.IsSVD.iterativeSketching_succ`: the step through
  a factorization of the sketch.
* `NLAlib.IsSubspaceEmbedding.norm_mulVec_sub_iterativeSketching_sq_le`: geometric convergence of
  the energy error for every step.
* `NLAlib.IsSubspaceEmbedding.norm_mulVec_sub_iterativeSketching_one_sq_le`,
  `NLAlib.IsSubspaceEmbedding.norm_mulVec_sub_iterativeSketching_one_sub_sq_sq_le`: undamped and
  optimally damped.
* `NLAlib.IsSubspaceEmbedding.norm_sub_mulVec_iterativeSketching_one_sub_sq_sq_le`: the residual
  from the sketch-and-solve start.
* `NLAlib.HasSubspaceEmbedding.measureReal_norm_mulVec_sub_iterativeSketching_sq_gt_le`,
  `NLAlib.HasSubspaceEmbedding.measureReal_norm_sub_mulVec_iterativeSketching_one_sub_sq_sq_gt_le`:
  the same with a random embedding.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {k m n : Type*} [Fintype k] [Fintype m] [Fintype n]

/-- The **iterative sketching iterate** with step $\omega$, for
$\mathbf{A} \in \Bbbk^{m \times n}$, a sketch $\mathbf{S} \in \Bbbk^{k \times m}$ and
$\mathbf{y} \in \Bbbk^m$:
$$\mathsf{iterativeSketching}(\mathbf{A}, \mathbf{S}, \omega, \mathbf{y}, \mathbf{x}_0, q) :=
\mathsf{richardsonIterate}(\mathbf{A}, \omega\mathbf{G}^{+}\mathbf{A}^{\mathsf{H}}, \mathbf{y},
\mathbf{x}_0, q)$$
with $\mathbf{G} = (\mathbf{S}\mathbf{A})^{\mathsf{H}}\mathbf{S}\mathbf{A}$, that is
$\mathbf{x}_{i+1} = \mathbf{x}_i + \omega\mathbf{G}^{+}\mathbf{A}^{\mathsf{H}}(\mathbf{y} -
\mathbf{A}\mathbf{x}_i)$. One sketch, fixed for all steps. $\omega = 1$ is Epperly's iterative
sketching; his damped variant is $\omega = (1 - \eta^2)^2/(1 + \eta^2)$ in the unsquared distortion
$\eta$, which is $1 - \varepsilon^2$ for an embedding with constants $1 \mp \varepsilon$ in squared
norms. [Epperly2024, (3.2)], there with $\omega = 1$; [Epperly2024, (B.2)], the damping;
[MartinssonTropp2020, §10.4], there with a fresh sketch at every step. -/
noncomputable def iterativeSketching (A : Matrix m n 𝕜) (S : Matrix k m 𝕜) (ω : ℝ) (y : m → 𝕜)
    (x₀ : n → 𝕜) (q : ℕ) : n → 𝕜 :=
  richardsonIterate A (ω • (pinv ((S * A)ᴴ * (S * A)) * Aᴴ)) y x₀ q

/-- **Iterative sketching is Richardson on the normal equations** with $\omega\mathbf{G}^{+}$,
$\mathbf{G} = (\mathbf{S}\mathbf{A})^{\mathsf{H}}\mathbf{S}\mathbf{A}$:
$$\mathsf{iterativeSketching}(\mathbf{A}, \mathbf{S}, \omega, \mathbf{y}, \mathbf{x}_0, q) =
\mathsf{richardsonIterate}(\mathbf{A}^{\mathsf{H}}\mathbf{A}, \omega\mathbf{G}^{+},
\mathbf{A}^{\mathsf{H}}\mathbf{y}, \mathbf{x}_0, q)\,.$$
[Epperly2024, (3.2)], there as iterative refinement on the normal equations. -/
theorem iterativeSketching_eq (A : Matrix m n 𝕜) (S : Matrix k m 𝕜) (ω : ℝ) (y : m → 𝕜)
    (x₀ : n → 𝕜) (q : ℕ) :
    iterativeSketching A S ω y x₀ q =
      richardsonIterate (Aᴴ * A) (ω • pinv ((S * A)ᴴ * (S * A))) (Aᴴ *ᵥ y) x₀ q := by
  sorry

variable {S : Matrix k m 𝕜} {A : Matrix m n 𝕜} {y : m → 𝕜} {xs x₀ : n → 𝕜}
  {a b ε : ℝ}

/-- **The iterative sketching step through QR**: for a thin QR factorization
$\mathbf{S}\mathbf{A} = \mathbf{Q}\mathbf{R}$ with $\mathbf{R}$ invertible, the iterates
$\mathbf{x}_q = \mathsf{iterativeSketching}(\mathbf{A}, \mathbf{S}, \omega, \mathbf{y},
\mathbf{x}_0, q)$ satisfy
$$\mathbf{x}_{q+1} = \mathbf{x}_q + \omega\mathbf{R}^{-1}\mathbf{R}^{-\mathsf{H}}
\mathbf{A}^{\mathsf{H}}(\mathbf{y} - \mathbf{A}\mathbf{x}_q)\,,$$
two triangular solves per step. [Epperly2024, Algorithm 2], there with $\omega = 1$. -/
theorem IsQR.iterativeSketching_succ [DecidableEq n] [LinearOrder n] {Q : Matrix k n 𝕜}
    {R : Matrix n n 𝕜} (hQR : IsQR (S * A) Q R) (hR : IsUnit R) (ω : ℝ) (y : m → 𝕜)
    (x₀ : n → 𝕜) (q : ℕ) :
    iterativeSketching A S ω y x₀ (q + 1) = iterativeSketching A S ω y x₀ q +
      ω • (R⁻¹ *ᵥ ((R⁻¹)ᴴ *ᵥ (Aᴴ *ᵥ (y - A *ᵥ iterativeSketching A S ω y x₀ q)))) := by
  sorry

/-- **The iterative sketching step through an SVD**: for a singular value decomposition
$\mathbf{S}\mathbf{A} = \mathbf{U}\mathbf{\Sigma}\mathbf{V}^{\mathsf{H}}$ with square $\mathbf{V}$
and every $\sigma_i > 0$, the iterates
$\mathbf{x}_q = \mathsf{iterativeSketching}(\mathbf{A}, \mathbf{S}, \omega, \mathbf{y},
\mathbf{x}_0, q)$ satisfy
$$\mathbf{x}_{q+1} = \mathbf{x}_q + \omega\mathbf{V}\mathbf{\Sigma}^{-2}\mathbf{V}^{\mathsf{H}}
\mathbf{A}^{\mathsf{H}}(\mathbf{y} - \mathbf{A}\mathbf{x}_q)\,.$$
[EpperlyMeierNakatsukasa2024, §2.1], there the change of variables for any orthogonal
factorization. -/
theorem IsSVD.iterativeSketching_succ [DecidableEq n] {U : Matrix k n 𝕜} {σ : n → ℝ}
    {V : Matrix n n 𝕜} (hSVD : IsSVD (S * A) U σ V) (hσ : ∀ i, 0 < σ i) (ω : ℝ) (y : m → 𝕜)
    (x₀ : n → 𝕜) (q : ℕ) :
    iterativeSketching A S ω y x₀ (q + 1) = iterativeSketching A S ω y x₀ q +
      ω • ((V * Matrix.diagonal (fun i => (((σ i) ^ 2)⁻¹ : 𝕜)) * Vᴴ) *ᵥ
        (Aᴴ *ᵥ (y - A *ᵥ iterativeSketching A S ω y x₀ q))) := by
  sorry

/-! ### Deterministic convergence -/

/-- **Iterative sketching converges geometrically**: if $\mathbf{S}$ is a subspace embedding of
$\operatorname{range}\mathbf{A}$ with constants $a > 0$, $b$ in squared norms
($a\|\mathbf{v}\|^2 \le \|\mathbf{S}\mathbf{v}\|^2 \le b\|\mathbf{v}\|^2$ for
$\mathbf{v} \in \operatorname{range}\mathbf{A}$), $\mathbf{A}$ has full column rank,
$\mathbf{x}_\star$ is a least-squares solution of $\mathbf{A}\mathbf{x} \approx \mathbf{y}$ and
$\omega > 0$, then for every start $\mathbf{x}_0$
$$\|\mathbf{A}(\mathbf{x}_\star - \mathsf{iterativeSketching}(\mathbf{A}, \mathbf{S}, \omega,
\mathbf{y}, \mathbf{x}_0, q))\|^2 \le \bigl(\max(\lvert 1 - \omega/b\rvert,
\lvert 1 - \omega/a\rvert)\bigr)^{2q}\|\mathbf{A}(\mathbf{x}_\star - \mathbf{x}_0)\|^2\,.$$
In Epperly's unsquared distortion $\eta$ ($a = (1 - \eta)^2$, $b = (1 + \eta)^2$) the rate at
$\omega = 1$ is his $g_{\mathrm{IS}} = (2 - \eta)\eta/(1 - \eta)^2$, and at
$\omega = (1 - \eta^2)^2/(1 + \eta^2)$ it is $g_{\mathrm{damp}} = 2\eta/(1 + \eta^2)$.
[Epperly2024, Theorem 5 and Theorem 10]; there through $\|\mathbf{S}\mathbf{A}\cdot\|$ with the
prefactor $(1 + \eta)/(1 - \eta)$, here in the energy norm without one.
Result: iterative-sketching-convergence -/
theorem IsSubspaceEmbedding.norm_mulVec_sub_iterativeSketching_sq_le
    (h : IsSubspaceEmbedding S A a b) (ha : 0 < a) (hA : Function.Injective A.mulVec)
    {ω : ℝ} (hω : 0 < ω) (hxs : IsLeastSquaresSolution A y xs) (x₀ : n → 𝕜) (q : ℕ) :
    ‖WithLp.toLp 2 (A *ᵥ (xs - iterativeSketching A S ω y x₀ q))‖ ^ 2 ≤
      (max |1 - ω / b| |1 - ω / a|) ^ (2 * q) * ‖WithLp.toLp 2 (A *ᵥ (xs - x₀))‖ ^ 2 := by
  sorry

/-- **Undamped iterative sketching, $\varepsilon$ form**: if $\mathbf{S}$ is a subspace embedding
of $\operatorname{range}\mathbf{A}$ with constants $1 \mp \varepsilon$ in squared norms
($(1 - \varepsilon)\|\mathbf{v}\|^2 \le \|\mathbf{S}\mathbf{v}\|^2 \le
(1 + \varepsilon)\|\mathbf{v}\|^2$ for $\mathbf{v} \in \operatorname{range}\mathbf{A}$),
$0 < \varepsilon < 1$, $\mathbf{A}$ has full column rank and $\mathbf{x}_\star$ is a
least-squares solution of $\mathbf{A}\mathbf{x} \approx \mathbf{y}$, then for every start
$$\|\mathbf{A}(\mathbf{x}_\star - \mathsf{iterativeSketching}(\mathbf{A}, \mathbf{S}, 1,
\mathbf{y}, \mathbf{x}_0, q))\|^2 \le \Bigl(\frac{\varepsilon}{1 - \varepsilon}\Bigr)^{2q}
\|\mathbf{A}(\mathbf{x}_\star - \mathbf{x}_0)\|^2\,,$$
a contraction for $\varepsilon < 1/2$. [Epperly2024, Theorem 5], there in the unsquared
convention with a prefactor. -/
theorem IsSubspaceEmbedding.norm_mulVec_sub_iterativeSketching_one_sq_le
    (h : IsSubspaceEmbedding S A (1 - ε) (1 + ε)) (hε : 0 < ε) (hε1 : ε < 1)
    (hA : Function.Injective A.mulVec) (hxs : IsLeastSquaresSolution A y xs) (x₀ : n → 𝕜)
    (q : ℕ) :
    ‖WithLp.toLp 2 (A *ᵥ (xs - iterativeSketching A S 1 y x₀ q))‖ ^ 2 ≤
      (ε / (1 - ε)) ^ (2 * q) * ‖WithLp.toLp 2 (A *ᵥ (xs - x₀))‖ ^ 2 := by
  sorry

/-- **Optimally damped iterative sketching, $\varepsilon$ form**: if $\mathbf{S}$ is a subspace
embedding of $\operatorname{range}\mathbf{A}$ with constants $1 \mp \varepsilon$ in squared norms
($(1 - \varepsilon)\|\mathbf{v}\|^2 \le \|\mathbf{S}\mathbf{v}\|^2 \le
(1 + \varepsilon)\|\mathbf{v}\|^2$ for $\mathbf{v} \in \operatorname{range}\mathbf{A}$),
$0 < \varepsilon < 1$, $\mathbf{A}$ has full column rank and $\mathbf{x}_\star$ is a
least-squares solution of $\mathbf{A}\mathbf{x} \approx \mathbf{y}$, then with step
$\omega = 1 - \varepsilon^2$, for every start
$$\|\mathbf{A}(\mathbf{x}_\star - \mathsf{iterativeSketching}(\mathbf{A}, \mathbf{S},
1 - \varepsilon^2, \mathbf{y}, \mathbf{x}_0, q))\|^2 \le \varepsilon^{2q}
\|\mathbf{A}(\mathbf{x}_\star - \mathbf{x}_0)\|^2\,,$$
a contraction for every $\varepsilon < 1$. Sketch-and-precondition is never worse
(`Matrix.PosDef.re_quadForm_sub_pcgIterate_le_re_quadForm_sub_richardsonIterate`).
[Epperly2024, Theorem 10], there in the unsquared convention with a prefactor. -/
theorem IsSubspaceEmbedding.norm_mulVec_sub_iterativeSketching_one_sub_sq_sq_le
    (h : IsSubspaceEmbedding S A (1 - ε) (1 + ε)) (hε : 0 < ε) (hε1 : ε < 1)
    (hA : Function.Injective A.mulVec) (hxs : IsLeastSquaresSolution A y xs) (x₀ : n → 𝕜)
    (q : ℕ) :
    ‖WithLp.toLp 2 (A *ᵥ (xs - iterativeSketching A S (1 - ε ^ 2) y x₀ q))‖ ^ 2 ≤
      ε ^ (2 * q) * ‖WithLp.toLp 2 (A *ᵥ (xs - x₀))‖ ^ 2 := by
  sorry

/-- **Damped iterative sketching from the sketch-and-solve start**: if $\mathbf{S}$ is a subspace
embedding of $\operatorname{range}[\mathbf{A}\ \mathbf{y}]$ with constants $1 \mp \varepsilon$ in
squared norms ($(1 - \varepsilon)\|\mathbf{v}\|^2 \le \|\mathbf{S}\mathbf{v}\|^2 \le
(1 + \varepsilon)\|\mathbf{v}\|^2$ on that range), $0 < \varepsilon < 1$, $\mathbf{A}$ has full
column rank and $\mathbf{x}_0$ minimizes $\|\mathbf{S}(\mathbf{A}\mathbf{x} - \mathbf{y})\|$, then
$$\|\mathbf{y} - \mathbf{A}\,\mathsf{iterativeSketching}(\mathbf{A}, \mathbf{S},
1 - \varepsilon^2, \mathbf{y}, \mathbf{x}_0, q)\|^2 \le
\Bigl(1 + \frac{2\varepsilon^{2q+1}}{1 - \varepsilon}\Bigr)
\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{y}\|^2\,,$$
the last factor being the optimal squared residual. [Epperly2024, Theorem 10, (B.4)], there
unsquared with a prefactor. -/
theorem IsSubspaceEmbedding.norm_sub_mulVec_iterativeSketching_one_sub_sq_sq_le [DecidableEq m]
    (h : IsSubspaceEmbedding S (Matrix.fromCols A (Matrix.replicateCol Unit y)) (1 - ε) (1 + ε))
    (hε : 0 < ε) (hε1 : ε < 1) (hA : Function.Injective A.mulVec)
    (hx₀ : IsLeastSquaresSolution (S * A) (S *ᵥ y) x₀) (q : ℕ) :
    ‖WithLp.toLp 2 (y - A *ᵥ iterativeSketching A S (1 - ε ^ 2) y x₀ q)‖ ^ 2 ≤
      (1 + 2 * ε ^ (2 * q + 1) / (1 - ε)) *
        ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2 := by
  sorry

/-! ### With a random embedding -/

section Random

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {δ : ℝ}

/-- **Iterative sketching with a random embedding, any start**: if the random sketch $\mathbf{S}$
is a subspace embedding of $\operatorname{range}\mathbf{A}$ with constants $a > 0$, $b$ in squared
norms ($a\|\mathbf{v}\|^2 \le \|\mathbf{S}\mathbf{v}\|^2 \le b\|\mathbf{v}\|^2$ for
$\mathbf{v} \in \operatorname{range}\mathbf{A}$) except with probability $\delta$, $\mathbf{A}$ has
full column rank, $\mathbf{x}_\star$ is a least-squares solution of
$\mathbf{A}\mathbf{x} \approx \mathbf{y}$ and the step is $\omega' > 0$, then for a fixed start
$\mathbf{x}_0$
$$\mathbb{P}\Bigl[\bigl(\max(\lvert 1 - \omega'/b\rvert, \lvert 1 - \omega'/a\rvert)\bigr)^{2q}
\|\mathbf{A}(\mathbf{x}_\star - \mathbf{x}_0)\|^2 < \|\mathbf{A}(\mathbf{x}_\star -
\mathsf{iterativeSketching}(\mathbf{A}, \mathbf{S}, \omega', \mathbf{y}, \mathbf{x}_0,
q))\|^2\Bigr] \le \delta\,.$$
No law is assumed: any distribution with the embedding property qualifies. -/
theorem HasSubspaceEmbedding.measureReal_norm_mulVec_sub_iterativeSketching_sq_gt_le
    [IsFiniteMeasure μ] {S : Ω → Matrix k m 𝕜} (h : HasSubspaceEmbedding S A a b δ μ)
    (ha : 0 < a) (hA : Function.Injective A.mulVec) {ω' : ℝ} (hω : 0 < ω')
    (hxs : IsLeastSquaresSolution A y xs) (x₀ : n → 𝕜) (q : ℕ) :
    μ.real {ω | (max |1 - ω' / b| |1 - ω' / a|) ^ (2 * q) *
        ‖WithLp.toLp 2 (A *ᵥ (xs - x₀))‖ ^ 2 <
      ‖WithLp.toLp 2 (A *ᵥ (xs - iterativeSketching A (S ω) ω' y x₀ q))‖ ^ 2} ≤ δ := by
  sorry

/-- **Damped iterative sketching with a random embedding, sketch-and-solve start**: if the random
sketch $\mathbf{S}$ is a subspace embedding of $\operatorname{range}[\mathbf{A}\ \mathbf{y}]$ with
constants $1 \mp \varepsilon$ in squared norms ($(1 - \varepsilon)\|\mathbf{v}\|^2 \le
\|\mathbf{S}\mathbf{v}\|^2 \le (1 + \varepsilon)\|\mathbf{v}\|^2$ on that range),
$0 < \varepsilon < 1$, except with probability $\delta$, $\mathbf{A}$ has full column rank and
almost surely $\mathbf{x}_0$ minimizes $\|\mathbf{S}(\mathbf{A}\mathbf{x} - \mathbf{y})\|$, then
$$\mathbb{P}\Bigl[\Bigl(1 + \frac{2\varepsilon^{2q+1}}{1 - \varepsilon}\Bigr)
\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{y}\|^2 < \|\mathbf{y} -
\mathbf{A}\,\mathsf{iterativeSketching}(\mathbf{A}, \mathbf{S}, 1 - \varepsilon^2, \mathbf{y},
\mathbf{x}_0, q)\|^2\Bigr] \le \delta\,.$$
No law is assumed: any distribution with the embedding property qualifies. -/
theorem HasSubspaceEmbedding.measureReal_norm_sub_mulVec_iterativeSketching_one_sub_sq_sq_gt_le
    [DecidableEq m] [IsFiniteMeasure μ] {S : Ω → Matrix k m 𝕜}
    (h : HasSubspaceEmbedding S (Matrix.fromCols A (Matrix.replicateCol Unit y))
      (1 - ε) (1 + ε) δ μ)
    (hε : 0 < ε) (hε1 : ε < 1) (hA : Function.Injective A.mulVec) {x₀ : Ω → n → 𝕜}
    (hx₀ : ∀ᵐ ω ∂μ, IsLeastSquaresSolution (S ω * A) (S ω *ᵥ y) (x₀ ω)) (q : ℕ) :
    μ.real {ω | (1 + 2 * ε ^ (2 * q + 1) / (1 - ε)) *
        ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2 <
      ‖WithLp.toLp 2 (y - A *ᵥ iterativeSketching A (S ω) (1 - ε ^ 2) y (x₀ ω) q)‖ ^ 2} ≤ δ := by
  sorry

end Random

end NLAlib
