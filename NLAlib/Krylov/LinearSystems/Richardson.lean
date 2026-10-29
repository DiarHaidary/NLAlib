/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.LinearSystems.PCG
public import NLAlib.Matrix.Spectral.PowerBounds

/-!
# Preconditioned Richardson iteration

`NLAlib.richardsonIterate A M b x₀ q` is the stationary iteration
$\mathbf{x}_{q+1} = \mathbf{x}_q + \mathbf{M}(\mathbf{b} - \mathbf{A}\mathbf{x}_q)$ for a
rectangular $\mathbf{A} \in \Bbbk^{m \times n}$ and an approximate inverse
$\mathbf{M} \in \Bbbk^{n \times m}$, a total recursion with no hypothesis. A step size $\omega$
is the preconditioner $\omega\mathbf{M}$. Square with $\mathbf{M} = \mathbf{I}$ it is Richardson's
method; with an approximate inverse, iterative refinement; with
$\mathbf{M} = \omega\mathbf{A}^{\mathsf{H}}$, Landweber's iteration; with
$\mathbf{M} = \mathbf{N}\mathbf{A}^{\mathsf{H}}$, Richardson on the normal equations
(`NLAlib.richardsonIterate_mul_conjTranspose`). Iterative sketching
(`NLAlib.iterativeSketching`) and the mean randomized Kaczmarz iterate are instances.

The error from a fixed point is the $q$-th power of $\mathbf{I} - \mathbf{M}\mathbf{A}$ applied to
the initial error, and the correction lies in the preconditioned Krylov space
$\mathcal{K}_q(\mathbf{M}\mathbf{A}, \mathbf{M}\mathbf{r}_0)$, so preconditioned CG with the same
$\mathbf{M}$ is never worse in the energy norm. For square positive definite $\mathbf{A}$ and
$\mathbf{M}$ the energy error contracts at the rate
$\max(\lvert 1 - a\rvert, \lvert 1 - a'\rvert)$ for the spectrum of $\mathbf{M}\mathbf{A}$ in
$[a, a']$, which the step $2/(a + a')$ makes $(a' - a)/(a' + a)$.

Design: `docs/design/Regression-SketchPrecondition.md` §3.1, §4.1.

## Main definitions

* `NLAlib.richardsonIterate`: the preconditioned Richardson iterate.

## Main results

* `NLAlib.sub_richardsonIterate_eq`: the error is $(\mathbf{I} - \mathbf{M}\mathbf{A})^q$ times
  the initial error.
* `NLAlib.forall_tendsto_richardsonIterate_iff_specRadius_lt_one`: the exact fixed-point
  convergence criterion.
* `NLAlib.forall_exists_mulVec_eq_and_tendsto_richardsonIterate_iff_specRadius_lt_one`:
  unique solvability and convergence for every right-hand side and starting vector.
* `NLAlib.richardsonIterate_sub_mem_krylovSpace`: the correction lies in the preconditioned
  Krylov space.
* `NLAlib.richardsonIterate_mul_conjTranspose`: Richardson through $\mathbf{A}^{\mathsf{H}}$ is
  Richardson on the normal equations.
* `Matrix.PosDef.re_quadForm_sub_richardsonIterate_le`: the rate in the spectrum of
  $\mathbf{M}\mathbf{A}$.
* `Matrix.PosDef.re_quadForm_sub_richardsonIterate_smul_le`: the optimal step.
* `Matrix.PosDef.re_quadForm_sub_pcgIterate_le_re_quadForm_sub_richardsonIterate`: PCG is never
  worse.
-/

@[expose] public section

open scoped Matrix ComplexOrder
open Filter Topology

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

/-- The **preconditioned Richardson iterate** for $\mathbf{A} \in \Bbbk^{m \times n}$ with an
approximate inverse $\mathbf{M} \in \Bbbk^{n \times m}$:
$\mathsf{richardsonIterate}(\mathbf{A}, \mathbf{M}, \mathbf{b}, \mathbf{x}_0, 0) := \mathbf{x}_0$
and $\mathsf{richardsonIterate}(\mathbf{A}, \mathbf{M}, \mathbf{b}, \mathbf{x}_0, q + 1) :=
\mathbf{x}_q + \mathbf{M}(\mathbf{b} - \mathbf{A}\mathbf{x}_q)$, with $\mathbf{x}_q$ the $q$-th
iterate. A step size $\omega$ is the preconditioner $\omega\mathbf{M}$. Square with
$\mathbf{M} = \mathbf{I}$ it is Richardson's method with unit step; with an approximate inverse,
iterative refinement; with $\mathbf{M} = \omega\mathbf{A}^{\mathsf{H}}$, Landweber's iteration;
with $\mathbf{M} = \mathbf{N}\mathbf{A}^{\mathsf{H}}$, Richardson on the normal equations
(`NLAlib.richardsonIterate_mul_conjTranspose`). Total, with no hypothesis on $\mathbf{A}$ or
$\mathbf{M}$. The argument order is that of `NLAlib.pcgIterate`. -/
noncomputable def richardsonIterate (A : Matrix m n 𝕜) (M : Matrix n m 𝕜) (b : m → 𝕜)
    (x₀ : n → 𝕜) : ℕ → n → 𝕜
  | 0 => x₀
  | q + 1 => richardsonIterate A M b x₀ q + M *ᵥ (b - A *ᵥ richardsonIterate A M b x₀ q)

/-- The zeroth Richardson iterate is the start:
$\mathsf{richardsonIterate}(\mathbf{A}, \mathbf{M}, \mathbf{b}, \mathbf{x}_0, 0) = \mathbf{x}_0$. -/
@[simp]
theorem richardsonIterate_zero (A : Matrix m n 𝕜) (M : Matrix n m 𝕜) (b : m → 𝕜) (x₀ : n → 𝕜) :
    richardsonIterate A M b x₀ 0 = x₀ :=
  rfl

/-- One Richardson step:
$\mathsf{richardsonIterate}(\mathbf{A}, \mathbf{M}, \mathbf{b}, \mathbf{x}_0, q + 1) =
\mathbf{x}_q + \mathbf{M}(\mathbf{b} - \mathbf{A}\mathbf{x}_q)$ with
$\mathbf{x}_q = \mathsf{richardsonIterate}(\mathbf{A}, \mathbf{M}, \mathbf{b}, \mathbf{x}_0, q)$. -/
theorem richardsonIterate_succ (A : Matrix m n 𝕜) (M : Matrix n m 𝕜) (b : m → 𝕜) (x₀ : n → 𝕜)
    (q : ℕ) :
    richardsonIterate A M b x₀ (q + 1) =
      richardsonIterate A M b x₀ q + M *ᵥ (b - A *ᵥ richardsonIterate A M b x₀ q) :=
  rfl

section DecidableEq

variable [DecidableEq n]

/-- The error of Richardson's iteration: for $\mathbf{A} \in \Bbbk^{m \times n}$,
$\mathbf{M} \in \Bbbk^{n \times m}$ and a fixed point $\mathbf{x}_\star$,
$\mathbf{M}(\mathbf{b} - \mathbf{A}\mathbf{x}_\star) = \mathbf{0}$, the Richardson iterate
$\mathbf{x}_q = \mathsf{richardsonIterate}(\mathbf{A}, \mathbf{M}, \mathbf{b}, \mathbf{x}_0, q)$
satisfies
$$\mathbf{x}_\star - \mathbf{x}_q = (\mathbf{I} - \mathbf{M}\mathbf{A})^q(\mathbf{x}_\star -
\mathbf{x}_0)\,.$$
The fixed-point hypothesis covers a solution of a consistent system,
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$, and, for
$\mathbf{M} = \mathbf{N}\mathbf{A}^{\mathsf{H}}$, a least-squares solution
(`NLAlib.isLeastSquaresSolution_iff_conjTranspose_mulVec_sub_eq_zero`). -/
theorem sub_richardsonIterate_eq {A : Matrix m n 𝕜} {M : Matrix n m 𝕜} {b : m → 𝕜}
    {xs : n → 𝕜} (hxs : M *ᵥ (b - A *ᵥ xs) = 0) (x₀ : n → 𝕜) (q : ℕ) :
    xs - richardsonIterate A M b x₀ q = ((1 - M * A) ^ q) *ᵥ (xs - x₀) := by
  induction q with
  | zero => rw [pow_zero, Matrix.one_mulVec, richardsonIterate_zero]
  | succ q ih =>
    have hr : b - A *ᵥ richardsonIterate A M b x₀ q =
        (b - A *ᵥ xs) + A *ᵥ (xs - richardsonIterate A M b x₀ q) := by
      rw [Matrix.mulVec_sub]; abel
    rw [richardsonIterate_succ, ← sub_sub, hr, Matrix.mulVec_add, hxs, zero_add,
      Matrix.mulVec_mulVec, ih, pow_succ', ← Matrix.mulVec_mulVec (M := 1 - M * A),
      Matrix.sub_mulVec, Matrix.one_mulVec]

/-- Richardson iteration converges to a fixed point $\mathbf{x}_\star$ from every start
$\mathbf{x}_0$ when $\rho(\mathbf{I}-\mathbf{M}\mathbf{A})<1$. The fixed-point condition is
$\mathbf{M}(\mathbf{b}-\mathbf{A}\mathbf{x}_\star)=\mathbf{0}$; the matrices may be rectangular.
The conclusion is $\mathsf{richardsonIterate}(\mathbf{A},\mathbf{M},\mathbf{b},\mathbf{x}_0,q)
\to\mathbf{x}_\star$. This is the fixed-point implication of the backend
`NLAlib.splittingConverges_iff_tendsto_pow_zero`, generalized to the Richardson interface. -/
theorem tendsto_richardsonIterate_of_specRadius_lt_one
    {A : Matrix m n 𝕜} {M : Matrix n m 𝕜} {b : m → 𝕜} {xs : n → 𝕜}
    (hxs : M *ᵥ (b - A *ᵥ xs) = 0) (hρ : specRadius (1 - M * A) < 1)
    (x₀ : n → 𝕜) :
    Tendsto (richardsonIterate A M b x₀) atTop (𝓝 xs) := by
  have hp := (tendsto_pow_zero_iff_specRadius_lt_one (1 - M * A)).mpr hρ
  have hc : Continuous (fun H : Matrix n n 𝕜 => H *ᵥ (xs - x₀)) :=
    continuous_id.matrix_mulVec continuous_const
  have he : Tendsto (fun q => xs - richardsonIterate A M b x₀ q) atTop (𝓝 0) := by
    simpa only [sub_richardsonIterate_eq hxs, Matrix.zero_mulVec, Function.comp_def] using
      (hc.tendsto (0 : Matrix n n 𝕜)).comp hp
  have hh : Tendsto (fun q => xs - (xs - richardsonIterate A M b x₀ q))
      atTop (𝓝 (xs - 0)) := tendsto_const_nhds.sub he
  simpa only [sub_zero, sub_sub_cancel] using hh

/-- The iterates
$\mathsf{richardsonIterate}(\mathbf{A},\mathbf{M},\mathbf{b},\mathbf{x}_0,q)$ converge to a
fixed point $\mathbf{x}_\star$ as $q\to\infty$ from every starting vector $\mathbf{x}_0$
if and only if $\rho(\mathbf{I}-\mathbf{M}\mathbf{A})<1$. The fixed-point condition is
$\mathbf{M}(\mathbf{b}-\mathbf{A}\mathbf{x}_\star)=\mathbf{0}$, and the matrices may be
rectangular. Convergence from one particular start alone does not imply this criterion.
The fixed-point form of the backend `NLAlib.splittingConverges_iff_spectralRadius_lt_one`. -/
theorem forall_tendsto_richardsonIterate_iff_specRadius_lt_one
    {A : Matrix m n 𝕜} {M : Matrix n m 𝕜} {b : m → 𝕜} {xs : n → 𝕜}
    (hxs : M *ᵥ (b - A *ᵥ xs) = 0) :
    (∀ x₀ : n → 𝕜, Tendsto (richardsonIterate A M b x₀) atTop (𝓝 xs)) ↔
      specRadius (1 - M * A) < 1 := by
  constructor
  · intro h
    apply (tendsto_pow_zero_iff_specRadius_lt_one (1 - M * A)).mp
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    have he : Tendsto (fun q => xs - richardsonIterate A M b (xs - Pi.single j 1) q)
        atTop (𝓝 (xs - xs)) := tendsto_const_nhds.sub (h (xs - Pi.single j 1))
    simp only [sub_self, sub_richardsonIterate_eq hxs, sub_sub_cancel,
      Matrix.mulVec_single_one] at he
    simpa only [Matrix.col, Function.comp_def, Matrix.transpose_apply, Matrix.zero_apply,
      Pi.zero_apply] using
      ((continuous_apply i).tendsto (0 : n → 𝕜)).comp he
  · intro hρ x₀
    exact tendsto_richardsonIterate_of_specRadius_lt_one hxs hρ x₀

/-- **The stationary iteration convergence criterion.** For square $\mathbf{A}$ and
$\mathbf{M}$, every right-hand side has a unique solution and
$\mathsf{richardsonIterate}(\mathbf{A},\mathbf{M},\mathbf{b},\mathbf{x}_0,q)$ converges to
that solution for every start if and only if $\rho(\mathbf{I}-\mathbf{M}\mathbf{A})<1$.
Neither matrix is assumed invertible; invertibility follows from the spectral condition.
No printed source. Port of `NLAlib.splittingConverges_iff_spectralRadius_lt_one` and
`NLAlib.splittingConverges_iff_complex_spectralRadius_lt_one`, using the existing Richardson
iteration: a splitting $\mathbf{S}-\mathbf{N}$ uses preconditioner $\mathbf{S}^{-1}$.
Result: richardson-iteration -/
theorem forall_exists_mulVec_eq_and_tendsto_richardsonIterate_iff_specRadius_lt_one
    (A M : Matrix n n 𝕜) :
    (∀ b : n → 𝕜, ∃ xs : n → 𝕜,
      A *ᵥ xs = b ∧
      (∀ ys : n → 𝕜, A *ᵥ ys = b → ys = xs) ∧
      ∀ x₀ : n → 𝕜, Tendsto (richardsonIterate A M b x₀) atTop (𝓝 xs)) ↔
      specRadius (1 - M * A) < 1 := by
  constructor
  · intro h
    obtain ⟨xs, _, huniq, hlim⟩ := h 0
    have hzero : xs = 0 := (huniq 0 (Matrix.mulVec_zero A)).symm
    subst xs
    exact (forall_tendsto_richardsonIterate_iff_specRadius_lt_one
      (A := A) (M := M) (b := 0) (xs := 0) (by simp only [Matrix.mulVec_zero, sub_self])).mp
      hlim
  · intro hρ b
    have hA : IsUnit A := isUnit_of_specRadius_one_sub_mul_lt_one hρ
    have hxs : A *ᵥ (A⁻¹ *ᵥ b) = b := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A
        ((Matrix.isUnit_iff_isUnit_det A).mp hA), Matrix.one_mulVec]
    refine ⟨A⁻¹ *ᵥ b, hxs, ?_, ?_⟩
    · intro ys hys
      exact Matrix.mulVec_injective_iff_isUnit.mpr hA (hys.trans hxs.symm)
    · intro x₀
      apply tendsto_richardsonIterate_of_specRadius_lt_one _ hρ x₀
      rw [hxs, sub_self, Matrix.mulVec_zero]

/-- The Richardson correction lies in the preconditioned Krylov space: for every
$\mathbf{A} \in \Bbbk^{m \times n}$ and $\mathbf{M} \in \Bbbk^{n \times m}$, the iterate
$\mathbf{x}_q = \mathsf{richardsonIterate}(\mathbf{A}, \mathbf{M}, \mathbf{b}, \mathbf{x}_0, q)$
satisfies $\mathbf{x}_q - \mathbf{x}_0 \in \mathcal{K}_q(\mathbf{M}\mathbf{A},
\mathbf{M}\mathbf{r}_0)$ with $\mathbf{r}_0 = \mathbf{b} - \mathbf{A}\mathbf{x}_0$, the space
that preconditioned CG searches (`NLAlib.pcgIterate_sub_mem_krylovSpace`). -/
theorem richardsonIterate_sub_mem_krylovSpace (A : Matrix m n 𝕜) (M : Matrix n m 𝕜)
    (b : m → 𝕜) (x₀ : n → 𝕜) (q : ℕ) :
    richardsonIterate A M b x₀ q - x₀ ∈ krylovSpace (M * A) (M *ᵥ (b - A *ᵥ x₀)) q := by
  induction q with
  | zero => rw [richardsonIterate_zero, sub_self]; exact Submodule.zero_mem _
  | succ q ih =>
    have hr : M *ᵥ (b - A *ᵥ richardsonIterate A M b x₀ q) = M *ᵥ (b - A *ᵥ x₀) -
        (M * A) *ᵥ (richardsonIterate A M b x₀ q - x₀) := by
      have h : b - A *ᵥ richardsonIterate A M b x₀ q =
          (b - A *ᵥ x₀) - A *ᵥ (richardsonIterate A M b x₀ q - x₀) := by
        rw [Matrix.mulVec_sub]; abel
      rw [h, Matrix.mulVec_sub, Matrix.mulVec_mulVec]
    rw [richardsonIterate_succ, add_sub_right_comm, hr]
    refine Submodule.add_mem _ (krylovSpace_mono _ _ (Nat.le_succ q) ih)
      (Submodule.sub_mem _ (self_mem_krylovSpace _ _ (Nat.succ_pos q))
        (mulVec_mem_krylovSpace_succ ih))

end DecidableEq

/-- Richardson through $\mathbf{A}^{\mathsf{H}}$ is Richardson on the normal equations: for
$\mathbf{A} \in \Bbbk^{m \times n}$ and $\mathbf{M} \in \Bbbk^{n \times n}$,
$$\mathsf{richardsonIterate}(\mathbf{A}, \mathbf{M}\mathbf{A}^{\mathsf{H}}, \mathbf{y},
\mathbf{x}_0, q) = \mathsf{richardsonIterate}(\mathbf{A}^{\mathsf{H}}\mathbf{A}, \mathbf{M},
\mathbf{A}^{\mathsf{H}}\mathbf{y}, \mathbf{x}_0, q)\,.$$
With $\mathbf{M} = \omega\mathbf{I}$ it identifies Landweber's iteration with Richardson on the
normal equations. -/
theorem richardsonIterate_mul_conjTranspose (A : Matrix m n 𝕜) (M : Matrix n n 𝕜) (y : m → 𝕜)
    (x₀ : n → 𝕜) (q : ℕ) :
    richardsonIterate A (M * Aᴴ) y x₀ q = richardsonIterate (Aᴴ * A) M (Aᴴ *ᵥ y) x₀ q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [richardsonIterate_succ, richardsonIterate_succ, ih, ← Matrix.mulVec_mulVec _ M Aᴴ,
      Matrix.mulVec_sub Aᴴ, Matrix.mulVec_mulVec _ Aᴴ A]

section Square

variable [DecidableEq n]

/-- **Preconditioned Richardson converges at the rate of the spectrum of $\mathbf{M}\mathbf{A}$**:
for positive definite $\mathbf{A}, \mathbf{M} \in \Bbbk^{n \times n}$ with the real spectrum of
$\mathbf{M}\mathbf{A}$ in $[a, a']$ and $\mathbf{A}\mathbf{x}_\star = \mathbf{b}$, the iterate
$\mathbf{x}_q = \mathsf{richardsonIterate}(\mathbf{A}, \mathbf{M}, \mathbf{b}, \mathbf{x}_0, q)$
satisfies
$$\|\mathbf{x}_\star - \mathbf{x}_q\|_{\mathbf{A}}^2 \le
\bigl(\max(\lvert 1 - a\rvert, \lvert 1 - a'\rvert)\bigr)^{2q}\,
\|\mathbf{x}_\star - \mathbf{x}_0\|_{\mathbf{A}}^2\,,$$
the squared $\mathbf{A}$-norm written
$\|\mathbf{z}\|_{\mathbf{A}}^2 = \operatorname{Re}(\mathbf{z}^{\mathsf{H}}\mathbf{A}\mathbf{z})$.
No printed source; the classical bound for the unpreconditioned stationary iteration, here with a
preconditioner and the energy norm.
Result: richardson-iteration -/
theorem _root_.Matrix.PosDef.re_quadForm_sub_richardsonIterate_le {A M : Matrix n n 𝕜}
    (hA : A.PosDef) (hM : M.PosDef) {a a' : ℝ} (hs : spectrum ℝ (M * A) ⊆ Set.Icc a a')
    {b xs : n → 𝕜} (hxs : A *ᵥ xs = b) (x₀ : n → 𝕜) (q : ℕ) :
    RCLike.re (quadForm A (xs - richardsonIterate A M b x₀ q)) ≤
      (max |1 - a| |1 - a'|) ^ (2 * q) * RCLike.re (quadForm A (xs - x₀)) := by
  have hfix : M *ᵥ (b - A *ᵥ xs) = 0 := by rw [hxs, sub_self, Matrix.mulVec_zero]
  obtain ⟨S, hS, hMS⟩ := hM.exists_isUnit_eq_mul_conjTranspose
  have hSu := (Matrix.isUnit_iff_isUnit_det S).mp hS
  have hB : (Sᴴ * A * S).PosDef := (Matrix.IsUnit.posDef_star_left_conjugate_iff hS).mpr hA
  have hspec : spectrum ℝ (Sᴴ * A * S) = spectrum ℝ (M * A) := by
    rw [hMS, spectrum_mul_conjTranspose_mul hS]
  have h1 : ∀ v, (1 - M * A) *ᵥ (S *ᵥ v) = S *ᵥ ((1 - Sᴴ * A * S) *ᵥ v) := fun v => by
    rw [hMS, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_sub]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hpow : ∀ j v, (1 - M * A) ^ j *ᵥ (S *ᵥ v) = S *ᵥ ((1 - Sᴴ * A * S) ^ j *ᵥ v) := by
    intro j
    induction j with
    | zero => intro v; simp only [pow_zero, Matrix.one_mulVec]
    | succ j ih =>
      intro v
      rw [pow_succ, pow_succ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1, ih]
  have hSv : S *ᵥ (S⁻¹ *ᵥ (xs - x₀)) = xs - x₀ := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv S hSu, Matrix.one_mulVec]
  have hp : ∀ x ∈ spectrum ℝ (Sᴴ * A * S),
      |((1 - Polynomial.X) ^ q : Polynomial ℝ).eval x| ≤ (max |1 - a| |1 - a'|) ^ q := by
    intro x hx
    obtain ⟨hxa, hxa'⟩ := hs (hspec ▸ hx)
    rw [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X,
      abs_pow, max_comm]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_le_max_abs_abs (by linarith) (by linarith)) q
  have h := hB.isHermitian.re_quadForm_aeval_aeval_mulVec_le subset_rfl Polynomial.X _
    (fun x hx => by rw [Polynomial.eval_X]; exact (hB.spectrum_subset_Ioi hx).le) hp
    (S⁻¹ *ᵥ (xs - x₀))
  simp only [Polynomial.aeval_X, map_pow, map_sub, map_one] at h
  rw [quadForm_conjTranspose_mul_mul, quadForm_conjTranspose_mul_mul] at h
  rwa [sub_richardsonIterate_eq hfix, ← hSv, hpow, mul_comm 2 q, pow_mul]

/-- Preconditioned Richardson with the optimal step: for positive definite
$\mathbf{A}, \mathbf{M} \in \Bbbk^{n \times n}$ with the real spectrum of $\mathbf{M}\mathbf{A}$ in
$[a, a']$, $0 < a \le a'$, and $\mathbf{A}\mathbf{x}_\star = \mathbf{b}$, the iterate
$\mathbf{x}_q = \mathsf{richardsonIterate}(\mathbf{A}, (2/(a + a'))\mathbf{M}, \mathbf{b},
\mathbf{x}_0, q)$ satisfies
$$\|\mathbf{x}_\star - \mathbf{x}_q\|_{\mathbf{A}}^2 \le
\Bigl(\frac{a' - a}{a' + a}\Bigr)^{2q}\|\mathbf{x}_\star - \mathbf{x}_0\|_{\mathbf{A}}^2\,,$$
the squared $\mathbf{A}$-norm written
$\|\mathbf{z}\|_{\mathbf{A}}^2 = \operatorname{Re}(\mathbf{z}^{\mathsf{H}}\mathbf{A}\mathbf{z})$.
The step $2/(a + a')$ minimises the rate
$\max(\lvert 1 - \omega a\rvert, \lvert 1 - \omega a'\rvert)$ over $\omega > 0$. -/
theorem _root_.Matrix.PosDef.re_quadForm_sub_richardsonIterate_smul_le {A M : Matrix n n 𝕜}
    (hA : A.PosDef) (hM : M.PosDef) {a a' : ℝ} (ha : 0 < a) (haa : a ≤ a')
    (hs : spectrum ℝ (M * A) ⊆ Set.Icc a a') {b xs : n → 𝕜} (hxs : A *ᵥ xs = b) (x₀ : n → 𝕜)
    (q : ℕ) :
    RCLike.re (quadForm A (xs - richardsonIterate A ((2 / (a + a')) • M) b x₀ q)) ≤
      ((a' - a) / (a' + a)) ^ (2 * q) * RCLike.re (quadForm A (xs - x₀)) := by
  have hc : 0 < 2 / (a + a') := div_pos two_pos (by linarith)
  have hs' : spectrum ℝ ((2 / (a + a')) • M * A) ⊆
      Set.Icc ((2 / (a + a')) * a) ((2 / (a + a')) * a') := by
    rw [smul_mul_assoc, ← Units.val_mk0 hc.ne', ← Units.smul_def,
      spectrum.unit_smul_eq_smul]
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨hya, hya'⟩ := hs hy
    simp only [Units.val_mk0, smul_eq_mul, Set.mem_Icc]
    exact ⟨mul_le_mul_of_nonneg_left hya hc.le, mul_le_mul_of_nonneg_left hya' hc.le⟩
  have hpos : 0 < a' + a := by linarith
  have hne : a + a' ≠ 0 := by linarith
  have hne' : a' + a ≠ 0 := hpos.ne'
  have h1 : 1 - 2 / (a + a') * a = (a' - a) / (a' + a) := by field_simp; ring
  have h2 : 1 - 2 / (a + a') * a' = -((a' - a) / (a' + a)) := by field_simp; ring
  have h := (hA.re_quadForm_sub_richardsonIterate_le (hM.smul hc) hs' hxs x₀ q)
  rwa [h1, h2, abs_neg, max_self, abs_of_nonneg (div_nonneg (by linarith) hpos.le)] at h

/-- Preconditioned CG is at least as good as Richardson with the same preconditioner: for
positive definite $\mathbf{A} \in \Bbbk^{n \times n}$, any $\mathbf{M} \in \Bbbk^{n \times n}$ and
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$,
$$\|\mathbf{x}_\star - \mathsf{pcgIterate}(\mathbf{A}, \mathbf{M}, \mathbf{b}, \mathbf{x}_0,
q)\|_{\mathbf{A}}^2 \le \|\mathbf{x}_\star - \mathsf{richardsonIterate}(\mathbf{A}, \mathbf{M},
\mathbf{b}, \mathbf{x}_0, q)\|_{\mathbf{A}}^2\,,$$
the squared $\mathbf{A}$-norm written
$\|\mathbf{z}\|_{\mathbf{A}}^2 = \operatorname{Re}(\mathbf{z}^{\mathsf{H}}\mathbf{A}\mathbf{z})$:
both iterates lie in $\mathbf{x}_0 + \mathcal{K}_q(\mathbf{M}\mathbf{A}, \mathbf{M}\mathbf{r}_0)$,
over which PCG minimises the energy error (`Matrix.PosDef.isMinOn_pcgIterate`). -/
theorem _root_.Matrix.PosDef.re_quadForm_sub_pcgIterate_le_re_quadForm_sub_richardsonIterate
    {A : Matrix n n 𝕜} (hA : A.PosDef) (M : Matrix n n 𝕜) {b xs : n → 𝕜} (hxs : A *ᵥ xs = b)
    (x₀ : n → 𝕜) (q : ℕ) :
    RCLike.re (quadForm A (xs - pcgIterate A M b x₀ q)) ≤
      RCLike.re (quadForm A (xs - richardsonIterate A M b x₀ q)) := by
  have hmem : richardsonIterate A M b x₀ q ∈
      (AffineSubspace.mk' x₀ (krylovSpace (M * A) (M *ᵥ (b - A *ᵥ x₀)) q) : Set (n → 𝕜)) := by
    rw [SetLike.mem_coe, AffineSubspace.mem_mk', vsub_eq_sub]
    exact richardsonIterate_sub_mem_krylovSpace A M b x₀ q
  exact isMinOn_iff.mp (hA.isMinOn_pcgIterate M hxs x₀ q) _ hmem

end Square

end NLAlib
