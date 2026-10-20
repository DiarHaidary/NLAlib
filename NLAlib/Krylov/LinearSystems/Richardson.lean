/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.LinearSystems.PCG

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

/-- **The error of Richardson's iteration**: for $\mathbf{A} \in \Bbbk^{m \times n}$,
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
  sorry

/-- **The Richardson correction lies in the preconditioned Krylov space**: for every
$\mathbf{A} \in \Bbbk^{m \times n}$ and $\mathbf{M} \in \Bbbk^{n \times m}$, the iterate
$\mathbf{x}_q = \mathsf{richardsonIterate}(\mathbf{A}, \mathbf{M}, \mathbf{b}, \mathbf{x}_0, q)$
satisfies $\mathbf{x}_q - \mathbf{x}_0 \in \mathcal{K}_q(\mathbf{M}\mathbf{A},
\mathbf{M}\mathbf{r}_0)$ with $\mathbf{r}_0 = \mathbf{b} - \mathbf{A}\mathbf{x}_0$, the space
that preconditioned CG searches (`NLAlib.pcgIterate_sub_mem_krylovSpace`). -/
theorem richardsonIterate_sub_mem_krylovSpace (A : Matrix m n 𝕜) (M : Matrix n m 𝕜)
    (b : m → 𝕜) (x₀ : n → 𝕜) (q : ℕ) :
    richardsonIterate A M b x₀ q - x₀ ∈ krylovSpace (M * A) (M *ᵥ (b - A *ᵥ x₀)) q := by
  sorry

end DecidableEq

/-- **Richardson through $\mathbf{A}^{\mathsf{H}}$ is Richardson on the normal equations**: for
$\mathbf{A} \in \Bbbk^{m \times n}$ and $\mathbf{M} \in \Bbbk^{n \times n}$,
$$\mathsf{richardsonIterate}(\mathbf{A}, \mathbf{M}\mathbf{A}^{\mathsf{H}}, \mathbf{y},
\mathbf{x}_0, q) = \mathsf{richardsonIterate}(\mathbf{A}^{\mathsf{H}}\mathbf{A}, \mathbf{M},
\mathbf{A}^{\mathsf{H}}\mathbf{y}, \mathbf{x}_0, q)\,.$$
With $\mathbf{M} = \omega\mathbf{I}$ it identifies Landweber's iteration with Richardson on the
normal equations. -/
theorem richardsonIterate_mul_conjTranspose (A : Matrix m n 𝕜) (M : Matrix n n 𝕜) (y : m → 𝕜)
    (x₀ : n → 𝕜) (q : ℕ) :
    richardsonIterate A (M * Aᴴ) y x₀ q = richardsonIterate (Aᴴ * A) M (Aᴴ *ᵥ y) x₀ q := by
  sorry

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
  sorry

/-- **Preconditioned Richardson with the optimal step**: for positive definite
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
  sorry

/-- **Preconditioned CG is at least as good as Richardson** with the same preconditioner: for
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
  sorry

end Square

end NLAlib
