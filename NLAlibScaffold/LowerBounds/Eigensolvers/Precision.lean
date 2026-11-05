/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Structured.Walsh
public import NLAlib.Matrix.Norms.Spectral
public import NLAlib.ForMathlib.Algebra.Order.Round
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# A lower bound on the precision of Hermitian diagonalization (scaffold)

Statements for a new file `NLAlib/LowerBounds/Eigensolvers/Precision.lean` (stage HDIAG, design
note `docs/design/Eigensolvers-HermitianDiagonalization.md` §3.10, open question OQ5). A method
that sees its input only after rounding cannot distinguish a $\pm1$ matrix $\mathbf{H}$ from
$\mathbf{H} \pm \delta\mathbf{J}$ ($\mathbf{J}$ the all-ones matrix) when the rounding absorbs
$\delta$; one of the two has residual at least $\delta n$ against any diagonalization, so a
backward error $\varepsilon\|\mathbf{A}\|_2$ forces $\delta n \le \varepsilon(\|\mathbf{H}\|_2 +
\delta n)$. For a Walsh–Hadamard $\mathbf{H}$ ($\|\mathbf{H}\|_2 = \sqrt n$) and rounding to
nearest with $t$ bits, $t \ge \log_2(1/\varepsilon) + \tfrac12\log_2 n - 2 + \log_2(1 -
\varepsilon)$ ([Shah2024, Proposition 1.1]).

## Main results

* `NLAlib.exists_mul_card_le_specNorm_add_smul`: one sign of $\pm\delta\mathbf{J}$ is far from any
  matrix.
* `NLAlib.mul_card_le_of_forall_specNorm_sub_le`: the abstract lower bound.
* `NLAlib.logb_inv_add_le_of_forall_specNorm_sub_le`: Proposition 1.1.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n]

/-- **One of $\mathbf{M} \pm \delta\mathbf{J}$ has norm at least $\delta n$**: for every square
complex $\mathbf{M}$ and $\delta \ge 0$, with $\mathbf{J}$ the all-ones matrix, there is a sign
$s \in \{1, -1\}$ with $\delta\lvert n \rvert \le \|\mathbf{M} + s\delta\mathbf{J}\|_2$. No
printed source; [Shah2024, proof of Proposition 1.1] argues with the signs of the entries, which
bounds the Frobenius norm only.
Proof: for $n$ nonempty, the unit vector $\mathbf{x} = \lvert n \rvert^{-1/2}\mathbf{1}$ gives
$\mathbf{x}^{\mathsf{H}}(\mathbf{M} + s\delta\mathbf{J})\mathbf{x} =
\mathbf{x}^{\mathsf{H}}\mathbf{M}\mathbf{x} + s\delta\lvert n \rvert$; choose $s$ with the sign of
$\operatorname{Re}\mathbf{x}^{\mathsf{H}}\mathbf{M}\mathbf{x}$ (or $1$), so the real part has
modulus at least $\delta\lvert n \rvert$; a quadratic form is at most the norm
(Cauchy–Schwarz with `NLAlib.norm_toLp_mulVec_le`). Empty $n$ is trivial. S, about 30 lines. -/
theorem exists_mul_card_le_specNorm_add_smul (M : Matrix n n ℂ) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∃ s ∈ ({1, -1} : Set ℝ),
      δ * Fintype.card n ≤ specNorm (M + (s * δ) • Matrix.of fun _ _ : n => (1 : ℂ)) := by
  sorry

/-- **A lower bound for diagonalization from rounded input**: let $\mathrm{fl}$ be a rounding of
reals and $\mathcal{A}$ any method that maps the rounded input $\mathrm{fl}(\mathbf{A})$
(entrywise) of a real symmetric $\mathbf{A}$ to $(\mathbf{U}, \mathbf{d})$, with
$\|\mathbf{A} - \mathbf{U}\operatorname{diag}(\mathbf{d})\mathbf{U}^{\mathsf{H}}\|_2 \le
\varepsilon\|\mathbf{A}\|_2$ for every real symmetric $\mathbf{A}$. If $\mathbf{H}$ is real
symmetric and $\delta \ge 0$ with $\mathrm{fl}(\mathbf{H}_{i,j} \pm \delta) =
\mathrm{fl}(\mathbf{H}_{i,j})$ for all entries and both signs, then
$$\delta\lvert n \rvert \le \varepsilon\bigl(\|\mathbf{H}\|_2 + \delta\lvert n \rvert\bigr) \,.$$
[Shah2024, proof of Proposition 1.1].
Proof: $\mathbf{H} \pm \delta\mathbf{J}$ are symmetric with the same rounded input as
$\mathbf{H}$, so the method returns the same $(\mathbf{U}, \mathbf{d})$; apply
`NLAlib.exists_mul_card_le_specNorm_add_smul` to $\mathbf{M} = \mathbf{H} -
\mathbf{U}\operatorname{diag}(\mathbf{d})\mathbf{U}^{\mathsf{H}}$ and bound
$\|\mathbf{H} + s\delta\mathbf{J}\|_2 \le \|\mathbf{H}\|_2 + \delta\lvert n \rvert$
(`NLAlib.specNorm_add_le`; the all-ones matrix has norm $\lvert n \rvert$). S, about 30 lines. -/
theorem mul_card_le_of_forall_specNorm_sub_le [DecidableEq n] {fl : ℝ → ℝ} {δ ε : ℝ} (hδ : 0 ≤ δ)
    (alg : Matrix n n ℝ → Matrix n n ℂ × (n → ℝ))
    (halg : ∀ A : Matrix n n ℝ, A.IsSymm →
      specNorm (A.map (fun x : ℝ => (x : ℂ)) - (alg (A.map fl)).1 *
        Matrix.diagonal (fun i => ((alg (A.map fl)).2 i : ℂ)) * (alg (A.map fl)).1ᴴ) ≤
        ε * specNorm A)
    {H : Matrix n n ℝ} (hH : H.IsSymm)
    (hfl : ∀ i j, ∀ s ∈ ({1, -1} : Set ℝ), fl (H i j + s * δ) = fl (H i j)) :
    δ * Fintype.card n ≤ ε * (specNorm H + δ * Fintype.card n) := by
  sorry

/-- **Hermitian diagonalization needs $\log_2(1/\varepsilon) + \tfrac12\log_2 n - 2$ bits**
(Proposition 1.1): for $t \ge 1$, $0 < \varepsilon < 1$ and $n = 2^b$, any method that maps the
input rounded to nearest with $t$ significant bits (`Real.roundNearest`) of every real symmetric
$n \times n$ matrix $\mathbf{A}$ to $(\mathbf{U}, \mathbf{d})$ with
$\|\mathbf{A} - \mathbf{U}\operatorname{diag}(\mathbf{d})\mathbf{U}^{\mathsf{H}}\|_2 \le
\varepsilon\|\mathbf{A}\|_2$ has
$$t \ge \log_2\frac1\varepsilon + \frac b2 - 2 + \log_2(1 - \varepsilon) \,.$$
[Shah2024, Proposition 1.1], there without the term $\log_2(1 - \varepsilon)$, which comes from
$\|\mathbf{H} \pm \delta\mathbf{J}\|_2 \ne \|\mathbf{H}\|_2$.
Proof: `NLAlib.mul_card_le_of_forall_specNorm_sub_le` with $\mathbf{H}$ = `NLAlib.walshHadamard`
$\mathbb{R}$ $b$ (symmetric, `NLAlib.transpose_walshHadamard`;
$\mathbf{H}\mathbf{H} = 2^b\mathbf{I}$,
`NLAlib.walshHadamard_mul_self`, so $\|\mathbf{H}\|_2 = 2^{b/2}$) and $\delta = 2^{-t}/4$: the
rounding to nearest of $\pm1 \pm 2^{-t-2}$ is $\pm1$ (the grid near $1$ has spacing $2^{-t}$
below and $2^{1-t}$ above; `Real.roundNearest_eq_self_of_mem_floatGrid` for $\pm1$ and the
definition of `Real.roundNearest`); then $2^{-t-2}(1 - \varepsilon)2^b \le \varepsilon 2^{b/2}$,
and take $\log_2$ (`Real.logb_le_logb`, `Real.logb_rpow`). M, about 60 lines. -/
theorem logb_inv_add_le_of_forall_specNorm_sub_le {t b : ℕ} (ht : 1 ≤ t) {ε : ℝ} (hε : 0 < ε)
    (hε₁ : ε < 1)
    (alg : Matrix (Fin b → ZMod 2) (Fin b → ZMod 2) ℝ →
      Matrix (Fin b → ZMod 2) (Fin b → ZMod 2) ℂ × ((Fin b → ZMod 2) → ℝ))
    (halg : ∀ A : Matrix (Fin b → ZMod 2) (Fin b → ZMod 2) ℝ, A.IsSymm →
      specNorm (A.map (fun x : ℝ => (x : ℂ)) - (alg (A.map (Real.roundNearest t))).1 *
        Matrix.diagonal (fun i => ((alg (A.map (Real.roundNearest t))).2 i : ℂ)) *
          (alg (A.map (Real.roundNearest t))).1ᴴ) ≤ ε * specNorm A) :
    Real.logb 2 ε⁻¹ + b / 2 - 2 + Real.logb 2 (1 - ε) ≤ t := by
  sorry

end NLAlib
