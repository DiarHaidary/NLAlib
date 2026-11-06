/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Norms.Spectral

/-!
# The decoded guarantee of an orthogonalization step

One step of an orthogonalization scheme reduces a vector $\mathbf{w}$ against the $j$ columns of
a computed, nearly orthonormal basis $\mathbf{V}$, writing coefficients $\mathbf{h}$ and the
reduced vector $\mathbf{w}'$. `NLAlib.IsOrthErr` is the guarantee a scheme provides on decoded
values: given $\|\mathbf{V}^{\mathsf{T}}\mathbf{V} - \mathbf{I}\|_2 \le \eta_0$,
$$\|\mathbf{w} - \mathbf{V}\mathbf{h} - \mathbf{w}'\| \le \varepsilon_2\|\mathbf{w}\|, \qquad
\|\mathbf{V}^{\mathsf{T}}\mathbf{w}'\| \le
\varepsilon_1\|\mathbf{w}'\| + \varepsilon_3\|\mathbf{w}\|.$$
The term $\varepsilon_3$ is first order in $\eta_0$ for one classical Gram–Schmidt pass and second
order for two ("twice is enough"). Design: `docs/design/Krylov-LanczosReorth.md` §1.1.

## Main definitions

* `NLAlib.IsOrthErr`: the decoded guarantee of one orthogonalization step.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

/-- **The decoded guarantee of one orthogonalization step** against a nearly orthonormal basis:
if $\|\mathbf{V}^{\mathsf{T}}\mathbf{V} - \mathbf{I}\|_2 \le \eta_0$, the coefficients
$\mathbf{h}$ and the reduced vector $\mathbf{w}'$ represent $\mathbf{w}$ up to
$\varepsilon_2\|\mathbf{w}\|$, and $\mathbf{w}'$ is orthogonal to the basis up to
$\varepsilon_1\|\mathbf{w}'\| + \varepsilon_3\|\mathbf{w}\|$. No admissibility condition on
$\mathbf{w}$; [GiraudLangouRozloznikVandenEshof2005, Theorems 1–2] for classical Gram–Schmidt with
one and two
passes in this sense. -/
structure IsOrthErr {n j : ℕ} (η₀ ε₁ ε₂ ε₃ : ℝ) (V : Matrix (Fin n) (Fin j) ℝ)
    (w : Fin n → ℝ) (h : Fin j → ℝ) (w' : Fin n → ℝ) : Prop where
  /-- The representation of the input. -/
  residual : specNorm (Vᵀ * V - 1) ≤ η₀ →
    ‖WithLp.toLp 2 (w - V *ᵥ h - w')‖ ≤ ε₂ * ‖WithLp.toLp 2 w‖
  /-- The local loss of orthogonality. -/
  orth : specNorm (Vᵀ * V - 1) ≤ η₀ →
    ‖WithLp.toLp 2 (Vᵀ *ᵥ w')‖ ≤ ε₁ * ‖WithLp.toLp 2 w'‖ + ε₃ * ‖WithLp.toLp 2 w‖

end NLAlib
