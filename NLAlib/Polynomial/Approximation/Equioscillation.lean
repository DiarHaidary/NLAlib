/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Fin.Basic

/-!
# Alternation and equioscillation

The alternation predicate of best uniform approximation: a real function alternates in sign at
$k$ ordered points of a set, with modulus at least a level $\varepsilon$. It is the hypothesis of
de la Vallée Poussin's lower bound and, at the level of the uniform error, the conclusion of
Chebyshev's equioscillation theorem. The theorems are in the scaffold until proved
(`docs/design/Polynomial-BestApproximation.md`).

## Main definitions

* `NLAlib.AlternatesOn`: alternation at $k$ ordered points with level $\varepsilon$, with its
  raw-condition constructor `NLAlib.alternatesOn_iff`.
-/

@[expose] public section

namespace NLAlib

/-- The function $g$ **alternates on $s$ at $k$ points with level $\varepsilon$**: there are
points $x_0 < x_1 < \dots < x_{k-1}$ of $s$ and a sign $\sigma \in \{1, -1\}$ with
$\varepsilon \le \sigma(-1)^i g(x_i)$ for every $i$. For $\varepsilon > 0$ the values
$g(x_i)$ alternate in sign and have modulus at least $\varepsilon$ (de la Vallée Poussin's
hypothesis); when also $\lvert g \rvert \le \varepsilon$ on $s$,
$g(x_i) = \sigma(-1)^i\varepsilon$ (equioscillation). For $\varepsilon \le 0$ the condition is
weaker than a sign change. [Trefethen2019, Theorem 10.1]; [Rivlin1981, Ch. 1]. -/
def AlternatesOn (g : ℝ → ℝ) (s : Set ℝ) (k : ℕ) (ε : ℝ) : Prop :=
  ∃ x : Fin k → ℝ, StrictMono x ∧ (∀ i, x i ∈ s) ∧
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ i : Fin k, ε ≤ σ * (-1) ^ (i : ℕ) * g (x i)

/-- Raw-condition constructor and elimination rule for `AlternatesOn`. -/
theorem alternatesOn_iff {g : ℝ → ℝ} {s : Set ℝ} {k : ℕ} {ε : ℝ} :
    AlternatesOn g s k ε ↔ ∃ x : Fin k → ℝ, StrictMono x ∧ (∀ i, x i ∈ s) ∧
      ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ i : Fin k, ε ≤ σ * (-1) ^ (i : ℕ) * g (x i) :=
  Iff.rfl

end NLAlib
