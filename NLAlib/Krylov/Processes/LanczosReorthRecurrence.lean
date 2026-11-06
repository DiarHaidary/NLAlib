/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Processes.LanczosRecurrence

/-!
# The Lanczos recurrence with full reorthogonalization

`NLAlib.lanczosReorthState A b j` is the state before step $j$ of Lanczos with full
reorthogonalization in exact arithmetic: Paige's order
$\mathbf{z}_j = \mathbf{A}\mathbf{q}_j - \beta_j\mathbf{q}_{j-1} - \alpha_j\mathbf{q}_j$ (as
`NLAlib.lanczosStep`), then two classical Gram–Schmidt passes of $\mathbf{z}_j$ against
$\mathbf{q}_0, \dots, \mathbf{q}_j$ (`NLAlib.cgsProject`), then normalization, with
$0^{-1} = 0$ at breakdown. The state also records the norm $\nu_j = \|\mathbf{z}_j\|$ before
orthogonalization, which the program stores. For every square $\mathbf{A}$ the recurrence is
total; for Hermitian $\mathbf{A}$ it is the Lanczos recurrence (the reorthogonalization subtracts
zeros). [Paige1970]. Design: `docs/design/Krylov-LanczosReorth.md` §2.3.

## Main definitions

* `NLAlib.cgsProject`: one exact classical Gram–Schmidt pass.
* `NLAlib.LanczosReorthState`, `NLAlib.lanczosReorthStep`, `NLAlib.lanczosReorthState`,
  `NLAlib.lanczosReorthMatrix`: the recurrence and its basis.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- **One exact classical Gram–Schmidt pass** of $\mathbf{w}$ against $\mathbf{q}_0, \dots,
\mathbf{q}_{m-1}$: $\mathbf{w} - \sum_{i<m} (\mathbf{q}_i^{\mathsf{H}}\mathbf{w})\mathbf{q}_i$.
Algorithm: gram-schmidt -/
noncomputable def cgsProject (Q : ℕ → n → 𝕜) (m : ℕ) (w : n → 𝕜) : n → 𝕜 :=
  w - ∑ i ∈ Finset.range m, (star (Q i) ⬝ᵥ w) • Q i

/-- The state of the Lanczos recurrence with full reorthogonalization before step $j$: all
vectors $\mathbf{q}_0, \dots, \mathbf{q}_j$ (zero beyond $j$), the previous and current vectors,
$\beta_j$, and the norm $\nu_j$ of the last vector before orthogonalization ($0$ for $j = 0$).
Algorithm: lanczos-reorth -/
structure LanczosReorthState (𝕜 n : Type*) where
  /-- The vectors $\mathbf{q}_0, \dots, \mathbf{q}_j$, zero beyond $j$. -/
  vecs : ℕ → n → 𝕜
  /-- The previous vector $\mathbf{q}_{j-1}$ ($\mathbf{0}$ for $j = 0$). -/
  prev : n → 𝕜
  /-- The current vector $\mathbf{q}_j$. -/
  cur : n → 𝕜
  /-- The coefficient $\beta_j$. -/
  beta : ℝ
  /-- The norm $\nu_j$ before orthogonalization. -/
  nu : ℝ

/-- The plain Lanczos state underlying a reorthogonalized one. -/
def LanczosReorthState.toLanczosState (s : LanczosReorthState 𝕜 n) : LanczosState 𝕜 n :=
  ⟨s.prev, s.cur, s.beta⟩

/-- **Step $j$ of Lanczos with full reorthogonalization**: Paige's update, two classical
Gram–Schmidt passes against $\mathbf{q}_0, \dots, \mathbf{q}_j$, normalization.
Algorithm: lanczos-reorth -/
noncomputable def lanczosReorthStep (A : Matrix n n 𝕜) (j : ℕ) (s : LanczosReorthState 𝕜 n) :
    LanczosReorthState 𝕜 n :=
  let z := A *ᵥ s.cur - (s.beta : 𝕜) • s.prev - (lanczosAlpha A s.toLanczosState : 𝕜) • s.cur
  let z' := cgsProject s.vecs (j + 1) (cgsProject s.vecs (j + 1) z)
  let c := (‖WithLp.toLp 2 z'‖⁻¹ : 𝕜) • z'
  ⟨Function.update s.vecs (j + 1) c, s.cur, c, ‖WithLp.toLp 2 z'‖, ‖WithLp.toLp 2 z‖⟩

/-- **The Lanczos recurrence with full reorthogonalization**: the state before step $j$, from
$\mathbf{q}_0 = \mathbf{b}/\|\mathbf{b}\|$.
Algorithm: lanczos-reorth -/
noncomputable def lanczosReorthState (A : Matrix n n 𝕜) (b : n → 𝕜) :
    ℕ → LanczosReorthState 𝕜 n
  | 0 =>
    let q₀ := (‖WithLp.toLp 2 b‖⁻¹ : 𝕜) • b
    ⟨Function.update 0 0 q₀, 0, q₀, 0, 0⟩
  | j + 1 => lanczosReorthStep A j (lanczosReorthState A b j)

/-- The basis computed by $q$ steps of the reorthogonalized recurrence: column $j$ is
$\mathbf{q}_j$.
Algorithm: lanczos-reorth -/
noncomputable def lanczosReorthMatrix (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) :
    Matrix n (Fin q) 𝕜 :=
  Matrix.of fun i j => (lanczosReorthState A b j).cur i

end NLAlib
