/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.FinitePrecision.LanczosReorthRun
public import NLAlib.Krylov.Processes.LanczosReorthProgramTree
public import NLAlib.Krylov.Processes.LanczosProgramRounding

/-!
# The decoded outputs of a rounded run of Lanczos with full reorthogonalization

`NLAlib.LanczosReorthOutputs` packages what the rounded execution theorems of the programs in
`NLAlib/Krylov/Processes/LanczosReorthProgramTree.lean` conclude about the final store: the
declared buffers decode to a basis $\mathbf{v}_1, \dots, \mathbf{v}_{q+1}$, coefficients
$\alpha_j$, $\beta_j$ and stored norms $\nu_j$; $\mathbf{v}_1$ is close to
$\mathbf{b}/\|\mathbf{b}\|$; and every admissible prefix ($\tau\nu_j < \beta_j$ for its steps) is a
`NLAlib.LanczosReorthRun` with the given parameters. Design:
`docs/design/Krylov-LanczosReorth.md` §2.3.

## Main definitions

* `NLAlib.LanczosReorthOutputs`: the decoded-output predicate.

## Main results

* `NLAlib.roundingFactor_succ_le_lanczosImplementationRoundoffBound`: the factor of a norm of
  length $N$ fits the budget.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation

/-- **The decoded outputs of a rounded Lanczos run with full reorthogonalization**, buffers as in
`NLAlib.lanczosReorthLoop` (`b` 0, `V` 1, `alpha` 2, `beta` 3, `nu` 6), with scalar accuracy
$\varepsilon$, admissibility threshold $\tau$ and orthogonalization parameters
$(\eta_0, \varepsilon_1, \varepsilon_2, \varepsilon_3)$. -/
def LanczosReorthOutputs {P K : Type} [DecidableEq P] (s : Store P K) (dec : P → K → ℝ)
    (tag : P) (N q : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ)
    (ε τ η₀ ε₁ ε₂ ε₃ : ℝ) : Prop :=
  ∃ (v : ℕ → Fin N → ℝ) (α β ν : ℕ → ℝ),
    HoldsDecoded s dec tag 0 0 (fun i (_ : Fin 1) => b i) ∧
    HoldsDecoded s dec tag 1 0 (fun i (j : Fin (q + 1)) => v ((j : ℕ) + 1) i) ∧
    HoldsDecoded s dec tag 2 0 (fun (j : Fin q) (_ : Fin 1) => α ((j : ℕ) + 1)) ∧
    HoldsDecoded s dec tag 3 0 (fun (j : Fin (q + 1)) (_ : Fin 1) => β j) ∧
    HoldsDecoded s dec tag 6 0 (fun (j : Fin q) (_ : Fin 1) => ν ((j : ℕ) + 1)) ∧
    ‖WithLp.toLp 2 (‖WithLp.toLp 2 b‖⁻¹ • b - v 1)‖ ≤ 3 * ε ∧
    ∀ m, 0 < m → m ≤ q → (∀ j < m, τ * ν (j + 1) < β (j + 1)) →
      ∃ L : LanczosReorthRun N m, L.H = A ∧ (∀ j, 1 ≤ j → j ≤ m + 1 → L.v j = v j) ∧
        (∀ j ≤ m, L.α j = α j ∧ L.β j = β j ∧ L.ν j = ν j) ∧
        L.ε = ε ∧ L.τ = τ ∧ L.η₀ = η₀ ∧ L.ε₁ = ε₁ ∧ L.ε₂ = ε₂ ∧ L.ε₃ = ε₃

/-- The rounding factor $\gamma_{N+1}(u)$ of a norm of length $N$ is at most the Lanczos
implementation budget `NLAlib.lanczosImplementationRoundoffBound` $N\,u$, which
is <!-- value lanczosImplementationRoundoffBound N u -->$16(N+1)^2u$, when $u \ge 0$ and the
budget is at most $1/100$. -/
theorem roundingFactor_succ_le_lanczosImplementationRoundoffBound (N : ℕ) {u : ℝ} (hu : 0 ≤ u)
    (hsmall : lanczosImplementationRoundoffBound N u ≤ 1 / 100) :
    roundingFactor (N + 1) u ≤ lanczosImplementationRoundoffBound N u := by
  have hγ := roundingFactor_le_two_mul_of_lanczosImplementationRoundoffBound_le
    (N := N) (m := N + 1) (by omega) hu hsmall
  rw [lanczosImplementationRoundoffBound_def] at hsmall ⊢
  push_cast at hγ
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  nlinarith [mul_nonneg (mul_nonneg hN hN) hu, mul_nonneg hN hu]

end NLAlib
