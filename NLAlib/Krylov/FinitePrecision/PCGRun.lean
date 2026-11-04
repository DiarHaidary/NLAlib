/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Basic.MatvecOracle
public import NLAlib.Krylov.FinitePrecision.CGRun
public import NLAlib.Krylov.LinearSystems.PCGRecurrence

/-!
# Preconditioned conjugate gradient runs with a matvec oracle

`NLAlib.PCGRun n k` records successful steps of PCG with bounded arithmetic errors and a
`NLAlib.MatvecOracle` for a fixed positive definite preconditioner. The preconditioner
approximates the inverse of the system matrix. Its application tolerance is separate from
that of the scalar and vector arithmetic. The initial direction is also an oracle output.

The scalar numerator is a computed pairing of the residual and its preconditioned vector,
with an additive dot-product error. It is not assumed to be an exactly weighted norm.
Successful steps have positive numerator and curvature; the terminal numerator may be zero.
The contract does not assert convergence for every oracle satisfying a Euclidean error bound.

## Main definitions

* `NLAlib.PCGRun`: the physical run and its error certificates.
* `NLAlib.CGRun.toPCGRun`: ordinary CG with the exact identity preconditioner.

## Main results

* `NLAlib.PCGRun.norm_mulVec_sub_z_le`: the preconditioner-application error.
* `NLAlib.PCGRun.norm_mulVec_sub_p_zero_le`: the initial direction error.
* `NLAlib.PCGRun.ν_eq_zero_of_r_eq_zero`: a zero residual has zero numerator.
* `NLAlib.PCGRun.sub_mulVec_x_sub_r_succ`: the residual-gap recurrence.
* `NLAlib.PCGRun.state_eq_pcgState`: zero errors recover the exact PCG recurrence.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

/-- A run of $k \ge 1$ successful PCG steps from the zero iterate, for a real Hermitian
$\mathbf{A}$ and a fixed positive definite preconditioner $\mathbf{M}$ applied through a
matvec oracle. Arithmetic defects are bounded by $\varepsilon$ times their operands, with
$\varepsilon \le 1/100$. The oracle supplies its own tolerance. The computed numerator and
curvature are positive at each step taken; the final numerator is nonnegative. This is a
local-error model of the recurrence in [Saad2003, Algorithm 9.1], in the convention where
$\mathbf{M}$ approximates $\mathbf{A}^{-1}$.
Algorithm: pcg (run model) -/
structure PCGRun (n k : ℕ) where
  /-- The matrix. -/
  A : Matrix (Fin n) (Fin n) ℝ
  /-- The fixed preconditioner, approximating the inverse of the system matrix. -/
  M : Matrix (Fin n) (Fin n) ℝ
  /-- The approximate action of the preconditioner, with its own error tolerance. -/
  preconditioner : MatvecOracle M
  /-- The reference preconditioner is positive definite. -/
  posDef_M : M.PosDef
  /-- The right-hand side. -/
  b : Fin n → ℝ
  /-- The iterates $\mathbf{x}_j$. -/
  x : ℕ → Fin n → ℝ
  /-- The updated residuals $\mathbf{r}_j$. -/
  r : ℕ → Fin n → ℝ
  /-- The oracle outputs on the updated residuals. -/
  z : ℕ → Fin n → ℝ
  /-- The search directions $\mathbf{p}_j$. -/
  p : ℕ → Fin n → ℝ
  /-- The products $\mathbf{s}_j$. -/
  s : ℕ → Fin n → ℝ
  /-- The computed residual-preconditioned-residual pairings $\nu_j$. -/
  ν : ℕ → ℝ
  /-- The computed curvatures $\mu_j$. -/
  μ : ℕ → ℝ
  /-- The step lengths $\gamma_j$. -/
  γ : ℕ → ℝ
  /-- The direction coefficients $\delta_j$. -/
  δ : ℕ → ℝ
  /-- The error of the product. -/
  es : ℕ → Fin n → ℝ
  /-- The additive error of the residual-preconditioned-residual pairing. -/
  eν : ℕ → ℝ
  /-- The error of the curvature. -/
  eμ : ℕ → ℝ
  /-- The relative error of the step length. -/
  eγ : ℕ → ℝ
  /-- The error of the iterate update. -/
  ex : ℕ → Fin n → ℝ
  /-- The error of the residual update. -/
  er : ℕ → Fin n → ℝ
  /-- The relative error of the direction coefficient. -/
  eδ : ℕ → ℝ
  /-- The error of the direction update. -/
  ep : ℕ → Fin n → ℝ
  /-- The accuracy parameter. -/
  ε : ℝ
  /-- The system matrix is Hermitian. -/
  isHermitian_A : A.IsHermitian
  /-- The accuracy parameter is nonnegative. -/
  ε_nonneg : 0 ≤ ε
  /-- At least one step. -/
  k_pos : 0 < k
  /-- Small accuracy parameter. -/
  ε_le : ε ≤ 1 / 100
  /-- $\mathbf{x}_0 = \mathbf{0}$. -/
  x_zero : x 0 = 0
  /-- $\mathbf{r}_0 = \mathbf{b}$. -/
  r_zero : r 0 = b
  /-- The initial direction is the first oracle output. -/
  p_zero : p 0 = z 0
  /-- Every preconditioned residual, including the initial one, comes from the oracle. -/
  z_eq : ∀ j ≤ k, z j = preconditioner.mulVec (r j)
  /-- The computed residual-preconditioned-residual pairing. -/
  ν_eq : ∀ j ≤ k, ν j = r j ⬝ᵥ z j + eν j
  /-- The error of that pairing, relative to its operands. -/
  abs_eν_le : ∀ j ≤ k,
    |eν j| ≤ ε * ‖WithLp.toLp 2 (r j)‖ * ‖WithLp.toLp 2 (z j)‖
  /-- The last pairing may be zero but is not negative. -/
  ν_last_nonneg : 0 ≤ ν k
  /-- No stop before the last step. -/
  ν_pos : ∀ j < k, 0 < ν j
  /-- The computed product. -/
  s_eq : ∀ j < k, s j = A *ᵥ p j + es j
  /-- The product error. -/
  norm_es_le : ∀ j < k,
    ‖WithLp.toLp 2 (es j)‖ ≤ ε * specNorm A * ‖WithLp.toLp 2 (p j)‖
  /-- The computed curvature. -/
  μ_eq : ∀ j < k, μ j = p j ⬝ᵥ s j + eμ j
  /-- The curvature error. -/
  abs_eμ_le : ∀ j < k, |eμ j| ≤ ε * ‖WithLp.toLp 2 (p j)‖ * ‖WithLp.toLp 2 (s j)‖
  /-- The curvature is positive at every step taken (the division succeeded). -/
  μ_pos : ∀ j < k, 0 < μ j
  /-- The step length. -/
  γ_eq : ∀ j < k, γ j = ν j / μ j * (1 + eγ j)
  /-- Its relative error. -/
  abs_eγ_le : ∀ j < k, |eγ j| ≤ ε
  /-- The iterate update. -/
  x_succ : ∀ j < k, x (j + 1) = x j + γ j • p j + ex j
  /-- The iterate update error. -/
  norm_ex_le : ∀ j < k, ‖WithLp.toLp 2 (ex j)‖ ≤
    ε * (‖WithLp.toLp 2 (x j)‖ + |γ j| * ‖WithLp.toLp 2 (p j)‖)
  /-- The residual update. -/
  r_succ : ∀ j < k, r (j + 1) = r j - γ j • s j + er j
  /-- The residual update error. -/
  norm_er_le : ∀ j < k, ‖WithLp.toLp 2 (er j)‖ ≤
    ε * (‖WithLp.toLp 2 (r j)‖ + |γ j| * ‖WithLp.toLp 2 (s j)‖)
  /-- The direction coefficient. -/
  δ_eq : ∀ j < k, δ j = ν (j + 1) / ν j * (1 + eδ j)
  /-- Its relative error. -/
  abs_eδ_le : ∀ j < k, |eδ j| ≤ ε
  /-- The direction update. -/
  p_succ : ∀ j < k, p (j + 1) = z (j + 1) + δ j • p j + ep j
  /-- The direction update error. -/
  norm_ep_le : ∀ j < k, ‖WithLp.toLp 2 (ep j)‖ ≤
    ε * (‖WithLp.toLp 2 (z (j + 1))‖ + |δ j| * ‖WithLp.toLp 2 (p j)‖)

namespace PCGRun

variable {n k : ℕ} (P : PCGRun n k)

/-- The four physical vectors of a PCG run at step $j$, in the exact recurrence's state type. -/
def state (j : ℕ) : PCGState ℝ (Fin n) := ⟨P.x j, P.r j, P.z j, P.p j⟩

/-- The preconditioned residual differs from the exact action by the oracle error budget. -/
theorem norm_mulVec_sub_z_le (j : ℕ) (hj : j ≤ k) :
    ‖WithLp.toLp 2 (P.M *ᵥ P.r j - P.z j)‖ ≤
      P.preconditioner.ε * specNorm P.M * ‖WithLp.toLp 2 (P.r j)‖ := by
  rw [P.z_eq j hj]
  exact P.preconditioner.norm_sub_mulVec_le _

/-- The initial search direction differs from the exact preconditioned right-hand side by
the first oracle application's error budget. -/
theorem norm_mulVec_sub_p_zero_le :
    ‖WithLp.toLp 2 (P.M *ᵥ P.b - P.p 0)‖ ≤
      P.preconditioner.ε * specNorm P.M * ‖WithLp.toLp 2 P.b‖ := by
  rw [P.p_zero, ← P.r_zero]
  exact P.norm_mulVec_sub_z_le 0 (Nat.zero_le _)

/-- A zero residual produces a zero preconditioned residual. -/
theorem z_eq_zero_of_r_eq_zero {j : ℕ} (hj : j ≤ k) (hr : P.r j = 0) : P.z j = 0 := by
  rw [P.z_eq j hj, hr, MatvecOracle.mulVec_zero]

/-- A zero residual has zero computed numerator, including at the terminal step. -/
theorem ν_eq_zero_of_r_eq_zero {j : ℕ} (hj : j ≤ k) (hr : P.r j = 0) : P.ν j = 0 := by
  have he := P.abs_eν_le j hj
  simp only [hr, WithLp.toLp_zero, norm_zero, mul_zero, zero_mul] at he
  have he0 : P.eν j = 0 := abs_eq_zero.mp (le_antisymm he (abs_nonneg _))
  rw [P.ν_eq j hj, hr, zero_dotProduct, he0, add_zero]

/-- Every residual before a successful step is nonzero. -/
theorem r_ne_zero {j : ℕ} (hj : j < k) : P.r j ≠ 0 := by
  intro hr
  have h := P.ν_pos j hj
  rw [P.ν_eq_zero_of_r_eq_zero hj.le hr] at h
  exact lt_irrefl _ h

/-- The residual-gap recurrence involves the matvec, iterate and residual-update defects.
The preconditioner influences it through the search directions, not through an extra gap term. -/
theorem sub_mulVec_x_sub_r_succ {j : ℕ} (hj : j < k) :
    P.b - P.A *ᵥ P.x (j + 1) - P.r (j + 1) =
      (P.b - P.A *ᵥ P.x j - P.r j) + P.γ j • P.es j - P.A *ᵥ P.ex j - P.er j := by
  rw [P.x_succ j hj, P.r_succ j hj, P.s_eq j hj]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, smul_add]
  abel

/-- At zero arithmetic tolerance, the computed residual pairing has no dot-product error. -/
theorem ν_eq_dotProduct_of_ε_eq_zero (hε : P.ε = 0) {j : ℕ} (hj : j ≤ k) :
    P.ν j = P.r j ⬝ᵥ P.z j := by
  have he := P.abs_eν_le j hj
  rw [hε, zero_mul, zero_mul] at he
  rw [P.ν_eq j hj, abs_eq_zero.mp (le_antisymm he (abs_nonneg _)), add_zero]

private theorem state_succ_of_ε_eq_zero (hε : P.ε = 0)
    (hM : P.preconditioner.ε = 0) {j : ℕ} (hj : j < k) :
    P.state (j + 1) = pcgStep P.A P.M (P.state j) := by
  have hes : P.es j = 0 := by
    simpa only [hε, zero_mul, norm_le_zero_iff, WithLp.toLp_eq_zero] using P.norm_es_le j hj
  have hex : P.ex j = 0 := by
    simpa only [hε, zero_mul, norm_le_zero_iff, WithLp.toLp_eq_zero] using P.norm_ex_le j hj
  have her : P.er j = 0 := by
    simpa only [hε, zero_mul, norm_le_zero_iff, WithLp.toLp_eq_zero] using P.norm_er_le j hj
  have hep : P.ep j = 0 := by
    simpa only [hε, zero_mul, norm_le_zero_iff, WithLp.toLp_eq_zero] using P.norm_ep_le j hj
  have heμ := P.abs_eμ_le j hj
  rw [hε, zero_mul, zero_mul] at heμ
  have heμ0 := abs_eq_zero.mp (le_antisymm heμ (abs_nonneg _))
  have heγ := P.abs_eγ_le j hj
  rw [hε] at heγ
  have heγ0 := abs_eq_zero.mp (le_antisymm heγ (abs_nonneg _))
  have heδ := P.abs_eδ_le j hj
  rw [hε] at heδ
  have heδ0 := abs_eq_zero.mp (le_antisymm heδ (abs_nonneg _))
  have hs : P.s j = P.A *ᵥ P.p j := by rw [P.s_eq j hj, hes, add_zero]
  have hμ : P.μ j = P.p j ⬝ᵥ (P.A *ᵥ P.p j) := by
    rw [P.μ_eq j hj, hs, heμ0, add_zero]
  have hγ : P.γ j = (P.r j ⬝ᵥ P.z j) / (P.p j ⬝ᵥ (P.A *ᵥ P.p j)) := by
    rw [P.γ_eq j hj, P.ν_eq_dotProduct_of_ε_eq_zero hε hj.le, hμ, heγ0, add_zero, mul_one]
  have hδ : P.δ j = (P.r (j + 1) ⬝ᵥ P.z (j + 1)) / (P.r j ⬝ᵥ P.z j) := by
    rw [P.δ_eq j hj, P.ν_eq_dotProduct_of_ε_eq_zero hε (Nat.succ_le_of_lt hj),
      P.ν_eq_dotProduct_of_ε_eq_zero hε hj.le, heδ0, add_zero, mul_one]
  have hx : P.x (j + 1) = P.x j + P.γ j • P.p j := by
    rw [P.x_succ j hj, hex, add_zero]
  have hr : P.r (j + 1) = P.r j - P.γ j • (P.A *ᵥ P.p j) := by
    rw [P.r_succ j hj, hs, her, add_zero]
  have hz : P.z (j + 1) = P.M *ᵥ P.r (j + 1) := by
    rw [P.z_eq (j + 1) (Nat.succ_le_of_lt hj),
      P.preconditioner.mulVec_eq_of_ε_eq_zero hM]
  have hp : P.p (j + 1) = P.z (j + 1) + P.δ j • P.p j := by
    rw [P.p_succ j hj, hep, add_zero]
  simp only [state, pcgStep, quadForm_def, star_trivial, RCLike.re_to_real]
  rw [hx, hp, hδ, hz, hr, hγ]
  simp only [RCLike.ofReal_real_eq_id, id_eq]

/-- With zero arithmetic and oracle tolerances, every state through step $k$ is the exact
PCG recurrence from zero, including its terminal state. -/
theorem state_eq_pcgState (hε : P.ε = 0) (hM : P.preconditioner.ε = 0)
    {j : ℕ} (hj : j ≤ k) : P.state j = pcgState P.A P.M P.b 0 j := by
  induction j with
  | zero =>
    simp only [state, pcgState, P.x_zero, P.p_zero, P.z_eq 0 (Nat.zero_le _),
      P.r_zero, P.preconditioner.mulVec_eq_of_ε_eq_zero hM, Matrix.mulVec_zero, sub_zero]
  | succ j ih =>
    rw [P.state_succ_of_ε_eq_zero hε hM (Nat.lt_of_succ_le hj),
      ih (Nat.le_of_succ_le hj), pcgState]

end PCGRun

namespace CGRun

variable {n k : ℕ}

/-- An ordinary CG run is a PCG run with the exact identity oracle. The iterates, residuals,
directions, computed products and scalar coefficients are preserved. The relative squared-norm
error becomes the additive dot-product error. -/
noncomputable def toPCGRun (C : CGRun n k) : PCGRun n k where
  A := C.A
  M := 1
  preconditioner := MatvecOracle.ofMatrix 1
  posDef_M := Matrix.PosDef.one
  b := C.b
  x := C.x
  r := C.r
  z := C.r
  p := C.p
  s := C.s
  ν := C.ν
  μ := C.μ
  γ := C.γ
  δ := C.δ
  es := C.es
  eν := fun j => ‖WithLp.toLp 2 (C.r j)‖ ^ 2 * C.θ j
  eμ := C.eμ
  eγ := C.eγ
  ex := C.ex
  er := C.er
  eδ := C.eδ
  ep := C.ep
  ε := C.ε
  isHermitian_A := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using
      C.transpose_A
  ε_nonneg := C.ε_nonneg
  k_pos := C.k_pos
  ε_le := C.ε_le
  x_zero := C.x_zero
  r_zero := C.r_zero
  p_zero := C.p_zero.trans C.r_zero.symm
  z_eq := fun j _ => (Matrix.one_mulVec (C.r j)).symm
  ν_eq := fun j hj => by
    rw [C.ν_eq j hj, ← EuclideanSpace.norm_toLp_sq_eq_dotProduct_self]
    ring
  abs_eν_le := fun j hj => by
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    calc
      _ ≤ ‖WithLp.toLp 2 (C.r j)‖ ^ 2 * C.ε :=
        mul_le_mul_of_nonneg_left (C.abs_θ_le j hj) (sq_nonneg _)
      _ = _ := by ring
  ν_last_nonneg := by
    rw [C.ν_eq' le_rfl]
    exact mul_nonneg (sq_nonneg _) (C.one_add_θ_pos le_rfl).le
  ν_pos := C.ν_pos
  s_eq := C.s_eq
  norm_es_le := C.norm_es_le
  μ_eq := C.μ_eq
  abs_eμ_le := C.abs_eμ_le
  μ_pos := C.μ_pos
  γ_eq := C.γ_eq
  abs_eγ_le := C.abs_eγ_le
  x_succ := C.x_succ
  norm_ex_le := C.norm_ex_le
  r_succ := C.r_succ
  norm_er_le := C.norm_er_le
  δ_eq := C.δ_eq
  abs_eδ_le := C.abs_eδ_le
  p_succ := C.p_succ
  norm_ep_le := C.norm_ep_le

/-- Embedding an ordinary CG run preserves its iterates. -/
@[simp] theorem x_toPCGRun (C : CGRun n k) : C.toPCGRun.x = C.x := rfl

/-- Embedding an ordinary CG run preserves its recursive residuals. -/
@[simp] theorem r_toPCGRun (C : CGRun n k) : C.toPCGRun.r = C.r := rfl

end CGRun

end NLAlib
