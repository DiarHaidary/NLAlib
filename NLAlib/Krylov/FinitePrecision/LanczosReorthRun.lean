/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.FinitePrecision.LanczosData
public import NLAlib.Matrix.Perturbation.OrthErr

/-!
# Finite-precision Lanczos runs with full reorthogonalization

`NLAlib.LanczosReorthRun n k` is the data of $k$ computed steps of Lanczos with full
reorthogonalization in Paige's order and the local guarantees that rounded execution supplies:
the local errors of `NLAlib.LanczosRun` for the product and the two updates, the stored norm
$\nu_j$ of $\mathbf{z}_j$, the orthogonalization guarantee `NLAlib.IsOrthErr` of
$\mathbf{z}_j$ against $\mathbf{v}_1, \dots, \mathbf{v}_j$ (parameters $\eta_0$,
$\varepsilon_1$, $\varepsilon_2$, $\varepsilon_3$), the normalization, and strict
$\tau$-admissibility $\tau\nu_j < \beta_j$ of every step (the stopping criterion of
[Paige1970] in contract form). It is not a `NLAlib.LanczosRun`: the reorthogonalization
correction is absolute, not relative to $\|\mathbf{w}_j\|$. Indices as in `NLAlib.LanczosRun`:
$\mathbf{v}_0 = \mathbf{0}$, steps $j + 1$ for $j < k$, coefficient $h_{j+1, i}$ of
$\mathbf{z}_{j+1}$ against $\mathbf{v}_{i+1}$ for $i \le j$. Design:
`docs/design/Krylov-LanczosReorth.md` §3.1.

## Main definitions

* `NLAlib.LanczosReorthRun`: the run.
* `NLAlib.LanczosReorthRun.basisOf`: the first $m$ vectors as a matrix.
* `NLAlib.LanczosReorthRun.toLanczosData`: the underlying three-term data.
* `NLAlib.LanczosReorthRun.orthLevel`, `NLAlib.LanczosReorthRun.recLevel`: the per-column
  orthogonality level $\mu$ and the recurrence level $\mu + \varepsilon + \varepsilon_2$.
* `NLAlib.LanczosReorthRun.backwardRadius`, `NLAlib.LanczosReorthRun.colSeq`: the backward
  radius and the columns of a basis as a sequence.
* `NLAlib.LanczosReorthRun.firstIndex`: the index $0$ of `Fin k`.
* `NLAlib.reorthSteps`: the admissible prefix read off computed outputs.

## Main results

* `NLAlib.LanczosReorthRun.recurrenceError_eq`: the residual of the three-term relation.
* `NLAlib.LanczosReorthRun.norm_transpose_mulVec_v_le`: one admissible column is nearly
  orthogonal to the previous ones.
* `NLAlib.LanczosReorthRun.frobNorm_transpose_mul_self_sub_one_le`: orthogonality of the computed
  basis, $\|\mathbf{V}_m^{\mathsf{T}}\mathbf{V}_m - \mathbf{I}\|_{\mathsf F} \le \sqrt{3m}\,\mu$.
* `NLAlib.LanczosReorthRun.succ_le_card`: the run stops by step $n$.
* `NLAlib.LanczosReorthRun.exists_ofLE`: prefixes of a run are runs.

## Basic API

* `NLAlib.LanczosReorthRun.orthLevel_nonneg`, `NLAlib.LanczosReorthRun.recLevel_nonneg`,
  `NLAlib.LanczosReorthRun.orthLevel_le_recLevel`: the levels.
* `NLAlib.LanczosReorthRun.β_succ_pos`, `NLAlib.LanczosReorthRun.β_nonneg`: signs of $\beta_j$.
* `NLAlib.LanczosReorthRun.norm_v_sq_le`, `NLAlib.LanczosReorthRun.norm_v_le`: norms of the
  Lanczos vectors.
* `NLAlib.LanczosReorthRun.specNorm_transpose_mul_self_sub_one_le`: the spectral form of the
  orthogonality bound.

The coefficient bounds are in `NLAlib/Krylov/FinitePrecision/LanczosReorthCoefficients.lean`, the
perturbed Lanczos relation in `NLAlib/Krylov/FinitePrecision/LanczosReorthResidual.lean`.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

/-- The first $m$ vectors $\mathbf{v}_1, \dots, \mathbf{v}_m$ of a sequence as the columns of an
$n \times m$ matrix. -/
def LanczosReorthRun.basisOf {n : ℕ} (v : ℕ → Fin n → ℝ) (m : ℕ) : Matrix (Fin n) (Fin m) ℝ :=
  Matrix.of fun i c => v ((c : ℕ) + 1) i

/-- **A finite-precision Lanczos run with full reorthogonalization**, $k \ge 1$ steps. -/
structure LanczosReorthRun (n k : ℕ) where
  /-- The matrix. -/
  H : Matrix (Fin n) (Fin n) ℝ
  /-- The Lanczos vectors $\mathbf{v}_j$. -/
  v : ℕ → Fin n → ℝ
  /-- The products $\mathbf{u}_j$. -/
  u : ℕ → Fin n → ℝ
  /-- The vectors $\mathbf{w}_j$. -/
  w : ℕ → Fin n → ℝ
  /-- The vectors $\mathbf{z}_j$ before orthogonalization. -/
  z : ℕ → Fin n → ℝ
  /-- The vectors $\mathbf{z}_j'$ after orthogonalization. -/
  z' : ℕ → Fin n → ℝ
  /-- The diagonal coefficients $\alpha_j$. -/
  α : ℕ → ℝ
  /-- The off-diagonal coefficients $\beta_j$. -/
  β : ℕ → ℝ
  /-- The stored norms $\nu_j$ of $\mathbf{z}_j$. -/
  ν : ℕ → ℝ
  /-- The reorthogonalization coefficients $h_{j,i}$ (discarded by the program). -/
  h : ℕ → ℕ → ℝ
  /-- The error of the product. -/
  eu : ℕ → Fin n → ℝ
  /-- The error of the first update. -/
  ew : ℕ → Fin n → ℝ
  /-- The error of the second update. -/
  ez : ℕ → Fin n → ℝ
  /-- The error of the inner product. -/
  eα : ℕ → ℝ
  /-- The error of the normalization. -/
  δ : ℕ → Fin n → ℝ
  /-- The scalar accuracy parameter. -/
  ε : ℝ
  /-- The admissibility threshold. -/
  τ : ℝ
  /-- The orthogonality precondition of the scheme. -/
  η₀ : ℝ
  /-- The output-relative orthogonality parameter of the scheme. -/
  ε₁ : ℝ
  /-- The residual parameter of the scheme. -/
  ε₂ : ℝ
  /-- The input-relative orthogonality parameter of the scheme. -/
  ε₃ : ℝ
  /-- The matrix is symmetric. -/
  transpose_H : Hᵀ = H
  /-- The scalar accuracy parameter is nonnegative. -/
  ε_nonneg : 0 ≤ ε
  /-- Local accuracy. -/
  ε_le : ε ≤ 1 / 100
  /-- The scheme parameters are nonnegative. -/
  ε₁_nonneg : 0 ≤ ε₁
  /-- The scheme parameters are nonnegative. -/
  ε₂_nonneg : 0 ≤ ε₂
  /-- The scheme parameters are nonnegative. -/
  ε₃_nonneg : 0 ≤ ε₃
  /-- At least one step. -/
  k_pos : 0 < k
  /-- $\mathbf{v}_0 = \mathbf{0}$. -/
  v_zero : v 0 = 0
  /-- $\beta_0 = 0$. -/
  β_zero : β 0 = 0
  /-- The computed product. -/
  u_eq : ∀ j < k, u (j + 1) = H *ᵥ v (j + 1) + eu (j + 1)
  /-- The product error. -/
  norm_eu_le : ∀ j < k,
    ‖WithLp.toLp 2 (eu (j + 1))‖ ≤ ε * specNorm H * ‖WithLp.toLp 2 (v (j + 1))‖
  /-- The first update. -/
  w_eq : ∀ j < k, w (j + 1) = u (j + 1) - β j • v j + ew (j + 1)
  /-- The first update error. -/
  norm_ew_le : ∀ j < k, ‖WithLp.toLp 2 (ew (j + 1))‖ ≤
    ε * (‖WithLp.toLp 2 (u (j + 1))‖ + |β j| * ‖WithLp.toLp 2 (v j)‖)
  /-- The inner product. -/
  α_eq : ∀ j < k, α (j + 1) = v (j + 1) ⬝ᵥ w (j + 1) + eα (j + 1)
  /-- The inner product error. -/
  abs_eα_le : ∀ j < k,
    |eα (j + 1)| ≤ ε * ‖WithLp.toLp 2 (v (j + 1))‖ * ‖WithLp.toLp 2 (w (j + 1))‖
  /-- The second update. -/
  z_eq : ∀ j < k, z (j + 1) = w (j + 1) - α (j + 1) • v (j + 1) + ez (j + 1)
  /-- The second update error. -/
  norm_ez_le : ∀ j < k, ‖WithLp.toLp 2 (ez (j + 1))‖ ≤
    ε * (‖WithLp.toLp 2 (w (j + 1))‖ + |α (j + 1)| * ‖WithLp.toLp 2 (v (j + 1))‖)
  /-- The stored norm before orthogonalization. -/
  abs_ν_sub_le : ∀ j < k, |ν (j + 1) - ‖WithLp.toLp 2 (z (j + 1))‖| ≤
    ε * ‖WithLp.toLp 2 (z (j + 1))‖
  /-- The orthogonalization guarantee against $\mathbf{v}_1, \dots, \mathbf{v}_{j+1}$. -/
  orth_eq : ∀ j < k, IsOrthErr η₀ ε₁ ε₂ ε₃ (LanczosReorthRun.basisOf v (j + 1)) (z (j + 1))
    (fun i => h (j + 1) i) (z' (j + 1))
  /-- The computed norm after orthogonalization. -/
  abs_β_sub_le : ∀ j < k, |β (j + 1) - ‖WithLp.toLp 2 (z' (j + 1))‖| ≤
    ε * ‖WithLp.toLp 2 (z' (j + 1))‖
  /-- The normalization. -/
  smul_v_eq : ∀ j < k, β (j + 1) • v (j + 2) = z' (j + 1) + δ (j + 1)
  /-- The normalization error. -/
  norm_δ_le : ∀ j < k, ‖WithLp.toLp 2 (δ (j + 1))‖ ≤ ε * ‖WithLp.toLp 2 (z' (j + 1))‖
  /-- Nearly unit Lanczos vectors, the next one included. -/
  abs_norm_v_sq_sub_one_le : ∀ j, 1 ≤ j → j ≤ k + 1 → |‖WithLp.toLp 2 (v j)‖ ^ 2 - 1| ≤ ε
  /-- Strict $\tau$-admissibility of every step (so $\beta_j > 0$). -/
  admissible : ∀ j < k, τ * ν (j + 1) < β (j + 1)
  /-- The threshold is positive. -/
  τ_pos : 0 < τ

namespace LanczosReorthRun

variable {n k : ℕ} (L : LanczosReorthRun n k)

/-- The underlying symmetric three-term data (forgetting the local errors). -/
def toLanczosData : LanczosData n k where
  H := L.H
  v := L.v
  α := L.α
  β := L.β
  transpose_H := L.transpose_H
  k_pos := L.k_pos
  v_zero := L.v_zero
  β_zero := L.β_zero

/-- **The per-column orthogonality level** $\mu = 2(\varepsilon_1 + \varepsilon_3/\tau +
\varepsilon)$: a bound for $\|\mathbf{V}_j^{\mathsf{T}}\mathbf{v}_{j+1}\|$ and
$|\|\mathbf{v}_{j+1}\|^2 - 1|$ on an admissible step. -/
noncomputable def orthLevel : ℝ :=
  2 * (L.ε₁ + L.ε₃ / L.τ + L.ε)

/-- **The recurrence level** $\mu + \varepsilon + \varepsilon_2$, the size (relative to
$\|\mathbf{H}\|_2$) of one column of the residual of the three-term relation. -/
noncomputable def recLevel : ℝ :=
  L.orthLevel + L.ε + L.ε₂

/-- **The backward radius** $100(k+1)\,(\mu + \varepsilon + \varepsilon_2)\,\|\mathbf{H}\|_2$, the
bound on the symmetric backward perturbation of the run. -/
noncomputable def backwardRadius : ℝ :=
  100 * ((k : ℝ) + 1) * L.recLevel * specNorm L.H

/-- The columns of an $n \times (k + 1)$ matrix as a sequence indexed from $1$
($\mathbf{u}_0 = \mathbf{0}$, $\mathbf{u}_j$ column $j - 1$ for $1 \le j \le k + 1$, zero beyond),
in the indexing of `NLAlib.lanczosState_eq_of_orthonormal_recurrence`. -/
def colSeq (U : Matrix (Fin n) (Fin (k + 1)) ℝ) (j : ℕ) : Fin n → ℝ :=
  fun i => if h : 1 ≤ j ∧ j ≤ k + 1 then U i ⟨j - 1, by omega⟩ else 0

/-- The first index $0$ of `Fin k` (a run has $k \ge 1$ steps), the row and column of the
$(0, 0)$ entry of $\mathbf{T}_k$. -/
def firstIndex : Fin k :=
  ⟨0, L.k_pos⟩

end LanczosReorthRun

/-- **The admissible prefix** read off computed outputs: the number of leading steps
$j = 1, 2, \dots$ (at most $q$) with $\tau\nu_j < \beta_j$, the coefficients indexed as the
program stores them ($\nu_j$ at `nu[j-1]`, $\beta_j$ at `beta[j]`). -/
noncomputable def reorthSteps (τ : ℝ) (ν β : ℕ → ℝ) (q : ℕ) : ℕ :=
  ((List.range q).takeWhile fun j => τ * ν j < β (j + 1)).length

namespace LanczosReorthRun

variable {n k : ℕ} (L : LanczosReorthRun n k)

/-- The orthogonality level is nonnegative: $0 \le \mu$. -/
theorem orthLevel_nonneg : 0 ≤ L.orthLevel := by
  have := div_nonneg L.ε₃_nonneg L.τ_pos.le
  unfold orthLevel
  linarith [L.ε₁_nonneg, L.ε_nonneg]

/-- The orthogonality level is at most the recurrence level:
$\mu \le \mu + \varepsilon + \varepsilon_2$. -/
theorem orthLevel_le_recLevel : L.orthLevel ≤ L.recLevel := by
  unfold recLevel
  linarith [L.ε_nonneg, L.ε₂_nonneg]

/-- The recurrence level is nonnegative: $0 \le \mu + \varepsilon + \varepsilon_2$. -/
theorem recLevel_nonneg : 0 ≤ L.recLevel :=
  L.orthLevel_nonneg.trans L.orthLevel_le_recLevel

/-- Strict admissibility makes every computed $\beta_{j+1}$, $j < k$, positive. -/
theorem β_succ_pos {j : ℕ} (hj : j < k) : 0 < L.β (j + 1) := by
  have hν := L.abs_ν_sub_le j hj
  have := L.ε_le
  have hν0 : 0 ≤ L.ν (j + 1) := by
    nlinarith [neg_abs_le (L.ν (j + 1) - ‖WithLp.toLp 2 (L.z (j + 1))‖),
      norm_nonneg (WithLp.toLp 2 (L.z (j + 1))),
      mul_nonneg L.ε_nonneg (norm_nonneg (WithLp.toLp 2 (L.z (j + 1))))]
  linarith [L.admissible j hj, mul_nonneg L.τ_pos.le hν0]

/-- The computed coefficients $\beta_j$, $j \le k$, are nonnegative ($\beta_0 = 0$). -/
theorem β_nonneg {j : ℕ} (hj : j ≤ k) : 0 ≤ L.β j := by
  rcases j with _ | j
  · exact L.β_zero.ge
  · exact (L.β_succ_pos (by omega)).le

/-- The Lanczos vectors $\mathbf{v}_i$, $i \le k + 1$, satisfy
$\|\mathbf{v}_i\|^2 \le 1 + \varepsilon$ ($\mathbf{v}_0 = \mathbf{0}$). -/
theorem norm_v_sq_le {i : ℕ} (hi : i ≤ k + 1) : ‖WithLp.toLp 2 (L.v i)‖ ^ 2 ≤ 1 + L.ε := by
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · simp only [L.v_zero, WithLp.toLp_zero, norm_zero]
    linarith [L.ε_nonneg]
  · linarith [le_abs_self (‖WithLp.toLp 2 (L.v i)‖ ^ 2 - 1), L.abs_norm_v_sq_sub_one_le i hi0 hi]

/-- The Lanczos vectors $\mathbf{v}_i$, $i \le k + 1$, satisfy $\|\mathbf{v}_i\| \le 101/100$. -/
theorem norm_v_le {i : ℕ} (hi : i ≤ k + 1) : ‖WithLp.toLp 2 (L.v i)‖ ≤ 101 / 100 := by
  nlinarith [L.norm_v_sq_le hi, L.ε_le, norm_nonneg (WithLp.toLp 2 (L.v i))]

/-- Column $j < k$ of the residual of the three-term relation of the underlying data is the
reorthogonalization correction plus the local errors,
$\mathbf{f}_j = \mathbf{V}_{j+1}\mathbf{h}_{j+1} + (\mathbf{z}_{j+1} - \mathbf{V}_{j+1}
\mathbf{h}_{j+1} - \mathbf{z}_{j+1}') - \boldsymbol\delta_{j+1} - \mathbf{e}^u_{j+1} -
\mathbf{e}^w_{j+1} - \mathbf{e}^z_{j+1}$. No printed source. -/
theorem recurrenceError_eq {j : ℕ} (hj : j < k) :
    L.toLanczosData.recurrenceError j =
      basisOf L.v (j + 1) *ᵥ (fun i => L.h (j + 1) i) +
        (L.z (j + 1) - basisOf L.v (j + 1) *ᵥ (fun i => L.h (j + 1) i) - L.z' (j + 1)) -
        L.δ (j + 1) - L.eu (j + 1) - L.ew (j + 1) - L.ez (j + 1) := by
  simp only [LanczosData.recurrenceError, toLanczosData]
  rw [L.smul_v_eq j hj, L.z_eq j hj, L.w_eq j hj, L.u_eq j hj]
  abel

/-- **One admissible column is nearly orthogonal to the previous ones**: if
$\|\mathbf{V}_{j+1}^{\mathsf{T}}\mathbf{V}_{j+1} - \mathbf{I}\|_2 \le \eta_0 \le 1/100$ then
$\|\mathbf{V}_{j+1}^{\mathsf{T}}\mathbf{v}_{j+2}\| \le \mu$ = `NLAlib.LanczosReorthRun.orthLevel`.
[Paige1971, §6.1, (6.9)–(6.10)] (the criterion in substance). -/
theorem norm_transpose_mulVec_v_le {j : ℕ} (hj : j < k)
    (hV : specNorm ((basisOf L.v (j + 1))ᵀ * basisOf L.v (j + 1) - 1) ≤ L.η₀)
    (hη : L.η₀ ≤ 1 / 100) :
    ‖WithLp.toLp 2 ((basisOf L.v (j + 1))ᵀ *ᵥ L.v (j + 2))‖ ≤ L.orthLevel := by
  have hord := (L.orth_eq j hj).orth hV
  have hs : Real.sqrt (1 + L.η₀) ≤ 3 / 2 := by
    rw [Real.sqrt_le_iff]
    constructor <;> nlinarith
  have hsq : specNorm (basisOf L.v (j + 1))ᵀ ≤ Real.sqrt (1 + L.η₀) := by
    rw [specNorm_transpose]
    exact specNorm_le_sqrt_of_specNorm_transpose_mul_self_sub_one_le hV
  have hδ := (norm_toLp_mulVec_le (basisOf L.v (j + 1))ᵀ (L.δ (j + 1))).trans
    (mul_le_mul hsq (L.norm_δ_le j hj) (norm_nonneg _) (Real.sqrt_nonneg _))
  have hvec : L.β (j + 1) • ((basisOf L.v (j + 1))ᵀ *ᵥ L.v (j + 2)) =
      (basisOf L.v (j + 1))ᵀ *ᵥ L.z' (j + 1) + (basisOf L.v (j + 1))ᵀ *ᵥ L.δ (j + 1) := by
    rw [← Matrix.mulVec_add, ← L.smul_v_eq j hj, Matrix.mulVec_smul]
  have hν := abs_le.mp (L.abs_ν_sub_le j hj)
  have hβ := abs_le.mp (L.abs_β_sub_le j hj)
  have hadm := L.admissible j hj
  have hτ := L.τ_pos
  have he0 := L.ε_nonneg
  have he1 := L.ε_le
  have hε₁ := L.ε₁_nonneg
  have hε₃ := L.ε₃_nonneg
  have hq0 := norm_nonneg (WithLp.toLp 2 (L.z (j + 1)))
  have hp0 := norm_nonneg (WithLp.toLp 2 (L.z' (j + 1)))
  set a := ‖WithLp.toLp 2 ((basisOf L.v (j + 1))ᵀ *ᵥ L.v (j + 2))‖ with ha
  set p := ‖WithLp.toLp 2 (L.z' (j + 1))‖ with hp
  set q := ‖WithLp.toLp 2 (L.z (j + 1))‖ with hq
  set s := Real.sqrt (1 + L.η₀) with hsdef
  set ε := L.ε with hεdef
  set τ := L.τ with hτdef
  set β := L.β (j + 1) with hβdef
  set ε₁ := L.ε₁ with hε₁def
  set ε₃ := L.ε₃ with hε₃def
  set T := ε₃ / τ with hT
  have hτν : τ * ((1 - ε) * q) ≤ τ * L.ν (j + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hτ.le
  have hτq : 0 ≤ τ * ((1 - ε) * q) :=
    mul_nonneg hτ.le (mul_nonneg (by linarith) hq0)
  have hβpos : 0 < β := by linarith
  have hnorm : β * a = ‖WithLp.toLp 2 (β • ((basisOf L.v (j + 1))ᵀ *ᵥ L.v (j + 2)))‖ := by
    rw [WithLp.toLp_smul, norm_smul, Real.norm_of_nonneg hβpos.le]
  have hb : β * a ≤ ε₁ * p + ε₃ * q + s * (ε * p) := by
    rw [hnorm, hvec, WithLp.toLp_add]
    exact (norm_add_le _ _).trans (by linarith)
  have hF2 : τ * ((1 - ε) * q) ≤ (1 + ε) * p := by linarith
  have hq2 : ε₃ * q * (1 - ε) ≤ T * (1 + ε) * p := by
    have h := mul_le_mul_of_nonneg_left hF2 (div_nonneg hε₃ hτ.le)
    calc ε₃ * q * (1 - ε) = T * (τ * ((1 - ε) * q)) := by
          rw [hT]; field_simp
      _ ≤ T * ((1 + ε) * p) := h
      _ = T * (1 + ε) * p := by ring
  have hT0 : 0 ≤ T := div_nonneg hε₃ hτ.le
  have hβlow : (1 - ε) * p ≤ β := by linarith [hβ.1]
  have h1 : a * β * (1 - ε) ≤ ((1 - ε) * (ε₁ + s * ε) + T * (1 + ε)) * p := by
    nlinarith [mul_le_mul_of_nonneg_right hb (by linarith : (0:ℝ) ≤ 1 - ε)]
  have hpoly : (1 - ε) * (ε₁ + s * ε) + T * (1 + ε) ≤ 2 * (ε₁ + T + ε) * (1 - ε) ^ 2 := by
    have c1 : 0 ≤ ε₁ * (1 - ε) * (1 - 2 * ε) :=
      mul_nonneg (mul_nonneg hε₁ (by linarith)) (by linarith)
    have c2 : 0 ≤ T * (1 - 5 * ε + 2 * ε ^ 2) :=
      mul_nonneg hT0 (by nlinarith)
    have c3 : 0 ≤ ε * (1 - ε) * (2 * (1 - ε) - s) :=
      mul_nonneg (mul_nonneg he0 (by linarith)) (by linarith)
    nlinarith [c1, c2, c3]
  have h2 : ((1 - ε) * (ε₁ + s * ε) + T * (1 + ε)) * p ≤ 2 * (ε₁ + T + ε) * (1 - ε) * β := by
    have hK : 0 ≤ 2 * (ε₁ + T + ε) * (1 - ε) := by
      have : 0 ≤ ε₁ + T + ε := by linarith
      have : 0 ≤ 1 - ε := by linarith
      positivity
    linarith [mul_le_mul_of_nonneg_right hpoly hp0, mul_le_mul_of_nonneg_left hβlow hK]
  have hpos : 0 < β * (1 - ε) := mul_pos hβpos (by linarith)
  unfold LanczosReorthRun.orthLevel
  by_contra! hcon
  linarith [mul_lt_mul_of_pos_right hcon hpos]

/-- **Orthogonality of the computed basis on the admissible prefix**: under the fixed-point
condition $\sqrt{3(k+1)}\,\mu \le \eta_0 \le 1/100$, for every $m \le k + 1$,
$\|\mathbf{V}_m^{\mathsf{T}}\mathbf{V}_m - \mathbf{I}\|_{\mathsf F} \le \sqrt{3m}\,\mu$.
[Paige1971, §6.1, (6.9)] for Lanczos with reorthogonalization;
[GiraudLangouRozloznikVandenEshof2005,
Theorem 2] for the CGS2 kernel constants.
Result: lanczos-reorth-orthogonality -/
theorem frobNorm_transpose_mul_self_sub_one_le (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀) :
    ∀ m ≤ k + 1, frobNorm ((basisOf L.v m)ᵀ * basisOf L.v m - 1) ≤
      Real.sqrt (3 * m) * L.orthLevel := by
  have hμ := L.orthLevel_nonneg
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hm
  apply frobNorm_transpose_mul_self_sub_one_le_of_columns L.v m hμ
  · intro c hc
    rcases Nat.eq_zero_or_pos c with rfl | hc0
    · simp [hμ, EuclideanSpace.norm_eq]
    · obtain ⟨j, rfl⟩ : ∃ j, c = j + 1 := ⟨c - 1, by omega⟩
      have hj : j < k := by omega
      have hIH := ih (j + 1) hc (by omega)
      have hc' : ((j + 1 : ℕ) : ℝ) ≤ (k : ℝ) + 1 := by
        have : j + 1 ≤ k + 1 := by omega
        exact_mod_cast this
      have h1 : Real.sqrt (3 * ((j + 1 : ℕ) : ℝ)) ≤ Real.sqrt (3 * ((k : ℝ) + 1)) :=
        Real.sqrt_le_sqrt (by linarith)
      have hV : specNorm ((basisOf L.v (j + 1))ᵀ * basisOf L.v (j + 1) - 1) ≤ L.η₀ :=
        (specNorm_le_frobNorm _).trans
          (hIH.trans ((mul_le_mul_of_nonneg_right h1 hμ).trans hsmall))
      exact norm_transpose_mulVec_v_le L hj hV hη
  · intro c hc
    have := L.abs_norm_v_sq_sub_one_le (c + 1) (by omega) (by omega)
    have hdiv := div_nonneg L.ε₃_nonneg L.τ_pos.le
    unfold orthLevel
    linarith [L.ε₁_nonneg, L.ε_nonneg]

/-- The spectral form of the orthogonality bound: under the fixed-point condition
$\sqrt{3(k+1)}\,\mu \le \eta_0 \le 1/100$, every $m \le k + 1$ has
$\|\mathbf{V}_m^{\mathsf{T}}\mathbf{V}_m - \mathbf{I}\|_2 \le \eta_0$. -/
theorem specNorm_transpose_mul_self_sub_one_le (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀) {m : ℕ} (hm : m ≤ k + 1) :
    specNorm ((basisOf L.v m)ᵀ * basisOf L.v m - 1) ≤ L.η₀ := by
  have hμ := L.orthLevel_nonneg
  refine (specNorm_le_frobNorm _).trans
    ((L.frobNorm_transpose_mul_self_sub_one_le hη hsmall m hm).trans (le_trans ?_ hsmall))
  gcongr
  exact_mod_cast hm

/-- Full reorthogonalization stops by step $n$: under the fixed-point condition
$\sqrt{3(k+1)}\,\mu \le \eta_0 \le 1/100$, the admissible prefix has $k + 1 \le n$ (strict
admissibility makes $\mathbf{v}_{k+1}$ a genuine column). No printed source. -/
theorem succ_le_card (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀) : k + 1 ≤ n :=
  le_of_specNorm_transpose_mul_self_sub_one_lt_one
    ((L.specNorm_transpose_mul_self_sub_one_le hη hsmall le_rfl).trans_lt (by linarith))

/-- Prefixes of a run are runs: for $0 < m \le k$ there is a run of $m$ steps with the same
data and parameters. (A run ending in $\beta_k = 0$ cannot occur under strict admissibility.) -/
theorem exists_ofLE {m : ℕ} (hm : 0 < m) (hmk : m ≤ k) :
    ∃ L' : LanczosReorthRun n m, L'.H = L.H ∧ L'.v = L.v ∧ L'.α = L.α ∧ L'.β = L.β ∧
      L'.ν = L.ν ∧ L'.h = L.h ∧ L'.ε = L.ε ∧ L'.τ = L.τ ∧ L'.η₀ = L.η₀ ∧ L'.ε₁ = L.ε₁ ∧
      L'.ε₂ = L.ε₂ ∧ L'.ε₃ = L.ε₃ := by
  refine ⟨{
    H := L.H, v := L.v, u := L.u, w := L.w, z := L.z, z' := L.z', α := L.α, β := L.β,
    ν := L.ν, h := L.h, eu := L.eu, ew := L.ew, ez := L.ez, eα := L.eα, δ := L.δ, ε := L.ε,
    τ := L.τ, η₀ := L.η₀, ε₁ := L.ε₁, ε₂ := L.ε₂, ε₃ := L.ε₃,
    transpose_H := L.transpose_H, ε_nonneg := L.ε_nonneg, ε_le := L.ε_le,
    ε₁_nonneg := L.ε₁_nonneg, ε₂_nonneg := L.ε₂_nonneg, ε₃_nonneg := L.ε₃_nonneg,
    k_pos := hm, v_zero := L.v_zero, β_zero := L.β_zero,
    u_eq := fun j hj => L.u_eq j (by omega),
    norm_eu_le := fun j hj => L.norm_eu_le j (by omega),
    w_eq := fun j hj => L.w_eq j (by omega),
    norm_ew_le := fun j hj => L.norm_ew_le j (by omega),
    α_eq := fun j hj => L.α_eq j (by omega),
    abs_eα_le := fun j hj => L.abs_eα_le j (by omega),
    z_eq := fun j hj => L.z_eq j (by omega),
    norm_ez_le := fun j hj => L.norm_ez_le j (by omega),
    abs_ν_sub_le := fun j hj => L.abs_ν_sub_le j (by omega),
    orth_eq := fun j hj => L.orth_eq j (by omega),
    abs_β_sub_le := fun j hj => L.abs_β_sub_le j (by omega),
    smul_v_eq := fun j hj => L.smul_v_eq j (by omega),
    norm_δ_le := fun j hj => L.norm_δ_le j (by omega),
    abs_norm_v_sq_sub_one_le := fun j h1 h2 => L.abs_norm_v_sq_sub_one_le j h1 (by omega),
    admissible := fun j hj => L.admissible j (by omega),
    τ_pos := L.τ_pos
  },
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end LanczosReorthRun

end NLAlib
