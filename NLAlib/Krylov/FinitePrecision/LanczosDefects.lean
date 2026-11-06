/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.FinitePrecision.LanczosData

/-!
# Measured local defects of a Lanczos recurrence

Local operation equations give recurrence and adjacent-inner-product certificates without
relative-only accuracy assumptions, a new run structure, or a nonbreakdown assertion.
The defects may include absolute arithmetic contributions. These are numerical implications;
a program execution theorem must supply the equations and their decoded defect bounds.
For unit-normalized data, the existing `NormalizedLanczosData` backward theorem consumes
uniform bounds on these same recurrence and adjacent-inner-product quantities.

## Main results

* `NLAlib.LanczosData.norm_recurrenceError_le_of_eq`: four local vector defects.
* `NLAlib.LanczosData.abs_adjacentInner_le_of_eq`: projection and normalization defects.
-/

@[expose] public section

namespace NLAlib.LanczosData

open scoped Matrix

variable {n k : ℕ}

/-- The recurrence residual is minus the sum of the matvec, previous-vector update,
projection update and normalization defects. The local equations use decoded values
at the supplied step; neither relative accuracy nor a positive next coefficient is assumed. -/
theorem recurrenceError_eq_of_eq (D : LanczosData n k) (j : ℕ)
    (u w z eu ew ez δ : Fin n → ℝ)
    (hu : u = D.H *ᵥ D.v (j + 1) + eu)
    (hw : w = u - D.β j • D.v j + ew)
    (hz : z = w - D.α (j + 1) • D.v (j + 1) + ez)
    (hδ : D.β (j + 1) • D.v (j + 2) = z + δ) :
    D.recurrenceError j = -(eu + ew + ez + δ) := by
  have h1 : D.H *ᵥ D.v (j + 1) = u - eu := by rw [hu]; abel
  have h2 : u = w + D.β j • D.v j - ew := by rw [hw]; abel
  have h3 : w = z + D.α (j + 1) • D.v (j + 1) - ez := by rw [hz]; abel
  have h4 : z = D.β (j + 1) • D.v (j + 2) - δ := by rw [hδ]; abel
  simp only [recurrenceError]
  rw [h1, h2, h3, h4]
  abel

/-- The recurrence residual has norm at most the sum of the four local vector-defect norms.
The projection coefficient is the computed one; its scalar dot-product error enters the
adjacent-inner-product certificate instead. The result includes a zero next coefficient. -/
theorem norm_recurrenceError_le_of_eq (D : LanczosData n k) (j : ℕ)
    (u w z eu ew ez δ : Fin n → ℝ)
    (hu : u = D.H *ᵥ D.v (j + 1) + eu)
    (hw : w = u - D.β j • D.v j + ew)
    (hz : z = w - D.α (j + 1) • D.v (j + 1) + ez)
    (hδ : D.β (j + 1) • D.v (j + 2) = z + δ) :
    ‖WithLp.toLp 2 (D.recurrenceError j)‖ ≤ ‖WithLp.toLp 2 eu‖ +
      ‖WithLp.toLp 2 ew‖ + ‖WithLp.toLp 2 ez‖ + ‖WithLp.toLp 2 δ‖ := by
  rw [D.recurrenceError_eq_of_eq j u w z eu ew ez δ hu hw hz hδ,
    WithLp.toLp_neg, norm_neg, WithLp.toLp_add, WithLp.toLp_add, WithLp.toLp_add]
  have h1 := norm_add_le (WithLp.toLp 2 eu) (WithLp.toLp 2 ew)
  have h2 := norm_add_le (WithLp.toLp 2 eu + WithLp.toLp 2 ew) (WithLp.toLp 2 ez)
  have h3 := norm_add_le (WithLp.toLp 2 eu + WithLp.toLp 2 ew + WithLp.toLp 2 ez)
    (WithLp.toLp 2 δ)
  linarith only [h1, h2, h3]

/-- The adjacent inner product splits into the scalar projection error, squared norm defect,
and the inner products of the current vector with projection-update and normalization errors.
The equations need no sign or nonzero assumptions on either coefficient. -/
theorem adjacentInner_eq_of_eq (D : LanczosData n k) (j : ℕ)
    (w z ez δ : Fin n → ℝ) (eα : ℝ)
    (hα : D.α (j + 1) = D.v (j + 1) ⬝ᵥ w + eα)
    (hz : z = w - D.α (j + 1) • D.v (j + 1) + ez)
    (hδ : D.β (j + 1) • D.v (j + 2) = z + δ) :
    D.adjacentInner j = -eα - (‖WithLp.toLp 2 (D.v (j + 1))‖ ^ 2 - 1) * D.α (j + 1)
      + D.v (j + 1) ⬝ᵥ ez + D.v (j + 1) ⬝ᵥ δ := by
  have hal : D.v (j + 1) ⬝ᵥ w = D.α (j + 1) - eα := by rw [hα]; ring
  simp only [adjacentInner]
  rw [hδ, dotProduct_add, hz, EuclideanSpace.norm_toLp_sq_eq_dotProduct_self]
  simp only [dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul, hal]
  ring

/-- The adjacent inner product is bounded by the scalar projection defect, the computed
coefficient times the squared norm defect, and the projection/normalization vector defects.
Thus additive arithmetic errors remain visible rather than being divided by an input norm.
The bound covers terminal computed coefficients and imperfectly normalized vectors. -/
theorem abs_adjacentInner_le_of_eq (D : LanczosData n k) (j : ℕ)
    (w z ez δ : Fin n → ℝ) (eα : ℝ)
    (hα : D.α (j + 1) = D.v (j + 1) ⬝ᵥ w + eα)
    (hz : z = w - D.α (j + 1) • D.v (j + 1) + ez)
    (hδ : D.β (j + 1) • D.v (j + 2) = z + δ) :
    |D.adjacentInner j| ≤ |eα| + |D.α (j + 1)| *
      |‖WithLp.toLp 2 (D.v (j + 1))‖ ^ 2 - 1| + ‖WithLp.toLp 2 (D.v (j + 1))‖ *
        (‖WithLp.toLp 2 ez‖ + ‖WithLp.toLp 2 δ‖) := by
  rw [D.adjacentInner_eq_of_eq j w z ez δ eα hα hz hδ]
  have hez := EuclideanSpace.abs_dotProduct_le_norm (D.v (j + 1)) ez
  have hed := EuclideanSpace.abs_dotProduct_le_norm (D.v (j + 1)) δ
  have habs := abs_add_le
    (-eα - (‖WithLp.toLp 2 (D.v (j + 1))‖ ^ 2 - 1) * D.α (j + 1) +
      D.v (j + 1) ⬝ᵥ ez) (D.v (j + 1) ⬝ᵥ δ)
  have habs' := abs_add_le
    (-eα - (‖WithLp.toLp 2 (D.v (j + 1))‖ ^ 2 - 1) * D.α (j + 1))
      (D.v (j + 1) ⬝ᵥ ez)
  have hsub := abs_sub (-eα) ((‖WithLp.toLp 2 (D.v (j + 1))‖ ^ 2 - 1) * D.α (j + 1))
  rw [abs_neg, abs_mul] at hsub
  nlinarith only [habs, habs', hsub, hez, hed]

end NLAlib.LanczosData
